use chrono::{DateTime, Local};
use jwalk::{Parallelism, WalkDir};
use regex::{Regex, RegexBuilder};
use std::collections::{HashMap, HashSet};
use std::env;
use std::fs::{self, File};
use std::io::{self, BufWriter, IsTerminal, Write};
use std::os::unix::ffi::OsStrExt;
use std::os::unix::fs::{FileTypeExt, PermissionsExt};
use std::path::{Component, Path, PathBuf};
use std::process::ExitCode;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;
use std::time::Duration;

use crossbeam_channel::{unbounded, Sender};
use rayon::prelude::*;

#[cfg(not(target_env = "msvc"))]
#[global_allocator]
static ALLOC: jemallocator::Jemalloc = jemallocator::Jemalloc;

const VERSION: &str = "0.8.6";
const NTFS_FS_TYPES: [&str; 3] = ["ntfs", "ntfs3", "fuseblk"];

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum TypeFlag {
    File,
    Dir,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum SortField {
    Date,
    Size,
    Name,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum SortOrder {
    Asc,
    Desc,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum ColorWhen {
    Auto,
    Always,
    Never,
}

#[derive(Clone, Debug)]
struct NamePattern {
    type_flag: Option<TypeFlag>,
    regex: String,
}

#[derive(Clone, Debug)]
enum SearchDirMode {
    Path(String),
    Pattern(String),
}

#[derive(Clone, Debug)]
struct MountInfo {
    device: PathBuf,
    mount_point: PathBuf,
    fs_type: String,
}

#[derive(Clone, Debug)]
struct Options {
    timeout_dur: Duration,
    force_pattern_mode: bool,
    long_format: bool,
    long_extended: bool,
    sizes: bool,
    counts: bool,
    regex_mode: bool,
    sort_field: Option<SortField>,
    sort_order: Option<SortOrder>,
    no_recurse: bool,
    follow_links: bool,
    respect_ignore: bool,
    visible_only: bool,
    threads_override: usize,
    cache_output: bool,
    absolute_paths: bool,
    force_dir: bool,
    force_file: bool,
    force_full: bool,
    classify: bool,
    color_when: ColorWhen,
    hyperlinks: bool,
    highlight_match: bool,
    contains_all: bool,
    path_override: Option<String>,
    positional: Vec<String>,
}

struct SearchResult {
    path: String,
    is_dir: bool,
    is_symlink: bool,
    metadata: Option<fs::Metadata>,
}

#[derive(Clone, Debug)]
struct ContainsAllSpec {
    terms: Vec<String>,
    root: PathBuf,
}

#[derive(Clone, Debug)]
struct HighlightSpec {
    prefix_rules: Vec<Regex>,
    leaf_rules: Vec<Regex>,
}

#[derive(Clone, Debug)]
struct DirStats {
    files: u64,
    bytes: u64,
    human: String,
}

#[derive(Default)]
struct DirStatsCache {
    map: HashMap<String, DirStats>,
    bytes_map: HashMap<String, u64>,
}

struct RawCacheState {
    dirs: BufWriter<File>,
    files: BufWriter<File>,
    seen_dirs: HashSet<String>,
    seen_files: HashSet<String>,
}

#[derive(Clone)]
struct ColorSpec {
    by_key: HashMap<String, String>,
    globs: Vec<(Regex, String)>,
    color_prefix_dir: String,
    color_dir: String,
    color_link: String,
    color_exec: String,
}

fn usage() -> String {
    let txt = r#"A parallel recursive file searcher (unearth)

Usage:
  unearth <filename/dirname> [<search_dir>]
  unearth (--full|-F) <pattern1>  [<pattern2> <pattern3>...]
                       [--dir|-d] [--file|-f] [--regex|-r] [--bypass|-b]
                       [--classify|-C]
                       [--absolute-paths|-A]
                       [--sizes]
                       [--contains-all]
                       [--path DIR]
                       [--timeout N] [--sort date|size|name asc|desc]
                       [--no-recurse|-R] [--follow-links]
                       [--ignore] [--hidden|-H] [--threads N] [--cache-raw]
                       [--color=auto|always|never] [--hyperlink]
                       [--highlight-match|--match-red]
  unearth (--version|-V)

Arguments:
   <filename/dirname>:
      The file or directory name to search for. Supports exact and partial
      matching by default; use --regex/-r for regex matching.

   SEARCH MATRIX:

   Goal           | Shorthand        | Wildcard Format        | Regex Format
   ---------------|------------------|------------------------|-------------------
   Contains (All) | abc              | "*abc*"                | -r "abc"
   Contains (File)| abc -f           | "*abc*" -f             | -r "abc" -f
   Contains (Dir) | abc -d           | "*abc*" -d             | -r "abc" -d
   Exact (All)    | -                | -                      | -r "^abc$"
   Exact (File)   | -                | -                      | -r "^abc$" -f
   Exact (Dir)    | /abc/            | -                      | -r "^abc$" -d
   Starts (All)   | /abc             | "abc*"                 | -r "^abc"
   Starts (File)  | /abc -f          | "abc*" -f              | -r "^abc" -f
   Starts (Dir)   | /abc -d          | "abc*" -d              | -r "^abc" -d
   Ends (All)     | -                | "*abc"                 | -r "abc$"
   Ends (File)    | -                | "*abc" -f              | -r "abc$" -f
   Ends (Dir)     | abc/             | "*abc" -d              | -r "abc$" -d

   <search_dir>:
      Location to search. Defaults to '.' (the current directory).
      Behavior follows this priority:
      1. Local/Absolute Path: If the path exists on disk (e.g., '.', '/',
         or a specific path), the search is limited to that directory and
         will not fallback to a global search.
      2. Global Pattern Match: If the path does not exist, the script
         searches the ENTIRE disk for all directories matching the pattern
         (see matrix below) and searches inside them.

   SEARCH DIR MATRIX:

   Goal           | Shorthand | Wildcard Format | Regex Format
   ---------------|-----------|-----------------|----------------
   Contains       | abc       | "*abc*"         | -r "abc"
   Exact          | /abc/     | -               | -r "^abc$"
   Starts         | /abc      | "abc*"          | -r "^abc"
   Ends           | abc/      | "*abc"          | -r "abc$"

   Note: If the 1st check (Literal Path) fails, the script performs a global
   directory match pass before searching within matched directories.

   The --full flag matches against the full absolute path instead of just
   the basename.
   It supports multiple patterns (implicit AND) and prunes redundant
   child results.

   Example: unearth --full "src" "main"   # Matches BOTH (hides children)
   Example: unearth --full "test"         # Returns /path/to/test, but hides
   /path/to/test/file

   Notes:
  - Use quotes around patterns containing $ or * to prevent shell expansion.
  - Regex mode is only enabled with --regex/-r.
  - --highlight-match (alias: --match-red) shows matched text in red inside
    output paths.
  - --sizes prints compact sizes as SIZE<TAB>PATH (max 6 chars including
    unit, e.g., 1.111M, 111.1M),
    using recursive directory totals for directory matches.
  - Name contains-all mode is implicit with 2+ plain positional terms
    (legacy name+search_dir selector forms still use search_dir mode),
    or enabled by --contains-all:
    unearth WORD1 WORD2 [WORD3 ...] [PATH]
    It finds filenames/paths containing all words in any order.
    PATH is implicit only if the last arg is absolute (/x), explicit relative
    (./x, ../x, ~/x), or contains a slash (a/b). A bare token like "folder1"
    is treated as a word unless --path folder1 is used.
  - On NTFS-like filesystems (ntfs, ntfs3, fuseblk), recursive directory size
    scans attempt an MFT fast path and fall back automatically.
    Set UNEARTH_NTFS_DEBUG=1 to print fast-path status.
  - Plain patterns are contains. For exact matches use regex anchors
    (e.g., --regex "^word$"), or /word/ for exact-directory shorthand.
"#;
    txt.to_string()
}

fn parse_duration(t: &str) -> Result<Duration, String> {
    let re = Regex::new(r"^(\d+)([sm])?$").unwrap();
    if let Some(caps) = re.captures(t) {
        let n = caps[1].parse::<u64>().map_err(|e| e.to_string())?;
        match caps.get(2).map(|m| m.as_str()) {
            Some("m") => Ok(Duration::from_secs(n * 60)),
            _ => Ok(Duration::from_secs(n)),
        }
    } else {
        Err(format!("Invalid timeout format: {}", t))
    }
}

fn parse_args() -> Result<Options, String> {
    let mut opts = Options {
        timeout_dur: Duration::from_secs(6),
        force_pattern_mode: false,
        long_format: false,
        long_extended: false,
        sizes: false,
        counts: false,
        regex_mode: false,
        sort_field: None,
        sort_order: None,
        no_recurse: false,
        follow_links: false,
        respect_ignore: false,
        visible_only: true,
        threads_override: 8,
        cache_output: false,
        absolute_paths: false,
        force_dir: false,
        force_file: false,
        force_full: false,
        classify: false,
        color_when: ColorWhen::Auto,
        hyperlinks: false,
        highlight_match: false,
        contains_all: false,
        path_override: None,
        positional: Vec::new(),
    };

    let args: Vec<String> = env::args().skip(1).collect();
    let mut i = 0usize;

    while i < args.len() {
        let arg = &args[i];

        if arg.starts_with('-') && !arg.starts_with("--") && arg.len() > 2 {
            let mut all_known = true;
            for ch in arg[1..].chars() {
                let handled = match ch {
                    'd' => {
                        opts.force_dir = true;
                        true
                    }
                    'f' => {
                        opts.force_file = true;
                        true
                    }
                    'F' => {
                        opts.force_full = true;
                        true
                    }
                    'C' => {
                        opts.classify = true;
                        true
                    }
                    'A' => {
                        opts.absolute_paths = true;
                        true
                    }
                    'r' => {
                        opts.regex_mode = true;
                        true
                    }
                    'R' => {
                        opts.no_recurse = true;
                        true
                    }
                    'H' => {
                        opts.visible_only = false;
                        true
                    }
                    'b' => {
                        opts.force_pattern_mode = true;
                        true
                    }
                    'l' => {
                        opts.long_format = true;
                        true
                    }
                    'L' => {
                        opts.long_format = true;
                        opts.long_extended = true;
                        true
                    }
                    'h' => {
                        print!("{}", usage());
                        std::process::exit(0);
                    }
                    'V' => {
                        println!("unearth {}", VERSION);
                        std::process::exit(0);
                    }
                    _ => false,
                };
                if !handled {
                    all_known = false;
                    break;
                }
            }

            if all_known {
                i += 1;
                continue;
            }
        }

        match arg.as_str() {
            "--timeout" => {
                i += 1;
                if i < args.len() {
                    opts.timeout_dur = parse_duration(&args[i])?;
                }
            }
            _ if arg.starts_with("--timeout=") => {
                opts.timeout_dur = parse_duration(arg.trim_start_matches("--timeout="))?;
            }
            "--threads" => {
                i += 1;
                if i < args.len() {
                    opts.threads_override = args[i]
                        .parse::<usize>()
                        .map_err(|_| "Invalid threads count")?;
                    if opts.threads_override == 0 {
                        return Err("--threads requires a positive integer".to_string());
                    }
                }
            }
            _ if arg.starts_with("--threads=") => {
                opts.threads_override = arg
                    .trim_start_matches("--threads=")
                    .parse::<usize>()
                    .map_err(|_| "Invalid threads count")?;
                if opts.threads_override == 0 {
                    return Err("--threads requires a positive integer".to_string());
                }
            }
            "--color" => {
                i += 1;
                if i < args.len() {
                    opts.color_when = parse_color_when(&args[i])?;
                }
            }
            _ if arg.starts_with("--color=") => {
                opts.color_when = parse_color_when(arg.trim_start_matches("--color="))?;
            }
            "--hyperlink" => opts.hyperlinks = true,
            "--highlight-match" | "--match-red" => opts.highlight_match = true,
            "--contains-all" => opts.contains_all = true,
            "--path" => {
                i += 1;
                if i < args.len() {
                    opts.path_override = Some(args[i].clone());
                } else {
                    return Err("--path requires a directory argument".to_string());
                }
            }
            _ if arg.starts_with("--path=") => {
                let v = arg.trim_start_matches("--path=").to_string();
                if v.is_empty() {
                    return Err("--path requires a non-empty directory argument".to_string());
                }
                opts.path_override = Some(v);
            }
            "--dir" | "-d" => opts.force_dir = true,
            "--file" | "-f" => opts.force_file = true,
            "--full" | "-F" => opts.force_full = true,
            "--classify" | "-C" => opts.classify = true,
            "--absolute-paths" | "-A" => opts.absolute_paths = true,
            "--regex" | "-r" => opts.regex_mode = true,
            "--sort" => {
                if i + 2 < args.len() {
                    let field = args[i + 1].as_str();
                    let order = args[i + 2].as_str();
                    opts.sort_field = match field {
                        "date" => Some(SortField::Date),
                        "size" => Some(SortField::Size),
                        "name" => Some(SortField::Name),
                        _ => return Err(format!("Unsupported sort field '{}'", field)),
                    };
                    opts.sort_order = match order {
                        "asc" => Some(SortOrder::Asc),
                        "desc" => Some(SortOrder::Desc),
                        _ => return Err(format!("Unsupported sort order '{}'", order)),
                    };
                    i += 2;
                }
            }
            "--no-recurse" | "-R" => opts.no_recurse = true,
            "--follow-links" => opts.follow_links = true,
            "--ignore" => opts.respect_ignore = true,
            "--hidden" | "-H" => opts.visible_only = false,
            "--cache-raw" => opts.cache_output = true,
            "--cache" => return Err("--cache was renamed to --cache-raw".to_string()),
            "--bypass" | "-b" => opts.force_pattern_mode = true,
            "--long" | "-l" => opts.long_format = true,
            "--sizes" => opts.sizes = true,
            "-L" | "--long-true-dirsize" => {
                opts.long_format = true;
                opts.long_extended = true;
            }
            "--info" | "-i" => return Err("--info/-i was renamed to --long/-l".to_string()),
            "--version" | "-V" => {
                println!("unearth {}", VERSION);
                std::process::exit(0);
            }
            "-h" | "--help" => {
                print!("{}", usage());
                std::process::exit(0);
            }
            "--" => {
                for x in args.iter().skip(i + 1) {
                    opts.positional.push(x.clone());
                }
                break;
            }
            _ => opts.positional.push(arg.clone()),
        }
        i += 1;
    }

    if opts.positional.is_empty() {
        return Err(usage());
    }
    Ok(opts)
}

fn parse_color_when(v: &str) -> Result<ColorWhen, String> {
    match v {
        "auto" => Ok(ColorWhen::Auto),
        "always" => Ok(ColorWhen::Always),
        "never" => Ok(ColorWhen::Never),
        _ => Err(format!("Unsupported --color value '{}'", v)),
    }
}

fn style_enabled(opts: &Options, stdout_is_tty: bool) -> bool {
    match opts.color_when {
        ColorWhen::Auto => stdout_is_tty,
        ColorWhen::Always => true,
        ColorWhen::Never => false,
    }
}

fn can_stream_direct(opts: &Options, use_style: bool) -> bool {
    !use_style
        && !opts.classify
        && !opts.force_full
        && !opts.highlight_match
        && !opts.counts
        && opts.sort_field.is_none()
        && !opts.long_format
        && !opts.sizes
        && !opts.absolute_paths
}

fn escape_regex_keep_star(s: &str) -> String {
    let mut out = String::with_capacity(s.len() * 2);
    for ch in s.chars() {
        if "[](){}.^$|+?".contains(ch) {
            out.push('\\');
        }
        out.push(ch);
    }
    out
}

fn to_regex_fragment(s: &str) -> String {
    let mut x = escape_regex_keep_star(s);
    x = x.replace(r"\*", "__LITERAL_STAR__");
    x = x.replace('*', ".*");
    x.replace("__LITERAL_STAR__", r"\*")
}

fn wildcard_to_regex(pat: &str) -> String {
    let lead_star = pat.starts_with('*');
    let trail_star =
        pat.ends_with('*') && (pat.len() < 2 || pat.as_bytes()[pat.len() - 2] != b'\\');
    let mut rx = to_regex_fragment(pat);
    if !lead_star {
        rx = format!("^{}", rx);
    }
    if !trail_star {
        rx.push('$');
    }
    rx
}

fn is_wrapped_quote(raw: &str) -> bool {
    (raw.starts_with('"') && raw.ends_with('"') && raw.len() >= 2)
        || (raw.starts_with('\'') && raw.ends_with('\'') && raw.len() >= 2)
}

fn parse_name_pattern(raw: &str, regex_mode: bool) -> NamePattern {
    let mut out = NamePattern {
        type_flag: None,
        regex: String::new(),
    };
    if is_wrapped_quote(raw) {
        let mut inner = raw[1..raw.len() - 1].to_string();
        inner = inner.trim_start_matches('/').to_string();
        if inner != "/" {
            inner = inner.trim_end_matches('/').to_string();
        }
        out.regex = if regex_mode {
            inner
        } else {
            wildcard_to_regex(&inner)
        };
        return out;
    }
    if regex_mode {
        out.regex = raw.to_string();
        return out;
    }
    if raw.starts_with('/') && raw.ends_with('/') {
        let frag = raw[1..raw.len() - 1].to_string();
        out.type_flag = Some(TypeFlag::Dir);
        out.regex = format!("^{}$", to_regex_fragment(&frag));
        return out;
    }
    if raw.starts_with('/') {
        let frag = raw.trim_start_matches('/');
        out.regex = format!("^{}", to_regex_fragment(frag));
        return out;
    }
    if raw != "/" && raw.ends_with('/') {
        out.type_flag = Some(TypeFlag::Dir);
        let no_slash = raw.trim_end_matches('/');
        out.regex = format!("{}$", to_regex_fragment(no_slash));
        return out;
    }
    if raw.contains('*') {
        out.regex = wildcard_to_regex(raw);
        return out;
    }
    out.regex = to_regex_fragment(raw);
    out
}

fn pattern_prefers_full_path(raw: &str, regex_mode: bool) -> bool {
    if regex_mode {
        return true;
    }
    let token = if is_wrapped_quote(raw) && raw.len() >= 2 {
        &raw[1..raw.len() - 1]
    } else {
        raw
    };
    token.contains('/')
}

fn term_selectivity_score(raw: &str, regex_mode: bool) -> i64 {
    let mut score: i64 = 0;
    let core = if is_wrapped_quote(raw) && raw.len() >= 2 {
        &raw[1..raw.len() - 1]
    } else {
        raw
    };
    let meaningful_len = core
        .chars()
        .filter(|c| c.is_alphanumeric() || *c == '_' || *c == '-' || *c == '.')
        .count() as i64;
    score += meaningful_len * 24;

    if regex_mode {
        if raw.starts_with('^') {
            score += 1200;
        }
        if raw.ends_with('$') {
            score += 1200;
        }
        if raw.contains(".*") || raw.contains(".+") {
            score -= 900;
        }
        if raw.contains('|') {
            score -= 600;
        }
        let heavy_meta = raw
            .chars()
            .filter(|c| matches!(c, '[' | ']' | '(' | ')' | '{' | '}' | '?' | '+'))
            .count() as i64;
        score -= heavy_meta * 60;
        return score;
    }

    if is_wrapped_quote(raw) {
        score += 2200;
    }
    if raw.starts_with('/') && raw.ends_with('/') {
        score += 1700;
    } else if raw.starts_with('/') || (raw != "/" && raw.ends_with('/')) {
        score += 900;
    }

    let stars = raw.matches('*').count() as i64;
    if stars > 0 {
        score -= stars * 500;
        if raw == "*" {
            score -= 5000;
        }
    } else {
        score += 300;
    }

    score
}

fn canonical_path(raw: &str) -> Option<String> {
    let p = Path::new(raw);
    if p.is_dir() {
        fs::canonicalize(p)
            .ok()
            .map(|x| x.to_string_lossy().to_string())
    } else {
        None
    }
}

fn parse_search_dir(raw: &str, regex_mode: bool, force_pattern_mode: bool) -> SearchDirMode {
    if !force_pattern_mode {
        if let Some(p) = canonical_path(raw) {
            return SearchDirMode::Path(p);
        }
    }
    let mut normalized = raw.to_string();
    if normalized != "/" {
        normalized = normalized.trim_end_matches('/').to_string();
    }
    if is_wrapped_quote(raw) {
        let inner = raw[1..raw.len() - 1].to_string();
        if !force_pattern_mode {
            if let Some(p) = canonical_path(&inner) {
                return SearchDirMode::Path(p);
            }
        }
        let mut pattern_inner = inner.trim_start_matches('/').to_string();
        if pattern_inner != "/" {
            pattern_inner = pattern_inner.trim_end_matches('/').to_string();
        }
        let rx = if regex_mode {
            pattern_inner
        } else {
            wildcard_to_regex(&pattern_inner)
        };
        return SearchDirMode::Pattern(rx);
    }
    if regex_mode {
        return SearchDirMode::Pattern(normalized);
    }
    if raw.starts_with('/') && raw.ends_with('/') {
        return SearchDirMode::Pattern(format!("^{}$", to_regex_fragment(&raw[1..raw.len() - 1])));
    }
    if raw.starts_with("./") && raw.ends_with('/') {
        return SearchDirMode::Pattern(format!("^{}$", to_regex_fragment(&raw[2..raw.len() - 1])));
    }
    if raw.starts_with('/') {
        return SearchDirMode::Pattern(format!(
            "^{}",
            to_regex_fragment(raw.trim_start_matches('/'))
        ));
    }
    if raw.starts_with("./") {
        return SearchDirMode::Pattern(format!(
            "^{}",
            to_regex_fragment(raw.trim_start_matches("./"))
        ));
    }
    if raw != "/" && raw.ends_with('/') {
        return SearchDirMode::Pattern(format!(
            "{}$",
            to_regex_fragment(raw.trim_end_matches('/'))
        ));
    }
    if normalized.contains('*') {
        return SearchDirMode::Pattern(wildcard_to_regex(&normalized));
    }
    SearchDirMode::Pattern(to_regex_fragment(&normalized))
}

fn expand_home_path(raw: &str) -> String {
    if raw == "~" {
        return env::var("HOME").unwrap_or_else(|_| raw.to_string());
    }
    if let Some(rest) = raw.strip_prefix("~/") {
        if let Ok(home) = env::var("HOME") {
            return format!("{}/{}", home, rest);
        }
    }
    raw.to_string()
}

fn is_implicit_content_path_token(raw: &str) -> bool {
    raw.starts_with('/')
        || raw.starts_with("./")
        || raw.starts_with("../")
        || raw.starts_with("~/")
        || raw.contains('/')
}

fn is_explicit_search_dir_selector(raw: &str) -> bool {
    if is_wrapped_quote(raw) {
        return true;
    }
    if raw.contains('*') {
        return true;
    }
    if (raw.starts_with('/') || raw.starts_with("./")) && raw.ends_with('/') {
        return true;
    }
    if raw.starts_with('/') || raw.starts_with("./") {
        return true;
    }
    raw != "/" && raw.ends_with('/')
}

fn resolve_literal_search_root(raw: &str) -> Result<PathBuf, String> {
    let expanded = expand_home_path(raw);
    let path = PathBuf::from(expanded);
    if path.is_dir() {
        Ok(path)
    } else {
        Err(format!("--path target '{}' is not an existing directory", raw))
    }
}

fn contains_all_spec_from_opts(opts: &Options) -> Result<Option<ContainsAllSpec>, String> {
    let implicit_by_terms = if opts.positional.len() >= 3 {
        true
    } else if opts.positional.len() == 2 {
        let first = &opts.positional[0];
        let second = &opts.positional[1];
        !opts.regex_mode
            && !opts.force_pattern_mode
            && !is_wrapped_quote(first)
            && !is_explicit_search_dir_selector(second)
    } else {
        false
    };
    let forced_by_flags = opts.contains_all || opts.path_override.is_some();
    if opts.force_full && !forced_by_flags && !implicit_by_terms {
        return Ok(None);
    }
    if !(forced_by_flags || implicit_by_terms) {
        return Ok(None);
    }
    let mut terms = opts.positional.clone();
    let mut root_raw = opts.path_override.clone();
    if root_raw.is_none() && !terms.is_empty() {
        if let Some(last) = terms.last() {
            if is_implicit_content_path_token(last) {
                root_raw = Some(last.clone());
                terms.pop();
            }
        }
    }
    if terms.is_empty() {
        return Err("contains-all mode requires at least one search term".to_string());
    }
    let root = if let Some(raw) = root_raw {
        resolve_literal_search_root(&raw)?
    } else {
        PathBuf::from(".")
    };
    Ok(Some(ContainsAllSpec { terms, root }))
}

struct PathInfo {
    path: PathBuf,
    is_dir: bool,
}

#[derive(Default)]
struct SimpleIgnoreRules {
    names: HashSet<String>,
    dir_names: HashSet<String>,
}

fn load_simple_ignore_rules(dir: &Path) -> SimpleIgnoreRules {
    let mut rules = SimpleIgnoreRules::default();
    for ignore_name in [".gitignore", ".ignore", ".fdignore"] {
        let path = dir.join(ignore_name);
        let Ok(content) = fs::read_to_string(path) else {
            continue;
        };
        for raw in content.lines() {
            let line = raw.trim();
            if line.is_empty() || line.starts_with('#') || line.starts_with('!') {
                continue;
            }
            let mut token = line;
            let is_dir_only = token.ends_with('/');
            if is_dir_only {
                token = token.trim_end_matches('/');
            }
            if token.is_empty() {
                continue;
            }
            if token.contains('/')
                || token.contains('*')
                || token.contains('?')
                || token.contains('[')
            {
                continue;
            }
            if is_dir_only {
                rules.dir_names.insert(token.to_string());
            } else {
                rules.names.insert(token.to_string());
            }
        }
    }
    rules
}

fn is_simple_ignored_name(name: &str, is_dir: bool, rules: &SimpleIgnoreRules) -> bool {
    rules.names.contains(name) || (is_dir && rules.dir_names.contains(name))
}

fn walk_fast(
    dir: PathBuf,
    re: &Regex,
    is_catch_all: bool,
    tx: &Sender<Vec<PathInfo>>,
    visible_only: bool,
    respect_ignore: bool,
    no_recurse: bool,
    follow_links: bool,
    type_flag: Option<TypeFlag>,
    full_path_match: bool,
    timeout_flag: &Arc<AtomicBool>,
) {
    if timeout_flag.load(Ordering::Relaxed) {
        return;
    }
    let Ok(read_dir) = fs::read_dir(&dir) else {
        return;
    };
    let ignore_rules = if respect_ignore {
        Some(load_simple_ignore_rules(&dir))
    } else {
        None
    };
    let mut subdirs = Vec::new();
    let mut local_buf = Vec::with_capacity(512);
    for entry_res in read_dir {
        let Ok(entry) = entry_res else { continue };
        let name = entry.file_name();
        let name_bytes = name.as_bytes();
        if visible_only && name_bytes.starts_with(b".") {
            continue;
        }
        let Ok(file_type) = entry.file_type() else {
            continue;
        };
        let path = entry.path();
        let is_symlink = file_type.is_symlink();
        let mut is_dir = file_type.is_dir();
        if is_symlink && follow_links {
            if let Ok(meta) = fs::metadata(&path) {
                if meta.is_dir() {
                    is_dir = true;
                }
            }
        }
        let name_lossy = name.to_string_lossy();
        if let Some(rules) = &ignore_rules {
            if is_simple_ignored_name(&name_lossy, is_dir, rules) {
                continue;
            }
        }
        let skip_type = match type_flag {
            Some(TypeFlag::File) => is_dir,
            Some(TypeFlag::Dir) => !is_dir,
            None => false,
        };
        if !skip_type {
            let is_match = if is_catch_all {
                true
            } else {
                let match_target = if full_path_match {
                    path.to_string_lossy()
                } else {
                    name.to_string_lossy()
                };
                re.is_match(&match_target)
            };
            if is_match {
                local_buf.push(PathInfo {
                    path: path.clone(),
                    is_dir,
                });
                if local_buf.len() >= 512 {
                    if tx.send(std::mem::take(&mut local_buf)).is_err() {
                        return;
                    }
                    local_buf.reserve(512);
                }
            }
        }
        if is_dir && !no_recurse {
            if dir.as_os_str().as_bytes() == b"/" {
                if name_bytes == b"proc"
                    || name_bytes == b"sys"
                    || name_bytes == b"dev"
                    || name_bytes == b"run"
                {
                    continue;
                }
            }
            if is_symlink && !follow_links {
                continue;
            }
            subdirs.push(path);
        }
    }
    if !local_buf.is_empty() {
        if tx.send(local_buf).is_err() {
            return;
        }
    }
    subdirs
        .into_par_iter()
        .for_each_with(tx.clone(), |tx_clone, subdir| {
            walk_fast(
                subdir,
                re,
                is_catch_all,
                tx_clone,
                visible_only,
                respect_ignore,
                no_recurse,
                follow_links,
                type_flag,
                full_path_match,
                timeout_flag,
            );
        });
}

fn walk_rayon_worker(
    dir: PathBuf,
    re: &Regex,
    is_catch_all: bool,
    tx: &Sender<Vec<SearchResult>>,
    opts: &Options,
    type_flag: Option<TypeFlag>,
    full_path_match: bool,
    prune_matched_dir_subtrees: bool,
    needs_metadata: bool,
    timeout_flag: &Arc<AtomicBool>,
) {
    if timeout_flag.load(Ordering::Relaxed) {
        return;
    }
    let Ok(read_dir) = fs::read_dir(&dir) else {
        return;
    };
    let ignore_rules = if opts.respect_ignore {
        Some(load_simple_ignore_rules(&dir))
    } else {
        None
    };
    let mut subdirs = Vec::new();
    let mut local_buf = Vec::with_capacity(256);
    for entry_res in read_dir {
        let Ok(entry) = entry_res else { continue };
        let name = entry.file_name();
        let name_lossy = name.to_string_lossy();
        if opts.visible_only && name_lossy.starts_with('.') {
            continue;
        }
        let Ok(file_type) = entry.file_type() else {
            continue;
        };
        let path = entry.path();
        let is_symlink = file_type.is_symlink();
        let mut is_dir = file_type.is_dir();
        if is_symlink && opts.follow_links {
            if let Ok(meta) = fs::metadata(&path) {
                if meta.is_dir() {
                    is_dir = true;
                }
            }
        }
        if let Some(rules) = &ignore_rules {
            if is_simple_ignored_name(&name_lossy, is_dir, rules) {
                continue;
            }
        }
        let skip_type = match type_flag {
            Some(TypeFlag::File) => is_dir,
            Some(TypeFlag::Dir) => !is_dir,
            None => false,
        };
        let mut matched_dir_pruned = false;
        if !skip_type {
            let is_match = if is_catch_all {
                true
            } else {
                if full_path_match {
                    if re.is_match(name_lossy.as_ref()) {
                        true
                    } else {
                        let match_target = path.to_string_lossy();
                        re.is_match(&match_target)
                    }
                } else {
                    re.is_match(name_lossy.as_ref())
                }
            };
            if is_match {
                let mut p_str = path
                    .into_os_string()
                    .into_string()
                    .unwrap_or_else(|os| os.to_string_lossy().into_owned());
                if is_dir && !p_str.ends_with('/') {
                    p_str.push('/');
                }
                local_buf.push(SearchResult {
                    path: p_str,
                    is_dir,
                    is_symlink,
                    metadata: if needs_metadata {
                        entry.metadata().ok()
                    } else {
                        None
                    },
                });

                if local_buf.len() >= 256 {
                    if tx.send(std::mem::take(&mut local_buf)).is_err() {
                        return;
                    }
                    local_buf.reserve(256);
                }
                if is_dir && prune_matched_dir_subtrees {
                    matched_dir_pruned = true;
                }
            }
        }
        if is_dir && !opts.no_recurse {
            if matched_dir_pruned {
                continue;
            }
            if dir.to_str() == Some("/")
                && (name_lossy == "proc"
                    || name_lossy == "sys"
                    || name_lossy == "dev"
                    || name_lossy == "run")
            {
                continue;
            }
            if is_symlink && !opts.follow_links {
                continue;
            }
            subdirs.push(entry.path());
        }
    }
    if !local_buf.is_empty() {
        if tx.send(local_buf).is_err() {
            return;
        }
    }
    subdirs
        .into_par_iter()
        .for_each_with(tx.clone(), |tx_clone, subdir| {
            walk_rayon_worker(
                subdir,
                re,
                is_catch_all,
                tx_clone,
                opts,
                type_flag,
                full_path_match,
                prune_matched_dir_subtrees,
                needs_metadata,
                timeout_flag,
            );
        });
}

fn unescape_proc_mount_field(field: &str) -> String {
    let bytes = field.as_bytes();
    let mut out: Vec<u8> = Vec::with_capacity(bytes.len());
    let mut i = 0usize;
    while i < bytes.len() {
        if bytes[i] == b'\\' && i + 3 < bytes.len() {
            let a = bytes[i + 1];
            let b = bytes[i + 2];
            let c = bytes[i + 3];
            let octal = (b'0'..=b'7').contains(&a)
                && (b'0'..=b'7').contains(&b)
                && (b'0'..=b'7').contains(&c);
            if octal {
                let value = ((a - b'0') << 6) | ((b - b'0') << 3) | (c - b'0');
                out.push(value);
                i += 4;
                continue;
            }
        }
        out.push(bytes[i]);
        i += 1;
    }
    String::from_utf8_lossy(&out).into_owned()
}

fn detect_mount_info(path: &Path) -> Option<MountInfo> {
    let canonical = fs::canonicalize(path).unwrap_or_else(|_| path.to_path_buf());
    let mounts = fs::read_to_string("/proc/mounts").ok()?;
    let mut best: Option<(usize, MountInfo)> = None;
    for line in mounts.lines() {
        let mut parts = line.split_whitespace();
        let (device_raw, mount_point_raw, fs_type) =
            match (parts.next(), parts.next(), parts.next()) {
                (Some(device), Some(mount), Some(fs_type)) => (device, mount, fs_type),
                _ => continue,
            };
        let device = PathBuf::from(unescape_proc_mount_field(device_raw));
        let mount_point = PathBuf::from(unescape_proc_mount_field(mount_point_raw));
        if !canonical.starts_with(&mount_point) {
            continue;
        }
        let mount_len = mount_point.as_os_str().as_bytes().len();
        if best
            .as_ref()
            .map(|(best_len, _)| mount_len > *best_len)
            .unwrap_or(true)
        {
            best = Some((
                mount_len,
                MountInfo {
                    device,
                    mount_point,
                    fs_type: fs_type.to_string(),
                },
            ));
        }
    }
    best.map(|(_, info)| info)
}

fn ntfs_best_filename(
    entry: &ntfs::NtfsIndexEntry<'_, ntfs::indexes::NtfsFileNameIndex>,
) -> Option<String> {
    if let Some(Ok(file_name)) = entry.key() {
        let name = file_name.name().to_string_lossy().to_string();
        if !name.contains('~') || name.len() > 12 {
            return Some(name);
        }
    }
    entry
        .key()
        .and_then(|result| result.ok())
        .map(|file_name| file_name.name().to_string_lossy().to_string())
}

fn ntfs_is_reparse_point(file: &ntfs::NtfsFile, device: &mut fs::File) -> bool {
    let mut attrs = file.attributes();
    while let Some(attr_result) = attrs.next(device) {
        if let Ok(attr_item) = attr_result {
            if let Ok(attr) = attr_item.to_attribute() {
                if let Ok(attr_ty) = attr.ty() {
                    if attr_ty == ntfs::NtfsAttributeType::ReparsePoint {
                        return true;
                    }
                }
            }
        }
    }
    false
}

fn ntfs_file_logical_size(file: &ntfs::NtfsFile, device: &mut fs::File) -> u64 {
    if let Some(data_attr) = file.data(device, "") {
        if let Ok(data_item) = data_attr {
            if let Ok(data_attr_obj) = data_item.to_attribute() {
                if let Ok(value) = data_attr_obj.value(device) {
                    return value.len();
                }
            }
        }
    }
    0
}

fn ntfs_find_subdir_record(
    ntfs: &ntfs::Ntfs,
    device: &mut fs::File,
    start_record: u64,
    rel_path: &Path,
) -> Option<u64> {
    let mut current_record = start_record;
    if rel_path.as_os_str().is_empty() {
        return Some(current_record);
    }
    for component in rel_path.components() {
        let name = match component {
            Component::Normal(name) => name.to_string_lossy().to_string(),
            _ => continue,
        };
        let dir_file = ntfs.file(device, current_record).ok()?;
        let index = dir_file.directory_index(device).ok()?;
        let mut entries = index.entries();
        let mut seen_records = HashSet::<u64>::new();
        let mut next_record: Option<u64> = None;
        while let Some(entry_result) = entries.next(device) {
            let entry = match entry_result {
                Ok(e) => e,
                Err(_) => continue,
            };
            let entry_name = match ntfs_best_filename(&entry) {
                Some(n) => n,
                None => continue,
            };
            if entry_name == "." || entry_name == ".." {
                continue;
            }
            let child_record = entry.file_reference().file_record_number();
            if !seen_records.insert(child_record) {
                continue;
            }
            if entry_name == name {
                next_record = Some(child_record);
                break;
            }
        }
        current_record = next_record?;
    }
    Some(current_record)
}

fn ntfs_scan_subtree_record(
    ntfs: &ntfs::Ntfs,
    device: &mut fs::File,
    top_record: u64,
    count_files: bool,
) -> (u64, u64) {
    let mut total_size = 0u64;
    let mut total_files = 0u64;
    let mut stack = vec![top_record];
    let mut seen_dirs = HashSet::<u64>::new();
    while let Some(current_record) = stack.pop() {
        if !seen_dirs.insert(current_record) {
            continue;
        }
        let dir_file = match ntfs.file(device, current_record) {
            Ok(file) => file,
            Err(_) => continue,
        };
        let index = match dir_file.directory_index(device) {
            Ok(i) => i,
            Err(_) => continue,
        };
        let mut entries = index.entries();
        let mut seen_records = HashSet::<u64>::new();
        while let Some(entry_result) = entries.next(device) {
            let entry = match entry_result {
                Ok(e) => e,
                Err(_) => continue,
            };
            let name = match ntfs_best_filename(&entry) {
                Some(n) => n,
                None => continue,
            };
            if name == "." || name == ".." {
                continue;
            }
            let child_record = entry.file_reference().file_record_number();
            if !seen_records.insert(child_record) {
                continue;
            }
            let child_file = match ntfs.file(device, child_record) {
                Ok(f) => f,
                Err(_) => continue,
            };
            let child_is_dir = child_file.is_directory();
            let child_is_reparse = ntfs_is_reparse_point(&child_file, device);
            if child_is_dir && !child_is_reparse {
                stack.push(child_record);
            } else if !child_is_reparse {
                total_size = total_size.saturating_add(ntfs_file_logical_size(&child_file, device));
                if count_files {
                    total_files = total_files.saturating_add(1);
                }
            }
        }
    }
    (total_size, total_files)
}

fn get_dir_stats_ntfs_mft(path: &Path, count_files: bool) -> io::Result<(u64, u64)> {
    let canonical_base = fs::canonicalize(path).unwrap_or_else(|_| path.to_path_buf());
    let mount = detect_mount_info(&canonical_base)
        .ok_or_else(|| io::Error::other("mount detection failed"))?;
    if !NTFS_FS_TYPES.iter().any(|t| mount.fs_type == *t) {
        return Err(io::Error::other("not ntfs"));
    }
    let mut device = fs::File::open(&mount.device)?;
    let ntfs = ntfs::Ntfs::new(&mut device).map_err(|err| io::Error::other(err.to_string()))?;
    let root_dir = ntfs
        .root_directory(&mut device)
        .map_err(|err| io::Error::other(err.to_string()))?;
    let root_record = root_dir.file_record_number();
    let rel_path = canonical_base
        .strip_prefix(&mount.mount_point)
        .unwrap_or(Path::new(""));
    let base_record = ntfs_find_subdir_record(&ntfs, &mut device, root_record, rel_path)
        .ok_or_else(|| io::Error::other("base directory not found in mft"))?;
    Ok(ntfs_scan_subtree_record(
        &ntfs,
        &mut device,
        base_record,
        count_files,
    ))
}

fn get_dir_stats_walk(path: &str, count_files: bool) -> (u64, u64) {
    let mut bytes = 0u64;
    let mut files = 0u64;
    for entry_res in WalkDir::new(path).follow_links(false) {
        let Ok(entry) = entry_res else { continue };
        let file_type = entry.file_type();
        if !file_type.is_file() {
            continue;
        }
        if let Ok(meta) = entry.metadata() {
            bytes = bytes.saturating_add(meta.len());
        }
        if count_files {
            files = files.saturating_add(1);
        }
    }
    (bytes, files)
}

fn get_dir_stats_native(path: &str, count_files: bool) -> (u64, u64) {
    let path_buf = PathBuf::from(path);
    let ntfs_debug = env::var_os("UNEARTH_NTFS_DEBUG").is_some();
    match get_dir_stats_ntfs_mft(&path_buf, count_files) {
        Ok(stats) => {
            if ntfs_debug {
                eprintln!("unearth: NTFS MFT fast path enabled for {}", path);
            }
            stats
        }
        Err(err) => {
            if ntfs_debug
                && detect_mount_info(&path_buf)
                    .as_ref()
                    .map(|m| NTFS_FS_TYPES.iter().any(|t| m.fs_type == *t))
                    .unwrap_or(false)
            {
                eprintln!("unearth: NTFS MFT fast path unavailable for {}: {}", path, err);
            }
            get_dir_stats_walk(path, count_files)
        }
    }
}

fn get_dir_bytes_native_serial(path: &str) -> u64 {
    if let Ok((bytes, _)) = get_dir_stats_ntfs_mft(Path::new(path), false) {
        return bytes;
    }
    let mut bytes = 0u64;
    for entry_res in WalkDir::new(path)
        .follow_links(false)
        .parallelism(Parallelism::Serial)
    {
        let Ok(entry) = entry_res else { continue };
        if !entry.file_type().is_file() {
            continue;
        }
        if let Ok(meta) = entry.metadata() {
            bytes = bytes.saturating_add(meta.len());
        }
    }
    bytes
}

fn normalize_dir_key(path: &str) -> String {
    if path == "/" {
        "/".to_string()
    } else {
        path.trim_end_matches('/').to_string()
    }
}

fn format_size_iec(bytes: u64) -> String {
    let units = ["B", "KiB", "MiB", "GiB", "TiB"];
    let mut unit = 0usize;
    let mut size = bytes as f64;
    while size >= 1024.0 && unit < units.len() - 1 {
        size /= 1024.0;
        unit += 1;
    }
    if unit == 0 {
        format!("{} {}", bytes, units[unit])
    } else if size >= 100.0 {
        format!("{:.0} {}", size, units[unit])
    } else if size >= 10.0 {
        format!("{:.1} {}", size, units[unit])
    } else {
        format!("{:.2} {}", size, units[unit])
    }
}

fn format_size_compact_3(bytes: u64) -> String {
    let units = ["B", "K", "M", "G", "T"];
    let mut unit = 0usize;
    let mut size = bytes as f64;
    while size >= 1024.0 && unit < units.len() - 1 {
        size /= 1024.0;
        unit += 1;
    }
    if unit == 0 {
        format!("{}{}", bytes, units[unit])
    } else {
        let decimals = if size >= 1000.0 {
            0
        } else if size >= 100.0 {
            1
        } else if size >= 10.0 {
            2
        } else {
            3
        };
        let factor = 10f64.powi(decimals as i32);
        let truncated = (size * factor).floor() / factor;
        format!("{:.*}{}", decimals, truncated, units[unit])
    }
}

fn should_use_recursive_dirsize(item: &SearchResult, opts: &Options) -> bool {
    if !item.is_dir || item.is_symlink {
        return false;
    }
    opts.sizes || opts.long_extended || !opts.no_recurse
}

fn size_bytes_for_result(item: &SearchResult, opts: &Options, cache: &mut DirStatsCache) -> u64 {
    if should_use_recursive_dirsize(item, opts) {
        return get_dirsize_bytes(&item.path, cache).unwrap_or(0);
    }
    item.metadata.as_ref().map(|m| m.len()).unwrap_or(0)
}

fn precompute_dirsize_cache(items: &[SearchResult], opts: &Options, cache: &mut DirStatsCache) {
    let need_recursive = opts.sizes
        || opts.long_extended
        || matches!(opts.sort_field, Some(SortField::Size) if !opts.no_recurse);
    if !need_recursive {
        return;
    }
    let mut needed_dirs: Vec<String> = items
        .iter()
        .filter(|item| should_use_recursive_dirsize(item, opts))
        .map(|item| normalize_dir_key(&item.path))
        .collect();
    needed_dirs.sort();
    needed_dirs.dedup();
    if opts.long_extended {
        for dir in needed_dirs {
            let _ = get_dirsize_stats(&dir, cache);
        }
    } else {
        let mut missing = Vec::new();
        for dir in needed_dirs {
            if !cache.bytes_map.contains_key(&dir) && !cache.map.contains_key(&dir) {
                missing.push(dir);
            }
        }
        let computed: Vec<(String, u64)> = missing
            .into_par_iter()
            .map(|dir| {
                let bytes = get_dir_bytes_native_serial(&dir);
                (dir, bytes)
            })
            .collect();
        for (dir, bytes) in computed {
            cache.bytes_map.insert(dir, bytes);
        }
    }
}

fn sort_results(
    mut items: Vec<SearchResult>,
    opts: &Options,
    cache: &mut DirStatsCache,
) -> Vec<SearchResult> {
    let Some(field) = opts.sort_field else {
        return items;
    };
    let order = opts.sort_order.unwrap_or(SortOrder::Asc);
    items.sort_by(|a, b| {
        let ord = match field {
            SortField::Date => {
                let da = a
                    .metadata
                    .as_ref()
                    .and_then(|m| m.modified().ok())
                    .and_then(|t| t.duration_since(std::time::UNIX_EPOCH).ok())
                    .map(|d| d.as_secs())
                    .unwrap_or(0);
                let db = b
                    .metadata
                    .as_ref()
                    .and_then(|m| m.modified().ok())
                    .and_then(|t| t.duration_since(std::time::UNIX_EPOCH).ok())
                    .map(|d| d.as_secs())
                    .unwrap_or(0);
                da.cmp(&db)
            }
            SortField::Size => {
                let sa = size_bytes_for_result(a, opts, cache);
                let sb = size_bytes_for_result(b, opts, cache);
                sa.cmp(&sb)
            }
            SortField::Name => a.path.to_lowercase().cmp(&b.path.to_lowercase()),
        };
        match order {
            SortOrder::Asc => ord,
            SortOrder::Desc => ord.reverse(),
        }
    });
    items
}

fn absolute_paths_transform(mut items: Vec<SearchResult>, opts: &Options) -> Vec<SearchResult> {
    if !opts.absolute_paths {
        return items;
    }
    let cwd_abs = env::current_dir()
        .ok()
        .and_then(|p| fs::canonicalize(p).ok())
        .unwrap_or_else(|| env::current_dir().unwrap_or_else(|_| PathBuf::from(".")));
    let cwd_abs_str = cwd_abs.to_string_lossy().to_string();
    for item in items.iter_mut() {
        if !item.path.starts_with('/') {
            item.path = format!("{}/{}", cwd_abs_str, item.path.trim_start_matches("./"));
        }
    }
    items
}

fn parent_pid() -> Option<u32> {
    let stat = fs::read_to_string("/proc/self/stat").ok()?;
    let (_, tail) = stat.rsplit_once(") ")?;
    let mut fields = tail.split_whitespace();
    let _state = fields.next()?;
    let ppid = fields.next()?.parse::<u32>().ok()?;
    Some(ppid)
}

fn fish_pid() -> String {
    if let Ok(v) = env::var("FISH_PID") {
        if !v.is_empty() && v.chars().all(|c| c.is_ascii_digit()) {
            return v;
        }
    }
    if let Ok(v) = env::var("fish_pid") {
        if !v.is_empty() && v.chars().all(|c| c.is_ascii_digit()) {
            return v;
        }
    }
    if let Some(ppid) = parent_pid() {
        return ppid.to_string();
    }
    std::process::id().to_string()
}

fn init_raw_cache_state() -> Option<RawCacheState> {
    let user = env::var("USER").unwrap_or_else(|_| "unknown".to_string());
    let pid = fish_pid();
    let cache_dir = format!("/tmp/fzf-history-{}", user);
    let dirs_file = format!("{}/universal-last-dirs-{}", cache_dir, pid);
    let files_file = format!("{}/universal-last-files-{}", cache_dir, pid);
    fs::create_dir_all(&cache_dir).ok()?;
    let dirs = BufWriter::new(File::create(&dirs_file).ok()?);
    let files = BufWriter::new(File::create(&files_file).ok()?);
    Some(RawCacheState {
        dirs,
        files,
        seen_dirs: HashSet::new(),
        seen_files: HashSet::new(),
    })
}

fn cache_raw_record_path(path: &str, is_dir: bool, state: &mut RawCacheState) {
    if is_dir {
        let mut p = path.to_string();
        if !p.ends_with('/') {
            p.push('/');
        }
        if state.seen_dirs.insert(p.clone()) {
            let _ = writeln!(state.dirs, "{}", p);
        }
    } else {
        if state.seen_files.insert(path.to_string()) {
            let _ = writeln!(state.files, "{}", path);
        }
    }
    let mut parent = path.trim_end_matches('/').to_string();
    if let Some(idx) = parent.rfind('/') {
        parent = parent[..idx].to_string();
        if parent.is_empty() {
            parent = "/".to_string();
        } else if !parent.ends_with('/') {
            parent.push('/');
        }
    } else {
        parent = "./".to_string();
    }
    if state.seen_dirs.insert(parent.clone()) {
        let _ = writeln!(state.dirs, "{}", parent);
    }
}

fn cache_transform(items: &Vec<SearchResult>, opts: &Options) {
    if !opts.cache_output {
        return;
    }
    let Some(mut state) = init_raw_cache_state() else {
        return;
    };
    for item in items {
        cache_raw_record_path(&item.path, item.is_dir, &mut state);
    }
    let _ = state.dirs.flush();
    let _ = state.files.flush();
}

fn get_dirsize_stats(path: &str, cache: &mut DirStatsCache) -> Option<DirStats> {
    let key = normalize_dir_key(path);
    let walk_path = if key == "/" { "/" } else { key.as_str() };
    if let Some(v) = cache.map.get(&key) {
        return Some(v.clone());
    }
    let (bytes, files) = get_dir_stats_native(walk_path, true);
    let stats = DirStats {
        files,
        bytes,
        human: format_size_iec(bytes),
    };
    cache.bytes_map.insert(key.clone(), bytes);
    cache.map.insert(key, stats.clone());
    Some(stats)
}

fn get_dirsize_bytes(path: &str, cache: &mut DirStatsCache) -> Option<u64> {
    let key = normalize_dir_key(path);
    let walk_path = if key == "/" { "/" } else { key.as_str() };
    if let Some(v) = cache.bytes_map.get(&key) {
        return Some(*v);
    }
    if let Some(v) = cache.map.get(&key) {
        cache.bytes_map.insert(key.clone(), v.bytes);
        return Some(v.bytes);
    }
    let (bytes, _) = get_dir_stats_native(walk_path, false);
    cache.bytes_map.insert(key, bytes);
    Some(bytes)
}

fn add_info_transform(
    items: Vec<SearchResult>,
    opts: &Options,
    cache: &mut DirStatsCache,
    use_style: bool,
    add_decorator: bool,
    colors: &ColorSpec,
    highlight: Option<&HighlightSpec>,
) -> Vec<String> {
    if !opts.long_format {
        return items.into_iter().map(|i| i.path).collect();
    }
    let mut out = Vec::new();
    for item in items {
        if let Some(meta) = &item.metadata {
            let dt: DateTime<Local> = meta
                .modified()
                .unwrap_or_else(|_| std::time::SystemTime::now())
                .into();
            let dt_str = dt.format("%Y-%m-%d %H:%M:%S").to_string();
            let mut human_size = format_size_iec(meta.len());
            let mut extra = String::new();
            if opts.long_extended {
                if item.is_symlink {
                    let link_path = item.path.trim_end_matches('/');
                    if fs::metadata(link_path).map(|m| m.is_dir()).unwrap_or(false) {
                        human_size = format_size_iec(meta.len());
                        extra = " 0".to_string();
                    }
                } else if item.is_dir {
                    if let Some(stats) = get_dirsize_stats(&item.path, cache) {
                        human_size = stats.human;
                        extra = format!(" {}", stats.files);
                    }
                }
            }
            let path_display = render_styled_path(
                &item,
                use_style,
                add_decorator,
                colors,
                opts,
                highlight,
            );
            out.push(format!(
                "{} {}{} {}",
                dt_str, human_size, extra, path_display
            ));
        } else {
            out.push(item.path);
        }
    }
    out
}

fn sizes_transform(
    items: Vec<SearchResult>,
    opts: &Options,
    cache: &mut DirStatsCache,
    use_style: bool,
    add_decorator: bool,
    colors: &ColorSpec,
    highlight: Option<&HighlightSpec>,
) -> Vec<String> {
    let mut out = Vec::with_capacity(items.len());
    for item in items {
        let bytes = size_bytes_for_result(&item, opts, cache);
        let compact = format_size_compact_3(bytes);
        let path_display = render_styled_path(
            &item,
            use_style,
            add_decorator,
            colors,
            opts,
            highlight,
        );
        out.push(format!("{}\t{}", compact, path_display));
    }
    out
}

fn counts_summary_transform(items: Vec<SearchResult>, is_tty: bool) -> Vec<String> {
    let mut counts: HashMap<String, u64> = HashMap::new();
    for item in items {
        let mut p = item.path.trim_end_matches('/').to_string();
        let d = if let Some(idx) = p.rfind('/') {
            p.truncate(idx);
            if p.is_empty() {
                "/".to_string()
            } else {
                p
            }
        } else {
            ".".to_string()
        };
        *counts.entry(d).or_insert(0) += 1;
    }
    let mut rows: Vec<(String, u64)> = counts.into_iter().collect();
    rows.sort_by(|a, b| b.1.cmp(&a.1).then(a.0.cmp(&b.0)));
    let mut out = Vec::new();
    if is_tty {
        out.push(format!("{:>7}  {}", "COUNT", "FOLDER"));
    }
    for (folder, n) in rows {
        out.push(format!("{:>7}  {}", n, folder));
    }
    out
}

fn parse_ls_colors() -> ColorSpec {
    let mut by_key = HashMap::new();
    let mut globs = Vec::new();
    let (mut color_dir, mut color_link, mut color_exec) = (
        "01;34".to_string(),
        "01;36".to_string(),
        "01;32".to_string(),
    );
    if let Ok(spec) = env::var("LS_COLORS") {
        for entry in spec.split(':') {
            if let Some((k, v)) = entry.split_once('=') {
                if k.starts_with('*') {
                    let mut rx = String::from("^");
                    for ch in k.chars() {
                        match ch {
                            '*' => rx.push_str(".*"),
                            '?' => rx.push('.'),
                            '.' | '+' | '(' | ')' | '[' | ']' | '{' | '}' | '^' | '$' | '|'
                            | '\\' => {
                                rx.push('\\');
                                rx.push(ch);
                            }
                            _ => rx.push(ch),
                        }
                    }
                    rx.push('$');
                    if let Ok(re) = Regex::new(&rx) {
                        globs.push((re, v.to_string()));
                    }
                } else {
                    by_key.insert(k.to_string(), v.to_string());
                    match k {
                        "di" => color_dir = v.to_string(),
                        "ln" => color_link = v.to_string(),
                        "ex" => color_exec = v.to_string(),
                        _ => {}
                    }
                }
            }
        }
    }
    ColorSpec {
        by_key,
        globs,
        color_prefix_dir: "38;2;255;255;255".to_string(),
        color_dir,
        color_link,
        color_exec,
    }
}

fn default_color_spec() -> ColorSpec {
    ColorSpec {
        by_key: HashMap::new(),
        globs: Vec::new(),
        color_prefix_dir: "38;2;255;255;255".to_string(),
        color_dir: "01;34".to_string(),
        color_link: "01;36".to_string(),
        color_exec: "01;32".to_string(),
    }
}

fn color_code_for_path(res: &SearchResult, colors: &ColorSpec) -> String {
    let ln_code = colors
        .by_key
        .get("ln")
        .cloned()
        .unwrap_or_else(|| colors.color_link.clone());
    let symlink_target_mode = res.is_symlink && ln_code == "target";
    if res.is_symlink && !symlink_target_mode {
        return ln_code;
    }
    if res.is_dir
        || (symlink_target_mode && res.metadata.as_ref().map(|m| m.is_dir()).unwrap_or(false))
    {
        return colors
            .by_key
            .get("di")
            .cloned()
            .unwrap_or_else(|| colors.color_dir.clone());
    }
    let base = res.path.rsplit('/').next().unwrap_or("");
    for (re, val) in &colors.globs {
        if re.is_match(base) {
            return val.clone();
        }
    }
    if let Some(m) = &res.metadata {
        if m.permissions().mode() & 0o111 != 0 {
            return colors.color_exec.clone();
        }
    }
    String::new()
}

fn decorator_for_res(res: &SearchResult) -> Option<char> {
    if res.is_symlink {
        return Some('@');
    }
    if res.is_dir {
        return if res.path.ends_with('/') {
            None
        } else {
            Some('/')
        };
    }
    if let Some(m) = &res.metadata {
        let ft = m.file_type();
        if ft.is_fifo() {
            return Some('|');
        }
        if ft.is_socket() {
            return Some('=');
        }
        if m.permissions().mode() & 0o111 != 0 {
            return Some('*');
        }
    }
    None
}

const MATCH_HIGHLIGHT_CODE: &str = "1;91";

fn compile_highlight_spec(patterns: &[(String, bool)]) -> Result<HighlightSpec, String> {
    let mut prefix_rules = Vec::new();
    let mut leaf_rules = Vec::new();
    for (raw, full_path_match) in patterns {
        let re = RegexBuilder::new(raw)
            .case_insensitive(true)
            .build()
            .map_err(|e| format!("Invalid regex: {}", e))?;
        if *full_path_match {
            prefix_rules.push(re.clone());
        }
        leaf_rules.push(re);
    }
    Ok(HighlightSpec {
        prefix_rules,
        leaf_rules,
    })
}

fn merge_match_ranges(mut ranges: Vec<(usize, usize)>) -> Vec<(usize, usize)> {
    if ranges.is_empty() {
        return ranges;
    }
    ranges.sort_by(|a, b| a.0.cmp(&b.0).then_with(|| a.1.cmp(&b.1)));
    let mut merged = Vec::with_capacity(ranges.len());
    let mut current = ranges[0];
    for (start, end) in ranges.into_iter().skip(1) {
        if start <= current.1 {
            current.1 = current.1.max(end);
        } else {
            merged.push(current);
            current = (start, end);
        }
    }
    merged.push(current);
    merged
}

fn colorize_segment_with_highlights(
    text: &str,
    base_code: Option<&str>,
    rules: &[Regex],
) -> String {
    if text.is_empty() {
        return String::new();
    }
    let mut ranges = Vec::new();
    for re in rules {
        for m in re.find_iter(text) {
            ranges.push((m.start(), m.end()));
        }
    }
    let ranges = merge_match_ranges(ranges);
    if ranges.is_empty() {
        return match base_code {
            Some(code) => format!("\x1b[{}m{}\x1b[0m", code, text),
            None => text.to_string(),
        };
    }
    let mut out = String::with_capacity(text.len() + ranges.len() * 16);
    if let Some(code) = base_code {
        out.push_str("\x1b[");
        out.push_str(code);
        out.push('m');
    }
    let mut cursor = 0;
    for (start, end) in ranges {
        if start > cursor {
            out.push_str(&text[cursor..start]);
        }
        out.push_str("\x1b[");
        out.push_str(MATCH_HIGHLIGHT_CODE);
        out.push('m');
        out.push_str(&text[start..end]);
        out.push_str("\x1b[0m");
        if let Some(code) = base_code {
            out.push_str("\x1b[");
            out.push_str(code);
            out.push('m');
        }
        cursor = end;
    }
    if cursor < text.len() {
        out.push_str(&text[cursor..]);
    }
    out.push_str("\x1b[0m");
    out
}

fn render_styled_path(
    res: &SearchResult,
    use_style: bool,
    add_decorator: bool,
    colors: &ColorSpec,
    opts: &Options,
    highlight: Option<&HighlightSpec>,
) -> String {
    let mut display_path = res.path.clone();
    if add_decorator {
        if let Some(d) = decorator_for_res(res) {
            if !display_path.ends_with(d) {
                display_path.push(d);
            }
        }
    }
    let (prefix, leaf) = if display_path.ends_with('/') {
        let core = display_path.trim_end_matches('/');
        if let Some((p, l)) = core.rsplit_once('/') {
            (format!("{}/", p), format!("{}/", l))
        } else {
            (String::new(), display_path.clone())
        }
    } else if let Some((p, l)) = display_path.rsplit_once('/') {
        (format!("{}/", p), l.to_string())
    } else {
        (String::new(), display_path.clone())
    };
    if !use_style {
        if let Some(spec) = highlight {
            let mut plain = String::new();
            if !prefix.is_empty() {
                plain.push_str(&colorize_segment_with_highlights(
                    &prefix,
                    None,
                    &spec.prefix_rules,
                ));
            }
            plain.push_str(&colorize_segment_with_highlights(&leaf, None, &spec.leaf_rules));
            return plain;
        }
        return display_path;
    }
    let leaf_code = color_code_for_path(res, colors);
    let leaf_colored = if let Some(spec) = highlight {
        colorize_segment_with_highlights(
            &leaf,
            if leaf_code.is_empty() {
                None
            } else {
                Some(leaf_code.as_str())
            },
            &spec.leaf_rules,
        )
    } else if leaf_code.is_empty() {
        leaf.clone()
    } else {
        format!("\x1b[{}m{}\x1b[0m", leaf_code, leaf)
    };
    let prefix_colored = if prefix.is_empty() {
        String::new()
    } else if let Some(spec) = highlight {
        colorize_segment_with_highlights(
            &prefix,
            Some(colors.color_prefix_dir.as_str()),
            &spec.prefix_rules,
        )
    } else {
        format!("\x1b[{}m{}\x1b[0m", colors.color_prefix_dir, prefix)
    };
    let mut final_str = if prefix.is_empty() {
        leaf_colored.clone()
    } else {
        format!("{}{}", prefix_colored, leaf_colored)
    };
    if opts.hyperlinks {
        let mut abs_prefix = prefix.clone();
        if !abs_prefix.is_empty() && !abs_prefix.starts_with('/') {
            if let Ok(cwd) = env::current_dir() {
                abs_prefix = format!("{}/{}", cwd.display(), abs_prefix.trim_start_matches("./"));
            }
        }
        let mut abs_leaf = res.path.clone();
        if !abs_leaf.starts_with('/') {
            if let Ok(cwd) = env::current_dir() {
                abs_leaf = format!("{}/{}", cwd.display(), abs_leaf.trim_start_matches("./"));
            }
        }
        if prefix.is_empty() {
            final_str = format!(
                "\x1b]8;;file://{}\x1b\\{}\x1b]8;;\x1b\\",
                abs_leaf, final_str
            );
        } else {
            final_str = format!(
                "\x1b]8;;file://{}\x1b\\{}\x1b]8;;\x1b\\\x1b]8;;file://{}\x1b\\{}\x1b]8;;\x1b\\",
                abs_prefix, prefix_colored, abs_leaf, leaf_colored
            );
        }
    }
    final_str
}

fn final_transform(
    items: Vec<SearchResult>,
    opts: &Options,
    use_style: bool,
    stdout_is_tty: bool,
    colors: &ColorSpec,
    cache: &mut DirStatsCache,
    highlight: Option<&HighlightSpec>,
) -> Vec<String> {
    let items = absolute_paths_transform(items, opts);
    cache_transform(&items, opts);
    let add_decorators = stdout_is_tty || opts.classify;
    if opts.counts {
        return counts_summary_transform(items, use_style);
    }
    precompute_dirsize_cache(&items, opts, cache);
    let items = sort_results(items, opts, cache);
    if opts.sizes {
        return sizes_transform(items, opts, cache, use_style, add_decorators, colors, highlight);
    }
    let mut out = Vec::new();
    if opts.long_format {
        for item_str in add_info_transform(
            items,
            opts,
            cache,
            use_style,
            add_decorators,
            colors,
            highlight,
        ) {
            out.push(item_str);
        }
    } else {
        for res in items {
            out.push(render_styled_path(
                &res,
                use_style,
                add_decorators,
                colors,
                opts,
                highlight,
            ));
        }
    }
    out
}

fn run_standard(
    opts: &Options,
    cache: &mut DirStatsCache,
    colors: &ColorSpec,
) -> Result<Vec<String>, String> {
    let stdout_is_tty = io::stdout().is_terminal();
    let use_style = style_enabled(opts, stdout_is_tty);
    let name = parse_name_pattern(&opts.positional[0], opts.regex_mode);
    let mut type_flag = name.type_flag;
    if opts.force_dir {
        type_flag = Some(TypeFlag::Dir);
    }
    if opts.force_file {
        type_flag = Some(TypeFlag::File);
    }
    let stream_direct = can_stream_direct(opts, use_style);
    let re = RegexBuilder::new(&name.regex)
        .case_insensitive(true)
        .build()
        .map_err(|e| format!("Invalid regex: {}", e))?;
    let is_catch_all = name.regex == ".*" || name.regex == "^.*$";
    let timeout_dur = opts.timeout_dur;
    let timeout_triggered = Arc::new(AtomicBool::new(false));
    let timeout_clone = timeout_triggered.clone();
    std::thread::spawn(move || {
        std::thread::sleep(timeout_dur);
        timeout_clone.store(true, Ordering::Relaxed);
    });

    if stream_direct {
        let (tx, rx) = unbounded::<Vec<PathInfo>>();
        let opts_clone = opts.clone();
        let timeout_fast = timeout_triggered.clone();
        if opts.positional.len() == 1 {
            rayon::spawn(move || {
                walk_fast(
                    PathBuf::from("."),
                    &re,
                    is_catch_all,
                    &tx,
                    opts_clone.visible_only,
                    opts_clone.respect_ignore,
                    opts_clone.no_recurse,
                    opts_clone.follow_links,
                    type_flag,
                    false,
                    &timeout_fast,
                )
            });
        } else {
            let p_raw = &opts.positional[1];
            let sd = parse_search_dir(p_raw, opts.regex_mode, opts.force_pattern_mode);
            rayon::spawn(move || match sd {
                SearchDirMode::Path(p) => walk_fast(
                    PathBuf::from(p),
                    &re,
                    is_catch_all,
                    &tx,
                    opts_clone.visible_only,
                    opts_clone.respect_ignore,
                    opts_clone.no_recurse,
                    opts_clone.follow_links,
                    type_flag,
                    false,
                    &timeout_fast,
                ),
                SearchDirMode::Pattern(sd_rx) => {
                    let mut roots = Vec::new();
                    let (rtx, rrx) = unbounded::<Vec<PathInfo>>();
                    let sd_re = RegexBuilder::new(&sd_rx)
                        .case_insensitive(true)
                        .build()
                        .unwrap();
                    walk_fast(
                        PathBuf::from("/"),
                        &sd_re,
                        false,
                        &rtx,
                        opts_clone.visible_only,
                        opts_clone.respect_ignore,
                        false,
                        opts_clone.follow_links,
                        Some(TypeFlag::Dir),
                        false,
                        &timeout_fast,
                    );
                    drop(rtx);
                    for chunk in rrx {
                        for info in chunk {
                            roots.push(info.path);
                        }
                    }
                    roots.into_par_iter().for_each_with(tx.clone(), |tx_c, d| {
                        walk_fast(
                            d,
                            &re,
                            is_catch_all,
                            tx_c,
                            opts_clone.visible_only,
                            opts_clone.respect_ignore,
                            opts_clone.no_recurse,
                            opts_clone.follow_links,
                            type_flag,
                            false,
                            &timeout_fast,
                        );
                    });
                }
            });
        }

        let stdout = io::stdout();
        let mut lock = BufWriter::with_capacity(128 * 1024, stdout.lock());
        let mut cache_state = if opts.cache_output {
            init_raw_cache_state()
        } else {
            None
        };

        for chunk in rx {
            for info in chunk {
                if let Some(state) = cache_state.as_mut() {
                    cache_raw_record_path(&info.path.to_string_lossy(), info.is_dir, state);
                }
                let _ = lock.write_all(info.path.as_os_str().as_bytes());
                if info.is_dir && !info.path.as_os_str().as_bytes().ends_with(b"/") {
                    let _ = lock.write_all(b"/");
                }
                let _ = lock.write_all(b"\n");
            }
        }

        if let Some(mut state) = cache_state {
            let _ = state.dirs.flush();
            let _ = state.files.flush();
        }
        let _ = lock.flush();
        return Ok(Vec::new());
    }

    let mut results = Vec::new();
    let needs_metadata = opts.long_format || opts.sort_field.is_some() || opts.sizes;
    let (tx, rx) = unbounded::<Vec<SearchResult>>();
    let opts_clone = opts.clone();
    if opts.positional.len() == 1 {
        rayon::spawn(move || {
            walk_rayon_worker(
                PathBuf::from("."),
                &re,
                is_catch_all,
                &tx,
                &opts_clone,
                type_flag,
                false,
                false,
                needs_metadata,
                &timeout_triggered,
            )
        });
    } else {
        let p_raw = &opts.positional[1];
        match parse_search_dir(p_raw, opts.regex_mode, opts.force_pattern_mode) {
            SearchDirMode::Path(p) => rayon::spawn(move || {
                walk_rayon_worker(
                    PathBuf::from(p),
                    &re,
                    is_catch_all,
                    &tx,
                    &opts_clone,
                    type_flag,
                    false,
                    false,
                    needs_metadata,
                    &timeout_triggered,
                )
            }),
            SearchDirMode::Pattern(sd_rx) => {
                rayon::spawn(move || {
                    let mut roots = Vec::new();
                    let (rtx, rrx) = unbounded::<Vec<SearchResult>>();
                    let sd_re = RegexBuilder::new(&sd_rx)
                        .case_insensitive(true)
                        .build()
                        .unwrap();
                    walk_rayon_worker(
                        PathBuf::from("/"),
                        &sd_re,
                        false,
                        &rtx,
                        &opts_clone,
                        Some(TypeFlag::Dir),
                        false,
                        false,
                        false,
                        &timeout_triggered,
                    );
                    drop(rtx);
                    for chunk in rrx {
                        for r in chunk {
                            roots.push(PathBuf::from(r.path));
                        }
                    }
                    roots.into_par_iter().for_each_with(tx.clone(), |tx_c, d| {
                        walk_rayon_worker(
                            d,
                            &re,
                            is_catch_all,
                            tx_c,
                            &opts_clone,
                            type_flag,
                            false,
                            false,
                            needs_metadata,
                            &timeout_triggered,
                        );
                    });
                });
            }
        }
    }
    for chunk in rx {
        results.extend(chunk);
    }
    let highlight_spec = if opts.highlight_match {
        Some(compile_highlight_spec(&[(name.regex.clone(), false)])?)
    } else {
        None
    };
    Ok(final_transform(
        results,
        opts,
        use_style,
        stdout_is_tty,
        colors,
        cache,
        highlight_spec.as_ref(),
    ))
}

fn run_contains_all(
    opts: &Options,
    spec: ContainsAllSpec,
    cache: &mut DirStatsCache,
    colors: &ColorSpec,
) -> Result<Vec<String>, String> {
    let stdout_is_tty = io::stdout().is_terminal();
    let use_style = style_enabled(opts, stdout_is_tty);
    let timeout_dur = opts.timeout_dur;
    let timeout_triggered = Arc::new(AtomicBool::new(false));
    let timeout_clone = timeout_triggered.clone();
    std::thread::spawn(move || {
        std::thread::sleep(timeout_dur);
        timeout_clone.store(true, Ordering::Relaxed);
    });

    let mut type_flag = if opts.force_dir {
        Some(TypeFlag::Dir)
    } else if opts.force_file {
        Some(TypeFlag::File)
    } else {
        None
    };
    let mut term_specs: Vec<(String, i64)> = Vec::new();
    for p in &spec.terms {
        let parsed = parse_name_pattern(p, opts.regex_mode);
        if parsed.type_flag == Some(TypeFlag::Dir) && !opts.force_file {
            type_flag = Some(TypeFlag::Dir);
        }
        term_specs.push((parsed.regex, term_selectivity_score(p, opts.regex_mode)));
    }
    term_specs.sort_by(|a, b| {
        b.1.cmp(&a.1).then_with(|| {
            b.0.len()
                .cmp(&a.0.len())
                .then_with(|| a.0.cmp(&b.0))
        })
    });
    let regexes: Vec<String> = term_specs.into_iter().map(|(rx, _)| rx).collect();
    if regexes.is_empty() {
        return Ok(Vec::new());
    }
    let first_re = RegexBuilder::new(&regexes[0])
        .case_insensitive(true)
        .build()
        .map_err(|e| format!("Invalid regex: {}", e))?;
    let is_catch_all = regexes[0] == ".*" || regexes[0] == "^.*$";
    let needs_metadata = opts.long_format || opts.sort_field.is_some() || opts.sizes;
    let (tx, rx) = unbounded::<Vec<SearchResult>>();
    let opts_clone = opts.clone();
    let root = spec.root.clone();
    rayon::spawn(move || {
        walk_rayon_worker(
            root,
            &first_re,
            is_catch_all,
            &tx,
            &opts_clone,
            type_flag,
            opts_clone.force_full,
            false,
            needs_metadata,
            &timeout_triggered,
        )
    });

    let mut rows = Vec::new();
    for chunk in rx {
        rows.extend(chunk);
    }
    for rx_str in regexes.iter().skip(1) {
        let re_extra = RegexBuilder::new(rx_str)
            .case_insensitive(true)
            .build()
            .map_err(|e| format!("Invalid regex: {}", e))?;
        rows = rows
            .into_iter()
            .filter(|r| {
                if opts.force_full {
                    re_extra.is_match(&r.path)
                } else {
                    let base = r.path.trim_end_matches('/').rsplit('/').next().unwrap_or("");
                    re_extra.is_match(base)
                }
            })
            .collect();
    }
    if opts.force_full && regexes.len() > 1 {
        let basename_res: Vec<Regex> = regexes
            .iter()
            .map(|rx| {
                RegexBuilder::new(rx)
                    .case_insensitive(true)
                    .build()
                    .map_err(|e| format!("Invalid regex: {}", e))
            })
            .collect::<Result<Vec<_>, _>>()?;
        rows = rows
            .into_iter()
            .filter(|r| {
                let base = r.path.trim_end_matches('/').rsplit('/').next().unwrap_or("");
                basename_res.iter().any(|re| re.is_match(base))
            })
            .collect();
    }
    rows.sort_by(|a, b| a.path.cmp(&b.path));
    let highlight_spec = if opts.highlight_match {
        let highlight_patterns: Vec<(String, bool)> = regexes
            .iter()
            .cloned()
            .map(|rx| (rx, opts.force_full))
            .collect();
        Some(compile_highlight_spec(&highlight_patterns)?)
    } else {
        None
    };

    Ok(final_transform(
        rows,
        opts,
        use_style,
        stdout_is_tty,
        colors,
        cache,
        highlight_spec.as_ref(),
    ))
}

fn run_full(
    opts: &Options,
    cache: &mut DirStatsCache,
    colors: &ColorSpec,
) -> Result<Vec<String>, String> {
    let stdout_is_tty = io::stdout().is_terminal();
    let use_style = style_enabled(opts, stdout_is_tty);
    let mut search_root = ".".to_string();
    let mut patterns = opts.positional.clone();
    if opts.positional.len() > 1 {
        if let Some(last) = opts.positional.last() {
            if Path::new(last).is_dir() {
                search_root = last.clone();
                patterns.pop();
            }
        }
    }
    let mut type_flag = if opts.force_dir {
        Some(TypeFlag::Dir)
    } else if opts.force_file {
        Some(TypeFlag::File)
    } else {
        None
    };
    let mut pattern_specs: Vec<(String, bool)> = Vec::new();
    for p in &patterns {
        let parsed = parse_name_pattern(p, opts.regex_mode);
        if parsed.type_flag == Some(TypeFlag::Dir) && !opts.force_file {
            type_flag = Some(TypeFlag::Dir);
        }
        pattern_specs.push((
            parsed.regex,
            pattern_prefers_full_path(p, opts.regex_mode),
        ));
    }
    if pattern_specs.is_empty() {
        return Ok(Vec::new());
    }
    let re = RegexBuilder::new(&pattern_specs[0].0)
        .case_insensitive(true)
        .build()
        .unwrap();
    let timeout_dur = opts.timeout_dur;
    let timeout_triggered = Arc::new(AtomicBool::new(false));
    let timeout_clone = timeout_triggered.clone();
    std::thread::spawn(move || {
        std::thread::sleep(timeout_dur);
        timeout_clone.store(true, Ordering::Relaxed);
    });
    let (tx, rx) = unbounded::<Vec<SearchResult>>();
    let opts_clone = opts.clone();
    let is_catch_all = pattern_specs[0].0 == ".*" || pattern_specs[0].0 == "^.*$";
    let first_full_path_match = pattern_specs[0].1;
    let prune_matched_dir_subtrees = false;
    rayon::spawn(move || {
        walk_rayon_worker(
            PathBuf::from(search_root),
            &re,
            is_catch_all,
            &tx,
            &opts_clone,
            type_flag,
            first_full_path_match,
            prune_matched_dir_subtrees,
            opts_clone.long_format || opts_clone.sort_field.is_some() || opts_clone.sizes,
            &timeout_triggered,
        );
    });
    let mut rows = Vec::new();
    for chunk in rx {
        rows.extend(chunk);
    }
    for (rx_str, full_path_match) in pattern_specs.iter().skip(1) {
        let re_extra = RegexBuilder::new(rx_str)
            .case_insensitive(true)
            .build()
            .map_err(|e| format!("Invalid regex: {}", e))?;
        rows = rows
            .into_iter()
            .filter(|r| {
                if *full_path_match {
                    re_extra.is_match(&r.path)
                } else {
                    let base = r.path.trim_end_matches('/').rsplit('/').next().unwrap_or("");
                    re_extra.is_match(base)
                }
            })
            .collect();
    }
    rows.sort_by(|a, b| a.path.cmp(&b.path));
    let highlight_spec = if opts.highlight_match {
        Some(compile_highlight_spec(&pattern_specs)?)
    } else {
        None
    };
    Ok(final_transform(
        rows,
        opts,
        use_style,
        stdout_is_tty,
        colors,
        cache,
        highlight_spec.as_ref(),
    ))
}

fn main() -> ExitCode {
    let opts = match parse_args() {
        Ok(v) => v,
        Err(e) => {
            if !e.is_empty() {
                eprintln!("{}", e);
            }
            return ExitCode::from(2);
        }
    };
    let content_spec = match contains_all_spec_from_opts(&opts) {
        Ok(v) => v,
        Err(e) => {
            if !e.trim().is_empty() {
                eprintln!("{}", e.trim());
            }
            return ExitCode::from(2);
        }
    };
    let mut cache = DirStatsCache {
        map: HashMap::new(),
        bytes_map: HashMap::new(),
    };
    let colors = if opts.color_when == ColorWhen::Never {
        default_color_spec()
    } else {
        parse_ls_colors()
    };
    let result = if let Some(spec) = content_spec {
        run_contains_all(&opts, spec, &mut cache, &colors)
    } else if opts.force_full {
        run_full(&opts, &mut cache, &colors)
    } else {
        run_standard(&opts, &mut cache, &colors)
    };
    match result {
        Ok(lines) => {
            if !lines.is_empty() {
                let stdout = io::stdout();
                let mut lock = BufWriter::with_capacity(128 * 1024, stdout.lock());
                for line in lines {
                    let _ = writeln!(lock, "{}", line);
                }
                let _ = lock.flush();
            }
            ExitCode::SUCCESS
        }
        Err(e) => {
            if !e.trim().is_empty() {
                eprintln!("{}", e.trim());
            }
            ExitCode::from(1)
        }
    }
}
