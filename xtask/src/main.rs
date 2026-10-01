//! Build tasks, run as `cargo xtask <task>`:
//!
//! - `package`: build the plugin in release mode and assemble the `outliner`
//!   folder Binary Ninja loads (the library and the Python package) in
//!   `target/outliner`, ready to copy into a plugins folder or to archive.
//! - `install`: package, then copy that folder into Binary Ninja's plugins
//!   folder (`--plugins-dir DIR` for another one).
//!
//! Other arguments are passed to `cargo build` (`--offline`, `--locked`, ...).

use std::env;
use std::ffi::OsString;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, ExitCode};

/// The folder's name, which is also the Python package's.
const FOLDER: &str = "outliner";

#[cfg(target_os = "macos")]
const LIBRARY: &str = "liboutliner.dylib";
#[cfg(target_os = "windows")]
const LIBRARY: &str = "outliner.dll";
#[cfg(not(any(target_os = "macos", target_os = "windows")))]
const LIBRARY: &str = "liboutliner.so";

const USAGE: &str = "usage: cargo xtask package [cargo build options]
       cargo xtask install [--plugins-dir DIR] [cargo build options]";

fn main() -> ExitCode {
    let mut args = env::args_os().skip(1);
    let task = args.next().and_then(|a| a.into_string().ok()).unwrap_or_default();
    let rest: Vec<OsString> = args.collect();
    let result = match task.as_str() {
        "package" => package(&rest).map(|folder| println!("Packaged {}", folder.display())),
        "install" => install(rest),
        _ => {
            eprintln!("{USAGE}");
            return ExitCode::from(2);
        }
    };
    match result {
        Ok(()) => ExitCode::SUCCESS,
        Err(e) => {
            eprintln!("error: {e}");
            ExitCode::FAILURE
        }
    }
}

fn workspace_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).parent().expect("xtask lives in the workspace").to_path_buf()
}

fn target_dir(root: &Path) -> PathBuf {
    match env::var_os("CARGO_TARGET_DIR") {
        Some(dir) => root.join(dir),
        None => root.join("target"),
    }
}

/// Build the plugin and assemble `target/outliner`; returns the folder.
fn package(build_args: &[OsString]) -> Result<PathBuf, String> {
    let root = workspace_root();
    let cargo = env::var_os("CARGO").unwrap_or_else(|| "cargo".into());
    let status = Command::new(cargo)
        .current_dir(&root)
        .args(["build", "--release", "--package", "outliner-plugin"])
        .args(build_args)
        .status()
        .map_err(|e| format!("could not run cargo: {e}"))?;
    if !status.success() {
        return Err("the build failed".into());
    }

    let target = target_dir(&root);
    let folder = target.join(FOLDER);
    if folder.exists() {
        fs::remove_dir_all(&folder).map_err(|e| format!("could not clear {}: {e}", folder.display()))?;
    }
    fs::create_dir_all(&folder).map_err(|e| format!("could not create {}: {e}", folder.display()))?;
    copy(&target.join("release").join(LIBRARY), &folder.join(LIBRARY))?;
    for file in files(&root.join("dist").join(FOLDER))? {
        copy(&file, &folder.join(file.file_name().expect("a file has a name")))?;
    }
    Ok(folder)
}

/// Package, then copy the folder into the plugins folder.
fn install(args: Vec<OsString>) -> Result<(), String> {
    let mut plugins: Option<PathBuf> = None;
    let mut build_args = Vec::new();
    let mut args = args.into_iter();
    while let Some(arg) = args.next() {
        if arg == "--plugins-dir" {
            plugins = Some(args.next().ok_or("--plugins-dir needs a folder")?.into());
        } else {
            build_args.push(arg);
        }
    }
    let plugins = match plugins {
        Some(dir) => dir,
        None => default_plugins_dir()?,
    };
    let folder = package(&build_args)?;
    let destination = plugins.join(FOLDER);
    fs::create_dir_all(&destination).map_err(|e| format!("could not create {}: {e}", destination.display()))?;
    for file in files(&folder)? {
        copy(&file, &destination.join(file.file_name().expect("a file has a name")))?;
    }
    println!("Installed into {}; restart Binary Ninja to load it", destination.display());
    Ok(())
}

/// Binary Ninja's plugins folder: in `BN_USER_DIRECTORY` when that is set,
/// else in the platform's default user folder.
fn default_plugins_dir() -> Result<PathBuf, String> {
    if let Some(dir) = env::var_os("BN_USER_DIRECTORY") {
        return Ok(PathBuf::from(dir).join("plugins"));
    }
    let home = |var: &str| env::var_os(var).map(PathBuf::from).ok_or_else(|| format!("{var} is not set; pass --plugins-dir"));
    let user = if cfg!(target_os = "macos") {
        home("HOME")?.join("Library").join("Application Support").join("Binary Ninja")
    } else if cfg!(target_os = "windows") {
        home("APPDATA")?.join("Binary Ninja")
    } else {
        home("HOME")?.join(".binaryninja")
    };
    Ok(user.join("plugins"))
}

/// The plain files of a folder (no subfolders, no compiled Python).
fn files(dir: &Path) -> Result<Vec<PathBuf>, String> {
    let entries = fs::read_dir(dir).map_err(|e| format!("could not read {}: {e}", dir.display()))?;
    let mut out = Vec::new();
    for entry in entries {
        let path = entry.map_err(|e| e.to_string())?.path();
        if path.is_file() && path.extension().is_none_or(|e| e != "pyc") {
            out.push(path);
        }
    }
    out.sort();
    Ok(out)
}

/// Copy a file, replacing the destination rather than writing into it: a
/// running Binary Ninja keeps the library it loaded, which overwriting in
/// place would corrupt.
fn copy(from: &Path, to: &Path) -> Result<(), String> {
    if to.exists() {
        fs::remove_file(to).map_err(|e| format!("could not replace {}: {e}", to.display()))?;
    }
    fs::copy(from, to).map(|_| ()).map_err(|e| format!("could not copy {} to {}: {e}", from.display(), to.display()))
}
