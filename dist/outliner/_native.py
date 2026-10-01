"""Loading the native Outliner library and calling its C API."""

import ctypes
import os
import platform
from typing import Optional

from binaryninja import log_error, log_info

LOGGER = "Outliner"
HERE = os.path.dirname(os.path.abspath(__file__))
LIBRARY = {"Darwin": "liboutliner.dylib", "Windows": "outliner.dll"}.get(platform.system(), "liboutliner.so")
PATH = os.path.join(HERE, LIBRARY)


class OutlinerError(Exception):
    """An Outliner call failed; the message says why."""


_void = ctypes.c_void_p
_text = ctypes.c_char_p
_u64 = ctypes.c_uint64

# Every exported function: (argument types, result type).  Strings the library
# returns are taken as raw pointers so that they can be freed.
_PROTOTYPES = {
    "outliner_initialized": ([], ctypes.c_bool),
    "outliner_free_string": ([_void], None),
    "outliner_version": ([], _void),
    "outliner_manual": ([], _void),
    "outliner_skill": ([], _void),
    "outliner_add_pattern": ([_void, _text, _text, ctypes.c_bool], _void),
    "outliner_remove_pattern": ([_void, _text, ctypes.c_bool], ctypes.c_bool),
    "outliner_load_pattern_file": ([_void, _text, ctypes.c_bool], _void),
    "outliner_save_pattern_file": ([_void, _text], _void),
    "outliner_list_patterns": ([_void], _void),
    "outliner_validate_pattern": ([_void, _text], _void),
    "outliner_save_patterns": ([_void, _text, ctypes.c_bool], _void),
    "outliner_split_chunks": ([_text], _void),
    "outliner_join_chunks": ([_text], _void),
    "outliner_chunk_title": ([_text], _void),
    "outliner_pattern_template": ([], _void),
    "outliner_function_pattern_text": ([_void], _void),
    "outliner_reset_timing": ([], None),
    "outliner_timing_json": ([], _void),
    "outliner_timing_report": ([], _void),
    "outliner_compile_count": ([], ctypes.c_size_t),
    "outliner_draft_region": ([_void, _u64, _u64], _void),
    "outliner_draft_indices": ([_void, _u64, ctypes.c_uint32, ctypes.c_uint32], _void),
    "outliner_draft_function": ([_void, _u64], _void),
    "outliner_preview_start": ([_void, _text, _text, _text], _u64),
    "outliner_preview_poll": ([_u64], _void),
    "outliner_preview_cancel": ([_u64], None),
    "outliner_preview_result": ([_u64], _void),
    "outliner_generalize": ([_text, _text], _void),
}

_lib: Optional[ctypes.CDLL] = None
_load_error = "the Outliner library has not been loaded"


def load() -> bool:
    """Open the library next to this package and initialise the plugin unless
    Binary Ninja has already loaded it itself.  Returns whether it is usable."""
    global _lib, _load_error
    if _lib is not None:
        return True
    if not os.path.exists(PATH):
        _load_error = f"{PATH} is missing; build it with `cargo build --release -p outliner-plugin`"
        log_error(f"Outliner: {_load_error}", LOGGER)
        return False
    try:
        lib = ctypes.CDLL(PATH)
    except OSError as e:
        _load_error = f"could not load {PATH}: {e}"
        log_error(f"Outliner {_load_error}", LOGGER)
        return False
    for name, (args, result) in _PROTOTYPES.items():
        function = getattr(lib, name, None)
        if function is not None:
            function.argtypes, function.restype = args, result
    lib.CorePluginInit.restype = ctypes.c_bool
    if not lib.outliner_initialized():
        if lib.CorePluginInit():
            log_info(f"Outliner loaded from {PATH}", LOGGER)
        else:
            _load_error = "the Outliner plugin failed to initialize"
            log_error(_load_error, LOGGER)
            return False
    _lib = lib
    return True


def function(name: str):
    """The exported function `name`, or an error when the library is missing
    or too old to have it."""
    if _lib is None:
        raise OutlinerError(_load_error)
    found = getattr(_lib, name, None)
    if found is None:
        raise OutlinerError(f"the installed Outliner library has no {name}; rebuild and reinstall it")
    return found


def take(pointer: Optional[int]) -> Optional[str]:
    """The string a call returned, freed; None for a null result."""
    if not pointer:
        return None
    try:
        return ctypes.string_at(pointer).decode("utf-8", "replace")
    finally:
        function("outliner_free_string")(_void(pointer))


def text(pointer: Optional[int]) -> str:
    """A returned string that is never null in practice."""
    return take(pointer) or ""


def check(pointer: Optional[int]) -> None:
    """Raise the error a fallible call returned (null means success)."""
    error = take(pointer)
    if error:
        raise OutlinerError(error)


def encode(value: str) -> bytes:
    return value.encode("utf-8")


def view_handle(bv) -> ctypes.c_void_p:
    """The core handle of a BinaryView."""
    handle = getattr(bv, "handle", None)
    if handle is None:
        raise OutlinerError("expected a binaryninja.BinaryView")
    return ctypes.cast(handle, _void)


def function_handle(func) -> ctypes.c_void_p:
    """The core handle of a Function."""
    handle = getattr(func, "handle", None)
    if handle is None:
        raise OutlinerError("expected a binaryninja.Function")
    return ctypes.cast(handle, _void)
