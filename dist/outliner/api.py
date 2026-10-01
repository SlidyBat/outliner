"""Python API for the Outliner plugin.

The functions wrap the plugin's C API.  They take Binary Ninja objects
(`BinaryView`, `Function`) and return Python values; a failure raises
`OutlinerError` with the plugin's message.  The pattern language is described
in the manual, `manual()`.
"""

import dataclasses
import json
import time
from dataclasses import dataclass, field, fields
from typing import Callable, ClassVar, Iterable, List, Optional, Sequence, Tuple, Union

from ._native import OutlinerError, check, encode, function, function_handle, take, text, view_handle

__all__ = [
    "OutlinerError",
    "PatternRecord",
    "Draft",
    "Hit",
    "Diagnosis",
    "FunctionRef",
    "CallTarget",
    "PatternReport",
    "TestReport",
    "Merge",
    "version",
    "manual",
    "skill",
    "list_patterns",
    "add_pattern",
    "remove_pattern",
    "replace_patterns",
    "load_pattern_file",
    "save_pattern_file",
    "validate_pattern",
    "split_chunks",
    "join_chunks",
    "chunk_title",
    "pattern_template",
    "function_pattern_text",
    "draft_instructions",
    "draft_region",
    "draft_function",
    "test_patterns",
    "test_pattern",
    "generalize",
    "call_targets",
    "timing_report",
    "timing",
    "reset_timing",
    "compile_count",
]


# --------------------------------------------------------------------------- records


def _hex_repr(self) -> str:
    """A record's repr with its address fields in hex."""
    parts = []
    for f in fields(self):
        value = getattr(self, f.name)
        if f.name in self._addresses and isinstance(value, int):
            parts.append(f"{f.name}={value:#x}")
        else:
            parts.append(f"{f.name}={value!r}")
    return f"{type(self).__name__}({', '.join(parts)})"



@dataclass(frozen=True)
class PatternRecord:
    """A saved pattern or rules chunk."""

    name: str
    signature: str
    text: str
    id: str
    kind: str
    full_text: str

    @classmethod
    def from_json(cls, data: dict) -> "PatternRecord":
        return cls(
            name=data.get("name", ""),
            signature=data.get("signature", ""),
            text=data.get("text", ""),
            id=data.get("id", ""),
            kind=data.get("kind", "pattern"),
            full_text=data.get("full_text", data.get("text", "")),
        )


@dataclass(frozen=True, repr=False)
class Draft:
    """A pattern drafted from code: its text, notes about it, and where the
    code is (`function` is the function's start address, `name` its name,
    `start` and `end` the drafted code's addresses)."""

    _addresses: ClassVar[Tuple[str, ...]] = ("function", "start", "end")
    __repr__ = _hex_repr

    text: str
    notes: List[str]
    function: int
    name: str
    start: int
    end: int


@dataclass(frozen=True, repr=False)
class Hit:
    """A place a tested pattern matches: `function` is the function's name,
    `address` the matched instruction's address, `instr` its MLIL index."""

    _addresses: ClassVar[Tuple[str, ...]] = ("address",)
    __repr__ = _hex_repr

    function: str
    address: int
    kind: str
    round: int
    instr: int
    text: str


@dataclass(frozen=True, repr=False)
class Diagnosis:
    """Why a pattern does not match a function the test focused on:
    `function` is the function's name, `address` its start address."""

    _addresses: ClassVar[Tuple[str, ...]] = ("address",)
    __repr__ = _hex_repr

    function: str
    address: int
    line: Optional[int]
    matched: int
    instr: int
    code: str
    reason: str


@dataclass(frozen=True, repr=False)
class FunctionRef:
    """A function by its name and start address; `bv.get_function_at(address)`
    gives the Function."""

    _addresses: ClassVar[Tuple[str, ...]] = ("address",)
    __repr__ = _hex_repr

    name: str
    address: int


@dataclass(frozen=True, repr=False)
class CallTarget:
    """The call target of one signature: the outlined function's name, the
    signature, and the address its calls go to, a slot in the `outlined`
    section Outliner adds after the end of the binary."""

    _addresses: ClassVar[Tuple[str, ...]] = ("address",)
    __repr__ = _hex_repr

    name: str
    signature: str
    address: int


@dataclass(frozen=True)
class PatternReport:
    """The test result of one pattern: `index` is its position among the
    texts tested (among the chunks of the text, for `test_pattern`), `name`
    the function it describes."""

    title: str
    error: str
    index: int = 0
    name: str = ""
    hits: List[Hit] = field(default_factory=list)
    diagnoses: List[Diagnosis] = field(default_factory=list)

    @property
    def diagnosis(self) -> Optional[Diagnosis]:
        """The first diagnosis, for a test focused on one function."""
        return self.diagnoses[0] if self.diagnoses else None


@dataclass(frozen=True)
class TestReport:
    """The result of a test over the whole binary.  `uncovered` lists the
    focus functions that none of the patterns tested matched."""

    patterns: List[PatternReport]
    functions: int
    skipped: int
    cancelled: bool
    message: str
    left_out: List[str]
    uncovered: List[FunctionRef] = field(default_factory=list)

    @property
    def pattern(self) -> PatternReport:
        """The report of the one pattern tested; use `patterns` for several."""
        if len(self.patterns) != 1:
            raise OutlinerError(f"the test reported {len(self.patterns)} patterns, not one")
        return self.patterns[0]


@dataclass(frozen=True)
class Merge:
    """The result of `generalize`: `merged` is true when `text` covers both
    instances; otherwise `text` is a separate chunk for the second shape."""

    merged: bool
    text: str
    notes: List[str]


def _json(pointer) -> Union[dict, list]:
    raw = take(pointer)
    if not raw:
        return {}
    return json.loads(raw)


def _address(value) -> int:
    """An address from an int or anything with a `start` (a Function)."""
    if isinstance(value, int):
        return value
    start = getattr(value, "start", None)
    if isinstance(start, int):
        return start
    raise OutlinerError("expected an address or a binaryninja.Function")


def _addresses(values) -> List[int]:
    """Function starts from None, one function or address, or several."""
    if values is None:
        return []
    if isinstance(values, int) or hasattr(values, "start"):
        return [_address(values)]
    return [_address(v) for v in values]


def _draft(pointer) -> Draft:
    data = _json(pointer)
    if not data.get("ok"):
        raise OutlinerError(data.get("error") or "the draft failed")
    return Draft(
        text=data.get("text", ""),
        notes=list(data.get("notes", [])),
        function=data.get("function", 0),
        name=data.get("name", ""),
        start=data.get("start", 0),
        end=data.get("end", 0),
    )


def _known(cls, data: dict) -> dict:
    """The entries of `data` that are fields of `cls` (newer libraries may add more)."""
    names = {f.name for f in fields(cls)}
    return {k: v for k, v in data.items() if k in names}


def _report(data: dict) -> TestReport:
    patterns = []
    for entry in data.get("patterns", []):
        patterns.append(
            PatternReport(
                title=entry.get("title", ""),
                error=entry.get("error", ""),
                index=entry.get("index", 0),
                name=entry.get("name", ""),
                hits=[Hit(**_known(Hit, hit)) for hit in entry.get("hits", [])],
                diagnoses=[Diagnosis(**_known(Diagnosis, d)) for d in entry.get("diagnoses", [])],
            )
        )
    return TestReport(
        patterns=patterns,
        functions=data.get("functions", 0),
        skipped=data.get("skipped", 0),
        cancelled=bool(data.get("cancelled", False)),
        message=data.get("message", ""),
        left_out=list(data.get("left_out", [])),
        uncovered=[FunctionRef(**_known(FunctionRef, f)) for f in data.get("uncovered", [])],
    )


# --------------------------------------------------------------------------- about


def version() -> str:
    """The plugin's version."""
    return text(function("outliner_version")())


def manual() -> str:
    """The manual for writing patterns (Markdown)."""
    return text(function("outliner_manual")())


def skill() -> str:
    """The skill that teaches AI agents to use Outliner (Markdown with a YAML header)."""
    return text(function("outliner_skill")())


# --------------------------------------------------------------------------- saved patterns


def list_patterns(bv) -> List[PatternRecord]:
    """The patterns and rules chunks saved in the view, in order.  Chunks of
    the same function share a name; `.id` tells them apart (see
    `remove_pattern`)."""
    return [PatternRecord.from_json(r) for r in _json(function("outliner_list_patterns")(view_handle(bv))) or []]


def add_pattern(bv, pattern: str, signature: Optional[str] = None, reanalyze: bool = True) -> None:
    """Validate and save a pattern or rules chunk, or several separated by
    lines holding only `---`: all are checked before any is saved.
    `signature` overrides each pattern's own `signature:` line.  Unless
    `reanalyze` is false, saving starts one reanalysis of every function and
    returns without waiting for it; `bv.update_analysis_and_wait()` waits.
    Returns nothing; raises OutlinerError when a chunk is invalid."""
    sig = None if signature is None else encode(signature)
    check(function("outliner_add_pattern")(view_handle(bv), encode(pattern), sig, reanalyze))


def remove_pattern(bv, name: str, reanalyze: bool = True) -> bool:
    """Remove every pattern saved under a function name, or, given a
    record's `.id`, that one chunk.  Returns whether anything was removed."""
    return bool(function("outliner_remove_pattern")(view_handle(bv), encode(name), reanalyze))


def replace_patterns(bv, texts: Sequence[str], reanalyze: bool = True) -> List[PatternRecord]:
    """Replace all saved patterns with `texts` (patterns and rules chunks).
    Every text is validated first; nothing changes if one fails."""
    records = []
    for index, chunk in enumerate(texts):
        try:
            records.append(validate_pattern(bv, chunk))
        except OutlinerError as e:
            raise OutlinerError(f"pattern {index + 1}: {e}") from None
    payload = [{"name": r.name, "signature": r.signature, "text": r.text, "id": r.id, "kind": r.kind} for r in records]
    check(function("outliner_save_patterns")(view_handle(bv), encode(json.dumps(payload)), reanalyze))
    return list_patterns(bv)


def load_pattern_file(bv, path: str, reanalyze: bool = True) -> None:
    """Add the patterns of a file (chunks separated by lines holding `---`),
    skipping those already saved."""
    check(function("outliner_load_pattern_file")(view_handle(bv), encode(str(path)), reanalyze))


def save_pattern_file(bv, path: str) -> None:
    """Write the saved patterns to a file that `load_pattern_file` reads."""
    check(function("outliner_save_pattern_file")(view_handle(bv), encode(str(path))))


def validate_pattern(bv, pattern: str) -> PatternRecord:
    """Check a complete pattern text (with its `signature:` line) or rules
    chunk without saving it.  Raises with the error, which names the line."""
    data = _json(function("outliner_validate_pattern")(view_handle(bv), encode(pattern)))
    if not data.get("ok"):
        raise OutlinerError(data.get("error") or "the pattern is invalid")
    return PatternRecord.from_json(data.get("record", {}))


# --------------------------------------------------------------------------- pattern text


def split_chunks(content: str) -> List[str]:
    """The chunks of a pattern file's text."""
    return list(_json(function("outliner_split_chunks")(encode(content))) or [])


def join_chunks(chunks: Sequence[str]) -> str:
    """A pattern file's text for a list of chunks."""
    return text(function("outliner_join_chunks")(encode(json.dumps(list(chunks)))))


def chunk_title(pattern: str) -> str:
    """The title the pattern editor shows for a chunk."""
    return text(function("outliner_chunk_title")(encode(pattern)))


def pattern_template() -> str:
    """The text a new pattern starts from in the editor."""
    return text(function("outliner_pattern_template")())


def function_pattern_text(func) -> str:
    """A function's MLIL in pattern syntax, with its signature and parameters."""
    return text(function("outliner_function_pattern_text")(function_handle(func)))


# --------------------------------------------------------------------------- drafting


def draft_instructions(func, first: int, last: int) -> Draft:
    """Draft a pattern for MLIL instructions `first` to `last` (indices into
    `func.mlil`).  The draft names the function `outlined`."""
    return _draft(function("outliner_draft_indices")(view_handle(func.view), func.start, first, last))


def draft_region(bv, start: int, end: int) -> Draft:
    """Draft a pattern for the MLIL instructions whose addresses lie in
    `[start, end)` of the function holding `start`."""
    return _draft(function("outliner_draft_region")(view_handle(bv), start, end))


def draft_function(func) -> Draft:
    """Draft a pattern from a function's own body: its parameters become the
    pattern's and each `return x` becomes `$ret = x`."""
    return _draft(function("outliner_draft_function")(view_handle(func.view), func.start))


# --------------------------------------------------------------------------- testing


def test_patterns(
    bv,
    texts: Sequence[str],
    focus=None,
    only: Union[None, int, Iterable[int]] = None,
    timeout: Optional[float] = None,
    progress: Optional[Callable[[int, int], None]] = None,
) -> TestReport:
    """Match pattern texts (one chunk each) against every function without
    changing anything.

    The test runs the way analysis would: on each function's MLIL from before
    any outlining, round after round, all texts together.  `focus` (a
    function or its start, or several) gets a diagnosis for each reported
    pattern that does not match there, unless another reported pattern for
    the same function did; `.uncovered` lists the focus functions no
    reported pattern matched.  With `only` (an index into `texts`, or
    several), only those texts are reported; the others still take part.
    `progress(done, total)` is called while the test runs.  The test runs on
    worker threads; this call waits for it, so do not call it from the UI
    thread.  It stops early on `timeout` (seconds) or KeyboardInterrupt and
    returns what was tested.
    """
    report = None if only is None else ([only] if isinstance(only, int) else list(only))
    job = function("outliner_preview_start")(
        view_handle(bv), encode(json.dumps(list(texts))), encode(json.dumps(_addresses(focus))), encode(json.dumps(report))
    )
    if not job:
        raise OutlinerError("the test could not be started")
    deadline = None if timeout is None else time.monotonic() + timeout
    cancelled = False
    try:
        while True:
            state = _json(function("outliner_preview_poll")(job))
            if progress is not None and state.get("total"):
                progress(state.get("processed", 0), state["total"])
            if state.get("done"):
                break
            if not cancelled and deadline is not None and time.monotonic() >= deadline:
                function("outliner_preview_cancel")(job)
                cancelled = True
            time.sleep(0.05)
    except KeyboardInterrupt:
        function("outliner_preview_cancel")(job)
        while not _json(function("outliner_preview_poll")(job)).get("done"):
            time.sleep(0.05)
    return _report(_json(function("outliner_preview_result")(job)))


def test_pattern(
    bv,
    pattern: str,
    focus=None,
    context: Optional[Sequence[str]] = None,
    timeout: Optional[float] = None,
    progress: Optional[Callable[[int, int], None]] = None,
) -> TestReport:
    """Test a pattern, or several separated by lines holding only `---`; the
    report's `.pattern` (or `.patterns`) holds the hits and diagnoses.

    `focus` is a function or its start, or several: each pattern that does
    not match one of them gets a diagnosis, unless another chunk for the same
    function matched there, and `.uncovered` lists the focus functions no
    chunk matched.  `context` is the other pattern
    texts that take part without being reported.  By default it is the
    view's saved rules chunks and the saved patterns for other functions, as
    analysis would run them alongside new versions of these; pass `[]` to
    test the patterns alone.
    """
    chunks = [c for c in split_chunks(pattern) if c.strip()]
    if not chunks:
        raise OutlinerError("the text holds no pattern")
    if context is None:
        names = set()
        for index, chunk in enumerate(chunks):
            try:
                names.add(validate_pattern(bv, chunk).name)
            except OutlinerError as e:
                raise (OutlinerError(f"pattern {index + 1}: {e}") if len(chunks) > 1 else e) from None
        context = [r.full_text for r in list_patterns(bv) if r.kind == "rules" or r.name not in names]
    texts = list(context) + chunks
    only = list(range(len(context), len(texts)))
    report = test_patterns(bv, texts, focus=focus, only=only, timeout=timeout, progress=progress)
    # Number the entries by their chunk in `pattern`, not by their place among the texts.
    patterns = [dataclasses.replace(p, index=p.index - len(context)) for p in report.patterns]
    return dataclasses.replace(report, patterns=patterns)


def generalize(base: str, other: str) -> Merge:
    """Combine a second instance of a function's code (`other`, a pattern
    drafted from it) into the pattern `base`.  Constants that differ become
    placeholders; a different shape becomes a separate chunk."""
    data = _json(function("outliner_generalize")(encode(base), encode(other)))
    kind = data.get("kind")
    if kind not in ("merged", "chunk"):
        raise OutlinerError(data.get("error") or "the patterns could not be combined")
    return Merge(merged=kind == "merged", text=data.get("text", ""), notes=list(data.get("notes", [])))


# --------------------------------------------------------------------------- results


def call_targets(bv) -> List[CallTarget]:
    """The call targets of the view's patterns, one per signature (overloads
    share a name), in address order.  `bv.get_code_refs(target.address)`
    finds the calls to one."""
    try:
        raw = bv.query_metadata("outliner.targets")
    except KeyError:
        return []
    addresses = json.loads(raw) if isinstance(raw, str) else dict(raw or {})
    # The metadata keys each target by its signature without whitespace.
    signatures = {"".join(r.signature.split()): r.signature for r in list_patterns(bv) if r.kind != "rules"}
    targets = []
    for key, address in addresses.items():
        if not isinstance(address, int):
            continue
        symbol = bv.get_symbol_at(address)
        targets.append(CallTarget(name=symbol.name if symbol is not None else key, signature=signatures.get(key, key), address=address))
    return sorted(targets, key=lambda t: t.address)


# --------------------------------------------------------------------------- timing


def timing_report() -> str:
    """The outlining activity's time per phase and per function since the
    last reset, as text."""
    return text(function("outliner_timing_report")())


def timing() -> list:
    """The outlining activity's timing records since the last reset."""
    return _json(function("outliner_timing_json")()) or []


def reset_timing() -> None:
    """Start a new timing period."""
    function("outliner_reset_timing")()


def compile_count() -> int:
    """How many times pattern sets were compiled since the plugin loaded."""
    return int(function("outliner_compile_count")())
