---
name: outliner
description: Use the Outliner plugin for Binary Ninja to replace inlined functions with calls by writing MLIL patterns. Use when decompiled code repeats the same inlined idiom (string or container accessors, reference counting, constructors), when asked to outline or recognise inlined functions, or when working with Outliner patterns.
---

# Outliner

Outliner is a Binary Ninja plugin. A pattern describes a fragment of MLIL that
a compiler produced by inlining a function, together with that function's C
signature. During analysis every match is replaced with a call, so MLIL, HLIL
and pseudo-C show `ret = f(args)` instead of the inlined body.

Patterns are stored in the database (`.bndb`). Adding, changing or removing a
pattern reanalyzes every function in the binary, so test first, and ask the
user before saving or removing patterns unless they have already asked for
them to be applied.

## Calling Outliner from Python

Run Python inside Binary Ninja, where `bv` is the current `BinaryView`
(Sidekick's `python_eval` tool, the Python console, or a script):

```python
import outliner
```

Every function raises `outliner.OutlinerError` with a readable message when it
fails.

| Call | Result |
|------|--------|
| `outliner.list_patterns(bv)` | Saved patterns: `.name`, `.signature`, `.kind` (`"pattern"` or `"rules"`), `.full_text`. |
| `outliner.function_pattern_text(func)` | A function's MLIL in pattern syntax, with its signature and parameters. |
| `outliner.draft_instructions(func, first, last)` | A draft pattern for MLIL instructions `first` to `last` of `func`: `.text`, `.notes`. |
| `outliner.draft_region(bv, start, end)` | A draft for the MLIL instructions in an address range. |
| `outliner.draft_function(func)` | A draft from a function's own body, for a function that also exists out of line. |
| `outliner.validate_pattern(bv, text)` | Checks one pattern; returns its record or raises with the error and line. |
| `outliner.test_pattern(bv, text, focus=[f1, f2])` | Matches the patterns in `text` against every function without changing anything, and explains each miss in the `focus` functions. |
| `outliner.generalize(base, other)` | Combines a second instance of the same function into a pattern; `.notes` says what changed. |
| `outliner.add_pattern(bv, text)` | Saves the patterns in `text` and starts one reanalysis of every function. Returns nothing and does not wait for the reanalysis; `bv.update_analysis_and_wait()` does. |
| `outliner.remove_pattern(bv, name)` | Removes the patterns saved under a function name, or one chunk given its record's `.id` from `list_patterns`. |
| `outliner.load_pattern_file(bv, path)`, `outliner.save_pattern_file(bv, path)` | Reads or writes a pattern file; loading skips patterns already saved. |
| `outliner.call_targets(bv)` | A list with one record per signature (overloads share a name): `.name`, `.signature`, and `.address`, the slot in the `outlined` section, after the end of the binary, that calls to it go to. `bv.get_code_refs(t.address)` finds the calls. |
| `outliner.manual()` | The full manual for the pattern language. Read it before writing anything beyond a simple pattern. |

A text may hold several patterns (chunks) separated by lines containing only
`---`, the format of pattern files. `add_pattern` and `test_pattern` accept
such text; `validate_pattern` takes one chunk. `add_pattern` checks every
chunk before saving any, then reanalyzes once.

`test_pattern` returns a report with one entry per chunk in `.patterns`
(`.pattern` when there is one). Each entry has `.index`, the chunk's position
in the text, `.name`, the function it describes, and:

- `.hits`: where it matches (`.function`, `.address`, `.kind` of `plain`,
  `fused` or `expression`, and `.round`; a round above 1 means it only matched
  after other patterns had been applied).
- `.diagnoses`: for each `focus` function the pattern does not match, the
  function (`.function`, `.address`), how many statements matched, the
  pattern `.line` that failed, the MLIL instruction (`.instr`, `.code`) it
  was tried against, and the `.reason`. `focus` takes one function or a list,
  so one test explains every function the pattern should have covered. A
  chunk is not diagnosed where another chunk for the same function matched.
- `.error`: set when the pattern does not compile.

The report's `.uncovered` lists the focus functions that no chunk matched,
which is the list still to work on. Its entries have `.name` and `.address`;
`bv.get_function_at(entry.address)` gives the Function.

In these records `.function` is a function's name (a string), and every
`.address` is an integer, which the records print in hex: a hit's `.address`
is the matched instruction, a diagnosis's and an `.uncovered` entry's is the
function's start.

By default the test runs alongside the binary's saved patterns, except saved
ones for the same functions, as analysis would; pass `context=[]` to test the
text alone.

## Workflow

1. **Find an instance.** Look for code that repeats with the same shape in
   several functions. Pick one function `func` and find the MLIL instruction
   indices of the inlined code. Print them by basic block, because block
   boundaries decide where a pattern can start:

   ```python
   for block in func.mlil.basic_blocks:
       print(f"block {block.start}..{block.end - 1}")
       for ins in block:
           print(f"  {ins.instr_index}: {ins}")
   ```

2. **Draft.** `d = outliner.draft_instructions(func, first, last)`, then read
   `d.text` and `d.notes`. The draft works out the parameters (inputs read
   from outside the selection), the result (`$ret`) and the block labels.
   For a loop, select from the loop's first block: a pattern that starts
   with a `goto` into the loop only matches code that has that jump. The
   draft leaves out such a jump when the selection starts with one.
3. **Edit.** The draft calls the function `outlined`. Replace that with the
   real name, in the signature and in any `result:` line, and give the
   parameters meaningful names and types. Binary Ninja names the variables
   passed to the call after its parameters, so choose names that read well
   at most call sites. One name may not fit them all (an object pointer at
   some, the address of a member at others); renaming the variable at such a
   call site is a normal edit outside Outliner.
   Keep the draft's intermediate copies (`$b = $a`) even where they look
   redundant. The matcher follows a variable back through a copy only when
   nothing else reads the copy; in a loop the copy usually feeds a
   comparison or the code after the loop, and a pattern without it then
   matches fewer places or none. Write
   C++ names in backticks in the signature line, the function's own name
   included: ``signature: uint64_t `std::string::size`(`std::__1::string` const* s) __pure``.
   Add type constraints such as `$s : /string(?![>\w])/` to pointer
   parameters, so that unrelated code with the same shape is not rewritten.
   Add `__pure` only if the function has no side effects.
4. **Test.** `r = outliner.test_pattern(bv, text, focus=[func, other, ...])`,
   listing every function the pattern should cover. Check that
   `r.pattern.hits` contains them and nothing else, and read
   `r.pattern.diagnoses` for the ones it misses.
5. **Generalise.** When another instance of the same function looks
   different, draft it too and call `outliner.generalize(text, other_text)`,
   with your edited pattern as `text` and the new draft, unedited, as
   `other_text`. The result keeps your signature, type constraints and
   `result:` lines and adds any `result:` line only the draft has. If
   `.merged` is true, `.text` covers both instances and `.notes` says what
   was generalised. Otherwise `.text` is a separate chunk for the second
   shape, already under your signature, and `.notes` says why; keep both,
   separated by a `---` line. Test the result before saving it.
6. **Apply.** After the user agrees, call `outliner.add_pattern(bv, text)`
   once with all the chunks. It starts the reanalysis and returns at once,
   so call `bv.update_analysis_and_wait()` before checking the HLIL of a few
   functions from the hits.

## Pattern language essentials

```
signature: char const* `std::string::data`(`std::__1::string` const* s) __pure
$s : /string(?![>\w])/

if (sx(load_struct.b($s, 0x17)) s< 0) then long else short
long:
    $ret = load_struct.q($s, 0)
    goto done
short:
    $ret = $s
    goto done
done:
```

- `signature:` is a C declaration parsed by Binary Ninja's type parser.
- `$name` is a placeholder. Placeholders named after the signature's
  parameters become the call's arguments. `$ret` receives the result. Any
  other placeholder is a temporary that must be dead after the match. `_`
  matches anything without binding.
- `$name : <C type>` or `$name : /regex/` constrains a placeholder's type.
- The first block is unlabeled. `L:` starts a block. Every block but the last
  ends with `if (...) then A else B`, `goto L`, `return ...` or `noret()`. The
  last block is where execution continues; if it has a label it is empty.
- Statements: `$x = expr`, `[addr].q = value`, `$x = call(f, a, b)`,
  `call(f, a)`, and any other MLIL statement written as
  `op.size(operands)`, for example `set_var_field.q($v, 8, $x)`.
- Expressions: C-style infix operators, with signed and unsigned comparisons
  written `s<`, `u<`, `s>=` and so on; loads `[e].b`, `[e].w`, `[e].d`,
  `[e].q`, `[e].o`; `&$v`; any MLIL operation by name, such as `sx.q(e)`,
  `zx.d(e)`, `low_part.b(e)` or `load_struct.q($s, 0x10)`; and `call(f, $s)`,
  which matches a variable defined by a call to `f`, so a pattern can build on
  calls that other patterns produced.
- `value: <expr>` replaces the body and outlines an expression wherever it
  occurs, for a pure function such as
  `value: call(std::string::size, $s) == 0` for `empty()`.
- `result: <expr>` says what `$ret` holds when the compiler specialised the
  function for one use. For example,
  `result: call(std::string::compare, $s, 0, $n, $str) == 0`.
- A chunk starting with `rules: <name>` holds `rewrite: lhs => rhs` lines that
  map other spellings of the same computation onto the one the patterns use.

The matcher follows a variable to its definition when the pattern expects an
expression, lets unrelated instructions sit between the statements of the
first block, recognises objects held in variables, members of structs and
globals, and repeats for up to 12 rounds. `outliner.manual()` has the details.

## Reading a diagnosis

- `$s is X, the constraint wants Y`: the type constraint rejected the value.
  Check the variable's type, or relax the constraint.
- `expects an assignment, the code has MLIL_IF` (or another operation): the
  code's statements differ in kind or order from the pattern's.
- `the block ends before this statement`: a statement is missing from the
  code there; the compiler may have moved it to another block or merged it.
- `instruction N (...) between the matched statements reads X, which the
  region computes`: an instruction the pattern does not name sits among the
  matched ones and uses a value the match computes, such as a comparison
  the compiler moved into a loop. It cannot stay, because that value no
  longer exists after the call. Add the instruction to the pattern where it
  occurs, and if its variable is read after the match, declare it with a
  `result:` line: `$c = $ret != $k` in the body, and
  `result: $c = call(f, $p) != $k`.
- `instruction N (...) between the matched statements overwrites X, which
  the region reads`: an instruction the pattern does not name writes a
  variable the pattern reads, typically a register copy left out of the
  pattern. Add it to the pattern, spelled as the draft has it.
- `instruction N (...) between the matched statements cannot stay next to a
  call or store the region removes`: it touches memory, so it cannot be
  reordered around the call. Add it to the pattern.
- `... is still read after it`: a temporary is used after the matched code.
  Declare it as an output with a `result:` line that states its value in
  terms of the call, for example
  `result: $cond = call(f, $p) != 1`. At least one `result:`
  line must contain the call to the pattern's own function; further lines
  may write `$ret` for the call's value
  (`result: call(f, $p)` and `result: $cond = $ret != 1`). Or extend the
  pattern to cover the use.
- `the target is X, not Y`: a call goes to a different function than the
  pattern names.

## Limitations

- Patterns match whole MLIL instructions. Use `value:` for code that the
  compiler folded into a larger expression.
- A shape the compiler produces with different constants or a different
  instruction order needs its own chunk, or a rewrite rule.
- A draft made from code that uses a global contains the global's addresses
  as constants. Replace them with a placeholder before saving.
