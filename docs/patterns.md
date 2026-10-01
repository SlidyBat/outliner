# Writing patterns

A pattern describes a piece of MLIL that a compiler produced by inlining a
function, and the C signature of that function. Wherever the pattern matches,
the plugin replaces the code with a call.

This document describes the pattern language and how patterns are matched.

- [Pattern files](#pattern-files)
- [Creating and testing a pattern](#creating-and-testing-a-pattern)
- [Structure of a pattern](#structure-of-a-pattern)
- [Signatures](#signatures)
- [Placeholders](#placeholders)
- [Type constraints](#type-constraints)
- [Blocks and control flow](#blocks-and-control-flow)
- [Statements](#statements)
- [Expressions](#expressions)
- [Results and outputs](#results-and-outputs)
- [String literals](#string-literals)
- [Expression patterns](#expression-patterns)
- [Rewrite rules](#rewrite-rules)
- [How code is matched](#how-code-is-matched)
- [What the rewrite produces](#what-the-rewrite-produces)
- [Limitations](#limitations)

## Pattern files

A pattern file holds chunks separated by a line that contains only `---`.
Each chunk is either:

- a pattern: a `signature:` line, optional type constraints and result lines,
  and a body of statements (or a `value:` line instead of a body), or
- a rules chunk: a `rules:` line followed by `rewrite:` lines.

Comments start with `#` or `//` and run to the end of the line. `;` separates
statements on one line. In the pattern editor each chunk is a tab.

Loading a file adds only the patterns that are not already present. A chunk
that is the same pattern as one already saved (or open in the editor), or as
an earlier chunk of the file, is skipped. Two chunks are the same pattern
when they differ only in comments, blank lines and spacing.

## Creating and testing a pattern

**From a selection.** Select the inlined code in the MLIL view, right-click,
and choose **Outliner > Create Pattern From Selection...**. The plugin works
out the values the selection reads from outside (the parameters, typed as the
decompiler types them), the value it leaves behind (`$ret`, with `result:`
lines for any others), the block labels and the exit. The draft opens in the
pattern editor next to the decompiled view of the selection. Name the function
in the signature line and apply.

**From a function.** **Create Pattern From Function...** drafts a pattern from
a function's own body: its parameters become the pattern's, and each
`return x` becomes `$ret = x`. The inlined form often differs from the
out-of-line body, so the draft usually needs editing.

**By hand.** **Show Function As Pattern Text** prints a function's MLIL in
pattern syntax, one instruction per line with the original text as a comment,
plus the exact spelling of the parameter types. Copy the lines of the inlined
code, rename the placeholders of the function's inputs to the parameter names
of your signature, rename the result variable to `$ret`, and delete the rest.

**Testing.** *Test* in the pattern editor matches the selected tab's pattern
against every function without changing anything. It runs the way analysis
would: on each function's MLIL from before any outlining, for as many rounds
as analysis would, with the other tabs taking part but not reported. It lists
where the pattern matches. For the function the editor was opened from, if
the pattern does not match there, it shows how many statements matched, the
pattern line that failed, the MLIL instruction it was tried against and the
reason. The test runs on all cores and can be cancelled.

**Merging.** When a second instance of the same function looks different,
draft it too and use *Merge Into...* to combine it with the first. The first
is the pattern being extended, edited or not; the second is a draft of the
new instance, unedited. The result keeps the first one's signature, type
constraints and `result:` lines. Constants that differ become placeholders,
in the body and in `result:` lines alike, and a `result:` line only the
second instance has is added. If the shapes differ, or the second declares
`$ret` or another output differently, it stays a separate chunk under the
first one's signature, and the notes say why.

**From Python.** The same steps are available to scripts through the
`outliner` package: `draft_instructions`, `draft_region`, `draft_function`,
`validate_pattern`, `test_pattern`, `generalize` and `add_pattern`.
`test_pattern` and `add_pattern` accept several chunks separated by `---`
lines, and `test_pattern` takes several functions to explain misses in. A
chunk is not diagnosed in a function where another chunk for the same
function matched, and the report lists the focus functions no chunk matched.
`remove_pattern` removes one chunk when given its record's id.

## Structure of a pattern

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

A pattern consists of these lines, in any order before the body:

| Line                     | Meaning                                                    |
|--------------------------|------------------------------------------------------------|
| `signature: <C decl>`    | The function the code is replaced with a call to. Required. |
| `$name : <type>`         | A type constraint on a placeholder.                        |
| `result: [$v =] <expr>`  | What `$ret` (or `$v`) holds after the matched code.        |
| `branch: <expr>`         | The pattern may leave through a branch; see below.         |
| `value: <expr>`          | Instead of a body: outline this expression wherever it occurs. |

The body is a sequence of blocks of statements.

## Signatures

The signature is a C declaration parsed by Binary Ninja's type parser, so
types from the view and its type libraries can be used, and function
attributes apply. `__pure` declares that the function has no side effects,
which [expression patterns](#expression-patterns) and
[fused calls](#fused-calls) require.

C++ names, including the function's own name, must be written in backticks
so that the type parser accepts them:
`` uint64_t `std::string::size`(`std::__1::string` const* s) __pure ``.
**Show Function As Pattern Text** prints types in this form. Inside the body,
a qualified name is written without backticks: `call(std::string::size, $s)`.

Several chunks may describe the same function when the compiler produces more
than one shape for it; they use the same signature. A name may also have
several signatures (overloads, such as the constructors of a class). Each
signature gets its own call target.

## Placeholders

- `$name` matches an expression or a variable and binds to it. Every use of
  the same name must match the same thing.
- Placeholders named after the signature's parameters are the call's
  arguments. They are evaluated at the call, so an argument may not depend on
  a value the pattern itself computes. Every parameter must appear in the
  pattern, unless a `result:` call passes a constant for it.
- `$ret` is the variable that receives the result. A pattern whose signature
  returns a value must assign it or have `result:` lines; with a `void`
  signature it may not be used.
- Other placeholders are temporaries. They are removed with the matched code,
  so a match is rejected if one of them is still read afterwards.
- `_` matches anything without binding.

## Type constraints

`$name : <C type>` restricts what `$name` may bind to. The type is parsed with
the view's type parser and compared with the type of the bound variable or
expression. A type that does not parse is compared as text with the printed
type. `$name : /regex/` matches the printed type against a regular
expression, which is practical for long C++ names: `/string(?![>\w])/`
accepts `std::__1::string`, `class std::string*` and
`std::__1::string const&`, but not `std::vector<std::string>`.

Without a constraint the placeholder matches any type.

## Blocks and control flow

The first block is where matching starts; it may start anywhere inside an MLIL
basic block. A label before the first statement names it, so that a loop in
the pattern can branch back to it. The match must then start at the beginning
of a basic block.

A loop pattern should start at the loop, not at a `goto` that jumps into it:
a pattern whose first statement is that jump only matches code that has it,
while the labelled loop matches code that enters the loop either way. A draft
leaves out a leading jump of this kind.

`L:` starts a new block named `L`. Each block except the last must end with
`if`, `goto`, `return`, a tail call, or `noret()`. The last block is where
execution continues after the call; if it has a label it must be empty (the
join of a diamond). Every labeled block other than the last must correspond
to a whole MLIL basic block that is only reachable from inside the match,
because it is deleted.

## Statements

| Pattern                                     | Matches |
|---------------------------------------------|---------|
| `$x = expr`                                 | `MLIL_SET_VAR`; `$x` binds the variable. |
| `[expr].q = expr`                           | `MLIL_STORE`; the size suffix is optional. |
| `$x = call(f, a, b)`                        | `MLIL_CALL` with one output, or `x = v` where `v` holds the result of an earlier pure call to `f`. |
| `$x = call(f, a) - 1`                       | An assignment computed from a call's result. |
| `$x, _ = call(f, a)`                        | A call with several outputs. A trailing `...` (`$x, ... = call(f, a)`) allows further outputs, such as clobbered registers. |
| `... = call(f, a)`                          | A call whose outputs, if any, are all clobbers. |
| `call(f, a, b)`                             | A call with no outputs. A trailing `...` among the arguments allows more arguments. |
| `$lo, $hi = intrinsic("_umul128", a, b)`    | `MLIL_INTRINSIC` with that name, outputs and arguments. The name is quoted and may use `*` and `?` wildcards; `...` works as for calls. |
| `if (expr) then L1 else L2`                 | `MLIL_IF`. |
| `goto L`                                    | `MLIL_GOTO`, or falling through into `L`. |
| `return expr, expr`                         | `MLIL_RET`. |
| `return call(f, a)`                         | `MLIL_TAILCALL`. |
| `noret()`                                   | `MLIL_NORET`, ending a block that does not continue (after a call that throws). |
| `nop`                                       | `MLIL_NOP`. |
| `set_var_field.q($d, 8, $v)`                | Any other MLIL statement, written as `<op>[.size](operands)`. |
| `set_var_field($v, 0, const_data($chars, $n))` | A run of constant stores that spell a string literal; see [String literals](#string-literals). |

In a call, `f` is a symbol name (`memcmp` or `"_memcmp"`), a placeholder, or
`_`.

## Expressions

| Pattern                         | Matches |
|---------------------------------|---------|
| `$name`                         | Any expression or variable. |
| `_`                             | Anything, without binding. |
| `0x17`, `-1`, `12`              | `MLIL_CONST` or `MLIL_CONST_PTR` with that value. |
| `sym`, `"sym"`                  | A constant pointer to an address with that symbol. Names may be qualified (`std::string::size`). A quoted name may use `*` and `?` wildcards and matches any of the address's names. |
| `call(f, $s)`                   | A variable whose definition is a call to `f` with these arguments. |
| `[expr].b`                      | `MLIL_LOAD` of 1, 2, 4, 8 or 16 bytes (`b`, `w`, `d`, `q`, `o`); without a suffix, any size. |
| `&$v`                           | `MLIL_ADDRESS_OF` of a variable. |
| `sx.q(e)`, `zx.d(e)`, `low_part.b(e)`, `load_struct.q($s, 8)`, `var_field($v, 4)`, ... | Any MLIL operation by name: `<op>[.size](operands)`. |
| `-e`, `~e`                      | `MLIL_NEG`, `MLIL_NOT`. |
| `a + b`, `a - b`, `a * b`, `a u/ b`, `a s/ b`, `a u% b`, `a s% b` | Arithmetic. |
| `a & b`, `a \| b`, `a ^ b`, `a << b`, `a >> b`, `a s>> b` | Bitwise operations and shifts. |
| `a == b`, `a != b`, `a s< b`, `a u< b`, `a s<= b`, `a u<= b`, `a s> b`, `a u> b`, `a s>= b`, `a u>= b` | Comparisons. Signed and unsigned comparisons are distinct, as in MLIL. |

Precedence follows C. Infix operators match any operation size; use the
generic form (`add.q(a, b)`) when the size matters.

The address operand of a load or store is compared without regard to its
width. Binary Ninja sizes an address computed inside a structure access by
the access it feeds, so the same address may be a 1-byte expression before a
byte load and an 8-byte one before a word load.

## Results and outputs

### `result:` lines

When a function's result is always used in the same way, the compiler may
specialise the inlined body for that use and never compute the value the
signature returns. For example, when `std::string::compare` is only tested
with `== 0`, the code computes `memcmp(...) == 0 && rlen == n2` and no `int`.
A `result:` line states what the matched code's `$ret` holds, in terms of a
call to the pattern's own function:

```
signature: int `std::string::compare`(`std::__1::string` const* s, uint64_t pos, uint64_t n, `std::__1::string` const* str) __pure
result: call(std::string::compare, $s, 0, $n, $str) == 0
```

This emits `t = std::string::compare(s, 0, n, str)` followed by
`ret = t == 0`, so the call keeps its real signature. A constant argument
stands for a parameter the compiler folded away (here `pos == 0`); such a
parameter does not need to appear in the body. Each specialisation is a
different shape and needs its own chunk.

Arguments of the call in a `result:` line may be:

- a constant,
- a bound placeholder,
- an expression over bound placeholders (`$pos + 1`),
- `&$v`, the address of the variable (or object) `$v` is bound to,
- `const_data($v, $n)`, the `$n` characters `$v` is bound to, passed as a
  string literal.

### Several outputs

`result: $z = <expr>` declares that the variable bound to `$z` holds `<expr>`
after the call. `$ret` still receives the call's own value unless a
`result:` line for `$ret` says otherwise. Declared outputs may be read after
the matched code.

At least one `result:` line must contain the call to the pattern's own
function. Further lines may write `$ret` for the call's value instead. Both
of these declare that `$c` holds the call's value compared with 1:

```
result: $c = call(f, $p) != 1
```

```
result: call(f, $p)
result: $c = $ret != 1
```

For example, the compiler often keeps both the offset that `find()` computes
and a folded `== npos` test:

```
signature: uint64_t `std::string::find`(`std::__1::string` const* s, char c, uint64_t pos) __pure
result: $z = call(std::string::find, $s, $c, 0) == -1
```

### Leaving through a branch

With a `branch:` line, the pattern's `if` statements may name one label that
has no block. Taking that side leaves the matched code; otherwise execution
continues after the pattern's last block. After the call, the plugin emits a
branch on the `branch:` condition, written over `$ret`, the declared outputs
and placeholders the pattern binds. The signature must return a value:

```
branch: $ret == -1
...
if ($r == 0) then missing else found
```

A loop may branch back to an earlier label, including the first block's.

### Tail calls and throws

`return call(f, ...)` matches a tail call. A block ending in `noret()` (the
path that calls a throw helper, for example) is removed with the match.

## String literals

The statement `set_var_field($s, 0, const_data($chars, $n))` stands for the
run of stores a compiler emits for a string literal: consecutive stores of
constants into `$s`, of any widths and in any order, that together spell `$n`
characters and a terminating zero from offset 0. Overlapping stores must
agree. `$chars` receives the characters, packed little-endian, and `$n` their
count. If `$n` is already bound (the size byte is often stored first), the
run must spell exactly that many characters.

The stored values may be immediates or loads from the binary's copy of the
literal, which compilers use for longer text; a stored variable is followed
to such a load. If the object was zeroed beforehand, the run may end without
a terminator.

In a `result:` line, `const_data($chars, $n)` passes the literal back. Up to
eight characters are emitted as constant data in a register-sized value; the
plugin registers a string recognizer so that the decompiler shows it as text,
and each literal appears in the strings view with the type
*Outlined literal*. Longer literals are emitted as a pointer to the binary's
copy, so they need one: the plugin uses the address the stores loaded from,
or searches the binary for the text.

For example, with

```
signature: void `std::string::string`(`std::__1::string`* s, char const* str, uint64_t n)
$s : /string(?![>\w])/
result: call(std::string::string, &$s, const_data($chars, $n), $n)

set_var_field.b($s, 0x17, $n)
set_var_field($s, 0, const_data($chars, $n))
```

the stores that construct a string from `"cmd:"` become
`std::string::string(&prefix, "cmd:", 4)`. The stores are what the call is
for, so they are exempt from the rule that values computed by the matched
code must be dead afterwards.

Not supported: an empty literal, and a literal that fills all 22 bytes of
libc++'s short form, whose terminator is stored together with the size byte.

## Expression patterns

Some inlined functions do not get a variable of their own: `empty()` is
`size() == 0` inside an `if` condition, `front()` is a load from `data()`. A
`value:` pattern outlines an expression wherever it occurs inside an
instruction:

```
signature: bool `std::string::empty`(`std::__1::string` const* s) __pure
value: call(std::string::size, $s) == 0
```

`call(std::string::size, $s)` matches a variable defined by a call to
`std::string::size` with that argument, so expression patterns can be written
in terms of calls that other patterns produced in earlier rounds.

Each match becomes `t = empty(s)` immediately before the instruction, with
`t` in place of the expression. When the expression is the whole right-hand
side of an assignment, the assigned variable receives the result directly.
Definitions that only fed the expression, including pure calls, are removed.
If a call the expression looks through is also read elsewhere, there is no
match, since replacing the expression would show one call as two.

`value:` patterns must be `__pure`.

## Rewrite rules

The same computation can be spelled in many ways. For example, the sign test
of a byte appears as `sx.q(b) s< 0`, `var_field.d(sx.q(b), 0) s< 0`,
`(sx.d(b) & 0x80000000) != 0` and more. A rules chunk declares such
equivalences once, for all patterns:

```
rules: libc++ string idioms
rewrite: (and.d(sx.d($b), 0x80000000)) != 0   =>  sx($b) s< 0
rewrite: var_field.d(sx.q($b), 0) s< 0         =>  sx($b) s< 0
rewrite: sx($b) => zx($b) when sx($b) s>= 0
```

`rewrite: lhs => rhs` means that code spelled like `lhs` may be read as `rhs`.
When an expression does not match a pattern directly, every rule whose left
side matches the code is applied, and matching continues with the right side.
Write each pattern in one spelling and let rules translate the others.
Placeholders on the right side must appear on the left. Rules nest: a rule
for an inner expression combines with a rule for the outer one.

A rule with `when <condition>` only applies where the condition is known to
hold, that is, inside a branch of the pattern whose test implies it. In the
`short` arm of a diamond tested on `sx(b) s< 0`, the rule above may read
`sx(b)` as `zx(b)`.

A pattern's `if` also matches the negated comparison with the targets
swapped, and the complement of the code's test where a rule describes the
code's spelling (`(x & 0x80000000) == 0` where a rule handles `!= 0`).

Rules are applied when matching fails, not to the whole function in advance,
so a rule must describe a complete sub-expression.

## How code is matched

### The entry block and kept instructions

The statements of the first block match a subsequence of the instructions in
an MLIL basic block. Instructions in between stay in place, before the call,
if they have no side effects, do not write anything the pattern or the call
arguments read, and do not read anything the pattern writes. Next to a store
or call that the match removes, only instructions that do not access memory
may stay.

An instruction that breaks one of these rules is named in the diagnosis
("instruction N (`...`) between the matched statements reads X, which the
region computes", "... overwrites X, which the region reads", "... cannot
stay next to a call or store the region removes"). The fix is to add the
instruction to the pattern where it occurs. When it computes a value that is
read after the match, such as a comparison the compiler moved into a loop,
declare that value with a `result:` line as well:

```
signature: int f(int* p)
result: $c = call(f, $p) != $k

loop:
    $old = [$p].d
    $ret = $old
    $c = $ret != $k
    ...
```

### Other blocks and absorbed assignments

In the other blocks, statements must match consecutive instructions, except
that an assignment without side effects that the pattern does not mention is
absorbed: it is removed with the match, provided nothing reads it afterwards
and no call argument depends on it.

### Following definitions

When the pattern expects an expression, such as `load_struct.q($s, 0)`, and
the code has a variable instead, the matcher follows the variable's unique
definition and matches that. This handles loads the compiler moved above a
branch. Followed definitions that nothing else reads are removed with the
match; shared ones stay in place, and then fall under the rules for
instructions left among the matched statements: one that reads a value the
match computes stops the match.

Definitions are followed through plain `x = expr` assignments with a single
reaching definition. Liveness is judged from SSA uses. Copies are followed
the same way: once a placeholder stands for a variable, a copy of that
variable (`t = x`) is accepted where the pattern names the placeholder, and
the copy is removed with the match when nothing else reads it. A copy whose
variable is read elsewhere, for instance by the code after a loop, must be a
statement of the pattern. Drafts contain such copies; keep them unless the
copied variable is read nowhere else.

### Arguments and the call's position

The call takes the place of the last matched instruction of the first block.
Arguments are read at the call, so a match is rejected when an instruction
that stays could overwrite a variable an argument reads, on any path between
where the argument was observed and the call.

### Objects held in variables

An object passed by value or kept in a local is the variable itself in MLIL:
its fields are `var_field` accesses and its address is `&s`, where a pattern
written for a pointer expects `load_struct`. The rule

```
rewrite: var_field($v, $off) => load_struct(&$v, $off)
```

bridges the two. The placeholder then stands for the object's address (its
type is checked as a pointer to the variable's type), the call receives `&s`,
and a variable holding that address (`p = &s`) is accepted wherever the
pattern reads `$s`.

### Members of larger objects

An object is often a member of something larger, such as `e->name` or
`this->name`. The field offsets in the code are then the member's offset plus
the pattern's, and the base the code addresses has the larger object's type.
When a field operation (`load_struct`, `store_struct`, `var_field`,
`set_var_field`, `address_of_field`) does not match directly, the matcher
looks up the member of the base's type that holds the code's offset. If the
pattern's offset is the code's offset minus the member's, and the member's
type satisfies the constraint, the placeholder stands for that member. Every
later access through the placeholder must fall in the same member.

The same applies where the placeholder is first met as a plain value: a
pointer whose own type fails the constraint stands for the member at its
offset 0 when that member's type fits. The call receives `&var.member` for a
local object and `p + offset` (shown as `&p->member`) for a pointer.

### Global objects

Binary Ninja folds a global's address and a field offset into one constant
pointer, so a field of a global `g` is a plain load or store at `&g + offset`
(`[&g..field].b`), not a `load_struct`. A field operation in a pattern
therefore also matches a load or store at a constant address. The placeholder
then stands for the object at that address minus the pattern's offset: its
address for `load_struct` and `store_struct`, the object itself for
`var_field` and `set_var_field` (whose `&$s` is the address).

The object is typed by the data variable at that address, or by the member
that starts there when the global is a struct. A global without a type, or of
a type the constraint rejects, does not match. A bare `&g` binds the same
way, and the calls come out as `f(&g)`.

### Fused calls

When two inlined functions test the same condition, the compiler tests it
once and specialises the code under each arm, often duplicating everything
that follows. No diamond is left for a pattern to match.

A pure diamond pattern `if G then $ret = A else $ret = B` says that the
function equals `A` where `G` holds and `B` where it does not. For every `if`
whose test matches such a `G`, the plugin checks whether the two arms are the
same except for pairs of expressions that a pure pattern explains as its `A`
and `B`, with the same arguments. If so, it emits one call per explained
value above the `if`, uses the results in the kept arm, and removes the other
arm and the test.

The arm comparison also allows:

- **An assignment in one arm only.** If a pure pattern explains it, it is
  dropped and the call's result is used where it was read. Where a read could
  also see another value, the assignment is kept as `v = <call result>`.
- **A value set only in the removed arm** that the code after the join
  reads. If a pattern explains it, the call's result is used there;
  otherwise the arms are not fused.
- **Inverted tests inside the arms.** `if (x != c)` in one arm pairs with
  `if (x == c)` in the other, with the targets swapped.
- **Either arm as the one kept.**
- **Blocks that only contain a `goto`.** Targets are compared after following
  them.
- **Statement runs.** A void pattern shaped like a diamond or a triangle with
  a `result:` call is recognised at the start of both arms, followed by
  duplicated code. The run is removed from both arms and one call is emitted
  above the `if`.

Variables may differ between the arms only when both are defined inside the
arms and neither is read after them.

Plain matches are found first. The fused pass then runs on the blocks they
did not claim.

### Rounds

After the matches of a round are rewritten, the function is matched again,
up to 12 rounds. Patterns can therefore match calls that earlier rounds
produced: `call(f, ...)` in a pattern matches a variable defined by a call to
`f`.

## What the rewrite produces

The plugin builds a new MLIL function: instructions outside the matches are
copied, each match becomes `ret = f(args)` followed by a `goto` to the join
when it spanned several blocks, and the function is finalized and replaces
the MLIL in the analysis.

Each signature has a call target: a function-typed data variable with an
external symbol in a synthetic `outlined` section, which Outliner adds after
the end of the binary. It is created when the pattern is saved, so the
decompiler shows the call with the signature's name, parameter names and
types. When no pattern uses a signature any more, its
symbol and data variable are removed and the address is reused, so a renamed
function keeps its address.

## Limitations

- Statements match whole MLIL instructions. Use a `value:` pattern for code
  that was folded into a larger expression.
- Untyped calls, syscalls, jump tables and `ASSERT` statements cannot be
  written in patterns; **Show Function As Pattern Text** shows them as
  `# unsupported`. An intrinsic can only be matched as a statement.
- Fused calls are only found when the arms differ in explained values and
  unmatched assignments without side effects.
- A shape the compiler produces with different constants or a different
  schedule needs its own chunk, unless a rewrite rule covers it.
- A pattern drafted from code that uses a global contains the global's
  addresses as constants.
