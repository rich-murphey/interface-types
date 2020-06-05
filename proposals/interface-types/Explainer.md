# Interface Types Proposal

The proposal adds a new set of **interface types** to WebAssembly that describe
high-level values (like strings, lists, records and variants) along with a new
set of highly-optimizable instructions that produce and consume interface types.
The proposal is semantically layered on top of the WebAssembly [core spec] and
thus can be implemented in terms of an unmodified core WebAssembly
implementation. This new layer wraps WebAssembly's *core modules* with a new
*kind* of WebAssembly module called a **component**. Components provide the
WebAssembly ecosystem a new highly embeddable, composable, virtualizable and
language-neutral unit of code reuse and distribution.

1. [Problem](#problem)
2. [Use Cases](#use-cases)
3. [Additional Requirements](#additional-requirements)
4. [Proposal](#proposal)
   1. [Interface Types](#interface-types)
   2. [Lifting and Lowering Instructions](#lifting-and-lowering-instructions)
      1. [Integers](#lifting-and-lowering-integers)
      2. [Characters](#lifting-and-lowering-characters)
      3. [Lists](#lifting-and-lowering-lists)
      4. [Records](#lifting-and-lowering-records)
      5. [Variants](#lifting-and-lowering-variants)
   3. [Adapter Functions](#adapter-functions)
   4. [Components](#components)
   5. [Lazy Lifting: Avoiding Intermediate Copies by Design](#lazy-lifting-avoiding-intermediate-copies-by-design)
   6. [Ownership Instructions: Reliably Releasing Resources In the Presence of Laziness](#ownership-instructions-reliably-releasing-resources-in-the-presence-of-laziness)
   7. [Exception and Trap Safety](#exception-and-trap-safety)
5. [Use Cases Revisited](#use-cases-revisited)
6. [Additional Requirements Revisited](#additional-requirements-revisited)
7. [FAQ](#FAQ)
8. [TODO](#TODO)


## Problem

As a compiler target, WebAssembly provides only low-level types that aim to be
as close to the underlying machine as possible allowing each source language to
implement its own high-level types efficiently on top of the low-level types.
However, when modules from multiple languages need to communicate with each
other or the host, this raises the question of how to exchange high-level
values at the interface.
 
The current best approach for dealing with this problem is to generate
JavaScript *glue code* that uses the powerful [JS API] to convert between
values at interface boundaries. However, the JavaScript glue code approach has
several limitations:
* It depends on the host including a JavaScript implementation, which not all
  hosts do or can.
* JavaScript glue code incurs unnecessary overhead due to copying, transition
  costs and loss of static type information.

Ideally, a solution to this problem would only depends on language-independent
WebAssembly standards or conventions.


## Use Cases

To help motivate the proposed solution, we consider 3 use cases. After the
proposal is introduced, the use cases are [revisited below](#use-cases-revisited).


### Optimizing calls to Web APIs

A long-standing source of friction between WebAssembly and the rest of the
Web platform (and the original motivating use case for this proposal) is that
calling Web APIs from WebAssembly usually requires thunking through JavaScript
which hurts performance and adds extra complexity for developers to think
about. Technically, since they are exported as JavaScript functions, Web
IDL-defined functions can be directly imported and called by WebAssembly
through the [JS API]. However, Web IDL functions usually take and produce
high-level Web IDL types like [`DOMString`] and [Sequence] while WebAssembly
can only pass numbers.

With Interface Types, ideally WebAssembly could create Web IDL-compatible
high-level types and pass them directly to statically-typed browser entry
points without transit through JS.


### Defining language-neutral interfaces like WASI

While many [WASI] signatures can be expressed in terms of `i32`s and,
in the future, references to [type imports][Type Import], there is still a need
for WASI functions to take and return higher-level value types like strings or
lists. Currently, these values are specified in terms of linear memory. For
example, in [`path_open`], a string is passed as a pair of `i32`s which
represent the offset and length, respectively, of the string in linear memory.

However, specifying this single, fixed representation for data types like
strings will become problematic if:
* WebAssembly gets access to GC memory with the [GC] proposal and the caller
  wants to pass a `ref array u8`;
* the host has a native string type which is not the same as the
  GC `ref array u8` (e.g., a JS/DOM string) which WASI would ideally accept
  without copy; or
* the need arises to allow more than just UTF-8 encoding.

Ideally, WASI APIs would be able to use simple high-level types that could be
constructed from a variety of source representations.

There's also another, more subtle problem with passing `i32`s: they implicitly
refer to the caller's memory. Currently, this requires that all WASI client
modules must export their memory with a designated name (`"memory"`) and it
also requires special tricks for WASI implementations to be able to find
this memory. Ideally, WASI APIs would simply take values without the client
or the implementation needing to expose its memory at all.


### Enabling Shared-Nothing Linking of WebAssembly Modules

While WebAssembly intentionally supports [native dynamic linking]
(a.k.a. "shared-everything" linking; cf. [shared-everything dynamic linking in
the Module Linking proposal][shared-everything-example]), this type of linking
is more fragile:
* Modules must carefully coordinate (at the toolchain and source level) to
  share data and generally avoid clobbering each other.
* Modules must agree on versions for common shared libraries since the
  libraries' state is generally shared by all clients.
* Corruption in one module can affect other modules, with certain bugs
  only manifesting with certain combinations of modules.
* Modules are less able to encapsulate, leading to unwanted representation
  dependencies or violations of the Principle of Least Authority.

In contrast, "shared-nothing" linking refers to a linking scheme in which each
module defines and encapsulates its own memories and tables and, in doing so,
ensures a degree of isolation that mitigates the sources of fragility listed
above. However, there is currently no host-independent way to implement even
basic shared-nothing linking operations like copying an array of bytes from one
module's linear memory to another.

With interface types available to use at the boundary between two
modules, exports and imports can take, e.g., an abstract sequence of bytes,
or a string, or a sequence of pairs of strings and integers, etc. It is then
the wasm engine that takes care of copying data between two modules' linear
memories, allowing all modules to fully encapsulate their state.


### Scoping Shared-Everything Linking

Shared-nothing linking should not, however, be mutually exclusive with
shared-everything linking: just because two modules don't share state doesn't
mean they can't share code. Indeed, the [Module Linking] proposal [explicitly
supports][shared-everything-use-case] having multiple wasm programs that share
modules, but not memories, but there is no provision for how those independent
programs can communicate with each other. While they could communicate
indirectly through a pipe/channel/socket/message API, with Interface Types,
they should additionally be able to be communicate efficiently through
synchronous function calls.

TODO:
* show diagram that shows two-level topology as desired end-state
  (using "component")


## Additional Requirements

TODO:
* Avoid baking in the assumption of linear memory or GC and allow
  zero-copy when both sides use a compatible, immutable, identity-less
  GC references.
* Allow efficient conversion to and from host values (e.g., JS strings)
  with zero copy possible when both sides agree on representation.
* Avoid committing to a single value representation for all time (e.g.,
  string encoding).
* Avoid unnecessary copies to temporaries and O(n) engine-internal
  allocations (not in linear or GC memory). Reducing copy overhead allows
  finer-granularity use of shared-nothing linking, which are, in turn, better
  for security and composability.
* Avoid reliance on a sufficiently-smart compiler to optimize effectively;
  optimization should be enabled by construction.
* Allow semver-compatible interface evolution with similar expressivity to
  what is enabled by ProtoBuf without runtime overhead.
* Avoid fragile ABIs that allow sloppy or out-of-date toolchains to manifest
  late or hard-to-debug errors when linked with well-behaved new toolchains.


## Proposal

The proposal is introduced bottom-up, starting with the new types, then the
instructions that produce/consume the new types, then the new functions that can
use the new instructions, then the new kind of module that can contain the new
functions.


### Interface Types

The wasm core spec defines the set [`valtype`] of low-level value types (`i32`,
`i64`, `f32`, `f64` and a growing set of [reference types], starting with
`externref` and `funcref`). The Interface Types proposal introduces a *new*
set `intertype` of *high-level* value types which are mostly disjoint from
`valtype`. The set `intertype` is inductively generated from the grammar below,
containing only types of finite nesting (unlike `valtype` which, starting with
the [function references] proposal, can contain cyclic function types).

```
intertype ::= f32 | f64
            | s8 | s16 | s32 | s64 | u8 | u16 | u32 | u64
            | char
            | (list <intertype>)
            | (record (field <name> <id>? <intertype>)+)
            | (variant (case <name> <id>? <intertype>*)+)
```
With core wasm's `valtype`, reference values refer to mutable state with
identity and thus subtyping is inherently non-coercive and constrained by
low-level memory layout considerations. In contrast, `intertype` values are
transitively immutable and, to allow more flexible backwards-compatible API
evolution, `intertype` subtyping instead has coercion semantics. Since copying
is essential to the use of interface types in the first place, the implicit
coercion functions can be folded into the copy at little, if any, extra cost.

The type constructors of `intertype` and their allowed subtyping are summarized
as follows:

| Type Constructor | Description of values | Subtyping allowed |
| ---------------- | --------------------- | ---------------- |
| `f32`, `f64` | same as core wasm | `f32 <: f64` |
| `s8`, `u8`, `s16`, `u16`, `s32`, `u32`, `s64`, `u64` | explicitly signed, ranged integer values | `I1 <: I2` if `I1`'s range is included in `I2`'s |
| `char` | a [Unicode scalar value] | |
| `list` | a sequence of homogeneous `intertype` values with a known length | `(list T) <: (list T')` if `T <: T'` |
| `record` | a tuple of named heterogeneous values | `(record Tᵢ*) <: (record T'ᵢ)` if `Tᵢ <: T'ᵢ`, matched by name, allowing `T` to have extra, ignored fields |
| `variant` | a discriminated union of named heterogeneous tuples of values | `(variant Tᵢ*) <: (variant T'ᵢ)` if `Tᵢ <: T'ᵢ`, matched by name, allowing `T'` to have extra, ignored cases |

While these types are sufficiently general to capture a number of
more-specialized types that often arise in interfaces, it can still be
beneficial for toolchains to have the specialized types explicitly represented
in the signature in order to allow more idiomatic source-level types. Thus,
several text-format and binary-format [abbreviations] are included. In the
notation below, the type on the left-hand side of the `≡` is expanded during
parsing to the right-hand side. Analogous decoding productions are added to
binary format.
```
                           string ≡ (list char)
                             bool ≡ (variant (case "True") (case "False"))
                   (enum <name>+) ≡ (variant (case <name>)+)
             (option <intertype>) ≡ (variant (case "None") (case "Some" <intertype>))
(result <intertype> <intertype>?) ≡ (variant (case "Ok" <intertype>) (case "Error" <intertype>?))
```
Given these abbreviations, a toolchain can generate the specialized
source-language string, boolean, optional, enumeration and result types.
In the case of `result`, a language with exceptions could translate the `Error`
case into a thrown exception.

An example type using these type constructors together is:
```
(list
  (record
    (field "person"
      (record
        (field "name" string)
        (field "age" u8)))
    (field "mood"
      (enum "happy" "sad" "angry" "confused"))))
```
Should consumers of this type wish to start considering ages beyond 256 or moods
beyond these four, due to the subtyping rules mentioned above, the type could be
backwards-compatibly changed to replace `u8` with `u16`, add new moods to
the `enum` or transform the `enum` into a full `variant` whose cases have
payloads.


### Lifting and Lowering Instructions

Along with each interface type, the proposal adds new instructions for producing 
and consuming the interface type. These instructions fall into two categories:
* **Lifting instructions** produce interface types, going from
  lower-level types to higher-level types.
* **Lowering instructions** consume interface types, going from higher-level
  types to lower-level types.

Lifting and lowering instructions thus act as the "bridge" between core wasm and
interface types and their instruction signatures include types from both
`valtype` and `intertype`. By having the conversion between `valtype` and
`intertype` explicit and programmable, this proposal allows for a wide gamut
of low-level value representations to be passed directly *in situ* (without the
wasm module performing an intermediate serialization step) and for this space to
be expanded over time.

As with core wasm instructions, lifting and lowering instructions can dynamically
fail and, when they do, they do so by trapping. In the future, alternative failure
options (like throwing an [exception]) may be added.

The following subsections list the initial proposed set of lifting and lowering
instructions, grouped by interface type.

#### Lifting and Lowering Integers

Similar to the core wasm numeric conversions, a matrix of integral conversion
instructions are given which allow converting between the 2 sign-less core
wasm integer types and the 8 explicitly-signed integral interface types:
```
uX.from_iY : [iY] -> [uX]
sX.from_iY : [iY] -> [sX]
iY.from_uX : [uX] -> [iY]
iY.from_sX : [sX] -> [iY]
where
 - X is one of 8, 16, 32 or 64
 - Y is one of 32 or 64
```

If the destination bitwidth is smaller than the source bitwidth and the dynamic
value is outside of the destination's range (determined by the explicit
signedness of the instruction), the instruction traps.

For example, the following instruction sequence gives an explicit sign to an
otherwise-ambiguous `i32` with its high-bit set:
```wasm
i32.const 0x80000000  ;; push i32
u32.from_i32  ;; pop i32, push u32
```

#### Lifting and Lowering Characters

TODO: consider
* move Characters to the end, and rename to "Lifting and Lowering String"
* move lists to after records and variants (so right before strings)
* in the string section just show how the various representations come together
  in terms of lists

A character is defined as a [Unicode scalar value], which means a positive
integer in the ranges [0, 0xD7FF] or [0xE000, 0x10FFFF], inclusive. (The hole
in the middle of those two ranges corresponds to the [surrogate code points][surrogate code point].)

The character lifting and lowering instruction signatures are:
```
char.lift : [i32] -> [char]
char.lower : [char] -> [i32]
```
While these signatures may superficially look like a requirement that all
strings are encoded with 4-byte code units, that is not the case: `char.lift`
is only used after decoding to lift the computed code point into the abstract
`char` type. Conversely, `char.lower` is only used before encoding into
whatever representation.

For example, `char.lift` can be used to decode a [Latin1] string:
```wasm
(i32.load8_u (local.get $ptr))
char.lift
```
or a [UCS-2] string:
```wasm
(i32.load16_u (local.get $ptr))
char.lift
```
or a [UTF-16LE] string:
```wasm
(local $codePt i32 (i32.load16_u (local.get $ptr)))
block $surrogatePair
  ;; decode a high surrogate pair into codePt if necessary:
  (br_if $surrogatePair (i32.lt_u (local.get $codePt) (i32.const 0xD800)))
  (br_if $surrogatePair (i32.ge_u (local.get $codePt) (i32.const 0xE000)))
  block $illegal
    (br_if $illegal (i32.ge_u $bad (local.get $codePt) (i32.const 0xDC00)))
    unreachable
  end
  let
    (local $high i32 (i32.load16_u offset=2 (local.get $ptr)))
    block $illegal
      (br_if $illegal (i32.lt_u (local.get $high) (i32.const 0xDC00)))
      (br_if $illegal (i32.gt_u (local.get $high) (i32.const 0xDFFF)))
      unreachable
    end
    (local.set $codePt
      (i32.add (i32.const 0x10000)
        (i32.add (i32.shl (i32.sub (local.get $codePt) (i32.const 0xDB00)) (i32.const 10))
          (i32.sub (local.get $high) (i32.const 0xDC00)))))
  end
end
local.get $codePt
char.lift
```
When one of the above expressions is placed in the loop body of a list lifting
instruction (along with appropriate `$ptr`-updating code), the net result is to
lift a `string`. This will be discussed more in the next section.

Usage of `char.lower` is symmetric and gives control over how to handle
out-of-range code points to the consumer code. For example, lowering [Latin1]
could choose to trap or, in the future, `throw`:
```wasm
char.lower
let (local $codePt i32)
  block $illegal
    br_if $ok (local.get $codePt) (i32.le_u (local.get $codePt) (i32.const 0xFF))
    unreachable
  end
  (i32.store8 (local.get $ptr) (local.get $codePt))
end
```
Together, character lifting and lowering instructions allow producers and
consumers of `char` to use different encodings.

#### Lifting and Lowering Lists

Since lists contain `intertype` elements, list lifting and lowering
instructions must contain lifting and lowering instructions for the element
type. Consequently, list lifting and lowering instructions are compound
instructions, containing bodies that are executed repeatedly, like the body of
a loop.

The list lifting instruction's signature is:
```wasm
list.lift T* $L <instr>* end : [T*, i32] -> [$L]
where:
  - $L refers to an (list E)
  - <instr>* : [T*] -> [T*, E]
```
The `i32` operand to `list.lift` is the list length and determines the number
of times the list body (`<instr>*`) will be executed. The `T*` values passed
into `list.lift` are passed into the first iteration of the loop body. The `T*`
values passed out of the body are passed into the next iteration. Thus, the
tuple `T*` describes the *loop-carried state* and gives the loop body
flexibility to define how to iterate over the list representation. The sequence
of `E` values produced by the loop body define the final `list` value.

The list lowering instruction is symmetric, but generalized to allow arbitrary
state to be passed both into *and* out of the loop body:
```wasm
list.lower T* $L <instr>* end : [T*, $L] -> [T*]
where
  - $L refers to an (list E)
  - <instr>* : [T*, E] -> [T*]
```
Thus, `list.lower` can either be given a pre-allocated array to write into or
perform (re)allocation during iteration, producing the final result.

To enable memory pre-allocation, the length of a `list` can be extracted
with the `list.count` instruction:
```wasm
list.count $L : [$L] -> [i32]
```

For example, a `string`, which is an abbreviation for a `(list char)`, can be
lifted from a [Latin1]-encoded string as follows:
```wasm
;; the stack contains [ptr:i32, length:i32]
list.lift i32 string
  let (result i32 string) (local $ptr i32)
    (i32.add (local.get $ptr) (i32.const 1))  ;; next iteration's value of $ptr
    (char.lift (i32.load8_u (local.get $ptr)))
  end
end
```
Latin1 is a simple case, but more complicated encodings like UTF-8 or UTF-16
could be used instead, as demonstrated in the [previous section](#lifting-and-lowering-characters).

To consume a `string` as, say, UTF-16, the following skeleton of code could be
used (UTF-16LE details ommitted for brevity):
```wasm
;; the stack contains [string]
let (local $str string)
  i32.const 0  ;; initialize $size
  local.get $str
  list.lower i32 string
    let (result i32) (local $size i32) (local $codePt char)
      local.get $size
      ;; compute number of code units to encode $codePt
      i32.add
    end
  end
  let (local $size i32)
    (call $malloc (local.get $size))
    local.get $str
    list.lower i32 string
      let (result i32) (local $current i32) (local $codePt char)
        ;; encode $codePt starting at $current
        local.get $current
        ;; push number of bytes stored
        i32.add
      end
    end
  end
end
```
Note, this code uses `list.lower` *twice*: once to compute the number of bytes
to pass to `malloc` and once to write the bytes into the allocated array. An
alternative scheme would be to first allocate an approximately-sized buffer
(using `list.count` to estimate) which is reallocated as needed during a single
`list.lower`.

While `list.lift` and `list.lower` cover the general case of list and string
lifting and lowering, additional performance can be had in the special case
where both sides use the exact same representation. For example, when passing a
`string` to a host call, if the host's native representation is UTF-8 and the
`string` is lifted from UTF-8 bytes in linear memory, it is possible to avoid
copying entirely by passing the host a raw pointer. When passing a `string`
between wasm modules, if both sides use UTF-8, the consumer should be able to
simply reuse the producer's exact encoding length.

The Interface Types proposal enables this extra degree of optimization, while
interoperating with the general case by adding a second set of lifting/lowering
instructions that fix a single linear memory layout:
```wasm
list.lift_array $L <memory>? : [i32, i32] -> [$L]
list.lower_array $L <memory>? : [$L, i32] -> []
list.array_size $L : [$L] -> [i32]
where
  - $L refers to an (list E) where E is a float, integer or character type
  - <memory>? defaults to index 0
```
By fixing a single memory layout, `list.size` can be O(1) when given a list
lifted by `list.lift_array`. When lifting a `string` (`(list char)`), the
canonical memory layout used is [UTF-8], using the UTF-8 decoding algorithm
specified by the [Encoding API] with [error mode] set to `fatal` and errors
generating traps. In the future, the set of allowed element types could be
expanded to include compound types, but for now the set is kept to a
conservative minimum set.

With these new instructions, a UTF-8 string can be simply and efficiently
lifted by a single instruction:
```wasm
;; the stack contains [ptr:i32, length:i32]
list.lift_array string
```
and lowered with a couple:
```wasm
;; the stack contains [string]
let (result i32 i32)
  (local $str string)
  (local $ptr (call $malloc (list.array_size string (local.get $str))))
  (local $count (list.count $str))
  (list.lower_array string (local.get $ptr) (local.get $count))
  local.get $ptr
  local.get $count
end
```

Importantly, a list lifted by `list.lift_array` can be consumed by
`list.lower`, and vice versa, because in all cases the `list` type sits in the
middle defining a uniform set of abstract list values. The existence of the
array lifting/lowering instructions does however introduce a preferred default
representation for toolchains and developers to use when possible, having the
net effect of aligning the ecosystem toward optimal performance without adding
performance cliffs.

#### Lifting and Lowering Records

Records are simply tuples of smaller interface values and thus can be produced
and consumed by simple stack operations:
```wasm
record.lift $R : [$F*] -> [$R]
record.lower $R : [$R] -> [$F*]
where
  - $R refers to a (record (field <name> $F)*)
```

For example, given a type definition of a record type:
```wasm
(type $Coord (record (field "x" s32) (field "y" s32)))
```
a `$Coord` value can be lifted from two `i32`s by the instruction sequence:
```wasm
(s32.from_i32 (i32.const 1))  ;; push s32
(s32.from_i32 (i32.const 2))  ;; push s32
record.lift $Coord  ;; pop two s32s, push record
```
and lowered back into two `i32`s by the instruction sequence:
```wasm
record.lower $Coord  ;; pop record, push two s32s
let (result i32 i32) (local $x s32) (local $y s32)  ;; pop s32s into locals
  (i32.from_s32 (local.get $x))  ;; push i32
  (i32.from_s32 (local.get $y))  ;; push i32
end
```

#### Lifting and Lowering Variants

Like lists, variant lifting and lowering instructions are compound, with a body
that encapsulates the control flow inherent in producing or consuming a
variant.

The variant lifting instruction's signature is:
```wasm
variant.lift T* $V <instr>* end : [T*] -> [$V]
where
 - $V refers to a (variant (case <name> C*)* (case <name> D*))
 - <instr>* : [T*] -> [D*]
```
Here, `(case <name> D*)` refers to the last of the cases, and thus the body
(`<instr>*`) is a sequence of instructions that, on exit, produce the last
case of the variant.

To lift all the other, non-last cases, there is a separate lifting instruction
which can be used within the body of a `variant.lift`:
```wasm
variant.case $case : [C*] -> [t*]
where
 - $case is the index of a `(case <name> C*)` in an enclosing `variant.lift`
 - `t*` is anything (like `br`, this instruction is [stack polymorphic])
```
The effect of this instruction is to produce a variant value containing the
indicated `$case` and `C*` payload, transferring control flow to the `end` of
the `variant.lift`. Because `variant.case` is an unconditional branch, this
instruction is [stack polymorphic] with its result type `t*` unbound.

To lift a variant, then, core wasm control flow instructions can be used to
conditionally execute different `variant.case` instructions based on the
dynamic values of the `T*` passed into the `variant.lift`.

As an example, given a type definition of a variant:
```wasm
(type $MaybeNum (variant (case $Some "Some" s32) (case $None "None")))
```
a `$MaybeNum` can be lifted from a single `i32` that uses a designated
sentinel value to represent the `None` case:
```wasm
variant.lift i32 $MaybeNum
  let (local $packed i32)
    block $some_case
      (br_if $some_case (i32.eq (local.get $packed) (i32.const -1)))
      (s32.from_i32 (local.get $packed))
      variant.lift $Some
    end
  end
  ;; fallthrough to produce the $None case, which has no payload
end
```
Here, a single `br_if` is used but, for more complicated representations,
arbitrary wasm control flow can be used to efficiently discriminate the
cases of the variant.

In contrast to lifting, variant embeds the branching on the variant cases with
directly into the instruction:
```wasm
variant.lower T1* $V T2* [case <instr>* end]* : [T1* $V] -> [T2*]
where
 - $V refers to a (variant (case <name> C*)*)
 - the number of cases in $V and variant.lower's body is the same
 - for each case: <instr>* : [T1* C*] -> [T2*]
```
This instruction allows arbitrary values to flow into and out of the cases,
which enables multiple lowering implementation strategies: writing into
an already-allocated memory location that is passed in or producing new values
that flow out.

Extending the example above, the variant `$MaybeNum` could be instead lowered
into two `i32`s (the first a boolean, the second the payload of `Some`):
```wasm
variant.lower $MaybeNum i32 i32
  case  ;; for the "None" case, the stack is empty on entry
    i32.const 0
    i32.const 0
  end
  case  ;; for the "Some" case, the stack contains an s32 on entry
    i32.const
    i32.from_i32
  end
end
```
As with `list`, these two unrelated representations of the same variant
can be used together because they meet in the middle at the abstract
`variant` type.


### Adapter Functions

Because the Interface Types proposal is *layered* on the core wasm spec (in
the same manner as the [JS API], [C API] and [Web API]), the new types and
instructions introduced above can't simply be used in core wasm functions
because core wasm functions can only contain *core* wasm types and instructions.
Instead, the proposal defines a *new kind* of function, distinct from existing
core wasm functions, called an **adapter function**. Adapter functions have the
same structure as core functions but allow a different set of types and
instructions.

For types, adapter functions allow a superset of the core wasm `valtype`:
```
adaptertype ::= valtype | intertype
```
By allowing a mix of both `valtype` and `intertype`, adapter functions enable
the use of lifting and lowering instructions, which manipulate both.

Similarly, for instructions, adapter functions allow a superset of the core
wasm [`instr`]:
```
adapterinstr ::= instr | new instructions in this proposal
```

TODO: rewrite this

For instructions, adapter functions do *not* similarly extend the core wasm
set of instructions ([`instr`]) with lifting and lowering instructions. The
reason is that adapter functions are designed to ensure a new property that is
not in general ensured by core wasm functions:

> The **Single Reaching Lift (SRL)** property requires that each use of an
> interface type is reached by exactly one lifting instruction definition.

The reason the SRL property is valuable is described in more detail in a
[later section](#lazy-lifting-avoiding-intermediate-copies-by-design), but a
short summary is that SRL allows guaranteed elimination of intermediate copies
without relying on compiler magic. 

TODO: what we need is:
* since we're importing core instruction validation/execution, they reject
  `intertype` types and values.
  * Exception: `drop` works, b/c it's polymorphic. `select` does not.
* `intertype` values may only be manipulated by new instructions
* lifting, lowering are new, preserve SRL
* enhanced:
  * call: require non-recursive --> inline
  * let: simply allow intertype
  * local.set: not allowed for intertype

To ensure SRL, adapter functions start with `instr` and remove all the
[control instructions] with the exception of:
* `unreachable`, since traps cannot rejoin
* `throw` (but not `try`), when [exception handling] is added
* `call`, by restricting it to be non-recursive and then interpreting the
  callee to be inlined into the caller

This definition is fairly conservative and could even be loosened, while
preserving SRL, to allow blocks and branches when  interface types were not
present in the block types.

With this restriction in place, a new set `adapterinstr` is defined which
contains the remainder of `instr` extended with the new instructions added
by this proposal.

With `valtype` replaced by `adaptertype` and `instr` replaced by
`adapterinstr`, adapter functions work just like core wasm functions. For
example, the following is a trivial adapter function:
```wasm
(func (result s8)
  i32.const 42
  s8.from_i32
)
```

In general, we can categorize adapter functions into three categories:

**Export adapter functions** use only `intertype` in their signatures and use
lifting and lowering instructions to wrap a call a core wasm function. An
example export adapter function is:
```wasm
(func $print_adapter (param $msg string)
  (call $malloc_cstr (string.size (local.get $msg)))
  let (local $cstr i32)
    (string.lower_memory (local.get $cstr) (local.get $msg))
    call $core_print
  end
)
```

**Import adapter functions** use only `valtype` in their signatures and use
lifting and lowering instructions to wrap a call to an imported function
that only uses `intertype` in its signature. An example import adapter function
is:
```wasm
(func $log_adapter (param $msgPtr i32) (param $msgLen i32)
  (string.lift_memory (local.get $msgPtr) (local.get $msgLen))
  call $imported_log
)
```

**Helper adapter functions** contain an arbitrary mix of types and are used
to implement export and import adapter functions. An example might be a
helper function that lifts a C-string and thus be used by both an
export adapter (for lifting parameters) or an import adapter (for lifting
results):
```wasm
(func $lift_cstring (param $cstr i32) (result string)
  local.get $cstr
  (call $strlen (local.get $cstr))
  string.lift_memory
)
```


### Components

TODO:
* ok, we have a new kind of adapter function, where does it go?
  * can't go in existing core wasm section (b/c layered spec)
* put it in a custom section?
  * well, we also need new types, new imports, new exports, ...
  * it'd be like a whole mini-module
  * and how do we "link" it to the core module?
* fundamentally, interface types "wraps" the core wasm spec
* so we define a new kind of "interface type" module that wraps a core module
* "interface type module" sounds bad, so call it **component** (historical reason...)
* components contain
  * type section, allowing core and interface types
  * import section: no memory/table/global, intertyped function, modules and components
  * function+code section: only adapter functions
  * start section
  * export section: only functions with `intertype` signatures
  * module/modulecode section: nested module or component instances
  * instance section: instantiation of modules or components
  * alias section: alias either module or component instances
* Examples
* Note on validation: allow function section in the mix
  * Component instances created *before* nested instances
  * Nested instances are stateful
  * Calling export of nested instance before created traps
  * Component start function called after last nested instance created
* Binary format
  * core wasm module physically embedded (in chars/bytes).  Just like .wast embeds .wat
  * can reuse the same text/binary parser/decoder and validator: just conditionalize on "kind"
    * in text format: `component`
    * in binary format: split "version" `u32` into `version` and `kind` `u16`s, use new `kind`


### Lazy Lifting: Avoiding Intermediate Copies By Design

One of the [Additional Requirements](#additional-requirements) mentioned above
is to avoid intermediate O(n) copies when using Interface Types. Without
further nuance, the instructions presented in the previous section would appear
to violate that requirement by requiring an intermediate copy to reify
`interval` values between lifting and lowering.

For example, in the following instruction sequence:
```wasm
(string.lift_memory (call $create_string))
...
let (local $str string)
  (call $malloc (string.size (local.get $str)))
  local.get $str
  string.lower_memory
  ...
end
```
while we might hope that the wasm engine would be able to copy directly
from the source memory passed to `string.lift_memory` to the destination
memory passed to `string.lower_memory`, from the engine's perspective, the
intervening call to `$malloc` may mutate the linear memory read by
`string.lift_memory` and thus an intermediate copy must be made just in case.
This is also the simplest possible case, so we can conclude that, without
any help, most interface-typed values would end up with an intermediate copy.

The root problem here is that standard [eager evaluation] semantics specify
the order effects to be:
1. read from linear memory
2. perform arbitrary side effects
3. write to linear memory

What we'd like is to reorder steps 1 and 2 so that the read was always
immediately followed by the write. But...

TODO:
* these will practically almost always be in separate adapter functions, so we
  just can't do that.
* what we need is to somehow change the *spec* so that the read always happened
  *right before* the write
* How? We can employ a less-common evaluation strategy called [lazy evaluation],
  but only for lifting instructions.
* The idea behind lazy evaluation is ...
* Haskell has this. Often coupled with purity, so reordering is unobservable.
  Laziness + Side Effects usually equals madness, but in this case, it's exactly
  what we just said we wanted.
* In the context of adapters at interface boundaries copying from source to 
  destination, there should be no problem. The compiler can ensure this.
  Not something programmer writes by hand.

* But doesn't lazy evaluation add overhead? Not with the static use-def
  property. Compiler can *statically* determine where a lifting instruction
  is consumed and thus compile *all* lifting and lowering instructions into
  fused direct-copy operations.

* For example, this byte list lifting+lowering
  * Example
* would be fused by the compiler into, effectively, this core wasm code:
  * Example


### Ownership Instructions: Reliably Releasing Resources in the Presence of Laziness

TODO
* Laziness avoids copies, but adds complexity in side-effectful world
  (which is why laziness is usually coupled with purity).
* Mostly it's not a problem for interface types b/c they're only used
  at module boundaries and can be generated by a compiler that is
  careful.
* There is one persistent issue though: ownership.
* In particular: how does m

* What to do when function returns interface value?
* How to pass value that is freed right after being read?
* With laziness: don't have a good place to put the 'free`
* It depends on the lifetime of the lazy value
* So add first-class instruction and type to `adaptertype`: `(own T)`


### Exception and Trap Safety

TODO
* Default: exceptions turn to traps at boundary
* Why necessary default
* Puts the burden on exception-safe languages to make explicit as variant return type
* In theory, could add exception-specification to interface types, but it is
  morally equivalent, especially once we recognize the `result` abbreviation

TODO
* Early wasm discussions: can you observe memory after trap? Call into an instance?
* Yes, we had to because...
* But this is terrible for the ecosystem
* With IT, have shared-nothing boundary, can enforce b/c IT takes the role of host
* So we specify this for components.


## Use Cases Revisited

TODO

### Optimizing calls to Web APIs (revisited)

TODO:
* Define mapping from Web IDL to interface types
* Valuable for incorporating Web IDL specs into WASI

The way this is to be achieved is by extending the Web IDL specification to
include a "WebAssembly binding" section which describes how WebAssembly types
(including the new interface types added by this proposal) are converted to and
from Web IDL types.

Since both Web IDL and WebAssembly are statically-typed, this specification
would start by defining when two Web IDL and WebAssembly types **match**. When
two types match, the specification would define how values of the two types are
converted back and forth.

In particular, going down the list of [Web IDL types]:
* [`any`]: the existing WebAssembly [`externref`] type is already effectively
  the same as `any` in Web embeddings.
* [Primitive types]: WebAssembly value types already can be efficiently
  converted back and forth.
* [`DOMString`]: since the WebAssembly `string` type is defined as a
  sequence of [Unicode code points] and `DOMString` is defined as a sequence of
  16-bit [code units], conversion would be UTF-16 encoding/decoding, where 
  lone surrogates in a `DOMString` decode to a surrogate code point.
* [`USVString`]: a WebAssembly `string` is a superset of `USVString`.
  Conversion to a `USVString` would follow the same strategy as
  [`DOMString`-to-`USVString` conversion] and map lone surrogates to the
  replacement character.
* [`ByteString`]: as a raw sequence of uninterpreted bytes, this type is probably
  best converted to and from a WebAssembly sequence interface type.
* [`object`], [`symbol`], [Frozen array] types: as JS-specific types, these
  could either be converted to and from `externref` or be statically typed via
  reference to a [type import].
* [Interface] types: while Web IDL defines interfaces as namespace structures
  containing methods, fields, etc., for the specific purpose of typing Web API
  functions, a Web IDL Interface type just defines an abstract reference type
  used in Web API function signatures. WebAssembly can represent this type with
  either an `externref` (implying dynamic type checks) or via reference to 
  [type import].
* [Callback], [Dictionary], [Sequence] types: these would be converted to and
  from WebAssembly closure, record, and sequence interface types, respectively.
* [Record] types: WebAssembly does not currently have plans for an "ordered map"
  interface type. This type appears to be infrequently used in APIs, and as long
  as that stays the case and uses remain cold, JS objects could be synthesized
  instead.
* [Enumeration], [Nullable], [Union] types: these would be converted to and
  from WebAssembly variant interface types, by imposing various matching
  requirements on the variant type.
* [Annotated] types: the annotations don't change the representation, but imply
  additional dynamic checks on argument values.
* [`BufferSource`] types: `ArrayBuffer`s could be converted to and from
  WebAssembly sequence types, while views would depend on first-class
  slice/view reference types being added to WebAssembly, which has been
  discussed but is not yet officially proposed.

An important question is: what happens, at instantiation-time, when the Web IDL
and WebAssembly signatures don't match. One option would be to throw an error,
however, this would lead to several practical compatibility hazards:
* Browsers sometimes have slightly incompatible Web IDL signatures (which can
  occur for historical compatibility reasons).
* Sometimes Web IDL specifications are refactored over time (e.g., changing a
  `long` to a `double`), assuming the coercive semantics of JavaScript.
* JavaScript Built-in functions that today have no Web IDL signature might be
  imbued with a Web IDL signature by a future iteration of the spec that is
  subtly incompatible with extant uses that depend on coercieve JS semantics.

To address all these concerns, on WebAssembly/Web IDL signature mismatch,
instantiation would fall back to first converting all WebAssembly values to JS
values and then passing those JS values to the existing, more-coercive Web IDL
ECMAScript binding. To help well-intentioned developers avoid unintended
performance degradation, WebAssembly engines could emit warning diagnostics on
mismatch.

TODO: describe the JS API


### Defining language-neutral interfaces like WASI (revisited)

TODO:
* talk about source-language generation from .wit files
* still want some mechanism to include common typedefs: hence .witx


### Enabling "shared-nothing linking" of WebAssembly modules (revisited)

TODO
* example: how to generate source-language client definitions from .wasm


### Scoping Shared-Everything Linking (revisited)

TODO
* reify diagram with code


## Additional Requirements Revisited

TODO


## FAQ

TODO:
* How does this relate to ESM-integration?
  * As with JS API: the outside world only sees the component
  * Component (instance) imports work symmetric to Module (instance) imports in Module Linking
  * With Interface Types, ESM-integration can yield glue-code-less wasm modules
  * The only thing left to achieve parity with JS is the ability for wasm modules to import Web APIs,
    which we could get "for free" in the future from the revised [get-originals] proposal


## TODO

* optional record fields or parameters
* lifting and lowering between `intertype`s and core wasm abstract reference types
* a mechanism for specifying the receiver of a method call ([#87](https://github.com/WebAssembly/interface-types/issues/87))
* types for describing resources and handles to resources
* slices / views of memory
* closures




[Core Spec]: https://webassembly.github.io/spec/core
[JS API]: https://webassembly.github.io/spec/js-api/index.html
[Web API]: https://webassembly.github.io/spec/web-api/index.html
[C API]: https://github.com/WebAssembly/wasm-c-api
[Abbreviations]: https://webassembly.github.io/reference-types/core/text/conventions.html#abbreviations
[`name`]: https://webassembly.github.io/spec/core/text/values.html#names
[`valtype`]: https://webassembly.github.io/spec/core/syntax/types.html#syntax-valtype
[`instr`]: https://webassembly.github.io/spec/core/syntax/instructions.html#syntax-instr
[Control Instructions]: https://webassembly.github.io/spec/core/syntax/instructions.html#control-instructions
[Stack Polymorphic]: https://webassembly.github.io/spec/core/valid/instructions.html#polymorphism

[Reference Types]: https://github.com/WebAssembly/reference-types/blob/master/proposals/reference-types/Overview.md
[`externref`]: https://webassembly.github.io/reference-types/core/syntax/types.html#syntax-reftype

[Function References]: https://github.com/WebAssembly/function-references/blob/master/proposals/function-references/Overview.md

[Exception Handling]: https://github.com/webassembly/exception-handling

[Type Import]: https://github.com/WebAssembly/proposal-type-imports/blob/master/proposals/type-imports/Overview.md#imports

[Module Linking]: https://github.com/WebAssembly/module-linking/blob/master/proposals/module-linking/Explainer.md
[shared-everything-use-case]: https://github.com/WebAssembly/module-linking/blob/master/proposals/module-linking/Explainer.md#shared-everything-dynamic-linking
[shared-everything-example]: https://github.com/WebAssembly/module-linking/blob/master/proposals/module-linking/Example-SharedEverythingDynamicLinking.md

[GC]: https://github.com/WebAssembly/gc/blob/master/proposals/gc/Overview.md

[WASI]: https://github.com/webassembly/wasi
[`path_open`]: https://github.com/WebAssembly/WASI/blob/master/design/WASI-core.md#path_open

[Native Dynamic Linking]: https://en.wikipedia.org/wiki/Dynamic_linker
[Product Type]: https://en.wikipedia.org/wiki/Product_type
[Sum Type]: https://en.wikipedia.org/wiki/Sum_type
[Eager Evaluation]: https://en.wikipedia.org/wiki/Eager_evaluation
[Lazy Evaluation]: https://en.wikipedia.org/wiki/Lazy_evaluation
[SSA Form]: https://en.wikipedia.org/wiki/Static_single_assignment_form

[ECMAScript Binding]: https://heycam.github.io/webidl/#ecmascript-binding
[Web IDL Types]: https://heycam.github.io/webidl/#idl-types
[Primitive Types]: https://heycam.github.io/webidl/#dfn-primitive-type
[Dictionary]: https://heycam.github.io/webidl/#idl-dictionaries
[Callback]: https://heycam.github.io/webidl/#idl-callback-function
[Sequence]: https://heycam.github.io/webidl/#idl-sequence
[Record]: https://heycam.github.io/webidl/#idl-record
[Enumeration]: https://heycam.github.io/webidl/#idl-enumeration
[Interface]: https://heycam.github.io/webidl/#idl-interfaces
[Union]: https://heycam.github.io/webidl/#idl-union
[Nullable]: https://heycam.github.io/webidl/#idl-nullable-type
[Annotated]: https://heycam.github.io/webidl/#idl-annotated-types
[Typed Array View]: https://heycam.github.io/webidl/#dfn-typed-array-type
[Frozen array]: https://heycam.github.io/webidl/#idl-frozen-array
[`BufferSource`]: https://heycam.github.io/webidl/#BufferSource
[`any`]: https://heycam.github.io/webidl/#idl-any
[`object`]: https://heycam.github.io/webidl/#idl-object
[`symbol`]: https://heycam.github.io/webidl/#idl-symbol
[`DOMString`]: https://heycam.github.io/webidl/#idl-DOMString
[`ByteString`]: https://heycam.github.io/webidl/#idl-ByteString
[`USVString`]: https://heycam.github.io/webidl/#idl-USVString
[`DOMString`-to-`USVString` conversion]: https://heycam.github.io/webidl/#dfn-obtain-unicode

[Unicode Scalar Value]: https://unicode.org/glossary/#unicode_scalar_value
[Surrogate Code Point]: https://unicode.org/glossary/#surrogate_code_point
[Encoding API]: https://encoding.spec.whatwg.org
[Error Mode]: https://encoding.spec.whatwg.org/#error-mode
[UTF-8]: https://unicode.org/glossary/#UTF_8
[UTF-16LE]: https://unicode.org/glossary/#UTF_16LE
[UCS-2]: https://unicode.org/glossary/#UCS_2
[Latin1]: https://en.wikipedia.org/wiki/ISO/IEC_8859-1
