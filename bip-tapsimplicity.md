```
  BIP: ?
  Layer: Consensus (soft fork)
  Title: TapSimplicity: Simplicity in Taproot
  Authors: Byron Hambly <bhambly@blockstream.com>
  Status: Draft
  Type: Specification
  Assigned: ?
  License: BSD-3-Clause
  Version: 0.1.0
  Requires: 340, 341, 342
```

## Abstract

This document proposes _TapSimplicity_, a new Taproot leaf version (`0xbe`). Under this leaf
version the leaf script is a 32-byte commitment to a [Simplicity][simplicity-paper] program
instead of a Tapscript.

Simplicity is a typed, combinator-based functional language without
loops or recursion. Its denotational semantics are defined in Coq, and its operational
semantics are given by an abstract machine called the Bit Machine. Because Simplicity is Turing
incomplete, static analysis derives an upper bound on the computational resources that a program
requires before the program runs. The language is still expressive enough to denote any function
between its finite types.

A TapSimplicity spend supplies the program and its witness values in the input witness stack. The
spend is valid when the program's commitment matches the leaf, the program decodes and
type-checks, the statically analysed cost of the program is within a budget derived from the size
of the witness, and evaluation completes without an assertion failure.

## Motivation

Simplicity is specifically designed as an alternate scripting system for Bitcoin. Instead of
adding operations to script one at a time, it defines a small set of combinators with formal
semantics. Any finitary function can be built from these combinators. Once this general-purpose
foundation is in consensus, functionality that would otherwise require a new opcode, and a new
soft fork, can be written directly as a Simplicity program by the parties who need it, without
further changes to the consensus rules. Consensus then concerns the quality and versions of the
interpreter, not the merits of each individual feature.

These properties make this practical:

- **Static resource bounds.** Simplicity has no loops or unbounded recursion, so an upper bound
  on the time and memory that an evaluation can consume is computed from the structure of the
  program before it runs. This removes the need for the per-operation accounting and sigop-style
  budgets that Script uses. It also lets the party that commits to a program verify in advance
  that any spend of the program is within the consensus limits.
- **Formal semantics.** The meaning of a Simplicity expression is defined denotationally in Coq.
  Programs, and the analyses applied to them, can be reasoned about with proof assistants instead
  of by reading the interpreter source.
- **Pruning and sharing.** Programs are committed by a Merkle root over their syntax tree.
  Unused branches are replaced by their hashes at spending time, and repeated subexpressions are
  transmitted once. This limits the on-chain size of large programs and reveals only the branch
  that is taken.
- **Jets.** Common subexpressions are recognised by their Merkle root and evaluated by verified
  native code instead of by traversal of the combinators. A jet is by definition equal to the
  expression it replaces, so it changes only the cost of evaluation, not the meaning of a program.
  This keeps a general-purpose language practical to validate at scale, because expensive
  primitives such as hashing and signature verification run at native speed.

## Specification

### Simplicity

This section introduces the language only as much as is necessary to state the consensus rules.
The normative definition of Simplicity, which includes its semantics, its Merkle roots, its
serialisation, and its jets, is the [Simplicity technical report][simplicity-tr] together with the
Coq, Haskell, and C sources of the [reference implementation](#reference-implementation).

#### Types

A Simplicity type is built from three formers:

- the unit type `1`, which has exactly one value, written `⟨⟩`;
- the sum type `A + B`, whose values are `σᴸ(a)` for `a : A` and `σᴿ(b)` for `b : B`;
- the product type `A × B`, whose values are the pairs `⟨a, b⟩`.

There are no recursive types, so every Simplicity type has finitely many values. The bit type is
`2 := 1 + 1`, and multi-bit words are defined by `2¹ := 2` and `2²ⁿ := 2ⁿ × 2ⁿ`, so `2²⁵⁶` is
the type of 256-bit words.

#### Core combinators

Expressions are written `t : A ⊢ B`, where `A` is the input type and `B` the output type. Every
well-typed expression denotes a function `⟦t⟧ : A → B`. Core Simplicity has nine combinators:

```
                          s : A ⊢ B    t : B ⊢ C
    iden : A ⊢ A          ─────────────────────────
                               comp s t : A ⊢ C

    unit : A ⊢ 1

        t : A ⊢ B                    t : A ⊢ C
    ─────────────────────      ─────────────────────
    injl t : A ⊢ B + C         injr t : A ⊢ B + C

    s : A × C ⊢ D    t : B × C ⊢ D        s : A ⊢ B    t : A ⊢ C
    ──────────────────────────────        ────────────────────────
      case s t : (A + B) × C ⊢ D            pair s t : A ⊢ B × C

        t : A ⊢ C                    t : B ⊢ C
    ─────────────────────      ─────────────────────
    take t : A × B ⊢ C         drop t : A × B ⊢ C
```

with semantics:

```
    ⟦iden⟧(a)            := a
    ⟦comp s t⟧(a)        := ⟦t⟧(⟦s⟧(a))
    ⟦unit⟧(a)            := ⟨⟩
    ⟦injl t⟧(a)          := σᴸ(⟦t⟧(a))
    ⟦injr t⟧(a)          := σᴿ(⟦t⟧(a))
    ⟦case s t⟧⟨σᴸ(a), c⟩ := ⟦s⟧⟨a, c⟩
    ⟦case s t⟧⟨σᴿ(b), c⟩ := ⟦t⟧⟨b, c⟩
    ⟦pair s t⟧(a)        := ⟨⟦s⟧(a), ⟦t⟧(a)⟩
    ⟦take t⟧⟨a, b⟩       := ⟦t⟧(a)
    ⟦drop t⟧⟨a, b⟩       := ⟦t⟧(b)
```

`case` is the only branching construct. These nine combinators are complete for finitary
functions: for any Simplicity types `A` and `B` and any function `f : A → B`, some core
Simplicity expression `t : A ⊢ B` satisfies `⟦t⟧ = f`.

#### Sharing and the program DAG

Expressions form an abstract syntax tree, but identical subexpressions are shared, so an
expression is transmitted and stored as a directed acyclic graph (DAG). Sharing is not observable
in the semantics. It is a property of the representation, and it makes realistic programs compact.
For example, the Simplicity SHA-256 block compression function has 3,274,442 nodes as a tree but
only 1130 distinct nodes as a DAG.

#### Commitment Merkle Root

A Simplicity expression is not committed by a hash of a linear encoding. Instead, it is committed
by a recursive hash of its syntax tree with the SHA-256 block compression function. This gives a
256-bit _Commitment Merkle Root_ (CMR), written `#(t)`. Each kind of node has a tag that supplies
the initial value of its hash. The CMR of a node is computed from its tag and the CMRs of its
children. Because the CMR is defined structurally, intermediate results are shared as the DAG is.
The CMR does not commit to the types of the expression.

#### Assertions, hidden nodes, and pruning

Two combinators replace `case` when a branch is not taken:

```
    s : A × C ⊢ D    h : 2²⁵⁶        h : 2²⁵⁶    t : B × C ⊢ D
    ─────────────────────────        ─────────────────────────
    assertl s h : (A+B) × C ⊢ D      assertr h t : (A+B) × C ⊢ D
```

An assertion evaluates its available branch. It fails if the tag of the input selects the branch
that was replaced by the hash `h`. Assertions use the same tag as `case` in the CMR computation,
so that

```
    #(case s t) = #(assertl s #(t)) = #(assertr #(s) t)
```

A spender therefore _prunes_ the committed program. Every `case` whose other branch is not taken
is replaced by the corresponding assertion, and the replaced branch is transmitted only as its
CMR, which is a _hidden_ node. Pruning reduces the witness size and reveals only the branch that
was used.

The language includes a `fail : A ⊢ B` combinator to construct programs that use assertions. A
program that reaches consensus **MUST** have every `fail` subexpression pruned away.

#### Witness values

Signatures and other spend-time inputs are supplied by the `witness` combinator:

```
       b : B
    ─────────────────
    witness b : A ⊢ B
```

Semantically, `witness b` is the constant function that returns `b`. Its CMR does not commit to
`b`, so a spender chooses witness values at redemption time without a change to the commitment of
the program. Every Simplicity type is finite, and the number of `witness` nodes is fixed at
commitment time, so the amount of witness data that a program can consume is bounded when the
program is committed. Type inference assigns each `witness` node the smallest type consistent with
its use, so a witness value cannot be padded with unused data.

#### Words and jets

Two further node kinds appear only in the DAG representation:

- A **word** node is a constant `2ⁿ` value of the form `scribe(v) : 1 ⊢ 2ⁿ`, where `n` is a
  power of two up to `2³¹`. It is encoded compactly instead of as a tree of `injl`, `injr`, and
  `pair`.
- A **jet** is a distinguished expression that an implementation recognises by its CMR and
  evaluates with native code instead of by traversal of the expression. A jet is by definition
  equal to the Simplicity expression that it replaces. It cannot introduce new behaviour, it is
  transparent to reasoning about programs, and it changes only the cost of evaluation, not the
  semantics of the language.

#### Delegation

The `disconnect` combinator allows part of a program to be chosen after commitment:

```
    s : 2²⁵⁶ × A ⊢ B × C    t : C ⊢ D
    ─────────────────────────────────
        disconnect s t : A ⊢ B × D
```

Given `a : A`, `s` is applied to `⟨#(t), a⟩` to produce `⟨b, c⟩`, and the result is
`⟨b, ⟦t⟧(c)⟩`. The CMR of `disconnect s t` commits only to `s`, so `t` can be supplied at
redemption time while `s` observes the CMR of `t`.

#### The Bit Machine, static analysis, and cost

Operational semantics are given by a translation of an expression into instructions for the _Bit
Machine_. The Bit Machine is an abstract machine whose state is two stacks of data frames of bit
cells. The translation gives a measure of the work that an evaluation performs. The same recursion
that computes this measure over the DAG also gives, before execution, an upper bound on:

- the number of cells required across both frame stacks (memory), and
- an abstract _cost_ (time).

Cost is measured in milli weight units (mWU). Every node contributes a fixed overhead of
100 mWU. The `iden`, `word`, and `witness` nodes additionally contribute their bit size. The
`comp` and `disconnect` nodes contribute the bit sizes of the intermediate types that they
materialise. A jet contributes its tabulated cost in place of the cost of the expression that it
replaces. The scale is normalised so that the `check_sig_verify` jet costs 50000 mWU. A `case`
node takes the maximum of its two branches. The other combinators take the sum of their children.

These analyses are recursive functions over the DAG, so their intermediate results are shared as
the DAG is, and their running time is proportional to the size of the DAG, not to the size of the
evaluation.

### Programs

A **Simplicity program** is an expression of type `1 ⊢ 1`. It is evaluated at `⟨⟩` and produces
no output. Its effect is to succeed or to fail. All spend-time inputs enter through `witness`
nodes, and all conditions are enforced by assertions.

### TapSimplicity leaf version

Taproot leaf versions are the first byte of the control block with the mask `0xfe` applied
(BIP-341). TapSimplicity uses leaf version `0xbe`:

```
    TAPROOT_LEAF_MASK          = 0xfe
    TAPROOT_LEAF_TAPSCRIPT     = 0xc0   (BIP-342)
    TAPROOT_LEAF_TAPSIMPLICITY = 0xbe   (this document)
```

All of the BIP-341 script path rules apply unchanged and are evaluated first: the control block
**MUST** have length `33 + 32m` for `0 ≤ m ≤ 128`; the taproot output key **MUST** be reproduced
by a tweak of the internal key with the Merkle root computed from the leaf hash and the path; and
the leaf hash is `hash_TapLeaf(leaf_version || compact_size(len(script)) || script)`.

### Leaf script

For a TapSimplicity leaf the script **MUST** be exactly 32 bytes, and is interpreted as the CMR
of the program that authorises the spend. If the script is not exactly 32 bytes, the leaf is not
a TapSimplicity leaf and is subject to the rules for unknown leaf versions in BIP-341.

### Witness stack

After the BIP-341 witness processing (removal of the annex if present, then the control block,
then the script), the remaining stack **MUST** contain exactly 2 or 3 items. Any other count
makes the spend invalid. The items are named from the top of the stack downwards:

| position          | name      | contents                                    |
| :---------------- | :-------- | :------------------------------------------ |
| top               | `program` | the serialised Simplicity DAG               |
| next              | `witness` | the serialised witness values, in DAG order |
| bottom (optional) | `padding` | zero or more `0x00` bytes                   |

For a spend without padding the full input witness stack is therefore:

```
    index  item
    ─────  ───────────────────────────────────────────
      0    witness
      1    program
      2    script (32-byte CMR)     ← popped as the taproot leaf script
      3    control block            ← popped as the taproot control block
     [4]   annex                    ← popped first, if present
```

and with padding:

```
    index  item
    ─────  ───────────────────────────────────────────
      0    padding (n bytes, all 0x00)
      1    witness
      2    program
      3    script (32-byte CMR)
      4    control block
     [5]   annex                    ← popped first, if present
```

If a `padding` item is present, all of its bytes **MUST** be `0x00`.

### Validation budget

Let `GetSerializeSize(stack)` be the length in bytes of the input's witness stack as it appears
on the wire: the compact-size count of items, plus, for each item, its compact-size length prefix
and its bytes. The budget is computed from the **full, unmodified** stack — including the annex,
control block, script, program, witness, and padding — before any item is removed:

```
    VALIDATION_WEIGHT_OFFSET = 50

    budget = GetSerializeSize(witness_stack) + VALIDATION_WEIGHT_OFFSET
```

`budget` is measured in weight units (WU) and bounds the statically analysed cost of the program.
A spender can need more budget than the natural size of the witness provides. The optional
`padding` item provides more budget at the standard rate of one weight unit per witness byte.

Padding must be minimal. Let `n` be the length of the `padding` item in bytes:

```
    minCost = 0                                                                if no padding item
    minCost = budget − GetSerializeSize_item(0)                                if n = 0
    minCost = budget − GetSerializeSize_item(n) + GetSerializeSize_item(n−1)   if n ≥ 1
```

where `GetSerializeSize_item(k)` is the serialised size of a `k`-byte stack item, that is, `k`
plus the size of its compact-size length prefix. Because `GetSerializeSize_item(0) = 1`, an empty
padding item gives `minCost = budget − 1`. For `n ≥ 1` the difference is `1`, except where the
removal of a byte crosses a compact-size boundary.

The program's analysed cost `cost` (in mWU) is accepted if and only if

```
    minCost × 1000 < cost ≤ budget × 1000
```

Every program has strictly positive cost, so `minCost = 0` imposes no constraint. Otherwise the
lower bound rejects a spend whose padding is larger than the budget it needs, so the cost of the
program determines the padding length.

### Resource limits

Independently of `budget`, an implementation enforces:

| constant      | value       | meaning                                                      |
| :------------ | :---------- | :----------------------------------------------------------- |
| `DAG_LEN_MAX` | `8 000 000` | maximum number of nodes in the decoded DAG                   |
| `CELLS_MAX`   | `5 242 880` | maximum number of Bit Machine cells the analysis may require |
| `BUDGET_MAX`  | `4 000 050` | maximum effective budget, in WU                              |

A `budget` computed above `BUDGET_MAX` is clamped to `BUDGET_MAX`. This is not an error. A witness
large enough to reach that clamp already exceeds the standard transaction weight limit.

### Validation algorithm

Given a Taproot script path spend whose leaf version is `0xbe` and whose script is 32 bytes, the
spend is valid if and only if every step below succeeds.

1. **Stack shape.** Exactly 2 or 3 items remain after BIP-341 witness processing. Pop `program`
   and then `witness` from the top.

2. **Budget.** Compute `budget` from the full witness stack as specified above.

3. **Padding.** If a third item remains, pop it as `padding`, require every byte to be `0x00`,
   and compute `minCost`. Otherwise `minCost = 0`.

4. **Taproot environment.** From the control block take the internal key (bytes 1–32) and the
   Merkle path (the remaining 32-byte chunks), and record the path length. Together with the
   32-byte CMR from the leaf script and the leaf version, these determine the `tapleaf_hash`,
   `tappath_hash`, and `tap_env_hash` values that the corresponding jets expose, as defined by
   the Simplicity specification.

5. **Decoding.** Decode `program` as a length-prefixed Simplicity DAG (see
   [Encoding](#encoding)). The spend is invalid if:
   - the bit stream ends prematurely, has trailing bytes beyond the final partial byte, or its
     final partial byte is padded with any bit other than zero;
   - a `fail` codeword or a reserved codeword is encountered;
   - a node refers to a child that is not a strictly earlier node in the DAG;
   - a hidden node appears anywhere other than as the pruned branch of an `assertl` or `assertr`;
   - the root of the DAG is a hidden node;
   - the nodes are not in the canonical order defined by the Simplicity specification;
   - a word encoding is larger than `2³¹` bits, or a jet code does not name a defined jet;
   - the DAG exceeds `DAG_LEN_MAX` nodes.

6. **CMR check.** The CMR of the root node **MUST** equal the 32-byte leaf script.

7. **Type inference.** Run first-order unification over the DAG, replacing any remaining type
   variables with `1`. The spend is invalid if unification fails, if the occurs check fails, or
   if the inferred type of the root is not `1 ⊢ 1`.

8. **Witness data.** Read `witness` as a bit stream and fill each `witness` node in DAG order
   with a value of its inferred type. The spend is invalid if the stream is exhausted early, if
   any whole byte remains unconsumed, or if the final partial byte is padded with any bit other
   than zero.

9. **Sharing.** Compute the identity hash of every node, including hidden nodes. The identity
   hash is a Merkle root that, unlike the CMR, also commits to inferred types and to witness
   values, so two nodes share one exactly when they denote the same subexpression at the same
   type with the same witness data. No two nodes may share an identity hash: a program whose
   subexpressions are not maximally shared is invalid.

10. **Static analysis.** Compute the memory and cost bounds. The spend is invalid if the cell
    bound exceeds `CELLS_MAX`, if `cost > budget × 1000`, or if `cost ≤ minCost × 1000`.

11. **Evaluation.** Run the program on the Bit Machine in the transaction environment. The spend
    is invalid if an `assertl` or `assertr` fails, or if a jet's own assertion fails.

12. **Anti-DoS checks.** After evaluation, the spend is invalid if any non-hidden node was never
    executed, or if any `case` node — as opposed to an assertion — did not execute both of its
    branches. Together these require that the transmitted program is exactly the pruned program
    that the spend actually uses.

A spend that passes every step is valid. Steps 5 through 12 are the operation of the Simplicity
evaluator. The reference implementation reports a distinct error code for each failure.
Implementations can surface this code, but it has no consensus significance.

### Transaction environment

Core Simplicity is pure. Access to the spending transaction is provided by jets, which replace the
`sighash` primitive of the original paper. The environment consists of the transaction that is
validated, the index of the input that is spent, and the taproot spending data from step 4. The
jets fall into these groups:

- **Transaction fields:** version, lock time, number of inputs and outputs, transaction id.
- **Per-input fields:** previous outpoint, sequence, value and script hash of the output being
  spent, annex hash, scriptSig hash; and the same fields for the current input.
- **Per-output fields:** value, script hash.
- **Aggregate values:** total input value, total output value, fee.
- **Aggregate hashes:** hashes over outputs, inputs, spent outputs, sequences, annexes, and
  scriptSigs, plus `sig_all_hash`, which is
  `SHA256(tx_hash || tap_env_hash || current_index)` and so commits to the whole transaction, the
  current input's taproot environment, and which input is being spent.
- **Taproot data:** leaf version, script CMR, internal key, path, `tapleaf_hash`,
  `tappath_hash`, `tap_env_hash`, and the `build_tapleaf_simplicity`, `build_tapbranch`, and
  `build_taptweak` constructors.
- **Time locks:** `tx_is_final`, `tx_lock_height`, `tx_lock_time`, `tx_lock_distance`,
  `tx_lock_duration`, and the corresponding `check_lock_*` assertions implementing BIP-65 and
  BIP-112 semantics.

These are in addition to the application-independent core jets, which cover word arithmetic,
comparison and bitwise operations from 1 to 64 bits and 256-bit arithmetic, SHA-256, secp256k1
field and group operations, and BIP-340 Schnorr signature verification.

Signature-checking programs are built from these parts. A program computes a digest with, for
example, `sig_all_hash`, and asserts that a `witness`-supplied signature verifies against a
committed public key for that digest. This reproduces the effect of `OP_CHECKSIGVERIFY`.

### Encoding

`program` is a bit stream, most significant bit first, padded to a byte boundary with zero bits.
It begins with a positive integer giving the number of nodes, followed by that many node
encodings. Positive integers are encoded self-delimitingly: `decodeUptoMaxInt` reads one bit; if
it is `0` the value is `1`; otherwise it reads a length `n` in the range 1–30 using the same
scheme applied to values up to 65535, then reads `n` bits `r` and yields `2ⁿ + r`.

Each node begins with one bit. If it is `0`, a two-bit `code` follows, then a `subcode` of two
bits when `code < 3` and one bit otherwise, then `2 − code` child references. Each child
reference is a positive integer `k`, and denotes node `i − k`, where `i` is the index of the node
being decoded.

| `code` | `subcode` | children | node                                                                       |
| :----- | :-------- | :------- | :------------------------------------------------------------------------- |
| 0      | 0         | 2        | `comp`                                                                     |
| 0      | 1         | 2        | `case`; `assertr` if the first child is hidden, `assertl` if the second is |
| 0      | 2         | 2        | `pair`                                                                     |
| 0      | 3         | 2        | `disconnect`                                                               |
| 1      | 0         | 1        | `injl`                                                                     |
| 1      | 1         | 1        | `injr`                                                                     |
| 1      | 2         | 1        | `take`                                                                     |
| 1      | 3         | 1        | `drop`                                                                     |
| 2      | 0         | 0        | `iden`                                                                     |
| 2      | 1         | 0        | `unit`                                                                     |
| 2      | 2         | 0        | `fail` — invalid at consensus                                              |
| 2      | 3         | 0        | reserved — invalid                                                         |
| 3      | 0         | 0        | `hidden`, followed by a 256-bit CMR                                        |
| 3      | 1         | 0        | `witness`                                                                  |

If the first bit is `1`, a second bit distinguishes a word (`0`) from a jet (`1`). A word encodes
a depth `d` in the range 1–32 as a positive integer, followed by `2^(d−1)` bits of value, and
denotes `scribe(v) : 1 ⊢ 2^(2^(d−1))`. A jet encodes its identifier as a sequence of positive
integers indexing the jet tables; the tables of core jets and Bitcoin jets are given by the
reference implementation.

`witness` is a separate bit stream that contains the witness values in DAG order. Each value is
encoded according to its inferred type: a value of `A + B` is a tag bit followed by the encoding
of the selected side, a value of `A × B` is the encoding of its components in order, and a value
of `1` is empty. Both streams are padded to a byte boundary with zero bits, and both **MUST** be
consumed exactly.

## Rationale

**Why a leaf version instead of opcodes.** Simplicity is not an extension of Script. It has its
own types, encoding, and cost model, and its programs are committed by a Merkle root instead of by
a hash of a linear encoding. BIP-341 reserved leaf versions so that an alternative script system
could be introduced without a change to Tapscript. The use of a leaf version keeps the two
interpreters separate. A Taproot output can offer both a Tapscript leaf and a TapSimplicity leaf,
so adoption does not require a choice between them.

**Why `0xbe`.** Leaf versions must be even, because the low bit is the parity bit of the output
key. They must not be `0x50`, which is reserved as the annex tag. `0xbe` satisfies both
constraints, and also matches the value used in [Elements](https://github.com/ElementsProject/elements/blob/b7fc5d080a7e9ccc0ef48c3ba11db243e794bdb0/src/script/interpreter.h#L282).

**Why the CMR goes in the script field.** The 32-byte CMR is placed where Tapscript places its
script. Therefore the leaf hash, the Merkle path, and the taproot commitment are computed by the
existing BIP-341 code with no changes, and the leaf has the same size as an ordinary
hash-committed leaf. The alternative, a direct commitment to the serialised program, would prevent
pruning, because the whole program would have to be revealed to check the commitment.

**Why the budget is derived from witness size.** The Tapscript validation weight budget is
`50 + witness size`. The reason is that a spender who wants the network to do more work should pay
for it in the same units that the network charges for everything else. TapSimplicity reuses this
rule unchanged. This keeps the cost of a Simplicity spend to validators proportional to its cost
to the spender, and it avoids a second, independent notion of computational cost in the fee
market.

**Why padding is used, and why it must be minimal.** The cost of a program is not always
proportional to the size of its witness. A compact program can be expensive, and a large program
can be cheap. Padding lets a spender add budget explicitly. The `minCost` lower bound requires the
padding to be minimal, so a spender cannot pad arbitrarily. For a given program cost, exactly one
padding length is accepted. Therefore the fee paid is proportional to the work requested, and a
maximum-budget spend cannot be constructed more cheaply than by payment for it.

**Why pruning is mandatory.** The rule that every non-hidden node must execute, and that both
branches of every genuine `case` must be taken, forces the transmitted program to be exactly the
pruned program that the spend uses. Without this rule, a spender could pay for a small witness
while it commits to a program whose analysis is dominated by branches that never run. The spender
could also pad transactions with dead code that validators must still decode, type-check, and
analyse.

**Why maximal sharing is required.** Two nodes with the same identity hash denote the same
subexpression at the same type. If duplicates were permitted, a witness could be inflated with
redundant nodes, and the same program could have many valid encodings. The rejection of
duplicates gives each program a single canonical serialisation and keeps the DAG size an accurate
measure of the work required.

**Why the annotated Merkle root is not checked.** The evaluator can optionally verify a supplied
annotated Merkle root, which is a Merkle root that also commits to inferred types. It is useful to
tooling, but it adds no security to consensus validation, because the CMR check and type inference
already determine the program. It is therefore not part of these rules.

**Jets and future changes.** New _functionality_ does not require a consensus change. It is
written as a Simplicity program by whoever needs it. A new _jet_, by contrast, does change
consensus, because it introduces a new codeword and a new cost. Such a change is narrower than a
new opcode. The behaviour of a jet is fully determined by the Simplicity expression that it
replaces, which is already valid and already has semantics. Review therefore concerns the
correctness of the native implementation and the fairness of its cost, not the merits of a new
capability. This proposal fixes the jet set to the one defined by the reference implementation.
Any extension is a separate proposal.

**Why the original `sighash` primitive is not used.** The 2017 paper introduced a single
`sighash` combinator that returns a digest selected by a SigHash type. The deployed language
instead exposes transaction data through a family of jets. This lets a program commit to exactly
the fields it needs, as covenants and signature-from-stack constructions require, instead of to
one of a fixed set of digests.

## Backward Compatibility

TapSimplicity is a soft fork. Under BIP-341, a Taproot script path spend with an unrecognised leaf
version succeeds unconditionally. Nodes that do not implement these rules therefore accept
TapSimplicity spends without evaluation of them, and stay in consensus with nodes that do. No
existing script, address, or transaction changes meaning.

Wallets that do not implement Simplicity are unaffected. They cannot construct or recognise a
TapSimplicity leaf, but the Taproot outputs that contain one are ordinary P2TR outputs, and any
key path or Tapscript leaf in the same output continues to work.

Before activation, relay policy discourages spends that rely on leaf version `0xbe`. A transaction
that would be invalid under these rules is therefore not propagated, so that no one relies on
unupgraded nodes to accept it.

## Reference Implementation

The Simplicity language, its Coq and Haskell specifications, and the consensus C implementation:

- <https://github.com/BlockstreamResearch/simplicity>
- Bitcoin jets and transaction environment: <https://github.com/BlockstreamResearch/simplicity/tree/bitcoin>

The Bitcoin integration:

- Russell O'Connor's original branch:
  <https://github.com/roconnor-blockstream/bitcoin/tree/simplicity>
- Bitcoin Inquisition implementation:
  <https://github.com/bitcoin-inquisition/bitcoin/pull/115>

## Test Vectors

Test vectors are not yet prepared for this document. They are required before it can be advanced
to Complete. They are expected to cover, at a minimum: the witness stack shape rules; the budget
and padding minimality boundary cases, which include the compact-size boundaries at 253 and 65536
bytes of padding; decoding failures for each rejected codeword and each malformed bit stream; the
CMR mismatch case; type inference failures and non-`1 ⊢ 1` roots; unpruned programs and unshared
subexpressions; and a set of complete spends that exercise the Bitcoin jets.

## Changelog

- **0.1.0** (2026-08-07):
  - Initial draft.

## Acknowledgements

Simplicity was designed by Dr. Russell O'Connor at Blockstream Research and presented at
[PLAS '17](https://dl.acm.org/doi/10.1145/3139337.3139340). The Bitcoin jets, the Bitcoin
transaction environment, and the original Bitcoin integration are his work.

## Copyright

This document is licensed under the [3-Clause BSD License](https://opensource.org/license/BSD-3-Clause).

[simplicity-paper]: https://blockstream.com/simplicity.pdf
[simplicity-tr]: https://github.com/BlockstreamResearch/simplicity/blob/pdf/Simplicity-TR.pdf
[liquid]: https://liquid.net
[inquisition]: https://github.com/bitcoin-inquisition/bitcoin
[binana]: https://github.com/bitcoin-inquisition/binana/pull/22
