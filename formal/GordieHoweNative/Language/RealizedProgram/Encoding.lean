-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweNative.Language.RealizedProgram

/-!
# GordieHowe: the compiled definitions of `GordieHowe.Language.RealizedProgram.Encoding`

The definitions of `GordieHowe.Language.RealizedProgram.Encoding` that the certificate checkers run, and the
facts their bodies use, in the Mathlib-free library `GordieHoweNative`, which Lake compiles to
a shared library (`precompileModules`): native mode runs the checkers as compiled code. The
declarations keep their names. Their lemmas are in
`GordieHowe/Language/RealizedProgram/Encoding.lean`, which imports this module.
-/

@[expose] public section

namespace GordieHowe.RealizedProgram

/-- **A run of a repeated pattern**: the index-map run `base = (start, step, count)` of the first
repetition, and the amounts `delta = (Δstart, Δstep, Δcount)` its start, step and count each
advance by from one repetition to the next. -/
structure RepRun where
  /-- The run `(start, step, count)` in repetition `0`. -/
  base : Nat × Int × Nat
  /-- The per-repetition advance `(Δstart, Δstep, Δcount)`. -/
  delta : Int × Int × Int

/-- **A segment of an index map**: one run, or a pattern of runs repeated `k` times. -/
inductive IdxSeg where
  /-- One index-map run `(start, step, count)`. -/
  | run (r : Nat × Int × Nat)
  /-- The runs of `pat` repeated `k` times (see `IdxSeg.expand`). -/
  | rep (pat : List RepRun) (k : Nat)

/-- **Run `b` advanced `j` times by `d`**: with `b = (s, t, c)` and `d = (ds, dt, dc)`, the run
`(toNat (s + j·ds), t + j·dt, toNat (c + j·dc))`, computed in `Int`; `Int.toNat` sends a negative
start or count to `0`. -/
def IdxSeg.shift (j : Nat) (b : Nat × Int × Nat) (d : Int × Int × Int) : Nat × Int × Nat :=
  (((b.1 : Int) + j * d.1).toNat, b.2.1 + j * d.2.1, ((b.2.2 : Int) + j * d.2.2).toNat)

/-- **The runs of a segment**: `.run r` is `[r]`; `.rep pat k` is, for `j = 0, …, k − 1` in order,
the runs `IdxSeg.shift j p.base p.delta` for `p` in `pat` in order (repetition-major, so
`k · pat.length` runs, run `t` of repetition `j` at position `j · pat.length + t`). `.rep pat 0` and
`.rep [] k` are empty. -/
def IdxSeg.expand : IdxSeg → IndexMap
  | .run r => [r]
  | .rep pat k => (List.range k).flatMap fun j => pat.map fun p => IdxSeg.shift j p.base p.delta

/-- **The left operand's view of `B` acyclic convolutions** of operands of lengths `la` and `lb`:
entry `(blk, k, t)` (position `(blk (la + lb − 1) + k) la + t`) is `blk la + t` when
`k + 1 − lb ≤ t ≤ k` and `t < la`, else `B la` (the zero coordinate after the `B la` operand
coordinates). -/
def IndexMap.convLeft (B la lb : Nat) : IndexMap :=
  (List.range B).flatMap fun blk => (List.range (la + lb - 1)).flatMap fun k =>
    [(B * la, 0, k + 1 - lb), (blk * la + (k + 1 - lb), 1, min k (la - 1) + 1 - (k + 1 - lb)),
      (B * la, 0, la - 1 - min k (la - 1))]

/-- **The right operand's view of `B` acyclic convolutions**: entry `(blk, k, t)` is
`blk lb + (k − t)` when `k + 1 − lb ≤ t ≤ k` and `t < la`, else `B lb`. -/
def IndexMap.convRight (B la lb : Nat) : IndexMap :=
  (List.range B).flatMap fun blk => (List.range (la + lb - 1)).flatMap fun k =>
    [(B * lb, 0, k + 1 - lb), (blk * lb + (k - (k + 1 - lb)), -1, min k (la - 1) + 1 - (k + 1 - lb)),
      (B * lb, 0, la - 1 - min k (la - 1))]

/-- **`B` blocks of `l` coordinates zero-extended to `M`**: entry `(blk, t)` is `blk l + t` for
`t < l`, else `B l` (the zero coordinate after the `B l` coordinates). -/
def IndexMap.zeroExtend (B l M : Nat) : IndexMap :=
  (List.range B).flatMap fun blk => [(blk * l, 1, l), (B * l, 0, M - l)]

/-- **The first `n` coordinates of each of `B` blocks of `M`**: entry `(blk, k)` is `blk M + k`. -/
def IndexMap.blockPrefix (B M n : Nat) : IndexMap :=
  (List.range B).flatMap fun blk => [(blk * M, 1, n)]

end GordieHowe.RealizedProgram
