-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.RealizedProgram

@[expose] public section

/-!
# Compact encodings of program data

Two compact forms for the data of a realized program: run-length constants (`ConstRuns.expand`), and
index maps given by segments, a segment being one run or a pattern of runs repeated with
per-repetition deltas (`IndexMap.ofSegs`). Each form is a definition that expands to the realized program's own
data (`List Nat`, `IndexMap`), so the checkers and their proofs are unchanged; the kernel evaluates
the expansion during `decide +kernel`.
-/

namespace GordieHowe.RealizedProgram

/-! ## Run-length constants -/

/-- **Runs of equal values**: the list `[(v₀, c₀), (v₁, c₁), …]` expands to `c₀` copies of `v₀`,
then `c₁` copies of `v₁`, and so on, in order. A run with count `0` contributes nothing. -/
def ConstRuns.expand : List (Nat × Nat) → List Nat
  | [] => []
  | (v, c) :: rs => List.replicate c v ++ expand rs

/-! ## Index maps by segments -/

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

/-- **An index map given by segments**: the concatenation, in order, of the segments' runs
(`IdxSeg.expand`). -/
def IndexMap.ofSegs (segs : List IdxSeg) : IndexMap := segs.flatMap IdxSeg.expand

/-- **An index map from segments is the concatenation of their runs.** -/
@[simp] theorem IndexMap.ofSegs_nil : IndexMap.ofSegs [] = [] := rfl

/-- **An index map from segments is the concatenation of their runs.** -/
@[simp] theorem IndexMap.ofSegs_cons (s : IdxSeg) (segs : List IdxSeg) :
    IndexMap.ofSegs (s :: segs) = s.expand ++ IndexMap.ofSegs segs := rfl

/-! ## The index maps of a convolution and its spectral realization

The views `compiler/conv.h` and the plan's exporter (`plan_program.h`, `conv`) read a batched
acyclic convolution and its realization through, by name, each a run per contiguous stretch of a
block; the entries are stated once (`IndexMap.entry_convLeft`, `IndexMap.entry_convRight`,
`IndexMap.entry_zeroExtend`, `IndexMap.entry_blockPrefix`,
`GordieHowe/Language/RealizedProgram/SpectralSound.lean`). -/

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
