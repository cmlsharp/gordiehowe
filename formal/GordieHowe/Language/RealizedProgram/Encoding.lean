-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.RealizedProgram
public import GordieHoweNative.Language.RealizedProgram.Encoding

@[expose] public section

/-!
# Compact encodings of program data

Two compact forms for the data of a realized program: run-length constants (`ConstRuns.expand`), and
index maps given by segments, a segment being one run or a pattern of runs repeated with
per-repetition deltas (`IndexMap.ofSegs`). Each form is a definition that expands to the realized program's own
data (`List Nat`, `IndexMap`), so the checkers and their proofs are unchanged; the kernel evaluates
the expansion during `decide +kernel`.

The definitions are in `GordieHoweNative/Language/RealizedProgram/Encoding.lean`
(the compiled library `GordieHoweNative`); this module has their lemmas.
-/

namespace GordieHowe.RealizedProgram

/-! ## Run-length constants -/

/-- **Runs of equal values**: the list `[(v₀, c₀), (v₁, c₁), …]` expands to `c₀` copies of `v₀`,
then `c₁` copies of `v₁`, and so on, in order. A run with count `0` contributes nothing. -/
def ConstRuns.expand : List (Nat × Nat) → List Nat
  | [] => []
  | (v, c) :: rs => List.replicate c v ++ expand rs

/-! ### The expansion the kernel evaluates

`decide +kernel` evaluates every index map of a program from its segments. A structural `flatMap`
over `List.range k` costs the kernel a `brecOn` step and an `Int` multiplication and addition per
coordinate of each run; the expansion below is written with the recursors directly and computes a
run's start and count in natural arithmetic (`IdxSeg.addMulNat`), which the kernel does on literals
in one step. On the 32,832 runs of a SHA-256 byte-order map it takes a kernel probe of the runs'
bounds from 19.3 s to 9.1 s. Compiled code runs `IndexMap.ofSegsC`, the `flatMap`
(`IndexMap.ofSegs_csimp`). -/

/-- **`toNat (x + j·d)`, in natural arithmetic** (`IdxSeg.addMulNat_eq`). -/
def IdxSeg.addMulNat (x j : Nat) : Int → Nat
  | .ofNat d => x + j * d
  | .negSucc m => x - j * (m + 1)

theorem IdxSeg.addMulNat_eq (x j : Nat) (d : Int) :
    IdxSeg.addMulNat x j d = ((x : Int) + j * d).toNat := by
  cases d with
  | ofNat d =>
    simp only [addMulNat, Int.ofNat_eq_natCast]
    rw [show (j : Int) * d = ((j * d : Nat) : Int) by push_cast; rfl]
    generalize j * d = y
    omega
  | negSucc m =>
    simp only [addMulNat, Int.negSucc_eq, Int.mul_neg]
    rw [show (j : Int) * ((m : Int) + 1) = ((j * (m + 1) : Nat) : Int) by
      simp [Int.natCast_mul, Int.natCast_add]]
    generalize j * (m + 1) = y
    omega

/-- **`t + j·d`**, and `t` itself for `d = 0` (`IdxSeg.addMulInt_eq`): the kernel then reads a
step that does not change across repetitions without an `Int` multiplication and addition. -/
def IdxSeg.addMulInt (t : Int) (j : Nat) : Int → Int
  | .ofNat 0 => t
  | .ofNat (n + 1) => t + j * ((n + 1 : Nat) : Int)
  | .negSucc m => t + j * .negSucc m

theorem IdxSeg.addMulInt_eq (t : Int) (j : Nat) (d : Int) : IdxSeg.addMulInt t j d = t + j * d := by
  cases d with
  | ofNat n => cases n <;> simp [addMulInt]
  | negSucc m => rfl

/-- **`IdxSeg.shift` with its start and count in natural arithmetic** (`IdxSeg.shiftNat_eq`). -/
def IdxSeg.shiftNat (j : Nat) (b : Nat × Int × Nat) (d : Int × Int × Int) : Nat × Int × Nat :=
  (IdxSeg.addMulNat b.1 j d.1, IdxSeg.addMulInt b.2.1 j d.2.1, IdxSeg.addMulNat b.2.2 j d.2.2)

theorem IdxSeg.shiftNat_eq (j : Nat) (b : Nat × Int × Nat) (d : Int × Int × Int) :
    IdxSeg.shiftNat j b d = IdxSeg.shift j b d := by
  simp only [shiftNat, shift, addMulNat_eq, addMulInt_eq]

/-- **The runs of repetitions `j, j + 1, …, j + k − 1` of `pat`, then `tail`** (`IdxSeg.repRuns_eq`),
by the recursors. -/
noncomputable def IdxSeg.repRuns (pat : List RepRun) (tail : IndexMap) (k : Nat) : Nat → IndexMap :=
  @Nat.rec (fun _ => Nat → IndexMap) (fun _ => tail)
    (fun _ ih j => @List.rec RepRun (fun _ => IndexMap) (ih (j + 1))
      (fun p _ acc => IdxSeg.shiftNat j p.base p.delta :: acc) pat) k

theorem IdxSeg.repRuns_eq (pat : List RepRun) (tail : IndexMap) :
    ∀ k j, IdxSeg.repRuns pat tail k j =
      ((List.range' j k).flatMap fun j => pat.map fun p => IdxSeg.shift j p.base p.delta) ++ tail
  | 0, _ => rfl
  | k + 1, j => by
    have h : ∀ acc : IndexMap, @List.rec RepRun (fun _ => IndexMap) acc
        (fun p _ acc => IdxSeg.shiftNat j p.base p.delta :: acc) pat =
        (pat.map fun p => IdxSeg.shift j p.base p.delta) ++ acc := by
      intro acc
      induction pat with
      | nil => rfl
      | cons p ps ih => simp only [List.map_cons, List.cons_append, ← ih, shiftNat_eq]
    change @List.rec RepRun (fun _ => IndexMap) (IdxSeg.repRuns pat tail k (j + 1)) _ pat = _
    rw [h, IdxSeg.repRuns_eq pat tail k (j + 1), List.range'_succ, List.flatMap_cons,
      List.append_assoc]

/-- **A segment's runs, then `tail`** (`IdxSeg.runsThen_eq`), by the recursors. -/
noncomputable def IdxSeg.runsThen (s : IdxSeg) (tail : IndexMap) : IndexMap :=
  @IdxSeg.casesOn (fun _ => IndexMap) s (fun r => r :: tail) fun pat k => IdxSeg.repRuns pat tail k 0

theorem IdxSeg.runsThen_eq (s : IdxSeg) (tail : IndexMap) : s.runsThen tail = s.expand ++ tail := by
  cases s with
  | run r => rfl
  | rep pat k =>
    change IdxSeg.repRuns pat tail k 0 = _
    rw [IdxSeg.repRuns_eq]
    simp only [IdxSeg.expand, List.range_eq_range']

/-- **An index map given by segments**: the concatenation, in order, of the segments' runs
(`IndexMap.ofSegs_eq`), written with the recursors for the kernel (see above). -/
noncomputable def IndexMap.ofSegs (segs : List IdxSeg) : IndexMap :=
  @List.rec IdxSeg (fun _ => IndexMap) [] (fun s _ acc => s.runsThen acc) segs

/-- **The segments' runs concatenated**, by `flatMap`: the code compiled for `IndexMap.ofSegs`. -/
def IndexMap.ofSegsC (segs : List IdxSeg) : IndexMap := segs.flatMap IdxSeg.expand

/-- **An index map from segments is the concatenation of their runs.** -/
theorem IndexMap.ofSegs_eq (segs : List IdxSeg) : IndexMap.ofSegs segs = segs.flatMap IdxSeg.expand := by
  induction segs with
  | nil => rfl
  | cons s segs ih =>
    change s.runsThen (IndexMap.ofSegs segs) = _
    rw [IdxSeg.runsThen_eq, ih, List.flatMap_cons]

@[csimp] theorem IndexMap.ofSegs_csimp : @IndexMap.ofSegs = @IndexMap.ofSegsC := by
  funext segs
  exact IndexMap.ofSegs_eq segs

/-- **An index map from segments is the concatenation of their runs.** -/
@[simp] theorem IndexMap.ofSegs_nil : IndexMap.ofSegs [] = [] := rfl

/-- **An index map from segments is the concatenation of their runs.** -/
@[simp] theorem IndexMap.ofSegs_cons (s : IdxSeg) (segs : List IdxSeg) :
    IndexMap.ofSegs (s :: segs) = s.expand ++ IndexMap.ofSegs segs := by
  simp only [IndexMap.ofSegs_eq, List.flatMap_cons]

end GordieHowe.RealizedProgram
