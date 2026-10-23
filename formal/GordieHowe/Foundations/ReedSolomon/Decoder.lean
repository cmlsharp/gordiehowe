-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Foundations.ToMathlib.SubfieldCode
public import GordieHowe.Foundations.ReedSolomon.BerlekampWelch

@[expose] public section

/-!
# Decoding a Reed–Solomon row matrix

Column distance counts a column once if any row disagrees. The unique-decoding radius ensures
that two nearby polynomial matrices coincide (`nearby_unique`). Extraction reads evaluations of
this uniquely determined matrix, or zero if decoding fails.

`decode` computes it: it decodes each row of `U` on its own with Berlekamp–Welch
(`BerlekampWelch.decode`), then counts the columns at which some row disagrees with its decoded
polynomial and succeeds iff at most `e` do (`decode_eq_some_iff`, `decode_eq_none_iff`). `read`
evaluates a decoded row. `nearbyRows` is the view, used in proofs, of the same value as a matrix of
polynomials, used to state the bad events of the proximity tests (`decode_map`).
-/

namespace GordieHowe.RSCode

open Polynomial

/-- Fixed code parameters, including the unique-decoding radius. -/
structure _root_.GordieHowe.RSCode (F : Type*) [Field F] (N : ℕ) where
  D : Fin N → F
  D_injective : Function.Injective D
  k : ℕ
  e : ℕ
  k_pos : 0 < k
  radius : 2 * e + k ≤ N

abbrev Matrix (F : Type*) (R N : ℕ) := Fin R → Fin N → F

variable {F : Type*} [Field F] {R N : ℕ}

section NearbyRows

open scoped Classical

/-- Columns on which at least one row differs from its polynomial. -/
noncomputable def columnErrors (C : RSCode F N) (U : Matrix F R N)
    (fs : Fin R → F[X]) : Finset (Fin N) :=
  Finset.univ.filter fun j => ∃ r, U r j ≠ (fs r).eval (C.D j)

@[simp] theorem mem_columnErrors {C : RSCode F N} {U : Matrix F R N}
    {fs : Fin R → F[X]} {j : Fin N} :
    j ∈ columnErrors C U fs ↔ ∃ r, U r j ≠ (fs r).eval (C.D j) := by
  simp [columnErrors]

/-- Degree-bounded rows within the specified column radius. -/
structure Nearby (C : RSCode F N) (U : Matrix F R N) (fs : Fin R → F[X]) : Prop where
  degree : ∀ r, (fs r).natDegree < C.k
  close : (columnErrors C U fs).card ≤ C.e

theorem Nearby.row_close {C : RSCode F N} {U : Matrix F R N}
    {fs : Fin R → F[X]} (h : Nearby C U fs) (r : Fin R) :
    (Finset.univ.filter fun j => U r j ≠ (fs r).eval (C.D j)).card ≤ C.e := by
  apply le_trans (Finset.card_le_card ?_) h.close
  intro j hj
  exact mem_columnErrors.mpr ⟨r, (Finset.mem_filter.mp hj).2⟩

/-- Distinct degree-bounded polynomial matrices cannot both be nearby. The
radius is a fixed parameter condition; proximity is the predicate being
analyzed, not an assumption about an arbitrary prover. -/
theorem nearby_unique {C : RSCode F N} {U : Matrix F R N}
    {fs gs : Fin R → F[X]} (hf : Nearby C U fs) (hg : Nearby C U gs) : fs = gs := by
  let B := columnErrors C U fs ∪ columnErrors C U gs
  let A := Finset.univ \ B
  have hB : B.card ≤ 2 * C.e := by
    have hu := Finset.card_union_le (columnErrors C U fs) (columnErrors C U gs)
    have hfc := hf.close
    have hgc := hg.close
    dsimp [B]
    omega
  have hA : C.k ≤ A.card := by
    have hs := Finset.le_card_sdiff B (Finset.univ : Finset (Fin N))
    have hr := C.radius
    simp only [Finset.card_univ, Fintype.card_fin] at hs
    dsimp [A]
    omega
  let S := A.image C.D
  have hS : S.card = A.card := Finset.card_image_of_injective _ C.D_injective
  funext r
  apply Polynomial.eq_of_degree_sub_lt_of_eval_finset_eq S
  · have hfdeg : (fs r).degree < (S.card : WithBot ℕ) :=
      (Polynomial.degree_le_natDegree).trans_lt (by exact_mod_cast (hf.degree r).trans_le (hS ▸ hA))
    have hgdeg : (gs r).degree < (S.card : WithBot ℕ) :=
      (Polynomial.degree_le_natDegree).trans_lt (by exact_mod_cast (hg.degree r).trans_le (hS ▸ hA))
    exact (Polynomial.degree_sub_le _ _).trans_lt (max_lt hfdeg hgdeg)
  · intro x hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
    have hjB := (Finset.mem_sdiff.mp hj).2
    have hfj : U r j = (fs r).eval (C.D j) := by
      by_contra h
      exact hjB (Finset.mem_union_left _ (mem_columnErrors.mpr ⟨r, h⟩))
    have hgj : U r j = (gs r).eval (C.D j) := by
      by_contra h
      exact hjB (Finset.mem_union_right _ (mem_columnErrors.mpr ⟨r, h⟩))
    exact hfj.symm.trans hgj

/-- **The nearby polynomial matrix**, if one exists: the unique (`nearby_unique`) matrix of
polynomials of degree `< k` within `e` columns of `U`. For the proofs: the bad events of the
proximity tests are stated with it; the extractor computes the same value with `decode`
(`decode_map`). -/
noncomputable def nearbyRows (C : RSCode F N) (U : Matrix F R N) : Option (Fin R → F[X]) :=
  if h : ∃ fs, Nearby C U fs then some h.choose else none

theorem nearbyRows_eq_some_iff {C : RSCode F N} {U : Matrix F R N} {fs : Fin R → F[X]} :
    nearbyRows C U = some fs ↔ Nearby C U fs := by
  unfold nearbyRows
  split
  · rename_i h
    constructor
    · intro heq
      cases Option.some.inj heq
      exact h.choose_spec
    · intro hf
      exact congrArg some (nearby_unique h.choose_spec hf)
  · rename_i h
    constructor
    · intro heq
      cases heq
    · intro hf
      exact (h ⟨fs, hf⟩).elim

theorem nearbyRows_eq_none_iff {C : RSCode F N} {U : Matrix F R N} :
    nearbyRows C U = none ↔ ¬ ∃ fs, Nearby C U fs := by
  simp [nearbyRows]

theorem nearbyRows_degree {C : RSCode F N} {U : Matrix F R N} {fs : Fin R → F[X]}
    (h : nearbyRows C U = some fs) (r : Fin R) : (fs r).natDegree < C.k :=
  (nearbyRows_eq_some_iff.mp h).degree r

theorem nearbyRows_row_close {C : RSCode F N} {U : Matrix F R N} {fs : Fin R → F[X]}
    (h : nearbyRows C U = some fs) (r : Fin R) :
    (Finset.univ.filter fun j => U r j ≠ (fs r).eval (C.D j)).card ≤ C.e :=
  (nearbyRows_eq_some_iff.mp h).row_close r

end NearbyRows

/-! ### The decoder -/

section Decode

open BerlekampWelch (evalCoeffs ofCoeffs eval_ofCoeffs natDegree_ofCoeffs_lt ofCoeffs_coeff
  errorSet)

variable [DecidableEq F]

/-- Columns on which at least one row differs from the polynomial with its coefficient vector. -/
def columnErrorsOfCoeffs (C : RSCode F N) (U : Matrix F R N) (cs : Fin R → Fin C.k → F) :
    Finset (Fin N) :=
  Finset.univ.filter fun j => ∃ r, U r j ≠ evalCoeffs (cs r) (C.D j)

theorem columnErrorsOfCoeffs_eq (C : RSCode F N) (U : Matrix F R N) (cs : Fin R → Fin C.k → F) :
    columnErrorsOfCoeffs C U cs = columnErrors C U fun r => ofCoeffs (cs r) := by
  ext j
  simp [columnErrorsOfCoeffs, eval_ofCoeffs]

/-- The row-decoding error set of `BerlekampWelch.decode` is the one `Nearby.row_close` bounds. -/
theorem errorSet_eq_filter (C : RSCode F N) (u : Fin N → F) (c : Fin C.k → F) :
    BerlekampWelch.errorSet C.D u c = Finset.univ.filter fun j => u j ≠ (ofCoeffs c).eval (C.D j) := by
  ext j
  simp [BerlekampWelch.errorSet, eval_ofCoeffs]

/-- Decode a row matrix: the coefficient vectors of the unique nearby polynomial matrix, if it
exists (`decode_eq_some_iff`, `decode_eq_none_iff`).

Running time: `R` Berlekamp–Welch row decodings, `O(R · N · (2e + k)²)` field operations
(`BerlekampWelch.decode`), each computed once and stored in an array; then the column count
evaluates every decoded row at every point, `O(R · N · k · log k)`. In total
`O(R · N · (2e + k)²) ⊆ O(R · N³)` field operations. This running time is argued here, not proved in
Lean. -/
def decode (C : RSCode F N) (U : Matrix F R N) : Option (Fin R → Fin C.k → F) :=
  let rows : Vector (Option (Fin C.k → F)) R :=
    Vector.ofFn fun r => BerlekampWelch.decode C.D C.k C.e (U r)
  if h : ∀ r : Fin R, (rows.get r).isSome then
    let cs : Fin R → Fin C.k → F := fun r => (rows.get r).get (h r)
    if (columnErrorsOfCoeffs C U cs).card ≤ C.e then some cs else none
  else none

/-- A decoded row matrix is within `e` columns of `U`, row by row decoded. -/
theorem decode_eq_some_iff {C : RSCode F N} {U : Matrix F R N} {cs : Fin R → Fin C.k → F} :
    decode C U = some cs ↔ Nearby C U fun r => ofCoeffs (cs r) := by
  have hrow : ∀ r, BerlekampWelch.decode C.D C.k C.e (U r) = some (cs r) ↔
      (BerlekampWelch.errorSet C.D (U r) (cs r)).card ≤ C.e := fun r =>
    BerlekampWelch.decode_eq_some_iff C.D_injective (by have := C.radius; omega) C.k_pos
  constructor
  · intro h
    unfold decode at h
    simp only [GaussianElimination.get_ofFn'] at h
    split_ifs at h with hs hc
    cases h
    refine ⟨fun r => natDegree_ofCoeffs_lt C.k_pos _, ?_⟩
    rw [← columnErrorsOfCoeffs_eq]
    exact hc
  · intro h
    have hdec : ∀ r, BerlekampWelch.decode C.D C.k C.e (U r) = some (cs r) := fun r =>
      (hrow r).mpr (by rw [errorSet_eq_filter]; convert h.row_close r)
    have hs : ∀ r : Fin R,
        ((Vector.ofFn fun r => BerlekampWelch.decode C.D C.k C.e (U r)).get r).isSome := by
      intro r
      simp [hdec r]
    have hcs : (fun r => ((Vector.ofFn fun r =>
        BerlekampWelch.decode C.D C.k C.e (U r)).get r).get (hs r)) = cs := by
      funext r
      simp [hdec r]
    have hc : (columnErrorsOfCoeffs C U cs).card ≤ C.e := by
      rw [columnErrorsOfCoeffs_eq]
      exact h.close
    unfold decode
    simp only [hs, hcs, hc, ↓reduceIte, implies_true, ↓reduceDIte]

/-- Decoding fails iff no polynomial matrix is nearby. -/
theorem decode_eq_none_iff {C : RSCode F N} {U : Matrix F R N} :
    decode C U = none ↔ ¬ ∃ fs, Nearby C U fs := by
  constructor
  · rintro h ⟨fs, hfs⟩
    have hco : (fun r => ofCoeffs (fun i : Fin C.k => (fs r).coeff i)) = fs :=
      funext fun r => ofCoeffs_coeff (hfs.degree r)
    have := decode_eq_some_iff (C := C) (U := U)
      (cs := fun r i => (fs r).coeff i) |>.mpr (by rw [hco]; exact hfs)
    rw [h] at this
    cases this
  · intro h
    cases hd : decode C U with
    | none => rfl
    | some cs => exact (h ⟨_, decode_eq_some_iff.mp hd⟩).elim

/-- `nearbyRows` is `decode` followed by the map, used in proofs, from coefficient vectors to
polynomials. -/
theorem decode_map (C : RSCode F N) (U : Matrix F R N) :
    (decode C U).map (fun cs r => ofCoeffs (cs r)) = nearbyRows C U := by
  cases hd : decode C U with
  | none => exact (nearbyRows_eq_none_iff.mpr (decode_eq_none_iff.mp hd)).symm
  | some cs => exact (nearbyRows_eq_some_iff.mpr (decode_eq_some_iff.mp hd)).symm

/-- Read a message-position evaluation; failed decoding uses the fixed zero default.

Running time: one `decode` (its docstring, shared by all reads of the same matrix) and one
evaluation of a coefficient vector of length `k`, `O(k log k)`.
This running time is argued here, not proved in Lean. -/
def read (C : RSCode F N) (U : Matrix F R N) (r : Fin R) (x : F) : F :=
  match decode C U with
  | some cs => evalCoeffs (cs r) x
  | none => 0

theorem read_of_nearby {C : RSCode F N} {U : Matrix F R N} {fs : Fin R → F[X]}
    (h : Nearby C U fs) (r : Fin R) (x : F) : read C U r x = (fs r).eval x := by
  have hco : (fun r => ofCoeffs (fun i : Fin C.k => (fs r).coeff i)) = fs :=
    funext fun r => ofCoeffs_coeff (h.degree r)
  have hd : decode C U = some fun r (i : Fin C.k) => (fs r).coeff i :=
    decode_eq_some_iff.mpr (by rw [hco]; exact h)
  rw [read, hd]
  dsimp only
  rw [← eval_ofCoeffs, congrFun hco r]

theorem read_of_not_nearby {C : RSCode F N} {U : Matrix F R N} (h : ¬ ∃ fs, Nearby C U fs)
    (r : Fin R) (x : F) : read C U r x = 0 := by
  rw [read, decode_eq_none_iff.mpr h]

/-- A read is the evaluation of the nearby polynomial matrix, or zero. -/
theorem read_eq_nearbyRows (C : RSCode F N) (U : Matrix F R N) (r : Fin R) (x : F) :
    read C U r x = match nearbyRows C U with
      | some fs => (fs r).eval x
      | none => 0 := by
  cases hn : nearbyRows C U with
  | none => exact read_of_not_nearby (nearbyRows_eq_none_iff.mp hn) r x
  | some fs => exact read_of_nearby (nearbyRows_eq_some_iff.mp hn) r x

end Decode

end GordieHowe.RSCode
