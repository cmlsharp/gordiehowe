-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Foundations.Fields.BinarySpread
public import GordieHowe.ProofSystem.RingSwitching.StageAlgebra
public import GordieHowe.Foundations.Algebra.KummerTrace

@[expose] public section

/-!
# Relative power bases of binary fields from spread certificates

A relative power basis `β_j = g^j` of `F_{2^(m D)}` over `F_{2^m}` inside a binary field `L`, with
its trace-dual basis, certified by one kernel computation in the spread representation
(`GordieHowe.Foundations.Fields.BinarySpread`): the generator `g` and the dual elements are given by their
polynomial-basis bits, and `Tr(dual_i · g^j) = δ_ij` is an identity of spread naturals
(`Rep.trace_dual_of_spread`). Membership of a spread element in a subfield `F_{2^m}` is the identity
`x^(2^m) = x` of spread naturals (`Rep.valVia_mem_fixedField`). A relative basis whose elements lie
in `F_{2^(m D)}` is the stage basis of the stage `F_{2^m} < F_{2^(m D)}`
(`StageBasis.ofFixedField`).
-/

namespace GordieHowe

open RelativePacking

namespace PackingStage

variable {K : Type*} [Field K] {p m d : ℕ} [ExpChar K p]

/-- **The stage basis of `F_{p^m} < F_{p^(m d)}`** from a relative basis whose basis and dual
elements lie in `F_{p^(m d)}`: the top is the fixed field of `x ↦ x^(p^(m d))`. -/
def StageBasis.ofFixedField (B : RelativeBasis K p m d)
    (hβ : ∀ j, B.β j ∈ fixedField K p (m * d)) (hdual : ∀ j, B.dual j ∈ fixedField K p (m * d)) :
    StageBasis K p m d where
  toRelativeBasis := B
  top := fixedField K p (m * d)
  top_fixed y hy := by
    rw [mem_fixedField_iff_pow] at hy
    rw [phi_def]
    exact hy
  base_le _ hx := mem_fixedField_mul hx d
  β_mem := hβ
  dual_mem := hdual

theorem StageBasis.ofFixedField_top (B : RelativeBasis K p m d)
    (hβ : ∀ j, B.β j ∈ fixedField K p (m * d)) (hdual : ∀ j, B.dual j ∈ fixedField K p (m * d)) :
    (StageBasis.ofFixedField B hβ hdual).top = fixedField K p (m * d) :=
  rfl

end PackingStage

/-- `F_{p^m}` lies in `F_{p^(m k)}`. -/
theorem RelativePacking.fixedField_le_mul {K : Type*} [Field K] {p : ℕ} [ExpChar K p] (m k : ℕ) :
    fixedField K p m ≤ fixedField K p (m * k) := fun _ hx => mem_fixedField_mul hx k

namespace BinarySpread

open Polynomial

variable {f : (ZMod 2)[X]} {E : Exec} (R : Rep E f) {L : Type*} [Field L] [ExpChar L 2]
  (e : L ≃+* AdjoinRoot f)

/-- The representation of the bits `1` is the natural `1`. -/
theorem Exec.ofBits_one (hn : 0 < E.n) : E.ofBits 1 = 1 := by
  have h0 : ∀ i, E.spread i 0 = 0 := by
    intro i
    induction i with
    | zero => rfl
    | succ i ih => simp [Exec.spread, ih]
  obtain ⟨n, hn'⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  rw [Exec.ofBits, hn', Exec.spread]
  simp [h0]

/-- `Exec.trace m D` computes `relTrace 2 m D`. -/
theorem Rep.valVia_relTrace (R : Rep E f) (m D : ℕ) {y : ℕ} (hy : Canon E y) :
    valVia e E (E.trace m D y) = relTrace 2 m D (valVia e E y) := by
  rw [R.valVia_trace e m hy D, relTrace]
  rfl

/-- **Subfield membership by a spread identity**: `x^(2^m) = x`. -/
theorem Rep.valVia_mem_fixedField (R : Rep E f) {m v : ℕ}
    (h : E.sqPow m (E.ofBits v) = E.ofBits v) : valVia e E (E.ofBits v) ∈ fixedField L 2 m := by
  rw [mem_fixedField_iff_pow, ← R.valVia_sqPow e (Rep.canon_ofBits _), h]

/-- **The duality of a relative power basis from a spread certificate**: for `g` and `dual_i`
given by their bits and read in `L` by `toL` (`hv`: `toL v` is the element the spread natural of
`v` represents), `Tr_{F_{2^(m D)}/F_{2^m}}(dual_i · g^j) = δ_ij` follows from the same identity of
spread naturals (`h`, the powers `g^j` by square-and-multiply over `w` bits). -/
theorem Rep.trace_dual_of_spread (R : Rep E f) (toL : ℕ → L)
    (hv : ∀ v, valVia e E (E.ofBits v) = toL v) {m D w : ℕ} (hw : D ≤ 2 ^ w) {g : ℕ}
    {dualN : Fin D → ℕ}
    (h : ∀ i j : Fin D, E.trace m D (E.mul (E.ofBits (dualN i)) (E.pow w j (E.ofBits g))) =
      if i = j then E.ofBits 1 else 0) (i j : Fin D) :
    relTrace 2 m D (toL (dualN i) * toL g ^ (j : ℕ)) = if i = j then 1 else 0 := by
  have hj : Canon E (E.pow w j (E.ofBits g)) :=
    R.canon_pow (Rep.canon_ofBits _) w j (by omega)
  have hm := R.canon_mul (Rep.canon_ofBits (dualN i)) hj
  have h' := congrArg (valVia e E) (h i j)
  rw [R.valVia_relTrace e m D hm, R.valVia_mul e (Rep.canon_ofBits _) hj,
    R.valVia_pow e (Rep.canon_ofBits _) (by omega), R.valVia_ite e, Exec.ofBits_one R.n_pos,
    R.valVia_one e, R.valVia_zero e, hv, hv] at h'
  exact h'

end BinarySpread

end GordieHowe
