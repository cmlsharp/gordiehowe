-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Lattice.MLDSA

@[expose] public section

/-!
# Short kernel vectors of `[Â | I]` at ML-DSA by pigeonhole

At each approved ML-DSA parameter set, every matrix `Â ∈ T_q^{k×l}` has a nonzero `(z, u)` with
`Â * z + u = 0`, `‖z‖∞ ≤ msisStrictBoundZ p` and `‖u‖∞ ≤ msisBoundU p`. The proof is the pigeonhole
(Dirichlet) argument: there are `(B + 1)^(256 l)` vectors `z` with coefficients in `[0, B]`,
`B = γ₁ − β − 1`, and fewer cells `⌊c / W⌋` (`W = msisBoundU p`) for the coefficients of `Â * z`;
two vectors `z ≠ z'` in the same cell give `(z − z', −(Â * z − Â * z'))`.

- `coeffMatVecMul_sub`: `A * (u − v) = A * u − A * v` under the transform laws.
- `exists_kernel`: the short kernel vector at every matrix.
- `not_msisHard_univ`, `not_keyGenMSISHard_univ`: Module-SIS with a uniform matrix, and its
  key-generation form, are not hard for the class of all adversaries at any `ε < 1`, at the
  bounds `(msisStrictBoundZ p, msisBoundU p)`.
- `not_msisHard_univ_boundZ`, `not_keyGenMSISHard_univ_boundZ`: the same at
  `(msisBoundZ p, msisBoundU p)`.
-/

namespace GordieHowe.Lattice

open _root_.MLDSA LatticeCrypto TransformOps
open scoped ENNReal

section Linear

variable {Coeff : Type} [CommRing Coeff] {ring : NegacyclicRing Coeff} {Hat : Type}
  [AddCommGroup Hat] (ops : TransformOps ring Hat) [Laws ops]

/-- **Subtraction through the transform-domain product**: `A * (u − v) = A * u − A * v`. -/
theorem coeffMatVecMul_sub {r c : ℕ} (A : PolyMatrix Hat r c) (u v : PolyVec ring.Poly c) :
    A * (u - v) = A * u - A * v := by
  show ops.coeffMatVecMul A (u - v) = ops.coeffMatVecMul A u - ops.coeffMatVecMul A v
  -- `M (a − b) + M b = M a` by additivity, read entrywise.
  have hv : (ops.hatVec u - ops.hatVec v) + ops.hatVec v = ops.hatVec u :=
    Vector.ext fun i _ => by simp [Vector.getElem_add, Vector.getElem_sub]
  have hadd := matVecMul_add ops A (ops.hatVec u - ops.hatVec v) (ops.hatVec v)
  rw [hv] at hadd
  have hm : ops.matVecMul A (ops.hatVec u - ops.hatVec v) =
      ops.matVecMul A (ops.hatVec u) - ops.matVecMul A (ops.hatVec v) := by
    refine Vector.ext fun i hi => ?_
    have := congrArg (fun w : PolyVec Hat r => w[i]) hadd
    simp only [Vector.getElem_add] at this
    rw [Vector.getElem_sub, this, add_sub_cancel_right]
  simp only [coeffMatVecMul]
  rw [hatVec_sub, hm, unhatVec_sub]

end Linear

variable (p : Params)

/-- **The numeric facts of the pigeonhole** at an approved parameter set, with
`B = γ₁ − β − 1` and `W = msisBoundU p`: `0 < W`, `2W < q`, `2B < q`, `B ≤ msisStrictBoundZ p`,
and `(⌊q / W⌋ + 1)^k < (B + 1)^l`. -/
theorem pigeon_facts (hp : p.isApproved) :
    0 < msisBoundU p ∧ 2 * msisBoundU p < modulus ∧ 2 * (p.gamma1 - p.beta - 1) < modulus ∧
      p.gamma1 - p.beta - 1 ≤ msisStrictBoundZ p ∧
      (modulus / msisBoundU p + 1) ^ p.k < (p.gamma1 - p.beta - 1 + 1) ^ p.l := by
  rcases hp with rfl | rfl | rfl <;>
    norm_num [msisBoundU, msisStrictBoundZ, mldsa44, mldsa65, mldsa87, ParameterSet.params,
      Params.beta, modulus]

/-- A coefficientwise bound bounds the centered `∞`-norm of an ML-DSA polynomial. -/
theorem polyNorm_le_of_coeff {f : Rq} {b : ℕ}
    (h : ∀ i, (centeredRepr (polyBackend.coeff f i)).natAbs ≤ b) : normOps.cInfNorm f ≤ b := by
  simp only [normOps, zmodPolyNormOps, normOpsOfCenteredView, cInfNormOf, Finset.sup_le_iff]
  exact fun i _ => h i

/-- The coefficients of a difference of vectors are the differences of the coefficients. -/
theorem coeff_vsub {m : ℕ} (v w : RqVec m) (j : Fin m) (i : Fin polyBackend.degree) :
    polyBackend.coeff ((v - w).get j) i =
      polyBackend.coeff (v.get j) i - polyBackend.coeff (w.get j) i := by
  rw [Vector.get_eq_getElem, Vector.getElem_sub]
  exact NegacyclicRing.coeff_sub coeffRing _ _ _

/-- The coefficients of a negated vector are the negated coefficients. -/
theorem coeff_vneg {m : ℕ} (v : RqVec m) (j : Fin m) (i : Fin polyBackend.degree) :
    polyBackend.coeff ((-v).get j) i = -polyBackend.coeff (v.get j) i := by
  rw [Vector.get_eq_getElem, Vector.getElem_neg]
  exact NegacyclicRing.coeff_neg coeffRing _ _

/-- The coefficients of the zero vector are zero. -/
theorem coeff_vzero {m : ℕ} (j : Fin m) (i : Fin polyBackend.degree) :
    polyBackend.coeff ((0 : RqVec m).get j) i = 0 := by
  simp [Vector.get_eq_getElem]

variable [nttOps : NTTRingOps] [NTTRingLaws nttOps]

/-- **Every ML-DSA matrix has a short kernel vector of `[Â | I]`** at an approved parameter set:
a nonzero `(z, u)` with `Â * z + u = 0`, `‖z‖∞ ≤ msisStrictBoundZ p` and `‖u‖∞ ≤ msisBoundU p`,
by pigeonhole. -/
theorem exists_kernel (hp : p.isApproved) (aHat : TqMatrix p.k p.l) :
    ∃ x, Kernel p (msisStrictBoundZ p) (msisBoundU p) aHat x := by
  classical
  obtain ⟨hW0, hW, hB, hBz, hcount⟩ := pigeon_facts p hp
  set B := p.gamma1 - p.beta - 1 with hBdef
  set W := msisBoundU p with hWdef
  set N := modulus / W + 1 with hNdef
  -- The vector with coefficients `g`.
  let emb : (Fin p.l → Fin ringDegree → Fin (B + 1)) → RqVec p.l := fun g =>
    Vector.ofFn fun j => polyBackend.build fun i => (((g j i : ℕ) : Coeff))
  have hemb : ∀ g j i, polyBackend.coeff ((emb g).get j) i = (((g j i : ℕ) : Coeff)) := by
    intro g j i
    simp only [emb]
    erw [Vector.get_eq_getElem, Vector.getElem_ofFn]
    exact Poly.get_vectorOfFn _ i
  -- The cell of each coefficient of a vector.
  have hcell : ∀ c : Coeff, c.val / W < N := fun c =>
    Nat.lt_succ_of_le (Nat.div_le_div_right (ZMod.val_lt c).le)
  let cell : RqVec p.k → Fin p.k → Fin ringDegree → Fin N := fun w j i =>
    ⟨(polyBackend.coeff (w.get j) i).val / W, hcell _⟩
  let f := fun g => cell (aHat * emb g)
  have hcard : Fintype.card (Fin p.k → Fin ringDegree → Fin N) <
      Fintype.card (Fin p.l → Fin ringDegree → Fin (B + 1)) := by
    simp only [Fintype.card_fun, Fintype.card_fin]
    rw [← pow_mul, ← pow_mul, mul_comm, pow_mul, mul_comm, pow_mul]
    exact pow_lt_pow_left₀ hcount (Nat.zero_le _) (by norm_num [ringDegree])
  obtain ⟨g, g', hne, hfg⟩ := Fintype.exists_ne_map_eq_of_card_lt f hcard
  have hlt : ∀ a : Fin (B + 1), (a : ℕ) < modulus := fun a => by have := a.isLt; omega
  set z := emb g
  set z' := emb g'
  refine ⟨(z - z', -(aHat * z - aHat * z')), KernelAI.of_fst_ne_zero ?_ ?_ ?_ ?_⟩
  · -- `z ≠ z'`, read on the coefficients.
    intro h
    apply hne
    funext j i
    have h1 := congrArg (fun v : RqVec p.l => polyBackend.coeff (v.get j) i) h
    simp only [coeff_vsub, hemb, z, z'] at h1
    rw [coeff_vzero, sub_eq_zero] at h1
    have h2 := congrArg ZMod.val h1
    rw [ZMod.val_natCast_of_lt (hlt _), ZMod.val_natCast_of_lt (hlt _)] at h2
    exact Fin.ext h2
  · rw [coeffMatVecMul_sub]
    refine Vector.ext fun j _ => ?_
    simp [Vector.getElem_add, Vector.getElem_neg]
    exact sub_self _
  · refine (PolyVec.cInfNorm_le_iff normOps).2 fun j => polyNorm_le_of_coeff fun i => ?_
    rw [coeff_vsub, hemb, hemb]
    have ha := (g j i).isLt
    have hb := (g' j i).isLt
    have hcast : (((g j i : ℕ) : Coeff)) - (((g' j i : ℕ) : Coeff)) =
        ((((g j i : ℕ) : ℤ) - ((g' j i : ℕ) : ℤ) : ℤ) : Coeff) := by push_cast; rfl
    rw [hcast, centeredRepr_intCast_eq_of_natAbs_le _ (b := B) (by omega) hB]
    omega
  · refine (PolyVec.cInfNorm_le_iff normOps).2 fun j => polyNorm_le_of_coeff fun i => ?_
    rw [coeff_vneg, centeredRepr_natAbs_neg, coeff_vsub]
    set c := polyBackend.coeff ((aHat * z).get j) i
    set c' := polyBackend.coeff ((aHat * z').get j) i
    -- The two coefficients lie in the same cell.
    have hsame : c.val / W = c'.val / W := congrArg Fin.val (congrFun (congrFun hfg j) i)
    have hcast : c - c' = (((c.val : ℤ) - (c'.val : ℤ) : ℤ) : Coeff) := by
      push_cast
      rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
    have h1 := Nat.div_add_mod c.val W
    have h2 := Nat.div_add_mod c'.val W
    have h3 := Nat.mod_lt c.val hW0
    have h4 := Nat.mod_lt c'.val hW0
    rw [hsame] at h1
    generalize W * (c'.val / W) = t at h1 h2
    rw [hcast, centeredRepr_intCast_eq_of_natAbs_le _ (b := W) (by omega) hW]
    omega

/-- **Module-SIS is not hard for all adversaries below `1`** at an approved ML-DSA parameter set,
with bounds `(msisStrictBoundZ p, msisBoundU p)`: the adversary that outputs the kernel vector of
`exists_kernel` wins with probability one (`not_hard_univ`). -/
theorem not_msisHard_univ (hp : p.isApproved) {ε : ℝ≥0∞} (hε : ε < 1) :
    ¬ MSISHard (Hat := Tq) (k := p.k) (l := p.l) normOps (msisStrictBoundZ p) (msisBoundU p)
      Set.univ ε :=
  not_hard_univ (exists_kernel p hp) hε

/-- The same at the bounds `(msisBoundZ p, msisBoundU p)`, which are at least as large. -/
theorem not_msisHard_univ_boundZ (hp : p.isApproved) {ε : ℝ≥0∞} (hε : ε < 1) :
    ¬ MSISHard (Hat := Tq) (k := p.k) (l := p.l) normOps (msisBoundZ p) (msisBoundU p)
      Set.univ ε := fun h =>
  not_msisHard_univ p hp hε (h.mono_bounds (msisStrictBoundZ_le p) le_rfl)

variable (prims : Primitives p)

/-- **The key-generation form is not hard for all adversaries below `1`** at an approved ML-DSA
parameter set, with bounds `(msisStrictBoundZ p, msisBoundU p)`: every key-generation matrix has
the kernel vector of `exists_kernel`. -/
theorem not_keyGenMSISHard_univ (hp : p.isApproved) {ε : ℝ≥0∞} (hε : ε < 1) :
    ¬ KeyGenMSISHard p prims (msisStrictBoundZ p) (msisBoundU p) Set.univ ε :=
  not_hard_univ (fun ξ => exists_kernel p hp (keyGenMatrix p prims ξ)) hε

/-- The same at the bounds `(msisBoundZ p, msisBoundU p)`. -/
theorem not_keyGenMSISHard_univ_boundZ (hp : p.isApproved) {ε : ℝ≥0∞} (hε : ε < 1) :
    ¬ KeyGenMSISHard p prims (msisBoundZ p) (msisBoundU p) Set.univ ε := fun h =>
  not_keyGenMSISHard_univ p prims hp hε
    (Hard.mono_valid h fun _ _ hx => hx.mono (msisStrictBoundZ_le p) le_rfl)

end GordieHowe.Lattice
