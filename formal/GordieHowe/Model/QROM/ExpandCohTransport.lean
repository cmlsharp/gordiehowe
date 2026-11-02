-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.QROM.DensityRunTransport

@[expose] public section

/-!
# Two expanded coherent runs related by permutations carried between the steps

A core algorithm `A` and the algorithm `A.withStep' K'` on `A`'s registers with other Kraus maps
`K'`, related by permutations carried between the steps (as `densityRun_transport`, with the
carried permutation `1` after the last step): their expanded coherent purifications have the same
law (`simLaw_expandAdv_transport`).

- `Alg.withStep'`: `A`'s registers, depth, initial state and output with other Kraus maps.
- `Alg.castDepth`, `simLaw_expandAdv_castDepth`: an algorithm read with an equal depth.
- `liftE`, `liftKraus_apply_eq`: a permutation and a Kraus map on the expansion's registers.
- `simQueryKernel_qIn` (with `hadamardKernel_qIn`, `decKernel_fst`, `phaseKernel_eq`): the
  simulated query keeps the query input.
- `liftP`, `liftSup`, `liftKraus_transport`, `liftKraus_supp`: the carried permutations and
  supports on the expansion's registers.
- `simLaw_expandAdv_transport`.
-/

open Matrix
open scoped BigOperators ENNReal Kronecker

namespace GordieHowe.Quantum

namespace Alg

variable {X Y O : Type} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]

/-- **`A`'s registers, depth, initial state and output, with the Kraus maps `K'`.** -/
abbrev withStep' (A : Alg X Y O) {R' : Type} [Fintype R']
    (K' : Fin (A.depth + 1) → KrausMap R' (QueryReg A.V 1 X Y) (QueryReg A.V 1 X Y)) :
    Alg X Y O where
  V := A.V
  depth := A.depth
  R := R'
  init := A.init
  step := K'
  out := A.out

/-- **An algorithm read with an equal depth** `d`. -/
abbrev castDepth (A : Alg X Y O) (d : ℕ) (h : A.depth = d) : Alg X Y O where
  V := A.V
  depth := d
  R := A.R
  init := A.init
  step i := A.step (Fin.cast (by omega) i)
  out := A.out

end Alg

end GordieHowe.Quantum

namespace GordieHowe.QROM

open GordieHowe.Quantum ExpandAdv

variable {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] {m : ℕ}
  {B C : Type} (e : BitStr I J ≃ B) (E : Expansion (Bits m) B C) (k : ℕ)

/-- **An algorithm read with an equal depth has the same expanded coherent law.** -/
theorem simLaw_expandAdv_castDepth {O : Type} (A : Alg (Bits m) (BitStr I J) O) (d : ℕ)
    (h : A.depth = d) (g : Option O → C) :
    simLaw e (expandAdv e E k ((A.castDepth d h).toQueryAlgCoh.mapOut g)) =
      simLaw e (expandAdv e E k (A.toQueryAlgCoh.mapOut g)) := by
  obtain ⟨V, depth, R, init, step, out⟩ := A
  subst h
  rfl

theorem tracePreserving_castDepth {O : Type} {A : Alg (Bits m) (BitStr I J) O}
    (hA : A.TracePreserving) (d : ℕ) (h : A.depth = d) : (A.castDepth d h).TracePreserving :=
  fun _ => hA _

variable {V : Type} [Fintype V] [DecidableEq V]

/-- **A permutation of `Q`'s registers on the expansion's registers.** -/
def liftE (π : Equiv.Perm (QueryReg V 1 (Bits m) (BitStr I J))) :
    Equiv.Perm (ExpBasis (X := Bits m) (Y := BitStr I J) k V) :=
  (registerSplit k V).symm.permCongr (π.prodCongr (Equiv.refl _))

theorem liftE_apply (π : Equiv.Perm (QueryReg V 1 (Bits m) (BitStr I J)))
    (b : ExpBasis (X := Bits m) (Y := BitStr I J) k V) :
    liftE k π b = (registerSplit k V).symm (π (registerSplit k V b).1, (registerSplit k V b).2) :=
  rfl

theorem liftE_one :
    liftE (V := V) (m := m) (I := I) (J := J) k 1 = 1 :=
  Equiv.ext fun _ => rfl

/-- A permutation that keeps the query pair keeps it on the expansion's registers. -/
theorem queryPairFix_liftE {π : Equiv.Perm (QueryReg V 1 (Bits m) (BitStr I J))}
    (hπ : QueryPairFix π) : QueryPairFix (liftE k π) := by
  obtain ⟨τ, hτ⟩ := hπ
  refine ⟨fun x => (τ x).prodCongr (Equiv.refl _), fun b => ?_⟩
  rw [liftE_apply, hτ]
  rfl

variable {R : Type} [Fintype R]

/-- **A lifted Kraus map applied to a matrix**, through the split of the expansion's
registers. -/
theorem liftKraus_apply_eq (K : KrausMap R (QueryReg V 1 (Bits m) (BitStr I J))
    (QueryReg V 1 (Bits m) (BitStr I J)))
    (ρ : Matrix (ExpBasis (X := Bits m) (Y := BitStr I J) k V)
      (ExpBasis (X := Bits m) (Y := BitStr I J) k V) ℂ) :
    liftKraus k K ρ = ((K.tensorId _) (ρ.submatrix (registerSplit k V).symm
      (registerSplit k V).symm)).submatrix (registerSplit k V) (registerSplit k V) := by
  have h := KrausMap.relabel_apply_submatrix (K.tensorId ((Bits m × BitStr I J) ×
    (Fin k → BitStr I J))) (registerSplit k V).symm
    (ρ.submatrix (registerSplit k V).symm (registerSplit k V).symm)
  simp only [Equiv.symm_symm, Matrix.submatrix_submatrix, Equiv.symm_comp_self,
    Matrix.submatrix_id_id] at h
  exact h

/-- The support `S` of `Q`'s registers on the expansion's registers. -/
def liftS (S : Set (QueryReg V 1 (Bits m) (BitStr I J))) :
    Set (ExpBasis (X := Bits m) (Y := BitStr I J) k V) :=
  {b | (registerSplit k V b).1 ∈ S}

theorem hadamardKernel_qIn {t : ℕ} {b' b : SimRegister V I J m t}
    (h : hadamardKernel V t b' b ≠ 0) : qIn b'.1 = qIn b.1 := by
  unfold hadamardKernel at h
  by_cases hc : b'.1.1 = b.1.1 ∧ qIn b'.1 = qIn b.1 ∧ b'.2 = b.2
  · exact hc.2.1
  · exact absurd (if_neg hc) h

theorem decKernel_fst {t : ℕ} {b' b : SimRegister V I J m t}
    (h : decKernel e V t b' b ≠ 0) : b'.1 = b.1 := by
  unfold decKernel at h
  by_cases hc : b'.1 = b.1
  · exact hc
  · exact absurd (if_neg hc) h

theorem phaseKernel_eq {t : ℕ} {b' b : SimRegister V I J m t}
    (h : phaseKernel e V t b' b ≠ 0) : b' = b := by
  unfold phaseKernel at h
  by_cases hc : b' = b
  · exact hc
  · exact absurd (if_neg hc) h

/-- **The simulated query keeps the query input.** -/
theorem simQueryKernel_qIn {t : ℕ} {b' b : SimRegister V I J m t}
    (h : simQueryKernel e V t b' b ≠ 0) : (b'.1.2 0).1 = (b.1.2 0).1 := by
  unfold simQueryKernel at h
  obtain ⟨c, -, hc⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  obtain ⟨c₁, -, hc₁⟩ := Finset.exists_ne_zero_of_sum_ne_zero (right_ne_zero_of_mul hc)
  obtain ⟨c₂, -, hc₂⟩ := Finset.exists_ne_zero_of_sum_ne_zero (right_ne_zero_of_mul hc₁)
  obtain ⟨c₃, -, hc₃⟩ := Finset.exists_ne_zero_of_sum_ne_zero (right_ne_zero_of_mul hc₂)
  have e1 := hadamardKernel_qIn (left_ne_zero_of_mul hc)
  have e2 := decKernel_fst e (left_ne_zero_of_mul hc₁)
  have e3 := phaseKernel_eq e (left_ne_zero_of_mul hc₂)
  have e4 := decKernel_fst e (left_ne_zero_of_mul hc₃)
  have e5 := hadamardKernel_qIn (right_ne_zero_of_mul hc₃)
  subst e3
  change qIn b'.1 = qIn b.1
  rw [e1, e2, e4, e5]

/-- The carried permutations on the expansion's registers: `P i` lifted up to the last step of
`A`, `1` after it. -/
def liftP (d : ℕ) (P : ℕ → Equiv.Perm (QueryReg V 1 (Bits m) (BitStr I J))) (i : ℕ) :
    Equiv.Perm (ExpBasis (X := Bits m) (Y := BitStr I J) k V) :=
  if i ≤ d then liftE k (P i) else 1

/-- The supports on the expansion's registers: `S i` lifted up to the last step, everything after
it. -/
def liftSup (d : ℕ) (S : ℕ → Set (QueryReg V 1 (Bits m) (BitStr I J))) (i : ℕ) :
    Set (ExpBasis (X := Bits m) (Y := BitStr I J) k V) :=
  if i ≤ d then liftS k (S i) else Set.univ

/-- A channel identity with carried permutations, lifted to the expansion's registers. -/
theorem liftKraus_transport {R' : Type} [Fintype R']
    {K' : KrausMap R' (QueryReg V 1 (Bits m) (BitStr I J)) (QueryReg V 1 (Bits m) (BitStr I J))}
    {K : KrausMap R (QueryReg V 1 (Bits m) (BitStr I J)) (QueryReg V 1 (Bits m) (BitStr I J))}
    {σ' σ : Equiv.Perm (QueryReg V 1 (Bits m) (BitStr I J))}
    {S : Set (QueryReg V 1 (Bits m) (BitStr I J))}
    (h : ∀ ρ, Supp S ρ → K' (ρ.submatrix σ.symm σ.symm) = (K ρ).submatrix σ'.symm σ'.symm)
    (ρ : Matrix (ExpBasis (X := Bits m) (Y := BitStr I J) k V)
      (ExpBasis (X := Bits m) (Y := BitStr I J) k V) ℂ) (hρ : Supp (liftS k S) ρ) :
    liftKraus k K' (ρ.submatrix (liftE k σ).symm (liftE k σ).symm) =
      (liftKraus k K ρ).submatrix (liftE k σ').symm (liftE k σ').symm := by
  rw [liftKraus_apply_eq, liftKraus_apply_eq]
  have hM : Supp {p | p.1 ∈ S} (ρ.submatrix (registerSplit k V).symm (registerSplit k V).symm) :=
    fun a b hab => by
      have := hρ _ _ hab
      simpa [liftS] using this
  have e1 : (ρ.submatrix (liftE k σ).symm (liftE k σ).symm).submatrix (registerSplit k V).symm
      (registerSplit k V).symm = (ρ.submatrix (registerSplit k V).symm
        (registerSplit k V).symm).submatrix (σ.prodCongr (Equiv.refl _)).symm
          (σ.prodCongr (Equiv.refl _)).symm := by
    ext a b
    rfl
  rw [e1, tensorId_apply_submatrix_of h _ hM]
  ext a b
  rfl

/-- Supports through a lifted Kraus map. -/
theorem liftKraus_supp
    {K : KrausMap R (QueryReg V 1 (Bits m) (BitStr I J)) (QueryReg V 1 (Bits m) (BitStr I J))}
    {S S' : Set (QueryReg V 1 (Bits m) (BitStr I J))} (h : ∀ ρ, Supp S ρ → Supp S' (K ρ))
    (ρ : Matrix (ExpBasis (X := Bits m) (Y := BitStr I J) k V)
      (ExpBasis (X := Bits m) (Y := BitStr I J) k V) ℂ) (hρ : Supp (liftS k S) ρ) :
    Supp (liftS k S') (liftKraus k K ρ) := by
  rw [liftKraus_apply_eq]
  have hM : Supp {p | p.1 ∈ S} (ρ.submatrix (registerSplit k V).symm (registerSplit k V).symm) :=
    fun a b hab => by
      have := hρ _ _ hab
      simpa [liftS] using this
  intro a b hab
  have := tensorId_supp_of h _ hM _ _ hab
  exact this

omit [Fintype V] [DecidableEq V] in
theorem liftP_of_le {d : ℕ} (P : ℕ → Equiv.Perm (QueryReg V 1 (Bits m) (BitStr I J))) {i : ℕ}
    (h : i ≤ d) : liftP k d P i = liftE k (P i) :=
  if_pos h

omit [Fintype V] [DecidableEq V] in
theorem liftP_of_lt {d : ℕ} (P : ℕ → Equiv.Perm (QueryReg V 1 (Bits m) (BitStr I J))) {i : ℕ}
    (h : d < i) : liftP k d P i = 1 :=
  if_neg (by omega)

/-- **Two expanded coherent runs with permutations carried between the steps**: for a
trace-preserving core algorithm `A` and Kraus maps `K'` on its registers (trace preserving) whose
step `i` read after `P i` is `A`'s step `i` followed by `P (i + 1)` on the matrices supported on
`S i` (`h1`), `A`'s steps carrying the supports (`h2`), the carried permutations keeping the query
pair (`hQ`), `P 0 = 1`, `P (depth + 1) = 1`, supports that read only the work register and the
query input (`hSwx`) and an initial state supported on `S 0`: the expanded coherent runs of
`A.withStep' K'` and of `A` have the same law. -/
theorem simLaw_expandAdv_transport {O : Type} (A : Alg (Bits m) (BitStr I J) O)
    (hA : A.TracePreserving) {R' : Type} [Fintype R']
    (K' : Fin (A.depth + 1) → KrausMap R' (QueryReg A.V 1 (Bits m) (BitStr I J))
      (QueryReg A.V 1 (Bits m) (BitStr I J)))
    (hK' : (A.withStep' K').TracePreserving)
    (P : ℕ → Equiv.Perm (QueryReg A.V 1 (Bits m) (BitStr I J)))
    (S : ℕ → Set (QueryReg A.V 1 (Bits m) (BitStr I J))) (hP0 : P 0 = 1)
    (hPd : P (A.depth + 1) = 1)
    (h1 : ∀ (i : Fin (A.depth + 1)) ρ, Supp (S i) ρ →
      K' i (ρ.submatrix (P i).symm (P i).symm) =
        (A.step i ρ).submatrix (P (i + 1)).symm (P (i + 1)).symm)
    (h2 : ∀ (i : Fin (A.depth + 1)) ρ, Supp (S i) ρ → Supp (S (i + 1)) (A.step i ρ))
    (hQ : ∀ i < A.depth, QueryPairFix (P (i + 1)))
    (hSwx : ∀ i < A.depth, ∀ p p' : QueryReg A.V 1 (Bits m) (BitStr I J), p.1 = p'.1 →
      (p.2 0).1 = (p'.2 0).1 → p ∈ S (i + 1) → p' ∈ S (i + 1))
    (hinit : Supp (S 0) A.init.mat) (g : Option O → C) :
    simLaw e (expandAdv e E k ((A.withStep' K').toQueryAlgCoh.mapOut g)) =
      simLaw e (expandAdv e E k (A.toQueryAlgCoh.mapOut g)) := by
  classical
  have hrun := densityRun_transport e (t := A.depth + k)
    (expKraus e E k K' fun v => g (some (A.out v)))
    (expKraus e E k A.step fun v => g (some (A.out v)))
    (liftP k A.depth P) (liftSup k A.depth S)
    (by rw [liftP_of_le k P (Nat.zero_le _), hP0, liftE_one])
    (fun i ρ hρ => ?_) (fun i ρ hρ => ?_) (fun i => ?_) (fun i b' b hb hbS => ?_)
    ((A.init.mat ⊗ₖ Matrix.single (fresh (X := Bits m) (Y := BitStr I J) k) (fresh k)
      (1 : ℂ)).submatrix (registerSplit k A.V) (registerSplit k A.V)) ?_ (A.depth + k) le_rfl
  · ext T
    rw [simLaw_expandCoh_eq e E k _ hK' g T, simLaw_expandCoh_eq e E k A hA g T]
    refine Finset.sum_congr rfl fun y _ => ?_
    have hy := congrFun (congrFun hrun.1 y) y
    rw [liftP_of_lt k P (show A.depth < A.depth + k + 1 by omega)] at hy
    exact congrArg (fun z => _ * ENNReal.ofReal (RCLike.re z)) hy
  · -- h1 on the expansion's registers
    obtain ⟨i, hi⟩ := i
    unfold expKraus
    split_ifs with ha hb
    · replace ha : i < A.depth := ha
      rw [KrausMap.optionSome_apply, KrausMap.optionSome_apply]
      change liftKraus k (K' ⟨i, by omega⟩)
          (ρ.submatrix (liftP k A.depth P i).symm (liftP k A.depth P i).symm) =
        (liftKraus k (A.step ⟨i, by omega⟩) ρ).submatrix (liftP k A.depth P (i + 1)).symm
          (liftP k A.depth P (i + 1)).symm
      rw [liftP_of_le k P (by omega), liftP_of_le k P (by omega)]
      have hρ' : Supp (liftS k (S i)) ρ := by
        have h := hρ
        simp only [liftSup, show i ≤ A.depth by omega, if_true] at h
        exact h
      exact liftKraus_transport k (h1 ⟨i, by omega⟩) ρ hρ'
    · replace hb : i = A.depth := hb
      subst hb
      rw [KrausMap.optionSome_apply, KrausMap.optionSome_apply, KrausMap.permConj_apply,
        KrausMap.permConj_apply]
      simp only [Equiv.Perm.one_symm, Equiv.Perm.coe_one, Matrix.submatrix_id_id, liftP,
        le_refl, if_true, show ¬ (A.depth + 1 ≤ A.depth) by omega, if_false]
      have hρ' : Supp (liftS k (S A.depth)) ρ := by
        have h := hρ
        simp only [liftSup, le_refl, if_true] at h
        exact h
      have h1d := h1 (Fin.last A.depth)
      simp only [Fin.val_last, hPd] at h1d
      have := liftKraus_transport k h1d ρ hρ'
      rw [liftE_one] at this
      simp only [Equiv.Perm.one_symm, Equiv.Perm.coe_one, Matrix.submatrix_id_id] at this ⊢
      rw [this]
    · replace ha : ¬ i < A.depth := ha
      replace hb : ¬ i = A.depth := hb
      rw [KrausMap.optionNone_apply, KrausMap.optionNone_apply,
        liftP_of_lt k P (show A.depth < i by omega),
        liftP_of_lt k P (show A.depth < i + 1 by omega)]
      simp only [Equiv.Perm.one_symm, Equiv.Perm.coe_one, Matrix.submatrix_id_id]
  · -- h2 on the expansion's registers
    obtain ⟨i, hi⟩ := i
    unfold expKraus
    split_ifs with ha hb
    · replace ha : i < A.depth := ha
      rw [KrausMap.optionSome_apply]
      have hρ' : Supp (liftS k (S i)) ρ := by
        have h := hρ
        simp only [liftSup, show i ≤ A.depth by omega, if_true] at h
        exact h
      have := liftKraus_supp k (h2 ⟨i, by omega⟩) ρ hρ'
      simp only [liftSup, show i + 1 ≤ A.depth by omega, if_true]
      exact this
    · replace hb : i = A.depth := hb
      simp only [liftSup, show ¬ (i + 1 ≤ A.depth) by omega, if_false]
      exact fun _ _ _ => ⟨trivial, trivial⟩
    · replace ha : ¬ i < A.depth := ha
      simp only [liftSup, show ¬ (i + 1 ≤ A.depth) by omega, if_false]
      exact fun _ _ _ => ⟨trivial, trivial⟩
  · -- the carried permutations keep the query pair
    by_cases hid : i + 1 ≤ A.depth
    · rw [liftP_of_le k P hid]
      exact queryPairFix_liftE k (hQ i (by omega))
    · rw [liftP_of_lt k P (by omega)]
      exact ⟨fun _ => 1, fun _ => rfl⟩
  · -- the query keeps the supports
    by_cases hid : i + 1 ≤ A.depth
    · simp only [liftSup, hid, if_true, liftS, Set.mem_setOf_eq] at hbS ⊢
      have hw := simQueryKernel_work e hb
      have hx := simQueryKernel_qIn e hb
      exact hSwx i (by omega) _ _ (by
        change b.1.1.1 = b'.1.1.1
        rw [hw]) hx.symm hbS
    · simp only [liftSup, hid, if_false]
      trivial
  · -- the initial state
    intro a b hab
    have hab' : A.init.mat (registerSplit k A.V a).1 (registerSplit k A.V b).1 ≠ 0 := by
      intro h0
      apply hab
      simp [Matrix.submatrix_apply, Matrix.kroneckerMap_apply, h0]
    obtain ⟨ha, hb⟩ := hinit _ _ hab'
    simp only [liftSup, Nat.zero_le, if_true, liftS, Set.mem_setOf_eq]
    exact ⟨ha, hb⟩

end GordieHowe.QROM
