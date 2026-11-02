-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.QROM.DensityRunRelabel

@[expose] public section

/-!
# The expanded coherent run along a relabelling of the work register

The law of the measured output and database of the expanded coherent purification of a
trace-preserving core algorithm, read from the density-matrix run of its own Kraus maps and the
expansion (`simLaw_expandCoh_eq`, for every event; `simProb_expandCoh_eq` is the case of the events
of the output).

- `expOut`: the expanded output read from the expansion's registers.
- `simLaw_expandCoh_eq`: the law as a diagonal sum of the density-matrix run.
-/

open Matrix
open scoped BigOperators ENNReal Kronecker

namespace GordieHowe.QROM

open GordieHowe.Quantum ExpandAdv

variable {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] {m : ℕ}
  {B C : Type} (e : BitStr I J ≃ B) (E : Expansion (Bits m) B C) (k : ℕ)

/-- **The expanded output read from the expansion's registers** `b`, with the output `o` of the
work register: the queries recomputed from the output and the answer slots, the answers read
through `e`, and the output. -/
def expOut {W : Type} (o : W → C) (b : ExpansionRegister (X := Bits m) (Y := BitStr I J) k W) :
    BaseGame.Tuple (Bits m) B C k :=
  ⟨fun j => queryAt e E k (o b.1) b.2.2 j, fun j => e (b.2.2 j), o b.1⟩

open Classical in
/-- **The law of the expanded coherent run, read from the run of the core maps**: for a
trace-preserving core algorithm, the probability that the expanded output and the database of the
expanded coherent purification lie in `S` is the diagonal of the density-matrix run of its own
Kraus maps and the expansion, summed over the basis states whose expanded output and database lie
in `S`. -/
theorem simLaw_expandCoh_eq {O : Type} (A : Alg (Bits m) (BitStr I J) O) (hA : A.TracePreserving)
    (g : Option O → C) (S : Set (BaseGame.Tuple (Bits m) B C k × DB (Bits m) B)) :
    simLaw e (expandAdv e E k (A.toQueryAlgCoh.mapOut g)) S =
      ∑ y, (if (expOut e E k (fun v => g (some (A.out v))) y.1.1, slotsDB e y.2) ∈ S then 1
          else 0) *
        ENNReal.ofReal (densityRun e (expKraus e E k A.step fun v => g (some (A.out v)))
          ((A.init.mat ⊗ₖ Matrix.single (fresh (X := Bits m) (Y := BitStr I J) k) (fresh k)
            (1 : ℂ)).submatrix (registerSplit k A.V) (registerSplit k A.V)) (A.depth + k) y y).re := by
  rw [simLaw, MeasureTheory.OuterMeasure.map_apply, bornWeight_apply_eq_sum]
  have h1 : ∀ b : SimRegister (expandAdv e E k (A.toQueryAlgCoh.mapOut g)).W I J m (A.depth + k),
      Set.indicator ((fun b : SimRegister (expandAdv e E k (A.toQueryAlgCoh.mapOut g)).W I J m
          (A.depth + k) => ((expandAdv e E k (A.toQueryAlgCoh.mapOut g)).out b.1.1,
            slotsDB e b.2)) ⁻¹' S)
        (fun b => ‖simState e (expandAdv e E k (A.toQueryAlgCoh.mapOut g)) b‖ₑ ^ 2) b =
      (fun x : SimRegister (ExpansionRegister (X := Bits m) (Y := BitStr I J) k (A.V × Bool)) I J m
          (A.depth + k) => if (expOut e E k (cohOut A g) x.1.1, slotsDB e x.2) ∈ S then
            (1 : ℝ≥0∞) else 0)
          (simAncSplit (expandCohDilation A g e E k).equiv b).1 *
        ‖simState e (expandAdv e E k (A.toQueryAlgCoh.mapOut g)) b‖ₑ ^ 2 := fun b => by
    simp only [Set.indicator, Set.mem_preimage]
    split_ifs with h2 h3 h3
    · rw [one_mul]
    · exact absurd h2 h3
    · exact absurd h3 h2
    · rw [zero_mul]
  simp_rw [h1]
  rw [sum_born_eq_sum_reduce (simAncSplit (expandCohDilation A g e E k).equiv) _
    (fun x => if (expOut e E k (cohOut A g) x.1.1, slotsDB e x.2) ∈ S then (1 : ℝ≥0∞) else 0),
    show simState e (expandAdv e E k (A.toQueryAlgCoh.mapOut g)) =
      simStage e (expandAdv e E k (A.toQueryAlgCoh.mapOut g)) (A.depth + k) from rfl,
    reduce_simStage_expandAdv_toQueryAlgCoh e A g e E k le_rfl,
    densityRun_expandCoh_eq_liftMat e e E k A g hA le_rfl, sum_diag_liftMat_single]
  rfl

/-! ### Kraus maps along a permutation, as predicates -/

namespace KrausRel

variable {R ι : Type*} [Fintype R] [Fintype ι] [DecidableEq ι]

/-- **Two Kraus maps agree along `π` on the columns in `S`**: `K'.op r (π a) (π b) = K.op r a b`
for `b ∈ S`. -/
def OpRel (π : Equiv.Perm ι) (S : Set ι) (K K' : KrausMap R ι ι) : Prop :=
  ∀ r a b, b ∈ S → K'.op r (π a) (π b) = K.op r a b

/-- **A Kraus map keeps `S`**: on the columns in `S`, its nonzero rows are in `S`. -/
def Keeps (S : Set ι) (K : KrausMap R ι ι) : Prop :=
  ∀ r a b, b ∈ S → K.op r a b ≠ 0 → a ∈ S

/-- `permConj` with basis permutations that commute with `π`, the first keeping `S`. -/
theorem OpRel.permConj {π : Equiv.Perm ι} {S : Set ι} {K K' : KrausMap R ι ι} (h : OpRel π S K K')
    {σ τ : Equiv.Perm ι} (hσ : ∀ b, σ (π b) = π (σ b)) (hτ : ∀ a, τ.symm (π a) = π (τ.symm a))
    (hσS : ∀ b ∈ S, σ b ∈ S) : OpRel π S (K.permConj σ τ) (K'.permConj σ τ) := fun r a b hb => by
  change (K'.op r).submatrix τ.symm σ (π a) (π b) = (K.op r).submatrix τ.symm σ a b
  simp only [Matrix.submatrix_apply, hσ, hτ]
  exact h r _ _ (hσS b hb)

theorem Keeps.permConj {S : Set ι} {K : KrausMap R ι ι} (h : Keeps S K) {σ τ : Equiv.Perm ι}
    (hσS : ∀ b ∈ S, σ b ∈ S) (hτS : ∀ a, τ.symm a ∈ S → a ∈ S) : Keeps S (K.permConj σ τ) :=
  fun r a b hb hne => hτS a (h r _ _ (hσS b hb) hne)

theorem OpRel.optionSome {π : Equiv.Perm ι} {S : Set ι} {K K' : KrausMap R ι ι}
    (h : OpRel π S K K') : OpRel π S K.optionSome K'.optionSome := fun r a b hb => by
  cases r with
  | none => rfl
  | some r => exact h r a b hb

theorem Keeps.optionSome {S : Set ι} {K : KrausMap R ι ι} (h : Keeps S K) :
    Keeps S K.optionSome := fun r a b hb hne => by
  cases r with
  | none => exact absurd rfl hne
  | some r => exact h r a b hb hne

/-- The identity agrees with itself along every permutation. -/
theorem opRel_identity (π : Equiv.Perm ι) (S : Set ι) :
    OpRel π S (KrausMap.identity ι) (KrausMap.identity ι) := fun _ a b _ => by
  change (1 : Matrix ι ι ℂ) (π a) (π b) = (1 : Matrix ι ι ℂ) a b
  simp only [Matrix.one_apply, π.injective.eq_iff]

theorem keeps_identity (S : Set ι) : Keeps S (KrausMap.identity ι) := fun _ a b hb hne => by
  change (1 : Matrix ι ι ℂ) a b ≠ 0 at hne
  by_cases h : a = b
  · exact h ▸ hb
  · exact absurd (Matrix.one_apply_ne h) hne

theorem OpRel.optionNone {π : Equiv.Perm ι} {S : Set ι} {K K' : KrausMap Unit ι ι}
    (h : OpRel π S K K') (R' : Type*) [Fintype R'] :
    OpRel π S (K.optionNone R') (K'.optionNone R') := fun r a b hb => by
  cases r with
  | none => exact h () a b hb
  | some r => rfl

theorem Keeps.optionNone {S : Set ι} {K : KrausMap Unit ι ι} (h : Keeps S K) (R' : Type*)
    [Fintype R'] : Keeps S (K.optionNone R') := fun r a b hb hne => by
  cases r with
  | none => exact h () a b hb hne
  | some r => exact absurd rfl hne

end KrausRel

/-! ### The expansion's Kraus maps along a permutation of the work register -/

section ExpLift

open KrausRel

variable {V R : Type} [Fintype V] [DecidableEq V] [Fintype R] (τ : Equiv.Perm V) (S : Set V)

omit [Fintype V] [DecidableEq V] in
/-- **A permutation of the work register on the expansion's basis.** -/
def expWorkPerm : Equiv.Perm (ExpansionRegister (X := Bits m) (Y := BitStr I J) k V) :=
  τ.prodCongr (Equiv.refl _)

omit [Fintype V] [DecidableEq V] in
/-- `τ` on the query registers of the work register `V`. -/
abbrev queryWorkPerm : Equiv.Perm (QueryReg V 1 (Bits m) (BitStr I J)) :=
  τ.prodCongr (Equiv.refl _)

omit [Fintype V] [DecidableEq V] in
/-- `τ` on the expansion's basis. -/
abbrev expBasisPerm : Equiv.Perm (ExpBasis (X := Bits m) (Y := BitStr I J) k V) :=
  (expWorkPerm k τ).prodCongr (Equiv.refl _)

variable {τ}

omit [Fintype V] [DecidableEq V] in
theorem registerSplit_expBasisPerm (b : ExpBasis (X := Bits m) (Y := BitStr I J) k V) :
    registerSplit k V (expBasisPerm k τ b) =
      (queryWorkPerm (m := m) (I := I) (J := J) τ (registerSplit k V b).1, (registerSplit k V b).2) :=
  rfl

omit [Fintype V] [DecidableEq V] in
/-- **The expansion's classical steps commute with a permutation of the work register** that the
output does not read. -/
theorem expPerm_expBasisPerm {o : V → C} (ho : ∀ v, o (τ v) = o v) (j : ℕ)
    (b : ExpBasis (X := Bits m) (Y := BitStr I J) k V) :
    expPerm e E k o j (expBasisPerm k τ b) = expBasisPerm k τ (expPerm e E k o j b) := by
  obtain ⟨⟨w, s, a⟩, q⟩ := b
  cases j with
  | zero =>
    simp only [expPerm, Equiv.trans_apply]
    simp only [stashPerm, movePerm, Equiv.coe_fn_mk, expBasisPerm, expWorkPerm,
      Equiv.prodCongr_apply, Equiv.coe_refl, Prod.map, id, ho]
  | succ j =>
    simp only [expPerm, Equiv.trans_apply]
    unfold recordPerm
    split_ifs
    · simp only [Equiv.trans_apply, addAnsPerm, subAnsPerm, movePerm, Equiv.coe_fn_mk,
        expBasisPerm, expWorkPerm, Equiv.prodCongr_apply, Equiv.coe_refl, Prod.map, id, ho]
    · simp only [Equiv.Perm.coe_one, id, movePerm, Equiv.coe_fn_mk, expBasisPerm, expWorkPerm,
        Equiv.prodCongr_apply, Equiv.coe_refl, Prod.map, ho]

omit [Fintype V] [DecidableEq V] in
theorem expPerm_symm_expBasisPerm {o : V → C} (ho : ∀ v, o (τ v) = o v) (j : ℕ)
    (b : ExpBasis (X := Bits m) (Y := BitStr I J) k V) :
    (expPerm e E k o j).symm (expBasisPerm k τ b) =
      expBasisPerm k τ ((expPerm e E k o j).symm b) := by
  apply (expPerm e E k o j).injective
  rw [Equiv.apply_symm_apply, expPerm_expBasisPerm e E k ho, Equiv.apply_symm_apply]

/-- **`liftKraus` along a permutation of the work register.** -/
theorem OpRel.liftKraus {K K' : KrausMap R (QueryReg V 1 (Bits m) (BitStr I J))
      (QueryReg V 1 (Bits m) (BitStr I J))}
    (h : OpRel (queryWorkPerm τ) {p | p.1 ∈ S} K K') :
    OpRel (expBasisPerm k τ) {b | b.1.1 ∈ S} (ExpandAdv.liftKraus k K) (ExpandAdv.liftKraus k K') :=
  fun r a b hb => by
    change (K'.op r ⊗ₖ (1 : Matrix _ _ ℂ)) (registerSplit k V (expBasisPerm k τ a))
      (registerSplit k V (expBasisPerm k τ b)) =
      (K.op r ⊗ₖ (1 : Matrix _ _ ℂ)) (registerSplit k V a) (registerSplit k V b)
    rw [registerSplit_expBasisPerm, registerSplit_expBasisPerm, Matrix.kroneckerMap_apply,
      Matrix.kroneckerMap_apply, h r _ _ hb]

theorem Keeps.liftKraus {K : KrausMap R (QueryReg V 1 (Bits m) (BitStr I J))
      (QueryReg V 1 (Bits m) (BitStr I J))} (h : Keeps {p | p.1 ∈ S} K) :
    Keeps {b : ExpBasis (X := Bits m) (Y := BitStr I J) k V | b.1.1 ∈ S} (ExpandAdv.liftKraus k K) :=
  fun r a b hb hne => by
    change (K.op r ⊗ₖ (1 : Matrix _ _ ℂ)) (registerSplit k V a) (registerSplit k V b) ≠ 0 at hne
    rw [Matrix.kroneckerMap_apply] at hne
    exact h r _ _ hb (left_ne_zero_of_mul hne)

/-- **The expansion's Kraus maps along a permutation of the work register** that the output does
not read, from the core maps along it. -/
theorem opRel_expKraus {t : ℕ}
    {K K' : Fin (t + 1) → KrausMap R (QueryReg V 1 (Bits m) (BitStr I J))
      (QueryReg V 1 (Bits m) (BitStr I J))}
    (h : ∀ i, OpRel (queryWorkPerm τ) {p | p.1 ∈ S} (K i) (K' i)) {o : V → C}
    (ho : ∀ v, o (τ v) = o v) (i : Fin (t + k + 1)) :
    OpRel (expBasisPerm k τ) {b | b.1.1 ∈ S} (expKraus e E k K o i) (expKraus e E k K' o i) := by
  unfold expKraus
  split_ifs with h1 h2
  · exact OpRel.optionSome (OpRel.liftKraus k S (h _))
  · exact OpRel.optionSome (OpRel.permConj (OpRel.liftKraus k S (h _)) (σ := 1)
      (τ := expPerm e E k o 0) (fun _ => rfl) (expPerm_symm_expBasisPerm e E k ho 0)
      (fun b hb => hb))
  · exact OpRel.optionNone (OpRel.permConj (opRel_identity (expBasisPerm k τ) {b | b.1.1 ∈ S}) (σ := 1)
      (τ := expPerm e E k o (i - t)) (fun _ => rfl) (expPerm_symm_expBasisPerm e E k ho _)
      (fun b hb => hb)) R

theorem keeps_expKraus {t : ℕ}
    {K : Fin (t + 1) → KrausMap R (QueryReg V 1 (Bits m) (BitStr I J))
      (QueryReg V 1 (Bits m) (BitStr I J))}
    (h : ∀ i, Keeps {p | p.1 ∈ S} (K i)) (o : V → C) (i : Fin (t + k + 1)) :
    Keeps {b : ExpBasis (X := Bits m) (Y := BitStr I J) k V | b.1.1 ∈ S} (expKraus e E k K o i) := by
  have hτS : ∀ j a, ((expPerm e E k o j).symm a).1.1 ∈ S → a.1.1 ∈ S := fun j a ha => by
    rwa [expPerm_symm_fst_fst] at ha
  unfold expKraus
  split_ifs with h1 h2
  · exact Keeps.optionSome (Keeps.liftKraus k S (h _))
  · exact Keeps.optionSome (Keeps.permConj (Keeps.liftKraus k S (h _)) (σ := 1)
      (τ := expPerm e E k o 0) (fun b hb => hb) (hτS 0))
  · exact Keeps.optionNone (Keeps.permConj (keeps_identity _) (σ := 1)
      (τ := expPerm e E k o (i - t)) (fun b hb => hb) (hτS _)) R

end ExpLift

/-! ### The expanded coherent run along a relabelling of the work register -/

/-- **A core algorithm with its Kraus maps read after basis permutations**: Kraus map `k` applied
after `σ k` (`KrausMap.permConj`), the same registers, Kraus index, depth, initial state and
output. -/
abbrev _root_.GordieHowe.Quantum.Alg.precomp {X Y O : Type} [Fintype X] [Fintype Y] [DecidableEq X]
    [DecidableEq Y] (A : Alg X Y O) (σ : Fin (A.depth + 1) → Equiv.Perm (QueryReg A.V 1 X Y)) :
    Alg X Y O where
  V := A.V
  depth := A.depth
  R := A.R
  init := A.init
  step k := (A.step k).permConj (σ k) (Equiv.refl _)
  out := A.out

theorem _root_.GordieHowe.Quantum.Alg.tracePreserving_precomp {X Y O : Type} [Fintype X]
    [Fintype Y] [DecidableEq X] [DecidableEq Y] {A : Alg X Y O} (hA : A.TracePreserving)
    (σ : Fin (A.depth + 1) → Equiv.Perm (QueryReg A.V 1 X Y)) : (A.precomp σ).TracePreserving :=
  fun k => by
    show ∑ r, (((A.step k).op r).submatrix (Equiv.refl _).symm (σ k))ᴴ *
      ((A.step k).op r).submatrix (Equiv.refl _).symm (σ k) = 1
    have h : ∑ r, (((A.step k).op r).submatrix (Equiv.refl _).symm (σ k))ᴴ *
        ((A.step k).op r).submatrix (Equiv.refl _).symm (σ k) =
        (∑ r, ((A.step k).op r)ᴴ * (A.step k).op r).submatrix (σ k) (σ k) := by
      rw [Matrix.submatrix_sum]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv]
    rw [h, hA k, Matrix.submatrix_one_equiv]

open KrausRel in
open Classical in
/-- **Two expanded coherent runs along a permutation of the work register**: for a
trace-preserving core algorithm `A`, an initial state `ρ` supported on the work registers in `S`,
basis permutations `σ` such that Kraus map `i` read after `σ i` agrees with Kraus map `i` along
`τ` on `S` (`hop`), Kraus maps that keep `S` (`hK`), `A`'s initial state the relabelled `ρ` and an
output that `τ` does not change, the expanded coherent run of `A` started at `ρ` and that of
`A.precomp σ` have the same law. -/
theorem simLaw_expandCoh_relabel {O : Type} (A : Alg (Bits m) (BitStr I J) O)
    (hA : A.TracePreserving) (ρ : MState (QueryReg A.V 1 (Bits m) (BitStr I J)))
    (σ : Fin (A.depth + 1) → Equiv.Perm (QueryReg A.V 1 (Bits m) (BitStr I J)))
    (g : Option O → C) (τ : Equiv.Perm A.V) (S : Set A.V)
    (hop : ∀ i, OpRel (queryWorkPerm τ) {p | p.1 ∈ S} (A.step i)
      ((A.step i).permConj (σ i) (Equiv.refl _)))
    (hK : ∀ i, Keeps {p | p.1 ∈ S} (A.step i))
    (hρ : ∀ a b, ρ.mat a b ≠ 0 → a.1 ∈ S ∧ b.1 ∈ S)
    (hinit : A.init.mat = ρ.mat.submatrix (queryWorkPerm τ).symm (queryWorkPerm τ).symm)
    (ho : ∀ v, g (some (A.out (τ v))) = g (some (A.out v))) :
    simLaw e (expandAdv e E k (({ A with init := ρ } : Alg (Bits m) (BitStr I J) O).toQueryAlgCoh.mapOut
        g)) = simLaw e (expandAdv e E k ((A.precomp σ).toQueryAlgCoh.mapOut g)) := by
  ext T
  rw [simLaw_expandCoh_eq e E k ({ A with init := ρ } : Alg (Bits m) (BitStr I J) O)
      (show ({ A with init := ρ } : Alg (Bits m) (BitStr I J) O).TracePreserving from hA) g T,
    simLaw_expandCoh_eq e E k _ (Alg.tracePreserving_precomp hA σ) g T]
  have hD := (densityRun_relabel e (expWorkPerm k τ) {v | v.1 ∈ S}
    (expKraus e E k A.step fun v => g (some (A.out v)))
    (expKraus e E k (A.precomp σ).step fun v => g (some (A.out v)))
    (fun i => opRel_expKraus e E k S (fun i' => hop i') ho i)
    (fun i => keeps_expKraus e E k S (fun i' => hK i') _ i)
    ((ρ.mat ⊗ₖ Matrix.single (fresh (X := Bits m) (Y := BitStr I J) k) (fresh k) (1 : ℂ)).submatrix
      (registerSplit k A.V) (registerSplit k A.V))
    (fun a b h => by
      have h' := left_ne_zero_of_mul (show ρ.mat (registerSplit k A.V a).1
        (registerSplit k A.V b).1 * _ ≠ 0 from h)
      exact hρ _ _ h') (A.depth + k)).1
  have hi : (A.init.mat ⊗ₖ Matrix.single (fresh (X := Bits m) (Y := BitStr I J) k) (fresh k)
      (1 : ℂ)).submatrix (registerSplit k A.V) (registerSplit k A.V) =
      ((ρ.mat ⊗ₖ Matrix.single (fresh (X := Bits m) (Y := BitStr I J) k) (fresh k)
        (1 : ℂ)).submatrix (registerSplit k A.V) (registerSplit k A.V)).submatrix
        ((expWorkPerm k τ).prodCongr (Equiv.refl _)).symm
        ((expWorkPerm k τ).prodCongr (Equiv.refl _)).symm := by
    rw [hinit]
    ext a b
    rfl
  dsimp only [Alg.precomp]
  erw [hi, hD]
  refine Fintype.sum_equiv (simWorkPerm (expWorkPerm k τ)) _ _ fun y => ?_
  simp only [Matrix.submatrix_apply, Equiv.symm_apply_apply]
  congr 2
  show _ = ((expOut e E k (fun v => g (some (A.out v))) (τ y.1.1.1, y.1.1.2), slotsDB e y.2) ∈ T)
  simp only [expOut, ho]

end GordieHowe.QROM

/-! ### A dilated algorithm with its steps read after basis permutations of the system -/

namespace GordieHowe.Quantum

namespace QueryAlg

variable {X Y O : Type} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y] {t : ℕ}
  {Q : QueryAlg X Y t O} {V Anc R : Type} [Fintype V] [DecidableEq V] [Fintype Anc] [Fintype R]
  (D : Q.Dilation V Anc R) (π : Fin (t + 1) → Equiv.Perm (QueryReg V 1 X Y))

/-- `π i` on the work register through the split of the dilation. -/
def precompPerm (i : Fin (t + 1)) : Equiv.Perm (QueryReg Q.W 1 X Y) :=
  ((queryAncSplit D.equiv).trans ((π i).prodCongr (Equiv.refl Anc))).trans
    (queryAncSplit D.equiv).symm

/-- **The dilated algorithm with step `i` read after `π i`** on the system. -/
noncomputable def precompSteps : QueryAlg X Y t O :=
  { Q with step := fun i => (permOp (precompPerm D π i)).trans (Q.step i) }

theorem permOp_precompPerm_relabel (i : Fin (t + 1)) (φ : QState (QueryReg V 1 X Y × Anc)) :
    permOp (precompPerm D π i) (relabel (queryAncSplit D.equiv).symm φ) =
      relabel (queryAncSplit D.equiv).symm (permOp ((π i).prodCongr (Equiv.refl Anc)) φ) := by
  ext p
  simp only [relabel_apply, permOp_apply, precompPerm, Equiv.symm_trans_apply, Equiv.symm_symm,
    Equiv.apply_symm_apply]

/-- **The precomposed algorithm is a dilation** with the Kraus maps read after `π`. -/
noncomputable def Dilation.precomp : (precompSteps D π).Dilation V Anc R where
  equiv := D.equiv
  kraus i := (D.kraus i).permConj (π i) 1
  clean := D.clean
  init := D.init
  reduce_init := D.reduce_init
  supported_init := D.supported_init
  supported_step i φ hφ := by
    change Supported _ (relabel (queryAncSplit D.equiv) (Q.step i (permOp (precompPerm D π i)
      (relabel (queryAncSplit D.equiv).symm φ))))
    rw [permOp_precompPerm_relabel]
    exact D.supported_step i _ (hφ.permOp fun _ hr => hr)
  cross_step i φ χ hφ hχ := by
    change cross (relabel (queryAncSplit D.equiv) (Q.step i (permOp (precompPerm D π i)
        (relabel (queryAncSplit D.equiv).symm φ))))
      (relabel (queryAncSplit D.equiv) (Q.step i (permOp (precompPerm D π i)
        (relabel (queryAncSplit D.equiv).symm χ)))) = _
    rw [permOp_precompPerm_relabel, permOp_precompPerm_relabel,
      D.cross_step i _ _ (hφ.permOp fun _ hr => hr) (hχ.permOp fun _ hr => hr),
      cross_permOp_prodCongr, KrausMap.permConj_apply]
    simp only [Equiv.Perm.one_symm, Equiv.Perm.coe_one, Matrix.submatrix_id_id]

end QueryAlg

end GordieHowe.Quantum

namespace GordieHowe.QROM

open GordieHowe.Quantum ExpandAdv

variable {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] {m : ℕ}
  {B C : Type} (e : BitStr I J ≃ B)

open Classical in
/-- **The law of a dilated algorithm, read from its density-matrix run**, when the output is read
from the system: the probability that the output and database lie in `T` is the diagonal of the
density-matrix run of the dilation's Kraus maps, summed over the basis states whose output and
database lie in `T`. -/
theorem simLaw_dilation {O : Type} {t : ℕ} {Q : QueryAlg (Bits m) (BitStr I J) t O}
    {V Anc R : Type} [Fintype V] [DecidableEq V] [Fintype Anc] [Fintype R]
    (D : Q.Dilation V Anc R) (f : V → O) (hf : ∀ w, Q.out w = f (D.equiv w).1)
    (T : Set (O × DB (Bits m) B)) :
    simLaw e Q T = ∑ x : SimRegister V I J m t, (if (f x.1.1, slotsDB e x.2) ∈ T then 1 else 0) *
      ENNReal.ofReal (densityRun e D.kraus D.init t x x).re := by
  rw [simLaw, MeasureTheory.OuterMeasure.map_apply, bornWeight_apply_eq_sum]
  have h1 : ∀ b : SimRegister Q.W I J m t,
      Set.indicator ((fun b : SimRegister Q.W I J m t => (Q.out b.1.1, slotsDB e b.2)) ⁻¹' T)
        (fun b => ‖simState e Q b‖ₑ ^ 2) b =
      (fun x : SimRegister V I J m t => if (f x.1.1, slotsDB e x.2) ∈ T then (1 : ℝ≥0∞) else 0)
          (simAncSplit D.equiv b).1 * ‖simState e Q b‖ₑ ^ 2 := fun b => by
    simp only [Set.indicator, Set.mem_preimage, hf]
    split_ifs with h2 h3 h3
    · rw [one_mul]
    · exact absurd h2 h3
    · exact absurd h3 h2
    · rw [zero_mul]
  simp_rw [h1]
  rw [sum_born_eq_sum_reduce (simAncSplit D.equiv) _
    (fun x => if (f x.1.1, slotsDB e x.2) ∈ T then (1 : ℝ≥0∞) else 0),
    reduce_simState_dilation e D]

/-! ### The expanded coherent run with its steps read after permutations of the core registers -/

/-- **A left basis permutation carried through a lift at `|z⟩⟨z|`**: a permutation that keeps the
`Z` coordinate and acts as `π` at `z`, applied first. -/
theorem _root_.GordieHowe.Quantum.KrausMap.LiftsAt.permConj_left_single {R R' ι ι' Z : Type*}
    [Fintype R] [Fintype R'] [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']
    [DecidableEq Z] {E : ι' ≃ ι × Z} {z : Z} {K' : KrausMap R' ι' ι'} {K : KrausMap R ι ι}
    (h : K'.LiftsAt E (Matrix.single z z 1) K) {π' : Equiv.Perm ι'} {π : Equiv.Perm ι}
    (hz : ∀ x, (E (π'.symm x)).2 = (E x).2)
    (hπ : ∀ y, π'.symm (E.symm (y, z)) = E.symm (π.symm y, z)) :
    (K'.permConj π' 1).LiftsAt E (Matrix.single z z 1) (K.permConj π 1) := fun ρ => by
  rw [KrausMap.permConj_apply, KrausMap.permConj_apply]
  simp only [Equiv.Perm.one_symm, Equiv.Perm.coe_one, Matrix.submatrix_id_id]
  rw [GordieHowe.Quantum.KrausMap.liftMat_single_submatrix E z hz hπ, h]

variable (E : Expansion (Bits m) B C) (k : ℕ)

section CohPrecomp

variable {O : Type} (A : Alg (Bits m) (BitStr I J) O) (g : Option O → C)
  (σ : Fin (A.depth + 1) → Equiv.Perm A.V)

/-- `σ` on the expansion's basis, the identity after `A`'s steps. -/
def expPrecompPerm (i : Fin (A.depth + k + 1)) :
    Equiv.Perm (ExpBasis (X := Bits m) (Y := BitStr I J) k A.V) :=
  if h : (i : ℕ) < A.depth + 1 then expBasisPerm k (σ ⟨i, h⟩) else 1

/-- `σ` on the system of the expanded coherent purification, the identity after `A`'s steps. -/
def cohPrecompPerm (i : Fin (A.depth + k + 1)) :
    Equiv.Perm (QueryReg (ExpansionRegister (X := Bits m) (Y := BitStr I J) k (A.V × Bool)) 1
      (Bits m) (BitStr I J)) :=
  if h : (i : ℕ) < A.depth + 1 then expBasisPerm k ((σ ⟨i, h⟩).prodCongr (Equiv.refl Bool)) else 1

theorem liftKraus_permConj_op {V R : Type} [Fintype V] [DecidableEq V] [Fintype R]
    (K : KrausMap R (QueryReg V 1 (Bits m) (BitStr I J)) (QueryReg V 1 (Bits m) (BitStr I J)))
    (s : Equiv.Perm V) (r : R) (a b : ExpBasis (X := Bits m) (Y := BitStr I J) k V) :
    (ExpandAdv.liftKraus k (K.permConj (queryWorkPerm s) (Equiv.refl _))).op r a b =
      (ExpandAdv.liftKraus k K).op r a (expBasisPerm k s b) := by
  change ((K.op r).submatrix (Equiv.refl _).symm (queryWorkPerm s) ⊗ₖ (1 : Matrix _ _ ℂ))
      (registerSplit k V a) (registerSplit k V b) =
    (K.op r ⊗ₖ (1 : Matrix _ _ ℂ)) (registerSplit k V a) (registerSplit k V (expBasisPerm k s b))
  rw [registerSplit_expBasisPerm, Matrix.kroneckerMap_apply, Matrix.kroneckerMap_apply]
  rfl

/-- **The expansion's Kraus maps of `A.precomp σ` are those of `A` read after `σ`.** -/
theorem expKraus_precomp_op (o : A.V → C) (i : Fin (A.depth + k + 1)) :
    (expKraus e E k (A.precomp fun j => queryWorkPerm (σ j)).step o i).op =
      ((expKraus e E k A.step o i).permConj (expPrecompPerm k A σ i) 1).op := by
  funext r
  ext a b
  change _ = (expKraus e E k A.step o i).op r a (expPrecompPerm k A σ i b)
  obtain ⟨i, hi⟩ := i
  unfold expKraus expPrecompPerm
  dsimp only [Alg.precomp]
  by_cases h1 : i < A.depth
  · rw [dif_pos h1, dif_pos h1, dif_pos (show i < A.depth + 1 by omega)]
    cases r with
    | none => rfl
    | some r => exact liftKraus_permConj_op k (A.step _) (σ _) r a b
  · rw [dif_neg h1, dif_neg h1]
    by_cases h2 : i = A.depth
    · rw [if_pos h2, if_pos h2, dif_pos (show i < A.depth + 1 by omega)]
      cases r with
      | none => rfl
      | some r =>
        have hl : (⟨i, by omega⟩ : Fin (A.depth + 1)) = Fin.last A.depth := Fin.ext h2
        change (ExpandAdv.liftKraus k ((A.step (Fin.last A.depth)).permConj
            (queryWorkPerm (σ (Fin.last A.depth))) (Equiv.refl _))).op r
            ((expPerm e E k o 0).symm a) b = (ExpandAdv.liftKraus k (A.step (Fin.last A.depth))).op r
            ((expPerm e E k o 0).symm a) (expBasisPerm k (σ ⟨i, by omega⟩) b)
        rw [hl]
        exact liftKraus_permConj_op k _ _ r _ b
    · rw [if_neg h2, if_neg h2, dif_neg (show ¬ i < A.depth + 1 by omega)]
      rfl

theorem expKraus_precomp_apply (o : A.V → C) (i : Fin (A.depth + k + 1))
    (ρ : Matrix (ExpBasis (X := Bits m) (Y := BitStr I J) k A.V)
      (ExpBasis (X := Bits m) (Y := BitStr I J) k A.V) ℂ) :
    (expKraus e E k (A.precomp fun j => queryWorkPerm (σ j)).step o i) ρ =
      ((expKraus e E k A.step o i).permConj (expPrecompPerm k A σ i) 1) ρ := by
  simp only [KrausMap.apply, expKraus_precomp_op e E k A σ o i]

/-- **The coherent run's Kraus maps lift `A`'s at flag `false`** (the steps of the proof of
`densityRun_expandCoh_eq_liftMat`). -/
theorem liftsAt_expandCoh (hA : A.TracePreserving) (i : Fin (A.depth + k + 1)) :
    ((expandCohDilation A g e E k).kraus i).LiftsAt
      (QueryAlg.queryAncSplit (expAncSplit k (Equiv.refl (A.V × Bool))))
      (Matrix.single false false 1) (expKraus e E k A.step (fun v => g (some (A.out v))) i) := by
  have hz : ∀ (j : ℕ) (x : ExpBasis (X := Bits m) (Y := BitStr I J) k (A.V × Bool)),
      (QueryAlg.queryAncSplit (expAncSplit k (Equiv.refl (A.V × Bool)))
        ((expPerm e E k (cohOut A g) j).symm x)).2 =
      (QueryAlg.queryAncSplit (expAncSplit k (Equiv.refl (A.V × Bool))) x).2 := fun j x => by
    simp only [QueryAlg.queryAncSplit_apply, expAncSplit, Equiv.coe_fn_mk, Equiv.refl_apply,
      expPerm_symm_fst_fst]
  show (expKraus e E k (A.cohDilation.mapOut g).kraus (cohOut A g) i).LiftsAt _ _
    (expKraus e E k A.step (fun v => g (some (A.out v))) i)
  unfold expKraus
  split_ifs with h1 h2
  · exact (ExpandAdv.LiftsAt.liftKraus k (liftsAt_complete _ (hA _))).optionSome
  · exact ((ExpandAdv.LiftsAt.liftKraus k (liftsAt_complete _ (hA _))).permConj_single
      (hz 0) (perm_symm_slice _ false (expPerm_cohOut_slice e E k A g 0))).optionSome
  · exact (((KrausMap.lifts_identity _).liftsAt _).permConj_single (hz _)
      (perm_symm_slice _ false (expPerm_cohOut_slice e E k A g _))).optionNone _ _

/-- **The flag stays `false` in the precomposed expanded coherent run**: its density-matrix run is
the run of the Kraus maps of `A.precomp σ` and the expansion, with the halting flag `false`. -/
theorem densityRun_precomp_liftMat (hA : A.TracePreserving) {n : ℕ} (hn : n ≤ A.depth + k) :
    densityRun e ((expandCohDilation A g e E k).precomp (cohPrecompPerm k A σ)).kraus
        (expandCohDilation A g e E k).init n =
      liftMat (simAncSplit (expAncSplit k (Equiv.refl (A.V × Bool))))
        (densityRun e (expKraus e E k (A.precomp fun j => queryWorkPerm (σ j)).step
          fun v => g (some (A.out v)))
          ((A.init.mat ⊗ₖ Matrix.single (fresh (X := Bits m) (Y := BitStr I J) k) (fresh k)
            (1 : ℂ)).submatrix (registerSplit k A.V) (registerSplit k A.V)) n)
        (Matrix.single false false 1) := by
  have hinit : (expandCohDilation A g e E k).init =
      liftMat (QueryAlg.queryAncSplit (expAncSplit k (Equiv.refl (A.V × Bool))))
        ((A.init.mat ⊗ₖ Matrix.single (fresh (X := Bits m) (Y := BitStr I J) k) (fresh k)
          (1 : ℂ)).submatrix (registerSplit k A.V) (registerSplit k A.V))
        (Matrix.single false false 1) := by
    rw [← expInit_liftMat]
    have hc : (A.cohDilation.mapOut g).init =
        liftMat (QueryAlg.queryAncSplit (Equiv.refl (A.V × Bool))) A.init.mat
          (Matrix.single false false 1) := by
      ext x y
      rfl
    rw [← hc]
    ext x y
    rfl
  rw [hinit]
  refine densityRun_liftMat e (expAncSplit k (Equiv.refl _)) _ _ _ (n := A.depth + k + 1)
    (fun i hi => ?_) _ n (by omega)
  have hl := (liftsAt_expandCoh e E k A g hA i).permConj_left_single
    (π' := cohPrecompPerm k A σ i) (π := expPrecompPerm k A σ i)
    (fun x => by
      unfold cohPrecompPerm
      split_ifs <;> rfl)
    (fun y => by
      unfold cohPrecompPerm expPrecompPerm
      split_ifs <;> rfl)
  intro ρ
  rw [show ((expandCohDilation A g e E k).precomp (cohPrecompPerm k A σ)).kraus i =
    ((expandCohDilation A g e E k).kraus i).permConj (cohPrecompPerm k A σ i) 1 from rfl, hl ρ]
  congr 1
  exact (expKraus_precomp_apply e E k A σ _ i ρ).symm

open Classical in
/-- **The expanded coherent run with its steps read after `σ` has the law of the expanded coherent
run of `A.precomp σ`**, for a trace-preserving `A`. -/
theorem simLaw_precompSteps_expandCoh (hA : A.TracePreserving) :
    simLaw e (QueryAlg.precompSteps (expandCohDilation A g e E k) (cohPrecompPerm k A σ)) =
      simLaw e (expandAdv e E k ((A.precomp fun j => queryWorkPerm (σ j)).toQueryAlgCoh.mapOut g)) := by
  ext T
  rw [simLaw_dilation e ((expandCohDilation A g e E k).precomp (cohPrecompPerm k A σ))
      (expOut e E k (cohOut A g)) (fun w => rfl) T,
    simLaw_expandCoh_eq e E k _ (Alg.tracePreserving_precomp hA _) g T]
  change ∑ x, _ * ENNReal.ofReal (densityRun e
    ((expandCohDilation A g e E k).precomp (cohPrecompPerm k A σ)).kraus
    (expandCohDilation A g e E k).init (A.depth + k) x x).re = _
  rw [densityRun_precomp_liftMat e E k A g σ hA le_rfl]
  erw [sum_diag_liftMat_single]
  rfl

/-- **A permutation of the core register on the registers of the expanded coherent
purification.** -/
def cohLiftAt (s : Equiv.Perm A.V)
    (p : QueryReg (expandAdv e E k (A.toQueryAlgCoh.mapOut g)).W 1 (Bits m) (BitStr I J)) :
    QueryReg (expandAdv e E k (A.toQueryAlgCoh.mapOut g)).W 1 (Bits m) (BitStr I J) :=
  ((((s p.1.1.1.1, p.1.1.1.2), p.1.1.2), p.1.2), p.2)

/-- **The precomposed steps of the expanded coherent purification act on the core register**:
`σ i` on the core part of the work register for a step of `A`. -/
theorem precompPerm_cohPrecompPerm_of_lt {i : Fin (A.depth + k + 1)} (h : (i : ℕ) < A.depth + 1)
    (p : QueryReg (expandAdv e E k (A.toQueryAlgCoh.mapOut g)).W 1 (Bits m) (BitStr I J)) :
    QueryAlg.precompPerm (expandCohDilation A g e E k) (cohPrecompPerm k A σ) i p =
      cohLiftAt e E k A g (σ ⟨i, h⟩) p := by
  unfold QueryAlg.precompPerm cohPrecompPerm
  rw [dif_pos h]
  rfl

/-- The precomposed steps after `A`'s steps are the identity. -/
theorem precompPerm_cohPrecompPerm_of_ge {i : Fin (A.depth + k + 1)} (h : ¬ (i : ℕ) < A.depth + 1)
    (p : QueryReg (expandAdv e E k (A.toQueryAlgCoh.mapOut g)).W 1 (Bits m) (BitStr I J)) :
    QueryAlg.precompPerm (expandCohDilation A g e E k) (cohPrecompPerm k A σ) i p = p := by
  unfold QueryAlg.precompPerm cohPrecompPerm
  rw [dif_neg h]
  simp

/-- The split of the expanded coherent purification's registers. -/
theorem queryAncSplit_expandCohDilation
    (p : QueryReg (expandAdv e E k (A.toQueryAlgCoh.mapOut g)).W 1 (Bits m) (BitStr I J)) :
    QueryAlg.queryAncSplit (expandCohDilation A g e E k).equiv p = (((p.1.1.1, p.1.2), p.2), p.1.1.2) :=
  rfl

theorem queryAncSplit_expandCohDilation_symm
    (q : QueryReg (ExpansionRegister (X := Bits m) (Y := BitStr I J) k (A.V × Bool)) 1 (Bits m)
      (BitStr I J) × A.HaltAnc) :
    (QueryAlg.queryAncSplit (expandCohDilation A g e E k).equiv).symm q =
      (((q.1.1.1, q.2), q.1.1.2), q.1.2) :=
  rfl

/-- **A family of permutations given by `σ` on the core part of the work register** (the identity
after `A`'s steps) is the precomposition family of `σ`. -/
theorem cohPrecompPerm_eq_of
    (π' : Fin (A.depth + k + 1) →
      Equiv.Perm (QueryReg (expandAdv e E k (A.toQueryAlgCoh.mapOut g)).W 1 (Bits m) (BitStr I J)))
    (h1 : ∀ (i : Fin (A.depth + k + 1)) p (h : (i : ℕ) < A.depth + 1),
      π' i p = cohLiftAt e E k A g (σ ⟨i, h⟩) p)
    (h2 : ∀ (i : Fin (A.depth + k + 1)) p, ¬ (i : ℕ) < A.depth + 1 → π' i p = p)
    (i : Fin (A.depth + k + 1)) :
    π' i = QueryAlg.precompPerm (expandCohDilation A g e E k) (cohPrecompPerm k A σ) i := by
  refine Equiv.ext fun p => ?_
  by_cases h : (i : ℕ) < A.depth + 1
  · rw [h1 i p h, precompPerm_cohPrecompPerm_of_lt e E k A g σ h p]
  · rw [h2 i p h, precompPerm_cohPrecompPerm_of_ge e E k A g σ h p]

/-- **A run of the expanded coherent purification with its steps read after `σ`, given by the
formula of its writes**, has the law of the expanded coherent run of `A.precomp σ`: for steps
`S i = U_i ∘ π' i` with `π' i` acting as `σ i` on the core part of the work register (the identity
after `A`'s steps), for a trace-preserving `A`. -/
theorem simLaw_steps_expandCoh (hA : A.TracePreserving)
    (π' : Fin (A.depth + k + 1) →
      Equiv.Perm (QueryReg (expandAdv e E k (A.toQueryAlgCoh.mapOut g)).W 1 (Bits m) (BitStr I J)))
    (h1 : ∀ (i : Fin (A.depth + k + 1)) p (h : (i : ℕ) < A.depth + 1),
      π' i p = cohLiftAt e E k A g (σ ⟨i, h⟩) p)
    (h2 : ∀ (i : Fin (A.depth + k + 1)) p, ¬ (i : ℕ) < A.depth + 1 → π' i p = p)
    (S : Fin (A.depth + k + 1) →
      QState (QueryReg (expandAdv e E k (A.toQueryAlgCoh.mapOut g)).W 1 (Bits m) (BitStr I J)) ≃ₗᵢ[ℂ]
        QState (QueryReg (expandAdv e E k (A.toQueryAlgCoh.mapOut g)).W 1 (Bits m) (BitStr I J)))
    (hS : ∀ i, S i = (permOp (π' i)).trans ((expandAdv e E k (A.toQueryAlgCoh.mapOut g)).step i)) :
    simLaw e { expandAdv e E k (A.toQueryAlgCoh.mapOut g) with step := S } =
      simLaw e (expandAdv e E k ((A.precomp fun j => queryWorkPerm (σ j)).toQueryAlgCoh.mapOut g)) := by
  have hπ : π' = QueryAlg.precompPerm (expandCohDilation A g e E k) (cohPrecompPerm k A σ) :=
    funext (cohPrecompPerm_eq_of e E k A g σ π' h1 h2)
  have hS' : S = (QueryAlg.precompSteps (expandCohDilation A g e E k) (cohPrecompPerm k A σ)).step := by
    funext i
    rw [hS i, hπ]
    rfl
  rw [hS', ← simLaw_precompSteps_expandCoh e E k A g σ hA]
  rfl

open Classical in
/-- **The law of a dilated algorithm with its steps read after `σ`**, for a dilation with the
Kraus maps and initial state of the expanded coherent purification of `A` and its output: that of
the expanded coherent run of `A.precomp σ`, for a trace-preserving `A`. -/
theorem simLaw_precompSteps_of_dilation (hA : A.TracePreserving)
    {Q : QueryAlg (Bits m) (BitStr I J) (A.depth + k) (BaseGame.Tuple (Bits m) B C k)}
    (D : Q.Dilation (ExpansionRegister (X := Bits m) (Y := BitStr I J) k (A.V × Bool)) A.HaltAnc
      (Option (A.R ⊕ Bool)))
    (hk : ∀ i, D.kraus i = (expandCohDilation A g e E k).kraus i)
    (hinit : D.init = (expandCohDilation A g e E k).init)
    (hout : ∀ w, Q.out w = expOut e E k (cohOut A g) (D.equiv w).1) :
    simLaw e (QueryAlg.precompSteps D (cohPrecompPerm k A σ)) =
      simLaw e (expandAdv e E k ((A.precomp fun j => queryWorkPerm (σ j)).toQueryAlgCoh.mapOut g)) := by
  ext T
  rw [simLaw_dilation e (D.precomp (cohPrecompPerm k A σ)) (expOut e E k (cohOut A g)) hout T,
    simLaw_expandCoh_eq e E k _ (Alg.tracePreserving_precomp hA _) g T]
  have hD : densityRun e (D.precomp (cohPrecompPerm k A σ)).kraus
      (D.precomp (cohPrecompPerm k A σ)).init (A.depth + k) =
      densityRun e ((expandCohDilation A g e E k).precomp (cohPrecompPerm k A σ)).kraus
        (expandCohDilation A g e E k).init (A.depth + k) := by
    change densityRun e (fun i => (D.kraus i).permConj (cohPrecompPerm k A σ i) 1) D.init _ =
      densityRun e (fun i => ((expandCohDilation A g e E k).kraus i).permConj
        (cohPrecompPerm k A σ i) 1) _ _
    simp only [hk, hinit]
  rw [hD, densityRun_precomp_liftMat e E k A g σ hA le_rfl]
  erw [sum_diag_liftMat_single]
  rfl

/-- **The dilated algorithm with given steps, read after `σ`**, has the law of the expanded
coherent run of `A.precomp σ`: for steps `S i = U_i ∘ π i` (`hS`) with `π` the precomposition of
`σ` through the dilation. -/
theorem simLaw_steps_of_dilation (hA : A.TracePreserving)
    {Q : QueryAlg (Bits m) (BitStr I J) (A.depth + k) (BaseGame.Tuple (Bits m) B C k)}
    (D : Q.Dilation (ExpansionRegister (X := Bits m) (Y := BitStr I J) k (A.V × Bool)) A.HaltAnc
      (Option (A.R ⊕ Bool)))
    (hk : ∀ i, D.kraus i = (expandCohDilation A g e E k).kraus i)
    (hinit : D.init = (expandCohDilation A g e E k).init)
    (hout : ∀ w, Q.out w = expOut e E k (cohOut A g) (D.equiv w).1)
    (S : Fin (A.depth + k + 1) →
      QState (QueryReg Q.W 1 (Bits m) (BitStr I J)) ≃ₗᵢ[ℂ] QState (QueryReg Q.W 1 (Bits m) (BitStr I J)))
    (hS : ∀ i, S i = (permOp (QueryAlg.precompPerm D (cohPrecompPerm k A σ) i)).trans (Q.step i)) :
    simLaw e { Q with step := S } =
      simLaw e (expandAdv e E k ((A.precomp fun j => queryWorkPerm (σ j)).toQueryAlgCoh.mapOut g)) := by
  have h : S = (QueryAlg.precompSteps D (cohPrecompPerm k A σ)).step := funext hS
  rw [← simLaw_precompSteps_of_dilation e E k A g σ hA D hk hinit hout, h]
  rfl

/-- **The expanded coherent run with its steps read after `σ`, on registers equal to its own**:
for a query algorithm `Q` equal to the expanded coherent purification (`hQ`) and steps
`S i = U_i ∘ π i` with `π` the precomposition of `σ` through the dilation carried along `hQ`, the
law is that of the expanded coherent run of `A.precomp σ`. -/
theorem simLaw_steps_transport (hA : A.TracePreserving)
    (Q : QueryAlg (Bits m) (BitStr I J) (A.depth + k) (BaseGame.Tuple (Bits m) B C k))
    (hQ : expandAdv e E k (A.toQueryAlgCoh.mapOut g) = Q)
    (S : Fin (A.depth + k + 1) →
      QState (QueryReg Q.W 1 (Bits m) (BitStr I J)) ≃ₗᵢ[ℂ] QState (QueryReg Q.W 1 (Bits m) (BitStr I J)))
    (hS : ∀ i, S i = (permOp (QueryAlg.precompPerm
      (hQ ▸ expandCohDilation A g e E k :
        Q.Dilation (ExpansionRegister (X := Bits m) (Y := BitStr I J) k (A.V × Bool)) A.HaltAnc
          (Option (A.R ⊕ Bool))) (cohPrecompPerm k A σ) i)).trans (Q.step i)) :
    simLaw e { Q with step := S } =
      simLaw e (expandAdv e E k ((A.precomp fun j => queryWorkPerm (σ j)).toQueryAlgCoh.mapOut g)) := by
  subst hQ
  exact simLaw_steps_of_dilation e E k A g σ hA (expandCohDilation A g e E k) (fun _ => rfl) rfl
    (fun _ => rfl) S hS

/-- **The precomposed steps carried along an equation of the registers** act as `σ i` on the core
part of the work register (`cohLiftAt`), for a step of `A`. -/
theorem precompPerm_transport_lt
    (Q : QueryAlg (Bits m) (BitStr I J) (A.depth + k) (BaseGame.Tuple (Bits m) B C k))
    (hQ : expandAdv e E k (A.toQueryAlgCoh.mapOut g) = Q) {i : Fin (A.depth + k + 1)}
    (h : (i : ℕ) < A.depth + 1) (p : QueryReg Q.W 1 (Bits m) (BitStr I J)) :
    QueryAlg.precompPerm (hQ ▸ expandCohDilation A g e E k :
        Q.Dilation (ExpansionRegister (X := Bits m) (Y := BitStr I J) k (A.V × Bool)) A.HaltAnc
          (Option (A.R ⊕ Bool))) (cohPrecompPerm k A σ) i p =
      hQ ▸ cohLiftAt e E k A g (σ ⟨i, h⟩) (hQ.symm ▸ p) := by
  subst hQ
  exact precompPerm_cohPrecompPerm_of_lt e E k A g σ h p

/-- The precomposed steps carried along an equation of the registers are the identity after the
steps of `A`. -/
theorem precompPerm_transport_ge
    (Q : QueryAlg (Bits m) (BitStr I J) (A.depth + k) (BaseGame.Tuple (Bits m) B C k))
    (hQ : expandAdv e E k (A.toQueryAlgCoh.mapOut g) = Q) {i : Fin (A.depth + k + 1)}
    (h : ¬ (i : ℕ) < A.depth + 1) (p : QueryReg Q.W 1 (Bits m) (BitStr I J)) :
    QueryAlg.precompPerm (hQ ▸ expandCohDilation A g e E k :
        Q.Dilation (ExpansionRegister (X := Bits m) (Y := BitStr I J) k (A.V × Bool)) A.HaltAnc
          (Option (A.R ⊕ Bool))) (cohPrecompPerm k A σ) i p = p := by
  subst hQ
  exact precompPerm_cohPrecompPerm_of_ge e E k A g σ h p

end CohPrecomp

end GordieHowe.QROM
