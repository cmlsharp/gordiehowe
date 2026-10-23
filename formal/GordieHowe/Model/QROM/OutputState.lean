-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.QROM.OutputLaw
public import GordieHowe.Model.QROM.ExpandAdv
public import GordieHowe.Model.Quantum.Core.Dilation

@[expose] public section

/-!
# The adversary's state in `Sim*(A)`: CMS19 Lemma 3.3 for density matrices

**CMS19 Lemma 3.3** (Chiesa–Manohar–Spooner, ePrint 2019/834, p. 17; Zha19 Lemma 4): "For any
quantum oracle algorithm A making at most t queries, Tr_D(|Sim*(A)⟩⟨Sim*(A)|) =
(1/(2^n)^(2^m)) ∑_h A_h A_h*". `GordieHowe/Model/QROM/OutputLaw.lean` uses it for the measured output only; this
file proves it for the whole register of `A`, and carries it through the expansion of CMS19
Proposition 8.11, so that the quantum state the adversary keeps is compared, not only its
measured output.

- `ketBra v`, `blockOn T`, `ptraceAlong σ`: the projector `|v⟩⟨v|`, the block `P_T M P_T` of a matrix
  on a set `T` of basis states (the subnormalized state after a projective measurement gave an
  outcome in `T`), and the partial trace along a split `κ ≃ ι × A` of a basis.
- `reduce_kernelMap_idLeft`: a matrix with orthonormal columns that acts on the second register
  only, the same on every branch of the first, leaves the reduced density matrix of the first
  register unchanged.
- `QueryAlg.realState`: the state `(1/|Y^X|) ∑_h |A^h⟩⟨A^h|` of `A`'s register against a uniformly
  random oracle.
- `reduce_simState`: CMS19 Lemma 3.3. The proof follows `simLaw_out`: `|Sim*(A)⟩` is the
  Fourier-basis run with its oracle register compressed (`simState_eq_compress`); compression
  (`reduce_compress`, `reduce_dbFun`) and the Fourier transform of the oracle register
  (`reduce_fourier`) act on the oracle register only, by matrices with orthonormal columns on the
  states the run reaches; the purified run has the slices `A^h` (`reduce_purStage`).
- `ExpandAdv.ptraceAlong_blockOn_final`, `ExpandAdv.ptraceAlong_blockOn_realState`: the expanded
  algorithm (`expandAdv`) at an outcome that fixes `A`'s output, with the expansion's registers
  traced out, leaves `A`'s register in the state `A^h` at that outcome. The expansion writes
  classical data computed from `A`'s output into its registers, so the identity needs the
  outcome to fix that output: across different outputs the expansion's registers differ, and the
  partial trace removes the coherence between them, as measuring the output does.
-/

open Finset

namespace GordieHowe.Quantum

/-! ### Projectors, blocks and partial traces -/

section Operators

variable {ι κ A : Type*} [Fintype ι] [Fintype κ] [Fintype A]

/-- **The projector onto a vector** `|v⟩⟨v|`: the matrix `v i * conj (v j)`, the density matrix of
a unit vector (HU25 p. 245, "the pure state |ψ⟩ corresponds to the density operator |ψ⟩⟨ψ|"). -/
def ketBra (v : QState ι) : Matrix ι ι ℂ :=
  Matrix.of fun i j => v i * star (v j)

@[simp]
theorem ketBra_apply (v : QState ι) (i j : ι) : ketBra v i j = v i * star (v j) :=
  rfl

open Classical in
/-- **The block of a matrix on a set of basis states**: `P M P` for the projector `P` onto the span
of the basis states in `T`. For a density matrix it is the subnormalized state after the
computational-basis measurement of the indicator of `T` gave the outcome "in `T`". -/
noncomputable def blockOn (T : Set ι) : Matrix ι ι ℂ →ₗ[ℂ] Matrix ι ι ℂ where
  toFun M := Matrix.of fun i j => if i ∈ T ∧ j ∈ T then M i j else 0
  map_add' M N := by
    ext i j
    simp only [Matrix.of_apply, Matrix.add_apply]
    split_ifs <;> simp
  map_smul' c M := by
    ext i j
    simp only [Matrix.of_apply, Matrix.smul_apply, RingHom.id_apply]
    split_ifs <;> simp

omit [Fintype ι] in
open Classical in
theorem blockOn_apply (T : Set ι) (M : Matrix ι ι ℂ) (i j : ι) :
    blockOn T M i j = if i ∈ T ∧ j ∈ T then M i j else 0 :=
  rfl

/-- The block of `|v⟩⟨v|` on `T` is the projector onto the masked vector. -/
theorem blockOn_ketBra (T : Set ι) (v : QState ι) : blockOn T (ketBra v) = ketBra (mask T v) := by
  ext i j
  rw [blockOn_apply, ketBra_apply, ketBra_apply, mask_apply, mask_apply]
  by_cases hi : i ∈ T <;> by_cases hj : j ∈ T <;> simp [hi, hj]

/-- **The partial trace along a split of the basis** `σ : κ ≃ ι × A`: the trace over the register
`A`, `(ptraceAlong σ M) i j = ∑ a, M (σ.symm (i, a)) (σ.symm (j, a))`. -/
def ptraceAlong (σ : κ ≃ ι × A) : Matrix κ κ ℂ →ₗ[ℂ] Matrix ι ι ℂ where
  toFun M := Matrix.of fun i j => ∑ a, M (σ.symm (i, a)) (σ.symm (j, a))
  map_add' M N := by
    ext i j
    simp [Finset.sum_add_distrib]
  map_smul' c M := by
    ext i j
    simp [Finset.mul_sum]

omit [Fintype ι] [Fintype κ] in
theorem ptraceAlong_apply (σ : κ ≃ ι × A) (M : Matrix κ κ ℂ) (i j : ι) :
    ptraceAlong σ M i j = ∑ a, M (σ.symm (i, a)) (σ.symm (j, a)) :=
  rfl

open Classical in
/-- The trace of a block is the sum of the diagonal over the block's basis states. -/
theorem trace_blockOn (T : Set ι) (M : Matrix ι ι ℂ) :
    (blockOn T M).trace = ∑ i, T.indicator (fun i => M i i) i := by
  simp only [Matrix.trace, Matrix.diag_apply, blockOn_apply, Set.indicator_apply, and_self]

/-- **The blocks on the fibres of a map sum to the block on the preimage**, in trace. -/
theorem sum_trace_blockOn_fiber {K : Type*} (f : ι → K) (s : Finset K) (M : Matrix ι ι ℂ) :
    ∑ x ∈ s, (blockOn {i | f i = x} M).trace = (blockOn {i | f i ∈ s} M).trace := by
  classical
  simp only [trace_blockOn]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Set.indicator_apply, Set.mem_setOf_eq]
  rw [Finset.sum_ite_eq]

omit [Fintype ι] in
/-- A block of a matrix with a nonnegative diagonal has a nonnegative diagonal. -/
theorem re_blockOn_apply_self_nonneg (T : Set ι) {M : Matrix ι ι ℂ} (h : ∀ i, 0 ≤ (M i i).re)
    (i : ι) : 0 ≤ (blockOn T M i i).re := by
  classical
  rw [blockOn_apply]
  split_ifs
  · exact h i
  · simp

/-- The partial trace keeps the trace. -/
theorem trace_ptraceAlong (σ : κ ≃ ι × A) (M : Matrix κ κ ℂ) : (ptraceAlong σ M).trace = M.trace := by
  simp only [Matrix.trace, Matrix.diag_apply, ptraceAlong_apply]
  rw [← Fintype.sum_prod_type' (f := fun i a => M (σ.symm (i, a)) (σ.symm (i, a)))]
  exact Equiv.sum_comp σ.symm (fun k => M k k)

omit [Fintype ι] [Fintype κ] in
/-- A partial trace of a matrix with a nonnegative diagonal has a nonnegative diagonal. -/
theorem re_ptraceAlong_apply_self_nonneg (σ : κ ≃ ι × A) {M : Matrix κ κ ℂ}
    (h : ∀ k, 0 ≤ (M k k).re) (i : ι) : 0 ≤ (ptraceAlong σ M i i).re := by
  rw [ptraceAlong_apply, Complex.re_sum]
  exact Finset.sum_nonneg fun a _ => h _

/-- A reduced state has a nonnegative diagonal. -/
theorem re_reduce_apply_self_nonneg (ψ : QState (ι × A)) (i : ι) : 0 ≤ (reduce ψ i i).re := by
  simp only [reduce_apply, Complex.re_sum, RCLike.star_def, Complex.mul_conj, Complex.ofReal_re]
  exact Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _

/-- **The block of a reduced state, in trace, is the Born weight** of the basis states whose first
component lies in the block. -/
theorem ofReal_re_trace_blockOn_reduce (T : Set ι) (ψ : QState (ι × A)) :
    ENNReal.ofReal (blockOn T (reduce ψ)).trace.re = bornWeight ψ {p | p.1 ∈ T} := by
  classical
  have hz : ∀ z : ℂ, (z * star z).re = ‖z‖ ^ 2 := fun z => by
    rw [RCLike.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rfl
  rw [trace_blockOn, bornWeight_apply_eq_sum, Fintype.sum_prod_type, Complex.re_sum,
    ENNReal.ofReal_sum_of_nonneg fun i _ => ?_]
  · refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hi : i ∈ T
    · simp only [Set.indicator_of_mem hi, Set.indicator_of_mem (show (i, _) ∈ {p : ι × A | p.1 ∈ T}
        from hi), reduce_apply, Complex.re_sum, hz]
      rw [ENNReal.ofReal_sum_of_nonneg fun _ _ => sq_nonneg _]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [← ofReal_norm, ENNReal.ofReal_pow (norm_nonneg _)]
    · simp only [Set.indicator_of_notMem hi, Set.indicator_of_notMem
        (show (i, _) ∉ {p : ι × A | p.1 ∈ T} from hi), Complex.zero_re, ENNReal.ofReal_zero,
        Finset.sum_const_zero]
  · by_cases hi : i ∈ T
    · rw [Set.indicator_of_mem hi]
      simp only [reduce_apply, Complex.re_sum, hz]
      exact Finset.sum_nonneg fun _ _ => sq_nonneg _
    · rw [Set.indicator_of_notMem hi, Complex.zero_re]

/-- **The partial trace of a vector carried into a larger basis**: if `w` is `v` placed at the
basis states `φ i`, whose second component under `σ` is `α i`, and zero elsewhere, then tracing
out the second register gives `|v⟩⟨v|`, provided `α` is constant on the support of `v`. (Where `α`
differs, the partial trace removes the coherence between the two basis states.) -/
theorem ptraceAlong_ketBra_of_embed (σ : κ ≃ ι × A) {φ : ι → κ} {α : ι → A}
    (hσ : ∀ i, σ (φ i) = (i, α i)) {w : QState κ} {v : QState ι} (hw : ∀ i, w (φ i) = v i)
    (hw0 : ∀ b, (∀ i, φ i ≠ b) → w b = 0) (hα : ∀ i j, v i ≠ 0 → v j ≠ 0 → α i = α j) :
    ptraceAlong σ (ketBra w) = ketBra v := by
  classical
  have key : ∀ i a, w (σ.symm (i, a)) = if a = α i then v i else 0 := by
    intro i a
    by_cases ha : a = α i
    · subst ha
      rw [if_pos rfl, ← hσ i, Equiv.symm_apply_apply, hw]
    · rw [if_neg ha]
      refine hw0 _ fun i' hi' => ha ?_
      have h := congrArg σ hi'
      rw [Equiv.apply_symm_apply, hσ, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rfl
  ext i j
  rw [ptraceAlong_apply, ketBra_apply]
  simp only [ketBra_apply, key]
  rw [Finset.sum_eq_single (α i) (fun a _ ha => by simp [ha]) (by simp), if_pos rfl]
  by_cases hvi : v i = 0
  · simp [hvi]
  by_cases hvj : v j = 0
  · simp [hvj]
  rw [if_pos (hα i j hvi hvj)]

end Operators

/-! ### Reduced density matrices under maps on the second register -/

section Reduce

variable {R ι κ : Type*} [Fintype R] [Fintype ι] [Fintype κ] [DecidableEq R] [DecidableEq ι]

/-- **A matrix on the second register with orthonormal columns leaves the reduced density matrix
of the first unchanged**: for `K` with orthonormal columns on `S`, applied to the second register
on every branch of the first (`idLeft fun _ => K`), and a vector supported where the second
register lies in `S`. -/
theorem reduce_kernelMap_idLeft {K : κ → ι → ℂ} {S : Set ι}
    (hK : ∀ l ∈ S, ∀ l' ∈ S, ∑ a, star (K a l) * K a l' = if l = l' then 1 else 0)
    {v : QState (R × ι)} (hv : Supported {b | b.2 ∈ S} v) :
    reduce (kernelMap (idLeft fun _ => K) v) = reduce v := by
  ext i j
  simp only [reduce_apply, kernelMap_idLeft_apply]
  have hK' : ∀ l ∈ S, ∀ l' ∈ S, ∑ a, K a l * star (K a l') = if l = l' then 1 else 0 :=
    fun l hl l' hl' => by
      rw [show ∑ a, K a l * star (K a l') = ∑ a, star (K a l') * K a l from
        sum_congr rfl fun _ _ => mul_comm _ _, hK l' hl' l hl]
      exact if_congr eq_comm rfl rfl
  calc ∑ a, (∑ l, K a l * v (i, l)) * star (∑ l', K a l' * v (j, l'))
      = ∑ a, ∑ l, ∑ l', v (i, l) * star (v (j, l')) * (K a l * star (K a l')) := by
        refine sum_congr rfl fun a _ => ?_
        rw [star_sum, Finset.sum_mul_sum]
        refine sum_congr rfl fun l _ => sum_congr rfl fun l' _ => ?_
        rw [star_mul']
        ring
    _ = ∑ l, ∑ l', v (i, l) * star (v (j, l')) * ∑ a, K a l * star (K a l') := by
        rw [Finset.sum_comm]
        refine sum_congr rfl fun l _ => ?_
        rw [Finset.sum_comm]
        refine sum_congr rfl fun l' _ => ?_
        rw [Finset.mul_sum]
    _ = ∑ l, v (i, l) * star (v (j, l)) := by
        refine sum_congr rfl fun l _ => ?_
        by_cases hl : l ∈ S
        · rw [Finset.sum_eq_single l (fun l' _ hl' => ?_) (by simp), hK' l hl l hl, if_pos rfl,
            mul_one]
          by_cases hl'' : l' ∈ S
          · rw [hK' l hl l' hl'', if_neg (Ne.symm hl'), mul_zero]
          · rw [show v (j, l') = 0 from hv (j, l') hl'', star_zero, mul_zero, zero_mul]
        · have h0 : v (i, l) = 0 := hv (i, l) hl
          simp [h0]

end Reduce

namespace QueryAlg

variable {X Y O : Type} [Fintype X] [Fintype Y] [DecidableEq X] [AddGroup Y] {t : ℕ}
  (A : QueryAlg X Y t O)

/-- **The state of `A`'s register against a uniformly random oracle** (CMS19 Lemma 3.3, p. 17,
right side, "(1/(2^n)^(2^m)) ∑_h A_h A_h*"): the average over `h : X → Y` of `|A^h⟩⟨A^h|`, the
final state before the measurement. -/
noncomputable def realState : Matrix (QueryReg A.W 1 X Y) (QueryReg A.W 1 X Y) ℂ :=
  ∑ h : X → Y, ((Fintype.card (X → Y) : ℂ)⁻¹) • ketBra (A.final h)

end QueryAlg

end GordieHowe.Quantum

open GordieHowe.Quantum

namespace GordieHowe.QROM

variable {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] {m : ℕ}
  {B : Type} [Fintype B] (e : BitStr I J ≃ B) {t : ℕ}

/-! ### CMS19 Lemma 3.3 -/

section Lemma33

variable {W : Type} [Fintype W] [DecidableEq W]

/-- The Fourier transform of the oracle register leaves the reduced state of the other registers
unchanged. -/
theorem reduce_fourier {Q : Type} [Fintype Q] [DecidableEq Q] (v : QState (Q × (Bits m → BitStr I J))) :
    reduce (fourier Q v) = reduce v :=
  reduce_kernelMap_idLeft (S := Set.univ)
    (fun F _ F' _ => piKernel_orthonormal (fun _ => hk_orthonormal) F F')
    (fun _ hb => absurd (Set.mem_univ _) hb)

/-- `dbFun` leaves the reduced state of the adversary's register unchanged. -/
theorem reduce_dbFun (v : QState (PurReg W I J m)) : reduce (dbFun e W v) = reduce v :=
  reduce_kernelMap_idLeft (S := Set.univ)
    (fun F _ F' _ => piKernel_orthonormal (fun _ y y' => fk_orthonormal e y y') F F')
    (fun _ hb => absurd (Set.mem_univ _) hb)

/-- **Compression leaves the reduced state of the adversary's register unchanged**, on vectors
whose Fourier-basis truth tables have at most `t` nonzero entries: there the `t`-slot database
states are the databases written as functions. -/
theorem reduce_compress {v : QState (PurReg W I J m)}
    (hv : Supported {b | b.2 ∈ {F : Bits m → BitStr I J | fourierSize F ≤ t}} v) :
    reduce (compress e t W v) = reduce (dbFun e W v) := by
  classical
  ext r r'
  simp only [reduce_apply]
  have key : ∀ s, compress e t W v (r, s) * star (compress e t W v (r', s)) =
      if IsDBState e s then dbFun e W v (r, fun x => (slotsDB e s).lookup x) *
        star (dbFun e W v (r', fun x => (slotsDB e s).lookup x)) else 0 := by
    intro s
    rw [compress_apply, compress_apply]
    split_ifs <;> simp
  simp_rw [key]
  have hdb : ∀ s : Slots I J m t, (if IsDBState e s then dbFun e W v (r, fun x => (slotsDB e s).lookup x) *
      star (dbFun e W v (r', fun x => (slotsDB e s).lookup x)) else 0) ≠ 0 → IsDBState e s :=
    fun s h => by
      by_contra hn
      exact h (by rw [if_neg hn])
  refine Finset.sum_bij_ne_zero (fun s _ _ => fun x => (slotsDB e s).lookup x)
    (fun _ _ _ => Finset.mem_univ _) ?_ ?_ ?_
  · intro s _ h1 s' _ h2 heq
    have hD : slotsDB e s = slotsDB e s' := Finmap.ext_lookup fun x => congrFun heq x
    rw [← (IsDBState.dbSlots_slotsDB e (hdb s h1)).2, ← (IsDBState.dbSlots_slotsDB e (hdb s' h2)).2,
      hD]
  · intro d _ h
    have hd : dbFun e W v (r, d) ≠ 0 := fun h0 => h (by rw [h0, zero_mul])
    have hsz : (DB.ofFun d).size ≤ t := by
      rw [DB.size_ofFun]
      exact card_isSome_le_of_dbFun e hv hd
    have hl : (fun x => (slotsDB e (dbSlots e t (DB.ofFun d))).lookup x) = d := by
      funext x
      rw [slotsDB_dbSlots e hsz, DB.lookup_ofFun]
    refine ⟨dbSlots e t (DB.ofFun d), Finset.mem_univ _, ?_, hl⟩
    rwa [if_pos (isDBState_dbSlots e hsz), hl]
  · intro s _ h
    rw [if_pos (hdb s h)]

/-- `unifAmp · conj unifAmp = 1/|Y^X|`. -/
theorem unifAmp_mul_star :
    unifAmp I J m * star (unifAmp I J m) = ((Fintype.card (Bits m → BitStr I J) : ℕ) : ℂ)⁻¹ := by
  have hN : (0 : ℝ) ≤ Fintype.card (BitStr I J) := Nat.cast_nonneg _
  rw [unifAmp, invSqrtCard, star_pow, Complex.star_def, Complex.conj_ofReal, ← mul_pow,
    ← Complex.ofReal_mul, ← mul_inv, Real.mul_self_sqrt hN, Fintype.card_fun, Nat.cast_pow]
  push_cast
  simp

variable {O : Type} (A : QueryAlg (Bits m) (BitStr I J) t O)

/-- **The purified run has the slices `A^h`** (Zha19 Lemma 2: "This can be seen by tracing out
the oracle registers"): the reduced state of the purified run on `A`'s register is `A.realState`. -/
theorem reduce_purStage : reduce (purStage A t) = A.realState := by
  ext r r'
  simp only [reduce_apply, QueryAlg.realState, Matrix.sum_apply, Matrix.smul_apply, ketBra_apply,
    purStage_apply, smul_eq_mul]
  refine sum_congr rfl fun h _ => ?_
  rw [star_mul', ← unifAmp_mul_star (I := I) (J := J) (m := m)]
  simp only [QueryAlg.final, OracleAlg.final]
  ring

/-- **CMS19 Lemma 3.3** (p. 17; Zha19 Lemma 4, p. 15): "For any quantum oracle algorithm A making
at most t queries, Tr_D(|Sim*(A)⟩⟨Sim*(A)|) = (1/(2^n)^(2^m)) ∑_h A_h A_h*": the state of `A`'s
register in `Sim*(A)`, with the database register traced out, is the state of `A`'s register
against a uniformly random oracle. -/
theorem reduce_simState [DecidableEq B] : reduce (simState e A) = A.realState := by
  rw [simState_eq_compress, reduce_compress e (supported_fourStage A t), reduce_dbFun,
    ← reduce_fourier (Q := QueryReg A.W 1 (Bits m) (BitStr I J)) (fourStage A t),
    fourier_fourStage, reduce_purStage]

end Lemma33

/-! ### The expanded algorithm leaves `A`'s register in the state `A^h` -/

namespace ExpandAdv

variable {X Y C : Type} [Fintype X] [DecidableEq X] [Inhabited X] [Fintype Y] [DecidableEq Y]
  [AddCommGroup Y] (k : ℕ) (W : Type)

/-- **The expanded algorithm's register split into `𝒜`'s register and the expansion's**: `𝒜`'s
work register together with the stash, which holds `𝒜`'s query register after the run
(`stashPerm`), is `𝒜`'s register `QueryReg W 1 X Y`; the query register and the answer slots are
the rest. -/
def adversarySplit :
    ExpBasis (X := X) (Y := Y) k W ≃ QueryReg W 1 X Y × ((Fin 1 → X × Y) × (Fin k → Y)) where
  toFun b := ((b.1.1, fun _ => b.1.2.1), (b.2, b.1.2.2))
  invFun p := ((p.1.1, p.1.2 0, p.2.2), p.2.1)
  left_inv _ := rfl
  right_inv p := by
    obtain ⟨⟨w, q⟩, q', a⟩ := p
    simp only [Prod.mk.injEq, and_true, true_and]
    exact funext fun i => by rw [Subsingleton.elim i 0]

variable {B : Type} (e : Y ≃ B) (E : Expansion X B C) {k} {t : ℕ}

/-- **At an outcome that fixes `𝒜`'s output, the expanded algorithm leaves `𝒜`'s register in the
state `𝒜^h`** (CMS19 section 8.5.2, p. 43: "B merely extends A with some classical computation
that depends on A's (classical) output"): for an event `P` of the expanded output that holds only
when `𝒜`'s output is `c`, the block of `|B^h⟩⟨B^h|` on `P`, with the query register and the answer
slots traced out, is the projector onto `𝒜^h` masked to the basis states whose expanded output
`E.expand (e ∘ h)` satisfies `P`. -/
theorem ptraceAlong_blockOn_final (𝒜 : QueryAlg X Y t C) (H : X → Y)
    {P : BaseGame.Tuple X B C k → Prop} {c : C} (hP : ∀ τ, P τ → τ.out = c) :
    ptraceAlong (adversarySplit k 𝒜.W)
        (blockOn {r | P ((expandAdv e E k 𝒜).out r.1)} (ketBra ((expandAdv e E k 𝒜).final H))) =
      ketBra (mask {r | P (E.expand (e ∘ H) (𝒜.out r.1))} (𝒜.final H)) := by
  classical
  refine (congrArg _ (blockOn_ketBra _ _)).trans ?_
  set π := expRun e E k 𝒜.out H k with hπ
  have hemb : ∀ b, embed k (𝒜.final H) b =
      𝒜.final H (registerSplit k 𝒜.W b).1 *
        if (registerSplit k 𝒜.W b).2 = fresh k then 1 else 0 := fun b => by
    rw [embed, relabel_apply, Equiv.symm_symm, tensorKet_apply]
  refine ptraceAlong_ketBra_of_embed _
    (φ := fun r => π ((registerSplit k 𝒜.W).symm (r, fresh k)))
    (α := fun r => (fun _ => (queryAt e E k (𝒜.out r.1) (ansUpTo e E k H (𝒜.out r.1) k) k, 0),
      ansUpTo e E k H (𝒜.out r.1) k)) ?_ ?_ ?_ ?_
  · rintro ⟨w, q⟩
    rw [hπ, expRun_apply e E k 𝒜.out H w q k le_rfl]
    simp only [adversarySplit, Equiv.coe_fn_mk, Prod.mk.injEq, and_true, true_and]
    exact funext fun i : Fin 1 => by rw [Subsingleton.elim i 0]
  · rintro ⟨w, q⟩
    have hout := expandAdv_out_expRun e E k 𝒜 H w q
    erw [mask_apply, mask_apply]
    rw [Set.indicator_apply, Set.indicator_apply]
    simp only [Set.mem_ofPred_eq]
    rw [← hπ] at hout
    rw [hout]
    refine if_congr Iff.rfl ?_ rfl
    rw [expandAdv_final, permOp_apply, ← hπ, Equiv.symm_apply_apply, hemb,
      Equiv.apply_symm_apply, if_pos rfl, mul_one]
  · intro b hb
    erw [mask_apply]
    rw [Set.indicator_apply]
    split_ifs
    · rw [expandAdv_final, permOp_apply, ← hπ, hemb]
      split_ifs with h
      · exfalso
        refine hb (registerSplit k 𝒜.W (π.symm b)).1 ?_
        rw [← h, Prod.mk.eta, Equiv.symm_apply_apply, Equiv.apply_symm_apply]
      · simp
    · rfl
  · intro i j hi hj
    have hc : ∀ r, mask {r | P (E.expand (e ∘ H) (𝒜.out r.1))} (𝒜.final H) r ≠ 0 →
        𝒜.out r.1 = c := fun r hr => by
      rw [mask_apply] at hr
      by_contra hn
      exact hr (Set.indicator_of_notMem (s := {r : QueryReg 𝒜.W 1 X Y | P (E.expand (e ∘ H) (𝒜.out r.1))})
        (fun h : P (E.expand (e ∘ H) (𝒜.out r.1)) => hn (hP _ h)) _)
    simp only [hc i hi, hc j hj]

/-- **The expanded algorithm against a random oracle, at an outcome that fixes `𝒜`'s output**:
the block of `(expandAdv e E k 𝒜).realState` on `P`, with the expansion's registers traced out,
is the average over `h` of the projector onto `𝒜^h` masked to `P` of its expanded output. -/
theorem ptraceAlong_blockOn_realState (𝒜 : QueryAlg X Y t C)
    {P : BaseGame.Tuple X B C k → Prop} {c : C} (hP : ∀ τ, P τ → τ.out = c) :
    ptraceAlong (adversarySplit k 𝒜.W)
        (blockOn {r | P ((expandAdv e E k 𝒜).out r.1)} (expandAdv e E k 𝒜).realState) =
      ∑ H : X → Y, ((Fintype.card (X → Y) : ℂ)⁻¹) •
        ketBra (mask {r | P (E.expand (e ∘ H) (𝒜.out r.1))} (𝒜.final H)) := by
  rw [QueryAlg.realState]
  refine (congrArg (ptraceAlong (adversarySplit k 𝒜.W)) (map_sum (blockOn _) _ _)).trans ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun H _ => ?_
  refine (congrArg (ptraceAlong (adversarySplit k 𝒜.W)) (map_smul (blockOn _) _ _)).trans ?_
  rw [map_smul]
  exact congrArg _ (ptraceAlong_blockOn_final e E 𝒜 H hP)

end ExpandAdv

end GordieHowe.QROM
