-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Interactive.TPRun
public import GordieHowe.Model.Quantum.Interactive.TestLift
public import GordieHowe.Model.Quantum.Interactive.PureRun

@[expose] public section

/-!
# Fixed-schedule adversaries as adversaries with run-time kinds

The oracle-test counterexample is a fixed-schedule adversary (`IAlg`); the headlines quantify over
adversaries with run-time kinds (`AdaptiveIAlg`, the query-bounded class `QueryBoundedAdversary`).
This file embeds the first into the second, keeping the law of the output and the oracle, the
final state of the mixed game, trace preservation and the query count.

## The embedding

A kind algorithm `K` with a budget `b` is an adversary with run-time kinds (`KindAlg.toAdaptive`).
Its semantics (`AdaptiveIAlg.toKindAlg`) adds a query counter and projects away a branch that asks
for a query slot after `b` of them. When `K` follows a schedule `sched` along its run
(`KindAlg.Respects`), the counter after the slots below `j` is the number of query slots of `sched`
below `j` on every branch (`cntAt`), so with `b` the number of query slots no branch is projected
away, and the mixed game of `K.toAdaptive b` is that of `K` with the counter placed at its value
(`KindAlg.mgRun_toAdaptive`: the final state, as a matrix placed along `KindAlg.placeCnt`).

- `IAlg.toAdaptive`: a fixed-schedule adversary, through its slot counter (`IAlg.toKindAlg`),
  with a budget of its query slots. `IAlg.realLaw_compose_toAdaptive`: same law of the output and
  the oracle against every challenger; `IAlg.realLaw_composeBothOut_toAdaptive`: same law of all
  composed registers, up to placing the final counter; `IAlg.toAdaptive_tracePreserving`,
  `IAlg.toAdaptive_queries`.

Trace preservation is kept by the embedding (`IAlg.toAdaptive_tracePreserving`); the embedding
into `AdaptiveIAlg` keeps the law for trace-losing steps as well.
-/

open Finset Matrix
open scoped BigOperators ENNReal Kronecker ComplexOrder

namespace GordieHowe.Quantum

namespace KrausMap

variable {R ι : Type*} [Fintype R] [Fintype ι] [DecidableEq ι]

theorem ext_op {κ : Type*} [Fintype κ] {K K' : KrausMap R ι κ} (h : K.op = K'.op) : K = K' := by
  cases K
  cases K'
  cases h
  rfl

/-- `⊗ 1` commutes with conjugation by permutations. -/
theorem tensorId_permConj (K : KrausMap R ι ι) (σ τ : Equiv.Perm ι) (A : Type*) [Fintype A]
    [DecidableEq A] :
    (K.permConj σ τ).tensorId A =
      (K.tensorId A).permConj (σ.prodCongr (Equiv.refl A)) (τ.prodCongr (Equiv.refl A)) :=
  ext_op (funext fun _ => Matrix.ext fun _ _ => rfl)

/-- `⊗ 1` commutes with the projection after a Kraus map. -/
theorem tensorId_restrict (K : KrausMap R ι ι) (p : ι → Bool) (A : Type*) [Fintype A]
    [DecidableEq A] :
    (K.restrict p).tensorId A = (K.tensorId A).restrict (fun x => p x.1) := by
  refine ext_op (funext fun r => Matrix.ext fun i j => ?_)
  simp only [tensorId, restrict, kroneckerMap_apply, Matrix.diagonal_mul]
  ring

/-- Reindexing commutes with conjugation by permutations. -/
theorem reindex_permConj {κ : Type*} [Fintype κ] [DecidableEq κ] (e : ι ≃ κ) (K : KrausMap R ι ι)
    (σ τ : Equiv.Perm ι) :
    (K.permConj σ τ).reindex e = (K.reindex e).permConj (e.permCongr σ) (e.permCongr τ) :=
  ext_op (funext fun _ => Matrix.ext fun _ _ => by
    simp only [reindex, permConj, submatrix_apply, Equiv.permCongr_apply, Equiv.symm_apply_apply]
    congr 1
    symm
    rw [Equiv.symm_apply_eq, Equiv.symm_apply_eq, Equiv.permCongr_apply]
    simp)

/-- Reindexing commutes with the projection after a Kraus map. -/
theorem reindex_restrict {κ : Type*} [Fintype κ] [DecidableEq κ] (e : ι ≃ κ) (K : KrausMap R ι ι)
    (p : ι → Bool) :
    (K.restrict p).reindex e = (K.reindex e).restrict (fun x => p (e.symm x)) :=
  ext_op (funext fun _ => Matrix.ext fun _ _ => by
    simp [reindex, restrict, Matrix.diagonal_mul])

/-- `⊗ 1` keeps trace preservation. -/
theorem tensorId_tp {K : KrausMap R ι ι} (h : ∑ r, (K.op r)ᴴ * K.op r = 1) (A : Type*)
    [Fintype A] [DecidableEq A] : ∑ r, ((K.tensorId A).op r)ᴴ * (K.tensorId A).op r = 1 := by
  have h' : ∑ r, (K.op r ⊗ₖ (1 : Matrix A A ℂ))ᴴ * (K.op r ⊗ₖ (1 : Matrix A A ℂ)) =
      (∑ r, (K.op r)ᴴ * K.op r) ⊗ₖ (1 : Matrix A A ℂ) := by
    rw [sum_kronecker]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [conjTranspose_kronecker, conjTranspose_one, ← mul_kronecker_mul, Matrix.one_mul]
  simp only [tensorId]
  rw [h', h, one_kronecker_one]

/-- Reindexing keeps trace preservation. -/
theorem reindex_tp {κ : Type*} [Fintype κ] [DecidableEq κ] (e : ι ≃ κ) {K : KrausMap R ι ι}
    (h : ∑ r, (K.op r)ᴴ * K.op r = 1) : ∑ r, ((K.reindex e).op r)ᴴ * (K.reindex e).op r = 1 := by
  have h' : ∑ r, ((K.op r).submatrix e.symm e.symm)ᴴ * (K.op r).submatrix e.symm e.symm =
      (∑ r, (K.op r)ᴴ * K.op r).submatrix e.symm e.symm := by
    rw [submatrix_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [conjTranspose_submatrix, submatrix_mul_equiv]
  simp only [reindex]
  rw [h', h, submatrix_one_equiv]

/-- Conjugation by permutations keeps trace preservation. -/
theorem permConj_tp {K : KrausMap R ι ι} (h : ∑ r, (K.op r)ᴴ * K.op r = 1) (σ τ : Equiv.Perm ι) :
    ∑ r, ((K.permConj σ τ).op r)ᴴ * (K.permConj σ τ).op r = 1 := by
  have h' : ∑ r, ((K.op r).submatrix τ.symm σ)ᴴ * (K.op r).submatrix τ.symm σ =
      (∑ r, (K.op r)ᴴ * K.op r).submatrix σ σ := by
    rw [submatrix_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [conjTranspose_submatrix, submatrix_mul_equiv]
  simp only [permConj]
  rw [h', h, submatrix_one_equiv]

end KrausMap

/-- **The projection onto `p` keeps a placed matrix supported where `p` holds.** -/
theorem cut_embed {κ ι : Type*} [Fintype κ] [Fintype ι] [DecidableEq ι] {e : κ → ι}
    (he : Function.Injective e) {S : Set κ} {τ : Matrix κ κ ℂ} (hτ : SuppIn S τ) {p : ι → Bool}
    (hp : ∀ a ∈ S, p (e a) = true) (i j : ι) :
    (if p i then 1 else 0) * embed e τ i j * (if p j then 1 else 0) = embed e τ i j := by
  by_cases hi : ∃ a, e a = i
  · by_cases hj : ∃ b, e b = j
    · obtain ⟨a, rfl⟩ := hi
      obtain ⟨b, rfl⟩ := hj
      rw [embed_apply_of_injective he]
      by_cases hab : a ∈ S ∧ b ∈ S
      · rw [hp a hab.1, hp b hab.2]
        simp
      · rw [hτ a b (by tauto)]
        simp
    · rw [embed_apply_of_notMem_right _ _ fun b h => hj ⟨b, h⟩]
      simp
  · rw [embed_apply_of_notMem_left _ fun a h => hi ⟨a, h⟩]
    simp

section QueryCount

variable {n : ℕ} (sched : Fin n → Bool)

/-- **The number of query slots below slot `j`** of a schedule (`sched i = false` is a query
slot). -/
def queryCountBelow (j : ℕ) : ℕ :=
  (univ.filter fun i : Fin n => (i : ℕ) < j ∧ sched i = false).card

/-- **The number of query slots** of a schedule. -/
def queryCount : ℕ :=
  (univ.filter fun i : Fin n => sched i = false).card

theorem queryCountBelow_zero : queryCountBelow sched 0 = 0 := by
  simp [queryCountBelow]

theorem queryCountBelow_le (j : ℕ) : queryCountBelow sched j ≤ queryCount sched :=
  card_le_card fun i hi => by
    simp only [mem_filter, mem_univ, true_and] at hi ⊢
    exact hi.2

theorem queryCountBelow_succ (k : Fin n) :
    queryCountBelow sched (k + 1) = queryCountBelow sched k + if sched k then 0 else 1 := by
  by_cases h : sched k = true
  · rw [if_pos h, add_zero, queryCountBelow, queryCountBelow]
    congr 1
    ext i
    simp only [mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨hi, hs⟩
      refine ⟨?_, hs⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | hi
      · exact hi
      · rw [Fin.ext hi, h] at hs
        exact absurd hs (by decide)
    · rintro ⟨hi, hs⟩
      exact ⟨by omega, hs⟩
  · rw [Bool.not_eq_true] at h
    rw [if_neg (by simp [h]), queryCountBelow, queryCountBelow, ← card_insert_of_notMem
      (s := univ.filter fun i : Fin n => (i : ℕ) < k ∧ sched i = false) (a := k) (by simp)]
    congr 1
    ext i
    simp only [mem_filter, mem_univ, true_and, mem_insert]
    constructor
    · rintro ⟨hi, hs⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | hi
      · exact Or.inr ⟨hi, hs⟩
      · exact Or.inl (Fin.ext hi)
    · rintro (rfl | ⟨hi, hs⟩)
      · exact ⟨by omega, h⟩
      · exact ⟨by omega, hs⟩

/-- A query slot is followed by at least one more query slot of the budget. -/
theorem queryCountBelow_lt_of_false {k : Fin n} (h : sched k = false) :
    queryCountBelow sched k < queryCount sched := by
  have h1 := queryCountBelow_succ sched k
  have h2 := queryCountBelow_le sched (k + 1)
  rw [h1, if_neg (by simp [h])] at h2
  omega

/-- The counter value after the slots below `j`, in the counter register of budget
`queryCount sched`. -/
def cntAt (j : ℕ) : Fin (queryCount sched + 2) :=
  ⟨queryCountBelow sched j, by have := queryCountBelow_le sched j; omega⟩

theorem cntAt_zero : cntAt sched 0 = 0 :=
  Fin.ext (queryCountBelow_zero sched)

theorem cntAt_ne_of_false {k : Fin n} (h : sched k = false) :
    cntAt sched k ≠ Fin.castSucc (Fin.last (queryCount sched)) := fun he => by
  have := congrArg Fin.val he
  simp only [cntAt, Fin.val_castSucc, Fin.val_last] at this
  have := queryCountBelow_lt_of_false sched h
  omega

theorem cntAt_succ (k : Fin n) :
    (if sched k then cntAt sched k else finRotate _ (cntAt sched k)) = cntAt sched (k + 1) := by
  apply Fin.ext
  rw [show ((cntAt sched (k + 1) : Fin _) : ℕ) = queryCountBelow sched (k + 1) from rfl,
    queryCountBelow_succ]
  by_cases h : sched k = true
  · simp [h, cntAt]
  · have hne : cntAt sched k ≠ Fin.last (queryCount sched + 1) := fun he => by
      have := congrArg Fin.val he
      simp only [cntAt, Fin.val_last] at this
      have := queryCountBelow_le sched k
      omega
    simp only [h, ↓reduceIte, Bool.false_eq_true, coe_finRotate_of_ne_last hne]
    rfl

end QueryCount

section BlankReg

variable {V Rq Rs L P : Type} [Fintype V] [DecidableEq V] [Fintype Rq] [DecidableEq Rq]
  [Fintype Rs] [DecidableEq Rs] [Fintype L] [DecidableEq L] [Fintype P] [DecidableEq P]

/-- A basis state of a register `V × P` placed in the game registers with fixed request,
response and log values. -/
def withBlank (rq₀ : Rq) (rs₀ : Rs) (l₀ : L) (q : V × P) : (V × Rq × Rs × L) × P :=
  ((q.1, rq₀, rs₀, l₀), q.2)

omit [Fintype V] [DecidableEq V] [Fintype Rq] [DecidableEq Rq] [Fintype Rs] [DecidableEq Rs]
  [Fintype L] [DecidableEq L] [Fintype P] [DecidableEq P] in
theorem withBlank_injective (rq₀ : Rq) (rs₀ : Rs) (l₀ : L) :
    Function.Injective (withBlank (V := V) (P := P) rq₀ rs₀ l₀) :=
  fun _ _ h => congrArg (fun x : (V × Rq × Rs × L) × P => (x.1.1, x.2)) h

/-- **A matrix tensored with the identity on the request, response and log registers is
intertwined with placing at fixed values of them.** -/
theorem blank_intertwine (M : Matrix (V × P) (V × P) ℂ) (rq₀ : Rq) (rs₀ : Rs) (l₀ : L) :
    ((M ⊗ₖ (1 : Matrix (Rq × Rs) (Rq × Rs) ℂ)).submatrix
        (fun d : (V × Rq × Rs) × P => ((d.1.1, d.2), (d.1.2.1, d.1.2.2)))
        (fun d : (V × Rq × Rs) × P => ((d.1.1, d.2), (d.1.2.1, d.1.2.2))) ⊗ₖ
      (1 : Matrix L L ℂ)).submatrix
        (fun r : (V × Rq × Rs × L) × P => (((r.1.1, r.1.2.1, r.1.2.2.1), r.2), r.1.2.2.2))
        (fun r : (V × Rq × Rs × L) × P => (((r.1.1, r.1.2.1, r.1.2.2.1), r.2), r.1.2.2.2)) *
      jmat (withBlank rq₀ rs₀ l₀) =
    jmat (withBlank rq₀ rs₀ l₀) * M := by
  ext ⟨⟨v, rq, rs, l⟩, p⟩ ⟨v', p'⟩
  simp only [Matrix.mul_apply, jmat, submatrix_apply, kroneckerMap_apply, mul_ite, mul_one,
    mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  by_cases h : rq = rq₀ ∧ rs = rs₀ ∧ l = l₀
  · obtain ⟨rfl, rfl, rfl⟩ := h
    symm
    refine (Finset.sum_eq_single (v, p) (fun j _ hj => ?_) (by simp)).trans ?_
    · split_ifs with h
      · exact absurd (withBlank_injective rq _ l h) hj
      · simp
    · simp [withBlank, Matrix.one_apply]
  · symm
    refine (Finset.sum_eq_zero fun j _ => ?_).trans ?_
    · split_ifs with h'
      · exact absurd ⟨(congrArg (fun x : (V × Rq × Rs × L) × P => x.1.2.1) h').symm,
          (congrArg (fun x : (V × Rq × Rs × L) × P => x.1.2.2.1) h').symm,
          (congrArg (fun x : (V × Rq × Rs × L) × P => x.1.2.2.2) h').symm⟩ h
      · simp
    · simp only [withBlank, Matrix.one_apply, Prod.mk.injEq]
      by_cases h1 : rq = rq₀ ∧ rs = rs₀
      · have h2 : ¬ l = l₀ := fun h2 => h ⟨h1.1, h1.2, h2⟩
        simp [h2]
      · simp only [not_and_or] at h1
        rcases h1 with h1 | h1 <;> simp [h1]

end BlankReg

section CounterReg

variable {W Rq Rs L F P : Type} [Fintype W] [DecidableEq W] [Fintype Rq] [DecidableEq Rq]
  [Fintype Rs] [DecidableEq Rs] [Fintype L] [DecidableEq L] [Fintype F] [DecidableEq F]
  [Fintype P] [DecidableEq P]

/-- A game basis state with a counter value `c` placed next to the workspace. -/
def withCnt (c : F) (r : (W × Rq × Rs × L) × P) : ((W × F) × Rq × Rs × L) × P :=
  (((r.1.1, c), r.1.2), r.2)

omit [Fintype W] [DecidableEq W] [Fintype Rq] [DecidableEq Rq] [Fintype Rs] [DecidableEq Rs]
  [Fintype L] [DecidableEq L] [Fintype F] [DecidableEq F] [Fintype P] [DecidableEq P] in
theorem withCnt_injective (c : F) :
    Function.Injective (withCnt (W := W) (Rq := Rq) (Rs := Rs) (L := L) (P := P) c) :=
  fun _ _ h => congrArg (fun x : ((W × F) × Rq × Rs × L) × P => ((x.1.1.1, x.1.2), x.2)) h

/-- **A matrix on the adversary's registers, tensored with the identity on a counter and on
the logs, is intertwined with placing at a counter value**. -/
theorem counter_intertwine (M : Matrix ((W × Rq × Rs) × P) ((W × Rq × Rs) × P) ℂ) (c : F) :
    ((M ⊗ₖ (1 : Matrix F F ℂ)).submatrix
        (fun p : ((W × F) × Rq × Rs) × P => (((p.1.1.1, p.1.2.1, p.1.2.2), p.2), p.1.1.2))
        (fun p : ((W × F) × Rq × Rs) × P => (((p.1.1.1, p.1.2.1, p.1.2.2), p.2), p.1.1.2)) ⊗ₖ
      (1 : Matrix L L ℂ)).submatrix
        (fun r : ((W × F) × Rq × Rs × L) × P => (((r.1.1, r.1.2.1, r.1.2.2.1), r.2), r.1.2.2.2))
        (fun r : ((W × F) × Rq × Rs × L) × P => (((r.1.1, r.1.2.1, r.1.2.2.1), r.2), r.1.2.2.2)) *
      jmat (withCnt c) =
    jmat (withCnt c) * (M ⊗ₖ (1 : Matrix L L ℂ)).submatrix
        (fun r : (W × Rq × Rs × L) × P => (((r.1.1, r.1.2.1, r.1.2.2.1), r.2), r.1.2.2.2))
        (fun r : (W × Rq × Rs × L) × P => (((r.1.1, r.1.2.1, r.1.2.2.1), r.2), r.1.2.2.2)) := by
  ext ⟨⟨⟨w, c'⟩, rq, rs, lg⟩, p⟩ ⟨⟨w', rq', rs', lg'⟩, p'⟩
  simp only [Matrix.mul_apply, jmat, submatrix_apply, kroneckerMap_apply, mul_ite, mul_one,
    mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  by_cases hc : c' = c
  · subst hc
    symm
    refine (Finset.sum_eq_single ((w, rq, rs, lg), p) (fun j _ hj => ?_) (by simp)).trans ?_
    · split_ifs with h
      · exact absurd (withCnt_injective c' h) hj
      · simp
    · simp only [withCnt, Matrix.one_apply, ite_true, mul_one, mul_ite, mul_zero]
      split_ifs <;> simp_all
  · symm
    refine (Finset.sum_eq_zero fun j _ => ?_).trans ?_
    · split_ifs with h
      · exact absurd (congrArg (fun x : ((W × F) × Rq × Rs × L) × P => x.1.1.2) h).symm hc
      · simp
    · simp only [withCnt, Matrix.one_apply]
      simp [hc]

end CounterReg

namespace KindAlg

variable {X Y Req Resp O : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp]
  (K : KindAlg X Y Req Resp O) (b : ℕ)

/-- **A kind algorithm as an adversary with run-time kinds and budget `b`**: the same registers,
kinds, Kraus maps and output, with a budget of `b` query slots. -/
def toAdaptive : AdaptiveIAlg X Y Req Resp O where
  W := K.W
  width := K.width
  width_pos := K.width_pos
  slots := K.slots
  post := K.post
  budget := b
  kind := K.kind
  R := K.R
  init := K.init
  step := K.step
  out := K.out

/-- A game basis state of `K` placed in `(K.toAdaptive b).toKindAlg` with the query counter at
`c`. -/
def placeCnt (c : Fin (b + 2)) (r : K.G) : (K.toAdaptive b).toKindAlg.G :=
  withCnt c r

theorem placeCnt_injective (c : Fin (b + 2)) : Function.Injective (K.placeCnt b c) :=
  withCnt_injective c

/-- The Kraus map of `K` with the counter carried along unchanged, on the game registers. -/
def rawLiftG (k : StepIdx K.slots K.post) :
    KrausMap (K.toAdaptive b).toKindAlg.R (K.toAdaptive b).toKindAlg.G
      (K.toAdaptive b).toKindAlg.G :=
  ((((K.step k).tensorId (Fin (b + 2))).reindex (K.toAdaptive b).cntSplit.symm).tensorId
    (LogReg Req K.slots)).reindex splitLogs.symm

theorem rawLiftG_embed (k : StepIdx K.slots K.post) (c : Fin (b + 2)) (σ : Matrix K.G K.G ℂ) :
    (K.rawLiftG b k) (embed (K.placeCnt b c) σ) = embed (K.placeCnt b c) ((K.liftG k) σ) :=
  KrausMap.apply_embed_of_intertwine (fun r => counter_intertwine ((K.step k).op r) c) σ

/-- The counter shift of `(K.toAdaptive b).toKindAlg` on the game registers. -/
def shiftG : Equiv.Perm (K.toAdaptive b).toKindAlg.G :=
  splitLogs.symm.permCongr ((K.toAdaptive b).cntShift.prodCongr (Equiv.refl _))

/-- The budget test of `(K.toAdaptive b).toKindAlg` on the game registers. -/
def inBudgetG (r : (K.toAdaptive b).toKindAlg.G) : Bool :=
  (K.toAdaptive b).inBudget (splitLogs r).1

theorem liftG_toAdaptive_slot {k : StepIdx K.slots K.post} (hk : (k : ℕ) < K.slots) :
    (K.toAdaptive b).toKindAlg.liftG k =
      ((K.rawLiftG b k).restrict (K.inBudgetG b)).permConj (Equiv.refl _) (K.shiftG b) := by
  have h : (K.toAdaptive b).toKindAlg.step k = (((K.step k).tensorId (Fin (b + 2))).reindex
      (K.toAdaptive b).cntSplit.symm |>.restrict (K.toAdaptive b).inBudget).permConj
        (Equiv.refl _) (K.toAdaptive b).cntShift :=
    if_pos hk
  show (((K.toAdaptive b).toKindAlg.step k).tensorId (LogReg Req K.slots)).reindex splitLogs.symm = _
  erw [h, KrausMap.tensorId_permConj, KrausMap.tensorId_restrict, KrausMap.reindex_permConj,
    KrausMap.reindex_restrict]
  rfl

theorem inBudgetG_withCnt (c : Fin (b + 2)) (a : K.G) :
    K.inBudgetG b (K.placeCnt b c a) = (K.kind a.1.1 || decide (c ≠ Fin.castSucc (Fin.last b))) :=
  rfl

theorem shiftG_withCnt (c : Fin (b + 2)) (a : K.G) :
    K.shiftG b (K.placeCnt b c a) =
      K.placeCnt b (if K.kind a.1.1 then c else finRotate _ c) a := by
  obtain ⟨⟨w, rq, rs, lg⟩, p⟩ := a
  change splitLogs.symm (((K.toAdaptive b).cntShift (((w, c), rq, rs), p)), lg) = _
  have hs : (K.toAdaptive b).cntShift (((w, c), rq, rs), p) =
      (((w, if K.kind w then c else finRotate _ c), rq, rs), p) := by
    have hk : (K.toAdaptive b).kind w = K.kind w := rfl
    simp only [AdaptiveIAlg.cntShift, Equiv.prodCongr_apply, Prod.map, Equiv.prodShear_apply,
      Equiv.refl_apply, hk]
    split_ifs <;> rfl
  rw [hs]
  rfl

/-- **A slot step of `K.toAdaptive b` on a placed state**: from counter `c`, on a state whose
kind after the step is `s`, within the budget, the step of `K` placed at the advanced counter. -/
theorem liftG_toAdaptive_slot_embed {k : StepIdx K.slots K.post} (hk : (k : ℕ) < K.slots)
    {c : Fin (b + 2)} {s : Bool} {σ : Matrix K.G K.G ℂ}
    (hs : SuppIn {r : K.G | K.kind r.1.1 = s} ((K.liftG k) σ))
    (hb : s = true ∨ c ≠ Fin.castSucc (Fin.last b)) :
    (K.toAdaptive b).toKindAlg.liftG k (embed (K.placeCnt b c) σ) =
      embed (K.placeCnt b (if s then c else finRotate _ c)) ((K.liftG k) σ) := by
  rw [K.liftG_toAdaptive_slot b hk]
  erw [KrausMap.permConj_apply]
  have hcut : (K.rawLiftG b k).restrict (K.inBudgetG b) (embed (K.placeCnt b c) σ) =
      embed (K.placeCnt b c) ((K.liftG k) σ) := by
    ext i j
    rw [KrausMap.restrict_apply_apply, K.rawLiftG_embed b k c σ]
    refine cut_embed (K.placeCnt_injective b c) hs (fun a ha => ?_) i j
    refine (K.inBudgetG_withCnt b c a).trans ?_
    rcases hb with hb | hb
    · simp only [Set.mem_ofPred_eq] at ha
      simp [ha, hb]
    · simp [hb]
  simp only [Equiv.refl_symm, Equiv.coe_refl, submatrix_id_id]
  rw [hcut]
  refine submatrix_embed (π' := Equiv.refl _) (fun a ha => ?_) hs
  simp only [Set.mem_ofPred_eq] at ha
  exact (K.shiftG_withCnt b c a).trans (by rw [ha]; rfl)

/-- `liftG_toAdaptive_slot_embed` at the step before slot `k`. -/
theorem liftG_slotStep_embed (k : Fin K.slots) {c : Fin (b + 2)} {s : Bool}
    {σ : Matrix K.G K.G ℂ} (hs : SuppIn {r : K.G | K.kind r.1.1 = s} ((K.liftG (slotStep k)) σ))
    (hb : s = true ∨ c ≠ Fin.castSucc (Fin.last b)) :
    (K.toAdaptive b).toKindAlg.liftG (slotStep k) (embed (K.placeCnt b c) σ) =
      embed (K.placeCnt b (if s then c else finRotate _ c)) ((K.liftG (slotStep k)) σ) :=
  K.liftG_toAdaptive_slot_embed b k.2 hs hb

theorem liftG_toAdaptive_post {k : StepIdx K.slots K.post} (hk : ¬ (k : ℕ) < K.slots) :
    (K.toAdaptive b).toKindAlg.liftG k = K.rawLiftG b k := by
  have h : (K.toAdaptive b).toKindAlg.step k = ((K.step k).tensorId (Fin (b + 2))).reindex
      (K.toAdaptive b).cntSplit.symm :=
    if_neg hk
  show (((K.toAdaptive b).toKindAlg.step k).tensorId (LogReg Req K.slots)).reindex splitLogs.symm = _
  rw [h]
  rfl

theorem liftG_postStep_embed (j : Fin K.post) (c : Fin (b + 2)) (σ : Matrix K.G K.G ℂ) :
    (K.toAdaptive b).toKindAlg.liftG (postStep j) (embed (K.placeCnt b c) σ) =
      embed (K.placeCnt b c) ((K.liftG (postStep j)) σ) := by
  exact (congrArg (fun M => KrausMap.apply M (embed (K.placeCnt b c) σ))
    (K.liftG_toAdaptive_post b (k := postStep j) (by simp))).trans (K.rawLiftG_embed b _ c σ)

theorem liftG_lastStep_embed (c : Fin (b + 2)) (σ : Matrix K.G K.G ℂ) :
    (K.toAdaptive b).toKindAlg.liftG lastStep (embed (K.placeCnt b c) σ) =
      embed (K.placeCnt b c) ((K.liftG lastStep) σ) := by
  exact (congrArg (fun M => KrausMap.apply M (embed (K.placeCnt b c) σ))
    (K.liftG_toAdaptive_post b (k := lastStep) (by simp))).trans (K.rawLiftG_embed b _ c σ)

theorem liftG_toAdaptive_post_embed {k : StepIdx K.slots K.post} (hk : ¬ (k : ℕ) < K.slots)
    (c : Fin (b + 2)) (σ : Matrix K.G K.G ℂ) :
    (K.toAdaptive b).toKindAlg.liftG k (embed (K.placeCnt b c) σ) = embed (K.placeCnt b c) ((K.liftG k) σ) := by
  rw [K.liftG_toAdaptive_post b hk]
  exact K.rawLiftG_embed b k c σ

theorem logAt_withCnt (k : Fin K.slots) (c : Fin (b + 2)) (a : K.G) :
    (K.toAdaptive b).toKindAlg.logAt k (K.placeCnt b c a) = K.logAt k a :=
  rfl

theorem copyG_withCnt (k : Fin K.slots) (c : Fin (b + 2)) (a : K.G) :
    (K.toAdaptive b).toKindAlg.copyG k (K.placeCnt b c a) = K.placeCnt b c (K.copyG k a) := by
  obtain ⟨⟨w, rq, rs, lg⟩, p⟩ := a
  have hk : (K.toAdaptive b).toKindAlg.kind (w, c) = K.kind w := rfl
  simp only [copyG, Equiv.prodCongr_apply, Prod.map, placeCnt, withCnt, Equiv.refl_apply]
  erw [copyPerm_apply, copyPerm_apply]
  rw [hk]
  by_cases h : K.kind w = true <;> simp [h] <;> rfl

variable [AddGroup Y] {Ω St : Type} {Q : ℕ} [OracleState St X Y] (E : Env Ω Req Resp X Y Q St)

omit [AddGroup Y] [OracleState St X Y] in
theorem respG_withCnt (ω : Ω) (k : Fin K.slots) (c : Fin (b + 2)) (a : K.G) :
    (K.toAdaptive b).toKindAlg.respG E ω k (K.placeCnt b c a) = K.placeCnt b c (K.respG E ω k a) := by
  obtain ⟨⟨w, rq, rs, lg⟩, p⟩ := a
  have hk : (K.toAdaptive b).toKindAlg.kind (w, c) = K.kind w := rfl
  simp only [respG, Equiv.prodCongr_apply, Prod.map, placeCnt, withCnt, Equiv.refl_apply]
  erw [respondPerm_apply, respondPerm_apply]
  rw [hk]
  by_cases h : K.kind w = true <;> simp [h] <;> rfl

theorem oraclePerm_withCnt (ω : Ω) (c : Fin (b + 2)) (a : K.G) :
    E.oraclePerm (K.toAdaptive b).toKindAlg.kind ω (K.placeCnt b c a) =
      K.placeCnt b c (E.oraclePerm K.kind ω a) :=
  rfl

theorem postG_withCnt (ω : Ω) (c : Fin (b + 2)) (a : K.G) :
    (K.toAdaptive b).toKindAlg.postG E ω (K.placeCnt b c a) = K.placeCnt b c (K.postG E ω a) :=
  rfl

omit [AddGroup Y] [OracleState St X Y] in
/-- Conjugating a placed matrix by a permutation that commutes with placing. -/
theorem submatrix_embed_withCnt {π' : Equiv.Perm (K.toAdaptive b).toKindAlg.G}
    {π : Equiv.Perm K.G} {c : Fin (b + 2)} (h : ∀ a, π' (K.placeCnt b c a) = K.placeCnt b c (π a))
    (τ : Matrix K.G K.G ℂ) :
    (embed (K.placeCnt b c) τ).submatrix π'.symm π'.symm = embed (K.placeCnt b c) (τ.submatrix π.symm π.symm) :=
  submatrix_embed (S := Set.univ) (fun a _ => h a) (fun _ _ h => by simp at h)

/-- **The events of a slot commute with placing at a counter value.** -/
theorem eventCirc_run_embed (ω : Ω) (k : Fin K.slots) (deph : Bool) (c : Fin (b + 2))
    (τ : Matrix K.G K.G ℂ) :
    ((K.toAdaptive b).toKindAlg.eventCirc E ω k deph).run (Equiv.refl _) (embed (K.placeCnt b c) τ) =
      embed (K.placeCnt b c) ((K.eventCirc E ω k deph).run (Equiv.refl _) τ) := by
  cases deph <;>
  · simp only [eventCirc, Circuit.run, KrausMap.ofPerm_apply, Bool.false_eq_true, ↓reduceIte, id,
      KrausMap.measureFn_apply]
    rw [K.submatrix_embed_withCnt b (K.copyG_withCnt b k c)]
    try rw [dephase_embed]
    rw [K.submatrix_embed_withCnt b (K.respG_withCnt b E ω k c),
      K.submatrix_embed_withCnt b (K.oraclePerm_withCnt b E ω c)]
    try rfl

omit [AddGroup Y] [OracleState St X Y] in
theorem embed_placeCnt_apply (c c' c'' : Fin (b + 2)) (σ : Matrix K.G K.G ℂ) (a a' : K.G) :
    embed (K.placeCnt b c) σ (K.placeCnt b c' a) (K.placeCnt b c'' a') =
      if c' = c ∧ c'' = c then σ a a' else 0 := by
  split_ifs with h
  · obtain ⟨rfl, rfl⟩ := h
    exact embed_apply_of_injective (K.placeCnt_injective b _) σ a a'
  · rcases not_and_or.1 h with h | h
    · refine embed_apply_of_notMem_left _ (fun x hx => h ?_) _
      exact (congrArg (fun r : (K.toAdaptive b).toKindAlg.G => r.1.1.2) hx).symm
    · refine embed_apply_of_notMem_right _ _ (fun x hx => h ?_)
      exact (congrArg (fun r : (K.toAdaptive b).toKindAlg.G => r.1.1.2) hx).symm

omit [AddGroup Y] [OracleState St X Y] in
theorem exists_placeCnt (r : (K.toAdaptive b).toKindAlg.G) : ∃ c a, K.placeCnt b c a = r :=
  ⟨r.1.1.2, ((r.1.1.1, r.1.2), r.2), rfl⟩

omit [AddGroup Y] [OracleState St X Y] in
/-- **The initial state of the mixed game of `K.toAdaptive b`** is that of `K` placed at counter
`0`. -/
theorem mgInit_toAdaptive : (K.toAdaptive b).toKindAlg.mgInit = embed (K.placeCnt b 0) K.mgInit := by
  ext i j
  obtain ⟨c', a, rfl⟩ := K.exists_placeCnt b i
  obtain ⟨c'', a', rfl⟩ := K.exists_placeCnt b j
  rw [embed_placeCnt_apply]
  obtain ⟨⟨w, rq, rs, lg⟩, p⟩ := a
  obtain ⟨⟨w', rq', rs', lg'⟩, p'⟩ := a'
  change (_ * Matrix.single (0 : Fin (b + 2)) 0 (1 : ℂ) c' c'') * _ = _
  simp only [mgInit, MState.reindex, MState.tensorKet_mat, submatrix_apply, kroneckerMap_apply,
    Matrix.single_apply]
  by_cases h : c' = 0 ∧ c'' = 0
  · rw [if_pos h, if_pos ⟨h.1.symm, h.2.symm⟩, mul_one]
    rfl
  · rw [if_neg h, if_neg fun h' => h ⟨h'.1.symm, h'.2.symm⟩, mul_zero, zero_mul]

end KindAlg

namespace KindAlg

variable {X Y Req Resp O : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp] [Nonempty X] [AddGroup Y]
  [Nonempty Y] (K : KindAlg X Y Req Resp O) (C : Challenger X Y Req Resp)

/-- **The mixed game of `K` with a budget counter follows `K` along a respected schedule**: if
`K` respects the schedule `sched` along its run (`KindAlg.Respects`), then with the budget the
number of query slots of `sched`, the mixed game of `K.toAdaptive` runs that of `K`, with the
counter after the slots below `j` equal to the number of query slots below `j`; no branch is
projected away by the budget. -/
theorem mgRun_toAdaptive {sched : Fin K.slots → Bool} {Inv : ℕ → Set K.G}
    (hInv : K.Respects C sched Inv) (h0 : SuppIn (Inv 0) K.mgInit) (H : X → Y) (c : C.Coins) :
    (K.toAdaptive (queryCount sched)).toKindAlg.mgRun C.toPureEnv (H, c) true =
      embed (K.placeCnt _ (cntAt sched K.slots)) (K.mgRun C.toPureEnv (H, c) true) := by
  set b := queryCount sched
  have hslots : ∀ (l : List (Fin K.slots)) (j : ℕ), l.map Fin.val = List.range' j l.length →
      ∀ {σ : Matrix K.G K.G ℂ}, SuppIn (K.blankFrom j ∩ Inv j) σ →
      (Circuit.concat (l.map fun k : Fin K.slots => Circuit.kraus
          ((K.toAdaptive b).toKindAlg.liftG (slotStep k))
          ((K.toAdaptive b).toKindAlg.eventCirc C.toPureEnv (H, c) k true))).run (Equiv.refl _)
          (embed (K.placeCnt b (cntAt sched j)) σ) =
        embed (K.placeCnt b (cntAt sched (j + l.length)))
          ((Circuit.concat (l.map (K.gameSlot C H c))).run (Equiv.refl _) σ) ∧
      SuppIn (K.blankFrom (j + l.length) ∩ Inv (j + l.length))
          ((Circuit.concat (l.map (K.gameSlot C H c))).run (Equiv.refl _) σ) := by
    intro l
    induction l with
    | nil => intro j _ σ hσ; exact ⟨rfl, hσ⟩
    | cons k l ih =>
      intro j hl σ hσ
      simp only [List.map_cons, List.length_cons, List.range'_succ, List.cons.injEq] at hl ⊢
      have hσ' : SuppIn (K.blankFrom k ∩ Inv k) σ := by rw [hl.1]; exact hσ
      have h2 : SuppIn (K.blankFrom (k + 1) ∩ Inv (k + 1))
          ((K.gameSlot C H c k).run (Equiv.refl _) σ) :=
        (K.suppIn_slot C H c k (hσ'.mono Set.inter_subset_left)).inter (hInv.step H c k hσ')
      obtain ⟨ih1, ih2⟩ := ih (↑k + 1) (by rw [hl.2, hl.1]) h2
      have hstep := K.liftG_slotStep_embed b k (hInv.kind k hσ')
        (c := cntAt sched k) (by
          cases hs : sched k
          · exact Or.inr (cntAt_ne_of_false sched hs)
          · exact Or.inl rfl)
      rw [cntAt_succ] at hstep
      rw [Circuit.run_concat, Circuit.run_concat, ← hl.1]
      simp only [Circuit.run]
      rw [hstep, eventCirc_run_embed]
      rw [show (k : ℕ) + 1 + l.length = k + (l.length + 1) by omega] at ih1 ih2
      exact ⟨ih1, ih2⟩
  have hposts : ∀ (l : List (Fin K.post)) (d : Fin (b + 2)) (σ : Matrix K.G K.G ℂ),
      (Circuit.concat (l.map fun j : Fin K.post =>
        Circuit.kraus ((K.toAdaptive b).toKindAlg.liftG (postStep j))
          (.kraus (KrausMap.ofPerm ((K.toAdaptive b).toKindAlg.postG C.toPureEnv (H, c))) .nil))).run
          (Equiv.refl _) (embed (K.placeCnt b d) σ) =
        embed (K.placeCnt b d) ((Circuit.concat (l.map fun j : Fin K.post =>
          Circuit.kraus (K.liftG (postStep j))
            (.kraus (KrausMap.ofPerm (K.postG C.toPureEnv (H, c))) .nil))).run (Equiv.refl _) σ) := by
    intro l
    induction l with
    | nil => intro d σ; rfl
    | cons j l ih =>
      intro d σ
      rw [List.map_cons, List.map_cons, Circuit.run_concat, Circuit.run_concat]
      simp only [Circuit.run, KrausMap.ofPerm_apply]
      rw [K.liftG_postStep_embed b j d σ,
        K.submatrix_embed_withCnt b (K.postG_withCnt b C.toPureEnv (H, c) d), ih]
  obtain ⟨h1, -⟩ := hslots (List.finRange K.slots) 0
    (by rw [List.map_coe_finRange_eq_range, List.range_eq_range', List.length_finRange])
    (K.suppIn_mgInit.inter h0)
  rw [List.length_finRange, Nat.zero_add, cntAt_zero] at h1
  simp only [mgRun, mgCirc, Circuit.run_append]
  rw [K.mgInit_toAdaptive b]
  erw [h1, hposts]
  simp only [Circuit.run]
  erw [K.liftG_lastStep_embed b]
  rfl

end KindAlg

namespace KindAlg

variable {X Y Req Resp O : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp] [Nonempty X] [AddGroup Y]
  [Nonempty Y] [DecidableEq O] (K : KindAlg X Y Req Resp O) (C : Challenger X Y Req Resp)

/-- **The mixed game of `K` with a budget counter accepts as that of `K`** along a respected
schedule. -/
theorem mgAccept_toAdaptive {sched : Fin K.slots → Bool} {Inv : ℕ → Set K.G}
    (hInv : K.Respects C sched Inv) (h0 : SuppIn (Inv 0) K.mgInit) (o : O) (H : X → Y)
    (c : C.Coins) :
    (K.toAdaptive (queryCount sched)).toKindAlg.mgAccept C.toPureEnv o (H, c) true =
      K.mgAccept C.toPureEnv o (H, c) true := by
  have hg : ∀ (L : Type) [Fintype L] (f : L → O) (M : Matrix L L ℂ),
      (∑ r, if f r = o then (M r r).re else 0) = ∑ r, (if f r = o then 1 else 0) * (M r r).re :=
    fun L _ f M => Finset.sum_congr rfl fun r _ => by split_ifs <;> simp
  rw [mgAccept, mgAccept, K.mgRun_toAdaptive C hInv h0 H c, hg, hg,
    embed_diag_of_injective (K.placeCnt_injective _ _)]
  rfl

end KindAlg

namespace KindAlg

variable {X Y Req Resp O : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp] [Nonempty X] [AddGroup Y]
  [Nonempty Y] (B : KindAlg X Y Req Resp O) (C : Challenger X Y Req Resp)

/-- **The output law of `composeBothOut f`** is the coin-average of the diagonal of the mixed game
with measured requests on the registers whose composed register `f` reads as `o` (as
`IAlg.outLaw_composeOut_some`). -/
theorem outLaw_composeBothOut_some {O' : Type} [DecidableEq O'] (f : B.CW C → O') (H : X → Y)
    (o : O') :
    (B.composeBothOut C f).outLaw H (some o) =
      ENNReal.ofReal (∑ c, (C.coins c).toReal * ∑ r : B.G,
        if f (B.emb C H c B.slots r).1 = o then (B.mgRun C.toPureEnv (H, c) true r r).re
        else 0) := by
  have hpsd := (B.composeBothOut C f).posSemidef_stage H (B.composeBothOut C f).depth
  rw [Alg.outLaw]
  refine (map_basisLaw_apply_some (o := o) ..).trans ?_
  have hdiag : ∀ p, 0 ≤ ((B.composeBothOut C f).final H p p).re := fun p =>
    (Complex.nonneg_iff.1 (hpsd.diag_nonneg (i := p))).1
  have hite : ∀ p, (if some o = some ((B.composeBothOut C f).out p.1) then
      ENNReal.ofReal ((B.composeBothOut C f).final H p p).re else 0) =
      ENNReal.ofReal (if o = (B.composeBothOut C f).out p.1 then
        ((B.composeBothOut C f).final H p p).re else 0) :=
    fun p => by split_ifs with h1 h2 h2 <;> simp_all
  refine (Finset.sum_congr rfl fun p _ => hite p).trans ?_
  rw [← ENNReal.ofReal_sum_of_nonneg fun p _ => by split_ifs; exact hdiag p; exact le_rfl]
  congr 1
  rw [composeBothOut_final, composeBoth_final]
  have hanc : ∀ a : X × Y × Bool, (reprogAnc (Y := Y) (x₀ : X) a a).im = 0 := fun a => by
    simp only [reprogAnc, ancWeight]
    split_ifs <;> simp
  have hstep : ∀ σ : Matrix (QueryReg (B.CW C) 1 X Y) (QueryReg (B.CW C) 1 X Y) ℂ,
      (∑ p : ReprogrammedQueryReg (B.CW C) X Y,
        if o = f p.1.1 then (withAnc x₀ σ p p).re else 0) =
        ∑ q : QueryReg (B.CW C) 1 X Y, if o = f q.1 then (σ q q).re else 0 := by
    intro σ
    rw [← (ancSplit (B.CW C) X Y).symm.sum_comp, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun q _ => ?_
    simp only [ancSplit, Equiv.coe_fn_symm_mk, withAnc, Complex.mul_re, hanc, mul_zero, sub_zero]
    split_ifs
    · rw [← Finset.mul_sum, sum_re_reprogAnc, mul_one]
    · simp
  refine (hstep _).trans ?_
  simp only [re_sum_smul_apply]
  have hg : ∀ q : QueryReg (B.CW C) 1 X Y, ∀ x : ℝ,
      (if o = f q.1 then x else 0) = (if o = f q.1 then 1 else 0) * x :=
    fun q x => by split_ifs <;> simp
  rw [Finset.sum_congr rfl fun q _ => hg q _]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp only [mul_left_comm _ (C.coins c).toReal, ← Finset.mul_sum]
  congr 1
  rw [embed_diag_of_injective (B.emb_injective C H c B.slots)]
  refine Finset.sum_congr rfl fun r _ => ?_
  by_cases h : f (B.emb C H c B.slots r).1 = o
  · simp [h]
  · simp [h, Ne.symm h]

variable (K : KindAlg X Y Req Resp O) (b : ℕ)

/-- The composed registers of `K` with the query counter of `K.toAdaptive b` at `d` added to the
workspace. -/
def cwLift (d : Fin (b + 2)) (v : K.CW C) : (K.toAdaptive b).toKindAlg.CW C :=
  ⟨(((v.adv.1.1, d), v.adv.1.2), v.adv.2), v.chal⟩

omit [Nonempty X] [AddGroup Y] [Nonempty Y] in
theorem cwLift_injective (d : Fin (b + 2)) : Function.Injective (K.cwLift C b d) := by
  intro v v' h
  have h1 := congrArg (fun u : (K.toAdaptive b).toKindAlg.CW C => ((u.adv.1.1.1, u.adv.1.2), u.adv.2)) h
  have h2 := congrArg (fun u : (K.toAdaptive b).toKindAlg.CW C => u.chal) h
  exact CWork.ext h1 h2

theorem emb_placeCnt (H : X → Y) (c : C.Coins) (J : ℕ) (d : Fin (b + 2)) (r : K.G) :
    ((K.toAdaptive b).toKindAlg.emb C H c J (K.placeCnt b d r)).1 =
      K.cwLift C b d (K.emb C H c J r).1 :=
  rfl

end KindAlg

namespace IAlg

variable {X Y Req Resp O : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp]
  (A : IAlg X Y Req Resp O)

/-- **A fixed-schedule interactive adversary as one with run-time kinds**: the adversary with its
slot counter (`IAlg.toKindAlg`), whose kind register reads the schedule from the counter, with a
budget of its number of query slots. -/
def toAdaptive : AdaptiveIAlg X Y Req Resp O :=
  A.toKindAlg.toAdaptive A.querySlots

@[simp] theorem toAdaptive_width : A.toAdaptive.width = A.width := rfl
@[simp] theorem toAdaptive_budget : A.toAdaptive.budget = A.querySlots := rfl
@[simp] theorem toAdaptive_post : A.toAdaptive.post = A.post := rfl
@[simp] theorem toAdaptive_slots : A.toAdaptive.slots = A.slots := rfl

/-- **The embedding keeps trace preservation**: the slot counter is advanced by a permutation. -/
theorem toAdaptive_tracePreserving (h : A.TracePreserving) : A.toAdaptive.TracePreserving :=
  fun k => KrausMap.permConj_tp (KrausMap.reindex_tp _ (KrausMap.tensorId_tp (h k) _)) _ _

/-- **The embedding keeps the query count**: the budget is the number of query slots. -/
theorem toAdaptive_queries : A.toAdaptive.width * (A.toAdaptive.budget + A.toAdaptive.post) =
    A.width * (A.querySlots + A.post) :=
  rfl

/-- **The slot counter keeps trace preservation**: it is advanced by a permutation. -/
theorem TracePreserving.toKindAlg_stepsTP {A : IAlg X Y Req Resp O} (h : A.TracePreserving) :
    A.toKindAlg.StepsTP :=
  fun k => KrausMap.permConj_tp (KrausMap.reindex_tp _ (KrausMap.tensorId_tp (h k) _)) _ _

variable [Nonempty X] [AddGroup Y] [Nonempty Y] (C : Challenger X Y Req Resp)

/-- **The embedding keeps the output law** on every oracle. -/
theorem outLaw_compose_toAdaptive (H : X → Y) :
    (A.toAdaptive.compose C).outLaw H = (A.compose C).outLaw H := by
  classical
  refine PMF.ext_of_some fun o => ?_
  rw [AdaptiveIAlg.compose, KindAlg.outLaw_composeBoth_some, outLaw_compose_some]
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  exact congrArg _ (A.toKindAlg.mgAccept_toAdaptive C (A.respects C) A.suppIn_mgInit_cnt o H c)

/-- **The embedding keeps the law of the output and the oracle.** -/
theorem realLaw_compose_toAdaptive {B : Type} (e : Y ≃ B) :
    (A.toAdaptive.compose C).realLaw e = (A.compose C).realLaw e := by
  simp only [Alg.realLaw, A.outLaw_compose_toAdaptive C]

variable {A} in
/-- **The composition of a trace-preserving adversary keeps the trace**: its final state has
trace one. -/
theorem TracePreserving.trace_final_compose (h : A.TracePreserving) (H : X → Y) :
    ((A.compose C).final H).trace = 1 := by
  have hfin : (A.compose C).final H =
      withAnc KindAlg.x₀ ((A.fullCirc C).run H (A.toKindAlg.initSys C).mat) := by
    rw [Circuit.toAlg_final]
    exact ReprogrammedCircuit.run_toCircuit H _ _ _
  rw [hfin, KindAlg.trace_withAnc, IAlg.fullCirc, (h.toKindAlg_stepsTP.allTP_fullCirc C A.sched).trace_run H,
    (A.toKindAlg.initSys C).trace_eq_one]

variable {A} in
/-- **A trace-preserving adversary always terminates**: its composition outputs `none` with
probability `0`. -/
theorem TracePreserving.outLaw_compose_none (h : A.TracePreserving) (H : X → Y) :
    (A.compose C).outLaw H none = 0 := by
  rw [Alg.outLaw_none, h.trace_final_compose C H]
  simp

variable {A} in
/-- **The embedding of a trace-preserving adversary stays within its budget**: its model run
always terminates (`AdaptiveIAlg.withinBudget_iff`), since that of `A` does. -/
theorem TracePreserving.toAdaptive_withinBudget (h : A.TracePreserving) :
    A.toAdaptive.WithinBudget :=
  (AdaptiveIAlg.withinBudget_iff _).2 fun C H => by
    rw [A.outLaw_compose_toAdaptive C H]
    exact h.outLaw_compose_none C H

/-- The composed registers of `A` placed in those of its embedding, with the query counter at its
final value. -/
def cwLift (v : A.toKindAlg.CW C) : A.toAdaptive.toKindAlg.CW C :=
  A.toKindAlg.cwLift C A.querySlots (cntAt A.sched A.slots) v

omit [Nonempty X] [AddGroup Y] [Nonempty Y] in
theorem cwLift_injective : Function.Injective (A.cwLift C) :=
  A.toKindAlg.cwLift_injective C _ _

/-- **The embedding keeps the law of all composed registers**: the output law of the composition
of the embedding with the challenger, reading all composed registers, is the image of that of `A`
under placing the final query counter. -/
theorem outLaw_composeBothOut_toAdaptive (H : X → Y) :
    (A.toAdaptive.toKindAlg.composeBothOut C id).outLaw H =
      ((A.composeOut C id).outLaw H).map (Option.map (A.cwLift C)) := by
  classical
  refine PMF.ext_of_some fun v' => ?_
  rw [KindAlg.outLaw_composeBothOut_some, PMF.map_apply, tsum_fintype, Fintype.sum_option]
  simp only [Option.map_none, reduceCtorEq, if_false, zero_add, Option.map_some, Option.some.injEq]
  have hrun : ∀ c, (∑ r : A.toAdaptive.toKindAlg.G,
      if id (A.toAdaptive.toKindAlg.emb C H c A.toAdaptive.toKindAlg.slots r).1 = v' then
        (A.toAdaptive.toKindAlg.mgRun C.toPureEnv (H, c) true r r).re else 0) =
      ∑ r : A.toKindAlg.G, if A.cwLift C (A.toKindAlg.emb C H c A.slots r).1 = v' then
        (A.toKindAlg.mgRun C.toPureEnv (H, c) true r r).re else 0 := by
    intro c
    rw [show A.toAdaptive.toKindAlg.mgRun C.toPureEnv (H, c) true = _ from
      A.toKindAlg.mgRun_toAdaptive C (A.respects C) A.suppIn_mgInit_cnt H c]
    have h := embed_diag_of_injective (A.toKindAlg.placeCnt_injective A.querySlots
      (cntAt A.sched A.slots)) (A.toKindAlg.mgRun C.toPureEnv (H, c) true)
      (fun i => if (A.toAdaptive.toKindAlg.emb C H c A.slots i).1 = v' then 1 else 0)
    simp only [boole_mul] at h
    exact h
  simp only [hrun]
  by_cases hv : ∃ v, A.cwLift C v = v'
  · obtain ⟨v, rfl⟩ := hv
    rw [Finset.sum_eq_single v (fun u _ hu => if_neg fun h => hu ((A.cwLift_injective C) h).symm)
      (by simp), if_pos rfl, outLaw_composeOut_some]
    congr 1
    refine Finset.sum_congr rfl fun c _ => ?_
    congr 1
    refine Finset.sum_congr rfl fun r _ => ?_
    simp only [id, (A.cwLift_injective C).eq_iff]
  · rw [Finset.sum_eq_zero fun u _ => if_neg fun h => hv ⟨u, h.symm⟩]
    rw [Finset.sum_eq_zero fun c _ => by
      rw [Finset.sum_eq_zero fun r _ => if_neg fun h => hv ⟨_, h⟩, mul_zero]]
    simp

/-- **The embedding keeps the law of all composed registers and the oracle**, up to placing the
final query counter. -/
theorem realLaw_composeBothOut_toAdaptive {B : Type} (e : Y ≃ B) :
    (A.toAdaptive.toKindAlg.composeBothOut C id).realLaw e =
      ((A.composeOut C id).realLaw e).map fun p => ⟨p.out.map (A.cwLift C), p.oracle⟩ := by
  simp only [Alg.realLaw, PMF.map_bind, A.outLaw_composeBothOut_toAdaptive C, PMF.map_comp]
  rfl

end IAlg

namespace QueryBoundedAdversary

variable {X Y Req Resp O : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp] [Nonempty X] [AddGroup Y]
  [Nonempty Y]

/-- **Trace-preserving fixed-schedule adversaries as a `t`-query adversary** (the paper's
`def:adversary`): the auxiliary input `aux`, at each value the embedding `IAlg.toAdaptive` of
`alg a`, whose steps are channels (`IAlg.toAdaptive_tracePreserving`), which stays within its
budget (`IAlg.TracePreserving.toAdaptive_withinBudget`) and which makes the queries of `alg a`. -/
noncomputable def ofIAlg {Aux : Type} (aux : PMF Aux) (alg : Aux → IAlg X Y Req Resp O)
    (htp : ∀ a, (alg a).TracePreserving) {t : ℕ}
    (hq : ∀ a, (alg a).width * ((alg a).querySlots + (alg a).post) ≤ t) :
    QueryBoundedAdversary X Y Req Resp O t where
  Aux := Aux
  aux := aux
  alg a := (alg a).toAdaptive
  tracePreserving a := (alg a).toAdaptive_tracePreserving (htp a)
  withinBudget a := (htp a).toAdaptive_withinBudget
  queries_le a := hq a

end QueryBoundedAdversary

end GordieHowe.Quantum
