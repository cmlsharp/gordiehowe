-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.QROM.QueryCountExpand
public import GordieHowe.Model.QROM.ExpandAt

@[expose] public section

/-!
# The per-branch count of an adversary with an inserted expansion

The expansion inserted after step `sp` of `𝒜` (`expandAt e E K 𝒜 sp κ`, `GordieHowe/Model/QROM/ExpandAt.lean`)
runs `𝒜` up to its step `sp` with fresh registers beside its work register, makes `K` classical
queries, and runs the rest of `𝒜`. If every branch of `𝒜` queries at no more than `b` of its steps
(`QueryCount`), and every query of `𝒜` from `sp` on is a record (`hpost`), every branch of the
inserted expansion queries at no more than `b + K` (`QueryCount.expandAt`): before step `sp` the
run is `𝒜`'s with the fresh registers appended, as for `expandAdv`
(`GordieHowe/Model/QROM/QueryCountExpand.lean`); from step `sp` on every query is counted, the classical steps of
the expansion keep `𝒜`'s work register, and `𝒜`'s later steps keep its supports.
-/

open Finset GordieHowe.Quantum
open scoped BigOperators

namespace GordieHowe.QROM

open ExpandAdv ExpandAt

variable {m : ℕ} {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  {B : Type} (e : BitStr I J ≃ B) (K : ℕ)

section ExpandAt

variable {B' C C' : Type} (e' : BitStr I J ≃ B') (E : Expansion (Bits m) B' C) {t : ℕ}
  (𝒜 : QueryAlg (Bits m) (BitStr I J) t C') (sp : ℕ) (κ : 𝒜.W → C)

/-! ### The classical steps keep the work register -/

theorem stashPerm_fst (r : ExpBasis (X := Bits m) (Y := BitStr I J) K 𝒜.W) :
    (stashPerm K r).1.1 = r.1.1 :=
  rfl

theorem recordPerm_fst (j : ℕ) (r : ExpBasis (X := Bits m) (Y := BitStr I J) K 𝒜.W) :
    (recordPerm K j r).1.1 = r.1.1 := by
  unfold recordPerm
  split_ifs <;> rfl

theorem openPerm_fst (r : ExpBasis (X := Bits m) (Y := BitStr I J) K 𝒜.W) :
    (openPerm e' E K κ r).1.1 = r.1.1 := by
  unfold openPerm
  rw [Equiv.trans_apply]
  split_ifs <;> rfl

theorem closePerm_fst (r : ExpBasis (X := Bits m) (Y := BitStr I J) K 𝒜.W) :
    (closePerm e' E K κ r).1.1 = r.1.1 := by
  unfold closePerm
  rw [Equiv.trans_apply, Equiv.trans_apply]
  change (stashPerm K (unmovePerm e' E K κ (recordPerm K (K - 1) r))).1.1 = r.1.1
  rw [stashPerm_fst]
  exact recordPerm_fst K 𝒜 (K - 1) r

theorem expPerm_fst' (i : ℕ) (r : ExpBasis (X := Bits m) (Y := BitStr I J) K 𝒜.W) :
    (expPerm e' E K κ i r).1.1 = r.1.1 := by
  cases i with
  | zero => rfl
  | succ i =>
    simp only [expPerm, Equiv.trans_apply]
    exact recordPerm_fst K 𝒜 i r

/-- A basis permutation that keeps `𝒜`'s work register keeps every support of it. -/
theorem permOp_supported_fst {π : Equiv.Perm (ExpBasis (X := Bits m) (Y := BitStr I J) K 𝒜.W)}
    (hπ : ∀ r, (π r).1.1 = r.1.1) {S : Set 𝒜.W}
    {v : QState (ExpBasis (X := Bits m) (Y := BitStr I J) K 𝒜.W)}
    (hv : Supported {r | r.1.1 ∈ S} v) : Supported {r | r.1.1 ∈ S} (permOp π v) :=
  hv.permOp fun r hr => by
    change (π r).1.1 ∈ S
    rw [hπ]
    exact hr

/-- **`𝒜`'s lifted step keeps a support of `𝒜`'s work register** that its step keeps, whatever
the contents of the expansion's registers. -/
theorem lift_supported_any {S S' : Set 𝒜.W}
    {U : QState (QueryReg 𝒜.W 1 (Bits m) (BitStr I J)) ≃ₗᵢ[ℂ] QState (QueryReg 𝒜.W 1 (Bits m) (BitStr I J))}
    (hU : ∀ u, Supported {r | r.1 ∈ S} u → Supported {r | r.1 ∈ S'} (U u))
    {v : QState (ExpBasis (X := Bits m) (Y := BitStr I J) K 𝒜.W)}
    (hv : Supported {r | r.1.1 ∈ S} v) :
    Supported {r | r.1.1 ∈ S'} (lift K U v) := by
  intro r hr
  change ((relabel (registerSplit K 𝒜.W)).symm
    (controlled (fun _ => U) (relabel (registerSplit K 𝒜.W) v))) r = 0
  rw [relabel_symm, relabel_apply]
  change controlled (fun _ => U) (relabel (registerSplit K 𝒜.W) v)
    ((registerSplit K 𝒜.W).symm.symm r) = 0
  rw [Equiv.symm_symm]
  obtain ⟨⟨w, f⟩, q⟩ := r
  change controlled (fun _ => U) (relabel (registerSplit K 𝒜.W) v) ((w, q), f) = 0
  rw [controlled_apply]
  refine hU _ (fun r' hr' => ?_) (w, q) hr
  change relabel (registerSplit K 𝒜.W) v (r', f) = 0
  rw [relabel_apply]
  exact hv _ hr'

/-! ### The steps -/

theorem stepAt_expandAt (i : ℕ) (hi : i < t + K + 1) :
    ((expandAt e' E K 𝒜 sp κ).toOracleAlg ∅).stepAt () i = expAtStep e' E K 𝒜 sp κ i := by
  rw [OracleAlg.stepAt_of_lt _ hi]
  rfl

/-- `𝒜`'s step `j < sp`, lifted to the inserted expansion, on the simulated run with the fresh
registers appended. -/
theorem simStepS_expandAt_appendS {s j : ℕ} (hj : j < sp) (hjt : j < t + K + 1)
    (v : QState (SimRegister 𝒜.W I J m s)) :
    simStepS (expandAt e' E K 𝒜 sp κ) s j (appendS K v) = appendS K (simStepS 𝒜 s j v) := by
  have hstep : ((expandAt e' E K 𝒜 sp κ).toOracleAlg ∅).stepAt () j =
      lift K ((𝒜.toOracleAlg ∅).stepAt () j) := by
    rw [stepAt_expandAt K e' E 𝒜 sp κ j hjt]
    unfold expAtStep
    rw [if_pos hj]
  ext ⟨r, d⟩
  have key : ((expandAt e' E K 𝒜 sp κ).toOracleAlg ∅).stepAt () j
      (WithLp.toLp 2 fun i => appendS K v (i, d)) =
      ExpandAdv.embed K ((𝒜.toOracleAlg ∅).stepAt () j (WithLp.toLp 2 fun i => v (i, d))) := by
    rw [hstep]
    have hslice : (WithLp.toLp 2 fun i => appendS K v (i, d) :
        QState (ExpBasis (X := Bits m) (Y := BitStr I J) K 𝒜.W)) =
        ExpandAdv.embed K (WithLp.toLp 2 fun i => v (i, d)) := by
      ext ⟨⟨w, f⟩, q⟩
      rfl
    exact (congrArg (lift K ((𝒜.toOracleAlg ∅).stepAt () j)) hslice).trans (lift_embed K _ _)
  exact congrArg (fun x => x r) key

theorem simQuery_appendS_expandAt {s : ℕ} (v : QState (SimRegister 𝒜.W I J m s)) :
    (simQuery e (expandAt e' E K 𝒜 sp κ).W s (appendS K v) :
      QState (SimRegister (expandAt e' E K 𝒜 sp κ).W I J m s)) = appendS K (simQuery e 𝒜.W s v) :=
  simQuery_appendS e K v

theorem dbProj_appendS_expandAt {s : ℕ} (P : Set (DB (Bits m) B))
    (v : QState (SimRegister 𝒜.W I J m s)) :
    (dbProj e (expandAt e' E K 𝒜 sp κ).W s P (appendS K v) :
      QState (SimRegister (expandAt e' E K 𝒜 sp κ).W I J m s)) = appendS K (dbProj e 𝒜.W s P v) :=
  dbProj_appendS e K P v

/-! ### The certificate -/

variable {e 𝒜} {b : ℕ} (h : QueryCount e 𝒜 b)

/-- The records of the inserted expansion: `𝒜`'s before step `sp`, every query from there on. -/
def atC : ℕ → Set (expandAt e' E K 𝒜 sp κ).W :=
  fun i => if i < sp then {w | w.1 ∈ h.C i} else Set.univ

/-- The supports of the inserted expansion: `𝒜`'s with the fresh registers before step `sp`; `𝒜`'s
support at `sp` during the expansion; `𝒜`'s, shifted by `K`, after it. -/
def atG : ℕ → Set (expandAt e' E K 𝒜 sp κ).W :=
  fun k => if k < sp then {w | w.1 ∈ h.G k ∧ w.2 = fresh K}
    else if k < sp + K then {w | w.1 ∈ h.G sp} else {w | w.1 ∈ h.G (k - K)}

/-- The vectors of the simulated run of the inserted expansion: `𝒜`'s with the fresh registers
appended, before step `sp`. -/
def atInv (s : ℕ) : ℕ → Set (QState (SimRegister (expandAt e' E K 𝒜 sp κ).W I J m s)) :=
  fun k => if k < sp then
    {v | ∃ u ∈ h.Inv s k, (appendS K u : QState (SimRegister (expandAt e' E K 𝒜 sp κ).W I J m s)) = v}
  else Set.univ

theorem countBelow_atC (n : ℕ) (w : (expandAt e' E K 𝒜 sp κ).W) :
    countBelow (atC K e' E sp κ h) n w = countBelow h.C (min n sp) w.1 + (n - sp) := by
  induction n with
  | zero => simp [countBelow_zero]
  | succ n ih =>
    rw [countBelow_succ, ih]
    by_cases hn : n < sp
    · rw [min_eq_left (by omega : n + 1 ≤ sp), min_eq_left hn.le, countBelow_succ]
      rw [show atC K e' E sp κ h n = {w | w.1 ∈ h.C n} from if_pos hn]
      have h1 : n + 1 - sp = 0 := by omega
      have h2 : n - sp = 0 := by omega
      rw [h1, h2]
      by_cases hc : w.1 ∈ h.C n <;> simp [hc]
    · rw [min_eq_right (by omega : sp ≤ n + 1), min_eq_right (by omega : sp ≤ n)]
      rw [show atC K e' E sp κ h n = Set.univ from if_neg hn]
      simp only [Set.mem_univ, if_true]
      omega

theorem atG_of_lt {k : ℕ} (hk : k < sp) :
    atG K e' E sp κ h k = {w | w.1 ∈ h.G k ∧ w.2 = fresh K} :=
  if_pos hk

theorem atG_of_mid {k : ℕ} (hk : sp ≤ k) (hk' : k < sp + K) :
    atG K e' E sp κ h k = {w | w.1 ∈ h.G sp} := by
  unfold atG
  rw [if_neg (by omega), if_pos hk']

theorem atG_of_ge {k : ℕ} (hk : sp + K ≤ k) :
    atG K e' E sp κ h k = {w | w.1 ∈ h.G (k - K)} := by
  unfold atG
  rw [if_neg (by omega), if_neg (by omega)]

/-- On the supports from step `sp` on, `𝒜`'s work register lies in `h.G` at the index of `𝒜`'s next
query. -/
theorem atG_fst_of_ge {k : ℕ} (hk : sp ≤ k) {w : (expandAt e' E K 𝒜 sp κ).W}
    (hw : w ∈ atG K e' E sp κ h k) : w.1 ∈ h.G (if k < sp + K then sp else k - K) := by
  split_ifs with h1
  · rwa [atG_of_mid K e' E sp κ h hk h1] at hw
  · rwa [atG_of_ge K e' E sp κ h (by omega)] at hw

variable (hsp : sp ≤ t)
include hsp

theorem expandAt_init :
    Supported {r | r.1 ∈ atG K e' E sp κ h 0}
      (((expandAt e' E K 𝒜 sp κ).toOracleAlg ∅).stepAt () 0 (expandAt e' E K 𝒜 sp κ).init) := by
  rw [stepAt_expandAt K e' E 𝒜 sp κ 0 (by omega)]
  have hemb : Supported {r : ExpBasis (X := Bits m) (Y := BitStr I J) K 𝒜.W |
      r.1.1 ∈ h.G 0 ∧ r.1.2 = fresh K} (lift K ((𝒜.toOracleAlg ∅).stepAt () 0) (ExpandAdv.embed K 𝒜.init)) := by
    rw [lift_embed]
    exact (embed_supported K 𝒜 h.init).mono fun _ h => ⟨h.1, h.2⟩
  by_cases h0 : 0 < sp
  · simp only [expAtStep, if_pos h0]
    refine hemb.mono fun r hr => ?_
    change r.1 ∈ atG K e' E sp κ h 0
    rw [atG_of_lt K e' E sp κ h h0]
    exact hr
  · have hsp0 : sp = 0 := by omega
    simp only [expAtStep, if_neg h0, if_pos hsp0.symm]
    have hl := hemb.mono (fun r (hr : r.1.1 ∈ h.G 0 ∧ r.1.2 = fresh K) => hr.1)
    rw [← congrArg ((𝒜.toOracleAlg ∅).stepAt ()) hsp0] at hl
    refine (permOp_supported_fst K 𝒜 (fun r => ?_) hl).mono fun r hr => ?_
    · split_ifs
      · rw [Equiv.trans_apply, closePerm_fst, openPerm_fst]
      · exact openPerm_fst K e' E 𝒜 κ r
    · change r.1 ∈ atG K e' E sp κ h 0
      have hw := atG_fst_of_ge (K := K) (e' := e') (E := E) (sp := sp) (κ := κ) (h := h)
        (k := 0) (by omega) (w := r.1)
      unfold atG
      rw [if_neg (by omega)]
      split_ifs with hK
      · show r.1.1 ∈ h.G sp
        rw [hsp0]
        exact hr
      · show r.1.1 ∈ h.G (0 - K)
        rw [Nat.zero_sub]
        exact hr

theorem expandAt_stepG {k : ℕ} (hk : k < t + K)
    {v : QState (QueryReg (expandAt e' E K 𝒜 sp κ).W 1 (Bits m) (BitStr I J))}
    (hv : Supported {r | r.1 ∈ atG K e' E sp κ h k} v) :
    Supported {r | r.1 ∈ atG K e' E sp κ h (k + 1)}
      (((expandAt e' E K 𝒜 sp κ).toOracleAlg ∅).stepAt () (k + 1) v) := by
  rw [stepAt_expandAt K e' E 𝒜 sp κ (k + 1) (by omega)]
  by_cases h1 : k + 1 < sp
  · have hk' : k < sp := by omega
    simp only [expAtStep, if_pos h1]
    have hv' : Supported {r : ExpBasis (X := Bits m) (Y := BitStr I J) K 𝒜.W |
        r.1.1 ∈ h.G k ∧ r.1.2 = fresh K} v := fun r hr => hv r fun h' => hr (by
          have h'' : r.1 ∈ atG K e' E sp κ h k := h'
          rwa [atG_of_lt K e' E sp κ h hk'] at h'')
    refine (lift_supported K (fun u hu => h.stepG k (by omega) u hu) hv').mono fun r hr => ?_
    change r.1 ∈ atG K e' E sp κ h (k + 1)
    rw [atG_of_lt K e' E sp κ h h1]
    exact hr
  by_cases h2 : k + 1 = sp
  · have hk' : k < sp := by omega
    simp only [expAtStep, if_neg h1, if_pos h2]
    have hv' : Supported {r : ExpBasis (X := Bits m) (Y := BitStr I J) K 𝒜.W |
        r.1.1 ∈ h.G k ∧ r.1.2 = fresh K} v := fun r hr => hv r fun h' => hr (by
          have h'' : r.1 ∈ atG K e' E sp κ h k := h'
          rwa [atG_of_lt K e' E sp κ h hk'] at h'')
    have hl := (lift_supported K (fun u hu => h.stepG k (by omega) u hu) hv').mono
      (fun r (hr : r.1.1 ∈ h.G (k + 1) ∧ r.1.2 = fresh K) => hr.1)
    rw [congrArg ((𝒜.toOracleAlg ∅).stepAt ()) h2] at hl
    have hl' := permOp_supported_fst K 𝒜 (π := if K = 0 then (openPerm e' E K κ).trans
      (closePerm e' E K κ) else openPerm e' E K κ) (fun r => by
        split_ifs
        · rw [Equiv.trans_apply, closePerm_fst, openPerm_fst]
        · exact openPerm_fst K e' E 𝒜 κ r) hl
    refine Supported.mono (hl'.mono fun r hr => ?_) fun _ h => h
    change r.1 ∈ atG K e' E sp κ h (k + 1)
    unfold atG
    rw [if_neg (by omega)]
    split_ifs with hK
    · show r.1.1 ∈ h.G sp
      rw [← h2]
      exact hr
    · show r.1.1 ∈ h.G (k + 1 - K)
      rw [show k + 1 - K = k + 1 by omega]
      exact hr
  have hk' : sp ≤ k := by omega
  have hvf : Supported {r : ExpBasis (X := Bits m) (Y := BitStr I J) K 𝒜.W |
      r.1.1 ∈ h.G (if k < sp + K then sp else k - K)} v := fun r hr => hv r fun h' =>
    hr (atG_fst_of_ge K e' E sp κ h hk' h')
  by_cases h3 : k + 1 < sp + K
  · simp only [expAtStep, if_neg h1, if_neg h2, if_pos h3]
    rw [if_pos (by omega)] at hvf
    refine (permOp_supported_fst K 𝒜 (expPerm_fst' K e' E 𝒜 κ _) hvf).mono fun r hr => ?_
    change r.1 ∈ atG K e' E sp κ h (k + 1)
    rw [atG_of_mid K e' E sp κ h (by omega) h3]
    exact hr
  by_cases h4 : k + 1 = sp + K
  · simp only [expAtStep, if_neg h1, if_neg h2, if_neg h3, if_pos h4]
    rw [if_pos (by omega)] at hvf
    refine (permOp_supported_fst K 𝒜 (closePerm_fst K e' E 𝒜 κ) hvf).mono fun r hr => ?_
    change r.1 ∈ atG K e' E sp κ h (k + 1)
    rw [atG_of_ge K e' E sp κ h (by omega), show k + 1 - K = sp by omega]
    exact hr
  · simp only [expAtStep, if_neg h1, if_neg h2, if_neg h3, if_neg h4]
    rw [if_neg (by omega)] at hvf
    have hidx : k + 1 - K = k - K + 1 := by omega
    have hl := lift_supported_any K 𝒜 (fun u hu => h.stepG (k - K) (by omega) u hu) hvf
    rw [← hidx] at hl
    refine hl.mono fun r hr => ?_
    change r.1 ∈ atG K e' E sp κ h (k + 1)
    rw [atG_of_ge K e' E sp κ h (by omega)]
    exact hr

/-- **A step of the inserted expansion keeps a record `T` of `𝒜`'s work register** before step
`sp` that `𝒜`'s steps keep. -/
theorem expandAt_stepKeep {T : Set 𝒜.W} {k : ℕ} (hk : k < t + K)
    (hT : ∀ j, j ≤ t → j = (if k + 1 ≤ sp then k + 1 else k + 1 - K) → 0 < j →
      (k + 1 ≤ sp ∨ sp + K < k + 1) →
      ∀ u, Supported {r | r.1 ∈ T ∩ h.G (j - 1)} u →
        Supported {r | r.1 ∈ T} ((𝒜.toOracleAlg ∅).stepAt () j u))
    {v : QState (QueryReg (expandAt e' E K 𝒜 sp κ).W 1 (Bits m) (BitStr I J))}
    (hv : Supported {r | r.1.1 ∈ T ∧ r.1 ∈ atG K e' E sp κ h k} v) :
    Supported {r | r.1.1 ∈ T} (((expandAt e' E K 𝒜 sp κ).toOracleAlg ∅).stepAt () (k + 1) v) := by
  rw [stepAt_expandAt K e' E 𝒜 sp κ (k + 1) (by omega)]
  by_cases h1 : k + 1 ≤ sp
  · have hk' : k < sp := by omega
    have hv' : Supported {r : ExpBasis (X := Bits m) (Y := BitStr I J) K 𝒜.W |
        r.1.1 ∈ T ∩ h.G k ∧ r.1.2 = fresh K} v := fun r hr => hv r fun h' => hr (by
          have h'' : r.1 ∈ atG K e' E sp κ h k := h'.2
          rw [atG_of_lt K e' E sp κ h hk'] at h''
          exact ⟨⟨h'.1, h''.1⟩, h''.2⟩)
    have hl := lift_supported K (hT (k + 1) (by omega) (by rw [if_pos h1]) (by omega)
      (Or.inl h1)) hv'
    by_cases h2 : k + 1 < sp
    · simp only [expAtStep, if_pos h2]
      exact hl.mono fun _ h => h.1
    · have h3 : k + 1 = sp := by omega
      simp only [expAtStep, if_neg h2, if_pos h3]
      rw [congrArg ((𝒜.toOracleAlg ∅).stepAt ()) h3] at hl
      have hl' := permOp_supported_fst K 𝒜 (π := if K = 0 then (openPerm e' E K κ).trans
        (closePerm e' E K κ) else openPerm e' E K κ) (fun r => by
          split_ifs
          · rw [Equiv.trans_apply, closePerm_fst, openPerm_fst]
          · exact openPerm_fst K e' E 𝒜 κ r) (hl.mono fun _ h => h.1)
      exact hl'
  · have hk' : sp ≤ k := by omega
    have hv1 : Supported {r : ExpBasis (X := Bits m) (Y := BitStr I J) K 𝒜.W | r.1.1 ∈ T} v :=
      hv.mono fun _ h => h.1
    simp only [expAtStep, if_neg (show ¬ k + 1 < sp by omega), if_neg (show ¬ k + 1 = sp by omega)]
    split_ifs with h3 h4
    · exact permOp_supported_fst K 𝒜 (expPerm_fst' K e' E 𝒜 κ _) hv1
    · exact permOp_supported_fst K 𝒜 (closePerm_fst K e' E 𝒜 κ) hv1
    · have hidx : k + 1 - K = k - K + 1 := by omega
      have hvf : Supported {r : ExpBasis (X := Bits m) (Y := BitStr I J) K 𝒜.W |
          r.1.1 ∈ T ∩ h.G (k + 1 - K - 1)} v := fun r hr => hv r fun h' => hr (by
            have h'' := atG_fst_of_ge K e' E sp κ h hk' h'.2
            rw [if_neg (by omega)] at h''
            refine ⟨h'.1, ?_⟩
            rwa [show k + 1 - K - 1 = k - K by omega])
      exact lift_supported_any K 𝒜 (hT (k + 1 - K) (by omega) (by rw [if_neg h1]) (by omega)
        (Or.inr (by omega))) hvf

variable (hpost : ∀ i, sp ≤ i → i < t → h.C i = Set.univ)
include hpost

/-- With every query of `𝒜` from `sp` on a record, the records below `n ≥ sp` are those below `sp`
and `n − sp`. -/
theorem countBelow_post {n : ℕ} (hn : sp ≤ n) (hnt : n ≤ t) (w : 𝒜.W) :
    countBelow h.C n w = countBelow h.C sp w + (n - sp) := by
  induction n with
  | zero =>
    have : sp = 0 := by omega
    subst this
    rfl
  | succ n ih =>
    by_cases hn' : sp ≤ n
    · rw [countBelow_succ, ih hn' (by omega), hpost n hn' (by omega)]
      simp only [Set.mem_univ, if_true]
      omega
    · have : sp = n + 1 := by omega
      subst this
      simp

theorem expandAt_count : ∀ k ≤ t + K, ∀ w ∈ atG K e' E sp κ h k,
    countBelow (atC K e' E sp κ h) (min (k + 1) (t + K)) w ≤ b + K := by
  intro k hk w hw
  rw [countBelow_atC]
  by_cases hks : k < sp
  · rw [atG_of_lt K e' E sp κ h hks] at hw
    have hc := h.count k (by omega) w.1 hw.1
    rw [min_eq_left (by omega : k + 1 ≤ t)] at hc
    rw [min_eq_left (by omega : k + 1 ≤ t + K), min_eq_left (by omega : k + 1 ≤ sp)]
    omega
  · rw [min_eq_right (by omega : sp ≤ min (k + 1) (t + K))]
    by_cases hkm : k < sp + K
    · rw [atG_of_mid K e' E sp κ h (by omega) hkm] at hw
      have hc := h.count sp hsp w.1 hw
      have h1 : countBelow h.C sp w.1 ≤ countBelow h.C (min (sp + 1) t) w.1 :=
        countBelow_mono _ (by omega) _
      have h2 : min (k + 1) (t + K) - sp ≤ K := by omega
      omega
    · rw [atG_of_ge K e' E sp κ h (by omega)] at hw
      have hc := h.count (k - K) (by omega) w.1 hw
      rw [countBelow_post (h := h) (n := min (k - K + 1) t) (sp := sp) (hsp := hsp) (hpost := hpost) (by omega) (by omega)] at hc
      have : min (k + 1) (t + K) - sp = min (k - K + 1) t - sp + K := by omega
      omega

omit hpost in
theorem expandAt_inv_init (s : ℕ) :
    simStepS (expandAt e' E K 𝒜 sp κ) s 0 (simInitS e (expandAt e' E K 𝒜 sp κ) s) ∈
      atInv K e' E sp κ h s 0 := by
  unfold atInv
  split_ifs with h0
  · have hinit : simInitS e (expandAt e' E K 𝒜 sp κ) s = appendS K (simInitS e 𝒜 s) := by
      ext ⟨⟨⟨w, f⟩, q⟩, d⟩
      change (𝒜.init (w, q) * (if f = fresh K then 1 else 0)) *
          (if d = dbSlots e s (∅ : DB (Bits m) B) then 1 else 0) =
        (𝒜.init (w, q) * (if d = dbSlots e s (∅ : DB (Bits m) B) then 1 else 0)) *
          (if f = fresh K then 1 else 0)
      ring
    rw [hinit, simStepS_expandAt_appendS K e' E 𝒜 sp κ h0 (by omega)]
    exact ⟨_, h.inv_init s, rfl⟩
  · trivial

omit hpost in
theorem expandAt_inv_step (s : ℕ) {k : ℕ} (hk : k < t + K)
    {v : QState (SimRegister (expandAt e' E K 𝒜 sp κ).W I J m s)} (hv : v ∈ atInv K e' E sp κ h s k) :
    simStepS (expandAt e' E K 𝒜 sp κ) s (k + 1) (simQuery e _ s v) ∈
      atInv K e' E sp κ h s (k + 1) := by
  unfold atInv at hv ⊢
  by_cases h2 : k + 1 < sp
  · rw [if_pos h2]
    rw [if_pos (by omega : k < sp)] at hv
    obtain ⟨u, hu, rfl⟩ := hv
    refine ⟨_, h.inv_step s k (by omega) _ hu, ?_⟩
    rw [simQuery_appendS_expandAt, simStepS_expandAt_appendS K e' E 𝒜 sp κ h2 (by omega)]
  · rw [if_neg h2]
    trivial

omit hpost hsp in
theorem expandAt_inv_dbProj (s k : ℕ) (P : Set (DB (Bits m) B))
    (v : QState (SimRegister (expandAt e' E K 𝒜 sp κ).W I J m s)) (hv : v ∈ atInv K e' E sp κ h s k) :
    dbProj e _ s P v ∈ atInv K e' E sp κ h s k := by
  unfold atInv at hv ⊢
  by_cases h1 : k < sp
  · rw [if_pos h1] at hv ⊢
    obtain ⟨u, hu, rfl⟩ := hv
    rw [dbProj_appendS_expandAt]
    exact ⟨_, h.inv_dbProj s k P u hu, rfl⟩
  · rw [if_neg h1]
    trivial

omit hpost in
theorem expandAt_pad (s : ℕ) {k : ℕ} (hk : k < t + K)
    {v : QState (SimRegister (expandAt e' E K 𝒜 sp κ).W I J m s)} (hv : v ∈ atInv K e' E sp κ h s k) :
    simQuery e (expandAt e' E K 𝒜 sp κ).W s
        (mask (workSet (expandAt e' E K 𝒜 sp κ).W s (atC K e' E sp κ h k))ᶜ v) =
      mask (workSet (expandAt e' E K 𝒜 sp κ).W s (atC K e' E sp κ h k))ᶜ v := by
  by_cases h1 : k < sp
  · have hv' := hv
    unfold atInv at hv'
    rw [if_pos h1] at hv'
    obtain ⟨u, hu, hvu⟩ := hv'
    have hvb : ∀ b, v b = u ((b.1.1.1, b.1.2), b.2) * (if b.1.1.2 = fresh K then 1 else 0) :=
      fun b => by rw [← hvu]; rfl
    have hb : ∀ b : SimRegister (expandAt e' E K 𝒜 sp κ).W I J m s,
        b ∈ (workSet (expandAt e' E K 𝒜 sp κ).W s (atC K e' E sp κ h k))ᶜ ↔ b.1.1.1 ∉ h.C k := by
      intro b
      change ¬ b.1.1 ∈ atC K e' E sp κ h k ↔ _
      rw [show atC K e' E sp κ h k = {w | w.1 ∈ h.C k} from if_pos h1]
      rfl
    have e1 : mask (workSet (expandAt e' E K 𝒜 sp κ).W s (atC K e' E sp κ h k))ᶜ v =
        (appendS K (mask (workSet 𝒜.W s (h.C k))ᶜ u) :
          QState (SimRegister (expandAt e' E K 𝒜 sp κ).W I J m s)) := by
      ext b
      by_cases hc : b.1.1.1 ∈ h.C k
      · rw [mask_apply_of_notMem _ (fun h' => ((hb b).1 h') hc)]
        change 0 = (mask (workSet 𝒜.W s (h.C k))ᶜ u) ((b.1.1.1, b.1.2), b.2) * _
        rw [mask_apply_of_notMem _ (show ((b.1.1.1, b.1.2), b.2) ∉ (workSet 𝒜.W s (h.C k))ᶜ from
          fun h' => h' hc)]
        simp
      · rw [mask_apply_of_mem _ ((hb b).2 hc), hvb]
        change _ = (mask (workSet 𝒜.W s (h.C k))ᶜ u) ((b.1.1.1, b.1.2), b.2) * _
        rw [mask_apply_of_mem _ (show ((b.1.1.1, b.1.2), b.2) ∈ (workSet 𝒜.W s (h.C k))ᶜ from hc)]
    rw [e1, simQuery_appendS_expandAt, h.pad s k (by omega) u hu]
  · have h0 : mask (workSet (expandAt e' E K 𝒜 sp κ).W s (atC K e' E sp κ h k))ᶜ v = 0 := by
      ext b
      rw [mask_apply_of_notMem]
      · rfl
      · intro hb
        apply hb
        change b.1.1 ∈ atC K e' E sp κ h k
        rw [show atC K e' E sp κ h k = Set.univ from if_neg h1]
        trivial
    rw [h0, map_zero]

/-- **The per-branch count of the inserted expansion** (`QueryCount`, our construction): if every
branch of `𝒜` queries at no more than `b` of its steps and every query of `𝒜` from step `sp` on is
a record, every branch of `expandAt e' E K 𝒜 sp κ` queries at no more than `b + K`. -/
noncomputable def QueryCount.expandAt : QueryCount e (QROM.expandAt e' E K 𝒜 sp κ) (b + K) where
  C := atC K e' E sp κ h
  G := atG K e' E sp κ h
  Inv := atInv K e' E sp κ h
  init := expandAt_init K e' E sp κ h hsp
  stepG k hk _ hv := expandAt_stepG K e' E sp κ h hsp hk hv
  stepC i k hik hk _ hv := by
    by_cases hi : i < sp
    · rw [show atC K e' E sp κ h i = {w | w.1 ∈ h.C i} from if_pos hi]
      refine expandAt_stepKeep K e' E sp κ h hsp hk (fun j hj hjk hj0 hcase u hu => ?_)
        (fun r hr => hv r fun h' => hr (by
          have h'' : r.1 ∈ atC K e' E sp κ h i := h'.1
          rw [show atC K e' E sp κ h i = {w | w.1 ∈ h.C i} from if_pos hi] at h''
          exact ⟨h'', h'.2⟩))
      have := h.stepC i (j - 1) (by split_ifs at hjk <;> omega) (by split_ifs at hjk <;> omega) u hu
      rwa [show j - 1 + 1 = j by omega] at this
    · rw [show atC K e' E sp κ h i = Set.univ from if_neg hi]
      exact fun r hr => absurd trivial hr
  stepCc i k hik hk _ hv := by
    by_cases hi : i < sp
    · rw [show atC K e' E sp κ h i = {w | w.1 ∈ h.C i} from if_pos hi]
      refine expandAt_stepKeep K e' E sp κ h hsp (T := (h.C i)ᶜ) hk (fun j hj hjk hj0 hcase u hu => ?_)
        (fun r hr => hv r fun h' => hr (by
          have h'' : r.1 ∈ (atC K e' E sp κ h i)ᶜ := h'.1
          rw [show atC K e' E sp κ h i = {w | w.1 ∈ h.C i} from if_pos hi] at h''
          exact ⟨h'', h'.2⟩))
      have := h.stepCc i (j - 1) (by split_ifs at hjk <;> omega) (by split_ifs at hjk <;> omega) u hu
      rwa [show j - 1 + 1 = j by omega] at this
    · have hv0 : ∀ r, ‹QState (QueryReg _ 1 (Bits m) (BitStr I J))› r = 0 := fun r => hv r (by
        rintro ⟨h1, -⟩
        apply h1
        rw [show atC K e' E sp κ h i = Set.univ from if_neg hi]
        trivial)
      have : ‹QState (QueryReg _ 1 (Bits m) (BitStr I J))› = 0 := by
        ext r
        exact hv0 r
      rw [this, map_zero]
      exact fun _ _ => rfl
  count := expandAt_count K e' E sp κ h hsp hpost
  inv_init := expandAt_inv_init K e' E sp κ h hsp
  inv_step s k hk _ hv := expandAt_inv_step K e' E sp κ h hsp s hk hv
  inv_dbProj s k P v hv := expandAt_inv_dbProj K e' E sp κ h s k P v hv
  pad s k hk _ hv := expandAt_pad K e' E sp κ h hsp s hk hv

end ExpandAt

end GordieHowe.QROM
