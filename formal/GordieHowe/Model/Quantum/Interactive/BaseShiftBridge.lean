-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Interactive.BaseShiftAdds
public import GordieHowe.Model.QROM.ExpandCohTransport
public import GordieHowe.Model.Quantum.Interactive.ReqBridgeExt

@[expose] public section

/-!
# The composition with local queries, read as the composition without them

For a kind algorithm `T` and Kraus maps `st'` that are `T`'s followed by local queries
(`KindAlg.BaseQ`), the expanded coherent run of the composition of `T.withStep st'` with its steps
read after writes `W` has the law of the composition of `T` with its steps read after the writes
followed by the drops `β` of the local queries, one after each query
(`KindShape.BaseQ.simLaw_composeBothOut_transport`).

- `supp_withAnc_flagF`: the initial state has the flag down.
- `KindShape.AddsAt.simLaw_composeBothOut_transport`: for a sorted list of additions
  (`KindAlg.AddsAt`); `KindShape.AddsAt.simLaw_withSteps_transport`: at a base with its Kraus maps
  replaced; `KindShape.BaseQ.simLaw_composeBothOut_transport`: its instance at the local
  queries (`KindShape.BaseQ.toAddsAt`).
-/

open Matrix
open scoped BigOperators ENNReal Kronecker

namespace GordieHowe.Quantum

open GordieHowe.QROM

variable {m : ℕ} {I J B : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  {Y₁ Req Resp O : Type} [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp]
  [AddGroup Y₁] {ksT : KindShape (Bits m) (BitStr I J) Req Resp} {T : KindAlg ksT O}
  {C : Challenger (Bits m) (BitStr I J) Req Resp} (D : T.BaseQ Y₁) (P : T.AddsAt Y₁)
  (ω : Bits m → Y₁)

/-- **The composed initial state has the reprogramming flag down.** -/
theorem supp_withAnc_flagF {V : Type} [Fintype V] [DecidableEq V]
    (ρ : Matrix (QueryReg V 1 (Bits m) (BitStr I J)) (QueryReg V 1 (Bits m) (BitStr I J)) ℂ) :
    Supp (flagF V (Bits m) (BitStr I J)) (withAnc KindAlg.x₀ ρ) := fun a b hab => by
  simp only [withAnc, reprogAnc, ancWeight] at hab
  refine ⟨?_, ?_⟩
  · by_contra h
    simp only [flagF, Set.mem_setOf_eq, Bool.not_eq_false] at h
    apply hab
    simp [h]
  · by_contra h
    simp only [flagF, Set.mem_setOf_eq, Bool.not_eq_false] at h
    apply hab
    simp [h]

/-- A step of a compiled algorithm read after a permutation, as a channel. -/
theorem compiled_precomp_apply {V O' : Type} [Fintype V] [DecidableEq V]
    (c : Circuit (QueryReg V 1 (Bits m) (BitStr I J)))
    (init : MState (QueryReg V 1 (Bits m) (BitStr I J)))
    (out : V → O') (σ : Fin ((c.toAlg init out).depth + 1) →
      Equiv.Perm (QueryReg V 1 (Bits m) (BitStr I J)))
    (i : Fin ((c.toAlg init out).depth + 1)) (ρ : Matrix (QueryReg V 1 (Bits m) (BitStr I J))
      (QueryReg V 1 (Bits m) (BitStr I J)) ℂ) :
    ((c.toAlg init out).precomp σ).step i ρ =
      (c.seg i).K (ρ.submatrix (σ i).symm (σ i).symm) := by
  change ((KrausMap.sigmaEmbed (fun k => c.seg k) i).permConj (σ i) (Equiv.refl _)) ρ = _
  rw [KrausMap.permConj_apply, KrausMap.sigmaEmbed_apply]
  simp

variable [Nonempty (Bits m)]

/-- **The composition with additions after the Kraus maps has the law of the composition without
them, each dropped after its pair's query**: for `st'` the steps of `T` followed by the sorted list
of additions `P` (`hst`), trace preserving (`hTP'`), none after the last step (`hlast`), writes `W`
that commute with every addition (`hW`) and keep the challenger's registers, the ancilla and the
query register (`hWk`), drops `β` that are the additions dropped after each query (`hβ`) and
`W 0 = 1`, `β 0 = 1`: the expanded coherent runs of the composition of `T.withStep st'` read after
`W` and of `T` read after `W` then `β` have the same law. -/
theorem KindShape.AddsAt.simLaw_composeBothOut_transport {C' : Type} (E : Expansion (Bits m) B C')
    (e : BitStr I J ≃ B) (kq : ℕ)
    {st' : StepIdx T.slots T.post → KrausMap T.R (DReg T.W T.width (Bits m) (BitStr I J) Req Resp)
      (DReg T.W T.width (Bits m) (BitStr I J) Req Resp)}
    (hst : ∀ k, KrausMap.LeftPerm (P.toStepAdds.perm ω k) (st' k) (T.step k))
    (hTP : T.StepsTP) (hTP' : (T.withStep st').StepsTP) (hlast : P.Off lastStep)
    (W β : ℕ → Equiv.Perm (ReprogrammedQueryReg (T.CW C) (Bits m) (BitStr I J)))
    (hW0 : W 0 = 1) (hβ0 : β 0 = 1) (hβ : ∀ q : T.QueryPos C, β q.idx = P.dropAt ω q)
    (hW : ∀ n k i pos p, W n (P.liftC ω k i pos p) = P.liftC ω k i pos (W n p))
    (hWk : ∀ n p, (W n p).1.1.chal = p.1.1.chal ∧ (W n p).1.2 = p.1.2 ∧ (W n p).2 = p.2)
    (g : Option (T.CW C) → C') :
    simLaw e (expandAdv e E kq ((((T.withStep st').composeBothOut C id).precomp
        fun j => W j).toQueryAlgCoh.mapOut g)) =
      simLaw e (expandAdv e E kq (((T.composeBothOut C id).precomp
        fun j => (W j).trans (β j)).toQueryAlgCoh.mapOut g)) := by
  have htw := P.twin_fullCircBoth ω hst hlast W β hβ hW hWk
  have hdep : ((T.withStep st').composeBothOut C id).depth = (T.composeBothOut C id).depth := by
    have := htw.queries_eq
    rwa [Circuit.queries_withPerms, Circuit.queries_withPerms] at this
  obtain ⟨P, S, hP0, hS0, hseg, hend, hqs⟩ := htw.segments
  rw [Circuit.queries_withPerms] at hend hqs
  rw [← simLaw_expandAdv_castDepth e E kq
    (((T.withStep st').composeBothOut C id).precomp fun j => W j) _ hdep]
  have hseg' : ∀ (c : Circuit (ReprogrammedQueryReg (T.CW C) (Bits m) (BitStr I J)))
      (π : ℕ → Equiv.Perm (ReprogrammedQueryReg (T.CW C) (Bits m) (BitStr I J))) (hπ : π 0 = 1)
      (i : ℕ) (hi : i ≤ c.queries) (ρ : Matrix _ _ ℂ),
      ((c.withPerms π 0).seg i).K ρ = (c.seg i).K (ρ.submatrix (π i).symm (π i).symm) :=
    fun c π hπ i hi ρ => by
      rw [Circuit.seg_withPerms π 0 c i hi]
      by_cases h0 : i = 0
      · subst h0
        rw [if_pos rfl, hπ]
        rfl
      · rw [if_neg h0, Nat.zero_add]
  refine simLaw_expandAdv_transport e E kq
    ((T.composeBothOut C id).precomp fun j => (W j).trans (β j))
    (Alg.tracePreserving_precomp (hTP.tracePreserving_composeBothOut C id) _)
    (((((T.withStep st').composeBothOut C id).precomp fun j => W j).castDepth _ hdep).step)
    (tracePreserving_castDepth (Alg.tracePreserving_precomp
      (hTP'.tracePreserving_composeBothOut C id) _) _ hdep)
    P S hP0 hend (fun i ρ hρ => ?_) (fun i ρ hρ => ?_) (fun i hi => (hqs i hi).1)
    (fun i hi => (hqs i hi).2) ?_ g
  · have hi : (i : ℕ) ≤ (T.fullCircBoth C).toCircuit.queries := Nat.lt_succ_iff.1 i.isLt
    have hi' : (i : ℕ) ≤ ((T.withStep st').fullCircBoth C).toCircuit.queries := by
      have := hdep
      change ((T.withStep st').fullCircBoth C).toCircuit.queries =
        (T.fullCircBoth C).toCircuit.queries at this
      omega
    change (((T.withStep st').composeBothOut C id).precomp fun j => W j).step
        (Fin.cast (congrArg (· + 1) hdep.symm) i) (ρ.submatrix (P i).symm (P i).symm) = _
    rw [compiled_precomp_apply, compiled_precomp_apply]
    have h₁ := hseg' _ W hW0 i hi' (ρ.submatrix (P i).symm (P i).symm)
    have h₂ := hseg' _ (fun n => (W n).trans (β n)) (by rw [hW0, hβ0]; rfl) i hi ρ
    simp only [Fin.coe_cast] at h₁ ⊢
    rw [← h₁, ← h₂]
    exact (hseg i).1 ρ hρ
  · have hi : (i : ℕ) ≤ (T.fullCircBoth C).toCircuit.queries := Nat.lt_succ_iff.1 i.isLt
    rw [compiled_precomp_apply]
    have h₂ := hseg' _ (fun n => (W n).trans (β n)) (by rw [hW0, hβ0]; rfl) i hi ρ
    rw [← h₂]
    exact (hseg i).2 ρ hρ
  · rw [hS0]
    exact supp_withAnc_flagF _

/-- **`KindShape.AddsAt.simLaw_composeBothOut_transport` at a base with its Kraus maps replaced by
`s₀`**, the additions, writes and drops indexed by `T`: for `st'` the Kraus maps `s₀` followed by
the sorted list of additions `P` (`hst`), the expanded coherent runs of the composition of
`T.withStep st'` read after `W` and of `T.withStep s₀` read after `W` then `β` have the same
law. -/
theorem KindShape.AddsAt.simLaw_withSteps_transport {C' : Type} (E : Expansion (Bits m) B C')
    (e : BitStr I J ≃ B) (kq : ℕ)
    (s₀ st' : StepIdx T.slots T.post →
      KrausMap T.R (DReg T.W T.width (Bits m) (BitStr I J) Req Resp)
        (DReg T.W T.width (Bits m) (BitStr I J) Req Resp))
    (hst : ∀ k, KrausMap.LeftPerm (P.toStepAdds.perm ω k) (st' k) (s₀ k))
    (hTP : (T.withStep s₀).StepsTP) (hTP' : (T.withStep st').StepsTP) (hlast : P.Off lastStep)
    (W β : ℕ → Equiv.Perm (ReprogrammedQueryReg (T.CW C) (Bits m) (BitStr I J)))
    (hW0 : W 0 = 1) (hβ0 : β 0 = 1) (hβ : ∀ q : T.QueryPos C, β q.idx = P.dropAt ω q)
    (hW : ∀ n k i pos p, W n (P.liftC ω k i pos p) = P.liftC ω k i pos (W n p))
    (hWk : ∀ n p, (W n p).1.1.chal = p.1.1.chal ∧ (W n p).1.2 = p.1.2 ∧ (W n p).2 = p.2)
    (g : Option (T.CW C) → C') :
    simLaw e (expandAdv e E kq ((((T.withStep st').composeBothOut C id).precomp
        fun j => W j).toQueryAlgCoh.mapOut g)) =
      simLaw e (expandAdv e E kq ((((T.withStep s₀).composeBothOut C id).precomp
        fun j => (W j).trans (β j)).toQueryAlgCoh.mapOut g)) := by
  exact KindShape.AddsAt.simLaw_composeBothOut_transport (T := T.withStep s₀) (P := P) ω E e kq
    hst hTP hTP' hlast W β hW0 hβ0 hβ hW hWk g

/-- **The composition with local queries has the law of the composition without them with the
local queries dropped after the queries**: for `st'` the steps of `T` followed by the local
queries (`hst`), trace preserving (`hTP'`), none after the last step (`hlast`), writes `W` that
commute with the pending local queries (`hW`) and keep the challenger's registers, the ancilla and
the query register (`hWk`), drops `β` that are the identity after the challenger's queries (`hβc`)
and the local query of each pair after its query (`hβs`, `hβp`), and `W 0 = 1`, `β 0 = 1`: the
expanded coherent runs of the composition of `T.withStep st'` read after `W` and of `T` read after
`W` then `β` have the same law (the list of additions `KindShape.BaseQ.toAddsAt`). -/
theorem KindShape.BaseQ.simLaw_composeBothOut_transport {C' : Type} (E : Expansion (Bits m) B C')
    (e : BitStr I J ≃ B) (kq : ℕ)
    {st' : StepIdx T.slots T.post → KrausMap T.R (DReg T.W T.width (Bits m) (BitStr I J) Req Resp)
      (DReg T.W T.width (Bits m) (BitStr I J) Req Resp)}
    (hst : ∀ k, KrausMap.LeftPerm (wsAdd D.Lw (D.on k) (D.on_set k) ω Req Resp).perm (st' k)
      (T.step k)) (hTP : T.StepsTP) (hTP' : (T.withStep st').StepsTP)
    (hlast : ∀ w, D.on lastStep w = false)
    (W β : ℕ → Equiv.Perm (ReprogrammedQueryReg (T.CW C) (Bits m) (BitStr I J)))
    (hW0 : W 0 = 1) (hβ0 : β 0 = 1)
    (hβc : ∀ (j : Fin T.slots) (i : Fin C.q), β ((j : ℕ) * (C.q + T.width) + i + 1) = 1)
    (hβs : ∀ (j : Fin T.slots) (i : Fin T.width), β ((j : ℕ) * (C.q + T.width) + C.q + i + 1) =
      D.carry ω (slotStep j) (fun j' => decide (j' = i)) fun _ => .til)
    (hβp : ∀ (b : Fin T.post) (i : Fin T.width),
      β (T.slots * (C.q + T.width) + (b : ℕ) * T.width + i + 1) =
        D.carry ω (postStep b) (fun j' => decide (j' = i)) fun _ => .til)
    (hW : ∀ n k pend pos p, W n (D.carry ω k pend pos p) = D.carry ω k pend pos (W n p))
    (hWk : ∀ n p, (W n p).1.1.chal = p.1.1.chal ∧ (W n p).1.2 = p.1.2 ∧ (W n p).2 = p.2)
    (g : Option (T.CW C) → C') :
    simLaw e (expandAdv e E kq ((((T.withStep st').composeBothOut C id).precomp
        fun j => W j).toQueryAlgCoh.mapOut g)) =
      simLaw e (expandAdv e E kq (((T.composeBothOut C id).precomp
        fun j => (W j).trans (β j)).toQueryAlgCoh.mapOut g)) :=
  D.toAddsAt.simLaw_composeBothOut_transport ω E e kq
    (fun k => by rw [D.toStepAdds_perm]; exact hst k) hTP hTP' (D.toStepAdds_off hlast) W β hW0
    hβ0 (fun q => by
      cases q with
      | chal j i => exact hβc j i
      | pair j i => rw [KindShape.QueryPos.idx, hβs, KindShape.AddsAt.dropAt, D.block_toAddsAt]
      | post b i => rw [KindShape.QueryPos.idx, hβp, KindShape.AddsAt.dropAt, D.block_toAddsAt])
    (fun n k i pos p => by erw [D.liftC_toAddsAt]; exact hW n k _ pos p) hWk g

end GordieHowe.Quantum
