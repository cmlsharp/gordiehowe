-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Ring.MLDSAW1CaseS
public import GordieHowe.Applications.Ring.MLDSAW1KeyFreeBase
public import GordieHowe.Foundations.Probability.SlotGuessUniform

@[expose] public section

/-!
# The guess of case S for the ML-DSA ring publishing `w₁`

The public part and the signature of a slot's request at a side coin (`w1SlotPub`, `w1SlotSig`):
for a tagged signing request `((sign s R m, c), T)`, the published value and base component
`(w₁, v)` and the signature of the key-free signer `w1KFOut` at the base component `ω` read
through the request's table `T`, at that coin; nothing for other requests. The guessing term of
`PMF.tsum_uniform_slots_guess_le` at them is at most `k · T · |BucketVec| / |MaskBox|`
(`sum_iSup_prob_w1KFOut_le`).

- `w1SlotOut`, `w1SlotPub`, `w1SlotSig`: the key-free signer's output, its public part and its
  signature at a slot's request and a coin.
- **`iSup_sum_iSup_w1Slot_le`**: the guessing term is at most `k · T · |BucketVec| / |MaskBox|`.
- `w1EntrySig_of_canAsk`: a signing entry that the relay's program of a slot's tagged request can
  make carries the slot's signature at its coin.
- **`tsum_w1Guess_le`**: an event on which the readout is a slot's signature at its coin, for laws
  satisfying the slot hypotheses, has average probability at most
  `Q · k · T · |BucketVec| / |MaskBox|`.
-/

open scoped ENNReal

namespace GordieHowe.Ring.MLDSAW1

open _root_.MLDSA GordieHowe.MLDSA GordieHowe.RingSignature GordieHowe.RingSignature.OracleSplit
open GordieHowe.Quantum GordieHowe.Signature RingSignature.KeyFree

variable {X Y : Type} {p : Params} {T : ℕ} {Msg : Type} {N reps : ℕ}
  {prims : Primitives p} [NeZero (bucketCount p)] [nttOps : NTTRingOps]
  [Fintype prims.Power2High] [DecidableEq prims.Power2High] [Fintype prims.Hint]
  [DecidableEq prims.Hint] [Nonempty (MaskBox p)] [Fintype Msg] [DecidableEq Msg]
  [Fintype Y] [DecidableEq Y] [Nonempty Y]
  {O : W1Oracles X Y p prims Msg N reps} {Mo : MaskOracle X Y p T Msg} {βmin : ℚ≥0} {tol : ℕ}
  {enc : Vector prims.High p.k → BucketVec p} {k D : ℕ} [NeZero D] {RMsg : Type} [Fintype RMsg]
  [DecidableEq RMsg] {bmsg : KeyRing (PubKey p prims) N → RMsg → Msg}
  {TPS : PSTypes} {PS : ProofSystem X Y (RingSignature.RingStmt (hedgedBase prims O Mo βmin tol enc k D bmsg)) (RingSignature.RingWitOf (FIPSSignature p prims)) TPS}
  {adm : KeyRing (PubKey p prims) N → Prop}
  [hadm : DecidablePred adm] {n Q : ℕ}
  {Y₁ Y₂ : Type} [AddGroup Y] [AddGroup Y₁] [AddGroup Y₂] [DecidableEq X]
  (sp : Y ≃+ Y₁ × Y₂) (pks : Fin n → PubKey p prims) (ω : X → Y₁)

local notation "Bf" => freshBase prims O Mo βmin tol enc k D bmsg
local notation "PSf" => PS

attribute [local instance] admDecF

/-- **The key-free signer's output at a slot's request and a coin**: for a tagged signing request
`((sign s R m, c), T)`, the public part and the signature of `w1KFOut` at the base component `ω`
read through `T`; nothing for other requests. -/
noncomputable def w1SlotOut
    (r : AssignRelay.TaggedReq X Y (RingSignature.Insider.Req Bf PSf adm n) Q)
    (c : KFCoins (p := p) (T := T) k D Y₁) :
    Option ((BucketVec p × Y₁) × FIPSSignature p prims) :=
  match r.1.1 with
  | .sign s Rg m => w1KFOut (T := T) prims O sp βmin tol enc k D bmsg (ωT sp ω r.2) (pks s) Rg
      r.1.2 m c
  | _ => none

/-- **The public part of a slot's request at a coin**: the published value and base component of
`w1SlotOut`. -/
noncomputable def w1SlotPub
    (r : AssignRelay.TaggedReq X Y (RingSignature.Insider.Req Bf PSf adm n) Q)
    (c : KFCoins (p := p) (T := T) k D Y₁) : Option (BucketVec p × Y₁) :=
  (w1SlotOut sp pks ω r c).map Prod.fst

/-- **The signature of a slot's request at a coin**: the signature of `w1SlotOut`. -/
noncomputable def w1SlotSig
    (r : AssignRelay.TaggedReq X Y (RingSignature.Insider.Req Bf PSf adm n) Q)
    (c : KFCoins (p := p) (T := T) k D Y₁) : Option (FIPSSignature p prims) :=
  (w1SlotOut sp pks ω r c).map Prod.snd

/-- **The guessing term of a slot's signature from its public part**
    (`PMF.tsum_uniform_slots_guess_le`
at `w1SlotPub` and `w1SlotSig`) is at most `k · T · |BucketVec| / |MaskBox|`
(`sum_iSup_prob_w1KFOut_le`). -/
theorem iSup_sum_iSup_w1Slot_le [Fintype Y₁] [DecidableEq Y₁] [Nonempty Y₁] :
    ⨆ r : AssignRelay.TaggedReq X Y (RingSignature.Insider.Req Bf PSf adm n) Q,
        ∑ y : Option (BucketVec p × Y₁), ⨆ z : FIPSSignature p prims,
          (PMF.uniformOfFintype (KFCoins (p := p) (T := T) k D Y₁)).toOuterMeasure
            {c | w1SlotPub sp pks ω r c = y ∧ w1SlotSig sp pks ω r c = some z} ≤
      k * T * Fintype.card (BucketVec p) / Fintype.card (MaskBox p) := by
  refine iSup_le fun r => ?_
  have hset : ∀ (y : Option (BucketVec p × Y₁)) (z : FIPSSignature p prims),
      {c | w1SlotPub sp pks ω r c = y ∧ w1SlotSig sp pks ω r c = some z} =
        {c | ∃ y', y = some y' ∧ w1SlotOut sp pks ω r c = some (y', z)} := by
    intro y z
    ext c
    simp only [w1SlotPub, w1SlotSig, Set.mem_setOf_eq]
    rcases w1SlotOut sp pks ω r c with _ | ⟨y', σ⟩
    · simp
    · constructor
      · rintro ⟨rfl, h⟩
        exact ⟨y', rfl, by simpa using h⟩
      · rintro ⟨y'', rfl, h⟩
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp
  simp only [hset]
  rw [Fintype.sum_option]
  simp only [reduceCtorEq, false_and, exists_false, Set.setOf_false,
    MeasureTheory.measure_empty, Option.some.injEq, exists_eq_left']
  rw [show (⨆ _ : FIPSSignature p prims, (0 : ℝ≥0∞)) = 0 from iSup_eq_bot.2 fun _ => rfl,
    zero_add]
  rcases hr : r.1.1 with _ | ⟨s, Rg, m⟩ | _
  · simp [w1SlotOut, hr]
  · simp only [w1SlotOut, hr]
    exact sum_iSup_prob_w1KFOut_le (T := T) prims O sp βmin tol enc k D bmsg (ωT sp ω r.2) (pks s)
      Rg r.1.2 m
  · simp [w1SlotOut, hr]

/-- **A logged signing entry asked by a slot's recorded request carries the slot's signature**:
for the side-mode key-free relay at the side coins `sc` and the base component `ω`, a main request
that the relay's program of the tagged request `r` with number `j` can make (`CanAsk`), its side
reads answered by `ω`, and that is a signing entry, has the signature `w1SlotSig r (sc j)`. -/
theorem w1EntrySig_of_canAsk [NeZero n] [Fintype X] [Inhabited X] {sc : Fin Q → KFCoins (p := p) (T
    := T) k D Y₁}
    (hO : O.ReadsFst sp) (idle : MURequest (SignOracle.none Bf) n ⊕
      W1Rq prims O Mo βmin tol enc k D bmsg PS adm n Q)
    (r : AssignRelay.TaggedReq X Y (RingSignature.Insider.Req Bf PSf adm n) Q) (j : Fin Q)
    (hj : (r.1.2 : ℕ) = j)
    {e : MURequest (SignOracle.none Bf) n ⊕ W1Rq prims O Mo βmin tol enc k D bmsg PS adm n Q}
    (he : MultiRelay.CanAsk (AssignRelay.relayOf (kfRelaySide sp Bf pks
      (w1KFFactors (T := T) prims O sp βmin tol enc k D bmsg hO)
      (w1KFStmt prims O Mo βmin tol enc k D bmsg sp) (w1ToR (PS := PS) (Q := Q))
      (w1DummyR (PS := PS) (Q := Q)) sc ω idle) Q) r e)
    (hs : (w1SignEntry e).isSome = true) :
    w1EntrySig e = w1SlotSig sp pks ω r (sc j) := by
  have hA := MultiRelay.canAsk_of_asksIn_elimSide _ (AssignRelay.asksIn_relayOf_elimSide _ Q
    (P := fun Tb c rq r' => r' = RingSignature.KeyFree.reqOf Bf (w1ToR (PS := PS) (Q := Q))
        (w1DummyR (PS := PS) (Q := Q)) c rq none none ∨
      KFSignedOf (PS := PSf) (adm := adm) sp Bf pks
        (w1KFFactors (T := T) prims O sp βmin tol enc k D bmsg hO)
        (w1StmtPω prims O Mo βmin tol enc k D bmsg sp) (w1ToR (Q := Q)) sc ω Tb c rq r')
    (fun Tb c rq => asksIn_kfRelaySide_signed sp Bf pks
      (w1KFFactors (T := T) prims O sp βmin tol enc k D bmsg hO) (w1ToR (PS := PS) (Q := Q)) sc
      (w1DummyR (PS := PS) (Q := Q)) (w1KFStmt prims O Mo βmin tol enc k D bmsg sp) ω idle Tb c rq)
    r) he
  rcases hA with hd | ⟨s, Rg, m, hc, q, y, hr, -, -, hq, rfl⟩
  · subst hd
    rcases r with ⟨⟨_ | _ | _, c⟩, Tb⟩ <;> simp [RingSignature.KeyFree.reqOf, w1SignEntry,
      w1DummyR] at hs
  · have hcj : (⟨(r.1.2 : ℕ), hc⟩ : Fin Q) = j := Fin.ext hj
    have h2 : w1SlotSig sp pks ω r (sc j) = some q.2 := by
      simp only [w1SlotSig, w1SlotOut, hr]
      rw [← hcj]
      have hq' : w1KFOut (T := T) prims O sp βmin tol enc k D bmsg (ωT sp ω r.2) (pks s) Rg
          r.1.2 m (sc ⟨r.1.2, hc⟩) = some q := hq
      rw [hq']
      rfl
    rw [h2]
    rfl

/-- **Two signatures of one slot with equal public parts agree on the relation**: for a slot's
signing request `r = ((sign s Rg m, c), T)` and two coins at which the key-free signer outputs the
same public part `φ` (published value and base component) with signatures `σ`, `σ'`, at the
statement of `r` read at the kept point's assignment `(φ, y₂)` (any second component `y₂`) and any
tag `t`, `σ` with the signer's position `w1Idx` is a witness of `w1Rel` exactly when `σ'` is: both
are exactly when the ring is supported and the position is in the ring (`ringVerify_of_w1KFOut`,
`w1Bnd_listed_of_w1KFOut`). -/
theorem w1Rel_iff_of_w1SlotPub_eq (hO : O.ReadsFst sp) (hdisj : ∀ a b, O.muPt a ≠ O.chPt b)
    (r : AssignRelay.TaggedReq X Y (RingSignature.Insider.Req Bf PSf adm n) Q)
    {s : Fin n} {Rg : KeyRing (PubKey p prims) N} {m : RMsg} (hr : r.1.1 = .sign s Rg m)
    {c c' : KFCoins (p := p) (T := T) k D Y₁} {φ : BucketVec p × Y₁}
    {σ σ' : FIPSSignature p prims}
    (hc : w1SlotOut sp pks ω r c = some (φ, σ)) (hc' : w1SlotOut sp pks ω r c' = some (φ, σ'))
    (y₂ : Y₂) (t : W1Tag prims O Mo βmin tol enc k D bmsg PS adm n Q) :
    w1Rel prims O Mo βmin tol enc k D bmsg PS adm n Q
        (w1Bnd (w1StmtPω prims O Mo βmin tol enc k D bmsg sp
          (ωT sp ω (overT r.2 (lastAssign
            [⟨w1KFKept prims O sp bmsg (ωT sp ω r.2) (pks s) Rg m φ, sp.symm (φ.2, y₂)⟩])))
          ⟨Rg, m, φ.1⟩), t)
        (w1Idx pks r.1.1, σ) ↔
      w1Rel prims O Mo βmin tol enc k D bmsg PS adm n Q
        (w1Bnd (w1StmtPω prims O Mo βmin tol enc k D bmsg sp
          (ωT sp ω (overT r.2 (lastAssign
            [⟨w1KFKept prims O sp bmsg (ωT sp ω r.2) (pks s) Rg m φ, sp.symm (φ.2, y₂)⟩])))
          ⟨Rg, m, φ.1⟩), t)
        (w1Idx pks r.1.1, σ') := by
  have key : ∀ {c₀ : KFCoins (p := p) (T := T) k D Y₁} {σ₀ : FIPSSignature p prims},
      w1SlotOut sp pks ω r c₀ = some (φ, σ₀) →
      (w1Rel prims O Mo βmin tol enc k D bmsg PS adm n Q
        (w1Bnd (w1StmtPω prims O Mo βmin tol enc k D bmsg sp
          (ωT sp ω (overT r.2 (lastAssign
            [⟨w1KFKept prims O sp bmsg (ωT sp ω r.2) (pks s) Rg m φ, sp.symm (φ.2, y₂)⟩])))
          ⟨Rg, m, φ.1⟩), t)
        (w1Idx pks r.1.1, σ₀) ↔ adm Rg ∧ ((w1Idx pks r.1.1 : ℕ) < Rg.1.length)) := by
    intro c₀ σ₀ h
    have hq : w1KFOut (T := T) prims O sp βmin tol enc k D bmsg (ωT sp ω r.2) (pks s) Rg r.1.2 m
        c₀ = some (φ, σ₀) := by
      have h' := h
      unfold w1SlotOut at h'
      rw [hr] at h'
      exact h'
    obtain ⟨hv, hw⟩ := ringVerify_of_w1KFOut sp hO hdisj hq
    have hx1 : (w1StmtPω prims O Mo βmin tol enc k D bmsg sp
        (ωT sp ω (overT r.2 (lastAssign
          [⟨w1KFKept prims O sp bmsg (ωT sp ω r.2) (pks s) Rg m φ, sp.symm (φ.2, y₂)⟩])))
        ⟨Rg, m, φ.1⟩).1 = ⟨Rg, m, φ.1⟩ := by
      simp only [w1StmtPω, w1StmtProg, OracleProg.run_mapOutput]
    constructor
    · rintro ⟨had, hi, -⟩
      rw [w1StmtX, w1Bnd, hx1] at had hi
      exact ⟨had, hi⟩
    · rintro ⟨had, hi⟩
      have hidx : (w1Idx pks r.1.1 : ℕ) = Rg.1.idxOf (pks s) := by
        rw [hr] at hi ⊢
        simp only [w1Idx] at hi ⊢
        rcases le_total (Rg.1.idxOf (pks s)) N with hle | hle
        · exact min_eq_left hle
        · rw [min_eq_right hle] at hi
          exact absurd (lt_of_lt_of_le hi Rg.2) (lt_irrefl _)
      have hmem : pks s ∈ Rg.1 := List.idxOf_lt_length_iff.1 (hidx ▸ hi)
      have hj : Rg.1[(w1Idx pks r.1.1 : ℕ)]? = some (pks s) := by
        rw [hidx, List.getElem?_idxOf hmem]
      have hl := w1Bnd_listed_of_w1KFOut (Mo := Mo) sp hdisj hq (sp.symm (0, y₂)) hj
      simp only [AddEquiv.apply_symm_apply] at hl
      have hget : Rg.1[(w1Idx pks r.1.1 : ℕ)]'hi = pks s :=
        Option.some.inj ((List.getElem?_eq_getElem hi).symm.trans hj)
      generalize hX : w1StmtPω prims O Mo βmin tol enc k D bmsg sp
        (ωT sp ω (overT r.2 (lastAssign
          [⟨w1KFKept prims O sp bmsg (ωT sp ω r.2) (pks s) Rg m φ, sp.symm (φ.2, y₂)⟩])))
        ⟨Rg, m, φ.1⟩ = X₀ at hx1 hl ⊢
      obtain ⟨x₁, cs⟩ := X₀
      simp only at hx1
      subst hx1
      simp only [w1Bnd, w1ExpRel, Set.mem_setOf_eq] at hl ⊢
      refine ⟨had, hi, σ₀.cTilde, hl, ?_, ?_⟩
      · change ringVerify prims (fun _ => σ₀.cTilde) enc
          (pubPk prims (Rg.1[(w1Idx pks r.1.1 : ℕ)]'hi)) (bmsg Rg m)
          (w1Of prims enc (Rg.1[(w1Idx pks r.1.1 : ℕ)]'hi) σ₀) σ₀ = true
        rw [hget, ← hw]
        exact hv
      · change w1Of prims enc (Rg.1[(w1Idx pks r.1.1 : ℕ)]'hi) σ₀ = φ.1
        rw [hget]
        exact hw.symm
  rw [key hc, key hc']

/-- **The guess of case S is at most `Q · k · T · |BucketVec| / |MaskBox|`**
(`PMF.tsum_uniform_slots_guess_le` with `iSup_sum_iSup_w1Slot_le`): for laws `L sc` of outcomes
at uniform side coins, the slot requests `rq j` and a readout `Fr` whose laws satisfy the slot
hypotheses (`h1`, `h2`, at the public part `w1SlotPub` and the signature `w1SlotSig`), an event
`G sc` whose probability under `L sc` is at most that of the readout being the signature of some
slot's request at its coin (`hG`), has average probability at most
`Q · k · T · |BucketVec| / |MaskBox|`. -/
theorem tsum_w1Guess_le [Fintype Y₁] [DecidableEq Y₁] [Nonempty Y₁] [Fintype X]
    [Fintype (RingSignature.Insider.Req Bf PSf adm n)] {Ω : Type}
    (L : (Fin Q → KFCoins (p := p) (T := T) k D Y₁) → PMF Ω)
    (rq : Fin Q → Ω → Option (AssignRelay.TaggedReq X Y (RingSignature.Insider.Req Bf PSf adm n) Q))
    (Fr : Ω → Option (FIPSSignature p prims))
    (h1 : ∀ j sc r c c', (L (Function.update sc j c)).toOuterMeasure {o | rq j o = some r} =
      (L (Function.update sc j c')).toOuterMeasure {o | rq j o = some r})
    (h2 : ∀ j sc r z c c', w1SlotPub sp pks ω r c = w1SlotPub sp pks ω r c' →
      (L (Function.update sc j c)).toOuterMeasure {o | rq j o = some r ∧ Fr o = some z} =
        (L (Function.update sc j c')).toOuterMeasure {o | rq j o = some r ∧ Fr o = some z})
    (G : (Fin Q → KFCoins (p := p) (T := T) k D Y₁) → Ω → Prop)
    (hG : ∀ sc, (L sc).toOuterMeasure {o | G sc o} ≤ (L sc).toOuterMeasure
      {o | ∃ j r z, rq j o = some r ∧ w1SlotSig sp pks ω r (sc j) = some z ∧ Fr o = some z}) :
    ∑' sc, PMF.uniformOfFintype (Fin Q → KFCoins (p := p) (T := T) k D Y₁) sc *
        (L sc).toOuterMeasure {o | G sc o} ≤
      Q * (k * T * Fintype.card (BucketVec p) / Fintype.card (MaskBox p)) := by
  refine le_trans (ENNReal.tsum_le_tsum fun sc => ?_)
    ((_root_.PMF.tsum_uniform_slots_guess_le L rq Fr (w1SlotPub sp pks ω) (w1SlotSig sp pks ω) h1
      h2).trans ?_)
  · exact mul_le_mul_of_nonneg_left (hG sc) zero_le
  · gcongr
    exact iSup_sum_iSup_w1Slot_le sp pks ω

end GordieHowe.Ring.MLDSAW1
