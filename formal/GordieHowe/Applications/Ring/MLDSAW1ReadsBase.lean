-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Ring.MLDSAW1Rejection
public import GordieHowe.Applications.Ring.MLDSAW1Anonymity
public import GordieHowe.Applications.Ring.MLDSAW1Split

@[expose] public section

/-!
# The base signer of the ML-DSA ring publishing `w₁` reads only the base component

For an additive split `sp : Y ≃+ Y₁ × Y₂` of the oracle's values
(`GordieHowe/Applications/Ring/MLDSAW1Split.lean`) and decodings of the base signer's oracles
reading only the first component (`W1Oracles.ReadsFst`, `MaskOracle.ReadsFst`), the hedged base
signer of `GordieHowe/Applications/Ring/MLDSAW1Ring.lean` (`w1BaseSigner … (hedgedLoop …)`), its
public value, its verification and its ordinary signer read the oracle only through its base
component `base sp H`.

- `W1Oracles.muOrc_eq_of_base`, `W1Oracles.chOrc_eq_of_base`, `W1Oracles.hOrc_eq_of_base`,
  `W1Oracles.gOrc_eq_of_base`, `MaskOracle.ans_eq_of_base`: the decoded oracles agree at oracles
  with the same base component.
- `BaseSigner.ReadsStdOnly B f`: the ordinary signer's runs agree at oracles with the same `f`.
- `readsOnly_w1Base`, `readsStdOnly_w1Base`: the hedged base signer and its ordinary signer read
  only the base component (`BaseSigner.ReadsOnly`,
  `GordieHowe/Applications/Ring/RingAnonymity.lean`).
-/

namespace GordieHowe.RingSignature

variable {X Y : Type} {N : ℕ}

/-- **The ordinary signer reads the oracle only through `f`**: its runs agree at two oracles with
the same value of `f`. -/
def BaseSigner.ReadsStdOnly {TS : Signature.SchemeTypes} {RMsg : Type}
    (B : BaseSigner X Y N TS RMsg) {Ω₂ : Type} (f : (X → Y) → Ω₂) : Prop :=
  ∀ H H', f H = f H' → ∀ sk bm c, (B.ssign sk bm c).run H = (B.ssign sk bm c).run H'

end GordieHowe.RingSignature

namespace GordieHowe.Ring.MLDSAW1

open _root_.MLDSA GordieHowe.MLDSA GordieHowe.RingSignature GordieHowe.RingSignature.OracleSplit
open scoped ENNReal

variable {X Y Y₁ Y₂ : Type} [AddGroup Y] [AddGroup Y₁] [AddGroup Y₂] {sp : OracleSplit Y Y₁ Y₂}
  {p : Params} {prims : Primitives p} {Msg : Type} {N reps T : ℕ}

/-! ### The decoded oracles at oracles with the same base component -/

section Decode

variable {O : W1Oracles X Y p prims Msg N reps} (hO : O.ReadsFst sp) {H H' : X → Y}
  (h : base sp H = base sp H')
include hO h

omit hO in
/-- The values of two oracles with the same base component have the same first components. -/
theorem fst_eq_of_base (x : X) : (sp (H x)).1 = (sp (H' x)).1 :=
  congrFun h x

/-- The message-representative oracles agree. -/
theorem W1Oracles.muOrc_eq_of_base : O.muOrc H = O.muOrc H' :=
  funext fun _ => hO.muAns_eq _ _ (fst_eq_of_base h _)

/-- The commitment-hash oracles agree. -/
theorem W1Oracles.chOrc_eq_of_base : O.chOrc H = O.chOrc H' :=
  funext fun _ => hO.chAns_eq _ _ (fst_eq_of_base h _)

/-- The check oracles agree. -/
theorem W1Oracles.gOrc_eq_of_base : O.gOrc H = O.gOrc H' :=
  funext fun _ => hO.gAns_eq _ _ (fst_eq_of_base h _)

/-- The commitment hashes agree. -/
theorem W1Oracles.hOrc_eq_of_base : O.hOrc H = O.hOrc H' := by
  simp only [MLDSAOracles.hOrc, W1Oracles.muOrc_eq_of_base hO h, W1Oracles.chOrc_eq_of_base hO h]

end Decode

/-- The masks of two oracles with the same base component agree, for a mask decoding reading only
the first component. -/
theorem _root_.GordieHowe.MLDSA.MaskOracle.ans_eq_of_base {M : MaskOracle X Y p T Msg}
    (hM : M.ReadsFst sp) {H H' : X → Y}
    (h : base sp H = base sp H') (x : X) : M.ans (H x) = M.ans (H' x) :=
  hM _ _ (congrFun h x)

/-! ### The hedged base signer -/

section Signer

variable [NeZero (bucketCount p)] [nttOps : NTTRingOps] [Fintype prims.Power2High]
  [DecidableEq prims.Power2High] [Fintype prims.Hint] [DecidableEq prims.Hint]
  [Inhabited prims.Hint] [Nonempty (MaskBox p)] [Fintype Msg] [DecidableEq Msg]
  (enc : Vector prims.High p.k → BucketVec p) {O : W1Oracles X Y p prims Msg N reps}
  {M : MaskOracle X Y p T Msg} (βmin : ℚ≥0) (tol k D : ℕ) [NeZero D] {RMsg : Type}
  [Fintype RMsg] [DecidableEq RMsg] (bmsg : KeyRing (PubKey p prims) N → RMsg → Msg)

omit [Inhabited prims.Hint] in
/-- **The hedged base signer reads only the base component**: its signer, public value and
verification agree at oracles with the same base component, for decodings reading only the first
component. -/
theorem readsOnly_w1Base (hO : O.ReadsFst sp) (hM : M.ReadsFst sp) :
    (w1Base p prims enc O M βmin tol k D bmsg).ReadsOnly (base sp) where
  run_bsign H H' h sk R i m c := by
    refine (run_bsign_w1BaseSigner prims O βmin tol enc (MaskSource.hedged M) k D bmsg sk R i m c
      H).trans (Eq.trans ?_ (run_bsign_w1BaseSigner prims O βmin tol enc (MaskSource.hedged M) k D
        bmsg sk R i m c H').symm)
    have hg := W1Oracles.gOrc_eq_of_base hO h
    have hmu := W1Oracles.muOrc_eq_of_base hO h
    have hh := W1Oracles.hOrc_eq_of_base hO h
    have hmask : (fun c' t =>
        ((MaskSource.hedged M).read (c.1 c') (t, (sk.key, (sk.tr, bmsg R m)))).run H) =
        fun c' t => ((MaskSource.hedged M).read (c.1 c') (t, (sk.key, (sk.tr, bmsg R m)))).run H' :=
      funext fun c' => funext fun t => MaskOracle.ans_eq_of_base hM h _
    rw [hh, hmask]
    by_cases hc :
        sampledRingCheck prims βmin tol (O.gOrc H') R ∧ MuDistinct prims (O.muOrc H') R (bmsg R m)
    · rw [if_pos (by rw [hg, hmu]; exact hc), if_pos hc]
    · rw [if_neg (by rw [hg, hmu]; exact hc), if_neg hc]
  run_pub _ _ _ _ _ := rfl
  bverify_eq H H' h := by
    funext pk bm σ
    change ringVerify prims (O.hOrc H) enc _ bm _ σ = ringVerify prims (O.hOrc H') enc _ bm _ σ
    rw [W1Oracles.hOrc_eq_of_base hO h]

omit [Inhabited prims.Hint] in
/-- **The ordinary signer of the hedged base signer reads only the base component.** -/
theorem readsStdOnly_w1Base (hO : O.ReadsFst sp) (hM : M.ReadsFst sp) :
    (w1Base p prims enc O M βmin tol k D bmsg).ReadsStdOnly (base sp) := by
  intro H H' h
  have key : ∀ (sk : SecretKey p) (bm : Msg) (r : Fin k → (MaskSource.hedged M).Rnd),
      (stdProg prims (MaskSource.hedged M) O.toMLDSAOracles k sk bm r).run H =
        (stdProg prims (MaskSource.hedged M) O.toMLDSAOracles k sk bm r).run H' := by
    intro sk bm r
    by_cases hk : 0 < k
    · have h1 : ∀ G : X → Y,
          (stdProg prims (MaskSource.hedged M) O.toMLDSAOracles k sk bm r).run G =
          (stdProg prims (MaskSource.hedged M) O.toMLDSAOracles 1 sk bm
            fun _ => r ⟨0, hk⟩).run G := fun G => by
        unfold stdProg
        simp only [hk, Nat.zero_lt_one, ↓reduceDIte]
      rw [h1, h1, run_stdProg_one, run_stdProg_one, W1Oracles.hOrc_eq_of_base hO h]
      have hmask : (fun t =>
          ((MaskSource.hedged M).read (r ⟨0, hk⟩) (t, (sk.key, (sk.tr, bm)))).run H) =
          fun t => ((MaskSource.hedged M).read (r ⟨0, hk⟩) (t, (sk.key, (sk.tr, bm)))).run H' :=
        funext fun t => MaskOracle.ans_eq_of_base hM h _
      simp only [congrFun hmask]
    · unfold stdProg
      simp only [hk, ↓reduceDIte, OracleProg.run_pure]
  intro sk bm c
  simpa only [w1BaseSigner, w1BaseSignerOf, mldsaT0BaseScheme, W1Loop.stdSigner, ringLoop,
      ringLoopOf] using key sk bm c.1

end Signer

end GordieHowe.Ring.MLDSAW1
