-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Ring.MLDSAW1HiddenStep
public import GordieHowe.Applications.Ring.MLDSAW1KeyFreeStep
public import GordieHowe.Model.Quantum.Interactive.HiddenReadsEvent
public import GordieHowe.Model.RingSignature.VerifiesBy

@[expose] public section

/-!
# The kept-only reprogramming challenger in the game of the fresh-mask ring

The game-level hop from the challenger that reprograms the commitment hash at every attempted
point of a signing request (`Challenger.preReprog` with `w1Pts`) to the kept-only challenger
(`w1C1`, `Challenger.preReprogKeep` with `w1KeptPts`) in BKM06 Definition 7 for the ML-DSA ring
publishing `w₁` with fresh masks. The forgery is read at the final oracle in force: the
signature verifies there and the ring and message are fresh. When the proof system's verifier is
a program with at most `qv` queries (`ProofSystem.VerifiesBy`), the verification is that program
run at the final oracle in force, and the forgery is an event of the output, the answered
requests and a program's result, so the hidden-reads bound for such events applies
(`RingSignature.gameAdvantage_runLawIn_le_of_hiddenReadsPair`,
`GordieHowe/Model/Quantum/Interactive/HiddenReadsEvent.lean`) at the pair `w1HiddenPair` with the
point bound of `hfind_w1HiddenPair` (`GordieHowe/Applications/Ring/MLDSAW1HiddenStep.lean`).

- `forges_iff_verify_fresh`: a forgery is a verifying program result and a fresh ring and message.
- `forgeProb_reprog_le_w1C1`: **the game against the full reprogramming challenger is at most
  the game against the kept-only one plus** `2 √(t + w qv + Q) √((t + w qv + q_C Q) Q δ̄)`, where
  `w` bounds the adversary's width, `q_C = 1 + k T + q_S` the reads of a request, and `δ̄` the
  average over the key coins of `2 k T Σ_s commitPointMax(Â_s)`.
-/

open Finset
open scoped ENNReal BigOperators

namespace GordieHowe.Ring.MLDSAW1

open _root_.MLDSA GordieHowe.MLDSA GordieHowe.MLDSA.Regularity GordieHowe.RingSignature
open GordieHowe.Quantum

variable {X Y : Type} {p : Params} {T : ℕ} {Msg : Type} {N reps : ℕ}

section Game

variable {prims : Primitives p} [NeZero (bucketCount p)] [nttOps : NTTRingOps]
  [Fintype prims.Power2High] [DecidableEq prims.Power2High] [Fintype prims.Hint]
  [DecidableEq prims.Hint] [Nonempty (MaskBox p)] [Fintype Msg] [DecidableEq Msg]
  [Fintype Y] [DecidableEq Y] [Nonempty Y] [Fintype X] [DecidableEq X]
  {O : W1Oracles X Y p prims Msg N reps} {M : MaskOracle X Y p T Msg} {βmin : ℚ≥0} {tol : ℕ}
  {enc : Vector prims.High p.k → BucketVec p} {k D : ℕ} [NeZero D] {RMsg : Type} [Fintype RMsg]
  [DecidableEq RMsg] {bmsg : KeyRing (PubKey p prims) N → RMsg → Msg}
  {TPS : PSTypes} [Fintype TPS.Proof] [DecidableEq TPS.Proof] [Fintype TPS.Coins] [DecidableEq TPS.Coins] [Nonempty TPS.Coins] {PS : ProofSystem X Y (RingSignature.RingStmt (hedgedBase prims O M βmin tol enc k D bmsg)) (RingSignature.RingWitOf (FIPSSignature p prims)) TPS}
  {adm : KeyRing (PubKey p prims) N → Prop}
  [hadm : DecidablePred adm] {n : ℕ}
  {Y₁ Y₂ : Type} [AddGroup Y] [AddGroup Y₁] [AddGroup Y₂] [Fintype Y₁] [DecidableEq Y₁]

local notation "Sf" => freshScheme prims O M βmin tol enc k D bmsg PS adm
local notation "Bf" => freshBase prims O M βmin tol enc k D bmsg

/-- **The verification program of a forgery** `(R, m, (pub, π))`: the program `Vp` at the
statement `(R, m, pub)` and the proof `π`. -/
def forgeVerifyProg (Vp : RingSignature.RingStmt (hedgedBase prims O M βmin tol enc k D bmsg) →
      PS.Proof → OracleProg X Y Bool)
    (o : KeyRing (Sf).PK N × (Sf).Msg × (Sf).Sig) : OracleProg X Y Bool :=
  Vp ⟨o.1, o.2.1, o.2.2.1⟩ o.2.2.2

omit [Fintype X] [DecidableEq X] [AddGroup Y] [Fintype TPS.Proof] [DecidableEq TPS.Proof]
  [Fintype TPS.Coins] [DecidableEq TPS.Coins] [Nonempty TPS.Coins] [Fintype Msg] [DecidableEq Msg]
  [Fintype Y] [DecidableEq Y] [Nonempty Y] in
/-- **A forgery is a verifying program result and a fresh ring and message**, when the proof
system verifies by `Vp`. -/
theorem forges_iff_verify_fresh {Of : SideOracle (Sf)}
    {Vp : RingSignature.RingStmt (hedgedBase prims O M βmin tol enc k D bmsg) →
      PS.Proof → OracleProg X Y Bool} {qv : ℕ} (hV : PS.VerifiesBy Vp qv)
    (keys : Fin n → (Sf).KeyCoins) (G : X → Y) (o : KeyRing (Sf).PK N × (Sf).Msg × (Sf).Sig)
    (hist : UnforgeHist (S := Sf) n Of) :
    Forges keys G o hist ↔ (forgeVerifyProg Vp o).run G = true ∧ Fresh keys hist o.1 o.2.1 :=
  ⟨fun h => ⟨(hV.verify_eq G _ o.2.2.2).symm.trans h.verify_eq, h.fresh⟩,
    fun h => ⟨(hV.verify_eq G _ o.2.2.2).trans h.1, h.2⟩⟩

open Classical in
/-- **The game against the full reprogramming challenger is at most the game against the
kept-only one plus the hidden-reads bound** (module docstring): for a proof system verifying by
a program with at most `qv` queries, honest keys (`hs2`), and an adversary of width at most `w`
at every key and auxiliary value, the probability of a forgery read at the final oracle in force
against `preReprog` is at most that against `w1C1` plus
`2 √(t + w qv + Q) √((t + w qv + (1 + k T + q_S) Q) Q δ̄)`, `δ̄` the average over the key coins
of `2 k T Σ_s commitPointMax(Â_s)`. -/
theorem forgeProb_reprog_le_w1C1 [Nonempty X] [NeZero n]
    (sp : Y ≃+ Y₁ × Y₂)
    (h : W1SplitMask O M) (hPS : ProverReadsPub O PS sp)
    (h_laws : SigningLaws prims) (hv : VerifyLaws prims)
    (henc : ∀ w : RqVec p.k, enc (prims.highBitsVec w) = bucketsOf (rqVecCoeffs w))
    (hs2 : ∀ seed, polyVecBounded (keyGen prims seed).2.s2 p.eta)
    {Vp : RingSignature.RingStmt (hedgedBase prims O M βmin tol enc k D bmsg) →
      PS.Proof → OracleProg X Y Bool} {qv : ℕ} (hV : PS.VerifiesBy Vp qv)
    {t w : ℕ} (A : InsiderAdversary Sf n (OracleView.queriesOnly X Y) t)
    (hw : ∀ (keys : Fin n → (Sf).KeyCoins) a,
      ((A (fun i => (Bf).pk (keys i), ())).alg a).width ≤ w) (Q : ℕ) :
    ((runLawIn (fun keys H => A (fun i => (Bf).pk (keys i), (OracleView.queriesOnly X Y).view H))
        (fun keys => (unforgeChallenger Sf n (SideOracle.none Sf) keys Q).preReprog sp
          (w1Pts (SideOracle.none Sf) keys) 1 (k * T) (w1Pts_queries keys)
          (card_w1Pts_le keys))).toOuterMeasure
        {x | ∃ q ∈ x.2.2, Forges x.1 q.2.2 q.1 (Challenger.histOf q.2.1)}).toReal ≤
      ((runLawIn (fun keys H => A (fun i => (Bf).pk (keys i), (OracleView.queriesOnly X Y).view H))
        (fun keys => w1C1 (SideOracle.none Sf) sp keys Q)).toOuterMeasure
        {x | ∃ q ∈ x.2.2, Forges x.1 q.2.2 q.1 (Challenger.histOf q.2.1)}).toReal +
      2 * √(t + w * qv + Q : ℝ) *
        √((t + w * qv + (1 + k * T + max (Sf).q (SideOracle.none Sf).q) * Q : ℝ) *
          (Q * ∑ keys : Fin n → (Sf).KeyCoins, (Fintype.card (Fin n → (Sf).KeyCoins) : ℝ)⁻¹ *
            (2 * k * T * ∑ s, commitPointMax (prims.expandA ((Sf).sk (keys s)).rho)))) := by
  set E : Set ((Fin n → (Sf).KeyCoins) × (X → Y) ×
      Option ((KeyRing (Sf).PK N × (Sf).Msg × (Sf).Sig) ×
        List (UnforgeRequest (S := Sf) n (SideOracle.none Sf)) × (X → Y))) :=
    {x | ∃ q ∈ x.2.2, Forges x.1 q.2.2 q.1 (Challenger.histOf q.2.1)}
  set Ev : (Fin n → (Sf).KeyCoins) → KeyRing (Sf).PK N × (Sf).Msg × (Sf).Sig →
      List (UnforgeRequest (S := Sf) n (SideOracle.none Sf)) → Bool → Prop :=
    fun keys o reqs b => b = true ∧ Fresh keys (Challenger.histOf reqs) o.1 o.2.1
  have hE : E = {x | ∃ q ∈ x.2.2, Ev x.1 q.1 q.2.1 ((forgeVerifyProg Vp q.1).run q.2.2)} :=
    Set.ext fun x => exists_congr fun q => and_congr_right fun _ =>
      forges_iff_verify_fresh hV x.1 q.2.2 q.1 _
  have h := gameAdvantage_runLawIn_le_of_hiddenReadsPair
    (fun keys => A (fun i => (Bf).pk (keys i), ())) (fun _ => forgeVerifyProg Vp) qv (w * qv)
    (fun _ o => hV.queries _ _) (fun keys a => Nat.mul_le_mul_right qv (hw keys a))
    (C := fun keys => w1C1 (SideOracle.none Sf) sp keys Q)
    (C' := fun keys => (unforgeChallenger Sf n (SideOracle.none Sf) keys Q).preReprog sp
      (w1Pts (SideOracle.none Sf) keys) 1 (k * T) (w1Pts_queries keys) (card_w1Pts_le keys))
    (qC := 1 + k * T + max (Sf).q (SideOracle.none Sf).q) (Q := Q)
    (fun keys => w1HiddenPair (SideOracle.none Sf) sp h.hch h.hdisj h.hdisjg hPS h_laws hv henc
      keys (fun s => hs2 (keys s)) Q) (fun _ => rfl)
    (fun keys _ => 2 * k * T * ∑ s, commitPointMax (prims.expandA ((Sf).sk (keys s)).rho))
    (fun keys j H ω₀ c rs₀ req hl g =>
      hfind_w1HiddenPair sp h.hMask h.hch h.hdisj h.hdisjg hPS h_laws hv henc keys
        (fun s => hs2 (keys s)) Q j H ω₀ c rs₀ req hl g) Ev
  beta_reduce at h
  rw [← hE, gameAdvantage, advantage_le_iff] at h
  have hq0 : ¬ (1 + k * T + max (Sf).q (SideOracle.none Sf).q = 0) := by omega
  have hQk : ∀ keys : Fin n → (Sf).KeyCoins, (w1C1 (SideOracle.none Sf) sp keys Q).Q = Q :=
    fun _ => rfl
  have hb : ∑ keys : Fin n → (Sf).KeyCoins, (Fintype.card (Fin n → (Sf).KeyCoins) : ℝ)⁻¹ *
      ((Q : ℝ) * (2 * k * T * ∑ s, commitPointMax (prims.expandA ((Sf).sk (keys s)).rho))) =
      Q * ∑ keys : Fin n → (Sf).KeyCoins, (Fintype.card (Fin n → (Sf).KeyCoins) : ℝ)⁻¹ *
        (2 * k * T * ∑ s, commitPointMax (prims.expandA ((Sf).sk (keys s)).rho)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring
  simp only [hq0, ↓reduceIte, Finset.sum_const, Finset.card_univ, Fintype.card_fin, hQk,
    nsmul_eq_mul, hb, Nat.cast_mul, Nat.cast_add, Nat.cast_one, Set.ofPred_mem_eq] at h
  have h2 := h.2
  change ((runLawIn (fun keys _ => A (fun i => (Bf).pk (keys i), ())) _).toOuterMeasure E).toReal -
    ((runLawIn (fun keys _ => A (fun i => (Bf).pk (keys i), ())) _).toOuterMeasure E).toReal ≤ _
    at h2
  change ((runLawIn (fun keys _ => A (fun i => (Bf).pk (keys i), ())) _).toOuterMeasure E).toReal ≤
    ((runLawIn (fun keys _ => A (fun i => (Bf).pk (keys i), ())) _).toOuterMeasure E).toReal + _
  linarith

end Game

end GordieHowe.Ring.MLDSAW1
