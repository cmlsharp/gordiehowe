-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Ring.MLDSAW1KeyFreeStep
public import GordieHowe.Applications.Ring.KeyFreeChainFull
public import GordieHowe.Model.Quantum.Interactive.AssignSideCoins

@[expose] public section

/-!
# The key-free relay challenger of the ML-DSA ring publishing `w₁`, at fixed side coins

The key-free relay challenger `w1C2` (`GordieHowe/Applications/Ring/MLDSAW1KeyFreeStep.lean`)
draws the side coins of every request with the coins of the main challenger. The key-free chain
(`RingSignature.KeyFree.kfChain_le`, `GordieHowe/Applications/Ring/KeyFreeChain.lean`) starts at
fixed side coins, from the outer challenger `kfGame` of the key-free relay. This file connects
the two.

- `prf_reprogram_keptValue`, `prf_reprogram_w1KFSign`: the key-free signer's assignment keeps the
  second component of the oracle.
- `transcriptLawIn_w1C2_eq`: an event of the output, the answered requests and the final oracle
  in force against `w1C2`, with the main challenger on the full oracle (`kfMainFull`), is the
  average over uniform side coins of the event against `kfGame` at those side coins
  (`QueryBoundedAdversary.assignLaw_eq_sum_of_relays`).
-/

open Finset
open scoped ENNReal BigOperators

namespace GordieHowe.Ring.MLDSAW1

open _root_.MLDSA GordieHowe.MLDSA GordieHowe.MLDSA.Regularity GordieHowe.RingSignature GordieHowe.Quantum
  GordieHowe.RingSignature.OracleSplit

variable {X Y : Type} {p : Params} {T : ℕ} {Msg : Type} {N reps : ℕ}

/-! ### The kept value keeps the second component -/

/-- **A value with the second component of the oracle keeps the second component**: reprogramming
`H` at `x` by `sp.symm (v, (sp (H x)).2)` leaves `prf sp H` unchanged. -/
theorem prf_reprogram_keptValue {Y₁ Y₂ : Type} [AddGroup Y] [AddGroup Y₁] [AddGroup Y₂]
    [DecidableEq X] (sp : Y ≃+ Y₁ × Y₂) (H : X → Y) (x : X) (v : Y₁) :
    prf sp (H.reprogram [⟨x, sp.symm (v, (sp (H x)).2)⟩]) = prf sp H := by
  funext z
  simp only [prf, Function.reprogram, List.foldl_cons, List.foldl_nil, Function.update_apply]
  split_ifs with h
  · subst h
    simp
  · rfl

section KeyFreeChal

open GordieHowe.Signature

variable {prims : Primitives p} [NeZero (bucketCount p)] [nttOps : NTTRingOps]
  [Fintype prims.Power2High] [DecidableEq prims.Power2High] [Fintype prims.Hint]
  [DecidableEq prims.Hint] [Nonempty (MaskBox p)] [Fintype Msg] [DecidableEq Msg]
  [Fintype Y] [DecidableEq Y] [Nonempty Y] [Fintype X] [DecidableEq X]
  {O : W1Oracles X Y p prims Msg N reps} {M : MaskOracle X Y p T Msg} {βmin : ℚ≥0} {tol : ℕ}
  {enc : Vector prims.High p.k → BucketVec p} {k D : ℕ} [NeZero D] {RMsg : Type} [Fintype RMsg]
  [DecidableEq RMsg] {bmsg : KeyRing (PubKey p prims) N → RMsg → Msg}
  {Pf PCs : Type} [Fintype Pf] [DecidableEq Pf] [Fintype PCs]
  [DecidableEq PCs] [Nonempty PCs]
  {PS : ProofSystem X Y (RingSignature.RingStmt (hedgedBase prims O M βmin tol enc k D bmsg))
    (RingSignature.RingWitOf (FIPSSignature p prims)) ⟨Pf, PCs⟩}
  {adm : KeyRing (PubKey p prims) N → Prop}
  [hadm : DecidablePred adm] {n : ℕ}
  {Y₁ Y₂ : Type} [AddGroup Y] [AddGroup Y₁] [AddGroup Y₂] [Fintype Y₁] [DecidableEq Y₁]
  {Stmt Wit X₀ Rq PC : Type} [Fintype PC] [DecidableEq PC]

local notation "Bf" => freshBase prims O M βmin tol enc k D bmsg
local notation "PSf" => PS

attribute [local instance] admDecF

omit [Fintype prims.Power2High] [Fintype prims.Hint] [DecidableEq prims.Hint]
  [Nonempty (MaskBox p)] [Fintype Msg] [DecidableEq Msg] [Fintype Y] [DecidableEq Y] [Nonempty Y]
  [Fintype X] [NeZero D] [Fintype RMsg] [DecidableEq RMsg] [Fintype Y₁] [DecidableEq Y₁] in
/-- **The key-free signer's assignment keeps the second component**: an output `(w₁, σ, L)` of
`w1KFSign` at `H` has `prf sp (H.reprogram L) = prf sp H` (`run_w1KFSign`: `L` is one value with
the second component of the oracle at its point). -/
theorem prf_reprogram_w1KFSign (sp : Y ≃+ Y₁ × Y₂) (pk : PubKey p prims)
    (R : KeyRing (PubKey p prims) N) (c : ℕ) (m : RMsg) (sc : KFCoins (p := p) (T := T) k D Y₁)
    (H : X → Y)
    (o : BucketVec p × FIPSSignature p prims × List (Quantum.Assignment X Y))
    (ho : (w1KFSign (RMsg := RMsg) prims O sp βmin tol enc k D bmsg pk R c m sc).run H = some o) :
    prf sp (H.reprogram o.2.2) = prf sp H := by
  rw [run_w1KFSign] at ho
  split_ifs at ho with h₁ h₂
  obtain ⟨s, -, rfl⟩ := Option.map_eq_some_iff.1 ho
  exact prf_reprogram_keptValue sp H _ _

open Classical in
omit [Fintype PCs] [DecidableEq PCs] [Nonempty PCs] [Fintype Msg] [DecidableEq Msg] in
/-- **The key-free relay challenger at fixed side coins**: with the main challenger on the full
oracle (`kfMainFull`, the prover `P₂` reading the second components), an event `E` of the
output, the answered requests and the final oracle in force against `w1C2` at the oracle `H` is
the average over uniform side coins `sc` of the event against the outer challenger `kfGame` of
the key-free relay at `sc` (`QueryBoundedAdversary.assignLaw_eq_sum_of_relays`; the relay's
assignments are safe by `prf_reprogram_w1KFSign` and `run_kfMainFull_congr`). -/
theorem transcriptLawIn_w1C2_eq [Nonempty X] [Inhabited X] [NeZero n] [Fintype Rq] [DecidableEq Rq]
    [Inhabited (MURequest (SignOracle.none (Bf).core) n ⊕ Rq)] (sp : Y ≃+ Y₁ × Y₂) (rel : Stmt → Wit → Prop)
    [DecidableRel rel] (P₂ : NARG.Prover X Y₂ Stmt Wit Pf PC) (μ : PMF PC)
    (penc : MURequest (SignOracle.none (Bf).core) n ⊕ Rq → QROM.ProofQuery Stmt Wit)
    (stmtP : RingSignature.RingStmt Bf → OracleProg X Y X₀)
    (toR : X₀ → RingSignature.Insider.Req Bf PSf adm n × ℕ → (Bf).BSig → Rq)
    (dummyR : RingSignature.Insider.Req Bf PSf adm n × ℕ → Rq) {qs : ℕ}
    (hs : ∀ x, (stmtP x).QueriesLE qs) (idle : MURequest (SignOracle.none (Bf).core) n ⊕ Rq)
    (keys : Fin n → (Bf).KeyCoins) (Q : ℕ) {Out : Type} {t : ℕ}
    (𝒜 : QueryBoundedAdversary X Y (RingSignature.Insider.Req Bf PSf adm n)
      (RingSignature.Insider.Resp Bf PSf adm) Out t) (H : X → Y)
    (E : Out × List (RingSignature.Insider.Req Bf PSf adm n) × (X → Y) → Prop) :
    (𝒜.transcriptLawIn (w1C2 prims O M βmin tol enc k D bmsg PS adm sp rel
        (P₂.mapQuery id fun y => (sp y).2) μ penc stmtP toR dummyR hs idle keys Q) H).toOuterMeasure
        {x | ∃ p ∈ x, E p} =
      ∑ sc, PMF.uniformOfFintype (Fin Q → KFCoins (p := p) (T := T) k D Y₁) sc *
        (𝒜.assignLaw (KeyFree.kfGame (KeyFree.kfMainFull sp Bf rel P₂ μ penc keys Q)
          (KeyFree.kfRelay Bf (fun i => (Bf).pk (keys i))
            (w1KFSign (RMsg := RMsg) prims O sp βmin tol enc k D bmsg) stmtP toR dummyR sc
            (w1KFSign_queries (RMsg := RMsg) prims O sp βmin tol enc k D bmsg) hs idle) Q)
          H).toOuterMeasure {x | ∃ p ∈ x, E p} := by
  rw [← QueryBoundedAdversary.assignLaw_eq_transcriptLawIn]
  have hRL := KeyFree.kfMain_readsLength Bf rel penc (P₂.mapQuery id fun y => (sp y).2) μ keys Q
  exact 𝒜.assignLaw_eq_sum_of_relays (PMF.uniformOfFintype _)
    (fun sc => KeyFree.kfRelay Bf (fun i => (Bf).pk (keys i))
      (w1KFSign (RMsg := RMsg) prims O sp βmin tol enc k D bmsg) stmtP toR dummyR sc
      (w1KFSign_queries (RMsg := RMsg) prims O sp βmin tol enc k D bmsg) hs idle)
    (C' := KeyFree.kfMainFull sp Bf rel P₂ μ penc keys Q)
    (fun sc => KeyFree.kfGame (KeyFree.kfMainFull sp Bf rel P₂ μ penc keys Q)
      (KeyFree.kfRelay Bf (fun i => (Bf).pk (keys i))
        (w1KFSign (RMsg := RMsg) prims O sp βmin tol enc k D bmsg) stmtP toR dummyR sc
        (w1KFSign_queries (RMsg := RMsg) prims O sp βmin tol enc k D bmsg) hs idle) Q)
    (Equiv.refl _) (fun s c' => prodLaw_apply _ _ s c')
    (fun _ c' => { run_eq := fun histD r H' hlen hsome =>
      KeyFree.kfGame_run_eq (fun _ _ => rfl) hRL c' histD hsome r H' hlen })
    (fun _ => (Equiv.punitProd _).symm) (fun _ _ => rfl)
    (fun _ c' => KeyFree.kfGame_relaysChallenger (fun _ _ => rfl) hRL c') (fun _ => rfl)
    (fun sc => KeyFree.kfRelay_safeAssign Bf (fun i => (Bf).pk (keys i))
      (w1KFSign (RMsg := RMsg) prims O sp βmin tol enc k D bmsg) stmtP toR dummyR sc
      (w1KFSign_queries (RMsg := RMsg) prims O sp βmin tol enc k D bmsg) hs idle
      (KeyFree.kfMainFull sp Bf rel P₂ μ penc keys Q) (prf sp)
      (fun pk Rg c msg s H o ho => prf_reprogram_w1KFSign sp pk Rg c msg s H o ho)
      (fun c' hist r' H L hL => KeyFree.run_kfMainFull_congr sp Bf rel P₂ μ penc keys Q c' hist r'
        hL))
    H E

open Classical in
omit [Fintype PCs] [DecidableEq PCs] [Nonempty PCs] [Fintype Msg] [DecidableEq Msg] in
/-- **The key-free relay challenger's game at fixed side coins** (`transcriptLawIn_w1C2_eq` at
each key draw and oracle): an event of the run against `w1C2` (of the key coins, the oracle and
the transcript), with the main challenger on the full oracle, is the average over the key coins,
the oracle and the side coins of the event against `kfGame` at those side coins. The encoding of the
main requests `penc keys` may read the key coins. -/
theorem runLawIn_w1C2_eq [Nonempty X] [Inhabited X] [NeZero n] [Fintype Rq] [DecidableEq Rq]
    [Inhabited (MURequest (SignOracle.none (Bf).core) n ⊕ Rq)] (sp : Y ≃+ Y₁ × Y₂)
    (rel : Stmt → Wit → Prop) [DecidableRel rel] (P₂ : NARG.Prover X Y₂ Stmt Wit Pf PC) (μ : PMF PC)
    (penc : (Fin n → (Bf).KeyCoins) → MURequest (SignOracle.none (Bf).core) n ⊕ Rq →
      QROM.ProofQuery Stmt Wit)
    (stmtP : RingSignature.RingStmt Bf → OracleProg X Y X₀)
    (toR : X₀ → RingSignature.Insider.Req Bf PSf adm n × ℕ → (Bf).BSig → Rq)
    (dummyR : RingSignature.Insider.Req Bf PSf adm n × ℕ → Rq) {qs : ℕ}
    (hs : ∀ x, (stmtP x).QueriesLE qs) (idle : MURequest (SignOracle.none (Bf).core) n ⊕ Rq)
    (Q : ℕ) {Out : Type} {t : ℕ}
    (A : (Fin n → (Bf).KeyCoins) → QueryBoundedAdversary X Y
      (RingSignature.Insider.Req Bf PSf adm n) (RingSignature.Insider.Resp Bf PSf adm) Out t)
    (Ev : (Fin n → (Bf).KeyCoins) → (X → Y) →
      Out × List (RingSignature.Insider.Req Bf PSf adm n) × (X → Y) → Prop) :
    (runLawIn (fun keys _ => A keys) (fun keys => w1C2 prims O M βmin tol enc k D bmsg PS adm sp
        rel (P₂.mapQuery id fun y => (sp y).2) μ (penc keys) stmtP toR dummyR hs idle keys
        Q)).toOuterMeasure
        {x | ∃ q ∈ x.2.2, Ev x.1 x.2.1 q} =
      ∑' keys, PMF.uniformOfFintype (Fin n → (Bf).KeyCoins) keys *
        ∑' H, PMF.uniformOfFintype (X → Y) H *
          ∑ sc, PMF.uniformOfFintype (Fin Q → KFCoins (p := p) (T := T) k D Y₁) sc *
            ((A keys).assignLaw (KeyFree.kfGame (KeyFree.kfMainFull sp Bf rel P₂ μ (penc keys) keys Q)
              (KeyFree.kfRelay Bf (fun i => (Bf).pk (keys i))
                (w1KFSign (RMsg := RMsg) prims O sp βmin tol enc k D bmsg) stmtP toR dummyR sc
                (w1KFSign_queries (RMsg := RMsg) prims O sp βmin tol enc k D bmsg) hs idle) Q)
              H).toOuterMeasure {x | ∃ p ∈ x, Ev keys H p} := by
  rw [toOuterMeasure_runLawIn]
  refine tsum_congr fun keys => congrArg _ (tsum_congr fun H => congrArg _ ?_)
  exact transcriptLawIn_w1C2_eq sp rel P₂ μ (penc keys) stmtP toR dummyR hs idle keys Q (A keys) H
    (Ev keys H)

local notation "Sf" => freshScheme prims O M βmin tol enc k D bmsg PS adm

open Classical in
/-- **The hop from the kept-only to the key-free relay challenger, for a game's run**
(`transcriptLawIn_w1C1_le_w1C2` at each key draw): with the users' key coins uniform and an
adversary family `A keys`, an event of the run against `w1C1` has at most the probability of the
event against `w1C2` plus the average over the key coins of
`Q · C(k T, 2) · Σ_s commitPointMax(Â_s)`. The encoding of the main
requests `penc keys` may read the key coins. -/
theorem runLawIn_w1C1_le_w1C2 [Nonempty X] (sp : Y ≃+ Y₁ × Y₂)
    (h : W1SplitMask O M) (hO : O.ReadsFst sp) (hPS : ProverReadsPub O PS sp)
    (h_laws : SigningLaws prims) (hv : VerifyLaws prims)
    (henc : ∀ w : RqVec p.k, enc (prims.highBitsVec w) = bucketsOf (rqVecCoeffs w))
    (rel : Stmt → Wit → Prop) [DecidableRel rel]
    (P : NARG.Prover X Y Stmt Wit Pf (PSf).Coins) (μ : PMF (PSf).Coins)
    (hPc : μ = PMF.uniformOfFintype (PSf).Coins)
    (penc : (Fin n → (Bf).KeyCoins) → MURequest (SignOracle.none (Bf).core) n ⊕ Rq →
      QROM.ProofQuery Stmt Wit)
    (stmtP : RingSignature.RingStmt Bf → OracleProg X Y X₀)
    (toR : X₀ → RingSignature.Insider.Req Bf PSf adm n × ℕ → (Bf).BSig → Rq)
    (dummyR : RingSignature.Insider.Req Bf PSf adm n × ℕ → Rq) {qs : ℕ}
    (hs : ∀ x, (stmtP x).QueriesLE qs) (idle : MURequest (SignOracle.none (Bf).core) n ⊕ Rq)
    (hs1 : ∀ keys : Fin n → (Bf).KeyCoins, ∀ s, polyVecBounded (keyGen prims (keys s)).2.s1 p.eta)
    (hs2 : ∀ keys : Fin n → (Bf).KeyCoins, ∀ s, polyVecBounded (keyGen prims (keys s)).2.s2 p.eta)
    (hPR : ∀ keys, ProverRelays O enc sp P (penc keys) stmtP toR keys)
    (hKR : ∀ keys, KeptInRel enc rel (penc keys) stmtP toR keys) (Q : ℕ) {Out : Type} {t : ℕ}
    (A : (Fin n → (Bf).KeyCoins) → QueryBoundedAdversary X Y
      (UnforgeRequest (S := Sf) n (SideOracle.none Sf))
      (UnforgeResponse (S := Sf) (SideOracle.none Sf)) Out t)
    (E : Set ((Fin n → (Bf).KeyCoins) × (X → Y) ×
      Option (Out × List (UnforgeRequest (S := Sf) n (SideOracle.none Sf)) × (X → Y)))) :
    (runLawIn (fun keys _ => A keys) (fun keys => w1C1 (SideOracle.none Sf) sp keys Q)).toOuterMeasure
        E ≤
      (runLawIn (fun keys _ => A keys) (fun keys => w1C2 prims O M βmin tol enc k D bmsg PS adm sp
        rel P μ (penc keys) stmtP toR dummyR hs idle keys Q)).toOuterMeasure E +
      ∑' keys, PMF.uniformOfFintype (Fin n → (Bf).KeyCoins) keys *
        (Q * ENNReal.ofReal (((k * T).choose 2 : ℝ) *
          ∑ s, commitPointMax (prims.expandA ((Sf).sk (keys s)).rho))) := by
  rw [toOuterMeasure_runLawIn]
  erw [toOuterMeasure_runLawIn]
  have hstep : ∀ keys H, ((A keys).transcriptLawIn (w1C1 (SideOracle.none Sf) sp keys Q)
      H).toOuterMeasure {o | (keys, H, o) ∈ E} ≤
      ((A keys).transcriptLawIn (w1C2 prims O M βmin tol enc k D bmsg PS adm sp rel P μ
        (penc keys) stmtP toR dummyR hs idle keys Q) H).toOuterMeasure {o | (keys, H, o) ∈ E} +
        Q * ENNReal.ofReal (((k * T).choose 2 : ℝ) *
          ∑ s, commitPointMax (prims.expandA ((Sf).sk (keys s)).rho)) := fun keys H =>
    transcriptLawIn_w1C1_le_w1C2 sp hO h.hMask h.hch h.hdisj h.hdisjg hPS h_laws hv henc rel P μ
      hPc (penc keys) stmtP toR dummyR hs idle keys (hs1 keys) (hs2 keys) (hPR keys) (hKR keys) Q
      (A keys) H _
  have avg : ∀ {β : Type} (p : PMF β) (x y : β → ℝ≥0∞) (s : ℝ≥0∞), (∀ b, x b ≤ y b + s) →
      ∑' b, p b * x b ≤ ∑' b, p b * y b + s := fun p x y s h => by
    calc _ ≤ ∑' b, (p b * y b + p b * s) := ENNReal.tsum_le_tsum fun b => by
          rw [← mul_add]; exact mul_le_mul_of_nonneg_left (h b) zero_le
      _ = _ := by rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
  calc _ ≤ ∑' keys, PMF.uniformOfFintype (Fin n → (Bf).KeyCoins) keys *
        (∑' H, PMF.uniformOfFintype (X → Y) H *
          ((A keys).transcriptLawIn (w1C2 prims O M βmin tol enc k D bmsg PS adm sp rel P μ
            (penc keys) stmtP toR dummyR hs idle keys Q) H).toOuterMeasure {o | (keys, H, o) ∈ E} +
        Q * ENNReal.ofReal (((k * T).choose 2 : ℝ) *
          ∑ s, commitPointMax (prims.expandA ((Sf).sk (keys s)).rho))) :=
        ENNReal.tsum_le_tsum fun keys => mul_le_mul_of_nonneg_left
          (avg _ _ _ _ fun H => hstep keys H) zero_le
    _ = _ := by simp_rw [mul_add]; rw [ENNReal.tsum_add]

end KeyFreeChal

end GordieHowe.Ring.MLDSAW1
