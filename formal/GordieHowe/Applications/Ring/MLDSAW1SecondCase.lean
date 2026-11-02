-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Ring.MLDSAW1Ring
public import GordieHowe.Applications.MLDSA.Signing.SecondSignature
public import GordieHowe.Model.Signature.MultiUser

@[expose] public section

/-!
# A forgery at a returned commitment of the ML-DSA ring publishing `w₁` gives a Module-SIS solution

In the multi-user strong game with never-returned signatures (`Signature.muSufSigProb`,
`GordieHowe/Model/Signature/MultiUser.lean`) at a signing oracle of a base signer of the ring
publishing `w₁` at the concrete primitives with any signing loop (`w1BaseSigner … L …`: the
hedged `w1ConcreteBase` and the fresh-mask `freshBase` of
`GordieHowe/Applications/Ring/MLDSAW1Anonymity.lean`), a forgery `(pk_i, bm, σ*)` whose commitment
`w1Of pk_i σ*` is that of a verifying signature `σ` returned to user `i` on `bm` has `σ ≠ σ*` (`σ*`
was never returned), so the pair is a solution of the key-generation-form Module-SIS instance at
user `i`'s seed (`keyGenKernel_secondSigVec`,
`GordieHowe/Applications/MLDSA/Signing/SecondSignature.lean`;
Dilithium specification Version 3.1, §6.2.2; KLS18 Lemma 4.9, §4.3). Every other forgery is fresh
for its commitment.

- `SameW1Forges`: the forgery verifies under the key of an uncorrupted user `i` never returned
  `σ*`, and a verifying signature returned to `i` on the base message has the same commitment.
- `FreshW1Forges`: the forgery verifies under the key of an uncorrupted user `i`, and no verifying
  signature returned to `i` on the base message has its commitment.
- `sigStrongForges_cases`: a strong forgery with never-returned signatures is one of the two.
- `msisReadout`, `msisReduction`: the reduction `B₂` of the `n`-seed key-generation-form Module-SIS
  game: on the users' seeds, the game run (uniform oracle, the adversary against the multi-user
  challenger at those keys), read out as `(i, secondSigVec pk_i σ* σ)` on `SameW1Forges`.
- `pubPk_pk_w1BaseSigner`, `ne_of_returned`, `keyGenKernel_of_sameW1`, `msisReadout_wins`: the
  forgery's key is that of `keyGenFromSeed` at the user's seed, the returned signature differs from
  the forgery, and the readout is a solution at that seed.
- `muSufSigProb_le_msis_add_fresh`: **the never-returned strong game is at most the Module-SIS win
  probability of `B₂` plus the probability of a forgery fresh for its commitment.**
-/

namespace GordieHowe.Ring.MLDSAW1

open _root_.MLDSA GordieHowe.MLDSA GordieHowe.RingSignature GordieHowe.Signature
open _root_.MLDSA.Concrete GordieHowe.MLDSA.Spec
open scoped ENNReal

attribute [local instance] concreteNTTRingOps

variable {X Y : Type} [AddGroup Y] {p : Params} {Msg : Type} [NeZero (bucketCount p)]
  {N reps : ℕ} [Fintype Msg] [DecidableEq Msg]
  {O : W1Oracles X Y p (concretePrimitivesKeyGen p) Msg N reps} {βmin : ℚ≥0} {tol : ℕ}
  {CL : Type} [Fintype CL] [DecidableEq CL] [Nonempty CL] {L : W1Loop X Y p (concretePrimitivesKeyGen p) Msg N CL} {RMsg : Type} [Fintype RMsg]
  [DecidableEq RMsg] {bmsg : KeyRing (PubKey p (concretePrimitivesKeyGen p)) N → RMsg → Msg}
  {SO : SignOracle (w1BaseSigner (concretePrimitivesKeyGen p) O βmin tol (concreteEnc p) L bmsg)}
  {n : ℕ}

local notation "Bc" => w1BaseSigner (concretePrimitivesKeyGen p) O βmin tol (concreteEnc p) L bmsg

/-- **A forgery at a returned commitment**: `σ*` verifies on `bm` under the key of a user `i`
neither
corrupted nor returned `σ*`, and a signature `σ` returned to `i` on `bm` verifies and has the same
commitment `w1Of pk σ = w1Of pk σ*`. -/
def SameW1Forges (keys : Fin n → Bytes 32) (H : X → Y) (f : (Bc).PK × (Bc).BMsg × (Bc).BSig)
    (hist : MUHist SO n) : Prop :=
  (Bc).bverify H f.1 f.2.1 f.2.2 = true ∧ ∃ i σ, (Bc).pk (keys i) = f.1 ∧ ¬ Corrupted hist i ∧
    ¬ ReturnedSig hist i f.2.2 ∧ Returned hist i f.2.1 σ ∧ (Bc).bverify H f.1 f.2.1 σ = true ∧
    w1Of (concretePrimitivesKeyGen p) (concreteEnc p) f.1 σ =
      w1Of (concretePrimitivesKeyGen p) (concreteEnc p) f.1 f.2.2

/-- **A forgery fresh for its commitment**: `σ*` verifies on `bm` under the key of an uncorrupted
user `i`, and no verifying signature returned to `i` on `bm` has the commitment of `σ*`. -/
def FreshW1Forges (keys : Fin n → Bytes 32) (H : X → Y) (f : (Bc).PK × (Bc).BMsg × (Bc).BSig)
    (hist : MUHist SO n) : Prop :=
  (Bc).bverify H f.1 f.2.1 f.2.2 = true ∧ ∃ i, (Bc).pk (keys i) = f.1 ∧ ¬ Corrupted hist i ∧
    ∀ σ, Returned hist i f.2.1 σ → (Bc).bverify H f.1 f.2.1 σ = true →
      w1Of (concretePrimitivesKeyGen p) (concreteEnc p) f.1 σ ≠
        w1Of (concretePrimitivesKeyGen p) (concreteEnc p) f.1 f.2.2

omit [AddGroup Y] in
/-- **A strong forgery with never-returned signatures is at a returned commitment or fresh for its
commitment.** -/
theorem sigStrongForges_cases {keys : Fin n → Bytes 32} {H : X → Y}
    {f : (Bc).PK × (Bc).BMsg × (Bc).BSig} {hist : MUHist SO n}
    (h : SigStrongForges keys H f hist) :
    SameW1Forges keys H f hist ∨ FreshW1Forges keys H f hist := by
  classical
  obtain ⟨hv, i, hpk, hc, hr⟩ := h
  by_cases hs : ∃ σ, Returned hist i f.2.1 σ ∧ (Bc).bverify H f.1 f.2.1 σ = true ∧
      w1Of (concretePrimitivesKeyGen p) (concreteEnc p) f.1 σ =
        w1Of (concretePrimitivesKeyGen p) (concreteEnc p) f.1 f.2.2
  · obtain ⟨σ, hσ, hσv, hw⟩ := hs
    exact Or.inl ⟨hv, i, σ, hpk, hc, hr, hσ, hσv, hw⟩
  · exact Or.inr ⟨hv, i, hpk, hc, fun σ hσ hσv hw => hs ⟨σ, hσ, hσv, hw⟩⟩

variable {V : OracleView X Y} {t : ℕ} [Fintype X] [DecidableEq X] [Nonempty X] [Fintype Y]
  [DecidableEq Y] [Nonempty Y]

open Classical in
/-- **The readout of the reduction `B₂`** at the seeds `keys`, the oracle `H` and the game's
outcome:
`(i, secondSigVec pk_i σ* σ)` for a forgery at a returned commitment (user `i`, returned `σ`),
none otherwise. -/
noncomputable def msisReadout (keys : Fin n → Bytes 32) (H : X → Y)
    (o : Option (((Bc).PK × (Bc).BMsg × (Bc).BSig) × MUHist SO n)) :
    Option (Fin n × (RqVec p.l × RqVec p.k)) :=
  if h : ∃ q ∈ o, SameW1Forges keys H q.1 q.2 then
    some (h.choose_spec.2.2.choose, secondSigVec p (pubPk (concretePrimitivesKeyGen p)
      h.choose.1.1) h.choose.1.2.2 h.choose_spec.2.2.choose_spec.choose)
  else none

/-- **The reduction `B₂` of the key-generation-form Module-SIS game**: on the users' seeds `keys`,
the oracle uniform, the adversary `A` on the users' public keys and the oracle's table against the
multi-user challenger at the keys with `Q` requests, the outcome read by `msisReadout`. -/
noncomputable def msisReduction (A : MUAdversary SO n V t) (Q : ℕ) (keys : Fin n → Bytes 32) :
    PMF (Option (Fin n × (RqVec p.l × RqVec p.k))) :=
  (PMF.uniformOfFintype (X → Y)).bind fun H =>
    ((A (fun i => (Bc).pk (keys i), V.view H)).transcriptLaw (muChallenger SO n keys Q) H).map
      (msisReadout keys H)

omit [AddGroup Y] [Fintype X] [DecidableEq X] [Nonempty X] [Fintype Y] [DecidableEq Y]
  [Nonempty Y] in
/-- The FIPS 204 public key of the base signer's key of the seed `ξ` is that of `keyGenFromSeed`. -/
theorem pubPk_pk_w1BaseSigner (ξ : Bytes 32) :
    pubPk (concretePrimitivesKeyGen p) ((Bc).pk ξ) =
      (keyGenFromSeed p (concretePrimitivesKeyGen p) ξ).1 :=
  rfl

omit [AddGroup Y] [Fintype X] [DecidableEq X] [Nonempty X] [Fintype Y] [DecidableEq Y]
  [Nonempty Y] in
/-- **A forgery at a returned commitment gives a solution at the user's seed**: for `σ*` and a
returned `σ ≠ σ*` both verifying on `bm` under the key of the seed `ξ` with the same commitment,
`secondSigVec` is a solution for the key-generation matrix of `ξ`, at an approved parameter set. -/
theorem keyGenKernel_of_sameW1 (hp : p.isApproved) (ξ : Bytes 32) {H : X → Y}
    {f : (Bc).PK × (Bc).BMsg × (Bc).BSig} {σ : (Bc).BSig}
    (hv : (Bc).bverify H f.1 f.2.1 f.2.2 = true) (hpk : (Bc).pk ξ = f.1) (hne : f.2.2 ≠ σ)
    (hσv : (Bc).bverify H f.1 f.2.1 σ = true)
    (hw : w1Of (concretePrimitivesKeyGen p) (concreteEnc p) f.1 σ =
      w1Of (concretePrimitivesKeyGen p) (concreteEnc p) f.1 f.2.2) :
    Lattice.KeyGenKernel p (concretePrimitivesKeyGen p) (Lattice.msisStrictBoundZ p)
      (Lattice.msisBoundU p) ξ
      (secondSigVec p (pubPk (concretePrimitivesKeyGen p) f.1) f.2.2 σ) := by
  obtain ⟨pk, bm, σ'⟩ := f
  dsimp only at hv hpk hne hσv hw ⊢
  subst hpk
  have hv₁ : ringVerify (concretePrimitivesKeyGen p) (O.hOrc H) (concreteEnc p)
      (keyGenFromSeed p (concretePrimitivesKeyGen p) ξ).1 bm
      (w1Of (concretePrimitivesKeyGen p) (concreteEnc p) ((Bc).pk ξ) σ') σ' = true := hv
  have hv₂ : ringVerify (concretePrimitivesKeyGen p) (O.hOrc H) (concreteEnc p)
      (keyGenFromSeed p (concretePrimitivesKeyGen p) ξ).1 bm
      (w1Of (concretePrimitivesKeyGen p) (concreteEnc p) ((Bc).pk ξ) σ) σ = true := hσv
  rw [hw] at hv₂
  rw [pubPk_pk_w1BaseSigner]
  exact keyGenKernel_secondSigVec hp ξ hne hv₁ hv₂

omit [AddGroup Y] [Fintype X] [DecidableEq X] [Nonempty X] [Fintype Y] [DecidableEq Y]
  [Nonempty Y] in
/-- A signature returned to user `i` is not one never returned to `i`. -/
theorem ne_of_returned {hist : MUHist SO n} {i : Fin n} {bm : (Bc).BMsg} {σ σ' : (Bc).BSig}
    (h : Returned hist i bm σ) (hn : ¬ ReturnedSig hist i σ') : σ' ≠ σ := by
  rintro rfl
  exact hn ⟨bm, h⟩

omit [AddGroup Y] [Fintype X] [DecidableEq X] [Nonempty X] [Fintype Y] [DecidableEq Y]
  [Nonempty Y] in
/-- **The readout of a forgery at a returned commitment wins the Module-SIS game** at the users'
seeds, at an approved parameter set. -/
theorem msisReadout_wins (hp : p.isApproved) {keys : Fin n → Bytes 32} {H : X → Y}
    {o : Option (((Bc).PK × (Bc).BMsg × (Bc).BSig) × MUHist SO n)}
    (h : ∃ q ∈ o, SameW1Forges keys H q.1 q.2) :
    Lattice.Wins (Lattice.multiValid (Lattice.KeyGenKernel p (concretePrimitivesKeyGen p)
      (Lattice.msisStrictBoundZ p) (Lattice.msisBoundU p)) n) keys (msisReadout keys H o) := by
  classical
  rw [msisReadout, dite_eq_left_of_eq_true (eq_true h)]
  refine ⟨_, rfl, ?_⟩
  have hv := h.choose_spec.2.1
  have hs := h.choose_spec.2.2.choose_spec.choose_spec
  exact keyGenKernel_of_sameW1 hp _ hv hs.1
    (ne_of_returned hs.2.2.2.1 hs.2.2.1) hs.2.2.2.2.1 hs.2.2.2.2.2

/-- **The never-returned strong game is at most the Module-SIS win probability of `B₂` plus the
probability of a forgery fresh for its commitment**, at an approved parameter set: every adversary
`A` of the multi-user game at a signing oracle of the base signer, with `Q` requests. -/
theorem muSufSigProb_le_msis_add_fresh (hp : p.isApproved) (A : MUAdversary SO n V t) (Q : ℕ) :
    muSufSigProb A Q ≤
      Lattice.keyGenMsisMultiWinProb p (concretePrimitivesKeyGen p) (Lattice.msisStrictBoundZ p)
          (Lattice.msisBoundU p) n (msisReduction A Q) +
        (muLaw A Q).toOuterMeasure {x | ∃ q ∈ x.2.2, FreshW1Forges x.1 x.2.1 q.1 q.2} := by
  classical
  refine le_trans (MeasureTheory.measure_mono (μ := (muLaw A Q).toOuterMeasure)
    (s := {x | ∃ q ∈ x.2.2, SigStrongForges x.1 x.2.1 q.1 q.2})
    (t := {x | ∃ q ∈ x.2.2, SameW1Forges x.1 x.2.1 q.1 q.2} ∪
      {x | ∃ q ∈ x.2.2, FreshW1Forges x.1 x.2.1 q.1 q.2}) fun x hx => ?_)
    ((MeasureTheory.measure_union_le _ _).trans (add_le_add ?_ le_rfl))
  · obtain ⟨q, hq, hs⟩ := hx
    rcases sigStrongForges_cases hs with h | h
    · exact Or.inl ⟨q, hq, h⟩
    · exact Or.inr ⟨q, hq, h⟩
  -- the two games, averaged over the seeds and the oracle
  simp only [muLaw, runLaw, Lattice.keyGenMsisMultiWinProb, Lattice.winProb, Lattice.winLaw,
    msisReduction, PMF.toOuterMeasure_bind_apply, PMF.toOuterMeasure_map_apply]
  refine ENNReal.tsum_le_tsum fun keys => mul_le_mul' le_rfl ?_
  refine ENNReal.tsum_le_tsum fun H => mul_le_mul' le_rfl ?_
  exact MeasureTheory.measure_mono fun o ho => msisReadout_wins hp ho

end GordieHowe.Ring.MLDSAW1
