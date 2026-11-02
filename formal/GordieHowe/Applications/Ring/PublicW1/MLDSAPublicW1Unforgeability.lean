-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Ring.PublicW1.MLDSAPublicW1
public import GordieHowe.Applications.Ring.InsiderStrong
public import GordieHowe.Applications.Ring.Unforgeability

@[expose] public section

/-!
# Unforgeability of the ML-DSA ring signature publishing `w₁`

BKM06 Definition 7 (unforgeability with respect to insider corruption; Bender, Katz, Morselli,
TCC 2006, LNCS p. 67; ePrint 2005/304, p. 7) for the ring signature whose statement carries the
ML-DSA commitment `w₁`, in the game of `GordieHowe/Applications/Ring/Games.lean`
(`BKMAdversary.insiderWinProb`), for both base-message maps, and the converted-signature game.

The base scheme is `w1SigScheme`: published keys `(ρ, t₁, t₀)` from `keyGen` (FIPS 204 Algorithm 6
with `t₀` published), signatures `(w₁, (c̃, z, h))` carrying their commitment, public value `w₁`,
and verification `ringVerify` (FIPS 204 Algorithm 8 with the commitment hash `c̃ = H((tr, m), w₁)`
read from the hash `H` and the recomputed commitment required to equal `w₁`). A verifying
signature's `w₁` is the commitment recomputed from the key and `(c̃, z, h)`
(`w1SigScheme_pub_eq_of_verify`). The signer is a parameter (`W1Signer`: finite signing coins, as
`Falcon512.Ring.Native.Signer`); the scheme's properties used below are hypotheses: correctness
error `εc` (`SigScheme.CorrectWithin`) and, for converted signatures, the probability `γ` of
guessing a signature from its `w₁` (`SigScheme.SigGivenPubLe`: the conditional min-entropy of
`(c̃, z, h)` given `w₁`).

- `insiderWinProb_le_of_bindsRing`: for a base message that binds the ring (`BindsRing`, as BKM06's
  generic construction signs `M ‖ PK_1 ‖ … ‖ PK_n`, Section 5), knowledge soundness of spBCS only
  (`BKMAdversary.insiderWinProb_le`): the extracted signature is a fresh base forgery of the
  multi-user game with adaptive corruption (Bader, Hofheinz, Jager, Kiltz, Li, TCC 2015, ePrint
  2014/797, Definition 2, p. 6), the reduction answering ring-signing requests with the honest
  prover on base signatures from the signing oracle.
- `insiderWinProb_le_converted`: converted signatures (`bind R m = m`): ring-signing requests are
  answered with a real signature `(w₁, σ)` from the signing oracle, its `w₁` published and the
  proof simulated (`BKMAdversary.insiderWinProb_le_of_strongUnforgeability`); the base game is
  multi-user strong unforgeability with adaptive corruption (`SignRelayForger.success`), since the
  forgery's message may have been signed for another ring, and an extracted signature equal to an
  oracle's costs `Q · γ`. No simulation of `w₁` (no regularity hybrid) enters: the published `w₁`
  are the real ones. ML-DSA is designed to be strongly unforgeable (FIPS 204, §3.1, p. 9: "ML-DSA
  is designed to be strongly existentially unforgeable under chosen message attack (SUF-CMA)");
  Kiltz, Lyubashevsky, Schaffner, EUROCRYPT 2018, ePrint 2017/916, Theorem 3.1 and eq. (21),
  bound the SUF-CMA advantage of Dilithium in the QROM. The theorems below take the assumption as
  a bound on `SignRelayForger.success` of the earlier interface. Its form over a class of
  adversaries of the interactive model is `Signature.MUSufCmaHard`
  (`GordieHowe/Model/Signature/Assumptions.lean`); `MLDSASufCma` and `MLDSAMUSufCma`
  (`GordieHowe/Applications/Ring/BaseSignerAssumptions.lean`) name it at `mldsaBaseSigner`.
- `convertedWinProb_le`: the converted-signature game at `bind R m = m`, knowledge soundness only
  (`RingAdversary.convertedWinProb_le`).

## Scope of the model

- The hash `H` of the base scheme is a fixed function here (the theorems hold at every `H`); the
  base assumptions are on `w1SigScheme` at that `H`.
- The game of `Games.lean` answers a ring-signing request `(s, R, m)` with one base signature by
  `s` on `bind R m`. At a ring-binding `bind` the signer can read the ring from its message. At
  `bind R m = m` the base signer sees only `m`, and this game's signing oracle does not receive the
  ring. No `W1Signer` is constructed from the flattened ring signer `pubSigner` of
  `MLDSAPublicW1.lean`.
-/

namespace GordieHowe.Ring.MLDSAW1

open _root_.MLDSA GordieHowe.MLDSA
open IOP GordieHowe.SPBCS GordieHowe.QROM Quantum SPTerm
open scoped ENNReal NNReal

variable {p : Params} (prims : Primitives p)

/-- **A signer of the ML-DSA scheme publishing `w₁`** with messages `Msg`: finite signing coins and
signing with them, outputting the commitment `w₁` with the FIPS 204 signature `(c̃, z, h)`. Which
signer (the FIPS 204 hedged signer with its bounded attempt loop, or a flattened ring signer for
rings read from the message) is a parameter; its properties are hypotheses where used. -/
structure W1Signer (p : Params) (prims : Primitives p) (Msg : Type) where
  /-- The coins of signing. -/
  SignCoins : Type
  [instFintypeSignCoins : Fintype SignCoins]
  [instDecEqSignCoins : DecidableEq SignCoins]
  [instNonemptySignCoins : Nonempty SignCoins]
  /-- Signing with drawn coins: the commitment and the signature. -/
  signWith : SecretKey p → Msg → SignCoins → BucketVec p × FIPSSignature p prims

attribute [instance] W1Signer.instFintypeSignCoins W1Signer.instDecEqSignCoins
  W1Signer.instNonemptySignCoins

variable [NeZero (bucketCount p)] [nttOps : NTTRingOps] [Fintype prims.Hint]
  [Fintype prims.Power2High] [DecidableEq prims.Power2High] [DecidableEq prims.Hint]
  {Msg : Type} [Fintype Msg] [DecidableEq Msg]

/-- **The ML-DSA scheme publishing `w₁`** at the hash `H` (standing for `H(µ ‖ w1Encode(w₁))` on
`(tr, m)` and bucket vectors), the encoding `enc` of recomputed commitments as bucket vectors and
the signer `G`: published keys `(ρ, t₁, t₀)` from `keyGen`, signatures `(w₁, (c̃, z, h))` with
public value `w₁`, and verification `ringVerify` (FIPS 204 Algorithm 8 with the recomputed
commitment required to equal `w₁`). -/
abbrev w1SigScheme (H : Orc p Msg) (enc : Vector prims.High p.k → BucketVec p)
    (G : W1Signer p prims Msg) : SigScheme where
  PK := PubKey p prims
  SK := SecretKey p
  Msg := Msg
  Sig := BucketVec p × FIPSSignature p prims
  Pub := BucketVec p
  KeyCoins := _root_.MLDSA.Bytes 32
  SignCoins := G.SignCoins
  keyGen := keyGen prims
  pub := Prod.fst
  signWith := G.signWith
  verify pk m σ := ringVerify prims H enc (pubPk prims pk) m σ.1 σ.2

/-- **A verifying signature's `w₁` is the commitment recomputed from the key and `(c̃, z, h)`**:
`w₁ = enc(UseHint(h, Â·z − c·t₁·2^d))` with `Â = ExpandA(ρ)` and `c = SampleInBall(c̃)`. -/
theorem w1SigScheme_pub_eq_of_verify {H : Orc p Msg} {enc : Vector prims.High p.k → BucketVec p}
    {G : W1Signer p prims Msg} {pk : PubKey p prims} {m : Msg}
    {σ : BucketVec p × FIPSSignature p prims}
    (h : (w1SigScheme prims H enc G).verify pk m σ = true) :
    σ.1 = enc (prims.useHintVec σ.2.h (computeWApprox p prims (prims.expandA pk.1)
      (prims.sampleInBall σ.2.cTilde) σ.2.z pk.2.1)) := by
  simp only [ringVerify, pubPk, Bool.and_eq_true] at h
  exact (of_decide_eq_true h.1.1.2).symm

section SPBCS

variable {H : Orc p Msg} {enc : Vector prims.High p.k → BucketVec p} {G : W1Signer p prims Msg}
  {n N : ℕ} {RMsg : Type} [Fintype RMsg] [DecidableEq RMsg]
  {k e : ℕ} {ι : Type} {τ : SPTerm ι} {Mg : Merges τ} {nr : ι → ℕ}
  {P : (j : ι) → ProtocolSpec (nr j)} [∀ j i, Fintype ((P j).Challenge i)]
  [∀ j i, DecidableEq ((P j).Challenge i)] [∀ j i, Nonempty ((P j).Challenge i)] {kN kS L : ℕ}
  (Λ : SiteLayout Mg) {B : ℕ} {R : Type} [Fintype R] [Nonempty R]

/-- **BKM06 Definition 7 for the ML-DSA ring publishing `w₁` with a base message that binds the
ring** (`BindsRing`, `hbind`), from knowledge soundness of spBCS (`hrbr`) and the format bound
(`hb`) (`BKMAdversary.insiderWinProb_le` at `w1SigScheme`): the probability that an adversary of
BKM06 with at most `Q` requests and `t` queries of its own wins is at most the success probability
of the explicit forger of the multi-user game with adaptive corruption on `w1SigScheme` plus the
knowledge error of spBCS at `t + Q · q + kq` queries. -/
theorem insiderWinProb_le_of_bindsRing
    {M : SPBCS Mg P (RingStmt (w1SigScheme prims H enc G) RMsg N) k kN kS L e}
    [∀ j i, Fintype ((M.comp j).MessageWrite i)] {E : (j : ι) → (M.comp j).Encoder}
    {Vr : RingStmt (w1SigScheme prims H enc G) RMsg N → FullTr P τ → Bool}
    {Qs : ∀ x, M.IOPQueries Vr x} (hb : M.FormatBounds Qs B B)
    (honest : RingWit (w1SigScheme prims H enc G) → R →
      CausalProver P τ (RingStmt (w1SigScheme prims H enc G) RMsg N))
    {Ext : CausalExtractor P τ (RingStmt (w1SigScheme prims H enc G) RMsg N)
      (RingWit (w1SigScheme prims H enc G))}
    {St : CausalStateFn P τ (RingStmt (w1SigScheme prims H enc G) RMsg N)} {ε : ChIdx P τ → ℝ≥0}
    (bind : List (PubKey p prims) → RMsg → Msg) (adm : List (PubKey p prims) → Prop)
    (hbind : BindsRing N (Sch := w1SigScheme prims H enc G) bind)
    (hrbr : CausalRBRKnowledgeSound (ringRel adm bind) Vr Ext St ε)
    {t Q : ℕ} (A : BKMAdversary (M.qVerifier Qs B B) (M.Response B) n t Q) :
    A.insiderWinProb (((M.niProver Λ honest E hb).mapOutput some).encode queryEncoding) bind adm ≤
      (A.forger (((M.niProver Λ honest E hb).mapOutput some).encode queryEncoding) bind adm
          (M.dbExtractBits Ext)).success +
        knowledgeError k e (kqOf Mg nr B B)
          (t + Q * (((M.niProver Λ honest E hb).mapOutput some).encode queryEncoding).q +
            kqOf Mg nr B B) M.senc.digestsPerInput Mg.nJ (maxError ε) :=
  BKMAdversary.insiderWinProb_le (Sch := w1SigScheme prims H enc G) (n := n) (RMsg := RMsg) (N := N)
    (M := M) (adm := adm) bind Λ hb honest A hbind hrbr

/-- **BKM06 Definition 7 for the ML-DSA ring publishing `w₁` with converted signatures**
(`bind R m = m`), from strong unforgeability
(`BKMAdversary.insiderWinProb_le_of_strongUnforgeability` at `w1SigScheme`): for a signer with
correctness error `εc` (`hcorr`) whose signatures are guessed from their `w₁` with probability at
most `γ` (`hγ`), and the spBCS compilation `M` with
honest-verifier zero knowledge at error `δ` (`hvzk`), round-by-round knowledge soundness (`hrbr`),
the format bound `B` (`hb`) and digests of at least one byte (`hk`), the probability that an
adversary of BKM06 with at most `Q` requests and `t` queries of its own wins is at most the
success probability of the explicit forger of the multi-user strong-unforgeability game with
adaptive corruption on `w1SigScheme` (`strongForgerSuccess`), plus `Q · γ`, the zero-knowledge
error, the simulation-extraction error, the knowledge error and `2 Q εc`. -/
theorem insiderWinProb_le_converted [Inhabited prims.Hint] [NeZero n] [Nonempty Msg]
    {M : SPBCS Mg P (RingStmt (w1SigScheme prims H enc G) Msg N) k kN kS L e}
    [∀ j i, Fintype ((M.comp j).MessageWrite i)] {E : (j : ι) → (M.comp j).Encoder}
    {Vr : RingStmt (w1SigScheme prims H enc G) Msg N → FullTr P τ → Bool}
    {Qs : ∀ x, M.IOPQueries Vr x} (hb : M.FormatBounds Qs B B)
    (honest : RingWit (w1SigScheme prims H enc G) → R →
      CausalProver P τ (RingStmt (w1SigScheme prims H enc G) Msg N))
    (VE : M.ViewEncoder E Qs) {Pub : Type} (pub : RingStmt (w1SigScheme prims H enc G) Msg N → Pub)
    (Sim : CausalJointSimulator VE.MV Pub) (T : M.Preimages) (adm : List (PubKey p prims) → Prop)
    (hk : 0 < k) {εc : ℝ≥0∞} (hcorr : (w1SigScheme prims H enc G).CorrectWithin εc) {γ : ℝ≥0∞}
    (hγ : (w1SigScheme prims H enc G).SigGivenPubLe γ) {δ : ℝ≥0}
    (hvzk : CausalHVZK VE.MV (ringRel adm fun _ m => m) honest pub Sim δ)
    {Ext : CausalExtractor P τ (RingStmt (w1SigScheme prims H enc G) Msg N)
      (RingWit (w1SigScheme prims H enc G))}
    {St : CausalStateFn P τ (RingStmt (w1SigScheme prims H enc G) Msg N)} {ε : ChIdx P τ → ℝ≥0}
    (hrbr : CausalRBRKnowledgeSound (ringRel adm fun _ m => m) Vr Ext St ε)
    {t Q : ℕ} (A : BKMAdversary (M.qVerifier Qs B B) (M.Response B) n t Q) :
    A.insiderWinProb (((M.niProver Λ honest E hb).mapOutput some).encode queryEncoding)
        (fun _ m => m) adm ≤
      A.strongForgerSuccess Λ VE pub Sim T (fun _ m => m) adm Ext + Q * γ +
        ENNReal.ofReal (M.zkError δ t Q) +
        M.simExtractionError (kqOf Mg nr B B) (maxError ε)
          (M.niJointSimulatorProg Λ VE.toViewRead B pub Sim T).q t Q +
        knowledgeError k e (kqOf Mg nr B B)
          (t + Q * (((M.niProver Λ honest E hb).mapOutput some).encode queryEncoding).q +
            kqOf Mg nr B B) M.senc.digestsPerInput Mg.nJ (maxError ε) +
        2 * Q * εc :=
  A.insiderWinProb_le_of_strongUnforgeability Λ hb honest VE pub Sim T (fun _ m => m) adm hk hcorr
    hγ hvzk hrbr

/-- **The converted-signature game for the ML-DSA ring publishing `w₁`** (`bind R m = m`), from
knowledge soundness of spBCS only (`RingAdversary.convertedWinProb_le` at `w1SigScheme`): a valid
ring signature on `(R*, m*)` whose members are honest and uncorrupted implies that some member was
asked to sign `m*`, except with the forger's success probability in the multi-user game with
adaptive corruption and the knowledge error. -/
theorem convertedWinProb_le
    {M : SPBCS Mg P (RingStmt (w1SigScheme prims H enc G) Msg N) k kN kS L e}
    [∀ j i, Fintype ((M.comp j).MessageWrite i)] {E : (j : ι) → (M.comp j).Encoder}
    {Vr : RingStmt (w1SigScheme prims H enc G) Msg N → FullTr P τ → Bool}
    {Qs : ∀ x, M.IOPQueries Vr x} (hb : M.FormatBounds Qs B B)
    (honest : RingWit (w1SigScheme prims H enc G) → R →
      CausalProver P τ (RingStmt (w1SigScheme prims H enc G) Msg N))
    {Ext : CausalExtractor P τ (RingStmt (w1SigScheme prims H enc G) Msg N)
      (RingWit (w1SigScheme prims H enc G))}
    {St : CausalStateFn P τ (RingStmt (w1SigScheme prims H enc G) Msg N)} {ε : ChIdx P τ → ℝ≥0}
    {adm : List (PubKey p prims) → Prop}
    (hrbr : CausalRBRKnowledgeSound (ringRel adm fun _ m => m) Vr Ext St ε)
    {t Q : ℕ} (A : RingAdversary (M.qVerifier Qs B B) (M.Response B) n t Q) :
    A.convertedWinProb (((M.niProver Λ honest E hb).mapOutput some).encode queryEncoding)
        (fun _ m => m) ≤
      (A.forger (((M.niProver Λ honest E hb).mapOutput some).encode queryEncoding) (fun _ m => m)
          (M.dbExtractBits Ext)).success +
        knowledgeError k e (kqOf Mg nr B B)
          (t + Q * (((M.niProver Λ honest E hb).mapOutput some).encode queryEncoding).q +
            kqOf Mg nr B B) M.senc.digestsPerInput Mg.nJ (maxError ε) :=
  A.convertedWinProb_le (fun _ m => m) Λ hb honest hrbr

end SPBCS

end GordieHowe.Ring.MLDSAW1
