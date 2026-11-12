-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Ring.MLDSAW1KeyFreeBridge
public import GordieHowe.Applications.Ring.MLDSAW1HiddenGame
public import GordieHowe.Applications.Ring.MLDSAW1FreshHop

@[expose] public section

/-!
# From the ring game to the key-free relay challenger, for the ML-DSA ring publishing `w₁`

The hybrids from BKM06 Definition 7 (`insiderForgeProb`) of the ring publishing `w₁` with hedged
masks to the game against the key-free relay challenger `w1C2`, composed:

1. hedged to fresh masks (`hedgedScheme.insiderForgeProb_le`);
2. the commitment hashes of all attempted points reprogrammed (`insiderForgeProb_fresh_le_reprog`);
3. only the kept points' assignments in force (`forgeProb_reprog_le_w1C1`, hidden reads);
4. the key-free signer (`runLawIn_w1C1_le_w1C2`).

- `w1FreshAdv`: the adversary against the fresh scheme (`GameAdversary.relabel`).
- `insiderForgeProb_le_w1C2`: the composition.
-/

open Finset
open scoped ENNReal BigOperators

namespace GordieHowe.Ring.MLDSAW1

open _root_.MLDSA GordieHowe.MLDSA GordieHowe.MLDSA.Regularity GordieHowe.RingSignature
  GordieHowe.Quantum

variable {X Y : Type} {p : Params} {T : ℕ} {Msg : Type} {N reps : ℕ}

/-! ### The average over the key coins -/

/-- **The average of one coordinate of a uniform tuple is the average**: for `f : K → ℝ`, the
average over `keys : Fin n → K` of `f (keys s)` is `𝔼 c, f c`. -/
theorem sum_inv_card_mul_apply {K : Type} [Fintype K] [Nonempty K] [DecidableEq K] {n : ℕ}
    (f : K → ℝ) (s : Fin n) :
    ∑ keys : Fin n → K, (Fintype.card (Fin n → K) : ℝ)⁻¹ * f (keys s) = 𝔼 c, f c := by
  have hsum : ∑ keys : Fin n → K, f (keys s) =
      (Fintype.card ({j // j ≠ s} → K) : ℝ) * ∑ c, f c := by
    rw [Fintype.sum_equiv (Equiv.piSplitAt s fun _ => K) (fun keys => f (keys s))
      (fun q => f q.1) (fun _ => rfl), Fintype.sum_prod_type]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [Finset.mul_sum]
  rw [← Finset.mul_sum, hsum, Finset.expect_eq_sum_div_card, Finset.card_univ,
    Fintype.card_congr (Equiv.piSplitAt s fun _ => K), Fintype.card_prod]
  have h1 : (Fintype.card K : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have h2 : (Fintype.card ({j // j ≠ s} → K) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  push_cast
  field_simp

/-- **The average of a sum over the users is `n` times the average**: for `f : K → ℝ`, the
average over `keys : Fin n → K` of `Σ_s f (keys s)` is `n · 𝔼 c, f c`. -/
theorem sum_inv_card_mul_sum_apply {K : Type} [Fintype K] [Nonempty K] [DecidableEq K] {n : ℕ}
    (f : K → ℝ) :
    ∑ keys : Fin n → K, (Fintype.card (Fin n → K) : ℝ)⁻¹ * ∑ s, f (keys s) = n * 𝔼 c, f c := by
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [sum_inv_card_mul_apply f]
  simp

section Chain

open GordieHowe.Signature

variable {prims : Primitives p} [NeZero (bucketCount p)] [nttOps : NTTRingOps]
  [Fintype prims.Power2High] [DecidableEq prims.Power2High] [Fintype prims.Hint]
  [DecidableEq prims.Hint] [Nonempty (MaskBox p)] [Fintype Msg] [DecidableEq Msg]
  [Fintype Y] [DecidableEq Y] [Nonempty Y] [Fintype X] [DecidableEq X] [Nonempty X]
  {O : W1Oracles X Y p prims Msg N reps} {M : MaskOracle X Y p T Msg} {βmin : ℚ≥0} {tol : ℕ}
  {enc : Vector prims.High p.k → BucketVec p} {k D : ℕ} [NeZero D] {RMsg : Type} [Fintype RMsg]
  [DecidableEq RMsg] {bmsg : KeyRing (PubKey p prims) N → RMsg → Msg}
  {Pf PC : Type} [Fintype Pf] [DecidableEq Pf] [Fintype PC]
  [DecidableEq PC] [Nonempty PC]
  {PS : ProofSystem X Y (RingSignature.RingStmt (hedgedBase prims O M βmin tol enc k D bmsg))
    (RingSignature.RingWitOf (FIPSSignature p prims)) ⟨Pf, PC⟩}
  {adm : KeyRing (PubKey p prims) N → Prop}
  [hadm : DecidablePred adm] {n : ℕ} [NeZero n]
  {Y₁ Y₂ : Type} [AddGroup Y] [AddGroup Y₁] [AddGroup Y₂] [Fintype Y₁] [DecidableEq Y₁]
  {Stmt Wit X₀ Rq : Type}

local notation "Bf" => freshBase prims O M βmin tol enc k D bmsg
local notation "Sh" => hedgedScheme prims O M βmin tol enc k D bmsg PS adm
local notation "Sf" => freshScheme prims O M βmin tol enc k D bmsg PS adm
local notation "PSf" => PS

attribute [local instance] admDecF

omit [Fintype X] [DecidableEq X] [Nonempty X] [NeZero n] [AddGroup Y] [Fintype Pf] [DecidableEq Pf]
  [Fintype PC] [DecidableEq PC] [Nonempty PC] [Fintype Msg] [DecidableEq Msg] [Fintype Y]
  [DecidableEq Y] [Nonempty Y] in
/-- **The average point bound over the key coins is `n · commitPointAt`**: the key-generation
matrix of a fresh scheme's secret key is `keyGenMatrix` of its seed. -/
theorem sum_inv_card_mul_commitPointMax :
    ∑ keys : Fin n → (Sf).KeyCoins, (Fintype.card (Fin n → (Sf).KeyCoins) : ℝ)⁻¹ *
        ∑ s, commitPointMax (prims.expandA ((Sf).sk (keys s)).rho) =
      n * commitPointAt prims :=
  sum_inv_card_mul_sum_apply (K := Bytes 32)
    (fun seed => commitPointMax (GordieHowe.Lattice.keyGenMatrix p prims seed))

variable (prims O M βmin tol enc k D bmsg PS adm) in
/-- **The adversary against the fresh scheme**: an adversary of BKM06 Definition 7 against the
hedged scheme, its requests and responses relabelled (`GameAdversary.relabel`). -/
noncomputable abbrev w1FreshAdv {t : ℕ}
    (A : InsiderAdversary (Sh) n (OracleView.queriesOnly X Y) t) :
    InsiderAdversary (Sf) n (OracleView.queriesOnly X Y) t :=
  GameAdversary.relabel (unfReqEquiv (sideHopNone prims O M βmin tol enc k D bmsg PS adm) n)
    (unfRespEquiv (sideHopNone prims O M βmin tol enc k D bmsg PS adm)) A

/-- **From BKM06 Definition 7 to the key-free relay challenger** (module docstring): the
probability of a forgery against the hedged scheme is at most the probability of the forgery
event against `w1C2` for the relabelled adversary, plus the four hybrids' terms. The encoding of the
main requests `penc keys` may read the key coins. -/
theorem insiderForgeProb_le_w1C2 [Nonempty Y₁]
    (sp : Y ≃+ Y₁ × Y₂) (h : W1OracleFacts O M sp)
    (hPSm : ∀ x w c H H', Quantum.AgreeOffRange M.pt H H' →
      (PS.prove x w c).run H = (PS.prove x w c).run H')
    (hPSv : ∀ x π H H', Quantum.AgreeOffRange M.pt H H' → PS.verify H x π = PS.verify H' x π)
    (hPS : ProverReadsPub O PS sp)
    (h_laws : SigningLaws prims) (hv : VerifyLaws prims)
    (henc : ∀ w : RqVec p.k, enc (prims.highBitsVec w) = bucketsOf (rqVecCoeffs w))
    (hs1 : ∀ seed, polyVecBounded (keyGen prims seed).2.s1 p.eta)
    (hs2 : ∀ seed, polyVecBounded (keyGen prims seed).2.s2 p.eta)
    {Vp : RingSignature.RingStmt (hedgedBase prims O M βmin tol enc k D bmsg) →
      Pf → OracleProg X Y Bool} {qv : ℕ} (hV : PS.VerifiesBy Vp qv)
    (rel : Stmt → Wit → Prop) [DecidableRel rel]
    (P : NARG.Prover X Y Stmt Wit Pf (PSf).Coins) (μ : PMF (PSf).Coins)
    (hPc : μ = PMF.uniformOfFintype (PSf).Coins)
    (penc : (Fin n → (Bf).KeyCoins) → MURequest (SignOracle.none (Bf).core) n ⊕ Rq →
      QROM.ProofQuery Stmt Wit)
    (stmtP : RingSignature.RingStmt Bf → OracleProg X Y X₀)
    (toR : X₀ → RingSignature.Insider.Req Bf PSf adm n × ℕ → (Bf).BSig → Rq)
    (dummyR : RingSignature.Insider.Req Bf PSf adm n × ℕ → Rq) {qs : ℕ}
    (hs : ∀ x, (stmtP x).QueriesLE qs) (idle : MURequest (SignOracle.none (Bf).core) n ⊕ Rq)
    (hPR : ∀ keys, ProverRelays O enc sp P (penc keys) stmtP toR keys)
    (hKR : ∀ keys, KeptInRel enc rel (penc keys) stmtP toR keys)
    {t w : ℕ} (A : InsiderAdversary (Sh) n (OracleView.queriesOnly X Y) t)
    (hw : ∀ (keys : Fin n → (Sf).KeyCoins) a,
      ((w1FreshAdv prims O M βmin tol enc k D bmsg PS adm A
        (fun i => (Bf).pk (keys i), ())).alg a).width ≤ w) (Q : ℕ) :
    (insiderForgeProb A Q).toReal ≤
      ((runLawIn (fun keys _ => w1FreshAdv prims O M βmin tol enc k D bmsg PS adm A
          (fun i => (Bf).pk (keys i), ()))
        (fun keys => w1C2 prims O M βmin tol enc k D bmsg PS adm sp rel P μ (penc keys) stmtP toR
          dummyR hs idle keys Q)).toOuterMeasure
        {x | ∃ q ∈ x.2.2, Forges x.1 q.2.2 q.1 (Challenger.histOf q.2.1)}).toReal +
      ((Q * k).choose 2 * (2 ^ 256 : ℝ)⁻¹ + 2 * t * √((Q * k : ℕ) * (2 ^ 256 : ℝ)⁻¹)) +
      Q * (√((k * T : ℝ) * (n * commitPointAt prims) *
            (t + max (Sf).q (SideOracle.none Sf).q * Q)) +
        (k * T : ℝ) * (n * commitPointAt prims) *
            (t + max (Sf).q (SideOracle.none Sf).q * Q) / 2) +
      2 * √(t + w * qv + Q : ℝ) *
        √((t + w * qv + (1 + k * T + max (Sf).q (SideOracle.none Sf).q) * Q : ℝ) *
          (Q * (2 * k * T * (n * commitPointAt prims)))) +
      Q * (((k * T).choose 2 : ℝ) * (n * commitPointAt prims)) := by
  have h01 : (insiderForgeProb A Q).toReal ≤
      (insiderForgeProb (w1FreshAdv prims O M βmin tol enc k D bmsg PS adm A) Q).toReal +
      ((Q * k).choose 2 * (2 ^ 256 : ℝ)⁻¹ + 2 * t * √((Q * k : ℕ) * (2 ^ 256 : ℝ)⁻¹)) :=
    hedgedScheme.insiderForgeProb_le h.toW1MaskPoints hPSm hPSv (fun _ _ _ => rfl) A Q
  have h12 := insiderForgeProb_fresh_le_reprog sp h.toW1SplitMask
    (w1FreshAdv prims O M βmin tol enc k D bmsg PS adm A) Q
  have h23 := forgeProb_reprog_le_w1C1 sp h.toW1SplitMask hPS h_laws hv henc hs2 hV
    (w1FreshAdv prims O M βmin tol enc k D bmsg PS adm A) hw Q
  have h34 : (runLawIn (fun keys H => w1FreshAdv prims O M βmin tol enc k D bmsg PS adm A
        (fun i => (Bf).pk (keys i), (OracleView.queriesOnly X Y).view H))
        (fun keys => w1C1 (SideOracle.none Sf) sp keys Q)).toOuterMeasure
        {x | ∃ q ∈ x.2.2, Forges x.1 q.2.2 q.1 (Challenger.histOf q.2.1)} ≤
      (runLawIn (fun keys _ => w1FreshAdv prims O M βmin tol enc k D bmsg PS adm A
          (fun i => (Bf).pk (keys i), ()))
        (fun keys => w1C2 prims O M βmin tol enc k D bmsg PS adm sp rel P μ (penc keys) stmtP toR
          dummyR hs idle keys Q)).toOuterMeasure
        {x | ∃ q ∈ x.2.2, Forges x.1 q.2.2 q.1 (Challenger.histOf q.2.1)} +
      ∑' keys, PMF.uniformOfFintype (Fin n → (Bf).KeyCoins) keys *
        (Q * ENNReal.ofReal (((k * T).choose 2 : ℝ) *
          ∑ s, commitPointMax (prims.expandA ((Sf).sk (keys s)).rho))) :=
    runLawIn_w1C1_le_w1C2 sp h.toW1SplitMask h.hO hPS h_laws hv henc rel P μ hPc penc
      stmtP toR dummyR hs idle (fun keys s => hs1 _) (fun keys s => hs2 _) hPR hKR Q
      (fun keys => w1FreshAdv prims O M βmin tol enc k D bmsg PS adm A
        (fun i => (Bf).pk (keys i), ())) _
  have hfin : (∑' keys, PMF.uniformOfFintype (Fin n → (Bf).KeyCoins) keys *
      (Q * ENNReal.ofReal (((k * T).choose 2 : ℝ) *
        ∑ s, commitPointMax (prims.expandA ((Sf).sk (keys s)).rho)))) ≠ ⊤ := by
    rw [tsum_fintype]
    exact ENNReal.sum_ne_top.2 fun _ _ => ENNReal.mul_ne_top (PMF.apply_ne_top _ _)
      (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) ENNReal.ofReal_ne_top)
  have h34' := (ENNReal.toReal_mono (ENNReal.add_ne_top.2
    ⟨ne_top_of_le_ne_top ENNReal.one_ne_top (PMF.toOuterMeasure_apply_le_one _ _), hfin⟩) h34).trans_eq
    (ENNReal.toReal_add (ne_top_of_le_ne_top ENNReal.one_ne_top (PMF.toOuterMeasure_apply_le_one _ _)) hfin)
  have hS : ∀ keys : Fin n → (Sf).KeyCoins,
      0 ≤ ∑ s, commitPointMax (prims.expandA ((Sf).sk (keys s)).rho) := fun _ =>
    Finset.sum_nonneg fun _ _ => (ENNReal.toReal_nonneg).trans
      (toReal_map_realBuckets_le_commitPointMax _ (Classical.arbitrary _))
  have hcard : ∀ c : ℝ, ∑ keys : Fin n → (Sf).KeyCoins,
      (Fintype.card (Fin n → (Sf).KeyCoins) : ℝ)⁻¹ *
        (c * ∑ s, commitPointMax (prims.expandA ((Sf).sk (keys s)).rho)) =
      c * (n * commitPointAt prims) := fun c => by
    rw [← sum_inv_card_mul_commitPointMax (prims := prims) (O := O) (M := M) (βmin := βmin)
      (tol := tol) (enc := enc) (k := k) (D := D) (bmsg := bmsg) (PS := PS) (adm := adm),
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring
  have hlast : (∑' keys, PMF.uniformOfFintype (Fin n → (Bf).KeyCoins) keys *
      (Q * ENNReal.ofReal (((k * T).choose 2 : ℝ) *
        ∑ s, commitPointMax (prims.expandA ((Sf).sk (keys s)).rho)))).toReal =
      Q * (((k * T).choose 2 : ℝ) * (n * commitPointAt prims)) := by
    rw [tsum_fintype, ENNReal.toReal_sum fun _ _ => ENNReal.mul_ne_top (PMF.apply_ne_top _ _)
      (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) ENNReal.ofReal_ne_top),
      ← hcard, Finset.mul_sum]
    refine Finset.sum_congr rfl fun keys _ => ?_
    rw [PMF.uniformOfFintype_apply, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_inv,
      ENNReal.toReal_natCast, ENNReal.toReal_natCast,
      ENNReal.toReal_ofReal (mul_nonneg (Nat.cast_nonneg _) (hS keys))]
    ring
  rw [hcard] at h12
  rw [hcard] at h23
  rw [hlast] at h34'
  linarith
