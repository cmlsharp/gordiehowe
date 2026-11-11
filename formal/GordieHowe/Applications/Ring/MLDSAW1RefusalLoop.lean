-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Ring.MLDSAW1IdealDist

@[expose] public section

/-!
# The refusal of the w₁ ring loop on an admitted ring

The base signer of the ML-DSA ring publishing `w₁` refuses an admitted ring (one passing the
public check, with distinct message representatives) only when all `k` calls of the ring loop
reject. This file bounds that refusal.

- `refusalPubLaw_freshBase_none_le`: with fresh masks, at an oracle `H` at which the ring of a
  valid challenge is admitted, the signer of the challenge's user `0` refuses with probability at
  most `2 · lowError + k / D + (1 - Lk)^k`, plus `1` when the ring's defect exceeds `s`. The
  bounded finite-coin loop is within `k / D + r^k` of the unbounded loop of one ideal attempt
  (`tvDist_refusalPubLaw_freshBase_le`), which never refuses. The attempt's rejection probability
  is `r ≤ 1 - Lk` when the family bound of the low-defect challenges is below `1/2`
  (`keep_ge_of_familyBound_lt`), and `2 · lowError ≥ 1` otherwise.
- `expect_mul_refusalPubLaw_hedged_le`: averaged over a uniform oracle and weighted by any
  `[0, 1]`-valued function of the oracle's values at the base signer's points, the refusal
  probability with hedged masks is at most the one with fresh masks plus `C(k, 2) / 2^256`. For
  distinct nonces the hedged masks are the oracle's values on disjoint slices of the mask oracle's
  points, uniform and independent of the values at the base signer's points
  (`hedgedScheme.run_sign`); the nonces collide with probability at most `C(k, 2) / 2^256`.
-/

namespace GordieHowe.Ring.MLDSAW1

open _root_.MLDSA GordieHowe.MLDSA GordieHowe.MLDSA.Regularity GordieHowe.RingSignature PMF
open scoped ENNReal NNReal BigOperators

variable {X Y : Type} {p : Params} {T : ℕ} {Msg : Type} {N reps : ℕ}

/-- **A point's probability moves by at most the total variation distance**: the probability of
`a` under `p` is at most its probability under `q` plus `tvDist p q`. -/
theorem _root_.PMF.toReal_apply_le_add_tvDist {α : Type*} (p q : PMF α) (a : α) :
    (p a).toReal ≤ (q a).toReal + tvDist p q := by
  have h := abs_toOuterMeasure_sub_le_tvDist p q {a}
  rw [PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_apply_singleton] at h
  linarith [le_abs_self ((p a).toReal - (q a).toReal)]

/-- **A uniform function read along an embedding off a set `S`**: averaged over a uniform `H`, a
function of `H` and of the pullback of `H` along `e`, which reads `H` only on a set `S` disjoint
from the range of `e`, has the average of that function at an independent uniform second
argument (`splitAlong`). -/
theorem _root_.GordieHowe.expect_comp_embedding_eq {X' A Y' : Type*} [Fintype X'] [DecidableEq X']
    [Fintype A] [DecidableEq A] [Fintype Y'] [Nonempty Y'] (e : A ↪ X') (S : X' → Prop)
    (hS : ∀ x, S x → x ∉ Set.range e) (G : (X' → Y') → (A → Y') → ℝ)
    (hG : ∀ H H' g, (∀ x, S x → H x = H' x) → G H g = G H' g) :
    𝔼 H : X' → Y', G H (fun a => H (e a)) = 𝔼 H : X' → Y', 𝔼 g : A → Y', G H g := by
  set E := GordieHowe.splitAlong (Y' := Y') e
  refine (Fintype.expect_equiv E.symm (fun w => G (E.symm w) (fun a => E.symm w (e a)))
    (fun H => G H fun a => H (e a)) fun w => rfl).symm.trans ?_
  refine Eq.trans ?_ (Fintype.expect_equiv E.symm (fun w => 𝔼 g : A → Y', G (E.symm w) g)
    (fun H => 𝔼 g : A → Y', G H g) fun w => rfl)
  rw [← Finset.univ_product_univ, Finset.expect_product, Finset.expect_product]
  refine Finset.expect_congr rfl fun u _ => ?_
  obtain ⟨v₀⟩ : Nonempty (A → Y') := inferInstance
  have hloc : ∀ v g, G (E.symm (u, v)) g = G (E.symm (u, v₀)) g := fun v g =>
    hG _ _ g fun x hx => by
      rw [GordieHowe.splitAlong_symm_apply_of_notMem e u v (hS x hx),
        GordieHowe.splitAlong_symm_apply_of_notMem e u v₀ (hS x hx)]
  have hemb : ∀ v, (fun a => E.symm (u, v) (e a)) = v := fun v =>
    funext fun a => GordieHowe.splitAlong_symm_apply_embed e u v a
  calc 𝔼 v, G (E.symm (u, v)) (fun a => E.symm (u, v) (e a)) = 𝔼 v, G (E.symm (u, v₀)) v :=
        Finset.expect_congr rfl fun v _ => by rw [hemb v, hloc v v]
    _ = 𝔼 _v : A → Y', 𝔼 g, G (E.symm (u, v₀)) g :=
        (Finset.expect_const Finset.univ_nonempty _).symm
    _ = _ := Finset.expect_congr rfl fun v _ => Finset.expect_congr rfl fun g _ => (hloc v g).symm

/-- **The refusal probability as an average**: the probability that the base signer refuses is the
average over its uniform coins of the indicator that its ring-aware signer returns `none`. -/
theorem _root_.GordieHowe.RingSignature.BaseSigner.toReal_refusalPubLaw_none
    {N : ℕ} {TB : BaseTypes} [DecidableEq TB.PK]
    [DecidableEq TB.Pub]
    [Fintype TB.Coins]
    [Nonempty TB.Coins] (B : BaseSigner X Y N TB) (H : X → Y) (kc : B.KeyCoins) (R : KeyRing B.PK N)
    (m : B.Msg) :
    (B.refusalPubLaw H kc R m none).toReal =
      𝔼 cb : B.Coins,
        if ((B.bsign (B.sk kc) R (R.1.idxOf (B.pk kc)) m cb).run H).isNone then (1 : ℝ) else 0 := by
  classical
  unfold BaseSigner.refusalPubLaw
  rw [PMF.toReal_map_apply, Fintype.expect_eq_sum_div_card, Finset.sum_div]
  refine Finset.sum_congr rfl fun cb _ => ?_
  rw [PMF.toReal_uniformOfFintype_apply]
  simp only [Option.map_eq_none_iff, Option.isNone_iff_eq_none]
  split_ifs <;> simp [div_eq_inv_mul]

/-- **The birthday bound for `k` uniform nonces**: `k` uniform values of `Bytes 32` collide with
probability at most `C(k, 2) / 2^256` (`prob_not_injective_le`). -/
theorem expect_not_injective_bytes32_le (k : ℕ) :
    𝔼 rv : Fin k → Bytes 32, (if Function.Injective rv then (0 : ℝ) else 1) ≤
      (k.choose 2 : ℝ) / 2 ^ 256 := by
  have hcard : (Fintype.card (Bytes 32) : ℝ) = 2 ^ 256 := by
    rw [Fintype.card_congr (Vector.equivFun UInt8 32), Fintype.card_fun, Fintype.card_fin,
      Fintype.card_congr UInt8.equivFin, Fintype.card_fin]
    norm_num
  rw [PMF.expect_eq_sum_uniformOfFintype, ← PMF.pi_uniformOfFintype, div_eq_mul_inv]
  refine PMF.prob_not_injective_le (uniformOfFintype (Bytes 32)) fun x => ?_
  rw [PMF.toReal_uniformOfFintype_apply, hcard]

section Loop

variable (prims : Primitives p) [NeZero (bucketCount p)] [nttOps : NTTRingOps]
  [Fintype prims.Power2High] [DecidableEq prims.Power2High] [Fintype prims.Hint]
  [DecidableEq prims.Hint] [Inhabited prims.Hint] [Nonempty (MaskBox p)] [Fintype Msg]
  [DecidableEq Msg] [Fintype Y] [DecidableEq Y] [Nonempty Y]
  (O : W1Oracles X Y p prims Msg N reps) (M : MaskOracle X Y p T Msg) (βmin : ℚ≥0) (tol : ℕ)
  (enc : Vector prims.High p.k → BucketVec p) (k D : ℕ) [NeZero D] {RMsg : Type} [Fintype RMsg]
  [DecidableEq RMsg] (bmsg : KeyRing (PubKey p prims) N → RMsg → Msg)
  {TPS : PSTypes} [Fintype TPS.Proof] [DecidableEq TPS.Proof] [Fintype TPS.Coins] [DecidableEq TPS.Coins] [Nonempty TPS.Coins] (PS : ProofSystem X Y (RingSignature.RingStmt (hedgedBase prims O M βmin tol enc k D bmsg)) (RingSignature.RingWitOf (FIPSSignature p prims)) TPS)
  (adm : KeyRing (PubKey p prims) N → Prop) [DecidablePred adm]
  (n : ℕ) (hp : SigningParams p) (hβ0 : (βmin : ℝ≥0∞) ≠ 0) (hβt : (βmin : ℝ≥0∞) ≠ ⊤)

local notation "Bh" => hedgedBase prims O M βmin tol enc k D bmsg
local notation "Bf" => freshBase prims O M βmin tol enc k D bmsg
local notation "Sh" => hedgedScheme prims O M βmin tol enc k D bmsg PS adm

omit [Fintype TPS.Proof] [DecidableEq TPS.Proof] [Fintype TPS.Coins] [DecidableEq TPS.Coins]
  [Nonempty TPS.Coins] in
/-- **The fresh-mask signer refuses an admitted ring rarely**: at an oracle `H` at which the ring
of the valid challenge `c` passes the check and has distinct message representatives, the signer
of user `0` refuses with probability at most `2 · lowError + k / D + (1 - Lk)^k`, plus `1` when the
ring's defect exceeds `s`. -/
theorem refusalPubLaw_freshBase_none_le (hT : 0 < T)
    (hMask : (uniformOfFintype Y).map M.ans = uniformOfFintype (MaskBox p))
    (h_laws : SigningLaws prims) (hv : VerifyLaws prims)
    (henc : ∀ w : RqVec p.k, enc (prims.highBitsVec w) = bucketsOf (rqVecCoeffs w))
    (hs2 : ∀ seed, polyVecBounded (keyGen prims seed).2.s2 p.eta) {s θ Lk : ℝ} (hθ0 : 0 < θ)
    (hθ1 : θ < 1) (hs1 : s < 1) (hLk : Lk ≤ keepLevel p βmin s θ) (hLk1 : Lk ≤ 1) (H : X → Y)
    (keys : Fin n → Bytes 32) (c : AnonRequest (Sh) n) (hc : c.Valid keys)
    (hok : RingCheck prims βmin tol (O.gOrc H) c.ring ∧
      MuDistinct prims (O.muOrc H) c.ring (bmsg c.ring c.msg)) :
    ((Bf).refusalPubLaw H (keys c.user₀) c.ring c.msg none).toReal ≤
      2 * lowError prims O M βmin tol enc k D bmsg PS adm n hp hβ0 hβt keys (O.muOrc H) s θ
          (O.chOrc H) +
        k * (D : ℝ)⁻¹ + (1 - Lk) ^ k +
        (if s < ringDefect prims βmin c.ring.1 then 1 else 0) := by
  have hF0 := lowError_nonneg (O := O) (M := M) (βmin := βmin) (tol := tol) (enc := enc) (k := k)
    (D := D) (bmsg := bmsg) (PS := PS) (adm := adm) hp hβ0 hβt hs1 hθ0 keys (O.muOrc H) (O.chOrc H)
  have hL1 : ((Bf).refusalPubLaw H (keys c.user₀) c.ring c.msg none).toReal ≤ 1 :=
    ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using PMF.coe_le_one _ _)
  have h2 : 0 ≤ (1 - Lk) ^ k := pow_nonneg (sub_nonneg.2 hLk1) _
  have h3 : (0 : ℝ) ≤ k * (D : ℝ)⁻¹ := by positivity
  by_cases hd : s < ringDefect prims βmin c.ring.1
  · simp only [hd, ↓reduceIte]
    linarith
  simp only [hd, ↓reduceIte, add_zero]
  have hd' : LowDefect prims βmin s c.ring := not_lt.1 hd
  let m : LowChal prims O M βmin tol enc k D bmsg PS adm n keys (O.muOrc H) s := ⟨c, hc, hok.2, hd'⟩
  have hne : Nonempty (LowChal prims O M βmin tol enc k D bmsg PS adm n keys (O.muOrc H) s) := ⟨m⟩
  set F := lowError prims O M βmin tol enc k D bmsg PS adm n hp hβ0 hβt keys (O.muOrc H) s θ
    (O.chOrc H)
  have hF : F = familyBound (lowFamily prims O M βmin tol enc k D bmsg PS adm n hp hβ0 hβt keys
      (O.muOrc H) s) θ (O.chOrc H) := dite_eq_left hne
  set P := chalPair prims O M βmin tol enc k D bmsg PS adm n hp hβ0 hβt keys (O.muOrc H) c hc hok.2
  by_cases hF2 : F < 1 / 2
  · have hk := keep_ge_of_familyBound_lt (lowFamily prims O M βmin tol enc k D bmsg PS adm n hp
      hβ0 hβt keys (O.muOrc H) s) hθ0 hθ1 (lowFamily_mass_pos hp hβ0 hβt hs1 keys (O.muOrc H))
      (hF ▸ hF2) m false
    have hmass : (1 - s) * Fintype.card (BucketVec p) ≤ P.wts.mass := by
      calc (1 - s) * Fintype.card (BucketVec p) = ∑ _v : BucketVec p, (1 - s) := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm]
        _ ≤ _ := Finset.sum_le_sum fun v _ =>
            one_sub_le_colMass_of_ringDefect_le prims hp hβ0 hβt hd' v
    have hlev : Lk ≤ (1 - P.attempt false (O.chOrc H) none).toReal := by
      refine hLk.trans (le_trans ?_ hk)
      unfold keepLevel
      change (standinScale p * βmin).toReal * (θ * ((1 - s) * Fintype.card (BucketVec p))) / 2 ≤
        (standinScale p * βmin).toReal * (θ * P.wts.mass) / 2
      have hβ := flatLevel_pos (cut := Cutoff.const βmin) hp hβ0 hβt
      gcongr
    have ha1 : P.attempt false (O.chOrc H) none ≤ 1 := PMF.coe_le_one _ _
    rw [ENNReal.toReal_sub_of_le ha1 ENNReal.one_ne_top, ENNReal.toReal_one] at hlev
    have hpow : ((P.attempt false (O.chOrc H) none) ^ k).toReal ≤ (1 - Lk) ^ k := by
      rw [ENNReal.toReal_pow]
      exact pow_le_pow_left₀ ENNReal.toReal_nonneg (by linarith) k
    by_cases h1 : P.attempt false (O.chOrc H) none = 1
    · have : (1 : ℝ) ≤ (1 - Lk) ^ k := by simpa [h1] using hpow
      linarith
    have htv := tvDist_refusalPubLaw_freshBase_le prims O M βmin tol enc k D bmsg hT hMask h_laws
      hv henc (hs2 _) H c.ring c.msg
      (idxOf_lt_of_valid prims O M βmin tol enc k D bmsg PS adm n hc false) hok
    have hpt := PMF.toReal_apply_le_add_tvDist ((Bf).refusalPubLaw H (keys c.user₀) c.ring c.msg)
      (untilSome (P.attempt false (O.chOrc H))) none
    erw [untilSome_apply_none h1, ENNReal.toReal_zero, zero_add] at hpt
    have hpt' : ((Bf).refusalPubLaw H (keys c.user₀) c.ring c.msg none).toReal ≤
        k * (D : ℝ)⁻¹ + ((P.attempt false (O.chOrc H) none) ^ k).toReal := hpt.trans htv
    linarith
  · push Not at hF2
    linarith

omit [Inhabited prims.Hint] in
/-- **Hedged refusal is fresh refusal up to nonce collisions**: for a weight `Φ` with values in
`[0, 1]` reading the oracle only at the base signer's points, the `Φ`-weighted average over a
uniform oracle of the hedged signer's refusal probability is at most that of the fresh signer plus
`C(k, 2) / 2^256`. -/
theorem expect_mul_refusalPubLaw_hedged_le [Fintype X] [DecidableEq X]
    (hM : Function.Injective M.pt) (hdisj : ∀ x, O.IsPt x → x ∉ Set.range M.pt)
    (kc : Bytes 32) (R : KeyRing (PubKey p prims) N) (m : RMsg) (Φ : (X → Y) → ℝ)
    (hΦ0 : ∀ H, 0 ≤ Φ H) (hΦ1 : ∀ H, Φ H ≤ 1)
    (hΦ : ∀ H H', (O.split H).1 = (O.split H').1 → Φ H = Φ H') :
    𝔼 H : X → Y, Φ H * ((Bh).refusalPubLaw H kc R m none).toReal ≤
      𝔼 H : X → Y, Φ H * ((Bf).refusalPubLaw H kc R m none).toReal +
        (k.choose 2 : ℝ) / 2 ^ 256 := by
  set fn : (X → Y) → (Fin k → MaskPt T Msg → Y) → (Fin k → Fin D) → ℝ := fun H g uv =>
    if (((Bf).bsign ((Bf).sk kc) R (R.1.idxOf ((Bf).pk kc)) m (g, uv)).run H).isNone then 1 else 0
    with hfn
  have fn0 : ∀ H g uv, 0 ≤ fn H g uv := fun H g uv => by
    simp only [hfn]; split_ifs <;> norm_num
  have fn1 : ∀ H g uv, fn H g uv ≤ 1 := fun H g uv => by
    simp only [hfn]; split_ifs <;> norm_num
  have hf : ∀ H, ((Bf).refusalPubLaw H kc R m none).toReal = 𝔼 g, 𝔼 uv, fn H g uv := fun H => by
    refine (BaseSigner.toReal_refusalPubLaw_none (Bf) H kc R m).trans ?_
    -- The coins' own instance and the product instance are different terms.
    refine (Fintype.expect_equiv (Equiv.refl (Bf).Coins) _
      (fun cb : (Fin k → MaskPt T Msg → Y) × (Fin k → Fin D) => fn H cb.1 cb.2)
      fun _ => rfl).trans ?_
    exact Finset.expect_product (s := Finset.univ) (t := Finset.univ) _
  have hh : ∀ H, ((Bh).refusalPubLaw H kc R m none).toReal =
      𝔼 rv : Fin k → Bytes 32, 𝔼 uv, fn H (fun c u => H (M.pt (rv c, u))) uv := fun H => by
    refine (BaseSigner.toReal_refusalPubLaw_none (Bh) H kc R m).trans ?_
    refine (Finset.expect_product (s := Finset.univ) (t := Finset.univ) _).trans ?_
    refine Finset.expect_congr rfl fun rv _ => Finset.expect_congr rfl fun uv _ => ?_
    have hb : ((Bh).bsign ((Bf).sk kc) R (R.1.idxOf ((Bf).pk kc)) m (rv, uv)).run H =
        ((Bf).bsign ((Bf).sk kc) R (R.1.idxOf ((Bf).pk kc)) m
          ((fun c u => H (M.pt (rv c, u))), uv)).run H :=
      (run_bsign_w1BaseSigner prims O βmin tol enc (MaskSource.hedged M) k D bmsg ((Bf).sk kc) R
        (R.1.idxOf ((Bf).pk kc)) m (rv, uv) H).trans
        (run_bsign_w1BaseSigner prims O βmin tol enc (MaskSource.fresh M) k D bmsg ((Bf).sk kc) R
          (R.1.idxOf ((Bf).pk kc)) m ((fun c u => H (M.pt (rv c, u))), uv) H).symm
    change (if (((Bh).bsign ((Bf).sk kc) R (R.1.idxOf ((Bf).pk kc)) m (rv, uv)).run H).isNone
      then (1 : ℝ) else 0) = _
    rw [hb]
  -- The term of the nonces `rv`, with the oracle and the keep coins averaged inside.
  have hterm : ∀ rv : Fin k → Bytes 32,
      𝔼 uv, 𝔼 H, Φ H * fn H (fun c u => H (M.pt (rv c, u))) uv ≤
        𝔼 uv, 𝔼 H, 𝔼 g, Φ H * fn H g uv + if Function.Injective rv then 0 else 1 := fun rv => by
    by_cases hinj : Function.Injective rv
    · simp only [hinj, ↓reduceIte, add_zero]
      refine le_of_eq (Finset.expect_congr rfl fun uv _ => ?_)
      let e : Fin k × MaskPt T Msg ↪ X := ⟨fun a => M.pt (rv a.1, a.2), fun a b h => by
        have h' : (rv a.1, a.2) = (rv b.1, b.2) := hM h
        obtain ⟨h1, h2⟩ := Prod.mk.inj h'
        exact Prod.ext_iff.2 ⟨hinj h1, h2⟩⟩
      have hS : ∀ x, O.IsPt x → x ∉ Set.range e := fun x hx ⟨a, ha⟩ =>
        hdisj x hx ⟨_, ha⟩
      have key := GordieHowe.expect_comp_embedding_eq e O.IsPt hS
        (fun H g' => Φ H * fn H (fun c u => g' (c, u)) uv) fun H H' g' h => by
          have hsp : (O.split H).1 = (O.split H').1 := funext fun x => h x.1 x.2
          simp only [hfn]
          rw [hΦ H H' hsp]
          congr 1
          exact congrArg (fun o => if Option.isNone o then (1 : ℝ) else 0)
            ((readsOnly_freshBase prims O M βmin tol enc k D bmsg).run_bsign H H' hsp _ _ _ _ _)
      refine key.trans (Finset.expect_congr rfl fun H _ => ?_)
      exact Fintype.expect_equiv (Equiv.curry _ _ _)
        (fun g' => Φ H * fn H (fun c u => g' (c, u)) uv) (fun g => Φ H * fn H g uv) fun g' => rfl
    · simp only [hinj, ↓reduceIte]
      have h1 : 𝔼 uv, 𝔼 H, Φ H * fn H (fun c u => H (M.pt (rv c, u))) uv ≤ 1 := by
        refine (Finset.expect_le_expect fun uv _ => (Finset.expect_le_expect fun H _ =>
          ?_).trans_eq (Finset.expect_const Finset.univ_nonempty 1)).trans_eq
            (Finset.expect_const Finset.univ_nonempty 1)
        exact (mul_le_mul_of_nonneg_right (hΦ1 H) (fn0 _ _ _)).trans
          ((one_mul _).trans_le (fn1 _ _ _))
      have h0 : 0 ≤ 𝔼 uv, 𝔼 H, 𝔼 g, Φ H * fn H g uv :=
        Finset.expect_nonneg fun uv _ => Finset.expect_nonneg fun H _ =>
          Finset.expect_nonneg fun g _ => mul_nonneg (hΦ0 H) (fn0 _ _ _)
      linarith
  have hL : 𝔼 H : X → Y, Φ H * ((Bh).refusalPubLaw H kc R m none).toReal =
      𝔼 rv : Fin k → Bytes 32, 𝔼 uv, 𝔼 H, Φ H * fn H (fun c u => H (M.pt (rv c, u))) uv := by
    simp only [hh, Finset.mul_expect]
    rw [Finset.expect_comm]
    exact Finset.expect_congr rfl fun rv _ => Finset.expect_comm _ _ _
  have hR : 𝔼 H : X → Y, Φ H * ((Bf).refusalPubLaw H kc R m none).toReal =
      𝔼 uv, 𝔼 H, 𝔼 g, Φ H * fn H g uv := by
    simp only [hf, Finset.mul_expect]
    exact (Finset.expect_congr rfl fun H _ => Finset.expect_comm _ _ _).trans
      (Finset.expect_comm _ _ _)
  rw [hL, hR]
  calc _ ≤ 𝔼 rv : Fin k → Bytes 32, (𝔼 uv, 𝔼 H, 𝔼 g, Φ H * fn H g uv +
        if Function.Injective rv then 0 else 1) := Finset.expect_le_expect fun rv _ => hterm rv
    _ = _ + 𝔼 rv : Fin k → Bytes 32, (if Function.Injective rv then (0 : ℝ) else 1) := by
        rw [Finset.expect_add_distrib, Finset.expect_const Finset.univ_nonempty]
    _ ≤ _ := add_le_add le_rfl (expect_not_injective_bytes32_le k)

end Loop

end GordieHowe.Ring.MLDSAW1
