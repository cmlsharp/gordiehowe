-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Foundations.Probability.Advantage
public import GordieHowe.Foundations.ToMathlib.PMFTV
public import GordieHowe.Foundations.ToMathlib.UniformFunction

@[expose] public section

/-!
# Unopened leaves are close to uniform given the whole random function

A Merkle leaf of the compiled proof is the digest `H (e ν)` of a Merkle salt `ν` under an injective
encoding `e : N → X` into the oracle's domain. After the last proof the distinguisher receives
the whole random function `H : X → Y`. This file shows that the digests of the unopened leaves
are still statistically close to independent uniform digests, jointly with `H`:

- `expect_collision_digestLaw`: for one leaf, the expected collision probability of `H (e ν)` over uniform `H`
  is exactly `1 / |N| + (1 - 1 / |N|) / |Y|`;
- `leaf_hiding_one`: for one leaf, the expected distance of the digest law from uniform is at
  most `√(|Y| / |N|) / 2` (collision bound, then Jensen for the square root);
- `leaf_hiding`: for `U` leaves with independent Merkle salts, the law of `(H, digests)` is within
  `U · √(|Y| / |N|) / 2` of the law of `(H, u)` with `u` uniform and independent of `H`;
- `leaf_hiding_bytes`: with `|Y| = 2^(8k)` and Merkle salts twice the digest length,
  `|N| = 2^(16k)`, the distance is at most `U · 2^(-4k) / 2`.
- `leaf_equivocation`: the joint law of `H` and the (Merkle salt, digest) pairs is within the same
  bound of the law with digests uniform and independent of `H` and each Merkle salt drawn from the
  preimage of its digest (`invert`, CY24's `RO.Invert`); `leaf_equivocation_bytes` is its
  bytes form. Nodes, roots and challenges are then honest functions of the digests and `H`,
  so the proof depends on the witness only through the opened columns.

This parallels BCS16 FACT 1 (Ben-Sasson, Chiesa, Spooner, "Interactive Oracle Proofs", ePrint
2016/116, p. 16) and CY24 Lemma 17.3.1 (Chiesa, Yogev, "Building Cryptographic Proofs from Hash
Functions") at query bound `t = ∞`, which it replaces in the zero-knowledge argument. The argument
is classical and the distinguisher is given the whole function `H`, so it covers every
distinguisher, quantum ones included. It goes by collision probability (leftover hash style), not by
a Chernoff bound.
-/

open Finset PMF
open scoped BigOperators

namespace GordieHowe.SPBCS

variable {X Y N : Type*}

/-! ### One leaf -/

section OneLeaf

variable [Fintype N] [Nonempty N]

/-- The law of one leaf digest `H (e ν)` for a fixed function `H` and a uniform Merkle salt `ν`. -/
noncomputable def digestLaw (H : X → Y) (e : N → X) : PMF Y :=
  (uniformOfFintype N).map (H ∘ e)

theorem toReal_digestLaw_apply [DecidableEq Y] (H : X → Y) (e : N → X) (y : Y) :
    (digestLaw H e y).toReal =
      (Fintype.card N : ℝ)⁻¹ * ∑ ν, if H (e ν) = y then (1 : ℝ) else 0 := by
  rw [digestLaw, toReal_map_apply, mul_sum]
  exact sum_congr rfl fun ν _ => by simp

variable [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [Nonempty Y]

/-- **Collision probability of one leaf.** For an injective encoding `e`, the collision
probability of `H (e ν)`, averaged over a uniform function `H`, is
`1 / |N| + (1 - 1 / |N|) / |Y|`. -/
theorem expect_collision_digestLaw {e : N → X} (he : Function.Injective e) :
    𝔼[H ← (X → Y) : ∑ y, (digestLaw H e y).toReal ^ 2] =
      1 / Fintype.card N + (1 - 1 / Fintype.card N) / Fintype.card Y := by
  classical
  set n : ℝ := (Fintype.card N : ℝ) with hn
  set c : ℝ := (Fintype.card Y : ℝ)⁻¹ with hc
  have hn0 : n ≠ 0 := by simp [hn]
  -- the collision probability given `H` counts colliding pairs of Merkle salts
  have hpair : ∀ H : X → Y, ∑ y, (digestLaw H e y).toReal ^ 2 =
      n⁻¹ ^ 2 * ∑ ν, ∑ ν', if H (e ν) = H (e ν') then (1 : ℝ) else 0 := fun H => by
    simp_rw [toReal_digestLaw_apply, mul_pow, ← mul_sum]
    congr 1
    simp_rw [sq, sum_mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun ν _ => ?_
    rw [sum_comm]
    refine sum_congr rfl fun ν' _ => ?_
    rw [Fintype.sum_eq_single (H (e ν)) fun y hy => by simp [Ne.symm hy]]
    simp [eq_comm]
  -- averaged over `H`, a pair of Merkle salts collides with probability `1` or `1 / |Y|`
  have hexp : ∀ ν ν' : N, 𝔼 H : X → Y, (if H (e ν) = H (e ν') then (1 : ℝ) else 0) =
      c + (1 - c) * (if ν = ν' then 1 else 0) := fun ν ν' => by
    by_cases h : ν = ν'
    · simp [h]
    · simp [h, expect_apply_eq_apply (he.ne h), hc]
  simp_rw [hpair, ← mul_expect, expect_sum_comm, hexp]
  simp only [sum_add_distrib, sum_const, card_univ, nsmul_eq_mul, ← mul_sum, sum_ite_eq,
    mem_univ, ite_true]
  rw [← hn, hc]
  field_simp
  ring

/-- **One leaf is close to uniform.** For an injective encoding `e`, the digest law of a
uniform Merkle salt is, on average over a uniform function `H`, within `√(|Y| / |N|) / 2` of
uniform. -/
theorem leaf_hiding_one {e : N → X} (he : Function.Injective e) :
    𝔼[H ← (X → Y) : tvDist (digestLaw H e) (uniformOfFintype Y)] ≤
      √(Fintype.card Y / Fintype.card N) / 2 := by
  set z : (X → Y) → ℝ := fun H => Fintype.card Y * ∑ y, (digestLaw H e y).toReal ^ 2 - 1
  have hz : ∀ H, 0 ≤ z H := fun H => sub_nonneg.2 (one_le_card_mul_sum_sq _)
  have hEz : 𝔼 H, z H ≤ Fintype.card Y / Fintype.card N := by
    simp only [z, expect_sub_distrib, ← mul_expect, expect_collision_digestLaw he, Fintype.expect_const]
    have hY : (0 : ℝ) < Fintype.card Y := by exact_mod_cast Fintype.card_pos
    have hN : (0 : ℝ) < Fintype.card N := by exact_mod_cast Fintype.card_pos
    have e : ∀ a b : ℝ, 0 < a → 0 < b → b / a - (b * (1 / a + (1 - 1 / a) / b) - 1) = 1 / a :=
      fun a b ha hb => by
        field_simp
        ring
    rw [← sub_nonneg, e _ _ hN hY]
    positivity
  calc 𝔼 H : X → Y, tvDist (digestLaw H e) (uniformOfFintype Y)
      ≤ 𝔼 H, √(z H) / 2 := expect_le_expect fun H _ => tvDist_uniformOfFintype_le _
    _ = (𝔼 H, √(z H)) / 2 := by rw [expect_div]
    _ ≤ √(𝔼 H, z H) / 2 := by gcongr; exact Real.expect_sqrt_le_sqrt_expect z hz
    _ ≤ √(Fintype.card Y / Fintype.card N) / 2 := by gcongr

end OneLeaf

/-! ### Leaf equivocation: Merkle salts sampled from the preimage of uniform digests -/

section Invert

variable [Fintype N] [Nonempty N] [DecidableEq Y]

/-- **The inversion sampler** (CY24 `RO.Invert`, defined in the proof of Lemma 3.4.3, p. 38):
a Merkle salt `ν` drawn uniformly from the preimage `{ν | H (e ν) = d}` of the digest `d`, and
uniformly from `N` when that preimage is empty (CY24: "an arbitrary string").

It enumerates the preimage, so it is not efficient. It is used only in statistical arguments
against a distinguisher that receives the whole function `H`, never as a simulator. -/
noncomputable def invert (H : X → Y) (e : N → X) (d : Y) : PMF N :=
  if h : (univ.filter fun ν => H (e ν) = d).Nonempty then uniformOfFinset _ h
  else uniformOfFintype N

omit [DecidableEq Y] in
/-- The digest law at `d` is the fraction of Merkle salts whose digest is `d`. -/
theorem digestLaw_apply [DecidableEq Y] (H : X → Y) (e : N → X) (d : Y) :
    digestLaw H e d = (univ.filter fun ν => H (e ν) = d).card * (Fintype.card N : ENNReal)⁻¹ := by
  rw [digestLaw, map_apply, tsum_fintype]
  simp [uniformOfFintype_apply, Finset.sum_ite, eq_comm]

/-- Given `H`, the inversion sampler is the conditional law of a uniform Merkle salt `ν` given its
digest `H (e ν)`. -/
theorem isDisintegration_invert (H : X → Y) (e : N → X) :
    (uniformOfFintype N).IsDisintegration (H ∘ e) (invert H e) := by
  intro d ν
  have hmap := digestLaw_apply H e d
  rw [digestLaw] at hmap
  rw [hmap, invert, uniformOfFintype_apply]
  set s := univ.filter fun ν => H (e ν) = d
  by_cases hν : H (e ν) = d
  · have hs : ν ∈ s := by simp [s, hν]
    have hc : (s.card : ENNReal) ≠ 0 := by simpa using Finset.ne_empty_of_mem hs
    have hne : s.Nonempty := ⟨ν, hs⟩
    rw [dite_eq_left hne, uniformOfFinset_apply_of_mem (ha := hs),
      ite_eq_left (c := (H ∘ e) ν = d) hν]
    rw [mul_comm, ← mul_assoc, ENNReal.inv_mul_cancel hc (ENNReal.natCast_ne_top _), one_mul]
  · rw [ite_eq_right (c := (H ∘ e) ν = d) hν]
    by_cases hs : s.Nonempty
    · rw [dite_eq_left hs, uniformOfFinset_apply_of_notMem (ha := by simpa [s] using hν),
        mul_zero]
    · rw [Finset.not_nonempty_iff_eq_empty.1 hs]
      simp

end Invert

/-! ### All unopened leaves jointly -/

variable [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [Nonempty Y]
  [Fintype N] [Nonempty N] {U : ℕ}

/-- The real joint law of the function and the unopened leaf digests: `H` uniform in `X → Y`,
Merkle salts `ν i` independent and uniform in `N`, output `(H, fun i => H (e i (ν i)))`. -/
noncomputable def leafLaw (e : Fin U → N → X) : PMF ((X → Y) × (Fin U → Y)) :=
  (uniformOfFintype (X → Y)).bind fun H =>
    (uniformOfFintype (Fin U → N)).map fun ν => (H, fun i => H (e i (ν i)))

/-- The ideal joint law: `H` uniform in `X → Y` and `u` uniform in `Fin U → Y`, independent of
`H`; output `(H, u)`. -/
noncomputable def leafHidingIdealLaw (X Y : Type*) [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y]
    (U : ℕ) : PMF ((X → Y) × (Fin U → Y)) :=
  (uniformOfFintype (X → Y)).bind fun H => (uniformOfFintype (Fin U → Y)).map (Prod.mk H)

omit [Fintype X] [DecidableEq X] [DecidableEq Y] [Nonempty Y] in
/-- Given `H`, the leaf digests are independent, each with law `digestLaw H (e i)`. -/
theorem uniformOfFintype_map_leaves (H : X → Y) (e : Fin U → N → X) :
    (uniformOfFintype (Fin U → N)).map (fun ν i => H (e i (ν i))) =
      PMF.pi fun i => digestLaw H (e i) := by
  rw [← pi_uniformOfFintype]
  exact pi_map _ fun i => H ∘ e i

/-- Given `H`, the distance of the joint leaf-digest law from uniform, averaged over a uniform
`H`, is at most `U · √(|Y| / |N|) / 2`: the hybrid over the leaves, then `leaf_hiding_one`. -/
theorem expect_tvDist_leaves_le {e : Fin U → N → X} (he : ∀ i, Function.Injective (e i)) :
    𝔼[H ← (X → Y) : tvDist ((uniformOfFintype (Fin U → N)).map fun ν i => H (e i (ν i)))
      (uniformOfFintype (Fin U → Y))] ≤ U * √(Fintype.card Y / Fintype.card N) / 2 := by
  calc 𝔼 H : X → Y, tvDist ((uniformOfFintype (Fin U → N)).map fun ν i => H (e i (ν i)))
        (uniformOfFintype (Fin U → Y))
      ≤ 𝔼 H : X → Y, ∑ i, tvDist (digestLaw H (e i)) (uniformOfFintype Y) := by
        refine expect_le_expect fun H _ => ?_
        rw [uniformOfFintype_map_leaves, ← pi_uniformOfFintype]
        exact tvDist_pi_le _ _
    _ = ∑ i, 𝔼 H : X → Y, tvDist (digestLaw H (e i)) (uniformOfFintype Y) := expect_sum_comm ..
    _ ≤ ∑ _i : Fin U, √(Fintype.card Y / Fintype.card N) / 2 :=
        sum_le_sum fun i _ => leaf_hiding_one (he i)
    _ = U * √(Fintype.card Y / Fintype.card N) / 2 := by simp [mul_div_assoc]

/-- **Unopened leaves are close to uniform given the whole function.** For `U` leaves with
injective encodings `e i` (their images may overlap) and independent uniform Merkle salts, the joint
law of `(H, fun i => H (e i (ν i)))` is within `U · √(|Y| / |N|) / 2` in total variation of
`(H, u)` with `u` uniform and independent of `H`. -/
theorem leaf_hiding {e : Fin U → N → X} (he : ∀ i, Function.Injective (e i)) :
    leafLaw e ≈[U * √(Fintype.card Y / Fintype.card N) / 2] leafHidingIdealLaw X Y U := by
  refine (tvDist_uniformOfFintype_bind_le _ _).trans
    ((expect_le_expect fun H _ => ?_).trans (expect_tvDist_leaves_le he))
  have hmap : (uniformOfFintype (Fin U → N)).map (fun ν => (H, fun i => H (e i (ν i)))) =
      ((uniformOfFintype (Fin U → N)).map fun ν i => H (e i (ν i))).map (Prod.mk H) := by
    rw [map_comp]
    rfl
  rw [hmap]
  exact tvDist_map_le _ _ _

omit [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [Nonempty Y] [Fintype N]
  [Nonempty N] in
/-- With `k`-byte digests (`|Y| = 2^(8k)`) and `2k`-byte Merkle salts (`|N| = 2^(16k)`),
`√(|Y| / |N|) = 2^(-4k)`. -/
theorem sqrt_card_div_card_of_bytes [Fintype Y] [Fintype N] {k : ℕ}
    (hY : Fintype.card Y = 2 ^ (8 * k)) (hN : Fintype.card N = 2 ^ (16 * k)) :
    √((Fintype.card Y : ℝ) / Fintype.card N) = ((2 : ℝ) ^ (4 * k))⁻¹ := by
  have h : (Fintype.card Y : ℝ) / Fintype.card N = (((2 : ℝ) ^ (4 * k))⁻¹) ^ 2 := by
    rw [hY, hN]
    push_cast
    rw [inv_pow, ← pow_mul, show 16 * k = 8 * k + 4 * k * 2 by ring, pow_add]
    field_simp
  rw [h, Real.sqrt_sq (by positivity)]

/-- **Merkle salts twice the digest length.** With `k`-byte digests (`|Y| = 2^(8k)`) and `2k`-byte
Merkle salts (`|N| = 2^(16k)`), the unopened leaves of one proof are within `U · 2^(-4k) / 2` of
uniform given the whole function: `U · 2^(-(s - σ) / 2) / 2` with Merkle salt length `s = 2σ` bits.

Hypotheses `hY` and `hN` fix the digest and salt lengths. -/
theorem leaf_hiding_bytes {k : ℕ} (hY : Fintype.card Y = 2 ^ (8 * k))
    (hN : Fintype.card N = 2 ^ (16 * k)) {e : Fin U → N → X}
    (he : ∀ i, Function.Injective (e i)) :
    leafLaw e ≈[U * ((2 : ℝ) ^ (4 * k))⁻¹ / 2] leafHidingIdealLaw X Y U := by
  rw [← sqrt_card_div_card_of_bytes hY hN]
  exact leaf_hiding he


variable (Y) in
/-- The real joint law of the function and the leaf (Merkle salt, digest) pairs: `H` uniform in
`X → Y`, Merkle salts `ν i` independent and uniform in `N`, output
`(H, fun i => (ν i, H (e i (ν i))))`. -/
noncomputable def leafPairLaw (e : Fin U → N → X) : PMF ((X → Y) × (Fin U → N × Y)) :=
  (uniformOfFintype (X → Y)).bind fun H =>
    (uniformOfFintype (Fin U → N)).map fun ν => (H, fun i => (ν i, H (e i (ν i))))

variable (Y) in
/-- The ideal joint law of the function and the leaf pairs: `H` uniform in `X → Y`, digests
`d i` independent and uniform in `Y`, then Merkle salts `ν i ← invert H (e i) (d i)` independently;
output `(H, fun i => (ν i, d i))`. -/
noncomputable def idealPairLaw (e : Fin U → N → X) : PMF ((X → Y) × (Fin U → N × Y)) :=
  (uniformOfFintype (X → Y)).bind fun H =>
    (uniformOfFintype (Fin U → Y)).bind fun d =>
      (PMF.pi fun i => invert H (e i) (d i)).map fun ν => (H, fun i => (ν i, d i))

/-- **Leaf equivocation against the whole function.** For `U` leaves with injective encodings
`e i` and independent uniform Merkle salts, the joint law of `H` and the (Merkle salt, digest) pairs
`(ν i, H (e i (ν i)))` is within `U · √(|Y| / |N|) / 2` in total variation of the law in which
the digests `d i` are uniform and independent of `H` and each Merkle salt is drawn from the preimage
of its digest by `invert`.

Why this suffices for everlasting zero knowledge. In the ideal law the nodes, roots, Merkle keys and
Fiat–Shamir challenges are computed honestly from the digests with the oracle `H`; an unopened
column appears nowhere, and an opened leaf reveals a Merkle salt drawn from the preimage of its digest
given that column. So the proof depends on the witness only through the opened columns. The set
of opened leaves is chosen adaptively (it depends on the roots), which is covered because the
whole vector of pairs is jointly close and any adaptive reveal is a function of `H` and that
vector. CY24's simulated roots and openings (Lemma 18.7.1, p. 217, `MT.SimulateRoot` and
`MT.SimulateOpening`) are not needed for this, and there is no internal-node term: no
`2ℓ · 2^(-σ/2)` summand appears.

The proof: given `H`, `invert` is the conditional law of a Merkle salt given its digest
(`isDisintegration_invert`), so both laws apply the same kernel to the digests and the distance
is at most that of the digest laws, which is `leaf_hiding`'s bound. This is the joint form,
at query bound `t = ∞`, of CY24 Lemma 3.4.3 (regularity, p. 37), and parallels BCS16 FACT 1
(Ben-Sasson, Chiesa, Spooner, ePrint 2016/116, p. 16). The distinguisher receives the whole
function `H`, so the bound covers every distinguisher, quantum ones included. -/
theorem leaf_equivocation {e : Fin U → N → X} (he : ∀ i, Function.Injective (e i)) :
    leafPairLaw Y e ≈[U * √(Fintype.card Y / Fintype.card N) / 2] idealPairLaw Y e := by
  refine (tvDist_uniformOfFintype_bind_le _ _).trans
    ((expect_le_expect fun H _ => ?_).trans (expect_tvDist_leaves_le he))
  let g : (Fin U → N) × (Fin U → Y) → (X → Y) × (Fin U → N × Y) :=
    fun x => (H, fun i => (x.1 i, x.2 i))
  have hreal : (uniformOfFintype (Fin U → N)).map (fun ν => (H, fun i => (ν i, H (e i (ν i))))) =
      ((uniformOfFintype (Fin U → N)).map fun ν => (ν, fun i => H (e i (ν i)))).map g := by
    rw [map_comp]
    rfl
  have hideal : ((uniformOfFintype (Fin U → Y)).bind fun d =>
        (PMF.pi fun i => invert H (e i) (d i)).map fun ν => (H, fun i => (ν i, d i))) =
      ((uniformOfFintype (Fin U → Y)).bind fun d =>
        (PMF.pi fun i => invert H (e i) (d i)).map fun ν => (ν, d)).map g := by
    simp_rw [map_bind, map_comp]
    rfl
  have hk : (uniformOfFintype (Fin U → N)).IsDisintegration (fun ν i => H (e i (ν i)))
      fun d => PMF.pi fun i => invert H (e i) (d i) := by
    rw [← pi_uniformOfFintype]
    exact IsDisintegration.pi fun i => isDisintegration_invert H (e i)
  rw [hreal, hideal]
  exact (tvDist_map_le _ _ _).trans (hk.tvDist_le _)

/-- **Leaf equivocation, Merkle salts twice the digest length.** With `k`-byte digests
(`|Y| = 2^(8k)`) and `2k`-byte Merkle salts (`|N| = 2^(16k)`), the leaf pairs of one proof are within
`U · 2^(-4k) / 2` of digests uniform given the whole function with Merkle salts drawn from their
preimages.

Hypotheses `hY` and `hN` fix the digest and salt lengths. -/
theorem leaf_equivocation_bytes {k : ℕ} (hY : Fintype.card Y = 2 ^ (8 * k))
    (hN : Fintype.card N = 2 ^ (16 * k)) {e : Fin U → N → X}
    (he : ∀ i, Function.Injective (e i)) :
    leafPairLaw Y e ≈[U * ((2 : ℝ) ^ (4 * k))⁻¹ / 2] idealPairLaw Y e := by
  rw [← sqrt_card_div_card_of_bytes hY hN]
  exact leaf_equivocation he

end GordieHowe.SPBCS
