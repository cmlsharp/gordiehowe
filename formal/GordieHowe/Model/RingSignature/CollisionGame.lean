-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.QROM.CollisionInteractive
public import GordieHowe.Model.RingSignature.RevealedReprogram

@[expose] public section

/-!
# Collisions at named points in a game's run

`AdaptiveIAlg.collision_le_add` (`GordieHowe/Model/QROM/CollisionInteractive.lean`) bounds the
probability that an interaction names two distinct points of a set `D` at which a decoding `f` of
the uniform oracle agrees. This file states it for a game's run (`RingSignature.runLawIn`): the
points are named by the adversary's output and its answered requests, and the run's events split
into the event without such a collision and the collision.

- `collides`: two distinct named points in `D` with equal decodings at the oracle.
- `toOuterMeasure_runLawIn_inter_length`: the run logs at most `Q` requests.
- `runLawIn_le_add_collision`: an event of the run is at most the event without a collision plus
  `12 b² (b − 1) / c + 2 ℓ / |BitStr I J|`, `b = t + Q q_C + ℓ`.
-/

open scoped ENNReal BigOperators

namespace GordieHowe.RingSignature

open Quantum GordieHowe.QROM GordieHowe.IOP

variable {m : ℕ} {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  {Req Resp O Z : Type} [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp]

/-- **A collision at the named points**: two distinct points of `D` among `pts` at which the
decoding `f` of the oracle `H` agrees. -/
def collides (f : BitStr I J → Z) (D : Set (Bits m)) (pts : List (Bits m))
    (H : Bits m → BitStr I J) : Prop :=
  ∃ x ∈ pts, ∃ x' ∈ pts, x ∈ D ∧ x' ∈ D ∧ x ≠ x' ∧ f (H x) = f (H x')

open Classical in
/-- **An event of a game's run without a collision at the named points**: for start draws `k`
and challengers `C k` answering `Q` requests with at most `q_C` queries each, and points named by
the output and the answered requests (at most `ℓ` of them), an event `E` of the run has at most
the probability of `E` without a collision of the decoding `f` at the oracle, plus
`12 b² (b − 1) / c + 2 ℓ / |BitStr I J|` with `b = t + Q q_C + ℓ`, when `f` of a uniform value
lies in every set `S` with probability at most `|S| / c` (`AdaptiveIAlg.collision_le_add`). -/
theorem runLawIn_le_add_collision {K : Type} [Fintype K] [Nonempty K] {t : ℕ} {c : ℝ≥0∞}
    (f : BitStr I J → Z)
    (hf : ∀ S : Finset Z, Pr[y ← BitStr I J : f y ∈ S] ≤ S.card / c)
    (A : K → QueryBoundedAdversary (Bits m) (BitStr I J) Req Resp O t)
    (C : K → Challenger (Bits m) (BitStr I J) Req Resp) {Q qC : ℕ} (hQ : ∀ k, (C k).Q = Q)
    (hq : ∀ k, (C k).q ≤ qC) (D : Set (Bits m)) (ℓ : ℕ)
    (pts : K → O × List Req → List (Bits m)) (hℓ : ∀ k o, (pts k o).length ≤ ℓ)
    (E : Set (K × (Bits m → BitStr I J) × Option (O × List Req × (Bits m → BitStr I J)))) :
    (runLawIn (fun k _ => A k) C).toOuterMeasure E ≤
      (runLawIn (fun k _ => A k) C).toOuterMeasure
          (E ∩ {x | ∀ q ∈ x.2.2, ¬ collides f D (pts x.1 (q.1, q.2.1)) x.2.1}) +
        (12 * ((t + Q * qC + ℓ : ℕ) : ℝ≥0∞) ^ 2 * ((t + Q * qC + ℓ - 1 : ℕ) : ℝ≥0∞) / c +
          2 * ℓ / Fintype.card (BitStr I J)) := by
  set γ := 12 * ((t + Q * qC + ℓ : ℕ) : ℝ≥0∞) ^ 2 * ((t + Q * qC + ℓ - 1 : ℕ) : ℝ≥0∞) / c +
    2 * ℓ / Fintype.card (BitStr I J)
  set Col := {x : K × (Bits m → BitStr I J) × Option (O × List Req × (Bits m → BitStr I J)) |
    ∃ q ∈ x.2.2, collides f D (pts x.1 (q.1, q.2.1)) x.2.1}
  have hsplit : E ⊆ (E ∩ {x | ∀ q ∈ x.2.2, ¬ collides f D (pts x.1 (q.1, q.2.1)) x.2.1}) ∪ Col :=
    fun x hx => by
      by_cases h : ∃ q ∈ x.2.2, collides f D (pts x.1 (q.1, q.2.1)) x.2.1
      · exact Or.inr h
      · exact Or.inl ⟨hx, fun q hq hc => h ⟨q, hq, hc⟩⟩
  refine (MeasureTheory.measure_mono hsplit).trans
    ((MeasureTheory.measure_union_le _ _).trans (add_le_add le_rfl ?_))
  -- the collision, at each start draw and auxiliary value, read from the output and the requests
  have hcol : ∀ k a, ∑ H, PMF.uniformOfFintype (Bits m → BitStr I J) H *
      ((((A k).alg a).toKindAlg.composeBothOut (C k) fun v =>
        (((A k).alg a).output (C k) v, (requests v.chal.logs).take (C k).Q)).outLaw
          H).toOuterMeasure {o | ∃ v ∈ o, collides f D (pts k v) H} ≤ γ := by
    intro k a
    have h := AdaptiveIAlg.collision_le_add (O' := O × List Req) (Equiv.refl (BitStr I J)) f hf
      ((A k).alg a) (C k) (fun v => (((A k).alg a).output (C k) v,
        (requests v.chal.logs).take (C k).Q)) D ℓ (pts k) (hℓ k)
    refine h.trans ?_
    have hb : ((A k).alg a).width * (((A k).alg a).budget + ((A k).alg a).post) + (C k).Q * (C k).q
        + ℓ ≤ t + Q * qC + ℓ := by
      have h1 := (A k).queries_le a
      have h2 : (C k).Q * (C k).q ≤ Q * qC := hQ k ▸ Nat.mul_le_mul_left _ (hq k)
      omega
    simp only [γ]
    gcongr
  -- the transcript's readout read down to the output and the requests
  have hread : ∀ k H a, ((((A k).alg a).toKindAlg.composeBothOut (C k) fun v =>
      (((A k).alg a).output (C k) v, (requests v.chal.logs).take (C k).Q,
        (C k).toPureEnv.oracle (H, v.chal.coins) v.chal.logs)).outLaw H).toOuterMeasure
        {o | (k, H, o) ∈ Col} =
      ((((A k).alg a).toKindAlg.composeBothOut (C k) fun v =>
        (((A k).alg a).output (C k) v, (requests v.chal.logs).take (C k).Q)).outLaw
          H).toOuterMeasure {o | ∃ v ∈ o, collides f D (pts k v) H} := by
    intro k H a
    have hm := KindAlg.outLaw_composeBothOut_map ((A k).alg a).toKindAlg (C k) (fun v =>
      (((A k).alg a).output (C k) v, (requests v.chal.logs).take (C k).Q,
        (C k).toPureEnv.oracle (H, v.chal.coins) v.chal.logs)) (fun x => (x.1, x.2.1)) H
    simp only at hm
    rw [hm, PMF.toOuterMeasure_map_apply]
    refine congrArg _ (Set.ext fun o => ?_)
    rcases o with _ | o <;> simp [Col]
  rw [toOuterMeasure_runLawIn]
  have hk : ∀ k, ∑' H, PMF.uniformOfFintype (Bits m → BitStr I J) H *
      ((A k).transcriptLawIn (C k) H).toOuterMeasure {o | (k, H, o) ∈ Col} ≤ γ := by
    intro k
    calc ∑' H, PMF.uniformOfFintype (Bits m → BitStr I J) H *
          ((A k).transcriptLawIn (C k) H).toOuterMeasure {o | (k, H, o) ∈ Col}
        = ∑' a, (A k).aux a * ∑ H, PMF.uniformOfFintype (Bits m → BitStr I J) H *
            ((((A k).alg a).toKindAlg.composeBothOut (C k) fun v =>
              (((A k).alg a).output (C k) v, (requests v.chal.logs).take (C k).Q)).outLaw
                H).toOuterMeasure {o | ∃ v ∈ o, collides f D (pts k v) H} := by
          simp only [QueryBoundedAdversary.transcriptLawIn, PMF.toOuterMeasure_bind_apply, hread]
          simp_rw [← ENNReal.tsum_mul_left]
          rw [ENNReal.tsum_comm]
          refine tsum_congr fun a => ?_
          rw [tsum_fintype, Finset.mul_sum]
          refine Finset.sum_congr rfl fun H _ => ?_
          ring
      _ ≤ ∑' a, (A k).aux a * γ :=
          ENNReal.tsum_le_tsum fun a => mul_le_mul_of_nonneg_left (hcol k a) zero_le
      _ = γ := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
  calc ∑' k, PMF.uniformOfFintype K k * ∑' H, PMF.uniformOfFintype (Bits m → BitStr I J) H *
        ((A k).transcriptLawIn (C k) H).toOuterMeasure {o | (k, H, o) ∈ Col}
      ≤ ∑' k, PMF.uniformOfFintype K k * γ :=
        ENNReal.tsum_le_tsum fun k => mul_le_mul_of_nonneg_left (hk k) zero_le
    _ = γ := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

open Classical in
/-- **A game's run logs at most `Q` requests**: for challengers answering `Q` requests, an event of
the run has the probability of the event with every logged request list of length at most `Q`. -/
theorem toOuterMeasure_runLawIn_inter_length {K : Type} [Fintype K] [Nonempty K] {t : ℕ}
    (A : K → QueryBoundedAdversary (Bits m) (BitStr I J) Req Resp O t)
    (C : K → Challenger (Bits m) (BitStr I J) Req Resp) {Q : ℕ} (hQ : ∀ k, (C k).Q = Q)
    (E : Set (K × (Bits m → BitStr I J) × Option (O × List Req × (Bits m → BitStr I J)))) :
    (runLawIn (fun k _ => A k) C).toOuterMeasure E =
      (runLawIn (fun k _ => A k) C).toOuterMeasure
        (E ∩ {x | ∀ q ∈ x.2.2, q.2.1.length ≤ Q}) := by
  rw [toOuterMeasure_runLawIn, toOuterMeasure_runLawIn]
  refine tsum_congr fun k => congrArg _ (tsum_congr fun H => congrArg _ ?_)
  rw [← PMF.toOuterMeasure_apply_inter_support _ {o | (k, H, o) ∈ E}]
  refine (congrArg _ (Set.ext fun o => ?_)).trans (PMF.toOuterMeasure_apply_inter_support _ _)
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
  refine ⟨fun ⟨hE, hs⟩ => ⟨⟨hE, ?_⟩, hs⟩, fun ⟨⟨hE, _⟩, hs⟩ => ⟨hE, hs⟩⟩
  unfold QueryBoundedAdversary.transcriptLawIn at hs
  obtain ⟨a, -, ha⟩ := (PMF.mem_support_bind_iff _ _ _).1 hs
  have hm := KindAlg.outLaw_composeBothOut_map ((A k).alg a).toKindAlg (C k) (fun v =>
    (((A k).alg a).output (C k) v, requests v.chal.logs,
      (C k).toPureEnv.oracle (H, v.chal.coins) v.chal.logs))
    (fun x => (x.1, x.2.1.take (C k).Q, x.2.2)) H
  simp only at hm
  rw [hm, PMF.mem_support_map_iff] at ha
  obtain ⟨y, -, rfl⟩ := ha
  intro q hq
  rcases y with _ | y
  · cases hq
  · cases hq
    exact (List.length_take_le _ _).trans (hQ k).le

end GordieHowe.RingSignature
