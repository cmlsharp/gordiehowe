-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA.Signing.Flatten
public import LatticeCrypto.MLDSA.ConcretePrimitives
public import LatticeCrypto.MLDSA.Concrete.LawBounds

@[expose] public section

/-!
# The shape of the concrete `SampleInBall`

The vendored `SampleInBall` (FIPS 204 Algorithm 29, `sampleInBallPoly?` with the bounded candidate
stream, total as `sampleInBallPoly`) starts from the zero array and runs one placement
`c[i] := c[j]; c[j] := ±1` per write index `i ∈ [256 - τ, 256)`. Every placement keeps the
coefficients in `{-1, 0, 1}` and adds at most one nonzero coefficient, so the output has
`polyNorm ≤ 1` and at most `τ` nonzero coefficients; the rejecting branch returns `0`.

* `sampleInBallShape_concrete`: `SampleInBallShape (concretePrimitives p)` for every `p`.
* `signingLaws_concrete`: `SigningLaws (concretePrimitives p)` with the concrete NTT, for every
  approved `p`.
* `tvDist_flatRingProver_mldsa65_concrete_le`, `tvDist_flatRingProver_mldsa87_concrete_le`:
  the ML-DSA-65 and ML-DSA-87 ring bounds at the concrete primitives and the concrete NTT, with no
  hypothesis on the primitives.
-/

namespace GordieHowe.MLDSA

open _root_.MLDSA _root_.MLDSA.Concrete GordieHowe.MLDSA44 Finset PMF
open scoped ENNReal

/-! ## Array lemmas -/

/-- Reading an array after `set!`: the written value at the written in-bounds index, the old
entry elsewhere. -/
theorem array_getElem!_set! {α : Type*} [Inhabited α] (a : Array α) (i k : ℕ) (v : α) :
    (a.set! i v)[k]! = if i = k ∧ i < a.size then v else a[k]! := by
  simp only [Array.set!, getElem!_def, Array.getElem?_setIfInBounds]
  by_cases h : i = k
  · subst h
    by_cases h2 : i < a.size
    · simp [h2]
    · simp [h2]
  · simp [h]

/-- Every entry of a zero array reads as `0`, in bounds or not. -/
theorem array_getElem!_replicate_zero (n k : ℕ) : (Array.replicate n (0 : Coeff))[k]! = 0 := by
  by_cases h : k < n
  · simp [h]
  · simp [h]
    rfl

/-- Counting the `Fin n` indices satisfying a predicate of their value counts `range n`. -/
theorem card_filter_fin_val (n : ℕ) (P : ℕ → Prop) [DecidablePred P] :
    (univ.filter fun k : Fin n => P k.val).card = ((range n).filter P).card := by
  refine card_bij (fun k _ => k.val) (by simp) (fun a _ b _ h => Fin.ext h) ?_
  intro b hb
  simp only [mem_filter, mem_range] at hb
  exact ⟨⟨b, hb.1⟩, by simp [hb.2], rfl⟩

/-! ## Ternary coefficients -/

/-- A coefficient in `{-1, 0, 1}`. -/
def IsTernary (x : Coeff) : Prop := x = 0 ∨ x = 1 ∨ x = -1

/-- A ternary coefficient has centered absolute value at most `1`. -/
theorem IsTernary.natAbs_centeredRepr_le {x : Coeff} (hx : IsTernary x) :
    (LatticeCrypto.centeredRepr x).natAbs ≤ 1 := by
  have h1 : ((1 : Coeff).valMinAbs).natAbs = 1 := by
    have : (1 : Coeff) = ((1 : ℕ) : Coeff) := by simp
    rw [this, ZMod.valMinAbs_natCast_of_le_half (by norm_num [modulus])]
    rfl
  rw [LatticeCrypto.centeredRepr_eq_valMinAbs]
  rcases hx with rfl | rfl | rfl
  · simp
  · exact h1.le
  · rw [ZMod.natAbs_valMinAbs_neg]
    exact h1.le

/-! ## The placement invariant -/

/-- The number of nonzero entries among the first `ringDegree` of an array. -/
def arrayWeight (a : Array Coeff) : ℕ :=
  ((range ringDegree).filter fun k => a[k]! ≠ 0).card

/-- The `SampleInBall` loop invariant after `n` placements: every entry is ternary and at most
`n` of the first `ringDegree` entries are nonzero. -/
structure BallState (a : Array Coeff) (n : ℕ) : Prop where
  /-- Every entry is in `{-1, 0, 1}`. -/
  ternary : ∀ k : ℕ, IsTernary a[k]!
  /-- At most `n` nonzero entries. -/
  weight_le : arrayWeight a ≤ n

/-- The zero array satisfies the invariant with no placements. -/
theorem ballState_replicate_zero : BallState (Array.replicate ringDegree 0) 0 where
  ternary k := Or.inl (array_getElem!_replicate_zero _ k)
  weight_le := by
    simp [arrayWeight, array_getElem!_replicate_zero]

/-- One placement `c[i] := c[j]; c[j] := s` with a ternary `s` keeps the coefficients ternary and
adds at most one nonzero entry. -/
theorem BallState.place {a : Array Coeff} {n : ℕ} (h : BallState a n) (i j : ℕ) {s : Coeff}
    (hs : IsTernary s) : BallState ((a.set! i a[j]!).set! j s) (n + 1) where
  ternary k := by
    rw [array_getElem!_set!, array_getElem!_set!]
    split_ifs
    · exact hs
    · exact h.ternary j
    · exact h.ternary k
  weight_le := by
    refine le_trans ?_ (Nat.succ_le_succ h.weight_le)
    refine le_trans (card_le_card (s := _) (t := insert (if a[j]! ≠ 0 then i else j)
      ((range ringDegree).filter fun k => a[k]! ≠ 0)) ?_) (card_insert_le _ _)
    intro k hk
    simp only [mem_filter, mem_range, mem_insert] at hk ⊢
    rw [array_getElem!_set!, array_getElem!_set!, Array.size_set!] at hk
    obtain ⟨hk, hne⟩ := hk
    by_cases hjk : j = k ∧ j < a.size
    · obtain ⟨rfl, -⟩ := hjk
      by_cases hz : a[j]! ≠ 0
      · exact Or.inr ⟨hk, hz⟩
      · simp [hz]
    · simp only [hjk, ite_false] at hne
      split_ifs at hne with hik
      · obtain ⟨rfl, -⟩ := hik
        simp [hne]
      · exact Or.inr ⟨hk, hne⟩

/-- `sampleInBallStep` extends the invariant by one placement. -/
theorem ballState_sampleInBallStep (candidates : Array UInt8) (start : ℕ) (signBit : ℕ → Bool)
    {s : Option (Array Coeff × ℕ)} {n : ℕ} (hs : ∀ st, s = some st → BallState st.1 n) (i : ℕ) :
    ∀ st, sampleInBallStep candidates start signBit s i = some st → BallState st.1 (n + 1) := by
  intro st hst
  cases s with
  | none => simp [sampleInBallStep] at hst
  | some st₀ =>
    simp only [sampleInBallStep, Option.bind_some, Option.map_eq_some_iff] at hst
    obtain ⟨r, -, rfl⟩ := hst
    refine (hs st₀ rfl).place i r.1 ?_
    unfold IsTernary
    split_ifs <;> simp

/-- The `SampleInBall` fold over the write indices `l` extends the invariant by `l.length`
placements. -/
theorem ballState_foldl_sampleInBallStep (candidates : Array UInt8) (start : ℕ)
    (signBit : ℕ → Bool) (l : List ℕ) :
    ∀ (s : Option (Array Coeff × ℕ)) (n : ℕ), (∀ st, s = some st → BallState st.1 n) →
      ∀ st, l.foldl (sampleInBallStep candidates start signBit) s = some st →
        BallState st.1 (n + l.length) := by
  induction l with
  | nil => intro s n hs st hst; exact hs st hst
  | cons i l ih =>
    intro s n hs st hst
    rw [List.foldl_cons] at hst
    have := ih _ (n + 1) (ballState_sampleInBallStep candidates start signBit hs i) st hst
    simpa [Nat.add_assoc, Nat.add_comm 1] using this

/-! ## The concrete `SampleInBall` -/

/-- A polynomial with ternary coefficients and at most `τ` nonzero ones: `polyNorm ≤ 1` and
weight at most `τ`, the two fields of `SampleInBallShape`. -/
theorem shape_of_ternary {c : Rq} {τ : ℕ} (hc : ∀ j : Fin ringDegree, IsTernary (c.get j))
    (hw : (univ.filter fun j : Fin ringDegree => c.get j ≠ 0).card ≤ τ) :
    polyNorm c ≤ 1 ∧ (univ.filter fun j : Fin ringDegree => c.get j ≠ 0).card ≤ τ := by
  refine ⟨?_, hw⟩
  rw [polyNorm_eq_cInfNorm, LatticeCrypto.cInfNorm_le_iff]
  exact fun j => (hc j).natAbs_centeredRepr_le

/-- A successful bounded `SampleInBall` (`sampleInBallPoly?`) outputs ternary coefficients, at
most `τ` of them nonzero. -/
theorem sampleInBallPoly?_shape (p : Params) {cTilde : CommitHashBytes p} {c : Rq}
    (h : sampleInBallPoly? p cTilde = some c) :
    (∀ j : Fin ringDegree, IsTernary (c.get j)) ∧
      (univ.filter fun j : Fin ringDegree => c.get j ≠ 0).card ≤ p.tau := by
  unfold sampleInBallPoly? at h
  obtain ⟨st, hst, rfl⟩ := Option.map_eq_some_iff.mp h
  have hb := ballState_foldl_sampleInBallStep _ _ _ _ _ 0
    (fun st h => by cases h; exact ballState_replicate_zero) st hst
  rw [List.length_range', Nat.zero_add] at hb
  refine ⟨fun j => by simpa using hb.ternary j, ?_⟩
  simpa [arrayWeight, card_filter_fin_val ringDegree (fun k => st.1[k]! ≠ 0)] using hb.weight_le

/-- The total concrete `SampleInBall` (`sampleInBallPoly`) has ternary coefficients, at most `τ`
of them nonzero (the rejecting branch is `0`). -/
theorem sampleInBallPoly_shape (p : Params) (cTilde : CommitHashBytes p) :
    (∀ j : Fin ringDegree, IsTernary ((sampleInBallPoly p cTilde).get j)) ∧
      (univ.filter fun j : Fin ringDegree => (sampleInBallPoly p cTilde).get j ≠ 0).card ≤
        p.tau := by
  unfold sampleInBallPoly
  cases h : sampleInBallPoly? p cTilde with
  | some c => exact sampleInBallPoly?_shape p h
  | none =>
    refine ⟨fun j => Or.inl ?_, ?_⟩ <;> simp

/-- **The concrete `SampleInBall` has the challenge shape**: centered coefficients in
`{-1, 0, 1}` and at most `τ` nonzero, for every parameter set. -/
theorem sampleInBallShape_concrete (p : Params) : SampleInBallShape (concretePrimitives p) where
  norm_le_one cTilde := (shape_of_ternary (sampleInBallPoly_shape p cTilde).1
    (sampleInBallPoly_shape p cTilde).2).1
  weight_le cTilde := (sampleInBallPoly_shape p cTilde).2

/-! ## The signing laws of the concrete primitives -/

section ConcreteRing

attribute [local instance] concreteNTTRingOps

/-- **The concrete primitives satisfy the signing laws** with the concrete NTT, at every approved
parameter set: the transform laws (`concreteNTTRingLaws`), `hide_low`
(`concreteRounding_hide_low_of_isApproved`), and the challenge product bound
(`sampleInBallShape_concrete` with `norm_challenge_coeffScalarVecMul_le`, `β = τη`). -/
theorem signingLaws_concrete (p : Params) (hp : p.isApproved) :
    SigningLaws (concretePrimitives p) where
  transform := concreteNTTRingLaws
  hide_low r s b hs hlow := concreteRounding_hide_low_of_isApproved p hp r s b
    (by rwa [polyNorm_eq_cInfNorm] at hs) (by rwa [polyNorm_eq_cInfNorm] at hlow)
  sampleInBall_smul_bound cTilde k s hs := by
    have := concreteNTTRingLaws
    exact norm_challenge_coeffScalarVecMul_le concreteNTTRingOps _ s
      ((sampleInBallShape_concrete p).norm_le_one cTilde)
      ((sampleInBallShape_concrete p).weight_le cTilde) hs

/-- **ML-DSA-65 rings of standard keys, concrete primitives**: `tvDist_flatRingProver_mldsa65_le`
at `concretePrimitives mldsa65` and the concrete NTT, with the signing laws discharged by
`signingLaws_concrete` and `SampleInBallShape` by `sampleInBallShape_concrete`. -/
theorem tvDist_flatRingProver_mldsa65_concrete_le [Nonempty (MaskBox mldsa65)]
    (sk : SecretKey mldsa65)
    (aHat : TqMatrix mldsa65.k mldsa65.l) (hs2 : polyVecBounded sk.s2 mldsa65.eta)
    (ht0 : polyVecNorm sk.t0 ≤ 2 ^ (droppedBits - 1)) {N : ℕ} (i : Fin N) {βmin : ℚ≥0}
    (hβ0 : (βmin : ℝ≥0∞) ≠ 0) (hβ1 : (βmin : ℝ≥0∞) ≤ 1)
    (hkeep : SignerKeeps (concretePrimitives mldsa65) sk aHat βmin) :
    tvDist (flatRingProver (concretePrimitives mldsa65) sk aHat
          (standardRing (concretePrimitives mldsa65) N) i βmin)
        ((PMF.uniformOfFintype (BucketVec mldsa65)).bind fun v =>
          (PMF.uniformOfFintype (Fin N × BucketVec mldsa65 → CommitHashBytes mldsa65)).map
            fun H => (H, some v)) ≤
      ringOracleError (concretePrimitives mldsa65) sk aHat
          (standardRing (concretePrimitives mldsa65) N) i βmin +
        regError (concretePrimitives mldsa65) sk aHat βmin +
        flatError (concretePrimitives mldsa65) sk
          (standardRing (concretePrimitives mldsa65) N) i βmin :=
  SigningLaws.tvDist_flatRingProver_mldsa65_le (concretePrimitives mldsa65)
    (signingLaws_concrete mldsa65 (Or.inr (Or.inl rfl)))
    (sampleInBallShape_concrete mldsa65) sk aHat hs2 ht0 i hβ0 hβ1 hkeep

/-- **ML-DSA-87 rings of standard keys, concrete primitives**: `tvDist_flatRingProver_mldsa87_le`
at `concretePrimitives mldsa87` and the concrete NTT, with the signing laws discharged by
`signingLaws_concrete` and `SampleInBallShape` by `sampleInBallShape_concrete`. -/
theorem tvDist_flatRingProver_mldsa87_concrete_le [Nonempty (MaskBox mldsa87)]
    (sk : SecretKey mldsa87)
    (aHat : TqMatrix mldsa87.k mldsa87.l) (hs2 : polyVecBounded sk.s2 mldsa87.eta)
    (ht0 : polyVecNorm sk.t0 ≤ 2 ^ (droppedBits - 1)) {N : ℕ} (i : Fin N) {βmin : ℚ≥0}
    (hβ0 : (βmin : ℝ≥0∞) ≠ 0) (hβ1 : (βmin : ℝ≥0∞) ≤ 1)
    (hkeep : SignerKeeps (concretePrimitives mldsa87) sk aHat βmin) :
    tvDist (flatRingProver (concretePrimitives mldsa87) sk aHat
          (standardRing (concretePrimitives mldsa87) N) i βmin)
        ((PMF.uniformOfFintype (BucketVec mldsa87)).bind fun v =>
          (PMF.uniformOfFintype (Fin N × BucketVec mldsa87 → CommitHashBytes mldsa87)).map
            fun H => (H, some v)) ≤
      ringOracleError (concretePrimitives mldsa87) sk aHat
          (standardRing (concretePrimitives mldsa87) N) i βmin +
        regError (concretePrimitives mldsa87) sk aHat βmin +
        flatError (concretePrimitives mldsa87) sk
          (standardRing (concretePrimitives mldsa87) N) i βmin :=
  SigningLaws.tvDist_flatRingProver_mldsa87_le (concretePrimitives mldsa87)
    (signingLaws_concrete mldsa87 (Or.inr (Or.inr rfl)))
    (sampleInBallShape_concrete mldsa87) sk aHat hs2 ht0 i hβ0 hβ1 hkeep

end ConcreteRing

end GordieHowe.MLDSA
