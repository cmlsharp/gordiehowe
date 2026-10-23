-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Spec.SelectionModel
public import GordieHowe.Applications.MLDSA44.Spec.Sampler

@[expose] public section

/-!
# ML-DSA selection with a rising threshold

`SampleInBall` placement `t` accepts the next candidate byte at most
`N − τ + t`.  The H circuit checks the whole selection over the `S = 128`
candidate bytes at once (`assert_sample_in_ball_gp` in `ml_dsa_hash_circuit.h`,
variant `kSibGpMemScalar`, report label `ml-native`):

```
gadget SelectFirstTau(stream, out, low, δ):
    thr[i]      := decode(low[i])                  // SibThresholdEncoding
    assert thr[0] == 256 − τ                        // eight bits
    accepted[i] := stream[i] ≤ thr[i]               // comparator on two variables
    full[i]     := i < τ ? 0 : NOT thr[i][7]
    selected[i] := accepted[i] AND NOT full[i]
    AssertFilteredPermutation(
        [(thr[i] + X·stream[i], selected[i]) for i],
        [((256 − τ + j) + X·out[j], 1) for j], δ)
    assert thr[i+1] == mux(selected[i], thr[i] + 1, thr[i])   // eight bits
```

The threshold is the scan state and also the slot label: it runs through
`256 − τ, …, 255` and wraps to `0` at the `τ`-th selection, whose cleared high
bit then disables further selection.  The prover commits only its low
`lowBits τ` bits (`kLowBits`); `decode` sets every higher bit to the `OR` of
bits `highFrom τ … lowBits τ − 1` (`kHighFrom`).  Soundness uses only that the
decoded bits are Boolean; the encoding matters for completeness, where
`Encodes τ` (a parameter condition, `decide`d at `τ = 39`) says it represents every
threshold of the trajectory.

`Model` restates the constraints over the natural-number samples, and
`Model.sound` derives the three facts `SelectScan.sound` needs.  The
specification is `SelectScan.scanFirst (accept (256 − τ))`, which
`scanFirst_accept` identifies with `GordieHowe.MLDSA44.acceptState`, the selection of
`GordieHowe.MLDSA44.acceptedCandidates`.

The `8`-bit sum `thr[i] + 1` is `Bits.increment` (`vadd(thr, 1)` in the C++, a
parallel-prefix adder; both compute `(thr + 1) mod 256` on bits).
-/

namespace GordieHowe.MLDSA44.SelectFirstTau

open Polynomial SelectScan

variable {K : Type*} [Field K] [DecidableEq K] {S τ : ℕ}

/-! ### The threshold encoding -/

/-- `kLowBits`: the bit length of `τ`. -/
def lowBits (τ : ℕ) : ℕ := Nat.size τ

/-- `kHighFrom`: the lowest bit whose `OR` with the bits above it, up to
`lowBits τ`, reconstructs the high bits. -/
def highFrom (τ : ℕ) : ℕ := Nat.log2 (2 ^ lowBits τ - τ)

/-- `SibThresholdEncoding::decode`: the committed low bits, and above them the
`OR` of bits `highFrom τ … lowBits τ − 1`. -/
def decode (τ : ℕ) (low : BitWires K (lowBits τ)) : BitWires K 8 :=
  fun b => if h : (b : ℕ) < lowBits τ then low ⟨b, h⟩
    else Bits.orRange (fun i => if h : i < lowBits τ then low ⟨i, h⟩ else 0) (highFrom τ) (lowBits τ)

omit [DecidableEq K] in
theorem decode_allBool {low : BitWires K (lowBits τ)} (hl : Bits.AllBool low) :
    Bits.AllBool (decode τ low) := by
  classical
  intro b
  unfold decode
  split_ifs
  · exact hl _
  · rw [Bits.orRange_eq (fun i _ _ => by split_ifs; exact hl _)]
    split_ifs <;> simp

/-- The encoding represents every threshold `(256 − τ + t) mod 256`, `t ≤ τ`: each
bit at or above `lowBits τ` is the `OR` of bits `highFrom τ … lowBits τ − 1`. -/
def Encodes (τ : ℕ) : Prop :=
  ∀ t ≤ τ, ∀ b < 8, lowBits τ ≤ b →
    (((256 - τ + t) % 256).testBit b ↔
      ∃ i < lowBits τ, highFrom τ ≤ i ∧ ((256 - τ + t) % 256).testBit i)

instance (τ : ℕ) : Decidable (Encodes τ) := by
  unfold Encodes
  infer_instance

example : lowBits 39 = 6 ∧ highFrom 39 = 4 := by decide

example : Encodes 39 := by decide

omit [DecidableEq K] in
theorem constBit_eq_ite_testBit (c i : ℕ) :
    Bits.constBit (K := K) c i = if c.testBit i then 1 else 0 := by
  simp [Bits.constBit, Nat.testBit_eq_decide_div_mod_eq]

omit [DecidableEq K] in
/-- On the trajectory, decoding the low bits of a threshold gives the threshold. -/
theorem decode_constBit (henc : Encodes τ) {t : ℕ} (ht : t ≤ τ) :
    decode τ (fun b : Fin (lowBits τ) => Bits.constBit (K := K) ((256 - τ + t) % 256) b) =
      fun b : Fin 8 => Bits.constBit (K := K) ((256 - τ + t) % 256) b := by
  classical
  funext b
  unfold decode
  split_ifs with hb
  · rfl
  · rw [Bits.orRange_eq (fun i _ _ => by split_ifs; exact Bits.constBit_bool _ _),
      constBit_eq_ite_testBit]
    have hiff := henc t ht b b.isLt (by omega)
    by_cases hc : ((256 - τ + t) % 256).testBit b
    · obtain ⟨i, hi, hhi, hti⟩ := hiff.mp hc
      rw [ite_eq_left hc, ite_eq_left ⟨i, hhi, hi, by rw [dite_eq_left hi]; dsimp only; rw [constBit_eq_ite_testBit, ite_eq_left hti]⟩]
    · rw [ite_eq_right hc, ite_eq_right]
      rintro ⟨i, hhi, hi, h1⟩
      rw [dite_eq_left hi] at h1
      dsimp only at h1
      rw [constBit_eq_ite_testBit] at h1
      split_ifs at h1 with hti
      · exact hc (hiff.mpr ⟨i, hi, hhi, hti⟩)
      · exact zero_ne_one h1

/-! ### The gadget -/

/-- `full[i]`: completion is impossible before position `τ`; afterwards it is the
complement of the threshold's high bit. -/
def full (τ : ℕ) (thr : Fin S → BitWires K 8) (i : Fin S) : K :=
  if (i : ℕ) < τ then 0 else Bits.bnot (thr i 7)

/-- `selected[i] = accepted[i] AND NOT full[i]`, `accepted[i] = stream[i] ≤ thr[i]`. -/
def selected (τ : ℕ) (stream thr : Fin S → BitWires K 8) (i : Fin S) : K :=
  Bits.leVar (stream i) (thr i) * Bits.bnot (full τ thr i)

/-- The pair encoding `label + X · stream`, `label_i = as_scalar(thr[i])`. -/
def enc (F : SelectionField K S) (label : K) (sample : BitWires K 8) : K :=
  label + F.X * F.embedBits (by decide) sample

/-- The recurrence target `mux(selected, thr + 1, thr)`, bitwise. -/
def next (sel : K) (thr : BitWires K 8) : BitWires K 8 :=
  fun b => mux sel (Bits.increment thr b) (thr b)

/-- `thr[0] == 256 − τ`, bitwise. -/
def initialOk (τ : ℕ) (thr : Fin S → BitWires K 8) : Bool :=
  (List.finRange S).all fun i => (i : ℕ) ≠ 0 ||
    (List.finRange 8).all fun b => decide (thr i b = Bits.constBit (256 - τ) b)

/-- `assert_selected_sequence`: the tagged product over the selected positions
equals the product over the claimed outputs. -/
def fingerprintOk (F : SelectionField K S) (τ : ℕ) (stream : Fin S → BitWires K 8)
    (out : Fin τ → BitWires K 8) (thr : Fin S → BitWires K 8) (δ : K) : Bool :=
  let sel := selected τ stream thr
  decide
    ((List.finRange S).foldl (fun acc i =>
        acc * mux (sel i) (δ - enc F (F.embedBits (by decide) (thr i)) (stream i)) 1) 1
      = (List.finRange τ).foldl
          (fun acc (j : Fin τ) => acc * (δ - enc F (F.embed (256 - τ + j)) (out j))) 1)

/-- The threshold recurrence `thr[i+1] == mux(selected[i], thr[i] + 1, thr[i])`, bitwise. -/
def stepOk (τ : ℕ) (stream thr : Fin S → BitWires K 8) : Bool :=
  (List.finRange S).all fun i =>
    if h : (i : ℕ) + 1 < S then
      (List.finRange 8).all fun b =>
        decide (thr ⟨i + 1, h⟩ b = next (selected τ stream thr i) (thr i) b)
    else true

/-- The selection constraints, in the order of `assert_sample_in_ball_gp`. -/
def run (F : SelectionField K S) (τ : ℕ) (stream : Fin S → BitWires K 8)
    (out : Fin τ → BitWires K 8) (low : Fin S → BitWires K (lowBits τ)) (δ : K) : Bool :=
  let thr := fun i => decode τ (low i)
  initialOk τ thr && fingerprintOk F τ stream out thr δ && stepOk τ stream thr

/-! ### The specification -/

/-- `SampleInBall`'s acceptance: at rank `t`, a candidate `v` is accepted when
`v ≤ i₀ + t`, with `i₀ = N − τ`. -/
-- spec-side
def accept (i₀ v t : ℕ) : Bool := decide (v ≤ i₀ + t)

/-! ### The natural-number model -/

namespace Model

/-- `selected` with the samples as naturals. -/
-- spec-side
def sel (τ : ℕ) (stream : Fin S → ℕ) (thr : Fin S → BitWires K 8) (i : Fin S) : K :=
  (if stream i ≤ Bits.natOfBits (thr i) then 1 else 0) * Bits.bnot (full τ thr i)

/-- The label of position `i`: the embedded threshold. -/
-- spec-side
def label (F : SelectionField K S) (thr : Fin S → BitWires K 8) (i : Fin S) : K :=
  F.embed (Bits.natOfBits (thr i))

/-- The label of slot `j`: the threshold `256 − τ + j` at which it is filled. -/
def outLabel (F : SelectionField K S) (τ : ℕ) (j : Fin τ) : K := F.embed (256 - τ + j)

/-- The selection's constraint groups, over the natural-number samples and the
decoded threshold bits. -/
structure Constraints (F : SelectionField K S) (τ : ℕ) (stream : Fin S → ℕ) (out : Fin τ → ℕ)
    (thr : Fin S → BitWires K 8) (δ : K) : Prop where
  initial : ∀ i : Fin S, (i : ℕ) = 0 → Bits.natOfBits (thr i) = (256 - τ) % 256
  step : ∀ (i : Fin S) (h : (i : ℕ) + 1 < S), Bits.natOfBits (thr ⟨i + 1, h⟩) =
    if sel τ stream thr i = 1 then (Bits.natOfBits (thr i) + 1) % 256 else Bits.natOfBits (thr i)
  fingerprint : Fingerprint F (sel τ stream thr) (label F thr) stream (outLabel F τ) out δ

/-- The bad event of the permutation check, fixed by the samples, the claimed
outputs and the thresholds. -/
noncomputable def badEvent (F : SelectionField K S) (τ : ℕ) (stream : Fin S → ℕ) (out : Fin τ → ℕ)
    (thr : Fin S → BitWires K 8) (hτS : τ ≤ S) : ChallengeEvent K :=
  SelectScan.badEvent F (sel τ stream thr) (label F thr) stream (outLabel F τ) out hτS

theorem sel_bool {stream : Fin S → ℕ} {thr : Fin S → BitWires K 8}
    (hthr : ∀ i, Bits.AllBool (thr i)) (i : Fin S) :
    sel τ stream thr i = 0 ∨ sel τ stream thr i = 1 := by
  unfold sel full Bits.bnot
  split_ifs <;> rcases hthr i 7 with h | h <;> simp [h]

/-- Bit `7` of an eight-bit value `v` is set exactly when `128 ≤ v`. -/
theorem bit7_eq {thr : BitWires K 8} (hb : Bits.AllBool thr) :
    thr 7 = if 128 ≤ Bits.natOfBits thr then 1 else 0 := by
  have h := Bits.constBit_natOfBits hb 7
  have hlt := Bits.natOfBits_lt thr
  have hiff : Bits.natOfBits thr / 2 ^ ((7 : Fin 8) : ℕ) % 2 = 1 ↔ 128 ≤ Bits.natOfBits thr := by
    show Bits.natOfBits thr / 2 ^ 7 % 2 = 1 ↔ _
    omega
  rw [← h, Bits.constBit]
  simp only [hiff]

/-- **The selection at one position.**  If the threshold at `i` is
`(256 − τ + t) mod 256` for a rank `t ≤ min(τ, i)`, position `i` is selected
exactly when `t < τ` and the sample is at most `256 − τ + t`.  At `t = τ` the
threshold is `0`, its high bit is clear and `full` stops selection. -/
theorem sel_eq_one_iff {stream : Fin S → ℕ} {thr : Fin S → BitWires K 8}
    (hτ : τ ≤ 128) (hthr : ∀ i, Bits.AllBool (thr i)) {i : Fin S} {t : ℕ}
    (ht : Bits.natOfBits (thr i) = (256 - τ + t) % 256) (htτ : t ≤ τ) (hti : t ≤ i) :
    sel τ stream thr i = 1 ↔ t < τ ∧ stream i ≤ 256 - τ + t := by
  have h7 := bit7_eq (hthr i)
  rw [ht] at h7
  unfold sel full Bits.bnot
  rcases Nat.lt_or_eq_of_le htτ with hlt | rfl
  · have hmod : (256 - τ + t) % 256 = 256 - τ + t := Nat.mod_eq_of_lt (by omega)
    rw [hmod] at ht h7
    rw [ite_eq_left (show 128 ≤ 256 - τ + t by omega)] at h7
    rw [ht, h7]
    split_ifs <;> simp_all
  · have hmod : (256 - t + t) % 256 = 0 := by rw [Nat.sub_add_cancel (by omega)]
    rw [hmod] at h7
    rw [ite_eq_right (by omega)] at h7
    rw [ite_eq_right (show ¬ (i : ℕ) < t by omega), h7]
    simp

/-- The threshold follows the rank: `thr[m] = (256 − τ + rank m) mod 256`, and
the rank never exceeds `τ`. -/
theorem thr_eq {stream : Fin S → ℕ} {thr : Fin S → BitWires K 8} (hτ : τ ≤ 128)
    (hthr : ∀ i, Bits.AllBool (thr i))
    (hinit : ∀ i : Fin S, (i : ℕ) = 0 → Bits.natOfBits (thr i) = (256 - τ) % 256)
    (hstep : ∀ (i : Fin S) (h : (i : ℕ) + 1 < S), Bits.natOfBits (thr ⟨i + 1, h⟩) =
      if sel τ stream thr i = 1 then (Bits.natOfBits (thr i) + 1) % 256
      else Bits.natOfBits (thr i)) :
    ∀ (m : ℕ) (hm : m < S), Bits.natOfBits (thr ⟨m, hm⟩) =
      (256 - τ + selRank (sel τ stream thr) m) % 256 ∧ selRank (sel τ stream thr) m ≤ τ := by
  intro m
  induction m with
  | zero =>
    intro hm
    rw [selRank_zero, hinit ⟨0, hm⟩ rfl]
    exact ⟨by simp, Nat.zero_le _⟩
  | succ m ih =>
    intro hm
    obtain ⟨ht, hr⟩ := ih (by omega)
    rw [hstep ⟨m, by omega⟩ hm, selRank_succ _ m (by omega)]
    have hiff := sel_eq_one_iff (stream := stream) hτ hthr ht hr (selRank_le_self _ m)
    split_ifs with hs
    · have hlt := (hiff.mp hs).1
      rw [ht]
      refine ⟨?_, by omega⟩
      rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
      omega
    · exact ⟨by rw [ht, Nat.add_zero], by omega⟩

/-- **Soundness of the model.**  `hτ0`, `hτ` and `hτS` are parameter conditions
(`0 < τ ≤ 128` as `static_assert`ed, `τ ≤ S`); `hs` and `ho` say the samples
and outputs are bytes (circuit Booleanity); `hthr` is Booleanity of the
decoded threshold bits (circuit Booleanity of the committed low bits). -/
theorem sound {F : SelectionField K S} {stream : Fin S → ℕ} {out : Fin τ → ℕ}
    {thr : Fin S → BitWires K 8} {δ : K} (hτ0 : 0 < τ) (hτ : τ ≤ 128) (hτS : τ ≤ S)
    (hs : ∀ i, stream i < 2 ^ falconSampleBits) (ho : ∀ j, out j < 2 ^ falconSampleBits)
    (hthr : ∀ i, Bits.AllBool (thr i)) (h : Constraints F τ stream out thr δ) :
    scanFirst (accept (256 - τ)) stream τ = some out ∨ (badEvent F τ stream out thr hτS).BadAt δ := by
  have hthr_eq := thr_eq (stream := stream) hτ hthr h.initial h.step
  have hthr8 : ∀ i : Fin S, Bits.natOfBits (thr i) < 2 ^ falconSampleBits := fun i =>
    (Bits.natOfBits_lt _).trans (by decide)
  refine SelectScan.sound hτS hs ho (sel_bool hthr) (fun i => F.embed_mem _) (fun j => F.embed_mem _)
    (fun i j _ hl => ?_) (fun i hlt => ?_) h.fingerprint
  · obtain ⟨ht, hr⟩ := hthr_eq i i.isLt
    have hj : 256 - τ + (j : ℕ) < 2 ^ falconSampleBits := by
      have := j.isLt; simp only [falconSampleBits]; omega
    have heq := F.embed_injOn (hthr8 i) hj hl
    rw [ht] at heq
    rcases Nat.lt_or_eq_of_le hr with hlt | heqτ
    · rw [Nat.mod_eq_of_lt (by omega)] at heq
      omega
    · rw [heqτ, Nat.sub_add_cancel (by omega)] at heq
      simp at heq
      omega
  · obtain ⟨ht, hr⟩ := hthr_eq i i.isLt
    rw [sel_eq_one_iff hτ hthr ht hr (selRank_le_self _ _)]
    simp [accept, hlt]

end Model

/-! ### Completeness of the model -/

/-- The number of candidates the greedy scan has accepted before position `m`. -/
-- spec-side
def rank (τ : ℕ) (stream : Fin S → ℕ) (m : ℕ) : ℕ :=
  (scanList (accept (256 - τ)) τ ((List.ofFn stream).take m)).length

theorem rank_le (τ : ℕ) (stream : Fin S → ℕ) (m : ℕ) : rank τ stream m ≤ τ :=
  scanList_length_le _ _ _

theorem rank_succ (τ : ℕ) (stream : Fin S → ℕ) {m : ℕ} (hm : m < S) :
    rank τ stream (m + 1) = rank τ stream m +
      if rank τ stream m < τ ∧ stream ⟨m, hm⟩ ≤ 256 - τ + rank τ stream m then 1 else 0 := by
  unfold rank
  rw [scanList_take_succ _ _ _ hm, scanStep]
  simp only [accept, decide_eq_true_eq]
  split_ifs <;> simp

theorem rank_le_self (τ : ℕ) (stream : Fin S → ℕ) : ∀ m, rank τ stream m ≤ m
  | 0 => by simp [rank, scanList]
  | m + 1 => by
    by_cases hm : m < S
    · rw [rank_succ τ stream hm]
      have := rank_le_self τ stream m
      split_ifs <;> omega
    · unfold rank
      rw [List.take_of_length_le (by simp; omega)]
      have h := rank_le_self τ stream m
      unfold rank at h
      rw [List.take_of_length_le (by simp; omega)] at h
      omega

/-- The honest threshold at position `i`: `(256 − τ + rank i) mod 256`. -/
-- spec-side
def honestThr (τ : ℕ) (stream : Fin S → ℕ) (i : Fin S) : ℕ := (256 - τ + rank τ stream i) % 256

/-- The honest committed low bits of the thresholds. -/
-- spec-side
def honestLow (τ : ℕ) (stream : Fin S → ℕ) (i : Fin S) : BitWires K (lowBits τ) :=
  fun b => Bits.constBit (honestThr τ stream i) b

namespace Model

/-- **Completeness of the model.**  The honest thresholds satisfy the constraint
groups for the greedy scan's output, at every `δ`.  `hτ` is a parameter condition; `hout` is
the success of the selection, the honest input. -/
theorem complete (F : SelectionField K S) (hτ : τ ≤ 128) {stream : Fin S → ℕ} {out : Fin τ → ℕ}
    (hout : scanFirst (accept (256 - τ)) stream τ = some out) (δ : K) :
    Constraints F τ stream out (fun i b => Bits.constBit (K := K) (honestThr τ stream i) b) δ := by
  set thr : Fin S → BitWires K 8 := fun i b => Bits.constBit (honestThr τ stream i) b
  have hthr : ∀ i, Bits.AllBool (thr i) := fun i b => Bits.constBit_bool _ _
  have hval : ∀ i : Fin S, Bits.natOfBits (thr i) = (256 - τ + rank τ stream i) % 256 := by
    intro i
    rw [Bits.natOfBits_constBit, honestThr, show (2 : ℕ) ^ 8 = 256 from rfl, Nat.mod_mod]
  have hsel : ∀ i : Fin S, sel τ stream thr i = 1 ↔
      rank τ stream i < τ ∧ stream i ≤ 256 - τ + rank τ stream i := fun i =>
    sel_eq_one_iff hτ hthr (hval i) (rank_le τ stream i) (rank_le_self τ stream i)
  have hrank : ∀ m, m ≤ S → selRank (sel τ stream thr) m = rank τ stream m := by
    intro m
    induction m with
    | zero => intro _; simp [selRank_zero, rank, scanList]
    | succ m ih =>
      intro hm
      rw [selRank_succ _ m (by omega), rank_succ τ stream (by omega), ih (by omega)]
      by_cases hs : sel τ stream thr ⟨m, by omega⟩ = 1
      · rw [ite_eq_left hs, ite_eq_left ((hsel _).mp hs)]
      · rw [ite_eq_right hs, ite_eq_right (fun h => hs ((hsel _).mpr h))]
  refine ⟨fun i hi => ?_, fun i h => ?_, ?_⟩
  · rw [hval, hi]
    simp [rank, scanList]
  · rw [hval, hval]
    have hr : rank τ stream (i + 1) = rank τ stream i +
        if rank τ stream i < τ ∧ stream i ≤ 256 - τ + rank τ stream i then 1 else 0 :=
      rank_succ τ stream i.isLt
    show (256 - τ + rank τ stream (i + 1)) % 256 = _
    rw [hr]
    by_cases h1 : sel τ stream thr i = 1
    · rw [ite_eq_left h1, ite_eq_left ((hsel i).mp h1)]
      omega
    · rw [ite_eq_right h1, ite_eq_right (fun h2 => h1 ((hsel i).mpr h2)), Nat.add_zero]
  · refine SelectScan.complete F (sel_bool hthr) (fun i => ?_) (fun i j hi hj => ?_) hout δ
    · rw [hrank i i.isLt.le, hsel]
      simp [accept]
    · rw [hrank i i.isLt.le] at hj
      have hlt : rank τ stream i < τ := ((hsel i).mp hi).1
      unfold label outLabel
      rw [hval, Nat.mod_eq_of_lt (by omega), hj]

end Model

/-! ### Correspondence and the gadget theorems -/

theorem enc_eq {F : SelectionField K S} {label : K} {sample : BitWires K 8}
    (hb : Bits.AllBool sample) : enc F label sample = SelectScan.enc F label (Bits.natOfBits sample) := by
  unfold enc SelectScan.enc
  rw [F.embedBits_eq (by decide) hb]

theorem selected_eq {stream thr : Fin S → BitWires K 8} (hs : ∀ i, Bits.AllBool (stream i))
    (hthr : ∀ i, Bits.AllBool (thr i)) (i : Fin S) :
    selected τ stream thr i = Model.sel τ (fun i => Bits.natOfBits (stream i)) thr i := by
  unfold selected Model.sel
  rw [Bits.leVar_eq (hs i) (hthr i)]

theorem next_eq {sel : K} (hsel : sel = 0 ∨ sel = 1) (thr : BitWires K 8) :
    next sel thr = if sel = 1 then Bits.increment thr else thr := by
  funext b
  unfold next mux
  rcases hsel with rfl | rfl <;> simp

theorem initialOk_iff {thr : Fin S → BitWires K 8} (hthr : ∀ i, Bits.AllBool (thr i)) :
    initialOk τ thr = true ↔
      ∀ i : Fin S, (i : ℕ) = 0 → Bits.natOfBits (thr i) = (256 - τ) % 256 := by
  simp only [initialOk, List.all_eq_true, List.mem_finRange, true_implies, Bool.or_eq_true,
    decide_eq_true_eq, ne_eq]
  refine forall_congr' fun i => ?_
  have hc := Bits.eq_constBit_iff (hthr i) (256 - τ)
  rw [show (2 : ℕ) ^ 8 = 256 from rfl] at hc
  rw [← hc]
  constructor
  · rintro (h | h) h0
    · exact absurd h0 h
    · exact h
  · intro h
    by_cases h0 : (i : ℕ) = 0
    · exact Or.inr (h h0)
    · exact Or.inl h0

theorem stepOk_iff {stream thr : Fin S → BitWires K 8} (hs : ∀ i, Bits.AllBool (stream i))
    (hthr : ∀ i, Bits.AllBool (thr i)) :
    stepOk τ stream thr = true ↔ ∀ (i : Fin S) (h : (i : ℕ) + 1 < S),
      Bits.natOfBits (thr ⟨i + 1, h⟩) =
        if Model.sel τ (fun i => Bits.natOfBits (stream i)) thr i = 1 then
          (Bits.natOfBits (thr i) + 1) % 256
        else Bits.natOfBits (thr i) := by
  simp only [stepOk, List.all_eq_true, List.mem_finRange, true_implies]
  refine forall_congr' fun i => ?_
  constructor
  · intro hi h
    rw [dite_eq_left h] at hi
    simp only [List.all_eq_true, List.mem_finRange, true_implies, decide_eq_true_eq] at hi
    rw [selected_eq hs hthr, next_eq (Model.sel_bool hthr i)] at hi
    rw [funext hi]
    split_ifs
    · exact Bits.natOfBits_increment (hthr i)
    · rfl
  · intro hi
    split_ifs with h
    · simp only [List.all_eq_true, List.mem_finRange, true_implies, decide_eq_true_eq]
      rw [selected_eq hs hthr, next_eq (Model.sel_bool hthr i)]
      have hnext : Bits.AllBool (if Model.sel τ (fun i => Bits.natOfBits (stream i)) thr i = 1 then
          Bits.increment (thr i) else thr i) := by
        split_ifs
        · exact Bits.increment_allBool (hthr i)
        · exact hthr i
      refine congrFun ((Bits.natOfBits_inj (hthr _) hnext).mp ?_)
      rw [hi h]
      split_ifs
      · exact (Bits.natOfBits_increment (hthr i)).symm
      · rfl
    · rfl

theorem fingerprintOk_iff {F : SelectionField K S} {stream : Fin S → BitWires K 8}
    {out : Fin τ → BitWires K 8} {thr : Fin S → BitWires K 8} (hs : ∀ i, Bits.AllBool (stream i))
    (ho : ∀ j, Bits.AllBool (out j)) (hthr : ∀ i, Bits.AllBool (thr i)) (δ : K) :
    fingerprintOk F τ stream out thr δ = true ↔
      Fingerprint F (Model.sel τ (fun i => Bits.natOfBits (stream i)) thr) (Model.label F thr)
        (fun i => Bits.natOfBits (stream i)) (Model.outLabel F τ) (fun j => Bits.natOfBits (out j)) δ := by
  obtain ⟨hc, hcl⟩ := SelectScan.fingerprint_products F
    (Model.sel τ (fun i => Bits.natOfBits (stream i)) thr) (Model.label F thr)
    (fun i => Bits.natOfBits (stream i)) (Model.outLabel F τ) (fun j => Bits.natOfBits (out j)) δ
  unfold fingerprintOk Fingerprint
  rw [decide_eq_true_iff, ← hc, ← hcl]
  simp only [selected_eq hs hthr, enc_eq (hs _), enc_eq (ho _), F.embedBits_eq (by decide) (hthr _)]
  rfl

/-- Correspondence to the model under Booleanity of the samples, the outputs and
the committed low bits. -/
theorem run_iff {F : SelectionField K S} {stream : Fin S → BitWires K 8}
    {out : Fin τ → BitWires K 8} {low : Fin S → BitWires K (lowBits τ)}
    (hs : ∀ i, Bits.AllBool (stream i)) (ho : ∀ j, Bits.AllBool (out j))
    (hl : ∀ i, Bits.AllBool (low i)) (δ : K) :
    run F τ stream out low δ = true ↔
      Model.Constraints F τ (fun i => Bits.natOfBits (stream i)) (fun j => Bits.natOfBits (out j))
        (fun i => decode τ (low i)) δ := by
  have hthr : ∀ i, Bits.AllBool (decode τ (low i)) := fun i => decode_allBool (hl i)
  simp only [run, Bool.and_eq_true, initialOk_iff hthr, stepOk_iff hs hthr,
    fingerprintOk_iff hs ho hthr]
  exact ⟨fun ⟨⟨h1, h2⟩, h3⟩ => ⟨h1, h3, h2⟩, fun h => ⟨⟨h.initial, h.fingerprint⟩, h.step⟩⟩

/-- The bad event of the wire-level gadget, fixed by its arguments. -/
-- spec-side
noncomputable def badEvent (F : SelectionField K S) (τ : ℕ) (stream : Fin S → BitWires K 8)
    (out : Fin τ → BitWires K 8) (low : Fin S → BitWires K (lowBits τ)) (hτS : τ ≤ S) :
    ChallengeEvent K :=
  Model.badEvent F τ (fun i => Bits.natOfBits (stream i)) (fun j => Bits.natOfBits (out j))
    (fun i => decode τ (low i)) hτS

/-- **Soundness.**  `hτ0`, `hτ`, `hτS` are parameter conditions; `hs` comes from the hash gadget
(the candidate bytes are SHAKE256 output bits), `ho` and `hl` are Booleanity of the
committed outputs and low threshold bits. -/
theorem sound {F : SelectionField K S} {stream : Fin S → BitWires K 8}
    {out : Fin τ → BitWires K 8} {low : Fin S → BitWires K (lowBits τ)} {δ : K}
    (hτ0 : 0 < τ) (hτ : τ ≤ 128) (hτS : τ ≤ S)
    (hs : ∀ i, Bits.AllBool (stream i)) (ho : ∀ j, Bits.AllBool (out j))
    (hl : ∀ i, Bits.AllBool (low i)) (h : run F τ stream out low δ = true) :
    scanFirst (accept (256 - τ)) (fun i => Bits.natOfBits (stream i)) τ =
        some (fun j => Bits.natOfBits (out j)) ∨
      (badEvent F τ stream out low hτS).BadAt δ :=
  Model.sound hτ0 hτ hτS (fun i => (Bits.natOfBits_lt _).trans (by decide))
    (fun j => (Bits.natOfBits_lt _).trans (by decide)) (fun i => decode_allBool (hl i))
    ((run_iff hs ho hl δ).mp h)

/-- **Completeness.**  With the honest low bits, the gadget passes at every `δ`
when the greedy scan selects `out`.  `hτ` and `henc` are parameter conditions; `hout` is the
honest input. -/
theorem complete (F : SelectionField K S) (hτ : τ ≤ 128) (henc : Encodes τ)
    {stream : Fin S → BitWires K 8} {out : Fin τ → BitWires K 8}
    (hs : ∀ i, Bits.AllBool (stream i)) (ho : ∀ j, Bits.AllBool (out j))
    (hout : scanFirst (accept (256 - τ)) (fun i => Bits.natOfBits (stream i)) τ =
      some (fun j => Bits.natOfBits (out j))) (δ : K) :
    run F τ stream out (honestLow τ fun i => Bits.natOfBits (stream i)) δ = true := by
  rw [run_iff (low := honestLow τ fun i => Bits.natOfBits (stream i)) hs ho
    (fun i b => Bits.constBit_bool _ _)]
  have hdec : (fun i => decode τ (honestLow (K := K) τ (fun i => Bits.natOfBits (stream i)) i)) =
      fun i (b : Fin 8) => Bits.constBit (honestThr τ (fun i => Bits.natOfBits (stream i)) i) b :=
    funext fun i => decode_constBit henc (rank_le τ _ i)
  rw [hdec]
  exact Model.complete F hτ hout δ

/-! ### The specification as `SampleInBall`'s selection -/

theorem foldl_scanStep_of_le {i₀ n : ℕ} :
    ∀ (u L : List ℕ), n ≤ L.length → u.foldl (scanStep (accept i₀) n) L = L
  | [], _, _ => rfl
  | v :: u, L, h => by
    rw [List.foldl_cons, scanStep, ite_eq_right (by omega)]
    exact foldl_scanStep_of_le u L h

theorem foldl_scanStep_next {i₀ n : ℕ} :
    ∀ {u L : List ℕ} {j : ℕ} {t : List ℕ}, L.length < n →
      MLDSA44.nextAccepted (i₀ + L.length) u = some (j, t) →
      u.foldl (scanStep (accept i₀) n) L = t.foldl (scanStep (accept i₀) n) (L ++ [j])
  | [], _, _, _, _, h => by simp [MLDSA44.nextAccepted] at h
  | v :: u, L, j, t, hL, h => by
    unfold MLDSA44.nextAccepted at h
    rw [List.foldl_cons, scanStep]
    split_ifs at h with hv
    · cases h
      rw [ite_eq_left ⟨hL, by simp [accept, hv]⟩]
    · rw [ite_eq_right (by simp [accept, hv])]
      exact foldl_scanStep_next hL h

theorem foldl_scanStep_none {i₀ n : ℕ} :
    ∀ {u L : List ℕ}, L.length < n → MLDSA44.nextAccepted (i₀ + L.length) u = none →
      u.foldl (scanStep (accept i₀) n) L = L
  | [], _, _, _ => rfl
  | v :: u, L, hL, h => by
    unfold MLDSA44.nextAccepted at h
    rw [List.foldl_cons, scanStep]
    split_ifs at h with hv
    rw [ite_eq_right (by simp [accept, hv])]
    exact foldl_scanStep_none hL h

/-- The greedy scan against `MLDSA44.acceptState`: after `k ≤ n` placements the
scan is at the state `acceptState` reaches, or has already stopped short. -/
theorem scanList_acceptState {i₀ n : ℕ} (u : List ℕ) :
    ∀ k ≤ n, match MLDSA44.acceptState i₀ u k with
      | some s => scanList (accept i₀) n u = s.2.foldl (scanStep (accept i₀) n) s.1
      | none => (scanList (accept i₀) n u).length < k := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
    intro hk
    have ih := ih (by omega)
    simp only [MLDSA44.acceptState]
    rcases hs : MLDSA44.acceptState i₀ u k with _ | s
    · rw [hs] at ih
      simp only [Option.bind_none]
      omega
    · rw [hs] at ih
      have hlen := MLDSA44.acceptState_length hs
      simp only [Option.bind_some]
      rcases hn : MLDSA44.nextAccepted (i₀ + k) s.2 with _ | ⟨j, t⟩
      · simp only [Option.map_none]
        rw [ih, foldl_scanStep_none (by omega) (by rw [hlen]; exact hn), hlen]
        omega
      · simp only [Option.map_some]
        rw [ih]
        exact foldl_scanStep_next (by omega) (by rw [hlen]; exact hn)

/-- **The specification is `SampleInBall`'s selection.** -/
theorem scanFirst_accept (i₀ n : ℕ) (stream : Fin S → ℕ) :
    scanFirst (accept i₀) stream n =
      (MLDSA44.acceptState i₀ (List.ofFn stream) n).map fun s (t : Fin n) => s.1.getD t 0 := by
  have h := scanList_acceptState (i₀ := i₀) (n := n) (List.ofFn stream) n le_rfl
  unfold scanFirst
  dsimp only
  rcases hs : MLDSA44.acceptState i₀ (List.ofFn stream) n with _ | s
  · rw [hs] at h
    dsimp only at h
    simp only [Option.map_none]
    rw [dite_eq_right (by omega)]
  · rw [hs] at h
    dsimp only at h
    have hlen := MLDSA44.acceptState_length hs
    rw [foldl_scanStep_of_le _ _ hlen.ge] at h
    simp only [Option.map_some, h, hlen, dite_true, Option.some.injEq]
    funext t
    rw [List.getD_eq_getElem _ _ (by omega)]
    rfl

/-- `MLDSA44.acceptedCandidates` is the greedy scan over the `C` candidate bytes. -/
theorem acceptedCandidates_eq (P : Params) {C : ℕ} (f : Fin (C + 8) → ℕ) :
    MLDSA44.acceptedCandidates P f =
      scanFirst (accept (P.N - P.τ)) (fun i : Fin C => f ⟨8 + i, by omega⟩) P.τ := by
  rw [scanFirst_accept]
  rfl

end GordieHowe.MLDSA44.SelectFirstTau
