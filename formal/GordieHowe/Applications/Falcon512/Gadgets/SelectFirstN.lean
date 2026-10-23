-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Spec.SelectionModel

@[expose] public section

/-!
# Falcon selection on bit wires

Samples and outputs are `w` little-endian field bits (`w = falconSampleBits = 16` for Falcon, the
default width of `SelectionField`). Comparisons use `Bits.ltConst`; encoding is a linear combination
of the chosen subfield basis. `Model` contains the proved natural-number selection argument.
`run_iff` connects this circuit to it under Booleanity, without decoding inside `run`. The caller
asserts Booleanity of committed outputs; hash soundness supplies it for the stream. The circuit also
pins each comparator result to a bit, as in `gp_select.h`. Bounds and indices are compile-time
constants.
-/

namespace GordieHowe.Falcon512.SelectFirstN

variable {K : Type*} [Field K] [DecidableEq K] {S n w : ℕ}

/-- The pair encoding used in the permutation fingerprint. -/
def enc (F : SelectionField K S w) (label : K) (sample : BitWires K w) : K :=
  label + F.X * F.embedBits le_rfl sample

/-- Selection indicator, with completion disabled before position `n`. -/
def selected (n bound : ℕ) (stream : Fin S → BitWires K w)
    (route : Fin S → Route K) (i : Fin S) : K :=
  if (i : ℕ) < n then Bits.ltConst (stream i) bound
  else Bits.ltConst (stream i) bound * (1 - (route i).full)

/-- Arithmetic-circuit selection constraints. -/
def run (F : SelectionField K S w) (bound : ℕ)
    (stream : Fin S → BitWires K w) (out : Fin n → BitWires K w)
    (route : Fin S → Route K) (δ : K) : Bool :=
  let sel := selected n bound stream route
  let idx := List.finRange S
  (idx.all fun i => decide (Bits.ltConst (stream i) bound * (Bits.ltConst (stream i) bound - 1) = 0))
  && (idx.all fun i => (i : ℕ) ≠ 0 || decide ((route i).count_enc = 1))
  && (idx.all fun i => (i : ℕ) < n ||
        (decide ((route i).full * ((route i).full - 1) = 0)
         && decide ((route i).full * ((route i).count_enc - F.g ^ n) = 0)))
  && (idx.all fun i =>
        if h : (i : ℕ) + 1 < S then
          decide ((route ⟨i + 1, h⟩).count_enc = (route i).count_enc * Model.mux (sel i) F.g 1)
        else true)
  && decide
      ((idx.foldl (fun acc i => acc * Model.mux (sel i) (δ - enc F (route i).count_enc (stream i)) 1) 1)
        = (List.finRange n).foldl (fun acc (j : Fin n) => acc * (δ - enc F (F.g ^ (j : ℕ)) (out j))) 1)

/-- The field encoding equals its semantic natural-number view on Boolean wires. -/
theorem enc_eq_model {F : SelectionField K S w} {label : K} {sample : BitWires K w}
    (hb : Bits.AllBool sample) :
    enc F label sample = Model.enc F label (Bits.natOfBits sample) := by
  unfold enc Model.enc
  rw [F.embedBits_eq le_rfl hb]

/-- Selection agrees with the semantic model when sample wires are Boolean. -/
theorem selected_eq_model {bound : ℕ} {stream : Fin S → BitWires K w}
    (hbound : bound < 2 ^ w) (hs : ∀ i, Bits.AllBool (stream i))
    (route : Fin S → Route K) (i : Fin S) :
    selected n bound stream route i =
      Model.selected n bound (fun j => Bits.natOfBits (stream j)) route i := by
  simp only [selected, Model.selected, Model.accept, Bits.ltConst_eq (hs i) hbound]

/-- Correspondence to the proved semantic model. `hbound` is a parameter condition;
`hs` and `ho` are the hash gadget's output Booleanity and committed-bit Booleanity,
respectively. -/
theorem run_iff {F : SelectionField K S w} {bound : ℕ}
    {stream : Fin S → BitWires K w} {out : Fin n → BitWires K w}
    (hbound : bound < 2 ^ w) (hs : ∀ i, Bits.AllBool (stream i))
    (ho : ∀ j, Bits.AllBool (out j)) (route : Fin S → Route K) (δ : K) :
    run F bound stream out route δ = true ↔
      Model.Constraints F bound (fun i => Bits.natOfBits (stream i))
        (fun j => Bits.natOfBits (out j)) route δ := by
  have hall : (List.finRange S).all (fun _ => true) = true := by simp
  simp only [run, Bits.ltConst_mul_sub_one (hs _) hbound, decide_true,
    hall, Bool.true_and, selected_eq_model hbound hs,
    enc_eq_model (hs _), enc_eq_model (ho _)]
  simp only [List.all_eq_true, decide_eq_true_eq, Bool.and_eq_true, Bool.or_eq_true]
  constructor
  · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i hi
      rcases h1 i (List.mem_finRange i) with h | h
      · omega
      · exact h
    · intro i hi
      rcases h2 i (List.mem_finRange i) with h | h
      · omega
      · exact h
    · intro i hi
      have h3i := h3 i (List.mem_finRange i)
      rw [dite_eq_left hi] at h3i
      exact of_decide_eq_true h3i
    · obtain ⟨hc, hcl⟩ := Model.fingerprint_products F bound
        (fun i => Bits.natOfBits (stream i)) (fun j => Bits.natOfBits (out j)) route δ
      rw [Model.Fingerprint, ← hc, ← hcl]
      exact h4
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
    · intro i _
      by_cases hi0 : (i:ℕ) = 0
      · right; exact h1 i hi0
      · left; exact hi0
    · intro i _
      by_cases hin : (i:ℕ) < n
      · left; exact hin
      · right; exact h2 i (by omega)
    · intro i _
      by_cases hi1 : (i : ℕ) + 1 < S
      · rw [dite_eq_left hi1]
        exact decide_eq_true (h3 i hi1)
      · rw [dite_eq_right hi1]
    · obtain ⟨hc, hcl⟩ := Model.fingerprint_products F bound
        (fun i => Bits.natOfBits (stream i)) (fun j => Bits.natOfBits (out j)) route δ
      rw [hc, hcl]
      exact h4

/-- Challenge polynomial fixed by the witness, before `δ` is sampled. -/
-- spec-side
noncomputable def badEvent (F : SelectionField K S w) (bound : ℕ)
    (stream : Fin S → BitWires K w) (out : Fin n → BitWires K w)
    (route : Fin S → Route K) (hnS : n ≤ S) : ChallengeEvent K :=
  Model.badEvent F bound (fun i => Bits.natOfBits (stream i))
    (fun j => Bits.natOfBits (out j)) route hnS

/-- Soundness of the wire-level gadget. The bound and length are parameter conditions;
Booleanity is supplied by the hash gadget and committed-bit assertions. -/
theorem sound {F : SelectionField K S w} {bound : ℕ}
    {stream : Fin S → BitWires K w} {out : Fin n → BitWires K w}
    {route : Fin S → Route K} {δ : K}
    (hnS : n ≤ S) (hbound : bound < 2 ^ w)
    (hs : ∀ i, Bits.AllBool (stream i)) (ho : ∀ j, Bits.AllBool (out j))
    (h : run F bound stream out route δ = true) :
    firstAccepted (fun v => decide (v < bound)) (fun i => Bits.natOfBits (stream i)) n
        = some (fun j => Bits.natOfBits (out j))
      ∨ (badEvent F bound stream out route hnS).BadAt δ := by
  rw [run_iff hbound hs ho] at h
  exact Model.sound hnS (fun _ => Bits.natOfBits_lt _) (fun _ => Bits.natOfBits_lt _) h

/-- Completeness for Boolean sample wires. The only input condition is success
of selection; Booleanity describes the honest wire encoding. -/
theorem complete (F : SelectionField K S w) {bound : ℕ}
    {stream : Fin S → BitWires K w} {out : Fin n → BitWires K w}
    (hbound : bound < 2 ^ w) (hs : ∀ i, Bits.AllBool (stream i))
    (ho : ∀ j, Bits.AllBool (out j))
    (hout : firstAccepted (fun v => decide (v < bound))
        (fun i => Bits.natOfBits (stream i)) n = some (fun j => Bits.natOfBits (out j)))
    (δ : K) :
    run F bound stream out
      (Model.hashToPointRoute n F bound (fun i => Bits.natOfBits (stream i))) δ = true := by
  rw [run_iff hbound hs ho]
  exact Model.complete F hout δ

end GordieHowe.Falcon512.SelectFirstN
