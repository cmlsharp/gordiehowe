-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.Assumptions

@[expose] public section

/-!
# GordieHowe: facts about a circuit's input layout

Facts about the input blocks of a GKR circuit (`InputBlock`, `InputBlock.layoutEnd`): in a
contiguous layout every input is held by exactly one block, so a function of the blocks defined
only at the blocks holding an input reads the holding block's value (`findSome?_eq_of_holds`); the
blocks holding a committed coordinate, a pad coordinate or a bit view's coordinate
(`GordieHowe.RealizedProgram.exists_committed_block`, `exists_pad_block`, `exists_view_block`).
-/

namespace GordieHowe.RealizedProgram

open Export

/-! ## Layout facts about input blocks -/

namespace InputBlock

theorem layoutEnd_first_le : ∀ {s e : ℕ} {bs : List InputBlock}, InputBlock.layoutEnd s bs = some e →
    ∀ b ∈ bs, s ≤ b.first
  | _, _, [], _, _, hb => absurd hb (List.not_mem_nil)
  | s, e, b' :: bs, h, b, hb => by
    simp only [InputBlock.layoutEnd] at h
    split_ifs at h with hf
    rcases List.mem_cons.1 hb with rfl | hb
    · omega
    · have := layoutEnd_first_le h b hb
      omega

theorem pubValue?_isSome {K : Type} {pv : ℕ → ℕ → K} {rp : RealPub → ℕ → K} {j : ℕ}
    {b : InputBlock} {y : K} (h : b.pubValue? pv rp j = some y) :
    b.first ≤ j ∧ j < b.first + b.len := by
  cases b <;> simp only [pubValue?, reduceCtorEq] at h <;> split_ifs at h with h' <;>
    simp_all [first, len]

/-- **In a contiguous layout, the block holding an input is the first one**: a public block holding
input `j` gives the first public block value of `j`. -/
theorem findSome_pubValue? {K : Type} {pv : ℕ → ℕ → K} {rp : RealPub → ℕ → K} {j : ℕ} {y : K} :
    ∀ {s e : ℕ} {bs : List InputBlock}, InputBlock.layoutEnd s bs = some e →
      ∀ b ∈ bs, b.pubValue? pv rp j = some y → bs.findSome? (·.pubValue? pv rp j) = some y
  | _, _, [], _, _, hb, _ => absurd hb (List.not_mem_nil)
  | s, e, b' :: bs, h, b, hb, hy => by
    simp only [InputBlock.layoutEnd] at h
    split_ifs at h with hf
    rw [List.findSome?_cons]
    rcases List.mem_cons.1 hb with rfl | hb
    · rw [hy]
    · cases hb' : b'.pubValue? pv rp j with
      | none => exact findSome_pubValue? h b hb hy
      | some y' =>
        exfalso
        have h1 := pubValue?_isSome hb'
        have h2 := pubValue?_isSome hy
        have h3 := layoutEnd_first_le h b hb
        omega

end InputBlock

/-! ## Two list facts -/

/-- **The first value of a list is the one element's** whose value is defined, when no other
element's is. -/
theorem findSome?_eq_of_unique {α β : Type} {f : α → Option β} :
    ∀ {l : List α} {b : α}, b ∈ l → (∀ b' ∈ l, f b' ≠ none → b' = b) → l.findSome? f = f b
  | [], _, hb, _ => absurd hb List.not_mem_nil
  | x :: l, b, hb, h => by
    rw [List.findSome?_cons]
    cases hx : f x with
    | some y =>
      have hxb : x = b := h x List.mem_cons_self (by simp [hx])
      subst hxb
      simp [hx]
    | none =>
      by_cases hxb : x = b
      · subst hxb
        rw [hx]
        refine List.findSome?_eq_none_iff.2 fun b' hb' => ?_
        by_contra hne
        exact hne (h b' (List.mem_cons_of_mem _ hb') hne ▸ hx)
      · exact findSome?_eq_of_unique ((List.mem_cons.1 hb).resolve_left (Ne.symm hxb))
          fun b' hb' => h b' (List.mem_cons_of_mem _ hb')

/-! ## Contiguous input layouts -/

namespace InputBlock

theorem layoutEnd_le : ∀ {s e : ℕ} {bs : List InputBlock}, InputBlock.layoutEnd s bs = some e →
    s ≤ e
  | _, _, [], h => by simp only [InputBlock.layoutEnd, Option.some.injEq] at h; omega
  | s, e, b :: bs, h => by
    simp only [InputBlock.layoutEnd] at h
    split_ifs at h
    have := layoutEnd_le h
    omega

/-- **Every block ends by the end of a contiguous layout.** -/
theorem layoutEnd_end_le : ∀ {s e : ℕ} {bs : List InputBlock}, InputBlock.layoutEnd s bs = some e →
    ∀ b ∈ bs, b.first + b.len ≤ e
  | _, _, [], _, _, hb => absurd hb List.not_mem_nil
  | s, e, b' :: bs, h, b, hb => by
    simp only [InputBlock.layoutEnd] at h
    split_ifs at h with hf
    rcases List.mem_cons.1 hb with rfl | hb
    · have := layoutEnd_le h
      omega
    · exact layoutEnd_end_le h b hb

/-- **A contiguous layout covers its inputs**: every input from the start to the end is held by a
block. -/
theorem layoutEnd_cover : ∀ {s e : ℕ} {bs : List InputBlock}, InputBlock.layoutEnd s bs = some e →
    ∀ {q : ℕ}, s ≤ q → q < e → ∃ b ∈ bs, b.Holds q
  | _, _, [], h, _, h1, h2 => by
    simp only [InputBlock.layoutEnd, Option.some.injEq] at h
    omega
  | s, e, b' :: bs, h, q, h1, h2 => by
    simp only [InputBlock.layoutEnd] at h
    split_ifs at h with hf
    by_cases hq : q < s + b'.len
    · exact ⟨b', List.mem_cons_self, by unfold Holds; omega⟩
    · obtain ⟨b, hb, hbq⟩ := layoutEnd_cover h (q := q) (by omega) h2
      exact ⟨b, List.mem_cons_of_mem _ hb, hbq⟩

/-- **In a contiguous layout, one block holds an input.** -/
theorem layoutEnd_unique : ∀ {s e : ℕ} {bs : List InputBlock}, InputBlock.layoutEnd s bs = some e →
    ∀ {q : ℕ} {b b' : InputBlock}, b ∈ bs → b' ∈ bs → b.Holds q → b'.Holds q → b' = b
  | _, _, [], _, _, _, _, hb, _, _, _ => absurd hb List.not_mem_nil
  | s, e, x :: bs, h, q, b, b', hb, hb', hq, hq' => by
    simp only [InputBlock.layoutEnd] at h
    split_ifs at h with hf
    unfold Holds at hq hq'
    rcases List.mem_cons.1 hb with hbx | hbs
    · rcases List.mem_cons.1 hb' with hbx' | hbs'
      · rw [hbx, hbx']
      · subst hbx
        have := layoutEnd_first_le h b' hbs'
        omega
    · rcases List.mem_cons.1 hb' with hbx' | hbs'
      · subst hbx'
        have := layoutEnd_first_le h b hbs
        omega
      · exact layoutEnd_unique h hbs hbs' hq hq'

/-- **The value at an input of a contiguous layout is the holding block's**, for a function of the
blocks defined only at blocks holding the input. -/
theorem findSome?_eq_of_holds {β : Type} {f : InputBlock → Option β} {s e q : ℕ}
    {bs : List InputBlock} (h : InputBlock.layoutEnd s bs = some e) {b : InputBlock} (hb : b ∈ bs)
    (hq : b.Holds q) (hf : ∀ b', f b' ≠ none → b'.Holds q) : bs.findSome? f = f b :=
  findSome?_eq_of_unique hb fun b' hb' hne => layoutEnd_unique h hb hb' hq (hf b' hne)

/-- **The value at an input no block holds** is undefined, for a function of the blocks defined
only at blocks holding the input. -/
theorem findSome?_eq_none_of_end_le {β : Type} {f : InputBlock → Option β} {s e q : ℕ}
    {bs : List InputBlock} (h : InputBlock.layoutEnd s bs = some e) (hq : e ≤ q)
    (hf : ∀ b', f b' ≠ none → b'.Holds q) : bs.findSome? f = none :=
  List.findSome?_eq_none_iff.2 fun b hb => by
    by_contra hne
    have h1 := hf b hne
    have h2 := layoutEnd_end_le h b hb
    unfold Holds at h1
    omega

theorem holds_of_privValue? {K : Type} [Zero K] {cv pv vv : ℕ → ℕ → K} {j : ℕ} {b : InputBlock}
    (h : b.privValue? cv pv vv j ≠ none) : b.Holds j := by
  cases b <;> simp only [privValue?, ne_eq, not_true_eq_false] at h <;>
    split_ifs at h with h' <;> simp_all [Holds, first, len]

end InputBlock

section

section Blocks

variable (ir : RealizedProgram) (I : Interp)

/-- **The inputs of circuit `c` holding batch pads**: the lengths of its batch-pad blocks. -/
def batchPadInputs (c : ℕ) : ℕ :=
  ((ir.circuit c).inputs.map fun b => match b with
    | .batchPads _ _ n => n
    | _ => 0).sum

/-- **The end of circuit `c`'s private block**: the input count less the batch-pad inputs. The C++
allocates a batch's pads as the circuit's last inputs, which no gate reads; the Lean commits them at
full-field cells beside the circuit's input, so the private block ends before them. -/
abbrev privEnd (c : ℕ) : ℕ := (ir.circuit c).inputCount - ir.batchPadInputs c

/-- **The public input of a domain's circuit proof**: the statement and the run, from which the
verifier computes the circuit's public inputs. -/
structure DomainPub where
  /-- The statement. -/
  stmt : ir.Valuation I
  /-- The run. -/
  run : (ir.layout I).Run

end Blocks

/-- A list sum over the first `n` naturals is the sum over `Fin n`. -/
theorem sum_map_range_eq_sum_fin (n : ℕ) (f : ℕ → ℕ) :
    ((List.range n).map f).sum = ∑ j : Fin n, f j := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih, Fin.sum_univ_castSucc]
                 simp

variable {ir : RealizedProgram}

/-- **The committed block holding a committed coordinate.** -/
theorem exists_committed_block {c u i q : ℕ} (hq : (ir.circuit c).committedPos u i = some q) :
    ∃ a n, InputBlock.committed u a n ∈ (ir.circuit c).inputs ∧ i < n ∧ q = a + i := by
  obtain ⟨b, hb, hbq⟩ := List.exists_of_findSome?_eq_some hq
  cases b <;> simp only [InputBlock.committedPos, reduceCtorEq] at hbq
  rename_i u' a n
  split_ifs at hbq with h'
  cases hbq
  obtain ⟨rfl, hi⟩ := h'
  exact ⟨a, n, hb, hi, rfl⟩

/-- **The pad block holding a pad coordinate.** -/
theorem exists_pad_block {c u i q : ℕ} (hq : (ir.circuit c).padPos u i = some q) :
    ∃ a n, InputBlock.pad u a n ∈ (ir.circuit c).inputs ∧ i < n ∧ q = a + i := by
  obtain ⟨b, hb, hbq⟩ := List.exists_of_findSome?_eq_some hq
  cases b <;> simp only [InputBlock.padPos, reduceCtorEq] at hbq
  rename_i u' a n
  split_ifs at hbq with h'
  cases hbq
  obtain ⟨rfl, hi⟩ := h'
  exact ⟨a, n, hb, hi, rfl⟩

/-- **The view block holding a bit view's coordinate.** -/
theorem exists_view_block {c u i q : ℕ} (hq : (ir.circuit c).viewPos u i = some q) :
    ∃ a n, InputBlock.view u a n ∈ (ir.circuit c).inputs ∧ i < n ∧ q = a + i := by
  obtain ⟨b, hb, hbq⟩ := List.exists_of_findSome?_eq_some hq
  cases b <;> simp only [InputBlock.viewPos, reduceCtorEq] at hbq
  rename_i u' a n
  split_ifs at hbq with h'
  cases hbq
  obtain ⟨rfl, hi⟩ := h'
  exact ⟨a, n, hb, hi, rfl⟩

end

end GordieHowe.RealizedProgram
