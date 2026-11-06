-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Foundations.ToMathlib.ListFilter

@[expose] public section

/-!
# The first accepted entries of a stream

`firstAccepted accept stream n`: the first `n` entries of `stream` that `accept` accepts, in
order, or `none` when fewer exist. Every ordered-selection gadget is proved against it.
-/

namespace GordieHowe

/-- The first `n` entries of `stream` satisfying `accept`, in order, or `none` if fewer than `n`
exist. Every ordered-selection gadget is proved against this. -/
def firstAccepted (accept : ℕ → Bool) {S : ℕ} (stream : Fin S → ℕ) (n : ℕ) : Option (Fin n → ℕ) :=
  let acc := (List.ofFn stream).filter accept
  if h : n ≤ acc.length then
    some fun i => acc[i]'(by have := i.isLt; omega)
  else none

/-- `firstAccepted` unfolded: it succeeds exactly when at least `n` entries of
`stream` are accepted, and then `out` is the entrywise readout of the filtered
list. -/
theorem firstAccepted_eq_some_iff {accept : ℕ → Bool} {S : ℕ} {stream : Fin S → ℕ} {n : ℕ}
    {out : Fin n → ℕ} :
    firstAccepted accept stream n = some out ↔
      ∃ h : n ≤ ((List.ofFn stream).filter accept).length,
        ∀ i : Fin n, out i = ((List.ofFn stream).filter accept)[i]'(by have := i.isLt; omega) := by
  unfold firstAccepted
  dsimp only
  by_cases h : n ≤ ((List.ofFn stream).filter accept).length
  · rw [dite_eq_left h]
    constructor
    · intro heq
      refine ⟨h, fun i => ?_⟩
      have := congrFun (Option.some.inj heq) i
      exact this.symm
    · rintro ⟨h', hout⟩
      congr 1
      funext i
      exact (hout i).symm
  · rw [dite_eq_right h]
    constructor
    · exact fun heq => absurd heq (by simp)
    · rintro ⟨h', -⟩
      exact absurd h' h

theorem firstAccepted_accept {accept : ℕ → Bool} {S n : ℕ} {stream : Fin S → ℕ}
    {out : Fin n → ℕ} (h : firstAccepted accept stream n = some out) (i : Fin n) :
    accept (out i) = true := by
  obtain ⟨hlen, hout⟩ := firstAccepted_eq_some_iff.mp h
  rw [hout i]
  exact (List.mem_filter.mp (List.getElem_mem (by omega))).2

/-- `firstAccepted` fails exactly when fewer than `n` entries of `stream` are
accepted. -/
theorem firstAccepted_eq_none_iff {accept : ℕ → Bool} {S : ℕ} {stream : Fin S → ℕ} {n : ℕ} :
    firstAccepted accept stream n = none ↔
      ((List.ofFn stream).filter accept).length < n := by
  unfold firstAccepted
  by_cases h : n ≤ ((List.ofFn stream).filter accept).length
  · rw [dif_pos h]
    simp only [reduceCtorEq, false_iff]
    omega
  · rw [dif_neg h]
    simp only [true_iff]
    omega

end GordieHowe
