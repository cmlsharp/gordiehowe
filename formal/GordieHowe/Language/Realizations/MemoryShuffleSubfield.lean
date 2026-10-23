-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.Realizations.MemoryShuffle
public import GordieHowe.Language.Realizations.Bits
public import GordieHowe.Foundations.ToMathlib.FinFlatten
public import Mathlib.Algebra.Field.Subfield.Basic

@[expose] public section

/-!
# The honest memory shuffle is subfield-valued

The honest simulation `memoryTrace` writes signed units `1 + (θ + 1)·s` with `s ∈ {0, 1}` and
copies of cells, so its read values and final cells lie in every subfield holding `θ`
(`memoryTrace_mem`). The committed values of the honest wire witness `honestWit` then lie in
such a subfield when it also contains the selection subfield: the read values and final cells,
the origin bits (constant bits), and the final origins `F.embed o`, which lie in `F.E`. In the
C++ the cells take values in `{0, 1, θ}`, `θ` the order-3 element of `GF(4) ⊂ GF(2^16)`
(`lib/gordiehowe/examples/mldsa/sample_in_ball.h` and `sample_in_ball.h:297-316`), and the final
origins are field embeddings of the origins, which is `F.embed` at the flagship basis `e i = g^i`
(`gf2_128SelectionField`).
-/

namespace GordieHowe.MemoryShuffle

variable {K : Type*} [Field K] {N τ : ℕ}

/-- The signed unit of a sign in a subfield holding `θ` lies in it. -/
theorem unit_mem (Θ : Theta K) {E : Subfield K} (hθ : Θ.θ ∈ E) {sign : K} (hs : sign ∈ E) :
    unit Θ sign ∈ E :=
  E.add_mem E.one_mem (E.mul_mem (E.add_mem hθ E.one_mem) hs)

/-- The cells and read values of the honest simulation, from any starting state and over any
prefix of steps, stay in a subfield `E` holding `θ` when the starting cells and advice do: a
step writes a copy of a cell and a signed unit. -/
theorem foldl_mem_aux (Θ : Theta K) {E : Subfield K} (hθ : Θ.θ ∈ E)
    (positions : Fin τ → ℕ) (signs : Fin τ → Bool) (l : List (Fin τ))
    (cell0 : Fin N → K) (origin0 : Fin N → ℕ) (adv0 : List (K × ℕ))
    (hc : ∀ a, cell0 a ∈ E) (ha : ∀ x ∈ adv0, x.1 ∈ E) :
    let st := l.foldl
        (fun (st : (Fin N → K) × (Fin N → ℕ) × List (K × ℕ)) (s : Fin τ) =>
          let (cell, origin, adv) := st
          if hi : N - τ + (s : ℕ) < N then
            let i : Fin N := ⟨N - τ + s, hi⟩
            if hj : positions s < N then
              let j : Fin N := ⟨positions s, hj⟩
              let adv' := adv ++ [⟨cell j, origin j⟩]
              let cell' :=
                Function.update (Function.update cell i (cell j)) j (unit Θ (if signs s then 1 else 0))
              let origin' := Function.update (Function.update origin i (origin j)) j ((s : ℕ) + 1)
              (cell', origin', adv')
            else st
          else st)
        (cell0, origin0, adv0)
    (∀ a, st.1 a ∈ E) ∧ ∀ x ∈ st.2.2, x.1 ∈ E := by
  induction l generalizing cell0 origin0 adv0 with
  | nil => exact ⟨hc, ha⟩
  | cons s l ih =>
    simp only [List.foldl_cons]
    by_cases hi : N - τ + (s : ℕ) < N
    · by_cases hj : positions s < N
      · simp only [hi, hj, ↓reduceDIte]
        refine ih _ _ _ (fun a => ?_) (fun x hx => ?_)
        · rcases eq_or_ne a ⟨positions s, hj⟩ with rfl | hne
          · rw [Function.update_self]
            exact unit_mem Θ hθ (by split_ifs <;> first | exact E.one_mem | exact E.zero_mem)
          · rw [Function.update_of_ne hne]
            rcases eq_or_ne a ⟨N - τ + s, hi⟩ with rfl | hne'
            · rw [Function.update_self]; exact hc _
            · rw [Function.update_of_ne hne']; exact hc a
        · rcases List.mem_append.mp hx with hx | hx
          · exact ha x hx
          · rw [List.mem_singleton.mp hx]; exact hc _
      · simp only [hi, hj, ↓reduceDIte]
        exact ih _ _ _ hc ha
    · simp only [hi, ↓reduceDIte]
      exact ih _ _ _ hc ha

/-- **The honest memory trace lies in a subfield `E` holding `θ`**: every read value and
every final cell is `0`, `1` or `θ` built from them (`sample_in_ball.h:297-316`). -/
theorem memoryTrace_mem (Θ : Theta K) {E : Subfield K} (hθ : Θ.θ ∈ E)
    (positions : Fin τ → ℕ) (signs : Fin τ → Bool) :
    (∀ s, ((memoryTrace (N := N) Θ positions signs).1 s).1 ∈ E) ∧
      ∀ a, (memoryTrace (N := N) Θ positions signs).2.1 a ∈ E := by
  obtain ⟨hc, ha⟩ := foldl_mem_aux (N := N) Θ hθ positions signs (List.finRange τ) (fun _ => 0)
    (fun _ => 0) [] (fun _ => E.zero_mem) (fun _ h => absurd h (List.not_mem_nil))
  refine ⟨fun s => ?_, hc⟩
  have key : ∀ (l : List (K × ℕ)), (∀ x ∈ l, x.1 ∈ E) → ∀ s : ℕ, (l.getD s ⟨0, 0⟩).1 ∈ E := by
    intro l hl s
    rw [List.getD_eq_getElem?_getD]
    cases h : l[s]? with
    | none => exact E.zero_mem
    | some x => exact hl x (List.mem_of_getElem? h)
  exact key _ ha s
variable [DecidableEq K] {S : ℕ} (F : SelectionField K S) (Θ : Theta K)
  (positions : Fin τ → ℕ) (signs : Fin τ → Bool) {E : Subfield K}

omit [DecidableEq K] in
/-- The honest read values lie in a subfield holding `θ`. -/
theorem honestWit_read_value_mem (hθ : Θ.θ ∈ E) (s : Fin τ) :
    ((honestWit (N := N) F Θ positions signs).read s).value ∈ E :=
  (memoryTrace_mem Θ hθ positions signs).1 s

omit [DecidableEq K] in
/-- The honest final cells lie in a subfield holding `θ`. -/
theorem honestWit_cEnc_mem (hθ : Θ.θ ∈ E) (a : Fin N) :
    (honestWit (N := N) F Θ positions signs).cEnc a ∈ E :=
  (memoryTrace_mem Θ hθ positions signs).2 a

omit [DecidableEq K] in
/-- The honest final origins lie in the selection subfield. -/
theorem honestWit_finalOrigin_mem (a : Fin N) :
    (honestWit (N := N) F Θ positions signs).finalOrigin a ∈ F.E :=
  F.embed_mem _

end GordieHowe.MemoryShuffle
