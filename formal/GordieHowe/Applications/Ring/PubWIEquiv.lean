-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Ring.AnonCoupling

@[expose] public section

/-!
# Witness indistinguishability with public outputs along maps of statements and witnesses

- `WIChoice.map fX fW`: a two-witness choice with its statement mapped by `fX` and both witnesses
  by `fW`; `WIChoice.map_injective`: injective for injective maps.
- `pubRun_comap`: the rounds of the proof law read through maps `fX`, `fW` with a selector `sel`
  are the rounds of the proof law with the selector mapped through `fX`, `fW`.
- `PubWI.comap`: witness indistinguishability with public outputs transported along equivalences
  of statements and witnesses.
- `pubRun_congr_roundLaw`: two selectors whose rounds have the same law give the same rounds.
- `PubWI.of_witness_indep`: a proof law not depending on the witness has witness
  indistinguishability with public outputs at error `0`.
-/

namespace GordieHowe.SPBCS.WIChoice

variable {X X' W W' : Type}

/-- A two-witness choice with its statement mapped by `fX` and both witnesses by `fW`. -/
def map (fX : X' → X) (fW : W' → W) (c : WIChoice X' W') : WIChoice X W :=
  ⟨fX c.stmt, fW c.wit₀, fW c.wit₁⟩

/-- **Mapping choices along injective maps is injective.** -/
theorem map_injective {fX : X' → X} {fW : W' → W} (hX : Function.Injective fX)
    (hW : Function.Injective fW) : Function.Injective (map fX fW) := by
  rintro ⟨a, b, c⟩ ⟨a', b', c'⟩ h
  simp only [map, mk.injEq] at h
  rw [hX h.1, hW h.2.1, hW h.2.2]

end GordieHowe.SPBCS.WIChoice

namespace GordieHowe.Ring

open GordieHowe.SPBCS

section Comap

variable {Ω X X' W W' Pub Pf : Type} [Fintype Ω] [Nonempty Ω]

/-- **Rounds of a proof law read through maps**: the rounds of `law` at the mapped statement and
witness with the selector `sel` are the rounds of `law` with `sel` mapped through `fX`, `fW`. -/
theorem pubRun_comap (law : Ω → X → W → PMF Pf) (pubOf : X → Pub) (fX : X' → X) (fW : W' → W)
    {Q : ℕ} (sel : Selector Ω X' W' Pub Pf Q) :
    ∀ j (hj : j ≤ Q), pubRun (fun ω x w => law ω (fX x) (fW w)) (pubOf ∘ fX) sel j hj =
      pubRun law pubOf (fun i h hist => (sel i h hist).map (Prod.map fX fW)) j hj
  | 0, _ => rfl
  | j + 1, hj => by
    rw [pubRun, pubRun, pubRun_comap law pubOf fX fW sel j (by omega)]
    congr 1
    funext s
    simp only [pubStep]
    congr 1
    rcases sel ⟨j, by omega⟩ s.1 s.2 with _ | xw <;> rfl

/-- **Witness indistinguishability along equivalences**: `PubWI` for `rel` transports to the proof
law, public values and relation read through equivalences `eS` of statements and `eW` of
witnesses, at the same error. -/
theorem PubWI.comap {law : Ω → X → W → PMF Pf} {pubOf : X → Pub} {rel : Set (X × W)}
    {wi : ℕ → ℝ} (h : PubWI law pubOf rel wi) (eS : X' ≃ X) (eW : W' ≃ W) :
    PubWI (fun ω x w => law ω (eS x) (eW w)) (pubOf ∘ eS) {p | (eS p.1, eW p.2) ∈ rel} wi := by
  intro Q c F S hS hrel hF U
  have hinj := SPBCS.WIChoice.map_injective eS.injective eW.injective
  have hsel : ∀ bs : ℕ → Bool,
      (fun i h hist => (wiSelector F bs i h hist).map (Prod.map eS eW)) =
        wiSelector (fun j h hist => (F j h hist).map (SPBCS.WIChoice.map eS eW)) bs := by
    intro bs
    funext i h hist
    simp only [wiSelector, Option.map_map]
    congr 1
    funext x
    cases bs i <;> rfl
  rw [pubRun_comap, pubRun_comap, hsel, hsel]
  refine h Q c _ (S.map ⟨_, hinj⟩) (by rwa [Finset.card_map]) ?_ ?_ U
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_map.1 hx
    exact hrel y hy
  · intro j h' hist x hx
    obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.1 hx
    exact Finset.mem_map_of_mem _ (hF j h' hist y hy)

/-- **Selectors with the same round laws give the same rounds**: if in every round, oracle and
history the two selections give the same `roundLaw`, the experiments agree after `j` rounds. -/
theorem pubRun_congr_roundLaw {law : Ω → X → W → PMF Pf} {pubOf : X → Pub} {Q : ℕ}
    {sel sel' : Selector Ω X W Pub Pf Q}
    (hsel : ∀ i h hist,
      roundLaw law pubOf h (sel i h hist) = roundLaw law pubOf h (sel' i h hist)) :
    ∀ j (hj : j ≤ Q), pubRun law pubOf sel j hj = pubRun law pubOf sel' j hj
  | 0, _ => rfl
  | j + 1, hj => by
    rw [pubRun, pubRun, pubRun_congr_roundLaw hsel j (by omega)]
    congr 1
    funext s
    rw [pubStep, pubStep, hsel]

/-- **A witness-independent proof law is perfectly witness indistinguishable**: if `law ω x w`
does not depend on `w`, then `PubWI law pubOf rel` holds at error `0`. -/
theorem PubWI.of_witness_indep {law : Ω → X → W → PMF Pf} (pubOf : X → Pub) (rel : Set (X × W))
    (hlaw : ∀ ω x w w', law ω x w = law ω x w') : PubWI law pubOf rel fun _ => 0 := by
  intro Q c F S _ _ _ U
  rw [pubRun_congr_roundLaw (sel' := wiSelector F fun _ => true) ?_ Q le_rfl]
  · simp [gameAdvantage, advantage]
  · intro i h hist
    simp only [wiSelector]
    rcases F i h hist with _ | x
    · rfl
    · simp only [Option.map_some, roundLaw, Bool.false_eq_true, ite_false, ite_true]
      rw [hlaw h x.stmt x.wit₀ x.wit₁]

end Comap

end GordieHowe.Ring
