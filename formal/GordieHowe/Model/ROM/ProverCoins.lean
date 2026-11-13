-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.ROM.NIZK

public section

/-!
# The tape of the prover's coins

The real environment of `GordieHowe/Model/ROM/NIZK.lean` draws the oracle and independent coins
for each proof query (`tapeDist`). Two facts about that tape:

* `tapeDist_map`: the tape of pushed-forward coins is the pushed-forward tape.
* `tvDist_tapeDist_le`: the tapes of coin laws `ν` and `ν'` with `Q` proof queries are within
  `Q · tvDist ν ν'` in total variation.
-/

open Finset
open scoped BigOperators ENNReal

namespace GordieHowe.ROM.NIZK

open GordieHowe.Quantum GordieHowe.QROM

variable {X Y Stmt Wit Proof : Type} [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y]
  (rel : Stmt → Wit → Prop) [DecidableRel rel] {Coins Coins' : Type} [Fintype Coins]
  [Fintype Coins']

/-- The tape of pushed-forward coins is the pushed-forward tape. -/
theorem tapeDist_map {Q : ℕ} (μ : PMF Coins) (f : Coins → Coins') :
    tapeDist (X := X) (Y := Y) Q (μ.map f) =
      (tapeDist Q μ).map fun ω => (ω.1, fun i => f (ω.2 i)) := by
  rw [tapeDist, tapeDist, PMF.map_bind]
  congr 1
  funext H
  rw [← PMF.pi_map, PMF.map_comp, PMF.map_comp]
  rfl

/-- The tapes of two coin laws are within `Q` times the distance of the laws. -/
theorem tvDist_tapeDist_le {Q : ℕ} (ν ν' : PMF Coins) :
    PMF.tvDist (tapeDist (X := X) (Y := Y) Q ν) (tapeDist Q ν') ≤ Q * PMF.tvDist ν ν' := by
  rw [tapeDist, tapeDist]
  refine (PMF.tvDist_bind_left_le' _ _ _).trans ?_
  have hk : ∀ H : X → Y, PMF.tvDist ((PMF.pi fun _ : Fin Q => ν).map fun c => (H, c))
      ((PMF.pi fun _ : Fin Q => ν').map fun c => (H, c)) ≤ Q * PMF.tvDist ν ν' := fun H =>
    (PMF.tvDist_map_le _ _ _).trans ((PMF.tvDist_pi_le _ _).trans_eq (by simp))
  calc ∑' H, ((PMF.uniformOfFintype (X → Y)) H).toReal *
        PMF.tvDist ((PMF.pi fun _ : Fin Q => ν).map fun c => (H, c))
          ((PMF.pi fun _ : Fin Q => ν').map fun c => (H, c))
      ≤ ∑' H, ((PMF.uniformOfFintype (X → Y)) H).toReal * (Q * PMF.tvDist ν ν') := by
        rw [tsum_fintype, tsum_fintype]
        exact sum_le_sum fun H _ => mul_le_mul_of_nonneg_left (hk H) ENNReal.toReal_nonneg
    _ = Q * PMF.tvDist ν ν' := by
        rw [tsum_fintype, ← sum_mul, PMF.sum_toReal, one_mul]

end GordieHowe.ROM.NIZK
