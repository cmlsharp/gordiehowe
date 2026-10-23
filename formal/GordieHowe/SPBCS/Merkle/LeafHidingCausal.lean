-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.SPBCS.Merkle.LeafHiding
public import GordieHowe.Foundations.ToMathlib.PMFTVCausal

@[expose] public section

/-!
# Leaf equivocation for leaves committed in order

A leaf `i` of rank `rank i` has the content `col d i`, which may depend on the digests of the
leaves of lower rank (`PMF.RankCausal`), as when a prover message with a tree is computed from
challenges derived from the roots of earlier trees. The honest digests `D ν` are then the
solution of `D ν i = H (e (col (D ν) i) (ν i))`, unique by induction on the rank
(`eq_of_leafDigests_eq`).

`tvDist_leafPairs_causal_le` is leaf equivocation (`leaf_equivocation`) for such contents, at a
fixed function `H`: the law of the Merkle salts and the honest digests (uniform Merkle salts) is within `|ι| · B` of the law of uniform
digests `d` with each Merkle salt drawn from the preimage of `d i` at the content `col d i`
(`invert`), when every content's digest law is within `B` of uniform. The proof:

- given the digests `d`, the contents are fixed, so `invert` is the conditional law of the Merkle
  salts given `D ν = d` (`isDisintegration_leafDigests`, from `isDisintegration_invert`
  coordinatewise), and both laws apply the same kernel to the digests;
- the law of `D ν` has mass `∏ i, digestLaw H (e (col d i)) (d i)` at `d`
  (`map_leafDigests_apply`), a causal product, so its distance from uniform is at most
  `|ι| · B` (`PMF.tvDist_le_of_rankCausal`, the hybrid over the leaves in order of rank).
-/

open Finset PMF

namespace GordieHowe.SPBCS

variable {X Y N C ι : Type*} [Fintype Y] [DecidableEq Y] [Nonempty Y] [Fintype N] [Nonempty N]
  [Fintype ι] [DecidableEq ι]

variable (H : X → Y) (e : C → N → X) (rank : ι → ℕ) {col : (ι → Y) → ι → C}
  {D : (ι → N) → ι → Y}

omit [Fintype Y] [DecidableEq Y] [Nonempty Y] [Fintype N] [Nonempty N] [Fintype ι]
  [DecidableEq ι] in
/-- **The honest digests are the unique solution**: digests `d` with `d i` the digest of the Merkle
salt `ν i` at the content `col d i`, for every `i`, are the honest digests `D ν`. -/
theorem eq_of_leafDigests_eq (hcol : RankCausal rank col)
    (hD : ∀ ν i, D ν i = H (e (col (D ν) i) (ν i))) {ν : ι → N} {d : ι → Y}
    (hd : ∀ i, d i = H (e (col d i) (ν i))) : d = D ν := by
  suffices h : ∀ m i, rank i < m → d i = D ν i from funext fun i => h _ i (Nat.lt_succ_self _)
  intro m
  induction m with
  | zero => exact fun i hi => absurd hi (Nat.not_lt_zero _)
  | succ m ih =>
    intro i hi
    rw [hd i, hD ν i, hcol i fun j hj => ih j (by omega)]

omit [Fintype Y] [DecidableEq Y] [Nonempty Y] in
/-- The law of the honest digests at `d` is the law, at `d`, of the digests at the fixed contents
`col d`. -/
theorem map_leafDigests_apply_eq (hcol : RankCausal rank col)
    (hD : ∀ ν i, D ν i = H (e (col (D ν) i) (ν i))) (d : ι → Y) :
    (uniformOfFintype (ι → N)).map D d =
      (uniformOfFintype (ι → N)).map (fun ν i => H (e (col d i) (ν i))) d := by
  have hiff : ∀ ν, d = D ν ↔ d = fun i => H (e (col d i) (ν i)) := fun ν => by
    constructor
    · rintro rfl
      exact funext fun i => hD ν i
    · exact fun h => eq_of_leafDigests_eq H e rank hcol hD fun i => congrFun h i
  simp only [map_apply]
  refine tsum_congr fun ν => ?_
  by_cases h : d = D ν
  · rw [ite_eq_left h, ite_eq_left ((hiff ν).1 h)]
  · rw [ite_eq_right h, ite_eq_right fun h' => h ((hiff ν).2 h')]

omit [DecidableEq Y] [Nonempty Y] in
/-- **The law of the honest digests** has mass `∏ i, digestLaw H (e (col d i)) (d i)` at `d`. -/
theorem map_leafDigests_apply (hcol : RankCausal rank col)
    (hD : ∀ ν i, D ν i = H (e (col (D ν) i) (ν i))) (d : ι → Y) :
    (uniformOfFintype (ι → N)).map D d = ∏ i, digestLaw H (e (col d i)) (d i) := by
  rw [map_leafDigests_apply_eq H e rank hcol hD, ← pi_uniformOfFintype]
  exact congrFun (congrArg DFunLike.coe (pi_map (fun _ => uniformOfFintype N)
    fun i => H ∘ e (col d i))) d

omit [Nonempty Y] in
/-- **Given the digests, the Merkle salts are drawn from the preimages**: `invert` at the contents
`col d` is a disintegration of the uniform Merkle salts along the honest digests. -/
theorem isDisintegration_leafDigests (hcol : RankCausal rank col)
    (hD : ∀ ν i, D ν i = H (e (col (D ν) i) (ν i))) :
    (uniformOfFintype (ι → N)).IsDisintegration D
      fun d => PMF.pi fun i => invert H (e (col d i)) (d i) := by
  intro b ν
  have hk := IsDisintegration.pi (p := fun _ => uniformOfFintype N)
    (φ := fun i => H ∘ e (col b i)) (k := fun i => invert H (e (col b i)))
    (fun i => isDisintegration_invert H (e (col b i))) b ν
  rw [pi_uniformOfFintype] at hk
  have hiff : D ν = b ↔ (fun i => H (e (col b i) (ν i))) = b := by
    constructor
    · rintro rfl
      exact funext fun i => (hD ν i).symm
    · exact fun h => (eq_of_leafDigests_eq H e rank hcol hD fun i => (congrFun h i).symm).symm
  rw [map_leafDigests_apply_eq H e rank hcol hD, if_congr hiff rfl rfl]
  exact hk

/-- **Leaf equivocation for leaves committed in order**, at a fixed function `H`: for contents
`col d i` that read only the digests of leaves of lower rank, the law of the Merkle salts and the
honest digests `D ν` (uniform Merkle salts) is within `|ι| · B` of the law of uniform digests `d`
with Merkle salts drawn from the preimages at the contents `col d` (`invert`), when every content's
digest law is within `B` of uniform. -/
theorem tvDist_leafPairs_causal_le (hcol : RankCausal rank col)
    (hD : ∀ ν i, D ν i = H (e (col (D ν) i) (ν i))) {B : ℝ}
    (hB : ∀ c, tvDist (digestLaw H (e c)) (uniformOfFintype Y) ≤ B) :
    tvDist ((uniformOfFintype (ι → N)).map fun ν => (ν, D ν))
        ((uniformOfFintype (ι → Y)).bind fun d =>
          (PMF.pi fun i => invert H (e (col d i)) (d i)).map fun ν => (ν, d)) ≤
      Fintype.card ι * B :=
  ((isDisintegration_leafDigests H e rank hcol hD).tvDist_le _).trans
    (tvDist_le_of_rankCausal rank (fun d i => digestLaw H (e (col d i)))
      (fun _ _ => uniformOfFintype Y) (fun _ _ i hd => by simp only [hcol i hd])
      (fun _ _ _ _ => rfl) (map_leafDigests_apply H e rank hcol hD)
      (fun d => by rw [← pi_uniformOfFintype, pi_apply]) fun _ _ => hB _)

end GordieHowe.SPBCS
