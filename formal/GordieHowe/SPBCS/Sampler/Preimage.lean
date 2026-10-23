-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.SPBCS.Extraction.Transcript
public import GordieHowe.Foundations.Probability.IdentDistrib

@[expose] public section

/-!
# Preimage samplers

A **preimage sampler** of a challenge sampler `S` (`Sampler.Preimage S`): from a challenge `c` and
uniform coins, a stream on which `S` returns `c`, uniform on the fibre of `c` (every stream of the
fibre is hit by the same number of coins). The zero-knowledge simulator for a simulator of the IOP
that chooses its own challenges (CY24 Definition 23.1.8, `GordieHowe.IOP.IOP.HVZK`) programs each
challenge round's oracle answer with a preimage of the simulated challenge
(`GordieHowe/SPBCS/FullPast/ZeroKnowledge.lean`).

**The law of the preimages of uniform challenges** (`Sampler.tvDist_preLaw_le`): the streams drawn
by preimage at uniform challenges are within the probability that some round rejects of uniform
streams. On a stream every round accepts, the preimage law is at least uniform, since each fibre has
at most `|stream| / |C|` streams (the fibres are disjoint and of one size); it puts no mass on the
other streams.
-/

namespace PMF

/-- **Two laws with `p ≤ q` outside an event** are at total variation distance at most the
probability of the event under `p`. -/
theorem tvDist_le_of_le_of_notMem {α : Type*} (p q : PMF α) (s : Set α)
    (h : ∀ a ∉ s, p a ≤ q a) : tvDist p q ≤ (p.toOuterMeasure s).toReal := by
  rw [tvDist_eq_toReal_tsum_tsub]
  refine ENNReal.toReal_mono
    (ne_top_of_le_ne_top ENNReal.one_ne_top (toOuterMeasure_apply_le_one p s)) ?_
  rw [toOuterMeasure_apply]
  refine ENNReal.tsum_le_tsum fun a => ?_
  by_cases ha : a ∈ s
  · simp only [Set.indicator_of_mem ha]
    exact tsub_le_self
  · simp [Set.indicator_of_notMem ha, tsub_eq_zero_of_le (h a ha)]

end PMF

/-- **Counting a coordinatewise property of a tuple**: the tuples whose every coordinate satisfies
its property are the product of the coordinate counts. -/
theorem Finset.card_filter_forall_pi {ι : Type*} [Fintype ι] [DecidableEq ι] {R : ι → Type*}
    [∀ i, Fintype (R i)] (P : ∀ i, R i → Prop) [∀ i, DecidablePred (P i)] :
    (Finset.univ.filter fun r : (∀ i, R i) => ∀ i, P i (r i)).card =
      ∏ i, (Finset.univ.filter (P i)).card := by
  rw [← Fintype.card_piFinset]
  congr 1
  ext r
  simp [Fintype.mem_piFinset]

namespace GordieHowe.SPBCS
open GordieHowe.QROM GordieHowe.IOP
open scoped ENNReal

variable {k e : ℕ} {C : Type} [Fintype C] [DecidableEq C]

/-- **A preimage sampler** of the challenge sampler `S` (module docstring): from a challenge and
uniform coins, a stream. When the fibre of the challenge is nonempty the stream lies in it
(`sample_pre`) and every stream of the fibre is hit by the same number of coins (`card_eq`), so the
stream is uniform on the fibre. Every value of this type is computable; its cost is stated where it
is constructed. -/
structure Sampler.Preimage (S : Sampler k e C) where
  /-- The coins. -/
  Coins : Type
  [fintype : Fintype Coins]
  [nonempty : Nonempty Coins]
  /-- The stream drawn for a challenge at the coins. -/
  pre : C → Coins → Fin (k + e) → Byte
  /-- When the fibre of `c` is nonempty, the drawn stream samples `c`. -/
  sample_pre : ∀ c r s, S.sample s = some c → S.sample (pre c r) = some c
  /-- Every stream of the fibre of `c` is drawn by the same number of coins. -/
  card_eq : ∀ c s s', S.sample s = some c → S.sample s' = some c →
    (Finset.univ.filter fun r => pre c r = s).card = (Finset.univ.filter fun r => pre c r = s').card

attribute [instance] Sampler.Preimage.fintype Sampler.Preimage.nonempty

namespace Sampler

/-- The fibres of a sampler fill at most the streams: `|C| · |fibre| ≤ |stream|`. -/
theorem card_mul_card_fibre_le (S : Sampler k e C) (c : C) :
    Fintype.card C * (Finset.univ.filter fun s => S.sample s = some c).card ≤
      Fintype.card (Fin (k + e) → Byte) := by
  calc Fintype.card C * (Finset.univ.filter fun s => S.sample s = some c).card
      = ∑ c' : C, (Finset.univ.filter fun s => S.sample s = some c').card := by
        rw [Finset.sum_congr rfl fun c' _ => S.card_eq c' c, Finset.sum_const, Finset.card_univ,
          smul_eq_mul]
    _ = ((Finset.univ : Finset C).biUnion fun c' =>
          Finset.univ.filter fun s => S.sample s = some c').card := by
        refine (Finset.card_biUnion fun a _ b _ hab => ?_).symm
        refine Finset.disjoint_left.2 fun y ha hb => hab ?_
        simp only [Finset.mem_filter] at ha hb
        exact Option.some_inj.1 (ha.2.symm.trans hb.2)
    _ ≤ _ := Finset.card_le_univ _

/-- **A stream of the fibre of `c` is drawn by at least its uniform share of the coins**:
`|C| · |coins| ≤ #{r | pre c r = s} · |stream|`. -/
theorem Preimage.card_mul_le {S : Sampler k e C} (T : S.Preimage) {c : C}
    {s : Fin (k + e) → Byte} (hs : S.sample s = some c) :
    Fintype.card C * Fintype.card T.Coins ≤
      (Finset.univ.filter fun r => T.pre c r = s).card * Fintype.card (Fin (k + e) → Byte) := by
  set F := Finset.univ.filter fun s' => S.sample s' = some c
  set m := (Finset.univ.filter fun r => T.pre c r = s).card
  have hcoins : Fintype.card T.Coins = F.card * m := by
    rw [← Finset.card_univ, Finset.card_eq_sum_card_fiberwise (f := T.pre c) (t := F)
      fun r _ => by simp [F, T.sample_pre c r s hs]]
    rw [Finset.sum_congr rfl fun s' hs' => T.card_eq c s' s (by simpa [F] using hs') hs,
      Finset.sum_const, smul_eq_mul]
  rw [hcoins, ← mul_assoc, mul_comm m]
  exact Nat.mul_le_mul_right _ (S.card_mul_card_fibre_le c)

variable {ι : Type} [Fintype ι] [DecidableEq ι] {Cs : ι → Type} [∀ i, Fintype (Cs i)]
  [∀ i, DecidableEq (Cs i)] [∀ i, Nonempty (Cs i)] {S : ∀ i, Sampler k e (Cs i)}

/-- **The streams drawn by preimage** at the challenges `ch` and the coins `r`, as oracle
answers. -/
def preStreams (T : ∀ i, (S i).Preimage) (ch : ∀ i, Cs i) (r : ∀ i, (T i).Coins) : ι → Out k e :=
  fun i => Out.streamEquiv.symm ((T i).pre (ch i) (r i))

/-- The law of the streams drawn by preimage at the challenges `ch`. -/
noncomputable def preLaw (T : ∀ i, (S i).Preimage) (ch : ∀ i, Cs i) : PMF (ι → Out k e) :=
  (PMF.uniformOfFintype (∀ i, (T i).Coins)).map (preStreams T ch)

omit [Fintype ι] [DecidableEq ι] [∀ i, Nonempty (Cs i)] in
/-- **Preimage streams sample their challenges** when every round's fibres are nonempty. -/
theorem sample_preStreams (T : ∀ i, (S i).Preimage)
    (hne : ∀ i, ∃ s, ((S i).sample s).isSome) (ch : ∀ i, Cs i) (r : ∀ i, (T i).Coins) (i : ι) :
    (S i).sample (preStreams T ch r i).stream = some (ch i) := by
  obtain ⟨s, hs⟩ := hne i
  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.1 hs
  have hcard := (S i).card_eq (ch i) c
  have hpos : 0 < (Finset.univ.filter fun s => (S i).sample s = some c).card :=
    Finset.card_pos.2 ⟨s, by simp [hc]⟩
  obtain ⟨s', hs'⟩ := Finset.card_pos.1 (hcard ▸ hpos)
  have hst : (preStreams T ch r i).stream = (T i).pre (ch i) (r i) :=
    Out.streamEquiv.apply_symm_apply _
  rw [hst]
  exact (T i).sample_pre (ch i) (r i) s' (by simpa using hs')

open Classical in
/-- **The preimages of uniform challenges are close to uniform streams**: within the probability
that some round rejects a uniform stream (module docstring). -/
theorem tvDist_preLaw_le (T : ∀ i, (S i).Preimage) :
    PMF.tvDist (PMF.uniformOfFintype (ι → Out k e))
        ((PMF.uniformOfFintype (∀ i, Cs i)).bind (preLaw T)) ≤
      (Pr[g ← (ι → Out k e) : ∃ i, (S i).sample (g i).stream = none]).toReal := by
  refine PMF.tvDist_le_of_le_of_notMem _ _ {g : ι → Out k e | ∃ i, (S i).sample (g i).stream = none} ?_
  intro g hg
  simp only [Set.mem_ofPred_eq, not_exists] at hg
  have hsome : ∀ i, ((S i).sample (g i).stream).isSome := fun i =>
    Option.isSome_iff_ne_none.2 (hg i)
  let c : ∀ i, Cs i := fun i => ((S i).sample (g i).stream).get (hsome i)
  have hc : ∀ i, (S i).sample (g i).stream = some (c i) := fun i => by simp [c]
  -- the bind as one uniform draw of challenges and coins
  have hbind : (PMF.uniformOfFintype (∀ i, Cs i)).bind (preLaw T) =
      (PMF.uniformOfFintype ((∀ i, Cs i) × ∀ i, (T i).Coins)).map
        fun p => preStreams T p.1 p.2 := by
    rw [PMF.uniformOfFintype_prod_eq_bind, PMF.map_bind]
    congr 1
    funext ch
    rw [PMF.map_comp]
    rfl
  rw [hbind, PMF.uniformOfFintype_apply, GordieHowe.IOP.map_uniformOfFintype_apply]
  -- counting: the pairs `(c, r)` with `r` drawing `g` at `c`
  set A := Finset.univ.filter fun r : (∀ i, (T i).Coins) =>
    ∀ i, (T i).pre (c i) (r i) = (g i).stream
  have hA : A.card = ∏ i, (Finset.univ.filter fun r => (T i).pre (c i) r = (g i).stream).card :=
    Finset.card_filter_forall_pi (fun i r => (T i).pre (c i) r = (g i).stream)
  have hle : A.card ≤ GordieHowe.IOP.fiber (fun p : (∀ i, Cs i) × ∀ i, (T i).Coins =>
      preStreams T p.1 p.2) g := by
    refine Finset.card_le_card_of_injOn (fun r => (c, r)) (fun r hr => ?_) (fun _ _ _ _ h => ?_)
    · simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq, A] at hr
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq]
      funext i
      simp only [preStreams, hr i]
      exact Out.streamEquiv.symm_apply_apply (g i)
    · exact (Prod.mk.inj h).2
  have hnat : Fintype.card ((∀ i, Cs i) × ∀ i, (T i).Coins) ≤
      A.card * Fintype.card (ι → Out k e) := by
    rw [Fintype.card_prod, Fintype.card_pi, Fintype.card_pi, hA, Fintype.card_fun, card_out,
      ← Finset.prod_mul_distrib, ← Finset.card_univ (α := ι), ← Finset.prod_const,
      ← Finset.prod_mul_distrib]
    exact Finset.prod_le_prod fun i _ => (T i).card_mul_le (hc i)
  have hN : (Fintype.card (ι → Out k e) : ℝ≥0∞) ≠ 0 := by simp
  have hD : (Fintype.card ((∀ i, Cs i) × ∀ i, (T i).Coins) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  rw [ENNReal.le_div_iff_mul_le (Or.inl hD) (Or.inl (ENNReal.natCast_ne_top _)), mul_comm, ← div_eq_mul_inv,
    ENNReal.div_le_iff hN (ENNReal.natCast_ne_top _)]
  exact_mod_cast hnat.trans (Nat.mul_le_mul_right _ hle)

end Sampler

end GordieHowe.SPBCS
