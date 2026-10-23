-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.SPBCS.FullPast.ZeroKnowledge
public import GordieHowe.SPBCS.FullPast.Completeness
public import GordieHowe.Model.ROM.AdaptiveCompleteness

@[expose] public section

/-!
# Witnesses drawn by the prover

Completeness and zero knowledge when the prover draws its witness with a witness sampler
(`WitnessSampler`: from a proof query `u` and uniform coins `r`, the witness `draw u r`; for a
proof of possession a proof query is a message with the signer's secret key and `draw` is the signer
with its randomness), each adding the sampler's failure probability `η` (once, or once per
proof query).

- `WitnessSampler.prob_draw_le`: a bound on a uniform oracle at every witness in `rel`
  holds at the drawn witness over the sampler's coins and the oracle, with `η` added; this is the
  completeness step for every compiler. `WitnessSampler.prob_draw_coins_le` is the same with the
  honest prover's uniform coins averaged with the oracle.
- `GordieHowe.QROM.SliceClose.of_draw`: the one-proof hypothesis of the salted zero-knowledge
  theorem (`GordieHowe.QROM.SliceClose`) for a prover that draws its witness, from the one at the
  drawn witnesses, with `η` added: the real slice law is the average over the sampler's coins of
  the slice laws at the drawn witnesses (`realSlice_eq_bind_of_draw`).
- `GordieHowe.SPBCS.FullPast.drawCoinsEquiv`: the draw's coins and the honest prover's coins are the coins of
  `drawProver` in the series–parallel base model. The spBCS compiler's zero knowledge for a prover that
  draws its witness is `GordieHowe.SPBCS.everlastingZeroKnowledge_of_sampler`, at the error of
  `GordieHowe.SPBCS.everlastingZeroKnowledge` plus `Q · η`.
-/

namespace GordieHowe

open GordieHowe.QROM GordieHowe.IOP
open scoped ENNReal NNReal BigOperators

namespace SPBCS

/-- **A witness sampler**: from a proof query `u` and uniform coins `r`, the witness `draw u r`. For a
proof of possession a proof query is a message with the signer's secret key, and `draw` is the signer
with its randomness `r`. -/
structure WitnessSampler (U Wit : Type) where
  /-- The sampler's coins, drawn uniformly. -/
  Coins : Type
  [fintype : Fintype Coins]
  [nonempty : Nonempty Coins]
  /-- The witness drawn on a proof query and the coins. -/
  draw : U → Coins → Wit

attribute [instance] WitnessSampler.fintype WitnessSampler.nonempty

/-- **The coins of a prover that draws its witness**: the coins of the witness draw and the prover's
coins. -/
@[ext]
structure DrawnCoins (RD R : Type) where
  /-- The coins of the witness draw. -/
  draw : RD
  /-- The prover's coins. -/
  iop : R

/-- Drawn-witness coins as their two parts. -/
def DrawnCoins.equivProd (RD R : Type) : DrawnCoins RD R ≃ RD × R where
  toFun c := (c.draw, c.iop)
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance (RD R : Type) [Fintype RD] [Fintype R] : Fintype (DrawnCoins RD R) :=
  Fintype.ofEquiv _ (DrawnCoins.equivProd RD R).symm

instance (RD R : Type) [Nonempty RD] [Nonempty R] : Nonempty (DrawnCoins RD R) :=
  ⟨⟨Classical.arbitrary _, Classical.arbitrary _⟩⟩

/-- **A proof query's witness drawn by the prover**: the prover that, on the proof query `u` and the coins
`c`, runs `honest` at the witness `D u c.draw` with the coins `c.iop`. -/
def drawProver {Wit R U RD Pv : Type} (honest : Wit → R → Pv) (D : U → RD → Wit) :
    U → DrawnCoins RD R → Pv :=
  fun u c => honest (D u c.draw) c.iop

namespace WitnessSampler

variable {Stmt U Wit : Type} (D : WitnessSampler U Wit)

/-- **The sampler misses `rel` with probability at most `η` on the proof query `u` for `x`**: the drawn
witness is outside `rel` with probability at most `η` over the sampler's coins. -/
def MissesAtMostAt (rel : Set (Stmt × Wit)) (x : Stmt) (u : U) (η : ℝ≥0) : Prop :=
  Pr[r ← D.Coins : (x, D.draw u r) ∉ rel] ≤ η

/-- **The sampler misses `rel` with probability at most `η`** on the proof queries of `relU`: for every
proof query `(x, u)` of `relU`, the drawn witness is outside `rel` with probability at most `η` over the
sampler's coins (`MissesAtMostAt`). -/
def MissesAtMost (rel : Set (Stmt × Wit)) (relU : Set (Stmt × U)) (η : ℝ≥0) : Prop :=
  ∀ x u, (x, u) ∈ relU → D.MissesAtMostAt rel x u η

/-- **A draw of the sampler's coins and of a uniform oracle** `Ω`: the probability space of
completeness at a drawn witness. -/
structure Draw (Ω : Type) where
  /-- The sampler's coins. -/
  coins : D.Coins
  /-- The random oracle. -/
  oracle : Ω

/-- A draw is a pair of the coins and the oracle. -/
def drawEquiv (Ω : Type) : D.Draw Ω ≃ D.Coins × Ω where
  toFun d := (d.coins, d.oracle)
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance (Ω : Type) [Fintype Ω] : Fintype (D.Draw Ω) :=
  Fintype.ofEquiv _ (D.drawEquiv Ω).symm

instance (Ω : Type) [Nonempty Ω] : Nonempty (D.Draw Ω) :=
  ⟨⟨Classical.arbitrary _, Classical.arbitrary _⟩⟩

open Classical in
/-- **A bound at every witness holds at the drawn witness, with the sampler's failure added**:
if the event `bad w` on a uniform oracle has probability at most `c` for every witness `w` of `x`
in `rel`, then over the sampler's coins and the oracle the event at the witness drawn on the
proof query `u` has probability at most `c + η` when the sampler misses `rel` on `u` with probability
at most `η` (`hD`). -/
theorem prob_draw_le {Ω : Type} [Fintype Ω] [Nonempty Ω] {rel : Set (Stmt × Wit)} {x : Stmt}
    {u : U} {η : ℝ≥0} (hD : D.MissesAtMostAt rel x u η) (bad : Wit → Ω → Prop) {c : ℝ≥0∞}
    (hc : ∀ w, (x, w) ∈ rel → Pr[h ← Ω : bad w h] ≤ c) :
    Pr[d ← D.Draw Ω : bad (D.draw u d.coins) d.oracle] ≤ c + η := by
  rw [← QROM.probUniform_equiv (D.drawEquiv Ω).symm]
  exact (probUniform_prod_le_add _ (fun r => (x, D.draw u r) ∉ rel) fun r hr =>
    hc _ (not_not.mp hr)).trans (add_le_add le_rfl hD)

/-- A draw over a product with the prover's coins `R` is a pair of the coins and a draw. -/
def drawCoinsProdEquiv (R Ω : Type) : D.Draw (R × Ω) ≃ R × D.Draw Ω where
  toFun d := (d.oracle.1, ⟨d.coins, d.oracle.2⟩)
  invFun q := ⟨q.2.coins, (q.1, q.2.oracle)⟩
  left_inv _ := rfl
  right_inv _ := rfl

open Classical in
/-- **A bound averaged over the prover's coins at every witness holds at the drawn witness, with
the sampler's failure added**: if the event `bad w r h` has probability at most `c` over uniform
coins `r` and a uniform oracle `h` for every witness `w` of `x` in `rel`, then its average over the
coins of the probability over the sampler's coins and the oracle at the witness drawn on the
proof query `u` is at most `c + η` when the sampler misses `rel` on `u` with probability at most `η`
(`hD`). -/
theorem prob_draw_coins_le {Ω R : Type} [Fintype Ω] [Nonempty Ω] [Fintype R] [Nonempty R]
    {rel : Set (Stmt × Wit)} {x : Stmt} {u : U} {η : ℝ≥0} (hD : D.MissesAtMostAt rel x u η)
    (bad : Wit → R → Ω → Prop) {c : ℝ≥0∞}
    (hc : ∀ w, (x, w) ∈ rel → Pr[q ← R × Ω : bad w q.1 q.2] ≤ c) :
    ∑ r, (Fintype.card R : ℝ≥0∞)⁻¹ * Pr[d ← D.Draw Ω : bad (D.draw u d.coins) r d.oracle] ≤
      c + η := by
  rw [← ROM.probUniform_prod_eq_sum
      (fun q : R × D.Draw Ω => bad (D.draw u q.2.coins) q.1 q.2.oracle),
    ← QROM.probUniform_equiv (D.drawCoinsProdEquiv R Ω)]
  exact D.prob_draw_le hD (fun w (q : R × Ω) => bad w q.1 q.2) hc

end WitnessSampler

end SPBCS

/-! ### The one-proof hypothesis for a prover that draws its witness -/

namespace QROM

section Drawn

variable {X Y Sd Stmt Wit U Proof C C' SC RD : Type} [Fintype X] [DecidableEq X] [Fintype Y]
  [DecidableEq Y] [Nonempty Y] [Fintype Sd] [DecidableEq Sd] [Nonempty Sd] [Fintype C]
  [Nonempty C] [Fintype C'] [Nonempty C'] [Fintype SC] [Nonempty SC] [Fintype Proof]
  [DecidableEq Proof] [Fintype RD] [Nonempty RD] {saltOf : X → Option Sd}
  {P : NARG.ProverFn X Y Stmt Wit Proof (SaltedCoins Sd C)}
  {P' : NARG.ProverFn X Y Stmt U Proof (SaltedCoins Sd C')} {D : U → RD → Wit} {e : RD × C ≃ C'}

omit [DecidableEq Y] [Fintype Proof] [DecidableEq Proof] in
/-- **The real slice law of a prover that draws its witness** is the average over the draw's coins
of the real slice laws at the drawn witnesses, when the prover `P'` on the proof query `u` with the
coins `e (r, c)` computes the proof of `P` at the witness `D u r` with the coins `c` (`he`). -/
theorem realSlice_eq_bind_of_draw
    (he : ∀ H x u σ r c, P'.prove H x u ⟨σ, e (r, c)⟩ = P.prove H x (D u r) ⟨σ, c⟩)
    (H : X → Y) (x : Stmt) (u : U) :
    realSlice saltOf P' H x u =
      (PMF.uniformOfFintype RD).bind fun r => realSlice saltOf P H x (D u r) := by
  let f : RD × FreshSlice X Y (SaltedCoins Sd C) ≃ FreshSlice X Y (SaltedCoins Sd C') :=
    { toFun := fun a => ⟨⟨a.2.coins.salt, e (a.1, a.2.coins.coins)⟩, a.2.slice⟩
      invFun := fun b =>
        ((e.symm b.coins.coins).1, ⟨⟨b.coins.salt, (e.symm b.coins.coins).2⟩, b.slice⟩)
      left_inv := fun ⟨r, ⟨⟨σ, c⟩, F⟩⟩ => by simp
      right_inv := fun ⟨⟨σ, c⟩, F⟩ => by simp }
  rw [realSlice, ← PMF.map_uniformOfFintype_equiv f, PMF.map_comp,
    PMF.uniformOfFintype_prod_eq_bind, PMF.map_bind]
  refine congrArg _ (funext fun r => ?_)
  rw [PMF.map_comp, realSlice]
  congr 1
  funext a
  simp only [Function.comp_apply, f, Equiv.coe_fn_mk, he]

omit [DecidableEq Y] [DecidableEq Proof] in
open Classical in
/-- **The one-proof hypothesis for a prover that draws its witness**: if the real and simulated
slice laws are within `η H` at every witness in `rel` (`hcl`), and on every proof query `(x, u)` of
`relU` the drawn witness `D u r` is outside `rel` with probability at most `η'` over uniform `r`
(`hD`), then for the prover `P'` that draws its witness (`he`) they are within `η H + η'` on
every proof query of `relU`: each drawn witness in `rel` costs `η H`, and the others at most `1`. -/
theorem SliceClose.of_draw {rel : Stmt → Wit → Prop} {relU : Stmt → U → Prop}
    {S : NARG.SimulatorFn X Y Stmt Proof (SaltedCoins Sd SC)} {η : (X → Y) → ℝ} {η' : ℝ≥0}
    (he : ∀ H x u σ r c, P'.prove H x u ⟨σ, e (r, c)⟩ = P.prove H x (D u r) ⟨σ, c⟩)
    (hcl : SliceClose saltOf rel P S η) (hD : ∀ x u, relU x u → Pr[r ← RD : ¬ rel x (D u r)] ≤ η') :
    SliceClose saltOf relU P' S fun H => η H + η' where
  close H x u hu := by
    rw [realSlice_eq_bind_of_draw he, ← PMF.bind_const (PMF.uniformOfFintype RD)
      (simSlice saltOf S H x)]
    refine (PMF.tvDist_uniformOfFintype_bind_le _ _).trans ?_
    have hle : ∀ r, PMF.tvDist (realSlice saltOf P H x (D u r)) (simSlice saltOf S H x) ≤
        η H + if ¬ rel x (D u r) then (1 : ℝ) else 0 := fun r => by
      by_cases hr : rel x (D u r)
      · simp only [hr, not_true_eq_false, ite_false, add_zero]
        exact hcl.close H x (D u r) hr
      · simp only [hr, not_false_eq_true, ite_true]
        exact (PMF.tvDist_le_one _ _).trans (le_add_of_nonneg_left (hcl.nonneg H))
    calc 𝔼 r, PMF.tvDist (realSlice saltOf P H x (D u r)) (simSlice saltOf S H x)
        ≤ 𝔼 r : RD, (η H + if ¬ rel x (D u r) then (1 : ℝ) else 0) :=
          Finset.expect_le_expect fun r _ => hle r
      _ = η H + (Pr[r ← RD : ¬ rel x (D u r)]).toReal := by
          rw [Finset.expect_add_distrib, Finset.expect_const Finset.univ_nonempty,
            toReal_probUniform]
      _ ≤ η H + η' := by
          gcongr
          exact ENNReal.toReal_le_of_le_ofReal η'.2
            ((hD x u hu).trans_eq (ENNReal.ofReal_coe_nnreal).symm)
  nonneg H := add_nonneg (hcl.nonneg H) η'.2
  congr H H' hH := by rw [hcl.congr H H' hH]

end Drawn

end QROM

/-! ### The coins of the series–parallel base model -/

namespace SPBCS.FullPast

open Base

open SPTerm Quantum GordieHowe.QROM

variable {k kN kS L e : ℕ} {ι : Type} {n : ι → ℕ} {P : (j : ι) → ProtocolSpec (n j)}
  [∀ j i, Fintype ((P j).Challenge i)] [∀ j i, DecidableEq ((P j).Challenge i)]
  [∀ j i, Nonempty ((P j).Challenge i)] {t : SPTerm ι} {X : Type}
  {M : FullPast P t X k kN kS L e}

variable (M) in
/-- **The coins of the prover drawing its witness, rearranged**: the draw's coins and the
honest prover's coins are the coins of `drawProver`. -/
def drawCoinsEquiv (RD R : Type) : RD × M.ProverCoins R ≃ M.ProverCoins (DrawnCoins RD R) where
  toFun a := ⟨⟨a.1, a.2.iop⟩, a.2.merkleSalts⟩
  invFun b := (b.iop.draw, ⟨b.iop.iop, b.merkleSalts⟩)
  left_inv _ := rfl
  right_inv _ := rfl

end SPBCS.FullPast

end GordieHowe
