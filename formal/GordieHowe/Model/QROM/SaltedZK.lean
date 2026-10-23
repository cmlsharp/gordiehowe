-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.QROM.NIZK
public import GordieHowe.Model.Quantum.Pure.GameTape
public import GordieHowe.Model.Quantum.O2H.Budget
public import GordieHowe.Foundations.ToMathlib.PMFUniform

@[expose] public section

/-!
# Zero knowledge of a non-interactive argument with a per-proof salt

A generic argument (with the unbounded phase after the last slot) for non-interactive arguments
whose oracle inputs carry a per-proof salt in a salt slot. The oracle is `H : X → Y`; `saltOf x` is
the salt in the slot of the input `x`, or `none` for an input without one. The prover's coins and
the simulator's coins are `(σ, c)` with a uniform salt `σ : Sd` and further uniform coins.

**Locality** (`SaltedLocal`). The prover with salt `σ` reads the oracle only on salt-free inputs
and inputs with salt `σ`; so does the simulator, and its assignment list programs only inputs
with its own salt.

**The slice laws.** For an oracle `H` and a salt `σ`, `replaceSlice saltOf σ H F` is `H` with
the inputs of salt `σ` answered by `F`. `realSlice H x w` is the law of the honest proof and the
oracle when the slice of a fresh salt is fresh (`F` uniform), and `simSlice H x` the law of the
simulator's proof and the reprogrammed oracle on the same oracle. The hypothesis of the theorem
(`SliceClose`) is that these are within `η H` in total variation for every valid proof query, where
`η H` reads `H` only on salt-free inputs. It is a classical statement about one proof.

**The theorem** (`zeroKnowledgeAfterAdaptive_of_sliceClose`): zero knowledge unbounded after the
last slot, against distinguishers with a query budget (`ZeroKnowledgeAfterAdaptive`), at the
simulator `S`, with error

    4 Q t / √|Sd| + Q (Q - 1) / |Sd| + Q · 𝔼 H, η H.

**The argument**, per proof query `j` of the hybrid `hybridEnv j` (simulator for the proof queries numbered
below `j`, prover from `j` on, both on the oracle in force), from `j` to `j + 1`. On the branches
that never make proof query `j` the two hybrids agree (`acceptProbOnAt_notMade_eq`); on the branches
that make it (`madeLogs j`):

1. (`relabel`, exact) The tape gets proof query `j`'s coins `(σ, c)` and a fresh slice `F`, and the
   initial oracle is `H` with the slice of `σ` answered by `F`: the same law
   (`acceptProbOn_hybridEnv_eq_relabelP`, `acceptProbOn_hybridEnv_eq_relabelS`).
2. (salt collision, `j / |Sd|`) Up to the event that an earlier simulator drew the salt `σ`, the
   oracle in force is the hybrid's oracle shifted by `D = F - H` on the slice of `σ`
   (`stepEnv` with shift `D`): the earlier simulators neither read nor program that slice.
3. (O2H, `2 q √(n / |Sd|)` for a budget of `q` query slots) Before proof query `j` the distinguisher
   queries `H` instead of the shifted oracle; at proof query `j` the shift is applied (`stepEnv` with
   shift `0`). The two differ before proof query `j` only on the inputs of salt `σ`, and `σ` is fresh
   (`Distinguisher.advantage_acceptProbOn_made_le_of_fresh_secret_budget`).
4. (kernel, `𝔼 H, η H`) Proof query `j`'s response kernel, the honest proof on the shifted oracle,
   has the law `realSlice`; it is replaced by the simulator's, `simSlice`
   (`Distinguisher.abs_acceptProbOn_sub_le_of_kernel`).
5. Steps 3, 2 and 1 backwards with the simulator's salt at proof query `j`, arriving at
   `hybridEnv (j + 1)`.

Two O2H steps per proof query are needed: the slice of `σ` is fresh only after the oracle before
proof query `j` has been changed, and the simulated game restores the original slice.
-/

open Finset
open scoped BigOperators

namespace GordieHowe

namespace QROM

variable {X Y Sd Stmt Wit Proof C SC : Type*}

/-! ### Slices -/

section Slice

variable (saltOf : X → Option Sd) [DecidableEq Sd]

/-- `H` with the inputs whose salt slot holds `σ` answered by `F`. -/
def replaceSlice (σ : Sd) (H F : X → Y) : X → Y :=
  fun x => if saltOf x = some σ then F x else H x

/-- The shift that turns `H` into `replaceSlice saltOf σ H F`: `F - H` on the inputs of salt `σ`,
`0` elsewhere. -/
def sliceShift [AddCommGroup Y] (σ : Sd) (H F : X → Y) : X → Y :=
  fun x => if saltOf x = some σ then F x - H x else 0

theorem replaceSlice_replaceSlice_left (σ : Sd) (H F G : X → Y) :
    replaceSlice saltOf σ (replaceSlice saltOf σ H F) G = replaceSlice saltOf σ H G := by
  funext x
  by_cases h : saltOf x = some σ <;> simp [replaceSlice, h]

theorem replaceSlice_replaceSlice_right (σ : Sd) (H F G : X → Y) :
    replaceSlice saltOf σ G (replaceSlice saltOf σ H F) = replaceSlice saltOf σ G F := by
  funext x
  by_cases h : saltOf x = some σ <;> simp [replaceSlice, h]

theorem replaceSlice_self (σ : Sd) (H : X → Y) : replaceSlice saltOf σ H H = H := by
  funext x
  simp [replaceSlice]

theorem replaceSlice_eq_add [AddCommGroup Y] (σ : Sd) (H F : X → Y) :
    replaceSlice saltOf σ H F = H + sliceShift saltOf σ H F := by
  funext x
  by_cases h : saltOf x = some σ
  · simp only [replaceSlice, sliceShift, h, ite_true, Pi.add_apply]
    abel
  · simp [replaceSlice, sliceShift, h]

end Slice

/-! ### Coins, fresh slices and hybrid tapes -/

/-- **The coins of a salted prover or simulator**: a salt for the salt slot and the further coins.
-/
@[ext]
structure SaltedCoins (Sd C : Type*) where
  /-- The salt. -/
  salt : Sd
  /-- The further coins. -/
  coins : C

namespace SaltedCoins

variable (Sd C : Type*)

/-- Salted coins as the salt and the further coins. -/
def equivProd : SaltedCoins Sd C ≃ Sd × C where
  toFun c := (c.salt, c.coins)
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance [Fintype Sd] [Fintype C] : Fintype (SaltedCoins Sd C) :=
  Fintype.ofEquiv _ (equivProd Sd C).symm

instance [Nonempty Sd] [Nonempty C] : Nonempty (SaltedCoins Sd C) :=
  ⟨⟨Classical.arbitrary Sd, Classical.arbitrary C⟩⟩

instance [DecidableEq Sd] [DecidableEq C] : DecidableEq (SaltedCoins Sd C) :=
  (equivProd Sd C).decidableEq

variable {Sd C}

theorem sum_eq {M : Type*} [AddCommMonoid M] [Fintype Sd] [Fintype C] (f : SaltedCoins Sd C → M) :
    ∑ c, f c = ∑ σ, ∑ c, f ⟨σ, c⟩ := by
  rw [← (equivProd Sd C).symm.sum_comp, Fintype.sum_prod_type]
  rfl

theorem card_eq [Fintype Sd] [Fintype C] :
    Fintype.card (SaltedCoins Sd C) = Fintype.card Sd * Fintype.card C := by
  rw [Fintype.card_congr (equivProd Sd C), Fintype.card_prod]

end SaltedCoins

/-- **A fresh slice draw**: the coins of one proof query and a function, the fresh answers on the slice
of their salt. -/
@[ext]
structure FreshSlice (X Y Cx : Type*) where
  /-- The proof query's coins. -/
  coins : Cx
  /-- The fresh answers on the slice. -/
  slice : X → Y

namespace FreshSlice

variable (X Y Cx : Type*)

/-- A fresh slice draw as its coins and its slice. -/
def equivProd : FreshSlice X Y Cx ≃ Cx × (X → Y) where
  toFun a := (a.coins, a.slice)
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance [Fintype X] [DecidableEq X] [Fintype Y] [Fintype Cx] : Fintype (FreshSlice X Y Cx) :=
  Fintype.ofEquiv _ (equivProd X Y Cx).symm

instance [Nonempty Y] [Nonempty Cx] : Nonempty (FreshSlice X Y Cx) :=
  ⟨⟨Classical.arbitrary Cx, fun _ => Classical.arbitrary Y⟩⟩

variable {X Y Cx} [Fintype X] [DecidableEq X] [Fintype Y]

theorem sum_eq {M : Type*} [AddCommMonoid M] [Fintype Cx] (f : FreshSlice X Y Cx → M) :
    ∑ a, f a = ∑ c, ∑ F, f ⟨c, F⟩ := by
  rw [← (equivProd X Y Cx).symm.sum_comp, Fintype.sum_prod_type]
  rfl

theorem card_eq [Fintype Cx] :
    Fintype.card (FreshSlice X Y Cx) = Fintype.card Cx * Fintype.card (X → Y) := by
  rw [Fintype.card_congr (equivProd X Y Cx), Fintype.card_prod]

variable [Nonempty Y] {Sd C : Type*} [Fintype Sd] [Nonempty Sd] [Fintype C] [Nonempty C]

/-- **A uniform salted draw averages over the salt**: the uniform law of a fresh slice draw with
salted coins, read through `f`, is the uniform salt followed by the uniform draw of the further
coins and the slice. -/
theorem map_uniformOfFintype_salted {β : Type*} (f : FreshSlice X Y (SaltedCoins Sd C) → β) :
    (PMF.uniformOfFintype (FreshSlice X Y (SaltedCoins Sd C))).map f =
      (PMF.uniformOfFintype Sd).bind fun σ =>
        (PMF.uniformOfFintype (FreshSlice X Y C)).map fun a => f ⟨⟨σ, a.coins⟩, a.slice⟩ := by
  let e : Sd × FreshSlice X Y C ≃ FreshSlice X Y (SaltedCoins Sd C) :=
    { toFun := fun p => ⟨⟨p.1, p.2.coins⟩, p.2.slice⟩
      invFun := fun a => (a.coins.salt, ⟨a.coins.coins, a.slice⟩)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← PMF.map_uniformOfFintype_equiv e, PMF.map_comp, PMF.uniformOfFintype_prod_eq_bind,
    PMF.map_bind]
  congr 1
  funext σ
  rw [PMF.map_comp]
  rfl

/-- The salt and the slice of a uniform salted draw are uniform. -/
theorem map_salt_slice_uniformOfFintype :
    (PMF.uniformOfFintype (FreshSlice X Y (SaltedCoins Sd C))).map (fun a => (a.coins.salt, a.slice)) =
      PMF.uniformOfFintype (Sd × (X → Y)) := by
  let e : FreshSlice X Y (SaltedCoins Sd C) ≃ (Sd × (X → Y)) × C :=
    { toFun := fun a => ((a.coins.salt, a.slice), a.coins.coins)
      invFun := fun p => ⟨⟨p.1.1, p.2⟩, p.1.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have h : (fun a : FreshSlice X Y (SaltedCoins Sd C) => (a.coins.salt, a.slice)) = Prod.fst ∘ e := rfl
  rw [h, ← PMF.map_comp, PMF.map_uniformOfFintype_equiv, PMF.map_fst_uniformOfFintype]

/-- **The salt of a uniform salted draw is in a fixed set of one salt with probability
`1 / |Sd|`.** -/
theorem prob_salt_eq (σ : Sd) :
    ((PMF.uniformOfFintype (FreshSlice X Y (SaltedCoins Sd C))).toOuterMeasure
      {a | a.coins.salt = σ}).toReal = (Fintype.card Sd : ℝ)⁻¹ := by
  classical
  rw [PMF.toReal_toOuterMeasure_apply, sum_eq, SaltedCoins.sum_eq,
    Finset.sum_eq_single σ (fun σ' _ hσ' => by simp [hσ']) (by simp)]
  simp only [Set.mem_ofPred_eq, ite_true, PMF.toReal_uniformOfFintype_apply, card_eq,
    SaltedCoins.card_eq, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  push_cast
  have h1 : (Fintype.card C : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have h2 : (Fintype.card (X → Y) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  field_simp

end FreshSlice

/-- **The tape of the hybrids**: the initial oracle, and prover coins and simulator coins for every
proof query. -/
@[ext]
structure HybridTape (X Y Coins SimCoins : Type*) (Q : ℕ) where
  /-- The initial oracle. -/
  oracle : X → Y
  /-- The prover's coins of each proof query. -/
  proverCoins : Fin Q → Coins
  /-- The simulator's coins of each proof query. -/
  simCoins : Fin Q → SimCoins

namespace HybridTape

variable (X Y Coins SimCoins : Type*) (Q : ℕ)

/-- A hybrid tape as its oracle and its two coin families. -/
def equivProd :
    HybridTape X Y Coins SimCoins Q ≃ (X → Y) × (Fin Q → Coins) × (Fin Q → SimCoins) where
  toFun v := (v.oracle, v.proverCoins, v.simCoins)
  invFun p := ⟨p.1, p.2.1, p.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance [Fintype X] [DecidableEq X] [Fintype Y] [Fintype Coins] [Fintype SimCoins] :
    Fintype (HybridTape X Y Coins SimCoins Q) :=
  Fintype.ofEquiv _ (equivProd X Y Coins SimCoins Q).symm

instance [Nonempty Y] [Nonempty Coins] [Nonempty SimCoins] :
    Nonempty (HybridTape X Y Coins SimCoins Q) :=
  ⟨⟨fun _ => Classical.arbitrary Y, fun _ => Classical.arbitrary Coins,
    fun _ => Classical.arbitrary SimCoins⟩⟩

variable {X Y Coins SimCoins Q} [Fintype X] [DecidableEq X] [Fintype Y] [Fintype Coins]
  [Fintype SimCoins]

theorem sum_eq {M : Type*} [AddCommMonoid M] (f : HybridTape X Y Coins SimCoins Q → M) :
    ∑ v, f v = ∑ H, ∑ cs : (Fin Q → Coins) × (Fin Q → SimCoins), f ⟨H, cs.1, cs.2⟩ := by
  rw [← (equivProd X Y Coins SimCoins Q).symm.sum_comp, Fintype.sum_prod_type]
  rfl

theorem card_eq : Fintype.card (HybridTape X Y Coins SimCoins Q) =
    Fintype.card (X → Y) * Fintype.card ((Fin Q → Coins) × (Fin Q → SimCoins)) := by
  rw [Fintype.card_congr (equivProd X Y Coins SimCoins Q), Fintype.card_prod]

/-- **The uniform hybrid tape** is a uniform oracle and uniform coin families, independent. -/
theorem uniformOfFintype_eq_bind [Nonempty Y] [Nonempty Coins] [Nonempty SimCoins] :
    PMF.uniformOfFintype (HybridTape X Y Coins SimCoins Q) =
      (PMF.uniformOfFintype (X → Y)).bind fun H =>
        (PMF.uniformOfFintype (Fin Q → Coins)).bind fun c =>
          (PMF.uniformOfFintype (Fin Q → SimCoins)).map fun s => ⟨H, c, s⟩ := by
  rw [← PMF.map_uniformOfFintype_equiv (equivProd X Y Coins SimCoins Q).symm,
    PMF.uniformOfFintype_prod_eq_bind, PMF.map_bind]
  congr 1
  funext H
  rw [PMF.uniformOfFintype_prod_eq_bind, PMF.map_comp, PMF.map_bind]
  congr 1
  funext c
  rw [PMF.map_comp]
  rfl

end HybridTape

/-! ### Hybrids over the proof queries -/

section Hybrid

variable [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y] (rel : Stmt → Wit → Prop)
  [DecidableRel rel] {Coins SimCoins : Type*} [Fintype Coins] [Fintype SimCoins]

/-- The law of the hybrid tape: a uniform oracle, prover coins and simulator coins for every
proof query, all independent. -/
noncomputable def hybridLaw (Q : ℕ) (μP : PMF Coins) (μS : PMF SimCoins) :
    PMF (HybridTape X Y Coins SimCoins Q) :=
  (PMF.uniformOfFintype (X → Y)).bind fun H =>
    (PMF.pi fun _ : Fin Q => μP).bind fun c => (PMF.pi fun _ : Fin Q => μS).map fun s => ⟨H, c, s⟩

/-- **Hybrid `j`**: a valid proof query numbered `i < j` is answered by the simulator on the oracle in
force, which it reprograms; a valid proof query numbered `i ≥ j` by the honest prover on the oracle in
force, which it leaves unchanged; an invalid proof query by `none`. Hybrid `0` is the real game and
hybrid `Q` the simulated game (`acceptProb_hybridEnv_zero`, `acceptProb_hybridEnv_card`). -/
noncomputable def hybridEnv (P : NARG.ProverFn X Y Stmt Wit Proof Coins)
    (S : NARG.SimulatorFn X Y Stmt Proof SimCoins) (Q j : ℕ) :
    Quantum.Env (HybridTape X Y Coins SimCoins Q) (ProofQuery Stmt Wit) Proof X Y Q where
  μ := hybridLaw Q P.coins S.coins
  oracle₀ ω := ω.oracle
  respond ω i req H :=
    if rel req.stmt req.wit then
      if (i : ℕ) < j then
        let r := S.run H req.stmt (ω.simCoins i)
        ⟨some r.proof, H.reprogram r.assignments⟩
      else ⟨some (P.prove H req.stmt req.wit (ω.proverCoins i)), H⟩
    else ⟨none, H⟩

variable [AddGroup Y] [Fintype Stmt] [DecidableEq Stmt] [Fintype Wit] [DecidableEq Wit]
  [Fintype Proof] [DecidableEq Proof] {W : Type} [Fintype W] {n m Q : ℕ}
  (D : Quantum.Distinguisher W X Y (ProofQuery Stmt Wit) Proof n m)
  (post : (X → Y) → Quantum.QState (Quantum.DReg W n X Y (ProofQuery Stmt Wit) Proof) ≃ₗᵢ[ℂ]
    Quantum.QState (Quantum.DReg W n X Y (ProofQuery Stmt Wit) Proof))

/-- Hybrid `0` is the real game. -/
theorem acceptProb_hybridEnv_zero (P : NARG.ProverFn X Y Stmt Wit Proof Coins)
    (S : NARG.SimulatorFn X Y Stmt Proof SimCoins) :
    D.acceptProb (hybridEnv rel P S Q 0) post = D.acceptProb (realEnv rel P Q) post := by
  refine D.acceptProb_comap post (fun ω => (ω.oracle, ω.proverCoins)) ?_ (fun _ => rfl) fun ω => ?_
  · simp only [realEnv, hybridEnv, tapeDist, hybridLaw, PMF.map_bind]
    congr 1
    funext H
    have h : ∀ a, PMF.map (fun ω : HybridTape X Y Coins SimCoins Q => (ω.oracle, ω.proverCoins))
        (PMF.map (fun s => (⟨H, a, s⟩ : HybridTape X Y Coins SimCoins Q))
          (PMF.pi fun _ : Fin Q => S.coins)) = PMF.pure (H, a) :=
      fun a => by
        rw [PMF.map_comp]
        exact PMF.map_const (PMF.pi fun _ : Fin Q => S.coins) (H, a)
    simp only [h]
    exact (PMF.bind_pure_comp _ _).symm
  · funext i req H
    simp only [hybridEnv, realEnv, Nat.not_lt_zero, ite_false]
    split_ifs <;> rfl

/-- Hybrid `Q` is the simulated game. -/
theorem acceptProb_hybridEnv_card (P : NARG.ProverFn X Y Stmt Wit Proof Coins)
    (S : NARG.SimulatorFn X Y Stmt Proof SimCoins) :
    D.acceptProb (hybridEnv rel P S Q Q) post = D.acceptProb (simEnv rel S Q) post := by
  refine D.acceptProb_comap post (fun ω => (ω.oracle, ω.simCoins)) ?_ (fun _ => rfl) fun ω => ?_
  · simp only [simEnv, hybridEnv, tapeDist, hybridLaw, PMF.map_bind]
    congr 1
    funext H
    have h : ∀ a, PMF.map (fun ω : HybridTape X Y Coins SimCoins Q => (ω.oracle, ω.simCoins))
        (PMF.map (fun s => (⟨H, a, s⟩ : HybridTape X Y Coins SimCoins Q))
          (PMF.pi fun _ : Fin Q => S.coins)) =
          PMF.map (fun s => (H, s)) (PMF.pi fun _ : Fin Q => S.coins) := fun a => by
      rw [PMF.map_comp]
      rfl
    simp only [h, PMF.bind_const]
  · funext i req H
    simp only [hybridEnv, simEnv, i.2, ite_true]

/-- **The hybrid argument over the proof queries**: the advantage is at most the sum over `j` of the
distance between hybrids `j` and `j + 1`. -/
theorem advantage_le_sum_hybrid (P : NARG.ProverFn X Y Stmt Wit Proof Coins)
    (S : NARG.SimulatorFn X Y Stmt Proof SimCoins) :
    QROM.advantage (Q := Q) rel P S D post ≤ ∑ j : Fin Q,
      |D.acceptProb (hybridEnv rel P S Q j) post - D.acceptProb (hybridEnv rel P S Q (j + 1)) post| := by
  rw [QROM.advantage, GordieHowe.advantage, ← acceptProb_hybridEnv_zero rel D post P S, ← acceptProb_hybridEnv_card rel D post P S,
    ← Finset.sum_range_sub' (fun j => D.acceptProb (hybridEnv rel P S Q j) post) Q,
    Fin.sum_univ_eq_sum_range (fun j => |D.acceptProb (hybridEnv rel P S Q j) post -
      D.acceptProb (hybridEnv rel P S Q (j + 1)) post|)]
  exact Finset.abs_sum_le_sum_abs _ _

end Hybrid

/-! ### Agreement on slices -/

section Agree

variable {X Y Sd : Type*} (saltOf : X → Option Sd)

/-- **`H` and `H'` agree on the slice of the salt `σ`**: on the salt-free inputs and on the inputs
with salt `σ`. -/
def AgreeOnSlice (σ : Sd) (H H' : X → Y) : Prop :=
  ∀ y, saltOf y = none ∨ saltOf y = some σ → H y = H' y

/-- **`H` and `H'` agree on the salt-free inputs.** -/
def AgreeOffSalted (H H' : X → Y) : Prop :=
  ∀ y, saltOf y = none → H y = H' y

variable {saltOf}

theorem agreeOnSlice_iff {σ : Sd} {H H' : X → Y} :
    AgreeOnSlice saltOf σ H H' ↔ ∀ y, saltOf y = none ∨ saltOf y = some σ → H y = H' y :=
  Iff.rfl

theorem agreeOffSalted_iff {H H' : X → Y} :
    AgreeOffSalted saltOf H H' ↔ ∀ y, saltOf y = none → H y = H' y :=
  Iff.rfl

end Agree

/-! ### Salted arguments -/

section Salted

variable [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [Nonempty Y] [Fintype Sd]
  [DecidableEq Sd] [Nonempty Sd] [Fintype C] [Nonempty C] [Fintype SC] [Nonempty SC]
  [Fintype Proof] [DecidableEq Proof] (saltOf : X → Option Sd) (rel : Stmt → Wit → Prop) [DecidableRel rel]
  (P : NARG.ProverFn X Y Stmt Wit Proof (SaltedCoins Sd C)) (S : NARG.SimulatorFn X Y Stmt Proof (SaltedCoins Sd SC))

/-- **Locality of a salted argument.** The prover with salt `σ` and the simulator with salt `σ`
read the oracle only on salt-free inputs and inputs with salt `σ`; the simulator's assignment list
programs only inputs with its salt; the prover draws uniform coins (the simulator's coins are
uniform by definition, `Simulator.coins`). -/
structure SaltedLocal : Prop where
  prove_congr : ∀ (H H' : X → Y) x w (c : SaltedCoins Sd C),
    AgreeOnSlice saltOf c.salt H H' → P.prove H x w c = P.prove H' x w c
  run_congr : ∀ (H H' : X → Y) x (s : SaltedCoins Sd SC),
    AgreeOnSlice saltOf s.salt H H' → S.run H x s = S.run H' x s
  run_salt : ∀ (H : X → Y) x (s : SaltedCoins Sd SC), ∀ a ∈ (S.run H x s).assignments,
    saltOf a.input = some s.salt
  coins_eq : P.coins = PMF.uniformOfFintype (SaltedCoins Sd C)

/-- **The real slice law**: for uniform prover coins `c` and a uniform slice `F`, the honest
proof of `(x, w)` on `H` with the slice of `c.salt` answered by `F`, and that oracle. -/
noncomputable def realSlice (H : X → Y) (x : Stmt) (w : Wit) : PMF (Quantum.EnvReply Proof (X → Y)) :=
  (PMF.uniformOfFintype (FreshSlice X Y (SaltedCoins Sd C))).map fun a =>
    let H' := replaceSlice saltOf a.coins.salt H a.slice
    ⟨some (P.prove H' x w a.coins), H'⟩

/-- **The simulated slice law**: for uniform simulator coins `s` and a uniform slice `F`, the
simulator's proof of `x` on `H` with the slice of `s.salt` answered by `F`, and that oracle
reprogrammed by the simulator's assignment list. -/
noncomputable def simSlice (H : X → Y) (x : Stmt) : PMF (Quantum.EnvReply Proof (X → Y)) :=
  (PMF.uniformOfFintype (FreshSlice X Y (SaltedCoins Sd SC))).map fun a =>
    let H' := replaceSlice saltOf a.coins.salt H a.slice
    let r := S.run H' x a.coins
    ⟨some r.proof, H'.reprogram r.assignments⟩

/-- **The one-proof hypothesis**: for every oracle `H` and valid proof query `(x, w)`, the real and
the simulated slice laws are within `η H` in total variation, where `η H ≥ 0` reads `H` only on
salt-free inputs. A classical statement about one proof. -/
structure SliceClose (η : (X → Y) → ℝ) : Prop where
  close : ∀ H x w, rel x w → realSlice saltOf P H x w ≈[η H] simSlice saltOf S H x
  nonneg : ∀ H, 0 ≤ η H
  congr : ∀ H H' : X → Y, AgreeOffSalted saltOf H H' → η H = η H'

variable {saltOf rel P S} in
/-- Locality in the salt survives reading statements and witnesses through maps. -/
theorem SaltedLocal.comap {Stmt' Wit' : Type*} (h : SaltedLocal saltOf P S) (fx : Stmt' → Stmt)
    (fw : Wit' → Wit) : SaltedLocal saltOf (P.comap fx fw) (S.comap fx) where
  prove_congr H H' x w c hH := h.prove_congr H H' (fx x) (fw w) c hH
  run_congr H H' x s hH := h.run_congr H H' (fx x) s hH
  run_salt H x s := h.run_salt H (fx x) s
  coins_eq := h.coins_eq

variable {saltOf rel P S} in
/-- The one-proof hypothesis survives reading statements and witnesses through maps, for the
relation read through the same maps. -/
theorem SliceClose.comap {Stmt' Wit' : Type*} {η : (X → Y) → ℝ} (h : SliceClose saltOf rel P S η)
    (fx : Stmt' → Stmt) (fw : Wit' → Wit) :
    SliceClose saltOf (fun x w => rel (fx x) (fw w)) (P.comap fx fw) (S.comap fx) η where
  close H x w hw := h.close H (fx x) (fw w) hw
  nonneg := h.nonneg
  congr := h.congr

variable [AddCommGroup Y] [Fintype Stmt] [DecidableEq Stmt] [Fintype Wit] [DecidableEq Wit]
  {W : Type} [Fintype W] {n m Q : ℕ}
  (D : Quantum.Distinguisher W X Y (ProofQuery Stmt Wit) Proof n m)
  (post : (X → Y) → Quantum.QState (Quantum.DReg W n X Y (ProofQuery Stmt Wit) Proof) ≃ₗᵢ[ℂ]
    Quantum.QState (Quantum.DReg W n X Y (ProofQuery Stmt Wit) Proof))

/-! ### The environments of one step -/

/-- The tape of the hybrids of a salted argument. -/
abbrev HTape (X Y Sd C SC : Type*) (Q : ℕ) := HybridTape X Y (SaltedCoins Sd C) (SaltedCoins Sd SC) Q

/-- A simulator response on an oracle shifted by `D`: the simulator on `H - D`, and its
reprogrammed oracle shifted back by `D`. With `D = 0` it is the simulator's response. -/
def simShifted (D H : X → Y) (x : Stmt) (s : SaltedCoins Sd SC) :
    Quantum.EnvReply Proof (X → Y) :=
  let r := S.run (H - D) x s
  ⟨some r.proof, (H - D).reprogram r.assignments + D⟩

/-- **The environments of step `j`.** The tape is a hybrid tape and proof query `j`'s randomness
`τ : R`. The initial oracle is `H + D ω`; a valid proof query numbered below `j` is answered by the
simulator on the oracle in force shifted back by `D ω` (`simShifted`), proof query `j` by `resp`,
and a valid later proof query by the honest prover on the oracle in force. -/
noncomputable def stepEnv {R : Type*} [Fintype R] [Nonempty R] (j : Fin Q)
    (D : HTape X Y Sd C SC Q × R → X → Y)
    (resp : HTape X Y Sd C SC Q × R → ProofQuery Stmt Wit → (X → Y) → Quantum.EnvReply Proof (X → Y)) :
    Quantum.Env (HTape X Y Sd C SC Q × R) (ProofQuery Stmt Wit) Proof X Y Q where
  μ := PMF.uniformOfFintype _
  oracle₀ ω := ω.1.oracle + D ω
  respond ω i req H :=
    if (i : ℕ) < j then
      if rel req.stmt req.wit then simShifted S (D ω) H req.stmt (ω.1.simCoins i) else ⟨none, H⟩
    else if i = j then resp ω req H
    else if rel req.stmt req.wit then ⟨some (P.prove H req.stmt req.wit (ω.1.proverCoins i)), H⟩
    else ⟨none, H⟩

/-- The shift of proof query `j`'s slice by the salt of its fresh draw: `F - H` on the inputs of that
salt. -/
def freshShift {Cx : Type*} (ω : HTape X Y Sd C SC Q × FreshSlice X Y (SaltedCoins Sd Cx)) :
    X → Y :=
  sliceShift saltOf ω.2.coins.salt ω.1.oracle ω.2.slice

/-- Proof query `j` answered by the prover on the oracle in force. -/
def respProver (ω : HTape X Y Sd C SC Q × FreshSlice X Y (SaltedCoins Sd C))
    (req : ProofQuery Stmt Wit) (H : X → Y) : Quantum.EnvReply Proof (X → Y) :=
  if rel req.stmt req.wit then ⟨some (P.prove H req.stmt req.wit ω.2.coins), H⟩ else ⟨none, H⟩

/-- Proof query `j` answered by the prover on the oracle in force with the fresh slice, which becomes
the oracle in force. -/
def respProverFresh (ω : HTape X Y Sd C SC Q × FreshSlice X Y (SaltedCoins Sd C))
    (req : ProofQuery Stmt Wit) (H : X → Y) : Quantum.EnvReply Proof (X → Y) :=
  respProver rel P ω req (H + freshShift saltOf ω)

/-- Proof query `j` answered by the simulator on the oracle in force, which it reprograms. -/
def respSim (ω : HTape X Y Sd C SC Q × FreshSlice X Y (SaltedCoins Sd SC))
    (req : ProofQuery Stmt Wit) (H : X → Y) : Quantum.EnvReply Proof (X → Y) :=
  if rel req.stmt req.wit then
    let r := S.run H req.stmt ω.2.coins
    ⟨some r.proof, H.reprogram r.assignments⟩
  else ⟨none, H⟩

/-- Proof query `j` answered by the simulator on the oracle in force with the fresh slice. -/
def respSimFresh (ω : HTape X Y Sd C SC Q × FreshSlice X Y (SaltedCoins Sd SC))
    (req : ProofQuery Stmt Wit) (H : X → Y) : Quantum.EnvReply Proof (X → Y) :=
  respSim rel S ω req (H + freshShift saltOf ω)

/-- The relabelling of a step tape with the prover's coins at proof query `j`: the hybrid tape with
proof query `j`'s prover coins from the fresh draw and the oracle's slice of their salt answered by
the fresh slice. -/
def relabelP (j : Fin Q) (ω : HTape X Y Sd C SC Q × FreshSlice X Y (SaltedCoins Sd C)) :
    HTape X Y Sd C SC Q :=
  ⟨replaceSlice saltOf ω.2.coins.salt ω.1.oracle ω.2.slice,
    Function.update ω.1.proverCoins j ω.2.coins, ω.1.simCoins⟩

/-- The relabelling with the simulator's coins at proof query `j`. -/
def relabelS (j : Fin Q) (ω : HTape X Y Sd C SC Q × FreshSlice X Y (SaltedCoins Sd SC)) :
    HTape X Y Sd C SC Q :=
  ⟨replaceSlice saltOf ω.2.coins.salt ω.1.oracle ω.2.slice, ω.1.proverCoins,
    Function.update ω.1.simCoins j ω.2.coins⟩

/-- The relabelling pushes the uniform step tape to the uniform hybrid tape. -/
theorem map_relabelP (j : Fin Q) :
    (PMF.uniformOfFintype (HTape X Y Sd C SC Q × FreshSlice X Y (SaltedCoins Sd C))).map
      (relabelP saltOf j) = PMF.uniformOfFintype (HTape X Y Sd C SC Q) := by
  let e : HTape X Y Sd C SC Q × FreshSlice X Y (SaltedCoins Sd C) ≃
      HTape X Y Sd C SC Q × FreshSlice X Y (SaltedCoins Sd C) :=
    { toFun := fun ω => (relabelP saltOf j ω,
        ⟨ω.1.proverCoins j, replaceSlice saltOf ω.2.coins.salt ω.2.slice ω.1.oracle⟩)
      invFun := fun ω => (⟨replaceSlice saltOf (ω.1.proverCoins j).salt ω.1.oracle ω.2.slice,
          Function.update ω.1.proverCoins j ω.2.coins, ω.1.simCoins⟩,
        ⟨ω.1.proverCoins j, replaceSlice saltOf (ω.1.proverCoins j).salt ω.2.slice ω.1.oracle⟩)
      left_inv := fun ω => by
        obtain ⟨⟨H, pc, sc⟩, c, F⟩ := ω
        simp [relabelP, replaceSlice_replaceSlice_left, replaceSlice_replaceSlice_right,
          replaceSlice_self]
      right_inv := fun ω => by
        obtain ⟨⟨H, pc, sc⟩, c, F⟩ := ω
        simp [relabelP, replaceSlice_replaceSlice_left, replaceSlice_replaceSlice_right,
          replaceSlice_self] }
  have h : relabelP saltOf j = Prod.fst ∘ e := rfl
  rw [h, ← PMF.map_comp, PMF.map_uniformOfFintype_equiv, PMF.map_fst_uniformOfFintype]

theorem map_relabelS (j : Fin Q) :
    (PMF.uniformOfFintype (HTape X Y Sd C SC Q × FreshSlice X Y (SaltedCoins Sd SC))).map
      (relabelS saltOf j) = PMF.uniformOfFintype (HTape X Y Sd C SC Q) := by
  let e : HTape X Y Sd C SC Q × FreshSlice X Y (SaltedCoins Sd SC) ≃
      HTape X Y Sd C SC Q × FreshSlice X Y (SaltedCoins Sd SC) :=
    { toFun := fun ω => (relabelS saltOf j ω,
        ⟨ω.1.simCoins j, replaceSlice saltOf ω.2.coins.salt ω.2.slice ω.1.oracle⟩)
      invFun := fun ω => (⟨replaceSlice saltOf (ω.1.simCoins j).salt ω.1.oracle ω.2.slice,
          ω.1.proverCoins, Function.update ω.1.simCoins j ω.2.coins⟩,
        ⟨ω.1.simCoins j, replaceSlice saltOf (ω.1.simCoins j).salt ω.2.slice ω.1.oracle⟩)
      left_inv := fun ω => by
        obtain ⟨⟨H, pc, sc⟩, c, F⟩ := ω
        simp [relabelS, replaceSlice_replaceSlice_left, replaceSlice_replaceSlice_right,
          replaceSlice_self]
      right_inv := fun ω => by
        obtain ⟨⟨H, pc, sc⟩, c, F⟩ := ω
        simp [relabelS, replaceSlice_replaceSlice_left, replaceSlice_replaceSlice_right,
          replaceSlice_self] }
  have h : relabelS saltOf j = Prod.fst ∘ e := rfl
  rw [h, ← PMF.map_comp, PMF.map_uniformOfFintype_equiv, PMF.map_fst_uniformOfFintype]

/-- With uniform coins the hybrid tape is uniform. -/
theorem hybridLaw_eq_uniform (hloc : SaltedLocal saltOf P S) :
    hybridLaw (X := X) (Y := Y) Q P.coins S.coins = PMF.uniformOfFintype (HTape X Y Sd C SC Q) := by
  rw [hybridLaw, hloc.coins_eq, S.coins_eq_uniform, PMF.pi_uniformOfFintype,
    PMF.pi_uniformOfFintype, HybridTape.uniformOfFintype_eq_bind]

/-- Hybrid `j` on the relabelled step tape with the prover's coins at proof query `j`. -/
noncomputable def relabelEnvP (j : Fin Q) :
    Quantum.Env (HTape X Y Sd C SC Q × FreshSlice X Y (SaltedCoins Sd C)) (ProofQuery Stmt Wit) Proof X Y Q where
  μ := PMF.uniformOfFintype _
  oracle₀ ω := (relabelP saltOf j ω).oracle
  respond ω := (hybridEnv rel P S Q j).respond (relabelP saltOf j ω)

/-- Hybrid `j + 1` on the relabelled step tape with the simulator's coins at proof query `j`. -/
noncomputable def relabelEnvS (j : Fin Q) :
    Quantum.Env (HTape X Y Sd C SC Q × FreshSlice X Y (SaltedCoins Sd SC)) (ProofQuery Stmt Wit) Proof X Y Q where
  μ := PMF.uniformOfFintype _
  oracle₀ ω := (relabelS saltOf j ω).oracle
  respond ω := (hybridEnv rel P S Q (j + 1)).respond (relabelS saltOf j ω)

theorem acceptProbOn_hybridEnv_eq_relabelP (hloc : SaltedLocal saltOf P S) (j : Fin Q)
    (L : Set (Quantum.LogReg (ProofQuery Stmt Wit) m)) :
    D.acceptProbOn (hybridEnv rel P S Q j) post L =
      D.acceptProbOn (relabelEnvP saltOf rel P S j) post L :=
  (D.acceptProbOn_comap post (relabelP saltOf j)
    (by simp only [hybridEnv, relabelEnvP, hybridLaw_eq_uniform saltOf P S hloc, map_relabelP])
    (fun _ => rfl) (fun _ => rfl) L).symm

theorem acceptProbOn_hybridEnv_eq_relabelS (hloc : SaltedLocal saltOf P S) (j : Fin Q)
    (L : Set (Quantum.LogReg (ProofQuery Stmt Wit) m)) :
    D.acceptProbOn (hybridEnv rel P S Q (j + 1)) post L =
      D.acceptProbOn (relabelEnvS saltOf rel P S j) post L :=
  (D.acceptProbOn_comap post (relabelS saltOf j)
    (by simp only [hybridEnv, relabelEnvS, hybridLaw_eq_uniform saltOf P S hloc, map_relabelS])
    (fun _ => rfl) (fun _ => rfl) L).symm

section StepEnv

variable {R : Type*} [Fintype R] [Nonempty R] (j : Fin Q)

theorem stepEnv_respond_lt (D' : HTape X Y Sd C SC Q × R → X → Y)
    (resp : HTape X Y Sd C SC Q × R → ProofQuery Stmt Wit → (X → Y) → Quantum.EnvReply Proof (X → Y))
    (ω : HTape X Y Sd C SC Q × R) {i : Fin Q} (hi : (i : ℕ) < j) (req : ProofQuery Stmt Wit) (H : X → Y) :
    (stepEnv rel P S j D' resp).respond ω i req H =
      if rel req.stmt req.wit then simShifted S (D' ω) H req.stmt (ω.1.simCoins i) else ⟨none, H⟩ := by
  simp only [stepEnv]
  rw [if_pos hi]

theorem stepEnv_respond_self (D' : HTape X Y Sd C SC Q × R → X → Y)
    (resp : HTape X Y Sd C SC Q × R → ProofQuery Stmt Wit → (X → Y) → Quantum.EnvReply Proof (X → Y))
    (ω : HTape X Y Sd C SC Q × R) (req : ProofQuery Stmt Wit) (H : X → Y) :
    (stepEnv rel P S j D' resp).respond ω j req H = resp ω req H := by
  simp [stepEnv]

theorem stepEnv_respond_gt (D' : HTape X Y Sd C SC Q × R → X → Y)
    (resp : HTape X Y Sd C SC Q × R → ProofQuery Stmt Wit → (X → Y) → Quantum.EnvReply Proof (X → Y))
    (ω : HTape X Y Sd C SC Q × R) {i : Fin Q} (hi : (j : ℕ) < i) (req : ProofQuery Stmt Wit) (H : X → Y) :
    (stepEnv rel P S j D' resp).respond ω i req H =
      if rel req.stmt req.wit then ⟨some (P.prove H req.stmt req.wit (ω.1.proverCoins i)), H⟩ else ⟨none, H⟩ := by
  have h1 : ¬ (i : ℕ) < j := by omega
  have h2 : i ≠ j := fun e => by subst e; omega
  simp only [stepEnv]
  rw [if_neg h1, if_neg h2]

/-- Before proof query `j`, the shifted environment's oracle is the unshifted one's plus the
shift. -/
theorem stepEnv_oracleIn_shift (D' : HTape X Y Sd C SC Q × R → X → Y)
    (resp resp' : HTape X Y Sd C SC Q × R → ProofQuery Stmt Wit → (X → Y) → Quantum.EnvReply Proof (X → Y))
    (ω : HTape X Y Sd C SC Q × R) :
    ∀ rs : List (ProofQuery Stmt Wit), rs.length ≤ j →
      (stepEnv rel P S j D' resp).oracleIn ω rs = (stepEnv rel P S j 0 resp').oracleIn ω rs + D' ω := by
  intro rs
  induction rs using List.reverseRecOn with
  | nil =>
    intro _
    simp [Quantum.Env.oracleIn_nil, stepEnv]
  | append_singleton l a ih =>
    intro hl
    have hlt : l.length < j := by simp at hl; omega
    have hQ : l.length < Q := hlt.trans j.2
    rw [Quantum.Env.oracleIn_append_singleton, Quantum.Env.oracleIn_append_singleton, ih (by omega)]
    simp only [Quantum.Env.update, dif_pos hQ]
    rw [stepEnv_respond_lt rel P S j _ _ ω (i := ⟨l.length, hQ⟩) hlt,
      stepEnv_respond_lt rel P S j _ _ ω (i := ⟨l.length, hQ⟩) hlt]
    split_ifs
    · simp [simShifted]
    · rfl

/-- Before proof query `j`, the shifted and unshifted environments give the same answers. -/
theorem stepEnv_answerAfter_shift (D' : HTape X Y Sd C SC Q × R → X → Y)
    (resp resp' : HTape X Y Sd C SC Q × R → ProofQuery Stmt Wit → (X → Y) → Quantum.EnvReply Proof (X → Y))
    (ω : HTape X Y Sd C SC Q × R) {rs : List (ProofQuery Stmt Wit)} (hrs : rs.length < j)
    (req : ProofQuery Stmt Wit) :
    (stepEnv rel P S j D' resp).answerAfter ω rs req =
      (stepEnv rel P S j 0 resp').answerAfter ω rs req := by
  have hQ : rs.length < Q := hrs.trans j.2
  simp only [Quantum.Env.answerAfter, dif_pos hQ]
  rw [stepEnv_respond_lt rel P S j _ _ ω (i := ⟨rs.length, hQ⟩) hrs,
    stepEnv_respond_lt rel P S j _ _ ω (i := ⟨rs.length, hQ⟩) hrs,
    stepEnv_oracleIn_shift rel P S j D' resp resp' ω rs hrs.le]
  split_ifs
  · simp [simShifted]
  · rfl

/-- From proof query `j` on, the shifted and unshifted environments agree if proof query `j`'s responses
correspond under the shift. -/
theorem stepEnv_oracleIn_of_resp (D' : HTape X Y Sd C SC Q × R → X → Y)
    (resp resp' : HTape X Y Sd C SC Q × R → ProofQuery Stmt Wit → (X → Y) → Quantum.EnvReply Proof (X → Y))
    (ω : HTape X Y Sd C SC Q × R) (hresp : ∀ req O, resp ω req (O + D' ω) = resp' ω req O) :
    ∀ rs : List (ProofQuery Stmt Wit), j < rs.length →
      (stepEnv rel P S j D' resp).oracleIn ω rs = (stepEnv rel P S j 0 resp').oracleIn ω rs := by
  intro rs
  induction rs using List.reverseRecOn with
  | nil => intro h; simp at h
  | append_singleton l a ih =>
    intro hl
    rw [Quantum.Env.oracleIn_append_singleton, Quantum.Env.oracleIn_append_singleton]
    simp only [List.length_append, List.length_singleton] at hl
    rcases Nat.lt_succ_iff_lt_or_eq.1 hl with hlt | heq
    · rw [ih hlt]
      simp only [Quantum.Env.update]
      split_ifs with hQ
      · rw [stepEnv_respond_gt rel P S j _ _ ω (i := ⟨l.length, hQ⟩) hlt,
          stepEnv_respond_gt rel P S j _ _ ω (i := ⟨l.length, hQ⟩) hlt]
      · rfl
    · have hQ : l.length < Q := heq ▸ j.2
      have hj : (⟨l.length, hQ⟩ : Fin Q) = j := Fin.ext heq.symm
      simp only [Quantum.Env.update, dif_pos hQ, hj, stepEnv_respond_self,
        stepEnv_oracleIn_shift rel P S j D' resp resp' ω l heq.symm.le, hresp]

/-- The shifted and unshifted environments give the same answers if proof query `j`'s responses
correspond under the shift. -/
theorem stepEnv_answerAfter_of_resp (D' : HTape X Y Sd C SC Q × R → X → Y)
    (resp resp' : HTape X Y Sd C SC Q × R → ProofQuery Stmt Wit → (X → Y) → Quantum.EnvReply Proof (X → Y))
    (ω : HTape X Y Sd C SC Q × R) (hresp : ∀ req O, resp ω req (O + D' ω) = resp' ω req O)
    (rs : List (ProofQuery Stmt Wit)) (req : ProofQuery Stmt Wit) :
    (stepEnv rel P S j D' resp).answerAfter ω rs req =
      (stepEnv rel P S j 0 resp').answerAfter ω rs req := by
  rcases lt_trichotomy rs.length j with hlt | heq | hgt
  · exact stepEnv_answerAfter_shift rel P S j D' resp resp' ω hlt req
  · have hQ : rs.length < Q := heq ▸ j.2
    have hj : (⟨rs.length, hQ⟩ : Fin Q) = j := Fin.ext heq
    simp only [Quantum.Env.answerAfter, dif_pos hQ, hj, stepEnv_respond_self,
      stepEnv_oracleIn_shift rel P S j D' resp resp' ω rs heq.le, hresp]
  · simp only [Quantum.Env.answerAfter, stepEnv_oracleIn_of_resp rel P S j D' resp resp' ω hresp rs hgt]
    split_ifs with hQ
    · rw [stepEnv_respond_gt rel P S j _ _ ω (i := ⟨rs.length, hQ⟩) hgt,
        stepEnv_respond_gt rel P S j _ _ ω (i := ⟨rs.length, hQ⟩) hgt]
    · rfl

/-- The unshifted environment before proof query `j` does not read proof query `j`'s randomness. -/
theorem stepEnv_oracleIn_fresh
    (resp : HTape X Y Sd C SC Q × R → ProofQuery Stmt Wit → (X → Y) → Quantum.EnvReply Proof (X → Y))
    (v : HTape X Y Sd C SC Q) (τ τ' : R) {rs : List (ProofQuery Stmt Wit)} (hrs : rs.length ≤ j) :
    (stepEnv rel P S j 0 resp).oracleIn (v, τ) rs = (stepEnv rel P S j 0 resp).oracleIn (v, τ') rs := by
  refine Quantum.Env.oracleIn_eq_of_update_eq _ _ (by simp [stepEnv]) rs fun i hi => ?_
  simp only [Quantum.Env.update]
  split_ifs with hQ
  · have hij : i < j := by omega
    rw [stepEnv_respond_lt rel P S j _ _ _ (i := ⟨i, hQ⟩) hij,
      stepEnv_respond_lt rel P S j _ _ _ (i := ⟨i, hQ⟩) hij]
    rfl
  · rfl

theorem stepEnv_answerAfter_fresh
    (resp : HTape X Y Sd C SC Q × R → ProofQuery Stmt Wit → (X → Y) → Quantum.EnvReply Proof (X → Y))
    (v : HTape X Y Sd C SC Q) (τ τ' : R) {rs : List (ProofQuery Stmt Wit)} (hrs : rs.length < j)
    (req : ProofQuery Stmt Wit) :
    (stepEnv rel P S j 0 resp).answerAfter (v, τ) rs req =
      (stepEnv rel P S j 0 resp).answerAfter (v, τ') rs req := by
  have hQ : rs.length < Q := hrs.trans j.2
  simp only [Quantum.Env.answerAfter, dif_pos hQ, stepEnv_oracleIn_fresh rel P S j resp v τ τ' hrs.le]
  rw [stepEnv_respond_lt rel P S j _ _ _ (i := ⟨rs.length, hQ⟩) hrs,
    stepEnv_respond_lt rel P S j _ _ _ (i := ⟨rs.length, hQ⟩) hrs]
  rfl

end StepEnv

/-! ### The pieces of one step -/

section Pieces

variable {R : Type*} [Fintype R] [Nonempty R]

/-- A simulator with a salt other than `σ` does not see a shift on the slice of `σ`. -/
theorem simShifted_eq_of_ne (hloc : SaltedLocal saltOf P S) {D' : X → Y} {σ : Sd}
    (hD : ∀ y, saltOf y ≠ some σ → D' y = 0) {s : SaltedCoins Sd SC} (hne : s.salt ≠ σ)
    (H : X → Y) (x : Stmt) :
    simShifted S D' H x s = ⟨some (S.run H x s).proof, H.reprogram (S.run H x s).assignments⟩ := by
  have hrun : S.run (H - D') x s = S.run H x s := hloc.run_congr _ _ x s fun y hy => by
    have : saltOf y ≠ some σ := by
      rcases hy with h | h
      · rw [h]
        simp
      · rw [h]
        exact fun h' => hne (Option.some_inj.1 h')
    simp [hD y this]
  simp only [simShifted, hrun]
  congr 1
  rw [← reprogram_add (H - D') D' fun a ha => hD _ (by rw [hloc.run_salt H x s a ha]; simpa using hne),
    sub_add_cancel]

theorem sliceShift_eq_zero {σ : Sd} {H F : X → Y} {y : X} (hy : saltOf y ≠ some σ) :
    sliceShift saltOf σ H F y = 0 := by
  simp [sliceShift, hy]

/-- **The salt-collision step for the prover.** Hybrid `j` relabelled with the prover's coins at
proof query `j` agrees with the shifted environment unless an earlier simulator drew the prover's salt.
-/
theorem relabelEnvP_eq_off (hloc : SaltedLocal saltOf P S) (j : Fin Q)
    (ω : HTape X Y Sd C SC Q × FreshSlice X Y (SaltedCoins Sd C))
    (hω : ω ∉ {ω : HTape X Y Sd C SC Q × FreshSlice X Y (SaltedCoins Sd C) |
      ∃ i : Fin Q, (i : ℕ) < j ∧ (ω.1.simCoins i).salt = ω.2.coins.salt}) :
    (relabelEnvP saltOf rel P S j).oracle₀ ω = (stepEnv rel P S j (freshShift saltOf)
        (respProver rel P)).oracle₀ ω ∧
      (relabelEnvP saltOf rel P S j).respond ω = (stepEnv rel P S j (freshShift saltOf)
        (respProver rel P)).respond ω := by
  refine ⟨replaceSlice_eq_add saltOf _ _ _, funext fun i => funext fun req => funext fun Hin => ?_⟩
  simp only [relabelEnvP, hybridEnv, relabelP]
  rcases lt_trichotomy (i : ℕ) j with hi | hi | hi
  · rw [stepEnv_respond_lt rel P S j _ _ ω hi]
    by_cases hrel : rel req.stmt req.wit
    · have hne : (ω.1.simCoins i).salt ≠ ω.2.coins.salt := fun h => hω ⟨i, hi, h⟩
      simp only [hrel, ite_true, hi]
      exact (simShifted_eq_of_ne saltOf P S hloc (D' := freshShift saltOf ω) (σ := ω.2.coins.salt)
        (fun y hy => sliceShift_eq_zero saltOf hy) hne Hin req.stmt).symm
    · simp [hrel]
  · have hij : i = j := Fin.ext hi
    subst hij
    rw [stepEnv_respond_self]
    by_cases hrel : rel req.stmt req.wit <;> simp [hrel, respProver]
  · rw [stepEnv_respond_gt rel P S j _ _ ω hi]
    have h1 : ¬ (i : ℕ) < j := by omega
    have h2 : i ≠ j := fun e => by subst e; omega
    by_cases hrel : rel req.stmt req.wit <;> simp [hrel, h1, Function.update_of_ne h2]

/-- **The salt-collision step for the simulator.** -/
theorem relabelEnvS_eq_off (hloc : SaltedLocal saltOf P S) (j : Fin Q)
    (ω : HTape X Y Sd C SC Q × FreshSlice X Y (SaltedCoins Sd SC))
    (hω : ω ∉ {ω : HTape X Y Sd C SC Q × FreshSlice X Y (SaltedCoins Sd SC) |
      ∃ i : Fin Q, (i : ℕ) < j ∧ (ω.1.simCoins i).salt = ω.2.coins.salt}) :
    (relabelEnvS saltOf rel P S j).oracle₀ ω = (stepEnv rel P S j (freshShift saltOf)
        (respSim rel S)).oracle₀ ω ∧
      (relabelEnvS saltOf rel P S j).respond ω = (stepEnv rel P S j (freshShift saltOf)
        (respSim rel S)).respond ω := by
  refine ⟨replaceSlice_eq_add saltOf _ _ _, funext fun i => funext fun req => funext fun Hin => ?_⟩
  simp only [relabelEnvS, hybridEnv, relabelS]
  rcases lt_trichotomy (i : ℕ) j with hi | hi | hi
  · rw [stepEnv_respond_lt rel P S j _ _ ω hi]
    have h1 : (i : ℕ) < (j : ℕ) + 1 := by omega
    have h2 : i ≠ j := fun e => by subst e; omega
    by_cases hrel : rel req.stmt req.wit
    · have hne : (ω.1.simCoins i).salt ≠ ω.2.coins.salt := fun h => hω ⟨i, hi, h⟩
      simp only [hrel, ite_true, h1, Function.update_of_ne h2]
      exact (simShifted_eq_of_ne saltOf P S hloc (D' := freshShift saltOf ω) (σ := ω.2.coins.salt)
        (fun y hy => sliceShift_eq_zero saltOf hy) hne Hin req.stmt).symm
    · simp [hrel]
  · have hij : i = j := Fin.ext hi
    subst hij
    rw [stepEnv_respond_self]
    by_cases hrel : rel req.stmt req.wit <;> simp [hrel, respSim]
  · rw [stepEnv_respond_gt rel P S j _ _ ω hi]
    have h1 : ¬ (i : ℕ) < (j : ℕ) + 1 := by omega
    by_cases hrel : rel req.stmt req.wit <;> simp [hrel, h1]

/-- **A fresh salt meets a fixed one with probability `1 / |Sd|`**: over a uniform hybrid tape
and a uniform fresh draw, the fresh salt equals a function of the tape with probability
`1 / |Sd|`. -/
theorem prob_freshSalt_eq {Cx : Type*} [Fintype Cx] [Nonempty Cx] (f : HTape X Y Sd C SC Q → Sd) :
    ((PMF.uniformOfFintype (HTape X Y Sd C SC Q × FreshSlice X Y (SaltedCoins Sd Cx))).toOuterMeasure
      {ω | f ω.1 = ω.2.coins.salt}).toReal = (Fintype.card Sd : ℝ)⁻¹ := by
  classical
  have hT : ∀ v : HTape X Y Sd C SC Q, ∑ τ : FreshSlice X Y (SaltedCoins Sd Cx),
      (if f v = τ.coins.salt then ((Fintype.card (HTape X Y Sd C SC Q) *
        Fintype.card (FreshSlice X Y (SaltedCoins Sd Cx)) : ℕ) : ℝ)⁻¹ else 0) =
        (Fintype.card (HTape X Y Sd C SC Q) : ℝ)⁻¹ * (Fintype.card Sd : ℝ)⁻¹ := fun v => by
    have h := FreshSlice.prob_salt_eq (X := X) (Y := Y) (C := Cx) (f v)
    rw [PMF.toReal_toOuterMeasure_apply] at h
    simp only [Set.mem_ofPred_eq, PMF.toReal_uniformOfFintype_apply] at h
    rw [← h, Finset.mul_sum]
    refine Finset.sum_congr rfl fun τ _ => ?_
    by_cases hτ : τ.coins.salt = f v
    · rw [if_pos hτ.symm, if_pos hτ, Nat.cast_mul, mul_inv]
    · rw [if_neg (Ne.symm hτ), if_neg hτ, mul_zero]
  rw [PMF.toReal_toOuterMeasure_apply, Fintype.sum_prod_type]
  simp only [Set.mem_ofPred_eq, PMF.toReal_uniformOfFintype_apply, Fintype.card_prod]
  rw [Finset.sum_congr rfl fun v _ => hT v, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have : (Fintype.card (HTape X Y Sd C SC Q) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  field_simp

/-- **The probability of a salt collision**: some proof query numbered below `j` drew the salt of
proof query `j`, at most `j / |Sd|`. -/
theorem prob_saltCollision_le {Cx : Type*} [Fintype Cx] [Nonempty Cx] (j : ℕ) :
    ((PMF.uniformOfFintype (HTape X Y Sd C SC Q × FreshSlice X Y (SaltedCoins Sd Cx))).toOuterMeasure
      {ω | ∃ i : Fin Q, (i : ℕ) < j ∧ (ω.1.simCoins i).salt = ω.2.coins.salt}).toReal ≤
        j / Fintype.card Sd := by
  classical
  have hset : {ω : HTape X Y Sd C SC Q × FreshSlice X Y (SaltedCoins Sd Cx) |
      ∃ i : Fin Q, (i : ℕ) < j ∧ (ω.1.simCoins i).salt = ω.2.coins.salt} =
      ⋃ i : Fin Q, {ω | (i : ℕ) < j ∧ (ω.1.simCoins i).salt = ω.2.coins.salt} := by
    ext ω
    simp
  rw [hset]
  refine (PMF.toReal_toOuterMeasure_iUnion_le _ _).trans ?_
  calc ∑ i : Fin Q, ((PMF.uniformOfFintype (HTape X Y Sd C SC Q ×
        FreshSlice X Y (SaltedCoins Sd Cx))).toOuterMeasure
        {ω | (i : ℕ) < j ∧ (ω.1.simCoins i).salt = ω.2.coins.salt}).toReal
      ≤ ∑ i : Fin Q, if (i : ℕ) < j then (Fintype.card Sd : ℝ)⁻¹ else 0 :=
        Finset.sum_le_sum fun i _ => by
          split_ifs with hi
          · simp only [hi, true_and]
            exact (prob_freshSalt_eq fun v => (v.simCoins i).salt).le
          · simp [hi]
    _ = (Finset.univ.filter fun i : Fin Q => (i : ℕ) < j).card * (Fintype.card Sd : ℝ)⁻¹ := by
        rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
    _ ≤ j / Fintype.card Sd := by
        rw [div_eq_mul_inv]
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        have : (Finset.univ.filter fun i : Fin Q => (i : ℕ) < j).card ≤ j := by
          calc (Finset.univ.filter fun i : Fin Q => (i : ℕ) < j).card
              ≤ ((Finset.range j).filter fun i => i < Q).card := by
                refine Finset.card_le_card_of_injOn (fun i => (i : ℕ)) (fun i hi => ?_)
                  (fun a _ b _ h => Fin.ext h)
                simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hi
                simp [hi, i.2]
            _ ≤ (Finset.range j).card := Finset.card_filter_le _ _
            _ = j := Finset.card_range j
        exact_mod_cast this

/-- A shift of the slice by `F - H` from `O` has the law of a replacement of the slice of `O` by a
uniform function. -/
theorem map_shift_eq {Cx β : Type*} [Fintype Cx] [Nonempty Cx] (H O : X → Y)
    (g : SaltedCoins Sd Cx → (X → Y) → β) :
    (PMF.uniformOfFintype (FreshSlice X Y (SaltedCoins Sd Cx))).map
        (fun τ => g τ.coins (O + sliceShift saltOf τ.coins.salt H τ.slice)) =
      (PMF.uniformOfFintype (FreshSlice X Y (SaltedCoins Sd Cx))).map
        (fun τ => g τ.coins (replaceSlice saltOf τ.coins.salt O τ.slice)) := by
  let e : FreshSlice X Y (SaltedCoins Sd Cx) ≃ FreshSlice X Y (SaltedCoins Sd Cx) :=
    { toFun := fun τ => ⟨τ.coins, τ.slice + (O - H)⟩
      invFun := fun τ => ⟨τ.coins, τ.slice - (O - H)⟩
      left_inv := fun τ => by simp
      right_inv := fun τ => by simp }
  conv_rhs => rw [← PMF.map_uniformOfFintype_equiv e, PMF.map_comp]
  congr 1
  funext τ
  simp only [Function.comp_apply, e, Equiv.coe_fn_mk]
  congr 1
  funext x
  by_cases hx : saltOf x = some τ.coins.salt
  · simp only [replaceSlice, sliceShift, hx, ite_true, Pi.add_apply, Pi.sub_apply]
    abel
  · simp [replaceSlice, sliceShift, hx]

/-- Before proof query `j`, the unshifted environment's oracle agrees with the initial oracle on the
salt-free inputs. -/
theorem stepEnv_oracleIn_unsalted (hloc : SaltedLocal saltOf P S) (j : Fin Q)
    (resp : HTape X Y Sd C SC Q × R → ProofQuery Stmt Wit → (X → Y) → Quantum.EnvReply Proof (X → Y))
    (ω : HTape X Y Sd C SC Q × R) :
    ∀ rs : List (ProofQuery Stmt Wit), rs.length ≤ j → ∀ y, saltOf y = none →
      (stepEnv rel P S j 0 resp).oracleIn ω rs y = ω.1.oracle y := by
  intro rs
  induction rs using List.reverseRecOn with
  | nil =>
    intro _ y _
    simp [Quantum.Env.oracleIn_nil, stepEnv]
  | append_singleton l a ih =>
    intro hl y hy
    have hlt : l.length < j := by simp at hl; omega
    have hQ : l.length < Q := hlt.trans j.2
    rw [Quantum.Env.oracleIn_append_singleton]
    simp only [Quantum.Env.update, dif_pos hQ]
    rw [stepEnv_respond_lt rel P S j _ _ ω (i := ⟨l.length, hQ⟩) hlt]
    split_ifs
    · simp only [simShifted, Pi.zero_apply, sub_zero, add_zero]
      rw [reprogram_apply_of_forall_ne _ fun b hb heq => by
          have := hloc.run_salt _ a.stmt _ b hb
          rw [heq, hy] at this
          exact absurd this (by simp),
        ih (by omega) y hy]
    · exact ih (by omega) y hy

/-- The salt of a uniform fresh draw lies in the salt slot of a fixed input with probability at
most `1 / |Sd|`. -/
theorem prob_saltSlot_le {Cx : Type*} [Fintype Cx] [Nonempty Cx] (x : X) :
    ((PMF.uniformOfFintype (FreshSlice X Y (SaltedCoins Sd Cx))).toOuterMeasure
      {τ | x ∈ {y | saltOf y = some τ.coins.salt}}).toReal ≤ (Fintype.card Sd : ℝ)⁻¹ := by
  classical
  rcases hx : saltOf x with _ | s
  · simp [hx]
  · have hset : {τ : FreshSlice X Y (SaltedCoins Sd Cx) | x ∈ {y | saltOf y = some τ.coins.salt}} =
        {τ | τ.coins.salt = s} := by
      ext τ
      simp [hx, eq_comm]
    rw [hset, FreshSlice.prob_salt_eq]

/-- The uniform law on a product of a hybrid tape and proof query `j`'s randomness. -/
theorem uniformOfFintype_step_apply (v : HTape X Y Sd C SC Q) (τ : R) :
    PMF.uniformOfFintype (HTape X Y Sd C SC Q × R) (v, τ) =
      PMF.uniformOfFintype (HTape X Y Sd C SC Q) v * PMF.uniformOfFintype R τ := by
  simp [PMF.uniformOfFintype_apply, Fintype.card_prod, ENNReal.mul_inv]

/-- The average of a function of the oracle over the uniform hybrid tape. -/
theorem sum_uniform_htape_eq_expect (η : (X → Y) → ℝ) :
    ∑ v : HTape X Y Sd C SC Q, (PMF.uniformOfFintype (HTape X Y Sd C SC Q) v).toReal * η v.oracle =
      𝔼[H ← (X → Y) : η H] := by
  rw [HybridTape.sum_eq, Finset.expect_eq_sum_div_card]
  simp only [PMF.toReal_uniformOfFintype_apply, HybridTape.card_eq, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, Nat.cast_mul]
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun H _ => ?_
  have h : ((Fintype.card ((Fin Q → SaltedCoins Sd C) × (Fin Q → SaltedCoins Sd SC))) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.2 Fintype.card_ne_zero
  field_simp

end Pieces

theorem hybridEnv_respond_lt (j : ℕ) (ω : HTape X Y Sd C SC Q) {i : Fin Q} (hi : (i : ℕ) < j)
    (req : ProofQuery Stmt Wit) (H : X → Y) :
    (hybridEnv rel P S Q j).respond ω i req H =
      if rel req.stmt req.wit then
        ⟨some (S.run H req.stmt (ω.simCoins i)).proof,
          H.reprogram (S.run H req.stmt (ω.simCoins i)).assignments⟩
      else ⟨none, H⟩ := by
  simp only [hybridEnv, hi, ite_true]

/-- **The two hybrids agree on the branches that never make proof query `j`.** -/
theorem acceptProbOn_hybridEnv_notMade (j : Fin Q) :
    D.acceptProbOn (hybridEnv rel P S Q j) post (Quantum.madeLogs (j : ℕ))ᶜ =
      D.acceptProbOn (hybridEnv rel P S Q (j + 1)) post (Quantum.madeLogs (j : ℕ))ᶜ := by
  have horacle : ∀ ω (rs : List (ProofQuery Stmt Wit)), rs.length ≤ j →
      (hybridEnv rel P S Q j).oracleIn ω rs = (hybridEnv rel P S Q (j + 1)).oracleIn ω rs :=
    fun ω rs hrs => Quantum.Env.oracleIn_eq_of_update_eq (hybridEnv rel P S Q j)
      (hybridEnv rel P S Q (j + 1)) rfl rs fun i hi => by
        simp only [Quantum.Env.update]
        split_ifs with hQ
        · rw [hybridEnv_respond_lt rel P S j ω (i := ⟨i, hQ⟩) (by simp; omega),
            hybridEnv_respond_lt rel P S (j + 1) ω (i := ⟨i, hQ⟩) (by simp; omega)]
        · rfl
  have hans : ∀ ω (rs : List (ProofQuery Stmt Wit)) req, rs.length < j →
      (hybridEnv rel P S Q j).answerAfter ω rs req =
        (hybridEnv rel P S Q (j + 1)).answerAfter ω rs req := fun ω rs req hrs => by
    simp only [Quantum.Env.answerAfter, ← horacle ω rs hrs.le]
    split_ifs with hQ
    · rw [hybridEnv_respond_lt rel P S j ω (i := ⟨rs.length, hQ⟩) (by simp; omega),
        hybridEnv_respond_lt rel P S (j + 1) ω (i := ⟨rs.length, hQ⟩) (by simp; omega)]
    · rfl
  refine Finset.sum_congr rfl fun ω _ => ?_
  have h := D.acceptProbOnAt_notMade_eq (hybridEnv rel P S Q j) (hybridEnv rel P S Q (j + 1)) post
    (ω := ω) (ω' := ω) (j := j) (fun rs req h => hans ω rs req h) (fun rs h => horacle ω rs h)
    Set.univ
  rw [Set.univ_inter] at h
  rw [h]
  rfl

/-- Step 2 for the prover: the salt-collision event. -/
theorem abs_relabelEnvP_sub_le (hloc : SaltedLocal saltOf P S) (j : Fin Q) :
    |D.acceptProbOn (relabelEnvP saltOf rel P S j) post (Quantum.madeLogs (j : ℕ)) -
      D.acceptProbOn (stepEnv rel P S j (freshShift saltOf) (respProver rel P)) post
        (Quantum.madeLogs (j : ℕ))| ≤ j / Fintype.card Sd :=
  (D.abs_acceptProbOn_sub_le_of_eq_off post (relabelEnvP saltOf rel P S j)
    (stepEnv rel P S j (freshShift saltOf) (respProver rel P)) rfl _
    (fun ω hω => (relabelEnvP_eq_off saltOf rel P S hloc j ω hω).1)
    (fun ω hω => (relabelEnvP_eq_off saltOf rel P S hloc j ω hω).2) _).trans
    (prob_saltCollision_le j)

/-- Step 2 for the simulator: the salt-collision event. -/
theorem abs_relabelEnvS_sub_le (hloc : SaltedLocal saltOf P S) (j : Fin Q) :
    |D.acceptProbOn (relabelEnvS saltOf rel P S j) post (Quantum.madeLogs (j : ℕ)) -
      D.acceptProbOn (stepEnv rel P S j (freshShift saltOf) (respSim rel S)) post
        (Quantum.madeLogs (j : ℕ))| ≤ j / Fintype.card Sd :=
  (D.abs_acceptProbOn_sub_le_of_eq_off post (relabelEnvS saltOf rel P S j)
    (stepEnv rel P S j (freshShift saltOf) (respSim rel S)) rfl _
    (fun ω hω => (relabelEnvS_eq_off saltOf rel P S hloc j ω hω).1)
    (fun ω hω => (relabelEnvS_eq_off saltOf rel P S hloc j ω hω).2) _).trans
    (prob_saltCollision_le j)

/-- Step 3 for the prover: O2H for the fresh slice of the prover's salt, charging the `q` query
slots of a budget `bud`. -/
theorem abs_stepEnvP_sub_le {q : ℕ} (bud : D.Budget q) (j : Fin Q) :
    |D.acceptProbOn (stepEnv rel P S j 0 (respProverFresh saltOf rel P)) post (Quantum.madeLogs (j : ℕ)) -
      D.acceptProbOn (stepEnv rel P S j (freshShift saltOf) (respProver rel P)) post
        (Quantum.madeLogs (j : ℕ))| ≤ 2 * q * √(n * (Fintype.card Sd : ℝ)⁻¹) := by
  refine D.advantage_acceptProbOn_made_le_of_fresh_secret_budget post bud _ _
    (μV := PMF.uniformOfFintype (HTape X Y Sd C SC Q))
    (ν := PMF.uniformOfFintype (FreshSlice X Y (SaltedCoins Sd C))) (T := fun τ => {y | saltOf y = some τ.coins.salt})
    j (fun v τ => uniformOfFintype_step_apply v τ) rfl
    (fun ω rs req => (stepEnv_answerAfter_of_resp rel P S j _ _ _ ω (fun _ _ => rfl) rs req).symm)
    (fun ω rs h => (stepEnv_oracleIn_of_resp rel P S j _ _ _ ω (fun _ _ => rfl) rs h).symm)
    (fun ω rs h x hx => ?_)
    (fun v σ σ' rs h => stepEnv_oracleIn_fresh rel P S j _ v σ σ' h)
    (fun v σ σ' rs req h => stepEnv_answerAfter_fresh rel P S j _ v σ σ' h req)
    (fun x => prob_saltSlot_le saltOf x)
  have h0 : freshShift saltOf ω x = 0 := sliceShift_eq_zero saltOf hx
  rw [stepEnv_oracleIn_shift rel P S j (freshShift saltOf) (respProver rel P)
    (respProverFresh saltOf rel P) ω rs h, Pi.add_apply, h0, add_zero]

/-- Step 3 for the simulator: O2H for the fresh slice of the simulator's salt, charging the `q`
query slots of a budget `bud`. -/
theorem abs_stepEnvS_sub_le {q : ℕ} (bud : D.Budget q) (j : Fin Q) :
    |D.acceptProbOn (stepEnv rel P S j 0 (respSimFresh saltOf rel S)) post (Quantum.madeLogs (j : ℕ)) -
      D.acceptProbOn (stepEnv rel P S j (freshShift saltOf) (respSim rel S)) post
        (Quantum.madeLogs (j : ℕ))| ≤ 2 * q * √(n * (Fintype.card Sd : ℝ)⁻¹) := by
  refine D.advantage_acceptProbOn_made_le_of_fresh_secret_budget post bud _ _
    (μV := PMF.uniformOfFintype (HTape X Y Sd C SC Q))
    (ν := PMF.uniformOfFintype (FreshSlice X Y (SaltedCoins Sd SC))) (T := fun τ => {y | saltOf y = some τ.coins.salt})
    j (fun v τ => uniformOfFintype_step_apply v τ) rfl
    (fun ω rs req => (stepEnv_answerAfter_of_resp rel P S j _ _ _ ω (fun _ _ => rfl) rs req).symm)
    (fun ω rs h => (stepEnv_oracleIn_of_resp rel P S j _ _ _ ω (fun _ _ => rfl) rs h).symm)
    (fun ω rs h x hx => ?_)
    (fun v σ σ' rs h => stepEnv_oracleIn_fresh rel P S j _ v σ σ' h)
    (fun v σ σ' rs req h => stepEnv_answerAfter_fresh rel P S j _ v σ σ' h req)
    (fun x => prob_saltSlot_le saltOf x)
  have h0 : freshShift saltOf ω x = 0 := sliceShift_eq_zero saltOf hx
  rw [stepEnv_oracleIn_shift rel P S j (freshShift saltOf) (respSim rel S)
    (respSimFresh saltOf rel S) ω rs h, Pi.add_apply, h0, add_zero]

/-- The reply of a proof query with coins `c` on the oracle `H'`, honest: the proof of a valid
proof query, `none` for an invalid one; the oracle is unchanged. -/
def honestReply (req : ProofQuery Stmt Wit) (c : SaltedCoins Sd C) (H' : X → Y) :
    Quantum.EnvReply Proof (X → Y) :=
  if rel req.stmt req.wit then ⟨some (P.prove H' req.stmt req.wit c), H'⟩ else ⟨none, H'⟩

/-- The reply of a proof query with coins `s` on the oracle `H'`, simulated: the simulator's proof
and reprogrammed oracle for a valid proof query, `none` for an invalid one. -/
def simReply (req : ProofQuery Stmt Wit) (s : SaltedCoins Sd SC) (H' : X → Y) :
    Quantum.EnvReply Proof (X → Y) :=
  if rel req.stmt req.wit then ⟨some (S.run H' req.stmt s).proof, H'.reprogram (S.run H' req.stmt s).assignments⟩
  else ⟨none, H'⟩

/-- Proof query `j` of the fresh prover step, at a fixed tape and oracle in force `O`, has the law of
the honest reply on `O` with a fresh slice. -/
theorem map_respond_stepEnvP (j : Fin Q) (v : HTape X Y Sd C SC Q) (req : ProofQuery Stmt Wit)
    (O : X → Y) :
    (PMF.uniformOfFintype (FreshSlice X Y (SaltedCoins Sd C))).map
        (fun τ => (stepEnv rel P S j 0 (respProverFresh saltOf rel P)).respond (v, τ) j req O) =
      (PMF.uniformOfFintype (FreshSlice X Y (SaltedCoins Sd C))).map
        (fun τ => honestReply rel P req τ.coins (replaceSlice saltOf τ.coins.salt O τ.slice)) := by
  refine Eq.trans ?_ (map_shift_eq saltOf v.oracle O (honestReply rel P req))
  congr 1
  funext τ
  rw [stepEnv_respond_self]
  rfl

/-- Proof query `j` of the fresh simulator step has the law of the simulated reply on `O` with a
fresh slice. -/
theorem map_respond_stepEnvS (j : Fin Q) (v : HTape X Y Sd C SC Q) (req : ProofQuery Stmt Wit)
    (O : X → Y) :
    (PMF.uniformOfFintype (FreshSlice X Y (SaltedCoins Sd SC))).map
        (fun τ => (stepEnv rel P S j 0 (respSimFresh saltOf rel S)).respond (v, τ) j req O) =
      (PMF.uniformOfFintype (FreshSlice X Y (SaltedCoins Sd SC))).map
        (fun τ => simReply rel S req τ.coins (replaceSlice saltOf τ.coins.salt O τ.slice)) := by
  refine Eq.trans ?_ (map_shift_eq saltOf v.oracle O (simReply rel S req))
  congr 1
  funext τ
  rw [stepEnv_respond_self]
  rfl

/-- **The refusal of an invalid proof query on a fresh slice** reads only the salt and the slice. -/
theorem map_refusal_eq_salt {Cx : Type*} [Fintype Cx] [Nonempty Cx] (O : X → Y) :
    (PMF.uniformOfFintype (FreshSlice X Y (SaltedCoins Sd Cx))).map
        (fun τ => (⟨none, replaceSlice saltOf τ.coins.salt O τ.slice⟩ : Quantum.EnvReply Proof (X → Y))) =
      (PMF.uniformOfFintype (Sd × (X → Y))).map
        (fun p => (⟨none, replaceSlice saltOf p.1 O p.2⟩ : Quantum.EnvReply Proof (X → Y))) := by
  rw [← FreshSlice.map_salt_slice_uniformOfFintype (C := Cx), PMF.map_comp]
  rfl

/-- Step 4: proof query `j`'s kernel, the honest proof on the fresh slice, replaced by the
simulator's. -/
theorem abs_stepEnv_kernel_le {η : (X → Y) → ℝ} (hloc : SaltedLocal saltOf P S)
    (hclose : SliceClose saltOf rel P S η) (j : Fin Q) :
    |D.acceptProbOn (stepEnv rel P S j 0 (respProverFresh saltOf rel P)) post (Quantum.madeLogs (j : ℕ)) -
      D.acceptProbOn (stepEnv rel P S j 0 (respSimFresh saltOf rel S)) post (Quantum.madeLogs (j : ℕ))| ≤
      𝔼[H ← (X → Y) : η H] := by
  classical
  rw [← sum_uniform_htape_eq_expect (X := X) (Y := Y) (Sd := Sd) (C := C) (SC := SC) (Q := Q) η]
  refine D.abs_acceptProbOn_sub_le_of_kernel post (stepEnv rel P S j 0 (respProverFresh saltOf rel P))
    (stepEnv rel P S j 0 (respSimFresh saltOf rel S))
    (μV := PMF.uniformOfFintype (HTape X Y Sd C SC Q))
    (ν := PMF.uniformOfFintype (FreshSlice X Y (SaltedCoins Sd C)))
    (ν' := PMF.uniformOfFintype (FreshSlice X Y (SaltedCoins Sd SC)))
    (fun v τ => uniformOfFintype_step_apply v τ) (fun v τ => uniformOfFintype_step_apply v τ) j
    (fun v τ τ' => by simp [stepEnv]) (fun v τ τ' i hi => ?_) (fun v => η v.oracle)
    (fun v => hclose.nonneg _) (fun v τ₀ req rs hrs => ?_) _
  · funext req H
    rcases lt_or_gt_of_ne (fun h : (i : ℕ) = j => hi (Fin.ext h)) with hlt | hgt
    · rw [stepEnv_respond_lt rel P S j _ _ _ hlt, stepEnv_respond_lt rel P S j _ _ _ hlt]
      rfl
    · rw [stepEnv_respond_gt rel P S j _ _ _ hgt, stepEnv_respond_gt rel P S j _ _ _ hgt]
  · set O := (stepEnv rel P S j 0 (respProverFresh saltOf rel P)).oracleIn (v, τ₀) rs
    have hO : η O = η v.oracle := hclose.congr _ _ fun y hy =>
      stepEnv_oracleIn_unsalted saltOf rel P S hloc j _ (v, τ₀) rs hrs.le y hy
    rw [map_respond_stepEnvP saltOf rel P S j v req O, map_respond_stepEnvS saltOf rel P S j v req O]
    by_cases hrel : rel req.stmt req.wit
    · simp only [honestReply, simReply, hrel, ite_true]
      rw [← hO]
      exact hclose.close O req.stmt req.wit hrel
    · simp only [honestReply, simReply, hrel, ite_false]
      rw [map_refusal_eq_salt saltOf (Proof := Proof) (Cx := C) O,
        map_refusal_eq_salt saltOf (Proof := Proof) (Cx := SC) O, PMF.tvDist_self]
      exact hclose.nonneg _

/-- **One step of the hybrid.** Hybrids `j` and `j + 1` are distinguished with advantage at
most `4 q √(n / |Sd|)` (two O2H steps over the `q` query slots of a budget `bud`) plus
`2 j / |Sd|` (an earlier simulator drew proof query `j`'s salt, twice) plus `𝔼 H, η H` (proof query
`j`'s kernel). -/
theorem abs_acceptProb_hybridEnv_sub_le {η : (X → Y) → ℝ} (hloc : SaltedLocal saltOf P S)
    (hclose : SliceClose saltOf rel P S η) {q : ℕ} (bud : D.Budget q) (j : Fin Q) :
    |D.acceptProb (hybridEnv rel P S Q j) post - D.acceptProb (hybridEnv rel P S Q (j + 1)) post| ≤
      4 * q * √(n / Fintype.card Sd) + 2 * j / Fintype.card Sd +
        𝔼[H ← (X → Y) : η H] := by
  have hsplit : ∀ E : Quantum.Env (HTape X Y Sd C SC Q) (ProofQuery Stmt Wit) Proof X Y Q, D.acceptProb E post =
      D.acceptProbOn E post (Quantum.madeLogs (j : ℕ)) + D.acceptProbOn E post (Quantum.madeLogs (j : ℕ))ᶜ :=
    fun E => by
      rw [← Quantum.Distinguisher.acceptProbOn_univ, D.acceptProbOn_eq_add post E Set.univ (Quantum.madeLogs (j : ℕ)),
        Set.univ_inter, Set.univ_inter]
  rw [hsplit, hsplit, acceptProbOn_hybridEnv_notMade rel P S D post j,
    add_sub_add_right_eq_sub, acceptProbOn_hybridEnv_eq_relabelP saltOf rel P S D post hloc j,
    acceptProbOn_hybridEnv_eq_relabelS saltOf rel P S D post hloc j]
  have hsqrt : √(n * (Fintype.card Sd : ℝ)⁻¹) = √(n / Fintype.card Sd) := by rw [div_eq_mul_inv]
  have h1 := abs_relabelEnvP_sub_le saltOf rel P S D post hloc j
  have h2 := abs_stepEnvP_sub_le saltOf rel P S D post bud j
  have h3 := abs_stepEnv_kernel_le saltOf rel P S D post hloc hclose j
  have h4 := abs_stepEnvS_sub_le saltOf rel P S D post bud j
  have h5 := abs_relabelEnvS_sub_le saltOf rel P S D post hloc j
  rw [hsqrt] at h2 h4
  have e : ∀ a b c d e f : ℝ, |a - f| ≤ |a - b| + |c - b| + |c - d| + |d - e| + |f - e| := by
    intro a b c d e f
    calc |a - f| = |(a - b) - (c - b) + (c - d) + (d - e) - (f - e)| := by ring_nf
      _ ≤ |a - b| + |c - b| + |c - d| + |d - e| + |f - e| := by
        have h1 := abs_sub (a - b - (c - b) + (c - d) + (d - e)) (f - e)
        have h2 := abs_add_le (a - b - (c - b) + (c - d)) (d - e)
        have h3 := abs_add_le (a - b - (c - b)) (c - d)
        have h4 := abs_sub (a - b) (c - b)
        linarith
  refine (e _ (D.acceptProbOn (stepEnv rel P S j (freshShift saltOf) (respProver rel P)) post
    (Quantum.madeLogs (j : ℕ))) (D.acceptProbOn (stepEnv rel P S j 0 (respProverFresh saltOf rel P)) post
    (Quantum.madeLogs (j : ℕ))) (D.acceptProbOn (stepEnv rel P S j 0 (respSimFresh saltOf rel S)) post
    (Quantum.madeLogs (j : ℕ))) (D.acceptProbOn (stepEnv rel P S j (freshShift saltOf) (respSim rel S)) post
    (Quantum.madeLogs (j : ℕ))) _).trans ?_
  have hj2 : 2 * ((j : ℕ) : ℝ) / Fintype.card Sd = (j : ℕ) / Fintype.card Sd + (j : ℕ) / Fintype.card Sd := by
    ring
  have hm4 : 4 * (q : ℝ) * √(n / Fintype.card Sd) =
      2 * q * √(n / Fintype.card Sd) + 2 * q * √(n / Fintype.card Sd) := by ring
  rw [hj2, hm4]
  linarith

/-- **Zero knowledge of a salted argument, unbounded after the last slot**: if the argument is
local in its salt (`SaltedLocal`) and one proof is simulated within `η H` on a fresh slice
(`SliceClose`), then every distinguisher with `m` slots of `n` parallel queries or one proof query
and a budget of `q` query slots with `n * q ≤ t` (each branch queries at no more than `q` slots,
chosen at run time), against environments answering `Q` proof queries, followed by any unitary of
the whole final oracle, has advantage at most `4 Q t / √|Sd| + Q (Q - 1) / |Sd| + Q · 𝔼 H, η H`
against the simulator `S`. Request slots are not charged
(`Distinguisher.advantage_acceptProbOn_made_le_of_fresh_secret_budget`); the O2H term per
proof query is `4 q √(n / |Sd|) ≤ 4 t / √|Sd|`.

Hypotheses: `hloc`, the locality of the prover and the simulator in the salt; `hclose`, the
classical one-proof statement, proved for the compiled Longfellow proof in
`GordieHowe/SPBCS/ZeroKnowledge.lean`. -/
theorem zeroKnowledgeAfterAdaptive_of_sliceClose {η : (X → Y) → ℝ}
    (hloc : SaltedLocal saltOf P S) (hclose : SliceClose saltOf rel P S η) :
    ZeroKnowledgeAfterAdaptive rel P S fun t Q =>
      4 * Q * t / √(Fintype.card Sd) + Q * (Q - 1) / Fintype.card Sd + Q * 𝔼[H ← (X → Y) : η H] := by
  intro t W _ n m Q q D post bud hD
  have hc : (0 : ℝ) < Fintype.card Sd := Nat.cast_pos.2 Fintype.card_pos
  -- the query count: `q √n ≤ t` for the `q` query slots
  have hmt : (q : ℝ) * √n ≤ t := by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · simp [hn]
    · have h1 : √(n : ℝ) ≤ n := Real.sqrt_le_iff.2 ⟨by positivity, by
        have : (1 : ℝ) ≤ n := by exact_mod_cast hn
        nlinarith⟩
      calc (q : ℝ) * √n ≤ q * n :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = (n * q : ℕ) := by push_cast; ring
        _ ≤ t := by exact_mod_cast hD
  have hstep : ∀ j : Fin Q, |D.acceptProb (hybridEnv rel P S Q j) post -
      D.acceptProb (hybridEnv rel P S Q (j + 1)) post| ≤
        4 * t / √(Fintype.card Sd) + 2 * j / Fintype.card Sd + 𝔼[H ← (X → Y) : η H] := fun j => by
    refine (abs_acceptProb_hybridEnv_sub_le saltOf rel P S D post hloc hclose bud j).trans ?_
    have : 4 * (q : ℝ) * √(n / Fintype.card Sd) ≤ 4 * t / √(Fintype.card Sd) := by
      rw [Real.sqrt_div' _ hc.le, mul_div_assoc', mul_assoc]
      gcongr
    linarith
  refine (advantage_le_sum_hybrid rel D post P S).trans ((Finset.sum_le_sum fun j _ => hstep j).trans ?_)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, nsmul_eq_mul]
  have hsum : ∑ j : Fin Q, 2 * (j : ℝ) / Fintype.card Sd = Q * (Q - 1) / Fintype.card Sd := by
    have key : ∀ q : ℕ, 2 * ∑ j ∈ Finset.range q, (j : ℝ) = q * (q - 1) := by
      intro q
      induction q with
      | zero => simp
      | succ q ih =>
        rw [Finset.sum_range_succ, mul_add, ih]
        push_cast
        ring
    rw [← Finset.sum_div, ← Finset.mul_sum, Fin.sum_univ_eq_sum_range (fun j => (j : ℝ)) Q, key]
  rw [hsum]
  ring_nf
  exact le_refl _

end Salted

end QROM

end GordieHowe
