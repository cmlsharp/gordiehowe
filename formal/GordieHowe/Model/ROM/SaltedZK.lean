-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.ROM.NIZK
public import GordieHowe.Model.QROM.SaltedZK
public import GordieHowe.Foundations.Probability.Probability

@[expose] public section

/-!
# Zero knowledge of a salted argument in the classical random-oracle model

The classical counterpart of `GordieHowe/Model/QROM/SaltedZK.lean`, for the same salted arguments:
the oracle is `H : X → Y`, `saltOf x` is the salt in the slot of the input `x`, the prover's and
the simulator's coins are `(σ, c)` with a uniform salt `σ : Sd`, and the prover and the simulator
are local in their salt (`GordieHowe.QROM.SaltedLocal`). The one-proof hypothesis is the slice
closeness at every fixed salt (`SliceCloseAt`): for every salt `σ`, oracle `H` and valid proof query,
the honest proof on `H` with the slice of `σ` answered by a fresh function and the simulated proof
with salt `σ` on the same oracle are within `η H` in total variation. It is a classical statement
about one proof; averaged over the salt it is the hypothesis `GordieHowe.QROM.SliceClose` of the
quantum theorem.

**The theorem** (`zeroKnowledge_of_sliceCloseAt`): zero knowledge against classical adversaries
(`ROM.NIZK.ZeroKnowledge`), unbounded after their steps, at the simulator `S`, with error

    Q t / |Sd| + Q (Q - 1) / (2 |Sd|) + Q · 𝔼 H, η H.

**The argument.** Hybrid `j` (`hybResp`) answers the valid proof queries numbered below `j` with the
simulator and the others with the prover, all on the oracle in force; its tape (`Tape`) draws one
salt per proof query, shared by the prover and the simulator, so that hybrids `j` and `j + 1` use the
same salt `σ` at proof query `j`. From `j` to `j + 1`:

1. (exact) Relabel the tape so that the initial oracle is `H` with the slice of `σ` answered by a
   fresh `F` (`expect_relabel`).
2. (identical until bad, `(t + j) / |Sd|`) Unless a query before proof query `j` carries the salt `σ`
   (`Hit`, at most `t / |Sd|`: the run before proof query `j` does not read `σ`) or an earlier proof query
   drew `σ` (`Coll`, at most `j / |Sd|`), the run from the relabelled oracle and the run from `H`
   in which proof query `j` replaces the slice of `σ` by `F` have the same replies, and the same state
   from proof query `j` on (`run_coupling`), in both hybrids.
3. (kernel, `𝔼 H, η H`) In the second run proof query `j`'s reply has the law `realSliceAt σ` in hybrid
   `j` and `simSliceAt σ` in hybrid `j + 1` on the oracle in force at that proof query, which agrees
   with `H` on the salt-free inputs; the bad event does not depend on proof query `j`'s coins, so the
   kernel step is charged on the good event at the fixed salt `σ`
   (`abs_expect_accepts_override_sub_le`).

The bad event is charged once per proof query, which is where the classical bound gains over the two
O2H steps of the quantum argument (`4 Q t / √|Sd|` there).
-/

open Finset
open scoped BigOperators ENNReal

namespace GordieHowe.ROM.NIZK

open GordieHowe.Quantum GordieHowe.QROM

variable {X Y Stmt Wit Proof : Type}

/-! ### Indicators and uniform averages -/

/-- **The indicator of a Boolean**, in `ℝ`. -/
def ind (b : Bool) : ℝ := if b then 1 else 0

theorem ind_nonneg (b : Bool) : 0 ≤ ind b := by
  unfold ind
  split <;> norm_num

theorem ind_le_one (b : Bool) : ind b ≤ 1 := by
  unfold ind
  split <;> norm_num

/-- An expectation over a product is the iterated expectation. -/
theorem expect_prod_eq {α β : Type*} [Fintype α] [Fintype β] (f : α × β → ℝ) :
    𝔼 p, f p = 𝔼 a, 𝔼 b, f (a, b) := by
  rw [← Finset.univ_product_univ, Finset.expect_product]

/-- **Averaging over one coordinate.** For a coordinate of `Ω` with values in `α`, read by `get`
and replaced by `upd` (a lens), the average of `f` is the average over `ω` and a fresh uniform
value `a` of `f` at `ω` with the coordinate replaced by `a`. -/
theorem expect_lens {Ω α : Type*} [Fintype Ω] [Fintype α] [Nonempty α] (upd : Ω → α → Ω)
    (get : Ω → α) (hget : ∀ ω a, get (upd ω a) = a) (hupd : ∀ ω, upd ω (get ω) = ω)
    (hupd₂ : ∀ ω a b, upd (upd ω a) b = upd ω b) (f : Ω → ℝ) :
    𝔼 ω, 𝔼 a, f (upd ω a) = 𝔼 ω, f ω := by
  let e : Ω × α ≃ Ω × α :=
    { toFun := fun p => (upd p.1 p.2, get p.1)
      invFun := fun p => (upd p.1 p.2, get p.1)
      left_inv := fun p => by simp only [hupd₂, hupd, hget]
      right_inv := fun p => by simp only [hupd₂, hupd, hget] }
  have h1 : 𝔼 ω, 𝔼 a, f (upd ω a) = 𝔼 p : Ω × α, f (upd p.1 p.2) :=
    (expect_prod_eq fun p : Ω × α => f (upd p.1 p.2)).symm
  have h2 : 𝔼 ω, f ω = 𝔼 p : Ω × α, f p.1 := by
    rw [expect_prod_eq]
    simp only [Fintype.expect_const]
  rw [h1, h2]
  exact Fintype.expect_equiv e _ _ fun p => rfl

/-- **A salt hits a fixed slot with probability at most `1 / |Sd|`**: for `o : Option Sd`, the
average over a uniform salt `σ` of the indicator of `o = some σ`. -/
theorem expect_ite_eq_some_le {Sd : Type*} [Fintype Sd] [DecidableEq Sd] [Nonempty Sd]
    (o : Option Sd) :
    𝔼 σ : Sd, (if o = some σ then (1 : ℝ) else 0) ≤ 1 / Fintype.card Sd := by
  rw [Fintype.expect_eq_sum_div_card]
  have hc : (0 : ℝ) < Fintype.card Sd := Nat.cast_pos.2 Fintype.card_pos
  rw [div_le_div_iff_of_pos_right hc]
  cases o with
  | none => simp
  | some s =>
    simp

/-- An expectation of a function of the first coordinate of a product. -/
theorem expect_prod_fst {α β : Type*} [Fintype α] [Fintype β] [Nonempty β] (f : α → ℝ) :
    𝔼 p : α × β, f p.1 = 𝔼 a, f a := by
  rw [expect_prod_eq]
  simp only [Fintype.expect_const]

/-- An expectation of a function of the second coordinate of a product. -/
theorem expect_prod_snd {α β : Type*} [Fintype α] [Nonempty α] [Fintype β] (f : β → ℝ) :
    𝔼 p : α × β, f p.2 = 𝔼 b, f b := by
  rw [expect_prod_eq]
  simp only [Fintype.expect_const]

/-! ### Overriding one proof query -/

/-- **A reply function**: the reply to a proof query on the oracle in force. -/
abbrev ReplyFn (X Y Stmt Wit Proof : Type) : Type :=
  ProofQuery Stmt Wit → (X → Y) → EnvReply Proof (X → Y)

/-- **The responder `R` with proof query number `j` answered by `g`.** -/
def override (R : Responder X Y Stmt Wit Proof) (j : ℕ) (g : ReplyFn X Y Stmt Wit Proof) :
    Responder X Y Stmt Wit Proof :=
  fun i => if i = j then g else R i

theorem override_self (R : Responder X Y Stmt Wit Proof) (j : ℕ) (g : ReplyFn X Y Stmt Wit Proof) :
    override R j g j = g := if_pos rfl

theorem override_of_ne (R : Responder X Y Stmt Wit Proof) {i j : ℕ} (g : ReplyFn X Y Stmt Wit Proof)
    (h : i ≠ j) : override R j g i = R i := if_neg h

/-- **The refusing reply**: `none`, the oracle unchanged. -/
def refuseReply : ReplyFn X Y Stmt Wit Proof := fun _ O => ⟨none, O⟩

namespace IAlg

variable {m : ℕ} (A : IAlg X Y Stmt Wit Proof m)

/-- **The output depends on the reply to proof query `j` only through one reply**: if the run with
proof query `j` answered by `g₀` makes proof query `j` at step `k₀` with `req₀` on the oracle `O₀`, then
with proof query `j` answered by any `g` the output is the output with proof query `j` answered by the
constant reply `g req₀ O₀`. -/
theorem accepts_override_eq (R : Responder X Y Stmt Wit Proof) (O : X → Y) {j : ℕ}
    (g₀ g : ReplyFn X Y Stmt Wit Proof) {k₀ : ℕ} {req₀ : ProofQuery Stmt Wit}
    (hk₀ : (A.run (override R j g₀) O k₀).nreq = j)
    (hreq₀ : A.next (A.run (override R j g₀) O k₀).hist = .request req₀) :
    A.accepts (override R j g) O = A.accepts (override R j
      (fun _ _ => g req₀ (A.run (override R j g₀) O k₀).oracle)) O := by
  refine A.accepts_eq_of_run_eq (A.run_eq_of_forall_ne (j := j) (fun i hi => by
    rw [override_of_ne _ _ hi, override_of_ne _ _ hi]) (fun k _ req hk hreq => ?_) m le_rfl)
  have hlt : ∀ i < j, override R j g i = override R j g₀ i := fun i hi => by
    rw [override_of_ne _ _ hi.ne, override_of_ne _ _ hi.ne]
  have hpre := A.run_eq_of_forall_lt (O := O) hlt k hk.le
  have hreq' : A.next (A.run (override R j g₀) O k).hist = .request req := by rw [hpre]; exact hreq
  have hkk : k = k₀ := A.eq_of_request_of_nreq_eq hreq' hreq₀ (by rw [hpre, hk, hk₀])
  subst hkk
  have hrr : req = req₀ := by
    rw [hreq'] at hreq₀
    exact Action.request.inj hreq₀
  subst hrr
  rw [override_self, override_self, hpre]

/-- **The output does not depend on the reply to proof query `j` when no step makes it.** -/
theorem accepts_override_eq_of_not_made (R : Responder X Y Stmt Wit Proof) (O : X → Y) {j : ℕ}
    (g₀ g : ReplyFn X Y Stmt Wit Proof)
    (h : ∀ k < m, ∀ req, (A.run (override R j g₀) O k).nreq = j →
      A.next (A.run (override R j g₀) O k).hist ≠ .request req) :
    A.accepts (override R j g) O = A.accepts (override R j g₀) O := by
  refine A.accepts_eq_of_run_eq (A.run_eq_of_forall_ne (j := j) (fun i hi => by
    rw [override_of_ne _ _ hi, override_of_ne _ _ hi]) (fun k hk req hn hreq => ?_) m le_rfl)
  have hlt : ∀ i < j, override R j g i = override R j g₀ i := fun i hi => by
    rw [override_of_ne _ _ hi.ne, override_of_ne _ _ hi.ne]
  have hpre := A.run_eq_of_forall_lt (O := O) hlt k hn.le
  exact absurd (by rw [hpre]; exact hreq) (h k hk req (by rw [hpre, hn]))

variable [Fintype X] [DecidableEq X] [Fintype Y] [Fintype Proof]

/-- **The kernel step**: replacing the reply to proof query `j` drawn as `gP u` for uniform `u` by
`gS v` for uniform `v` changes the probability that `A` outputs `true` by at most `ε` when, at
every step of the run that makes proof query `j` (with any other reply `g₀` to it), the two laws of the
reply are within `ε` in total variation. -/
theorem abs_expect_accepts_override_sub_le (R : Responder X Y Stmt Wit Proof) (O : X → Y) (j : ℕ)
    (g₀ : ReplyFn X Y Stmt Wit Proof) {U V : Type*} [Fintype U] [Nonempty U] [Fintype V]
    [Nonempty V] (gP : U → ReplyFn X Y Stmt Wit Proof) (gS : V → ReplyFn X Y Stmt Wit Proof)
    {ε : ℝ} (hε : 0 ≤ ε)
    (h : ∀ k < m, ∀ req, (A.run (override R j g₀) O k).nreq = j →
      A.next (A.run (override R j g₀) O k).hist = .request req →
      PMF.tvDist ((PMF.uniformOfFintype U).map fun u => gP u req (A.run (override R j g₀) O k).oracle)
        ((PMF.uniformOfFintype V).map fun v => gS v req (A.run (override R j g₀) O k).oracle) ≤ ε) :
    |𝔼 u, ind (A.accepts (override R j (gP u)) O) - 𝔼 v, ind (A.accepts (override R j (gS v)) O)| ≤
      ε := by
  classical
  by_cases hmade : ∃ k < m, ∃ req, (A.run (override R j g₀) O k).nreq = j ∧
      A.next (A.run (override R j g₀) O k).hist = .request req
  · obtain ⟨k₀, hk₀m, req₀, hk₀, hreq₀⟩ := hmade
    set O₀ := (A.run (override R j g₀) O k₀).oracle
    let Φ : EnvReply Proof (X → Y) → ℝ := fun r => ind (A.accepts (override R j fun _ _ => r) O)
    have hP : ∀ u, ind (A.accepts (override R j (gP u)) O) = Φ (gP u req₀ O₀) := fun u => by
      rw [A.accepts_override_eq R O g₀ (gP u) hk₀ hreq₀]
    have hS : ∀ v, ind (A.accepts (override R j (gS v)) O) = Φ (gS v req₀ O₀) := fun v => by
      rw [A.accepts_override_eq R O g₀ (gS v) hk₀ hreq₀]
    have hexpU : 𝔼 u, Φ (gP u req₀ O₀) =
        ∑ r, ((PMF.uniformOfFintype U).map (fun u => gP u req₀ O₀) r).toReal * Φ r := by
      rw [PMF.sum_toReal_map_mul, Fintype.expect_eq_sum_div_card, Finset.sum_div]
      refine Finset.sum_congr rfl fun w _ => ?_
      rw [PMF.toReal_uniformOfFintype_apply]
      ring
    have hexpV : 𝔼 v, Φ (gS v req₀ O₀) =
        ∑ r, ((PMF.uniformOfFintype V).map (fun v => gS v req₀ O₀) r).toReal * Φ r := by
      rw [PMF.sum_toReal_map_mul, Fintype.expect_eq_sum_div_card, Finset.sum_div]
      refine Finset.sum_congr rfl fun w _ => ?_
      rw [PMF.toReal_uniformOfFintype_apply]
      ring
    simp_rw [hP, hS]
    rw [hexpU, hexpV]
    refine (PMF.abs_sum_toReal_mul_sub_le _ _ (fun r => ind_nonneg _) (fun r => ind_le_one _)).trans ?_
    rw [one_mul]
    exact h k₀ hk₀m req₀ hk₀ hreq₀
  · push Not at hmade
    have hP : ∀ u, A.accepts (override R j (gP u)) O = A.accepts (override R j g₀) O := fun u =>
      A.accepts_override_eq_of_not_made R O g₀ _ fun k hk req hn => hmade k hk req hn
    have hS : ∀ v, A.accepts (override R j (gS v)) O = A.accepts (override R j g₀) O := fun v =>
      A.accepts_override_eq_of_not_made R O g₀ _ fun k hk req hn => hmade k hk req hn
    simp_rw [hP, hS, Fintype.expect_const, sub_self, abs_zero]
    exact hε

end IAlg

/-! ### Runs that differ on one slice -/

section Slice

variable {Sd : Type} [DecidableEq Sd] (saltOf : X → Option Sd)

/-- **Two states that differ on one slice**: the same replies and proof queries, and the first
state's oracle is the second's with the slice of `σ` answered by `F`. -/
structure SliceRel (σ : Sd) (F : X → Y) (s₁ s₂ : GameState X Y Proof) : Prop where
  hist : s₁.hist = s₂.hist
  nreq : s₁.nreq = s₂.nreq
  oracle : s₁.oracle = replaceSlice saltOf σ s₂.oracle F

/-- **The coupling of a run from a relabelled oracle with a run that relabels at proof query `j`.**
Let `R₁` answer the proof queries below `j` without reading or changing the slice of `σ` (`hlt`), and
let `R₂` agree with `R₁` except at proof query `j`, which `R₂` answers as `R₁` does on the oracle with
the slice of `σ` answered by `F` (`hj`). If no query of the run of `R₂` from `H` before proof query `j`
carries the salt `σ` (`hq`), then at every step either proof query `j` is not yet made and the run of
`R₁` from `H` with the slice of `σ` answered by `F` differs from the run of `R₂` from `H` only on
that slice, or proof query `j` is made and the two states are equal. -/
theorem run_coupling {m : ℕ} (A : IAlg X Y Stmt Wit Proof m) {R₁ R₂ : Responder X Y Stmt Wit Proof}
    {H F : X → Y} {σ : Sd} {j : ℕ} (h12 : ∀ i, i ≠ j → R₂ i = R₁ i)
    (hlt : ∀ i < j, ∀ req O,
      (R₁ i req (replaceSlice saltOf σ O F)).response = (R₁ i req O).response ∧
        (R₁ i req (replaceSlice saltOf σ O F)).state = replaceSlice saltOf σ (R₁ i req O).state F)
    (hj : ∀ req O, R₂ j req O = R₁ j req (replaceSlice saltOf σ O F))
    (hq : ∀ k < m, ∀ x, (A.run R₂ H k).nreq ≤ j → A.next (A.run R₂ H k).hist = .query x →
      saltOf x ≠ some σ) :
    ∀ k ≤ m, ((A.run R₂ H k).nreq ≤ j ∧
        SliceRel saltOf σ F (A.run R₁ (replaceSlice saltOf σ H F) k) (A.run R₂ H k)) ∨
      (j < (A.run R₂ H k).nreq ∧ A.run R₁ (replaceSlice saltOf σ H F) k = A.run R₂ H k)
  | 0, _ => Or.inl ⟨Nat.zero_le _, ⟨rfl, rfl, rfl⟩⟩
  | k + 1, hk => by
    rw [IAlg.run_succ, IAlg.run_succ]
    rcases run_coupling A h12 hlt hj hq k (by omega) with ⟨hn, hrel⟩ | ⟨hn, heq⟩
    · set s₁ := A.run R₁ (replaceSlice saltOf σ H F) k
      set s₂ := A.run R₂ H k
      cases hnext : A.next s₂.hist with
      | query x =>
        have hnext₁ : A.next s₁.hist = .query x := by rw [hrel.hist]; exact hnext
        rw [IAlg.step_of_query hnext, IAlg.step_of_query hnext₁]
        have hx : s₁.oracle x = s₂.oracle x := by
          rw [hrel.oracle, replaceSlice, if_neg (hq k (by omega) x hn hnext)]
        exact Or.inl ⟨hn, ⟨by rw [hrel.hist, hx], hrel.nreq, hrel.oracle⟩⟩
      | request req =>
        have hnext₁ : A.next s₁.hist = .request req := by rw [hrel.hist]; exact hnext
        rw [IAlg.step_of_request hnext, IAlg.step_of_request hnext₁, hrel.nreq, hrel.oracle]
        rcases Nat.lt_or_eq_of_le hn with hlt' | heq'
        · rw [h12 _ hlt'.ne]
          obtain ⟨hr, hs⟩ := hlt _ hlt' req s₂.oracle
          exact Or.inl ⟨by simpa using hlt', ⟨by rw [hrel.hist, hr], rfl, hs⟩⟩
        · rw [heq', hj]
          refine Or.inr ⟨by simp, ?_⟩
          rw [hrel.hist]
    · refine Or.inr ⟨hn.trans_le (A.nreq_le_nreq_step _), ?_⟩
      rw [heq]
      refine (A.step_congr fun req _ => ?_).symm
      rw [h12 _ (by omega)]

end Slice

/-! ### The salted argument -/

/-- **The tape of the classical hybrids**: the initial oracle, one salt per proof query, shared by the
prover and the simulator, and the further coins of the prover and of the simulator for every
proof query. -/
@[ext]
structure Tape (X Y Sd C SC : Type) (Q : ℕ) where
  /-- The initial oracle. -/
  oracle : X → Y
  /-- The salt of each proof query. -/
  salts : Fin Q → Sd
  /-- The prover's further coins of each proof query. -/
  proverCoins : Fin Q → C
  /-- The simulator's further coins of each proof query. -/
  simCoins : Fin Q → SC

namespace Tape

variable (X Y : Type) (Sd C SC : Type) (Q : ℕ)

/-- A tape as its four parts. -/
def equivProd :
    Tape X Y Sd C SC Q ≃ (X → Y) × (Fin Q → Sd) × (Fin Q → C) × (Fin Q → SC) where
  toFun ω := (ω.oracle, ω.salts, ω.proverCoins, ω.simCoins)
  invFun p := ⟨p.1, p.2.1, p.2.2.1, p.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance [Fintype X] [DecidableEq X] [Fintype Y] [Fintype Sd] [Fintype C] [Fintype SC] :
    Fintype (Tape X Y Sd C SC Q) :=
  Fintype.ofEquiv _ (equivProd X Y Sd C SC Q).symm

instance [Nonempty Y] [Nonempty Sd] [Nonempty C] [Nonempty SC] : Nonempty (Tape X Y Sd C SC Q) :=
  ⟨⟨fun _ => Classical.arbitrary Y, fun _ => Classical.arbitrary Sd, fun _ => Classical.arbitrary C,
    fun _ => Classical.arbitrary SC⟩⟩

variable {X Y Sd C SC Q}

/-- The tape with the salt of proof query `i` replaced by `a`. -/
def updSalt (ω : Tape X Y Sd C SC Q) (i : Fin Q) (a : Sd) : Tape X Y Sd C SC Q :=
  { ω with salts := Function.update ω.salts i a }

/-- The tape with the prover's further coins of proof query `i` replaced by `a`. -/
def updProver (ω : Tape X Y Sd C SC Q) (i : Fin Q) (a : C) : Tape X Y Sd C SC Q :=
  { ω with proverCoins := Function.update ω.proverCoins i a }

/-- The tape with the simulator's further coins of proof query `i` replaced by `a`. -/
def updSim (ω : Tape X Y Sd C SC Q) (i : Fin Q) (a : SC) : Tape X Y Sd C SC Q :=
  { ω with simCoins := Function.update ω.simCoins i a }

variable [Fintype X] [DecidableEq X] [Fintype Y] [Fintype Sd] [Fintype C] [Fintype SC]

theorem expect_updSalt [Nonempty Sd] (i : Fin Q) (f : Tape X Y Sd C SC Q → ℝ) :
    𝔼 ω : Tape X Y Sd C SC Q, 𝔼 a : Sd, f (ω.updSalt i a) = 𝔼 ω, f ω :=
  expect_lens (fun (ω : Tape X Y Sd C SC Q) a => updSalt ω i a) (fun ω => ω.salts i)
    (fun _ _ => by simp [updSalt]) (fun _ => by simp [updSalt]) (fun _ _ _ => by simp [updSalt]) f

theorem expect_updProver [Nonempty C] (i : Fin Q) (f : Tape X Y Sd C SC Q → ℝ) :
    𝔼 ω : Tape X Y Sd C SC Q, 𝔼 a : C, f (ω.updProver i a) = 𝔼 ω, f ω :=
  expect_lens (fun (ω : Tape X Y Sd C SC Q) a => updProver ω i a) (fun ω => ω.proverCoins i)
    (fun _ _ => by simp [updProver]) (fun _ => by simp [updProver])
    (fun _ _ _ => by simp [updProver]) f

theorem expect_updSim [Nonempty SC] (i : Fin Q) (f : Tape X Y Sd C SC Q → ℝ) :
    𝔼 ω : Tape X Y Sd C SC Q, 𝔼 a : SC, f (ω.updSim i a) = 𝔼 ω, f ω :=
  expect_lens (fun (ω : Tape X Y Sd C SC Q) a => updSim ω i a) (fun ω => ω.simCoins i)
    (fun _ _ => by simp [updSim]) (fun _ => by simp [updSim]) (fun _ _ _ => by simp [updSim]) f

/-- An expectation of a function of the initial oracle is the expectation over the oracle. -/
theorem expect_oracle [Nonempty Sd] [Nonempty C] [Nonempty SC] (f : (X → Y) → ℝ) :
    𝔼 ω : Tape X Y Sd C SC Q, f ω.oracle = 𝔼 H, f H := by
  rw [Fintype.expect_equiv (equivProd X Y Sd C SC Q) (fun ω => f ω.oracle) (fun p => f p.1)
    fun _ => rfl]
  rw [expect_prod_eq]
  simp only [Fintype.expect_const]

end Tape

section Salted

variable [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y] {Sd C SC : Type} [Fintype Sd]
  [DecidableEq Sd] [Nonempty Sd] [Fintype C] [Nonempty C] [Fintype SC] [Nonempty SC]
  (saltOf : X → Option Sd) (rel : Stmt → Wit → Prop) [DecidableRel rel]
  (P : NARG.ProverFn X Y Stmt Wit Proof (SaltedCoins Sd C)) (S : NARG.SimulatorFn X Y Stmt Proof (SaltedCoins Sd SC))

/-! #### The slice laws at a fixed salt -/

/-- **The real slice law at the salt `σ`**: for uniform further coins `c` and a uniform slice
`F`, the honest proof of `(x, w)` with coins `(σ, c)` on `H` with the slice of `σ` answered by
`F`, and that oracle (`GordieHowe.QROM.realSlice` at the fixed salt `σ`). -/
noncomputable def realSliceAt (σ : Sd) (H : X → Y) (x : Stmt) (w : Wit) :
    PMF (EnvReply Proof (X → Y)) :=
  (PMF.uniformOfFintype (FreshSlice X Y C)).map fun a =>
    ⟨some (P.prove (replaceSlice saltOf σ H a.slice) x w ⟨σ, a.coins⟩),
      replaceSlice saltOf σ H a.slice⟩

/-- **The simulated slice law at the salt `σ`**: for uniform further coins `c` and a uniform
slice `F`, the simulator's proof of `x` with coins `(σ, c)` on `H` with the slice of `σ` answered
by `F`, and that oracle reprogrammed by its assignment list (`GordieHowe.QROM.simSlice` at the fixed
salt `σ`). -/
noncomputable def simSliceAt (σ : Sd) (H : X → Y) (x : Stmt) : PMF (EnvReply Proof (X → Y)) :=
  (PMF.uniformOfFintype (FreshSlice X Y SC)).map fun a =>
    ⟨some (S.run (replaceSlice saltOf σ H a.slice) x ⟨σ, a.coins⟩).proof,
      (replaceSlice saltOf σ H a.slice).reprogram
        (S.run (replaceSlice saltOf σ H a.slice) x ⟨σ, a.coins⟩).assignments⟩

/-- **The one-proof hypothesis at every salt**: for every salt `σ`, oracle `H` and valid proof query
`(x, w)`, the real and the simulated slice laws at `σ` are within `η H` in total variation, where
`η H ≥ 0` reads `H` only on salt-free inputs. A classical statement about one proof. -/
structure SliceCloseAt (η : (X → Y) → ℝ) : Prop where
  close : ∀ σ H x w, rel x w → realSliceAt saltOf P σ H x w ≈[η H] simSliceAt saltOf S σ H x
  nonneg : ∀ H, 0 ≤ η H
  congr : ∀ H H' : X → Y, AgreeOffSalted saltOf H H' → η H = η H'

omit [DecidableRel rel] in
variable {saltOf rel P S} in
/-- **Closeness at every salt gives closeness averaged over the salt**
(`GordieHowe.QROM.SliceClose`, the hypothesis of the quantum theorem): the slice laws of a uniform
salt are mixtures over the salt of the slice laws at each salt. -/
theorem SliceCloseAt.sliceClose [DecidableEq Y] [Fintype Proof] [DecidableEq Proof]
    {η : (X → Y) → ℝ} (h : SliceCloseAt saltOf rel P S η) : SliceClose saltOf rel P S η where
  close H x w hw := by
    rw [realSlice, simSlice, FreshSlice.map_uniformOfFintype_salted,
      FreshSlice.map_uniformOfFintype_salted]
    refine (PMF.tvDist_uniformOfFintype_bind_le _ _).trans ?_
    exact (Finset.expect_le_expect fun σ _ => h.close σ H x w hw).trans_eq
      (Finset.expect_const Finset.univ_nonempty _)
  nonneg := h.nonneg
  congr := h.congr

/-! #### The hybrids -/

/-- The honest reply with coins `c`: the proof of a valid proof query, `none` for an invalid one; the
oracle is unchanged. -/
def proverReply (c : SaltedCoins Sd C) : ReplyFn X Y Stmt Wit Proof := fun req O =>
  if rel req.stmt req.wit then ⟨some (P.prove O req.stmt req.wit c), O⟩ else ⟨none, O⟩

/-- The simulated reply with coins `s`: the simulator's proof and the reprogrammed oracle for a
valid proof query, `none` and the oracle unchanged for an invalid one. -/
def simulatorReply (s : SaltedCoins Sd SC) : ReplyFn X Y Stmt Wit Proof := fun req O =>
  if rel req.stmt req.wit then
    ⟨some (S.run O req.stmt s).proof, O.reprogram (S.run O req.stmt s).assignments⟩
  else ⟨none, O⟩

/-- **Hybrid `j`** at the tape `ω`: a proof query numbered `i < Q` is answered by the simulator with
coins `(salts i, simCoins i)` if `i < j` and by the prover with coins `(salts i, proverCoins i)`
otherwise, on the oracle in force; later proof queries are refused. -/
def hybResp {Q : ℕ} (j : ℕ) (ω : Tape X Y Sd C SC Q) : Responder X Y Stmt Wit Proof :=
  fun i req O =>
    if h : i < Q then
      if i < j then simulatorReply rel S ⟨ω.salts ⟨i, h⟩, ω.simCoins ⟨i, h⟩⟩ req O
      else proverReply rel P ⟨ω.salts ⟨i, h⟩, ω.proverCoins ⟨i, h⟩⟩ req O
    else ⟨none, O⟩

/-- Hybrids `j` and `j + 1` agree except at proof query `j`. -/
theorem hybResp_succ_of_ne {Q : ℕ} {i j : ℕ} (ω : Tape X Y Sd C SC Q) (h : i ≠ j) :
    hybResp rel P S (j + 1) ω i = hybResp rel P S j ω i := by
  funext req O
  unfold hybResp
  split_ifs <;> first | rfl | omega

/-- The real reply at proof query `j` with salt `σ` and fresh slice draw `a`: the honest reply with
coins `(σ, a.coins)` on the oracle in force with the slice of `σ` answered by `a.slice`. -/
def realReplyAt (σ : Sd) (a : FreshSlice X Y C) : ReplyFn X Y Stmt Wit Proof := fun req O =>
  proverReply rel P ⟨σ, a.coins⟩ req (replaceSlice saltOf σ O a.slice)

/-- The simulated reply at proof query `j` with salt `σ` and fresh slice draw `a`: the simulated reply
with coins `(σ, a.coins)` on the oracle in force with the slice of `σ` answered by `a.slice`. -/
def simReplyAt (σ : Sd) (a : FreshSlice X Y SC) : ReplyFn X Y Stmt Wit Proof := fun req O =>
  simulatorReply rel S ⟨σ, a.coins⟩ req (replaceSlice saltOf σ O a.slice)

/-- The refused reply on the oracle with a fresh slice has the same law whatever the further
coins. -/
theorem map_uniform_freshSlice {Cx : Type} [Fintype Cx] [Nonempty Cx] (σ : Sd) (O : X → Y) :
    (PMF.uniformOfFintype (FreshSlice X Y Cx)).map
        (fun a => (⟨none, replaceSlice saltOf σ O a.slice⟩ : EnvReply Proof (X → Y))) =
      (PMF.uniformOfFintype (X → Y)).map fun F => ⟨none, replaceSlice saltOf σ O F⟩ := by
  rw [← PMF.map_uniformOfFintype_equiv (FreshSlice.equivProd X Y Cx).symm, PMF.map_comp,
    ← PMF.map_snd_uniformOfFintype (α := Cx) (β := X → Y), PMF.map_comp]
  rfl

/-- **The kernel at a fixed salt**: on a valid proof query the laws of the real and the simulated
replies at the salt `σ` are the slice laws at `σ`, within `η O`; on an invalid proof query they are
equal. -/
theorem tvDist_replyAt_le {η : (X → Y) → ℝ} (hcl : SliceCloseAt saltOf rel P S η) (σ : Sd)
    (req : ProofQuery Stmt Wit) (O : X → Y) :
    PMF.tvDist ((PMF.uniformOfFintype (FreshSlice X Y C)).map fun a => realReplyAt saltOf rel P σ a req O)
      ((PMF.uniformOfFintype (FreshSlice X Y SC)).map fun a => simReplyAt saltOf rel S σ a req O) ≤
      η O := by
  by_cases hr : rel req.stmt req.wit
  · have h1 : (fun a : FreshSlice X Y C => realReplyAt saltOf rel P σ a req O) = fun a =>
        ⟨some (P.prove (replaceSlice saltOf σ O a.slice) req.stmt req.wit ⟨σ, a.coins⟩),
          replaceSlice saltOf σ O a.slice⟩ := funext fun a => by
      simp only [realReplyAt, proverReply, if_pos hr]
    have h2 : (fun a : FreshSlice X Y SC => simReplyAt saltOf rel S σ a req O) = fun a =>
        ⟨some (S.run (replaceSlice saltOf σ O a.slice) req.stmt ⟨σ, a.coins⟩).proof,
          (replaceSlice saltOf σ O a.slice).reprogram
            (S.run (replaceSlice saltOf σ O a.slice) req.stmt ⟨σ, a.coins⟩).assignments⟩ :=
      funext fun a => by simp only [simReplyAt, simulatorReply, if_pos hr]
    rw [h1, h2]
    exact hcl.close σ O req.stmt req.wit hr
  · have h1 : (fun a : FreshSlice X Y C => realReplyAt saltOf rel P σ a req O) = fun a =>
        ⟨none, replaceSlice saltOf σ O a.slice⟩ := funext fun a => by
      simp only [realReplyAt, proverReply, if_neg hr]
    have h2 : (fun a : FreshSlice X Y SC => simReplyAt saltOf rel S σ a req O) = fun a =>
        ⟨none, replaceSlice saltOf σ O a.slice⟩ := funext fun a => by
      simp only [simReplyAt, simulatorReply, if_neg hr]
    rw [h1, h2, map_uniform_freshSlice, map_uniform_freshSlice, PMF.tvDist_self]
    exact hcl.nonneg O

/-- Replacing a slice commutes with reprogramming at inputs off that slice. -/
theorem replaceSlice_reprogram {σ : Sd} (O F : X → Y) {ass : List (Assignment X Y)}
    (h : ∀ a ∈ ass, saltOf a.input ≠ some σ) :
    (replaceSlice saltOf σ O F).reprogram ass = replaceSlice saltOf σ (O.reprogram ass) F := by
  funext y
  by_cases hy : saltOf y = some σ
  · rw [reprogram_apply_of_forall_ne _ fun a ha e => h a ha (e ▸ hy)]
    simp only [replaceSlice, hy, if_true]
  · rw [show replaceSlice saltOf σ (O.reprogram ass) F y = O.reprogram ass y from if_neg hy]
    exact reprogram_apply_congr ass (if_neg hy)

variable {saltOf rel P S}

/-- **The proof queries below `j` do not read or change the slice of a fresh salt**: when no proof query
below `j` has the salt `σ`, hybrid `j`'s replies to them on an oracle with the slice of `σ`
replaced are its replies on the original oracle, with the slice replaced. -/
theorem hybResp_replaceSlice (hloc : SaltedLocal saltOf P S) {Q : ℕ} {j : ℕ}
    (ω : Tape X Y Sd C SC Q) {σ : Sd} (hcol : ∀ i : Fin Q, (i : ℕ) < j → ω.salts i ≠ σ)
    (F : X → Y) {i : ℕ} (hi : i < j) (req : ProofQuery Stmt Wit) (O : X → Y) :
    (hybResp rel P S j ω i req (replaceSlice saltOf σ O F)).response =
        (hybResp rel P S j ω i req O).response ∧
      (hybResp rel P S j ω i req (replaceSlice saltOf σ O F)).state =
        replaceSlice saltOf σ (hybResp rel P S j ω i req O).state F := by
  unfold hybResp
  by_cases hQ : i < Q
  · simp only [dif_pos hQ, if_pos hi, simulatorReply]
    have hs := hcol ⟨i, hQ⟩ hi
    have hag : AgreeOnSlice saltOf (ω.salts ⟨i, hQ⟩) (replaceSlice saltOf σ O F) O := by
      intro y hy
      have : saltOf y ≠ some σ := by
        rcases hy with hy | hy <;> rw [hy]
        · simp
        · exact fun e => hs (Option.some_injective _ e)
      simp only [replaceSlice, this, if_false]
    split_ifs with hr
    · rw [hloc.run_congr (replaceSlice saltOf σ O F) O req.stmt _ hag]
      refine ⟨rfl, replaceSlice_reprogram saltOf O F fun a ha e => ?_⟩
      rw [hloc.run_salt O req.stmt _ a ha] at e
      exact hs (Option.some_injective _ e)
    · exact ⟨rfl, rfl⟩
  · simp [dif_neg hQ]

/-- **Hybrid `j`'s replies do not change the oracle on salt-free inputs.** -/
theorem agreeOffSalted_hybResp (hloc : SaltedLocal saltOf P S) {Q : ℕ} (j : ℕ)
    (ω : Tape X Y Sd C SC Q) (i : ℕ) (req : ProofQuery Stmt Wit) (O : X → Y) :
    AgreeOffSalted saltOf (hybResp rel P S j ω i req O).state O := by
  intro y hy
  unfold hybResp
  split_ifs
  · simp only [simulatorReply]
    split_ifs
    · exact reprogram_apply_of_forall_ne _ fun a ha e => by
        rw [← e, hloc.run_salt O req.stmt _ a ha] at hy
        exact Option.some_ne_none _ hy
    · rfl
  · simp only [proverReply]
    split_ifs <;> rfl
  · rfl

/-- **The run of a responder whose replies keep the salt-free inputs** agrees with the initial
oracle on the salt-free inputs at every step. -/
theorem IAlg.agreeOffSalted_run {m : ℕ} (A : IAlg X Y Stmt Wit Proof m)
    {R : Responder X Y Stmt Wit Proof} (hR : ∀ i req O, AgreeOffSalted saltOf (R i req O).state O)
    (H : X → Y) : ∀ k, AgreeOffSalted saltOf (A.run R H k).oracle H
  | 0 => fun _ _ => rfl
  | k + 1 => fun y hy => by
    rw [IAlg.run_succ]
    cases hn : A.next (A.run R H k).hist with
    | query x =>
      rw [IAlg.step_of_query hn]
      exact A.agreeOffSalted_run hR H k y hy
    | request req =>
      rw [IAlg.step_of_request hn]
      exact (hR _ req _ y hy).trans (A.agreeOffSalted_run hR H k y hy)

/-! #### One hybrid step -/

variable (rel P S) in
/-- **Hybrid `j` with proof query `j` refused**: the responder whose run is the common run of hybrids
`j` and `j + 1` before proof query `j`. -/
def baseResp {Q : ℕ} (j : ℕ) (ω : Tape X Y Sd C SC Q) : Responder X Y Stmt Wit Proof :=
  override (hybResp rel P S j ω) j refuseReply

variable (saltOf rel P S) in
/-- **A query hits the salt of proof query `j`**: some query of the run of `baseResp j ω` carries the
salt of proof query `j`. -/
def StepHit {m : ℕ} (A : IAlg X Y Stmt Wit Proof m) {Q : ℕ} {j : ℕ} (hj : j < Q)
    (ω : Tape X Y Sd C SC Q) : Prop :=
  ∃ k < m, ∃ x, A.next (A.run (baseResp rel P S j ω) ω.oracle k).hist = .query x ∧
    saltOf x = some (ω.salts ⟨j, hj⟩)

/-- **An earlier proof query drew the salt of proof query `j`.** -/
def StepColl {Q : ℕ} {j : ℕ} (hj : j < Q) (ω : Tape X Y Sd C SC Q) : Prop :=
  ∃ i : Fin Q, (i : ℕ) < j ∧ ω.salts i = ω.salts ⟨j, hj⟩

/-- The responder with proof query `j` overridden does not read the coins of proof query `j`. -/
theorem override_hybResp_updSalt {Q : ℕ} {j : ℕ} (hj : j < Q) (j' : ℕ) (ω : Tape X Y Sd C SC Q)
    (a : Sd) (g : ReplyFn X Y Stmt Wit Proof) :
    override (hybResp rel P S j' (ω.updSalt ⟨j, hj⟩ a)) j g = override (hybResp rel P S j' ω) j g := by
  funext i req O
  by_cases hi : i = j
  · simp only [override, if_pos hi]
  · simp only [override, if_neg hi, hybResp, Tape.updSalt]
    by_cases h1 : i < Q
    · have hne : (⟨i, h1⟩ : Fin Q) ≠ ⟨j, hj⟩ := fun e => hi (congrArg Fin.val e)
      simp only [dif_pos h1, Function.update_of_ne hne]
    · simp only [dif_neg h1]

theorem override_hybResp_updProver {Q : ℕ} {j : ℕ} (hj : j < Q) (j' : ℕ) (ω : Tape X Y Sd C SC Q)
    (a : C) (g : ReplyFn X Y Stmt Wit Proof) :
    override (hybResp rel P S j' (ω.updProver ⟨j, hj⟩ a)) j g =
      override (hybResp rel P S j' ω) j g := by
  funext i req O
  by_cases hi : i = j
  · simp only [override, if_pos hi]
  · simp only [override, if_neg hi, hybResp, Tape.updProver]
    by_cases h1 : i < Q
    · have hne : (⟨i, h1⟩ : Fin Q) ≠ ⟨j, hj⟩ := fun e => hi (congrArg Fin.val e)
      simp only [dif_pos h1, Function.update_of_ne hne]
    · simp only [dif_neg h1]

theorem override_hybResp_updSim {Q : ℕ} {j : ℕ} (hj : j < Q) (j' : ℕ) (ω : Tape X Y Sd C SC Q)
    (a : SC) (g : ReplyFn X Y Stmt Wit Proof) :
    override (hybResp rel P S j' (ω.updSim ⟨j, hj⟩ a)) j g = override (hybResp rel P S j' ω) j g := by
  funext i req O
  by_cases hi : i = j
  · simp only [override, if_pos hi]
  · simp only [override, if_neg hi, hybResp, Tape.updSim]
    by_cases h1 : i < Q
    · have hne : (⟨i, h1⟩ : Fin Q) ≠ ⟨j, hj⟩ := fun e => hi (congrArg Fin.val e)
      simp only [dif_pos h1, Function.update_of_ne hne]
    · simp only [dif_neg h1]

/-- **One hybrid step, pointwise**: unless a query before proof query `j` or an earlier proof query has
the salt of proof query `j`, the difference of the outputs of hybrids `j` and `j + 1` from the oracle
with that salt's slice answered by `F` is the difference of the outputs from the original oracle
when proof query `j` is answered with that slice by the prover and by the simulator. -/
theorem step_pointwise (hloc : SaltedLocal saltOf P S) {m : ℕ} (A : IAlg X Y Stmt Wit Proof m)
    {Q j : ℕ} (hj : j < Q) (ω : Tape X Y Sd C SC Q) (F : X → Y)
    (hH : ¬ StepHit saltOf rel P S A hj ω) (hC : ¬ StepColl hj ω) :
    ind (A.accepts (hybResp rel P S j ω) (replaceSlice saltOf (ω.salts ⟨j, hj⟩) ω.oracle F)) -
        ind (A.accepts (hybResp rel P S (j + 1) ω)
          (replaceSlice saltOf (ω.salts ⟨j, hj⟩) ω.oracle F)) =
      ind (A.accepts (override (hybResp rel P S j ω) j
          (realReplyAt saltOf rel P (ω.salts ⟨j, hj⟩) ⟨ω.proverCoins ⟨j, hj⟩, F⟩)) ω.oracle) -
        ind (A.accepts (override (hybResp rel P S j ω) j
          (simReplyAt saltOf rel S (ω.salts ⟨j, hj⟩) ⟨ω.simCoins ⟨j, hj⟩, F⟩)) ω.oracle) := by
  classical
  set σ := ω.salts ⟨j, hj⟩ with hσ
  set H := ω.oracle
  set R₁ := hybResp rel P S j ω with hR₁
  set R₁' := hybResp rel P S (j + 1) ω with hR₁'
  set gP := realReplyAt saltOf rel P σ ⟨ω.proverCoins ⟨j, hj⟩, F⟩
  set gS := simReplyAt saltOf rel S σ ⟨ω.simCoins ⟨j, hj⟩, F⟩
  have hcol : ∀ i : Fin Q, (i : ℕ) < j → ω.salts i ≠ σ := fun i hi e => hC ⟨i, hi, e⟩
  have hlt : ∀ i < j, ∀ req O,
      (R₁ i req (replaceSlice saltOf σ O F)).response = (R₁ i req O).response ∧
        (R₁ i req (replaceSlice saltOf σ O F)).state = replaceSlice saltOf σ (R₁ i req O).state F :=
    fun i hi req O => hybResp_replaceSlice hloc ω hcol F hi req O
  have hlt' : ∀ i < j, ∀ req O,
      (R₁' i req (replaceSlice saltOf σ O F)).response = (R₁' i req O).response ∧
        (R₁' i req (replaceSlice saltOf σ O F)).state = replaceSlice saltOf σ (R₁' i req O).state F :=
    fun i hi req O => by
      rw [hR₁', hybResp_succ_of_ne rel P S ω hi.ne]
      exact hlt i hi req O
  have h12 : ∀ i, i ≠ j → override R₁ j gP i = R₁ i := fun i hi => override_of_ne _ _ hi
  have h12' : ∀ i, i ≠ j → override R₁ j gS i = R₁' i := fun i hi => by
    rw [override_of_ne _ _ hi, hR₁', hybResp_succ_of_ne rel P S ω hi]
  have hj1 : ∀ req O, override R₁ j gP j req O = R₁ j req (replaceSlice saltOf σ O F) := by
    intro req O
    rw [override_self]
    simp only [gP, realReplyAt, hR₁, hybResp, dif_pos hj, lt_irrefl, if_false]
    rfl
  have hj1' : ∀ req O, override R₁ j gS j req O = R₁' j req (replaceSlice saltOf σ O F) := by
    intro req O
    rw [override_self]
    simp only [gS, simReplyAt, hR₁', hybResp, dif_pos hj, Nat.lt_succ_self, if_true]
    rfl
  have hagree : ∀ g g' : ReplyFn X Y Stmt Wit Proof, ∀ i < j, override R₁ j g i = override R₁ j g' i :=
    fun g g' i hi => by rw [override_of_ne _ _ hi.ne, override_of_ne _ _ hi.ne]
  -- the runs before proof query `j` are the run of `baseResp`
  have hpre : ∀ (g : ReplyFn X Y Stmt Wit Proof) k, (A.run (override R₁ j g) H k).nreq ≤ j →
      A.run (baseResp rel P S j ω) H k = A.run (override R₁ j g) H k :=
    fun g => A.run_eq_of_forall_lt (hagree g refuseReply)
  have hpre₀ : ∀ (g : ReplyFn X Y Stmt Wit Proof) k, (A.run (baseResp rel P S j ω) H k).nreq ≤ j →
      A.run (override R₁ j g) H k = A.run (baseResp rel P S j ω) H k :=
    fun g => A.run_eq_of_forall_lt (hagree refuseReply g)
  have hq : ∀ g : ReplyFn X Y Stmt Wit Proof, ∀ k < m, ∀ x, (A.run (override R₁ j g) H k).nreq ≤ j →
      A.next (A.run (override R₁ j g) H k).hist = .query x → saltOf x ≠ some σ :=
    fun g k hk x hn hx e => hH ⟨k, hk, x, by rw [hpre g k hn]; exact hx, e⟩
  have C1 := run_coupling saltOf A h12 hlt hj1 (hq gP)
  have C2 := run_coupling saltOf A h12' hlt' hj1' (hq gS)
  by_cases hM : ∃ k < m, ∃ req, (A.run (baseResp rel P S j ω) H k).nreq = j ∧
      A.next (A.run (baseResp rel P S j ω) H k).hist = .request req
  · obtain ⟨k, hk, req, hn, hr⟩ := hM
    have fin : ∀ (g : ReplyFn X Y Stmt Wit Proof) (R : Responder X Y Stmt Wit Proof),
        (((A.run (override R₁ j g) H m).nreq ≤ j ∧
          SliceRel saltOf σ F (A.run R (replaceSlice saltOf σ H F) m) (A.run (override R₁ j g) H m)) ∨
        (j < (A.run (override R₁ j g) H m).nreq ∧
          A.run R (replaceSlice saltOf σ H F) m = A.run (override R₁ j g) H m)) →
        A.accepts R (replaceSlice saltOf σ H F) = A.accepts (override R₁ j g) H := by
      intro g R hC'
      rcases hC' with ⟨hn', -⟩ | ⟨-, heq⟩
      · have he := hpre₀ g k hn.le
        have hr' : A.next (A.run (override R₁ j g) H k).hist = .request req := by rw [he]; exact hr
        have := A.nreq_lt_of_request hr' hk
        rw [he, hn] at this
        omega
      · exact A.accepts_eq_of_run_eq heq
    rw [fin gP R₁ (C1 m le_rfl), fin gS R₁' (C2 m le_rfl)]
  · push Not at hM
    have ha' : A.accepts (override R₁ j gP) H = A.accepts (override R₁ j gS) H := by
      rw [A.accepts_override_eq_of_not_made R₁ H refuseReply gP hM,
        A.accepts_override_eq_of_not_made R₁ H refuseReply gS hM]
    have ha : A.accepts R₁ (replaceSlice saltOf σ H F) = A.accepts R₁' (replaceSlice saltOf σ H F) := by
      refine A.accepts_eq_of_run_eq (A.run_eq_of_forall_ne (j := j)
        (fun i hi => (hybResp_succ_of_ne rel P S ω hi).symm) (fun k hk req hn hr => ?_) m le_rfl)
      rcases C1 k hk.le with ⟨hn2, hrel⟩ | ⟨hlt2, heq⟩
      · have hn3 : (A.run (override R₁ j gP) H k).nreq = j := by rw [← hrel.nreq]; exact hn
        have hr3 : A.next (A.run (override R₁ j gP) H k).hist = .request req := by
          rw [← hrel.hist]; exact hr
        have he := hpre gP k hn3.le
        rw [← he] at hn3 hr3
        exact absurd hr3 (hM k hk req hn3)
      · rw [heq] at hn
        omega
    rw [ha, ha', sub_self, sub_self]

/-! #### Counting the bad events -/

/-- The indicator of an existential is at most the sum of the indicators. -/
theorem ite_exists_le_sum {ι : Type*} (s : Finset ι) (p : ι → Prop) [DecidablePred p]
    [Decidable (∃ i ∈ s, p i)] :
    (if ∃ i ∈ s, p i then (1 : ℝ) else 0) ≤ ∑ i ∈ s, if p i then (1 : ℝ) else 0 := by
  split_ifs with h
  · obtain ⟨i, hi, hp⟩ := h
    calc (1 : ℝ) = if p i then 1 else 0 := by rw [if_pos hp]
      _ ≤ ∑ i ∈ s, if p i then (1 : ℝ) else 0 :=
        Finset.single_le_sum (f := fun i => if p i then (1 : ℝ) else 0)
          (fun j _ => by split_ifs <;> norm_num) hi
  · exact Finset.sum_nonneg fun j _ => by split_ifs <;> norm_num

open Classical in
/-- **A query among `m` steps hits a uniform salt** with probability at most the number of query
steps over `|Sd|`. -/
theorem expect_ite_exists_query_le {Sd : Type} [Fintype Sd] [DecidableEq Sd] [Nonempty Sd]
    (saltOf : X → Option Sd) (N : ℕ → Action X Stmt Wit) (m : ℕ) :
    𝔼 a : Sd, (if ∃ k < m, ∃ x, N k = .query x ∧ saltOf x = some a then (1 : ℝ) else 0) ≤
      ((range m).filter fun k => (N k).IsQuery).card / Fintype.card Sd := by
  classical
  have h1 : ∀ a : Sd, (if ∃ k < m, ∃ x, N k = .query x ∧ saltOf x = some a then (1 : ℝ) else 0) ≤
      ∑ k ∈ range m, if ∃ x, N k = .query x ∧ saltOf x = some a then (1 : ℝ) else 0 := fun a => by
    have := ite_exists_le_sum (range m) (fun k => ∃ x, N k = .query x ∧ saltOf x = some a)
    simp only [Finset.mem_range] at this
    exact this
  have h2 : ∀ k, 𝔼 a : Sd, (if ∃ x, N k = .query x ∧ saltOf x = some a then (1 : ℝ) else 0) ≤
      if (N k).IsQuery then (1 : ℝ) / Fintype.card Sd else 0 := fun k => by
    cases hN : N k with
    | query x =>
      simp only [Action.query.injEq, exists_eq_left', Action.IsQuery, if_true]
      exact expect_ite_eq_some_le (saltOf x)
    | request req => simp [Action.IsQuery]
  calc 𝔼 a : Sd, (if ∃ k < m, ∃ x, N k = .query x ∧ saltOf x = some a then (1 : ℝ) else 0)
      ≤ 𝔼 a : Sd, ∑ k ∈ range m, if ∃ x, N k = .query x ∧ saltOf x = some a then (1 : ℝ) else 0 :=
        Finset.expect_le_expect fun a _ => h1 a
    _ = ∑ k ∈ range m, 𝔼 a : Sd, if ∃ x, N k = .query x ∧ saltOf x = some a then (1 : ℝ) else 0 :=
        Finset.expect_sum_comm _ _ _
    _ ≤ ∑ k ∈ range m, if (N k).IsQuery then 1 / (Fintype.card Sd : ℝ) else 0 :=
        Finset.sum_le_sum fun k _ => h2 k
    _ = _ := by
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one_div]

/-- **An earlier proof query drew a uniform salt** with probability at most `j / |Sd|`. -/
theorem expect_ite_exists_salt_le {Sd : Type} [Fintype Sd] [DecidableEq Sd] [Nonempty Sd] {Q : ℕ}
    (s : Fin Q → Sd) (j : ℕ) :
    𝔼 a : Sd, (if ∃ i : Fin Q, (i : ℕ) < j ∧ s i = a then (1 : ℝ) else 0) ≤ j / Fintype.card Sd := by
  classical
  set T := univ.filter fun i : Fin Q => (i : ℕ) < j
  have h1 : ∀ a : Sd, (if ∃ i : Fin Q, (i : ℕ) < j ∧ s i = a then (1 : ℝ) else 0) ≤
      ∑ i ∈ T, if s i = a then (1 : ℝ) else 0 := fun a => by
    have := ite_exists_le_sum T (fun i => s i = a)
    simp only [T, Finset.mem_filter, Finset.mem_univ, true_and] at this
    exact this
  have hT : (T.card : ℝ) ≤ j := by
    have : T.card ≤ (range j).card :=
      Finset.card_le_card_of_injOn Fin.val (fun i hi => by
        simp only [T, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hi
        simpa using hi) (fun i _ i' _ h => Fin.ext h)
    rw [Finset.card_range] at this
    exact_mod_cast this
  calc 𝔼 a : Sd, (if ∃ i : Fin Q, (i : ℕ) < j ∧ s i = a then (1 : ℝ) else 0)
      ≤ 𝔼 a : Sd, ∑ i ∈ T, if s i = a then (1 : ℝ) else 0 := Finset.expect_le_expect fun a _ => h1 a
    _ = ∑ i ∈ T, 𝔼 a : Sd, if s i = a then (1 : ℝ) else 0 := Finset.expect_sum_comm _ _ _
    _ ≤ ∑ _i ∈ T, 1 / (Fintype.card Sd : ℝ) := Finset.sum_le_sum fun i _ => by
        have := expect_ite_eq_some_le (some (s i))
        simpa only [Option.some.injEq] using this
    _ = T.card / Fintype.card Sd := by rw [Finset.sum_const, nsmul_eq_mul, mul_one_div]
    _ ≤ j / Fintype.card Sd := by gcongr

theorem baseResp_updSalt {Q j : ℕ} (hj : j < Q) (ω : Tape X Y Sd C SC Q) (a : Sd) :
    baseResp rel P S j (ω.updSalt ⟨j, hj⟩ a) = baseResp rel P S j ω :=
  override_hybResp_updSalt hj j ω a refuseReply

theorem baseResp_updProver {Q j : ℕ} (hj : j < Q) (ω : Tape X Y Sd C SC Q) (a : C) :
    baseResp rel P S j (ω.updProver ⟨j, hj⟩ a) = baseResp rel P S j ω :=
  override_hybResp_updProver hj j ω a refuseReply

theorem baseResp_updSim {Q j : ℕ} (hj : j < Q) (ω : Tape X Y Sd C SC Q) (a : SC) :
    baseResp rel P S j (ω.updSim ⟨j, hj⟩ a) = baseResp rel P S j ω :=
  override_hybResp_updSim hj j ω a refuseReply

/-- **The bad events of step `j`** have probability at most `(t + j) / |Sd|` for an algorithm
with a budget of `t` queries: the run before proof query `j` does not read proof query `j`'s salt. -/
theorem expect_ite_bad_le {m t : ℕ} (A : IAlg X Y Stmt Wit Proof m) (hA : A.Budget t) {Q j : ℕ}
    (hj : j < Q) [DecidablePred (fun ω : Tape X Y Sd C SC Q =>
      StepHit saltOf rel P S A hj ω ∨ StepColl hj ω)] :
    𝔼 ω : Tape X Y Sd C SC Q,
        (if StepHit saltOf rel P S A hj ω ∨ StepColl hj ω then (1 : ℝ) else 0) ≤
      (t + j) / Fintype.card Sd := by
  classical
  rw [← Tape.expect_updSalt ⟨j, hj⟩]
  have hpt : ∀ (ω : Tape X Y Sd C SC Q) (a : Sd),
      (if StepHit saltOf rel P S A hj (ω.updSalt ⟨j, hj⟩ a) ∨ StepColl hj (ω.updSalt ⟨j, hj⟩ a)
        then (1 : ℝ) else 0) ≤
      (if ∃ k < m, ∃ x, A.next (A.run (baseResp rel P S j ω) ω.oracle k).hist = .query x ∧
          saltOf x = some a then (1 : ℝ) else 0) +
        (if ∃ i : Fin Q, (i : ℕ) < j ∧ ω.salts i = a then (1 : ℝ) else 0) := by
    intro ω a
    have hH : StepHit saltOf rel P S A hj (ω.updSalt ⟨j, hj⟩ a) ↔
        ∃ k < m, ∃ x, A.next (A.run (baseResp rel P S j ω) ω.oracle k).hist = .query x ∧
          saltOf x = some a := by
      unfold StepHit
      rw [baseResp_updSalt]
      simp [Tape.updSalt]
    have hC : StepColl hj (ω.updSalt ⟨j, hj⟩ a) ↔ ∃ i : Fin Q, (i : ℕ) < j ∧ ω.salts i = a := by
      unfold StepColl
      refine exists_congr fun i => and_congr_right fun hi => ?_
      have hne : i ≠ ⟨j, hj⟩ := fun e => by rw [e] at hi; exact lt_irrefl _ hi
      simp [Tape.updSalt, Function.update_of_ne hne]
    rw [if_congr (or_congr hH hC) rfl rfl]
    split_ifs <;> simp_all
  have hq : ∀ ω : Tape X Y Sd C SC Q,
      (((range m).filter fun k =>
        (A.next (A.run (baseResp rel P S j ω) ω.oracle k).hist).IsQuery).card : ℝ) ≤ t := fun ω => by
    exact_mod_cast hA _ _
  calc 𝔼 ω : Tape X Y Sd C SC Q, 𝔼 a : Sd,
        (if StepHit saltOf rel P S A hj (ω.updSalt ⟨j, hj⟩ a) ∨ StepColl hj (ω.updSalt ⟨j, hj⟩ a)
          then (1 : ℝ) else 0)
      ≤ 𝔼 ω : Tape X Y Sd C SC Q, 𝔼 a : Sd,
          ((if ∃ k < m, ∃ x, A.next (A.run (baseResp rel P S j ω) ω.oracle k).hist = .query x ∧
              saltOf x = some a then (1 : ℝ) else 0) +
            (if ∃ i : Fin Q, (i : ℕ) < j ∧ ω.salts i = a then (1 : ℝ) else 0)) :=
        Finset.expect_le_expect fun ω _ => Finset.expect_le_expect fun a _ => hpt ω a
    _ ≤ 𝔼 _ω : Tape X Y Sd C SC Q, ((t : ℝ) / Fintype.card Sd + j / Fintype.card Sd) := by
        refine Finset.expect_le_expect fun ω _ => ?_
        rw [Finset.expect_add_distrib]
        exact add_le_add ((expect_ite_exists_query_le saltOf _ m).trans
          (div_le_div_of_nonneg_right (hq ω) (Nat.cast_nonneg _)))
          (expect_ite_exists_salt_le ω.salts j)
    _ = (t + j) / Fintype.card Sd := by rw [Fintype.expect_const, add_div]

/-! #### The relabelled oracle -/

theorem replaceSlice_replaceSlice_swap (σ : Sd) (H F : X → Y) :
    replaceSlice saltOf σ (replaceSlice saltOf σ H F) (replaceSlice saltOf σ F H) = H := by
  funext y
  by_cases h : saltOf y = some σ <;> simp [replaceSlice, h]

variable (saltOf) in
/-- **Relabelling the slice of proof query `j`'s salt** (exact): the initial oracle with the slice of
the salt of proof query `j` answered by a fresh uniform `F` is a uniform oracle independent of the rest
of the tape. -/
theorem expect_relabel {Q j : ℕ} (hj : j < Q) (g : Tape X Y Sd C SC Q → ℝ) :
    𝔼 ω : Tape X Y Sd C SC Q, 𝔼 F : X → Y,
        g { ω with oracle := replaceSlice saltOf (ω.salts ⟨j, hj⟩) ω.oracle F } = 𝔼 ω, g ω := by
  let f : Tape X Y Sd C SC Q × (X → Y) → Tape X Y Sd C SC Q × (X → Y) := fun p =>
    ({ p.1 with oracle := replaceSlice saltOf (p.1.salts ⟨j, hj⟩) p.1.oracle p.2 },
      replaceSlice saltOf (p.1.salts ⟨j, hj⟩) p.2 p.1.oracle)
  have hf : Function.Involutive f := by
    rintro ⟨ω, F⟩
    simp only [f, replaceSlice_replaceSlice_swap]
  have h1 : 𝔼 ω : Tape X Y Sd C SC Q, 𝔼 F : X → Y,
      g { ω with oracle := replaceSlice saltOf (ω.salts ⟨j, hj⟩) ω.oracle F } =
        𝔼 p : Tape X Y Sd C SC Q × (X → Y), g (f p).1 :=
    (expect_prod_eq fun p : Tape X Y Sd C SC Q × (X → Y) => g (f p).1).symm
  have h2 : 𝔼 ω, g ω = 𝔼 p : Tape X Y Sd C SC Q × (X → Y), g p.1 := by
    rw [expect_prod_eq]
    simp only [Fintype.expect_const]
  rw [h1, h2]
  exact Fintype.expect_equiv hf.toPerm (fun p => g (f p).1) (fun p => g p.1) fun p => rfl

/-! #### One hybrid step -/

variable (rel P S) in
/-- **The probability that `A` outputs `true` in hybrid `j`**, over a uniform tape. -/
noncomputable def hyb {m : ℕ} (A : IAlg X Y Stmt Wit Proof m) (Q j : ℕ) : ℝ :=
  𝔼 ω : Tape X Y Sd C SC Q, ind (A.accepts (hybResp rel P S j ω) ω.oracle)

theorem abs_ind_sub_ind_le (b b' : Bool) : |ind b - ind b'| ≤ 1 :=
  abs_sub_le_iff.2 ⟨by linarith [ind_le_one b, ind_nonneg b'], by linarith [ind_le_one b', ind_nonneg b]⟩

/-- **One hybrid step**: hybrids `j` and `j + 1` differ by at most `(t + j) / |Sd| + 𝔼 H, η H`
for an algorithm with a budget of `t` queries. -/
theorem abs_hyb_sub_le [Fintype Proof] (hloc : SaltedLocal saltOf P S) {η : (X → Y) → ℝ}
    (hcl : SliceCloseAt saltOf rel P S η) {m t : ℕ} (A : IAlg X Y Stmt Wit Proof m)
    (hA : A.Budget t) {Q j : ℕ} (hj : j < Q) :
    |hyb rel P S A Q j - hyb rel P S A Q (j + 1)| ≤ (t + j) / Fintype.card Sd + 𝔼 H, η H := by
  classical
  set J : Fin Q := ⟨j, hj⟩
  let a : Tape X Y Sd C SC Q → (X → Y) → ℝ := fun ω F =>
    ind (A.accepts (hybResp rel P S j ω) (replaceSlice saltOf (ω.salts J) ω.oracle F))
  let b : Tape X Y Sd C SC Q → (X → Y) → ℝ := fun ω F =>
    ind (A.accepts (hybResp rel P S (j + 1) ω) (replaceSlice saltOf (ω.salts J) ω.oracle F))
  let Φ : Tape X Y Sd C SC Q → ReplyFn X Y Stmt Wit Proof → ℝ := fun ω g =>
    ind (A.accepts (override (hybResp rel P S j ω) j g) ω.oracle)
  let a' : Tape X Y Sd C SC Q → (X → Y) → ℝ := fun ω F =>
    Φ ω (realReplyAt saltOf rel P (ω.salts J) ⟨ω.proverCoins J, F⟩)
  let b' : Tape X Y Sd C SC Q → (X → Y) → ℝ := fun ω F =>
    Φ ω (simReplyAt saltOf rel S (ω.salts J) ⟨ω.simCoins J, F⟩)
  let Bad : Tape X Y Sd C SC Q → Prop := fun ω => StepHit saltOf rel P S A hj ω ∨ StepColl hj ω
  have ha : hyb rel P S A Q j = 𝔼 ω, 𝔼 F, a ω F :=
    (expect_relabel saltOf hj fun ω => ind (A.accepts (hybResp rel P S j ω) ω.oracle)).symm
  have hb : hyb rel P S A Q (j + 1) = 𝔼 ω, 𝔼 F, b ω F :=
    (expect_relabel saltOf hj fun ω => ind (A.accepts (hybResp rel P S (j + 1) ω) ω.oracle)).symm
  have hpt : ∀ ω F, a ω F - b ω F =
      (if Bad ω then a ω F - b ω F else 0) + (if Bad ω then 0 else a' ω F - b' ω F) := by
    intro ω F
    by_cases h : Bad ω
    · simp [h]
    · rw [if_neg h, if_neg h, zero_add]
      exact step_pointwise hloc A hj ω F (fun h' => h (Or.inl h')) (fun h' => h (Or.inr h'))
  have hsplit : hyb rel P S A Q j - hyb rel P S A Q (j + 1) =
      𝔼 ω, 𝔼 F, (if Bad ω then a ω F - b ω F else 0) +
        𝔼 ω, 𝔼 F, (if Bad ω then 0 else a' ω F - b' ω F) := by
    rw [ha, hb, ← Finset.expect_sub_distrib]
    rw [← Finset.expect_add_distrib univ (fun ω => 𝔼 F, (if Bad ω then a ω F - b ω F else 0))
      (fun ω => 𝔼 F, (if Bad ω then 0 else a' ω F - b' ω F))]
    refine Finset.expect_congr rfl fun ω _ => ?_
    rw [← Finset.expect_sub_distrib,
      ← Finset.expect_add_distrib univ (fun F => if Bad ω then a ω F - b ω F else 0)
        (fun F => if Bad ω then 0 else a' ω F - b' ω F)]
    exact Finset.expect_congr rfl fun F _ => hpt ω F
  rw [hsplit]
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · -- the bad events
    calc |𝔼 ω, 𝔼 F, (if Bad ω then a ω F - b ω F else 0)|
        ≤ 𝔼 ω : Tape X Y Sd C SC Q, (if Bad ω then (1 : ℝ) else 0) := by
          refine (Finset.abs_expect_le _ _).trans (Finset.expect_le_expect fun ω _ => ?_)
          refine (Finset.abs_expect_le _ _).trans ?_
          by_cases h : Bad ω
          · simp only [h, if_true]
            exact (Finset.expect_le_expect fun F _ => abs_ind_sub_ind_le _ _).trans_eq
              (Fintype.expect_const (1 : ℝ))
          · simp [h]
      _ ≤ (t + j) / Fintype.card Sd := expect_ite_bad_le A hA hj
  · -- the kernel step at the fixed salt, on the good event
    set f : Tape X Y Sd C SC Q → ℝ := fun ω => 𝔼 F, (if Bad ω then 0 else a' ω F - b' ω F)
    have hupd : ∀ ω : Tape X Y Sd C SC Q, ∀ (s : SC) (c : C),
        f ((ω.updSim J s).updProver J c) = if Bad ω then 0 else
          (𝔼 F, Φ ω (realReplyAt saltOf rel P (ω.salts J) ⟨c, F⟩) -
            𝔼 F, Φ ω (simReplyAt saltOf rel S (ω.salts J) ⟨s, F⟩)) := by
      intro ω s c
      have hΦ : ∀ g, Φ ((ω.updSim J s).updProver J c) g = Φ ω g := fun g => by
        simp only [Φ]
        rw [override_hybResp_updProver, override_hybResp_updSim]
        rfl
      have hBad : Bad ((ω.updSim J s).updProver J c) ↔ Bad ω := by
        simp only [Bad, StepHit, StepColl]
        rw [baseResp_updProver, baseResp_updSim]
        rfl
      have hpc : ((ω.updSim J s).updProver J c).proverCoins J = c := by simp [Tape.updProver]
      have hsc : ((ω.updSim J s).updProver J c).simCoins J = s := by
        simp [Tape.updProver, Tape.updSim]
      have hs : ((ω.updSim J s).updProver J c).salts = ω.salts := rfl
      simp only [f, a', b', hΦ, hs, hpc, hsc]
      by_cases h : Bad ω
      · have h' : Bad ((ω.updSim J s).updProver J c) := hBad.2 h
        simp [h, h']
      · have h' : ¬ Bad ((ω.updSim J s).updProver J c) := fun h'' => h (hBad.1 h'')
        simp only [h, h', if_false, Finset.expect_sub_distrib]
    have hfresh : ∀ {Cx : Type} [Fintype Cx] [Nonempty Cx] (g : FreshSlice X Y Cx → ℝ),
        𝔼 c : Cx, 𝔼 F : X → Y, g ⟨c, F⟩ = 𝔼 a, g a := by
      intro Cx _ _ g
      rw [← expect_prod_eq (fun p : Cx × (X → Y) => g ⟨p.1, p.2⟩)]
      exact Fintype.expect_equiv (FreshSlice.equivProd X Y _).symm _ _ fun _ => rfl
    have hker : ∀ ω : Tape X Y Sd C SC Q,
        |𝔼 s : SC, 𝔼 c : C, f ((ω.updSim J s).updProver J c)| ≤ η ω.oracle := by
      intro ω
      simp_rw [hupd]
      by_cases h : Bad ω
      · simp only [h, if_true, Fintype.expect_const, abs_zero]
        exact hcl.nonneg _
      · simp only [h, if_false]
        have e : 𝔼 s : SC, 𝔼 c : C,
            (𝔼 F, Φ ω (realReplyAt saltOf rel P (ω.salts J) ⟨c, F⟩) -
              𝔼 F, Φ ω (simReplyAt saltOf rel S (ω.salts J) ⟨s, F⟩)) =
            𝔼 c : C, 𝔼 F, Φ ω (realReplyAt saltOf rel P (ω.salts J) ⟨c, F⟩) -
              𝔼 s : SC, 𝔼 F, Φ ω (simReplyAt saltOf rel S (ω.salts J) ⟨s, F⟩) := by
          simp only [Finset.expect_sub_distrib, Fintype.expect_const]
        rw [e, hfresh (fun a => Φ ω (realReplyAt saltOf rel P (ω.salts J) a)),
          hfresh (fun a => Φ ω (simReplyAt saltOf rel S (ω.salts J) a))]
        refine A.abs_expect_accepts_override_sub_le (hybResp rel P S j ω) ω.oracle j refuseReply
          (realReplyAt saltOf rel P (ω.salts J)) (simReplyAt saltOf rel S (ω.salts J))
          (hcl.nonneg _) fun k _ req _ _ => ?_
        refine (tvDist_replyAt_le saltOf rel P S hcl _ req _).trans_eq (hcl.congr _ _ ?_)
        refine A.agreeOffSalted_run (saltOf := saltOf) (fun i req' O => ?_) ω.oracle k
        by_cases hi : i = j
        · rw [hi, override_self]
          exact fun _ _ => rfl
        · rw [override_of_ne _ _ hi]
          exact agreeOffSalted_hybResp hloc j ω i req' O
    calc |𝔼 ω, f ω|
        = |𝔼 ω : Tape X Y Sd C SC Q, 𝔼 s : SC, 𝔼 c : C, f ((ω.updSim J s).updProver J c)| := by
          rw [← Tape.expect_updProver J f]
          rw [← Tape.expect_updSim J fun ω => 𝔼 c : C, f (ω.updProver J c)]
      _ ≤ 𝔼 ω : Tape X Y Sd C SC Q, η ω.oracle :=
          (Finset.abs_expect_le _ _).trans (Finset.expect_le_expect fun ω _ => hker ω)
      _ = 𝔼 H, η H := Tape.expect_oracle η

/-! #### The real and the simulated games -/

/-- The real environment's responder is hybrid `0`'s. -/
theorem envResponder_realEnv {Q : ℕ} (ω : Tape X Y Sd C SC Q) :
    envResponder (realEnv rel P Q) (ω.oracle, fun i => ⟨ω.salts i, ω.proverCoins i⟩) =
      hybResp rel P S 0 ω := by
  funext i req O
  simp only [envResponder, hybResp, proverReply, realEnv]
  split_ifs <;> first | rfl | omega

/-- The simulated environment's responder is hybrid `Q`'s. -/
theorem envResponder_simEnv {Q : ℕ} (ω : Tape X Y Sd C SC Q) :
    envResponder (simEnv rel S Q) (ω.oracle, fun i => ⟨ω.salts i, ω.simCoins i⟩) =
      hybResp rel P S Q ω := by
  funext i req O
  simp only [envResponder, hybResp, simulatorReply, simEnv]
  split_ifs <;> first | rfl | omega

/-- The tape of `Q` proof queries with uniform coins is uniform. -/
theorem tapeDist_uniformOfFintype {Q : ℕ} {Cx : Type} [Fintype Cx] [Nonempty Cx] :
    tapeDist (X := X) (Y := Y) Q (PMF.uniformOfFintype Cx) =
      PMF.uniformOfFintype ((X → Y) × (Fin Q → Cx)) := by
  rw [tapeDist, PMF.pi_uniformOfFintype, PMF.uniformOfFintype_prod_eq_bind]

/-- **The real game is hybrid `0`**, for a prover with uniform coins. -/
theorem toReal_acceptProb_realEnv {m : ℕ} (A : IAlg X Y Stmt Wit Proof m) {Q : ℕ}
    (hP : P.coins = PMF.uniformOfFintype (SaltedCoins Sd C)) :
    (A.acceptProb (realEnv rel P Q)).toReal = hyb rel P S A Q 0 := by
  classical
  have hμ : (realEnv rel P Q).μ = PMF.uniformOfFintype ((X → Y) × (Fin Q → SaltedCoins Sd C)) := by
    change tapeDist Q P.coins = _
    rw [hP, tapeDist_uniformOfFintype]
  rw [IAlg.acceptProb, hμ]
  change (GordieHowe.IOP.probUniform ((X → Y) × (Fin Q → SaltedCoins Sd C)) fun p =>
    A.accepts (envResponder (realEnv rel P Q) p) p.1 = true).toReal = _
  rw [GordieHowe.IOP.toReal_probUniform]
  let e : Tape X Y Sd C SC Q ≃ ((X → Y) × (Fin Q → SaltedCoins Sd C)) × (Fin Q → SC) :=
    { toFun := fun ω => ((ω.oracle, fun i => ⟨ω.salts i, ω.proverCoins i⟩), ω.simCoins)
      invFun := fun q => ⟨q.1.1, fun i => (q.1.2 i).salt, fun i => (q.1.2 i).coins, q.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [hyb, Fintype.expect_equiv e _ (fun q => if A.accepts (envResponder (realEnv rel P Q) q.1) q.1.1 = true
    then (1 : ℝ) else 0) fun ω => by rw [Equiv.coe_fn_mk, envResponder_realEnv (S := S)]; rfl]
  exact (expect_prod_fst (fun c => if A.accepts (envResponder (realEnv rel P Q) c) c.1 = true
    then (1 : ℝ) else 0)).symm

/-- **The simulated game is hybrid `Q`.** -/
theorem toReal_acceptProb_simEnv {m : ℕ} (A : IAlg X Y Stmt Wit Proof m) {Q : ℕ} :
    (A.acceptProb (simEnv rel S Q)).toReal = hyb rel P S A Q Q := by
  classical
  have hμ : (simEnv rel S Q).μ = PMF.uniformOfFintype ((X → Y) × (Fin Q → SaltedCoins Sd SC)) := by
    change tapeDist Q S.coins = _
    rw [NARG.SimulatorFn.coins_eq_uniform, tapeDist_uniformOfFintype]
  rw [IAlg.acceptProb, hμ]
  change (GordieHowe.IOP.probUniform ((X → Y) × (Fin Q → SaltedCoins Sd SC)) fun p =>
    A.accepts (envResponder (simEnv rel S Q) p) p.1 = true).toReal = _
  rw [GordieHowe.IOP.toReal_probUniform]
  let e : Tape X Y Sd C SC Q ≃ ((X → Y) × (Fin Q → SaltedCoins Sd SC)) × (Fin Q → C) :=
    { toFun := fun ω => ((ω.oracle, fun i => ⟨ω.salts i, ω.simCoins i⟩), ω.proverCoins)
      invFun := fun q => ⟨q.1.1, fun i => (q.1.2 i).salt, q.2, fun i => (q.1.2 i).coins⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [hyb, Fintype.expect_equiv e _ (fun q => if A.accepts (envResponder (simEnv rel S Q) q.1) q.1.1 = true
    then (1 : ℝ) else 0) fun ω => by rw [Equiv.coe_fn_mk, envResponder_simEnv (P := P)]; rfl]
  exact (expect_prod_fst (fun c => if A.accepts (envResponder (simEnv rel S Q) c) c.1 = true
    then (1 : ℝ) else 0)).symm

/-- The sum of the errors of the proof queries. -/
theorem sum_range_stepError (t c e : ℝ) (Q : ℕ) :
    ∑ j ∈ range Q, ((t + j) / c + e) = Q * t / c + Q * (Q - 1) / (2 * c) + Q * e := by
  induction Q with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    by_cases hc : c = 0
    · simp [hc]
      ring
    · field_simp
      ring

/-- **The hybrids from the real to the simulated game**: hybrids `0` and `Q` differ by at most
`Q t / |Sd| + Q (Q - 1) / (2 |Sd|) + Q · 𝔼 H, η H` for an algorithm with a budget of `t`
queries. -/
theorem abs_hyb_zero_sub_le [Fintype Proof] (hloc : SaltedLocal saltOf P S) {η : (X → Y) → ℝ}
    (hcl : SliceCloseAt saltOf rel P S η) {m t : ℕ} (A : IAlg X Y Stmt Wit Proof m)
    (hA : A.Budget t) (Q : ℕ) :
    |hyb rel P S A Q 0 - hyb rel P S A Q Q| ≤
      Q * t / Fintype.card Sd + Q * (Q - 1) / (2 * Fintype.card Sd) + Q * 𝔼 H, η H := by
  rw [← Finset.sum_range_sub' (fun j => hyb rel P S A Q j), ← sum_range_stepError]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j hj => ?_)
  exact abs_hyb_sub_le hloc hcl A hA (Finset.mem_range.1 hj)

/-! ### The theorem -/

/-- **Zero knowledge of a salted argument in the classical random-oracle model.** For a prover
and a simulator local in their salt (`hloc`) whose real and simulated slice laws are within
`η H` at every salt (`hcl`), every classical adversary with a budget of `t` queries and `Q`
proof queries answered has advantage at most

    Q t / |Sd| + Q (Q - 1) / (2 |Sd|) + Q · 𝔼 H, η H

between the honest prover `P` and the simulator `S`, unbounded after its steps. -/
theorem zeroKnowledge_of_sliceCloseAt [Fintype Proof] (hloc : SaltedLocal saltOf P S)
    {η : (X → Y) → ℝ} (hcl : SliceCloseAt saltOf rel P S η) :
    ZeroKnowledge rel P S fun t Q =>
      Q * t / Fintype.card Sd + Q * (Q - 1) / (2 * Fintype.card Sd) + Q * 𝔼 H, η H := by
  intro m t Q 𝒜
  refine 𝒜.abs_acceptProb_sub_le _ _ fun r => ?_
  rw [toReal_acceptProb_realEnv (S := S) (𝒜.alg r) hloc.coins_eq,
    toReal_acceptProb_simEnv (P := P) (𝒜.alg r)]
  exact abs_hyb_zero_sub_le hloc hcl (𝒜.alg r) (𝒜.budget r) Q

end Salted

end GordieHowe.ROM.NIZK
