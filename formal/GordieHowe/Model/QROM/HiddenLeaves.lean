-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.ROM.HiddenLeaves
public import GordieHowe.Model.Quantum.O2H.WholeRun
public import GordieHowe.Model.Quantum.Pure.GameTape

@[expose] public section

/-!
# Hidden leaf digests against quantum distinguishers with every query counted

The quantum counterpart of `GordieHowe/Model/ROM/HiddenLeaves.lean`: for a leaf kernel `L` with its laws
(`LeafKernel.Laws`), the games of the honest-digest kernel `L.kL` and of the uniform-digest kernel
`L.kD`, against a distinguisher with a budget of `q` query slots and no final unitary (so every
query is counted, `GordieHowe/Model/Quantum/Pure/PostSlots.lean`), differ by at most
`Q (4 q √(n |Pos| / |N|) + 2 pBad)` (`abs_acceptProb_progEnv_kL_sub_kD_le`), with `pBad` the
probability of a collision of the salts of one proof query with each other, with a public salt or
with a salt of a proof query's coins.

**The argument**, per proof query `j` of the hybrid (`kD` below `j`, `kL` from `j` on), on one tape
(`LeafTape`) holding the initial oracle, the coins of every proof query, a fresh salt per position
(`secret`, the hidden salts of proof query `j`) and a fresh function (`table`):

1. (mux, exact kernel replacement) Proof query `j` takes its hidden salts from `secret`
   (`muxCoins`); its reply reads only the other salts, so the law of the reply is unchanged.
2. (relabel, exact) The initial oracle answers the inputs carrying a salt of `secret` by `table`.
3. (bad tape) Off the tapes where a salt of `secret` collides (`Bad`), the proof queries other than `j`
   read neither `table` nor the oracle on those inputs.
4. (O2H before proof query `j`, `2 q √(n |Pos| / |N|)`) Before proof query `j` the oracle is the plain
   oracle, and proof query `j` first answers the inputs of `secret` by `table` (a shift): the oracles
   differ only before proof query `j`, on inputs carrying a fresh salt
   (`Distinguisher.advantage_acceptProbOn_made_le_of_fresh_secret_budget`).
5. (swap, exact kernel replacement) Proof query `j` fills the hidden points of `table` from its drawn
   digests and reads them there (`fill`).
6. (bad tape) As in 3.
7. (O2H over the whole run, `2 q √(n |Pos| / |N|)`) Proof query `j` no longer shifts the oracle and
   reads its drawn digests: the uniform-digest reply. The oracles differ only after proof query `j`,
   on inputs carrying a salt of `secret`, which nothing else reads
   (`Distinguisher.advantage_acceptProb_le_of_fresh_secret_budget`).
8. (mux back, exact) Proof query `j`'s salts are its own again.
-/

open Finset
open scoped BigOperators

namespace GordieHowe

/-! ### Reindexed environments -/

namespace Quantum.Env

variable {Ω Ω' Req A X Y : Type*} {Q : ℕ}

/-- **An environment read through an equivalence of tapes.** -/
noncomputable def reindex (E : Env Ω Req A X Y Q) (e : Ω ≃ Ω') : Env Ω' Req A X Y Q where
  μ := E.μ.map e
  oracle₀ ω := E.oracle₀ (e.symm ω)
  respond ω := E.respond (e.symm ω)

/-- **Oracles of two environments related along the proof queries**: if the initial oracles are related
at `0`, and every proof query numbered `c < Q` maps related oracles to related oracles at `c + 1`,
and related oracles stay related after proof query `Q`, the oracles after any proof queries are related at
their number. -/
theorem oracleIn_rel {Ω' : Type*} (E : Env Ω Req A X Y Q) (E' : Env Ω' Req A X Y Q) {ω : Ω}
    {ω' : Ω'} (R : ℕ → (X → Y) → (X → Y) → Prop) (h0 : R 0 (E.oracle₀ ω) (E'.oracle₀ ω'))
    (hstep : ∀ c (hc : c < Q) req H H', R c H H' →
      R (c + 1) (E.respond ω ⟨c, hc⟩ req H).state (E'.respond ω' ⟨c, hc⟩ req H').state)
    (hQ : ∀ c H H', Q ≤ c → R c H H' → R (c + 1) H H') :
    ∀ rs : List Req, R rs.length (E.oracleIn ω rs) (E'.oracleIn ω' rs) := by
  intro rs
  induction rs using List.reverseRecOn with
  | nil => exact h0
  | append_singleton l a ih =>
    rw [oracleIn_append_singleton, oracleIn_append_singleton, List.length_append,
      List.length_singleton]
    simp only [update]
    split_ifs with hc
    · exact hstep _ hc a _ _ ih
    · exact hQ _ _ _ (not_lt.1 hc) ih

/-- Related environments give the same answers when their responses at related oracles agree. -/
theorem answerAfter_eq_of_rel {Ω' : Type*} (E : Env Ω Req A X Y Q) (E' : Env Ω' Req A X Y Q)
    {ω : Ω} {ω' : Ω'} (R : ℕ → (X → Y) → (X → Y) → Prop)
    (hrel : ∀ rs : List Req, R rs.length (E.oracleIn ω rs) (E'.oracleIn ω' rs))
    (hresp : ∀ c (hc : c < Q) req H H', R c H H' →
      (E.respond ω ⟨c, hc⟩ req H).response = (E'.respond ω' ⟨c, hc⟩ req H').response)
    (rs : List Req) (req : Req) : E.answerAfter ω rs req = E'.answerAfter ω' rs req := by
  unfold answerAfter
  split_ifs with h
  · exact hresp _ h req _ _ (hrel rs)
  · rfl

@[simp] theorem oracleIn_reindex (E : Env Ω Req A X Y Q) (e : Ω ≃ Ω') (ω : Ω') (rs : List Req) :
    (E.reindex e).oracleIn ω rs = E.oracleIn (e.symm ω) rs :=
  rfl

@[simp] theorem answerAfter_reindex (E : Env Ω Req A X Y Q) (e : Ω ≃ Ω') (ω : Ω') (rs : List Req)
    (req : Req) : (E.reindex e).answerAfter ω rs req = E.answerAfter (e.symm ω) rs req :=
  rfl

end Quantum.Env

namespace Quantum.Distinguisher

variable {W X Y Req A : Type*} [Fintype W] [Fintype X] [Fintype Y] [Fintype Req] [Fintype A]
  {n m : ℕ} (D : Distinguisher W X Y Req A n m) [DecidableEq Req] [DecidableEq A] [AddGroup Y]
  {Q : ℕ} (post : (X → Y) → QState (DReg W n X Y Req A) ≃ₗᵢ[ℂ] QState (DReg W n X Y Req A))

/-- **Reindexing the tape keeps the game.** -/
theorem acceptProbOn_reindex {Ω Ω' : Type*} [Fintype Ω] [Fintype Ω'] (E : Env Ω Req A X Y Q)
    (e : Ω ≃ Ω') (L : Set (LogReg Req m)) :
    D.acceptProbOn (E.reindex e) post L = D.acceptProbOn E post L :=
  (D.acceptProbOn_comap post e rfl (fun ω => by simp [Env.reindex])
    (fun ω => by simp [Env.reindex]) L).symm

theorem acceptProb_reindex {Ω Ω' : Type*} [Fintype Ω] [Fintype Ω'] (E : Env Ω Req A X Y Q)
    (e : Ω ≃ Ω') : D.acceptProb (E.reindex e) post = D.acceptProb E post := by
  rw [← acceptProbOn_univ, ← acceptProbOn_univ, acceptProbOn_reindex]

end Quantum.Distinguisher

theorem Quantum.PMF.uniformOfFintype_prod_apply {V R : Type*} [Fintype V] [Nonempty V] [Fintype R]
    [Nonempty R] (v : V) (r : R) :
    PMF.uniformOfFintype (V × R) (v, r) = PMF.uniformOfFintype V v * PMF.uniformOfFintype R r := by
  simp [PMF.uniformOfFintype_apply, Fintype.card_prod, ENNReal.mul_inv]



/-- The first component of a uniform pair equals a function of the second with probability
`1 / |α|`. -/
theorem Quantum.PMF.toReal_uniform_fst_eq_fn {α β : Type*} [Fintype α] [Nonempty α] [Fintype β]
    [Nonempty β] (g : β → α) :
    ((PMF.uniformOfFintype (α × β)).toOuterMeasure {x | x.1 = g x.2}).toReal =
      (Fintype.card α : ℝ)⁻¹ := by
  classical
  rw [PMF.toReal_toOuterMeasure_apply, Fintype.sum_prod_type, Finset.sum_comm]
  simp only [Set.mem_ofPred_eq, PMF.toReal_uniformOfFintype_apply, Fintype.card_prod]
  have : ∀ b : β, ∑ a : α, (if a = g b then ((Fintype.card α : ℝ) * Fintype.card β)⁻¹ else 0) =
      ((Fintype.card α : ℝ) * Fintype.card β)⁻¹ := fun b => by
    rw [Finset.sum_ite_eq']
    simp
  simp only [Nat.cast_mul, this, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hb : (Fintype.card β : ℝ) ≠ 0 := by simp
  field_simp

/-- Through an equivalence with a pair, an event "first component equals a function of the
second" has probability `1 / |α|`. -/
theorem Quantum.PMF.toReal_uniform_eq_fn {Ω α β : Type*} [Fintype Ω] [Nonempty Ω] [Fintype α] [Nonempty α]
    [Fintype β] [Nonempty β] (e : Ω ≃ α × β) (g : β → α) :
    ((PMF.uniformOfFintype Ω).toOuterMeasure {ω | (e ω).1 = g (e ω).2}).toReal =
      (Fintype.card α : ℝ)⁻¹ := by
  rw [show {ω | (e ω).1 = g (e ω).2} = e ⁻¹' {x | x.1 = g x.2} from rfl,
    ← PMF.toOuterMeasure_map_apply, PMF.map_uniformOfFintype_equiv, PMF.toReal_uniform_fst_eq_fn]

/-- A uniform function takes a given value at a given point with probability `1 / |N|`. -/
theorem Quantum.PMF.toReal_uniform_eval_eq {Pos N : Type*} [Fintype Pos] [DecidableEq Pos] [Fintype N]
    [Nonempty N] (p : Pos) (a : N) :
    ((PMF.uniformOfFintype (Pos → N)).toOuterMeasure {σ | σ p = a}).toReal =
      (Fintype.card N : ℝ)⁻¹ := by
  have h : {σ : Pos → N | σ p = a} =
      (Equiv.piSplitAt p fun _ => N) ⁻¹' {x | x.1 = a} := by
    ext σ
    simp [Equiv.piSplitAt]
  rw [h, ← PMF.toOuterMeasure_map_apply, PMF.map_uniformOfFintype_equiv,
    PMF.toOuterMeasure_uniformOfFintype_fst_eq]

/-- A uniform function takes a given value somewhere with probability at most `|Pos| / |N|`. -/
theorem Quantum.PMF.toReal_uniform_exists_eval_le {Pos N : Type*} [Fintype Pos] [DecidableEq Pos]
    [Fintype N] [Nonempty N] (a : N) :
    ((PMF.uniformOfFintype (Pos → N)).toOuterMeasure {σ | ∃ p, σ p = a}).toReal ≤
      Fintype.card Pos / Fintype.card N := by
  rw [show {σ : Pos → N | ∃ p, σ p = a} = ⋃ p, {σ | σ p = a} by ext; simp]
  refine (PMF.toReal_toOuterMeasure_iUnion_le _ _).trans_eq ?_
  simp only [PMF.toReal_uniform_eval_eq, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

namespace QROM

open GordieHowe.ROM.NIZK

variable {X Y Stmt Wit Proof Cm Pos N : Type}

/-! ### The tape of the leaf hybrids -/

/-- **The tape of the quantum leaf hybrids**: the initial oracle, the coins of each proof query, a fresh
salt per position and a fresh function. -/
@[ext]
structure LeafTape (X Y Cm Pos N : Type) (Q : ℕ) where
  /-- The initial oracle. -/
  oracle : X → Y
  /-- The coins of each proof query. -/
  coins : Fin Q → LeafCoins Cm Pos N Y
  /-- A fresh salt per position: the hidden salts of the proof query of the step. -/
  secret : Pos → N
  /-- A fresh function, answering the inputs carrying a salt of `secret`. -/
  table : X → Y

/-- The tape as its four parts. -/
def LeafTape.equivProd (X Y Cm Pos N : Type) (Q : ℕ) : LeafTape X Y Cm Pos N Q ≃
    (X → Y) × (Fin Q → LeafCoins Cm Pos N Y) × (Pos → N) × (X → Y) where
  toFun t := (t.oracle, t.coins, t.secret, t.table)
  invFun p := ⟨p.1, p.2.1, p.2.2.1, p.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

variable [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y] [Fintype Cm] [Nonempty Cm]
  [Fintype Pos] [DecidableEq Pos] [Fintype N] [DecidableEq N] [Nonempty N] {Q : ℕ}

instance : Fintype (LeafTape X Y Cm Pos N Q) :=
  Fintype.ofEquiv _ (LeafTape.equivProd X Y Cm Pos N Q).symm

instance : Nonempty (LeafTape X Y Cm Pos N Q) :=
  ⟨⟨fun _ => Classical.arbitrary _, fun _ => Classical.arbitrary _, fun _ => Classical.arbitrary _,
    fun _ => Classical.arbitrary _⟩⟩

variable (rel : Stmt → Wit → Prop) [DecidableRel rel] (L : LeafKernel X Y Stmt Wit Proof Cm Pos N)
  (nsalt : X → Option N) (pub : Finset N)

/-- The kernel of proof query `i` in hybrid `j`: `kD` below `j`, `kL` from `j` on. -/
def hybKernel (j : ℕ) (i : Fin Q) : Kernel X Y Stmt Wit Proof (LeafCoins Cm Pos N Y) :=
  if (i : ℕ) < j then L.kD else L.kL

/-- **The environment of a step of the leaf hybrid**: the initial oracle `init`, proof query `j`
answered by `rj`, every other proof query `i` by the kernel of hybrid `j` with its coins. -/
noncomputable def leafStepEnv (j : Fin Q) (init : LeafTape X Y Cm Pos N Q → X → Y)
    (rj : LeafTape X Y Cm Pos N Q → ProofQuery Stmt Wit → (X → Y) → Quantum.EnvReply Proof (X → Y)) :
    Quantum.Env (LeafTape X Y Cm Pos N Q) (ProofQuery Stmt Wit) Proof X Y Q where
  μ := PMF.uniformOfFintype _
  oracle₀ := init
  respond t i := if i = j then rj t else kernelReply rel (hybKernel L j i) (t.coins i)

/-- **Hybrid `j` of the leaf kernels** on the leaf tape: `kD` below proof query `j`, `kL` from `j`
on. -/
noncomputable def leafHybEnv (j : ℕ) : Quantum.Env (LeafTape X Y Cm Pos N Q) (ProofQuery Stmt Wit) Proof X Y Q where
  μ := PMF.uniformOfFintype _
  oracle₀ t := t.oracle
  respond t i := kernelReply rel (hybKernel L j i) (t.coins i)

/-! ### The step: proof query `j`'s replies -/

section Step

variable (j : Fin Q)

/-- **Proof query `j`'s coins with the hidden salts from `secret`**: the salt of a position hidden at
the proof query is the tape's fresh salt, the salt of another position is the coins' own. -/
def muxCoins (t : LeafTape X Y Cm Pos N Q) (req : ProofQuery Stmt Wit) : LeafCoins Cm Pos N Y :=
  ⟨(t.coins j).main, fun p => if L.hidden req (t.coins j).main p then t.secret p
    else (t.coins j).salts p, (t.coins j).digests⟩

/-- The oracle `H` with the inputs carrying a salt of `secret` answered by `table`. -/
noncomputable def shiftOracle (t : LeafTape X Y Cm Pos N Q) (H : X → Y) : X → Y :=
  replaceSlice (inSalts nsalt t.secret) () H t.table

/-- Proof query `j` answered by the kernel `K` with its coins (the hybrid's reply). -/
def rCoins (K : Kernel X Y Stmt Wit Proof (LeafCoins Cm Pos N Y)) (t : LeafTape X Y Cm Pos N Q) :
    ProofQuery Stmt Wit → (X → Y) → Quantum.EnvReply Proof (X → Y) :=
  kernelReply rel K (t.coins j)

/-- Proof query `j` answered by the kernel `K` with its hidden salts from `secret`. -/
def rMux (K : Kernel X Y Stmt Wit Proof (LeafCoins Cm Pos N Y)) (t : LeafTape X Y Cm Pos N Q)
    (req : ProofQuery Stmt Wit) (H : X → Y) : Quantum.EnvReply Proof (X → Y) :=
  kernelReply rel K (muxCoins L j t req) req H

/-- Proof query `j` first answers the inputs of `secret` by `table`, then replies with honest
digests. -/
noncomputable def rShift (t : LeafTape X Y Cm Pos N Q) (req : ProofQuery Stmt Wit) (H : X → Y) :
    Quantum.EnvReply Proof (X → Y) :=
  rMux rel L j L.kL t req (shiftOracle nsalt t H)

/-- Proof query `j` first answers the inputs of `secret` by `table` and its hidden points by its drawn
digests, then replies with honest digests. -/
noncomputable def rFill (t : LeafTape X Y Cm Pos N Q) (req : ProofQuery Stmt Wit) (H : X → Y) :
    Quantum.EnvReply Proof (X → Y) :=
  rMux rel L j L.kL t req (fill (L.hidden req (t.coins j).main)
    (fun p => L.point req (t.coins j).main p (t.secret p)) (shiftOracle nsalt t H)
    (t.coins j).digests)

/-- The tapes on which a salt of `secret` collides: with a public salt, with a salt of some
proof query's coins, or with another salt of `secret`. -/
def LeafBad (t : LeafTape X Y Cm Pos N Q) : Prop :=
  (∃ a ∈ pub, ∃ p, t.secret p = a) ∨ (∃ i p q, (t.coins i).salts p = t.secret q) ∨
    ¬ Function.Injective t.secret

/-- **An environment patched on a set of tapes**: `F` on the tapes of `B`, `E` elsewhere. -/
noncomputable def patchEnv (B : Set (LeafTape X Y Cm Pos N Q))
    (E F : Quantum.Env (LeafTape X Y Cm Pos N Q) (ProofQuery Stmt Wit) Proof X Y Q) :
    Quantum.Env (LeafTape X Y Cm Pos N Q) (ProofQuery Stmt Wit) Proof X Y Q :=
  open Classical in
  { μ := E.μ
    oracle₀ t := if t ∈ B then F.oracle₀ t else E.oracle₀ t
    respond t := if t ∈ B then F.respond t else E.respond t }

/-! ### Splitting the tape at proof query `j` -/

/-- The tape as the part read by the proof queries other than `j` (the oracle, their coins, the table)
and proof query `j`'s coins with the fresh salts. -/
def splitJ : LeafTape X Y Cm Pos N Q ≃
    ((X → Y) × ({i : Fin Q // i ≠ j} → LeafCoins Cm Pos N Y) × (X → Y)) ×
      (LeafCoins Cm Pos N Y × (Pos → N)) where
  toFun t := ((t.oracle, fun i => t.coins i, t.table), (t.coins j, t.secret))
  invFun p := ⟨p.1.1, (Equiv.piSplitAt j _).symm (p.2.1, p.1.2.1), p.2.2, p.1.2.2⟩
  left_inv t := by
    obtain ⟨O, c, σ, T⟩ := t
    simp only [LeafTape.mk.injEq, true_and, and_true]
    exact (Equiv.piSplitAt j _).symm_apply_apply c
  right_inv p := by
    obtain ⟨⟨O, c, T⟩, cj, σ⟩ := p
    simp only [Prod.mk.injEq]
    refine ⟨⟨trivial, ?_, trivial⟩, ?_, trivial⟩ <;> first
      | (funext i; simp [Equiv.piSplitAt, i.2])
      | simp [Equiv.piSplitAt]

end Step

section SplitLemmas

variable (j : Fin Q)

@[simp] theorem splitJ_symm_oracle (v : (X → Y) × ({i : Fin Q // i ≠ j} → LeafCoins Cm Pos N Y) × (X → Y))
    (τ : LeafCoins Cm Pos N Y × (Pos → N)) : ((splitJ j).symm (v, τ)).oracle = v.1 := rfl

@[simp] theorem splitJ_symm_table (v : (X → Y) × ({i : Fin Q // i ≠ j} → LeafCoins Cm Pos N Y) × (X → Y))
    (τ : LeafCoins Cm Pos N Y × (Pos → N)) : ((splitJ j).symm (v, τ)).table = v.2.2 := rfl

@[simp] theorem splitJ_symm_secret (v : (X → Y) × ({i : Fin Q // i ≠ j} → LeafCoins Cm Pos N Y) × (X → Y))
    (τ : LeafCoins Cm Pos N Y × (Pos → N)) : ((splitJ j).symm (v, τ)).secret = τ.2 := rfl

@[simp] theorem splitJ_symm_coins_self (v : (X → Y) × ({i : Fin Q // i ≠ j} → LeafCoins Cm Pos N Y) × (X → Y))
    (τ : LeafCoins Cm Pos N Y × (Pos → N)) : ((splitJ j).symm (v, τ)).coins j = τ.1 := by
  simp [splitJ, Equiv.piSplitAt]

theorem splitJ_symm_coins_ne (v : (X → Y) × ({i : Fin Q // i ≠ j} → LeafCoins Cm Pos N Y) × (X → Y))
    (τ : LeafCoins Cm Pos N Y × (Pos → N)) {i : Fin Q} (hi : i ≠ j) :
    ((splitJ j).symm (v, τ)).coins i = v.2.1 ⟨i, hi⟩ := by
  simp [splitJ, Equiv.piSplitAt, hi]

/-- The uniform tape, split at proof query `j`, is a product. -/
theorem map_splitJ_uniform_apply (v : (X → Y) × ({i : Fin Q // i ≠ j} → LeafCoins Cm Pos N Y) × (X → Y))
    (τ : LeafCoins Cm Pos N Y × (Pos → N)) :
    ((PMF.uniformOfFintype (LeafTape X Y Cm Pos N Q)).map (splitJ j)) (v, τ) =
      PMF.uniformOfFintype _ v * PMF.uniformOfFintype _ τ := by
  rw [PMF.map_uniformOfFintype_equiv, Quantum.PMF.uniformOfFintype_prod_apply]

end SplitLemmas


/-- The tape as the part read outside proof query `j`'s digests and table (the oracle, the other
proof queries' coins, the fresh salts) and proof query `j`'s coins with the table. -/
def splitT (j : Fin Q) : LeafTape X Y Cm Pos N Q ≃
    ((X → Y) × ({i : Fin Q // i ≠ j} → LeafCoins Cm Pos N Y) × (Pos → N)) ×
      (LeafCoins Cm Pos N Y × (X → Y)) where
  toFun t := ((t.oracle, fun i => t.coins i, t.secret), (t.coins j, t.table))
  invFun p := ⟨p.1.1, (Equiv.piSplitAt j _).symm (p.2.1, p.1.2.1), p.1.2.2, p.2.2⟩
  left_inv t := by
    obtain ⟨O, c, σ, T⟩ := t
    simp only [LeafTape.mk.injEq, true_and, and_true]
    exact (Equiv.piSplitAt j _).symm_apply_apply c
  right_inv p := by
    obtain ⟨⟨O, c, σ⟩, cj, T⟩ := p
    simp only [Prod.mk.injEq]
    refine ⟨⟨trivial, ?_, trivial⟩, ?_, trivial⟩ <;> first
      | (funext i; simp [Equiv.piSplitAt, i.2])
      | simp [Equiv.piSplitAt]

section SplitTLemmas

variable (j : Fin Q) (v : (X → Y) × ({i : Fin Q // i ≠ j} → LeafCoins Cm Pos N Y) × (Pos → N))
  (τ : LeafCoins Cm Pos N Y × (X → Y))

@[simp] theorem splitT_symm_oracle : ((splitT j).symm (v, τ)).oracle = v.1 := rfl
@[simp] theorem splitT_symm_secret : ((splitT j).symm (v, τ)).secret = v.2.2 := rfl
@[simp] theorem splitT_symm_table : ((splitT j).symm (v, τ)).table = τ.2 := rfl
@[simp] theorem splitT_symm_coins_self : ((splitT j).symm (v, τ)).coins j = τ.1 := by
  simp [splitT, Equiv.piSplitAt]
theorem splitT_symm_coins_ne {i : Fin Q} (hi : i ≠ j) :
    ((splitT j).symm (v, τ)).coins i = v.2.1 ⟨i, hi⟩ := by
  simp [splitT, Equiv.piSplitAt, hi]

theorem map_splitT_uniform_apply :
    ((PMF.uniformOfFintype (LeafTape X Y Cm Pos N Q)).map (splitT j)) (v, τ) =
      PMF.uniformOfFintype _ v * PMF.uniformOfFintype _ τ := by
  rw [PMF.map_uniformOfFintype_equiv, Quantum.PMF.uniformOfFintype_prod_apply]

end SplitTLemmas


/-- The tape as everything but the fresh salts, and the fresh salts. -/
def splitS : LeafTape X Y Cm Pos N Q ≃
    ((X → Y) × (Fin Q → LeafCoins Cm Pos N Y) × (X → Y)) × (Pos → N) where
  toFun t := ((t.oracle, t.coins, t.table), t.secret)
  invFun p := ⟨p.1.1, p.1.2.1, p.2, p.1.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem map_splitS_uniform_apply (v : (X → Y) × (Fin Q → LeafCoins Cm Pos N Y) × (X → Y))
    (σ : Pos → N) :
    ((PMF.uniformOfFintype (LeafTape X Y Cm Pos N Q)).map splitS) (v, σ) =
      PMF.uniformOfFintype _ v * PMF.uniformOfFintype _ σ := by
  rw [PMF.map_uniformOfFintype_equiv, Quantum.PMF.uniformOfFintype_prod_apply]

/-- An input carries one of the fresh salts with probability at most `|Pos| / |N|`. -/
theorem toReal_inSalts_le (nsalt : X → Option N) (x : X) :
    ((PMF.uniformOfFintype (Pos → N)).toOuterMeasure {σ | x ∈ {y | inSalts nsalt σ y = some ()}}).toReal ≤
      Fintype.card Pos / Fintype.card N := by
  rcases h : nsalt x with _ | a
  · have : {σ : Pos → N | x ∈ {y | inSalts nsalt σ y = some ()}} = ∅ := by
      ext σ
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      exact inSalts_eq_none_of_salt_none h
    rw [this]
    simp only [MeasureTheory.measure_empty, ENNReal.toReal_zero]
    positivity
  · refine le_trans (ENNReal.toReal_mono ?_ (MeasureTheory.measure_mono fun σ hσ => ?_))
      (Quantum.PMF.toReal_uniform_exists_eval_le a)
    · exact ne_of_lt (lt_of_le_of_lt (PMF.toOuterMeasure_apply_le_one _ _) ENNReal.one_lt_top)
    · obtain ⟨p, hp⟩ := inSalts_eq_some_iff.1 hσ
      rw [h] at hp
      exact ⟨p, (Option.some_injective _ hp).symm⟩

/-- **Swapping the hidden salts of coins with fresh salts** (an involution of the coins and the
fresh salts at a proof query and further coins). -/
def muxSwap (req : ProofQuery Stmt Wit) : Equiv.Perm (LeafCoins Cm Pos N Y × (Pos → N)) :=
  Function.Involutive.toPerm (fun τ => (⟨τ.1.main, fun p => if L.hidden req τ.1.main p then τ.2 p
      else τ.1.salts p, τ.1.digests⟩, fun p => if L.hidden req τ.1.main p then τ.1.salts p else τ.2 p))
    fun τ => by
      obtain ⟨⟨m, s, d⟩, σ⟩ := τ
      simp only [Prod.mk.injEq]
      refine ⟨?_, ?_⟩
      · congr 1
        funext p
        split_ifs <;> rfl
      · funext p
        split_ifs <;> rfl

section Game

variable [AddGroup Y] [Fintype Stmt] [Fintype Wit] [DecidableEq Stmt] [DecidableEq Wit]
  [Fintype Proof] [DecidableEq Proof] {W : Type*} [Fintype W] {n m : ℕ}
  (D : Quantum.Distinguisher W X Y (ProofQuery Stmt Wit) Proof n m)
  (post : (X → Y) → Quantum.QState (Quantum.DReg W n X Y (ProofQuery Stmt Wit) Proof) ≃ₗᵢ[ℂ]
    Quantum.QState (Quantum.DReg W n X Y (ProofQuery Stmt Wit) Proof))

/-- The law of proof query `j`'s reply with its coins and with its hidden salts from `secret`. -/
theorem map_rCoins_eq_map_rMux (j : Fin Q) (K : Kernel X Y Stmt Wit Proof (LeafCoins Cm Pos N Y))
    (v : (X → Y) × ({i : Fin Q // i ≠ j} → LeafCoins Cm Pos N Y) × (X → Y))
    (req : ProofQuery Stmt Wit) (H : X → Y) :
    (PMF.uniformOfFintype (LeafCoins Cm Pos N Y × (Pos → N))).map
        (fun τ => rCoins rel j K ((splitJ j).symm (v, τ)) req H) =
      (PMF.uniformOfFintype (LeafCoins Cm Pos N Y × (Pos → N))).map
        (fun τ => rMux rel L j K ((splitJ j).symm (v, τ)) req H) := by
  have hf : (fun τ => rMux rel L j K ((splitJ j).symm (v, τ)) req H) =
      (fun τ => rCoins rel j K ((splitJ j).symm (v, τ)) req H) ∘ muxSwap L req := by
    funext τ
    simp only [rMux, rCoins, muxCoins, splitJ_symm_coins_self, splitJ_symm_secret,
      Function.comp_apply]
    rfl
  rw [hf, ← PMF.map_comp, PMF.map_uniformOfFintype_equiv]

/-- **The hidden salts of proof query `j` from `secret`, exactly** (steps 1 and 8): for every kernel,
proof query `j` answered with its coins and with its hidden salts from `secret` give the same game. -/
theorem acceptProbOn_rCoins_eq_rMux (j : Fin Q) (K : Kernel X Y Stmt Wit Proof (LeafCoins Cm Pos N Y)) (Lg : Set (Quantum.LogReg (ProofQuery Stmt Wit) m)) :
    D.acceptProbOn (leafStepEnv rel L j (·.oracle) (rCoins rel j K)) post Lg =
      D.acceptProbOn (leafStepEnv rel L j (·.oracle) (rMux rel L j K)) post Lg := by
  rw [← D.acceptProbOn_reindex post _ (splitJ j), ← D.acceptProbOn_reindex post _ (splitJ j)]
  refine eq_of_abs_sub_nonpos ?_
  have h := D.abs_acceptProbOn_sub_le_of_kernel post
    ((leafStepEnv rel L j (·.oracle) (rCoins rel j K)).reindex (splitJ j))
    ((leafStepEnv rel L j (·.oracle) (rMux rel L j K)).reindex (splitJ j))
    (μV := PMF.uniformOfFintype _) (ν := PMF.uniformOfFintype _) (ν' := PMF.uniformOfFintype _)
    (fun v τ => map_splitJ_uniform_apply j v τ) (fun v τ => map_splitJ_uniform_apply j v τ) j
    (fun v τ τ' => rfl)
    (fun v τ τ' i hi => by
      simp only [Quantum.Env.reindex, leafStepEnv, if_neg hi, splitJ_symm_coins_ne j _ _ hi])
    (fun _ => 0) (fun _ => le_rfl)
    (fun v τ₀ req rs _ => by
      refine le_of_eq ?_
      simp only [Quantum.Env.reindex, leafStepEnv, ↓reduceIte]
      rw [map_rCoins_eq_map_rMux, PMF.tvDist_self])
    Lg
  simpa using h

/-- **Exchanging the oracle and the table on the inputs of `secret`**, an involution of tapes. -/
noncomputable def tableSwap : Equiv.Perm (LeafTape X Y Cm Pos N Q) :=
  Function.Involutive.toPerm (fun t => ⟨replaceSlice (inSalts nsalt t.secret) () t.oracle t.table,
      t.coins, t.secret, replaceSlice (inSalts nsalt t.secret) () t.table t.oracle⟩)
    fun t => by
      obtain ⟨O, c, σ, T⟩ := t
      simp only [LeafTape.mk.injEq, true_and]
      exact ⟨replaceSlice_replaceSlice_swap' _ _ _ _, by
        funext x
        by_cases h : inSalts nsalt σ x = some () <;> simp [replaceSlice, h]⟩

/-- **The relabel** (step 2, exact): the initial oracle answering the inputs of `secret` by
`table` gives the same game. -/
theorem acceptProbOn_shift_init (j : Fin Q)
    (rj : LeafTape X Y Cm Pos N Q → ProofQuery Stmt Wit → (X → Y) → Quantum.EnvReply Proof (X → Y))
    (hrj : ∀ t, rj (tableSwap nsalt t) = rj t) (Lg : Set (Quantum.LogReg (ProofQuery Stmt Wit) m)) :
    D.acceptProbOn (leafStepEnv rel L j (·.oracle) rj) post Lg =
      D.acceptProbOn (leafStepEnv rel L j (fun t => shiftOracle nsalt t t.oracle) rj) post Lg :=
  D.acceptProbOn_comap post (tableSwap nsalt)
    (PMF.map_uniformOfFintype_equiv (tableSwap nsalt)).symm
    (fun t => (replaceSlice_replaceSlice_swap' _ _ _ _).symm)
    (fun t => by
      funext i
      simp only [leafStepEnv]
      split_ifs
      · rw [hrj]
      · rfl) Lg

/-- **Filling the hidden points of the table from the drawn digests** (an involution of proof query
`j`'s coins and the table at a proof query, the further coins and injective fresh salts). -/
noncomputable def fillSwap (req : ProofQuery Stmt Wit) (σ : Pos → N) (hinj : Function.Injective σ)
    (hL : L.Laws nsalt pub) : Equiv.Perm (LeafCoins Cm Pos N Y × (X → Y)) :=
  Function.Involutive.toPerm (fun τ =>
      (⟨τ.1.main, τ.1.salts, fun p => if L.hidden req τ.1.main p then
        τ.2 (L.point req τ.1.main p (σ p)) else τ.1.digests p⟩,
        fill (L.hidden req τ.1.main) (fun p => L.point req τ.1.main p (σ p)) τ.2 τ.1.digests))
    fun τ => by
      obtain ⟨⟨m, s, d⟩, S⟩ := τ
      have hpt : ∀ p q, L.hidden req m p = true → L.hidden req m q = true →
          L.point req m p (σ p) = L.point req m q (σ q) → p = q := fun p q _ _ h =>
        hinj (Option.some_injective _ (by rw [← hL.point_salt req m p, ← hL.point_salt req m q, h]))
      simp only [Prod.mk.injEq]
      refine ⟨?_, ?_⟩
      · congr 1
        funext p
        by_cases hp : L.hidden req m p = true
        · simp only [hp, ite_true]
          exact fill_apply_pt hpt _ _ hp
        · simp only [hp, Bool.false_eq_true, ite_false]
      · funext x
        by_cases hx : ∃ p, L.hidden req m p = true ∧ L.point req m p (σ p) = x
        · obtain ⟨p, hp, rfl⟩ := hx
          rw [fill_apply_pt hpt _ _ hp, if_pos hp]
        · push Not at hx
          rw [fill_apply_of_forall_ne _ _ hx, fill_apply_of_forall_ne _ _ hx]

theorem fillSwap_apply (req : ProofQuery Stmt Wit) (σ : Pos → N) (hinj : Function.Injective σ)
    (hL : L.Laws nsalt pub) (τ : LeafCoins Cm Pos N Y × (X → Y)) :
    fillSwap L nsalt pub req σ hinj hL τ =
      (⟨τ.1.main, τ.1.salts, fun p => if L.hidden req τ.1.main p then
        τ.2 (L.point req τ.1.main p (σ p)) else τ.1.digests p⟩,
        fill (L.hidden req τ.1.main) (fun p => L.point req τ.1.main p (σ p)) τ.2 τ.1.digests) :=
  rfl

omit [AddGroup Y] [Fintype Stmt] [Fintype Wit] [DecidableEq Stmt] [DecidableEq Wit]
  [Fintype Proof] [DecidableEq Proof] in
/-- The honest-digest reply does not read the drawn digests of its coins. -/
theorem kernelReply_kL_congr_digests {c c' : LeafCoins Cm Pos N Y} (hm : c.main = c'.main)
    (hs : c.salts = c'.salts) : kernelReply rel L.kL c = kernelReply rel L.kL c' := by
  obtain ⟨m, s, d⟩ := c
  obtain ⟨m', s', d'⟩ := c'
  simp only at hm hs
  subst hm hs
  rfl

/-- The oracle read by the filled reply at the swapped coins is the shifted oracle. -/
theorem fill_replaceSlice_fill {ι : Type} (slot : X → Option Unit) (hid : ι → Bool) (pt : ι → X)
    (hinj : ∀ p q, hid p = true → hid q = true → pt p = pt q → p = q)
    (hslot : ∀ p, slot (pt p) = some ()) (H S : X → Y) (d : ι → Y) :
    fill hid pt (replaceSlice slot () H (fill hid pt S d)) (fun p => if hid p then S (pt p) else d p) =
      replaceSlice slot () H S := by
  funext x
  by_cases hx : ∃ p, hid p = true ∧ pt p = x
  · obtain ⟨p, hp, rfl⟩ := hx
    rw [fill_apply_pt hinj _ _ hp, if_pos hp]
    simp [replaceSlice, hslot p]
  · push Not at hx
    rw [fill_apply_of_forall_ne _ _ hx]
    simp only [replaceSlice]
    split_ifs
    · exact fill_apply_of_forall_ne _ _ hx
    · rfl

/-- The law of proof query `j`'s shifted reply and of its filled reply, at injective fresh salts. -/
theorem map_rShift_eq_map_rFill (hL : L.Laws nsalt pub) (j : Fin Q)
    (v : (X → Y) × ({i : Fin Q // i ≠ j} → LeafCoins Cm Pos N Y) × (Pos → N))
    (hinj : Function.Injective v.2.2) (req : ProofQuery Stmt Wit) (H : X → Y) :
    (PMF.uniformOfFintype (LeafCoins Cm Pos N Y × (X → Y))).map
        (fun τ => rShift rel L nsalt j ((splitT j).symm (v, τ)) req H) =
      (PMF.uniformOfFintype (LeafCoins Cm Pos N Y × (X → Y))).map
        (fun τ => rFill rel L nsalt j ((splitT j).symm (v, τ)) req H) := by
  have hf : (fun τ => rShift rel L nsalt j ((splitT j).symm (v, τ)) req H) =
      (fun τ => rFill rel L nsalt j ((splitT j).symm (v, τ)) req H) ∘
        fillSwap L nsalt pub req v.2.2 hinj hL := by
    funext τ
    obtain ⟨⟨m, s, d⟩, S⟩ := τ
    have hpt : ∀ p q, L.hidden req m p = true → L.hidden req m q = true →
        L.point req m p (v.2.2 p) = L.point req m q (v.2.2 q) → p = q := fun p q _ _ h =>
      hinj (Option.some_injective _ (by rw [← hL.point_salt req m p, ← hL.point_salt req m q, h]))
    rw [Function.comp_apply, fillSwap_apply]
    simp only [rShift, rFill, rMux, shiftOracle, muxCoins, splitT_symm_coins_self,
      splitT_symm_secret, splitT_symm_table]
    rw [fill_replaceSlice_fill _ _ _ hpt (fun p => inSalts_eq_some_iff.2 ⟨p, hL.point_salt _ _ _ _⟩)]
    exact congrFun (congrFun (kernelReply_kL_congr_digests rel L rfl rfl) req) _
  rw [hf, ← PMF.map_comp, PMF.map_uniformOfFintype_equiv]

/-- **Filling the hidden points from the drawn digests** (step 5): the shifted reply and the
filled reply give games at most the probability of a collision of the fresh salts apart. -/
theorem abs_acceptProbOn_rShift_sub_rFill_le (hL : L.Laws nsalt pub) (j : Fin Q)
    (Lg : Set (Quantum.LogReg (ProofQuery Stmt Wit) m)) :
    |D.acceptProbOn (leafStepEnv rel L j (·.oracle) (rShift rel L nsalt j)) post Lg -
      D.acceptProbOn (leafStepEnv rel L j (·.oracle) (rFill rel L nsalt j)) post Lg| ≤
      ∑ v : (X → Y) × ({i : Fin Q // i ≠ j} → LeafCoins Cm Pos N Y) × (Pos → N),
        (PMF.uniformOfFintype _ v).toReal * (if Function.Injective v.2.2 then 0 else 1) := by
  classical
  rw [← D.acceptProbOn_reindex post _ (splitT j), ← D.acceptProbOn_reindex post _ (splitT j)]
  refine D.abs_acceptProbOn_sub_le_of_kernel post
    ((leafStepEnv rel L j (·.oracle) (rShift rel L nsalt j)).reindex (splitT j))
    ((leafStepEnv rel L j (·.oracle) (rFill rel L nsalt j)).reindex (splitT j))
    (μV := PMF.uniformOfFintype _) (ν := PMF.uniformOfFintype _) (ν' := PMF.uniformOfFintype _)
    (fun v τ => map_splitT_uniform_apply j v τ) (fun v τ => map_splitT_uniform_apply j v τ) j
    (fun v τ τ' => rfl)
    (fun v τ τ' i hi => by
      simp only [Quantum.Env.reindex, leafStepEnv, if_neg hi, splitT_symm_coins_ne j _ _ hi])
    _ (fun v => by split_ifs <;> norm_num)
    (fun v τ₀ req rs _ => ?_) Lg
  split_ifs with hinj
  · refine le_of_eq ?_
    simp only [Quantum.Env.reindex, leafStepEnv, ↓reduceIte]
    rw [map_rShift_eq_map_rFill rel L nsalt pub hL j v hinj, PMF.tvDist_self]
  · exact PMF.tvDist_le_one _ _

/-! ### The environments of the step -/

/-- Step 2's environment: the initial oracle shifted, proof query `j` with its hidden salts from
`secret` and honest digests. -/
noncomputable def envB (j : Fin Q) : Quantum.Env (LeafTape X Y Cm Pos N Q) (ProofQuery Stmt Wit) Proof X Y Q :=
  leafStepEnv rel L j (fun t => shiftOracle nsalt t t.oracle) (rMux rel L j L.kL)

/-- Step 4's environment: the plain initial oracle, proof query `j` shifting it. -/
noncomputable def envC (j : Fin Q) : Quantum.Env (LeafTape X Y Cm Pos N Q) (ProofQuery Stmt Wit) Proof X Y Q :=
  leafStepEnv rel L j (·.oracle) (rShift rel L nsalt j)

/-- Step 5's environment: proof query `j` shifting and filling. -/
noncomputable def envD (j : Fin Q) : Quantum.Env (LeafTape X Y Cm Pos N Q) (ProofQuery Stmt Wit) Proof X Y Q :=
  leafStepEnv rel L j (·.oracle) (rFill rel L nsalt j)

/-- Step 7's environment: proof query `j` with uniform digests and its hidden salts from `secret`. -/
noncomputable def envE (j : Fin Q) : Quantum.Env (LeafTape X Y Cm Pos N Q) (ProofQuery Stmt Wit) Proof X Y Q :=
  leafStepEnv rel L j (·.oracle) (rMux rel L j L.kD)

/-- A tape off `LeafBad` has fresh salts off the public salts, off every coins' salts, and
injective. -/
structure LeafGood (t : LeafTape X Y Cm Pos N Q) : Prop where
  pub : ∀ a ∈ pub, ∀ p, t.secret p ≠ a
  coins : ∀ i p q, (t.coins i).salts p ≠ t.secret q
  inj : Function.Injective t.secret

theorem leafGood_of_not_bad {t : LeafTape X Y Cm Pos N Q} (h : ¬ LeafBad pub t) : LeafGood pub t where
  pub a ha p e := h (Or.inl ⟨a, ha, p, e⟩)
  coins i p q e := h (Or.inr (Or.inl ⟨i, p, q, e⟩))
  inj := by
    by_contra hi
    exact h (Or.inr (Or.inr hi))

omit [Fintype X] [Fintype Y] [Nonempty Y] [Fintype Cm] [Nonempty Cm] [Fintype Pos] [Fintype N]
  [Nonempty N] in
theorem hybKernel_of_lt {j : ℕ} {i : Fin Q} (h : (i : ℕ) < j) : hybKernel L j i = L.kD := if_pos h

omit [Fintype X] [Fintype Y] [Nonempty Y] [Fintype Cm] [Nonempty Cm] [Fintype Pos] [Fintype N]
  [Nonempty N] in
theorem hybKernel_of_ge {j : ℕ} {i : Fin Q} (h : j ≤ (i : ℕ)) : hybKernel L j i = L.kL :=
  if_neg (not_lt.2 h)

/-- The relation of the oracles of step 4 before and after proof query `j`: shifted up to proof query
`j`, equal after it. -/
def RelB (j : Fin Q) (t : LeafTape X Y Cm Pos N Q) (c : ℕ) (HC HB : X → Y) : Prop :=
  (c ≤ j → HB = shiftOracle nsalt t HC) ∧ ((j : ℕ) < c → HB = HC)

/-- **On a good tape the oracles of steps 2 and 4 are related**, and their responses agree. -/
theorem relB_step (hL : L.Laws nsalt pub) (j : Fin Q) {t : LeafTape X Y Cm Pos N Q}
    (hg : LeafGood pub t) (c : ℕ) (hc : c < Q) (req : ProofQuery Stmt Wit) (HC HB : X → Y)
    (hR : RelB nsalt j t c HC HB) :
    ((envC rel L nsalt j).respond t ⟨c, hc⟩ req HC).response =
        ((envB rel L nsalt j).respond t ⟨c, hc⟩ req HB).response ∧
      RelB nsalt j t (c + 1) ((envC rel L nsalt j).respond t ⟨c, hc⟩ req HC).state
        ((envB rel L nsalt j).respond t ⟨c, hc⟩ req HB).state := by
  rcases lt_trichotomy c j with hcj | hcj | hcj
  · have hne : (⟨c, hc⟩ : Fin Q) ≠ j := fun e => by rw [← e] at hcj; exact lt_irrefl _ hcj
    have hB := hR.1 hcj.le
    subst hB
    simp only [envC, envB, leafStepEnv, if_neg hne, hybKernel_of_lt L (show ((⟨c, hc⟩ : Fin Q) : ℕ) < j from hcj)]
    obtain ⟨h1, h2⟩ := (hL.kernelLocal_kD).reply_replaceSlice (rel := rel) (ν := t.secret)
      (c := t.coins ⟨c, hc⟩) (fun p q => hg.coins _ p q) (fun q hq => hg.pub _ hq q rfl) req HC t.table
    refine ⟨h1.symm, fun _ => ?_, fun h => absurd h (by omega)⟩
    exact h2
  · have he : (⟨c, hc⟩ : Fin Q) = j := Fin.ext hcj
    have hB := hR.1 hcj.le
    subst hB
    simp only [envC, envB, leafStepEnv, if_pos he, rShift]
    refine ⟨trivial, fun h => absurd h (by omega), fun _ => rfl⟩
  · have hne : (⟨c, hc⟩ : Fin Q) ≠ j := fun e => by rw [← e] at hcj; exact lt_irrefl _ hcj
    have hB := hR.2 hcj
    subst hB
    simp only [envC, envB, leafStepEnv, if_neg hne]
    exact ⟨trivial, fun h => absurd h (by omega), fun _ => rfl⟩

theorem relB_oracleIn (hL : L.Laws nsalt pub) (j : Fin Q) {t : LeafTape X Y Cm Pos N Q}
    (hg : LeafGood pub t) (rs : List (ProofQuery Stmt Wit)) :
    RelB nsalt j t rs.length ((envC rel L nsalt j).oracleIn t rs) ((envB rel L nsalt j).oracleIn t rs) :=
  Quantum.Env.oracleIn_rel _ _ (RelB nsalt j t) ⟨fun _ => rfl, fun h => absurd h (by omega)⟩
    (fun c hc req HC HB hR => (relB_step rel L nsalt pub hL j hg c hc req HC HB hR).2)
    (fun c HC HB hcQ hR => ⟨fun h => absurd (h.trans_lt j.2) (by omega),
      fun _ => hR.2 (by omega)⟩) rs

section Patch

variable {B : Set (LeafTape X Y Cm Pos N Q)}
  {E F : Quantum.Env (LeafTape X Y Cm Pos N Q) (ProofQuery Stmt Wit) Proof X Y Q}
  {t : LeafTape X Y Cm Pos N Q}

theorem patchEnv_oracleIn_of_mem (ht : t ∈ B) (rs : List (ProofQuery Stmt Wit)) :
    (patchEnv B E F).oracleIn t rs = F.oracleIn t rs :=
  Quantum.Env.oracleIn_eq_of_agree (by simp [patchEnv, ht]) (by simp [patchEnv, ht]) rs

theorem patchEnv_oracleIn_of_notMem (ht : t ∉ B) (rs : List (ProofQuery Stmt Wit)) :
    (patchEnv B E F).oracleIn t rs = E.oracleIn t rs :=
  Quantum.Env.oracleIn_eq_of_agree (by simp [patchEnv, ht]) (by simp [patchEnv, ht]) rs

theorem patchEnv_answerAfter_of_mem (ht : t ∈ B) (rs : List (ProofQuery Stmt Wit))
    (req : ProofQuery Stmt Wit) : (patchEnv B E F).answerAfter t rs req = F.answerAfter t rs req :=
  Quantum.Env.answerAfter_eq_of_agree (by simp [patchEnv, ht]) (by simp [patchEnv, ht]) rs req

theorem patchEnv_answerAfter_of_notMem (ht : t ∉ B) (rs : List (ProofQuery Stmt Wit))
    (req : ProofQuery Stmt Wit) : (patchEnv B E F).answerAfter t rs req = E.answerAfter t rs req :=
  Quantum.Env.answerAfter_eq_of_agree (by simp [patchEnv, ht]) (by simp [patchEnv, ht]) rs req

end Patch

/-- **Patching on the bad tapes** (steps 3 and 6): at most the probability of the bad tapes. -/
theorem abs_acceptProbOn_patch_le (E F : Quantum.Env (LeafTape X Y Cm Pos N Q) (ProofQuery Stmt Wit) Proof X Y Q)
    (hE : E.μ = PMF.uniformOfFintype _) (Lg : Set (Quantum.LogReg (ProofQuery Stmt Wit) m)) :
    |D.acceptProbOn E post Lg - D.acceptProbOn (patchEnv {t | LeafBad pub t} E F) post Lg| ≤
      ((PMF.uniformOfFintype (LeafTape X Y Cm Pos N Q)).toOuterMeasure {t | LeafBad pub t}).toReal := by
  rw [← hE]
  exact D.abs_acceptProbOn_sub_le_of_eq_off post E (patchEnv {t | LeafBad pub t} E F) rfl
    {t | LeafBad pub t} (fun t ht => (if_neg ht).symm) (fun t ht => (if_neg ht).symm) Lg

/-- **O2H before proof query `j`** (step 4): on the branches that make proof query `j`, the patched
environment of step 2 and the shifting environment are at most `2 q √(n |Pos| / |N|)` apart, for
a distinguisher with a budget of `q` query slots. -/
theorem abs_acceptProbOn_envB_patch_sub_envC_le (hL : L.Laws nsalt pub) (j : Fin Q) {q : ℕ}
    (bud : D.Budget q) :
    |D.acceptProbOn (patchEnv {t | LeafBad pub t} (envB rel L nsalt j) (envC rel L nsalt j)) post
        (Quantum.madeLogs (j : ℕ)) - D.acceptProbOn (envC rel L nsalt j) post (Quantum.madeLogs (j : ℕ))| ≤
      2 * q * √(n * (Fintype.card Pos / Fintype.card N)) := by
  classical
  rw [← D.acceptProbOn_reindex post _ splitS, ← D.acceptProbOn_reindex post (envC rel L nsalt j) splitS,
    abs_sub_comm]
  have hfresh : ∀ v σ σ' (rs : List (ProofQuery Stmt Wit)), rs.length ≤ j →
      (envC rel L nsalt j).oracleIn (splitS.symm (v, σ)) rs =
        (envC rel L nsalt j).oracleIn (splitS.symm (v, σ')) rs := fun v σ σ' rs hrs => by
    have := Quantum.Env.oracleIn_rel (envC rel L nsalt j) (envC rel L nsalt j)
      (ω := splitS.symm (v, σ)) (ω' := splitS.symm (v, σ')) (fun c H H' => c ≤ j → H = H')
      (fun _ => rfl)
      (fun c hc req H H' hR hc' => by
        have hne : (⟨c, hc⟩ : Fin Q) ≠ j := fun e => by
          have := congrArg Fin.val e
          simp at this
          omega
        rw [hR (by omega)]
        simp only [envC, leafStepEnv, if_neg hne]
        rfl)
      (fun c H H' hcQ _ h => absurd (h.trans_lt j.2) (by omega)) rs
    exact this hrs
  refine D.advantage_acceptProbOn_made_le_of_fresh_secret_budget post bud
    ((envC rel L nsalt j).reindex splitS)
    ((patchEnv {t | LeafBad pub t} (envB rel L nsalt j) (envC rel L nsalt j)).reindex splitS)
    (μV := PMF.uniformOfFintype _) (ν := PMF.uniformOfFintype _)
    (T := fun σ => {y | inSalts nsalt σ y = some ()}) (ε := Fintype.card Pos / Fintype.card N) j
    (fun v σ => map_splitS_uniform_apply v σ) rfl ?_ ?_ ?_
    (fun v σ σ' rs hrs => hfresh v σ σ' rs hrs) ?_ (toReal_inSalts_le nsalt)
  · intro ω rs req
    simp only [Quantum.Env.answerAfter_reindex]
    by_cases hb : splitS.symm ω ∈ {t | LeafBad pub t}
    · rw [patchEnv_answerAfter_of_mem hb]
    · rw [patchEnv_answerAfter_of_notMem hb]
      have hg := leafGood_of_not_bad pub hb
      exact Quantum.Env.answerAfter_eq_of_rel _ _ (RelB nsalt j (splitS.symm ω))
        (relB_oracleIn rel L nsalt pub hL j hg)
        (fun c hc req H H' hR => (relB_step rel L nsalt pub hL j hg c hc req H H' hR).1) rs req
  · intro ω rs hrs
    simp only [Quantum.Env.oracleIn_reindex]
    by_cases hb : splitS.symm ω ∈ {t | LeafBad pub t}
    · rw [patchEnv_oracleIn_of_mem hb]
    · rw [patchEnv_oracleIn_of_notMem hb]
      exact ((relB_oracleIn rel L nsalt pub hL j (leafGood_of_not_bad pub hb) rs).2 hrs).symm
  · intro ω rs hrs x hx
    simp only [Quantum.Env.oracleIn_reindex]
    by_cases hb : splitS.symm ω ∈ {t | LeafBad pub t}
    · rw [patchEnv_oracleIn_of_mem hb]
    · rw [patchEnv_oracleIn_of_notMem hb,
        (relB_oracleIn rel L nsalt pub hL j (leafGood_of_not_bad pub hb) rs).1 hrs]
      simp only [shiftOracle, replaceSlice]
      exact (if_neg hx).symm
  · intro v σ σ' rs req hrs
    simp only [Quantum.Env.answerAfter_reindex]
    unfold Quantum.Env.answerAfter
    split_ifs with hQ
    · have hne : (⟨rs.length, hQ⟩ : Fin Q) ≠ j := fun e => by
        have := congrArg Fin.val e
        simp at this
        omega
      rw [hfresh v σ σ' rs hrs.le]
      simp only [envC, leafStepEnv, if_neg hne]
      rfl
    · rfl

/-- The inputs carrying a fresh salt. -/
def secretInputs (t : LeafTape X Y Cm Pos N Q) : Set X := {x | inSalts nsalt t.secret x = some ()}

theorem kernelLocal_hybKernel (hL : L.Laws nsalt pub) (j : ℕ) (i : Fin Q) :
    KernelLocal nsalt pub (hybKernel L j i) (fun c : LeafCoins Cm Pos N Y => c.salts) := by
  unfold hybKernel
  split_ifs
  · exact hL.kernelLocal_kD
  · exact hL.kernelLocal_kL

/-- On a good tape the proof queries' own salts are not fresh salts. -/
theorem secretInputs_foreign {t : LeafTape X Y Cm Pos N Q} (hg : LeafGood pub t) (i : Fin Q) :
    ∀ x ∈ secretInputs nsalt t, nsalt x ≠ none ∧ (∀ a ∈ pub, nsalt x ≠ some a) ∧
      ∀ p, nsalt x ≠ some ((t.coins i).salts p) := by
  intro x hx
  obtain ⟨q, hq⟩ := inSalts_eq_some_iff.1 hx
  refine ⟨by rw [hq]; simp, fun a ha e => hg.pub a ha q (Option.some_injective _ (hq ▸ e)),
    fun p e => hg.coins i p q (Option.some_injective _ (hq ▸ e)).symm⟩

/-- **Proof query `j`'s filled reply is its uniform-digest reply** on a good tape, at oracles that
agree off the inputs of the fresh salts: same response, states that agree off them. -/
theorem rFill_rMux_kD (hL : L.Laws nsalt pub) (j : Fin Q) {t : LeafTape X Y Cm Pos N Q}
    (hg : LeafGood pub t) (req : ProofQuery Stmt Wit) {HE HD : X → Y}
    (h : AgreeOff (secretInputs nsalt t) HE HD) :
    (rMux rel L j L.kD t req HE).response = (rFill rel L nsalt j t req HD).response ∧
      AgreeOff (secretInputs nsalt t) (rMux rel L j L.kD t req HE).state
        (rFill rel L nsalt j t req HD).state := by
  set c := muxCoins L j t req
  set m := (t.coins j).main
  have hpt : ∀ p q, L.hidden req m p = true → L.hidden req m q = true →
      L.point req m p (t.secret p) = L.point req m q (t.secret q) → p = q := fun p q _ _ e =>
    hg.inj (Option.some_injective _ (by rw [← hL.point_salt req m p, ← hL.point_salt req m q, e]))
  set O'' := fill (L.hidden req m) (fun p => L.point req m p (t.secret p)) (shiftOracle nsalt t HD)
    (t.coins j).digests
  -- off the fresh inputs the filled oracle is `HE`
  have hoff : AgreeOff (secretInputs nsalt t) O'' HE := fun x hx => by
    have hnp : ∀ p, L.hidden req m p = true → L.point req m p (t.secret p) ≠ x := fun p _ e =>
      hx (e ▸ inSalts_eq_some_iff.2 ⟨p, hL.point_salt _ _ _ _⟩)
    simp only [O'', fill_apply_of_forall_ne _ _ hnp, shiftOracle, replaceSlice]
    rw [if_neg (show ¬ (inSalts nsalt t.secret x = some ()) from hx)]
    exact (h x hx).symm
  have hrun : L.kL req O'' c = L.kD req HE c := by
    unfold LeafKernel.kL LeafKernel.kD
    rw [hL.run_digests req O'' c.main c.salts _ c.digests fun p hp => by
      show O'' (L.point req m p (if L.hidden req m p = true then t.secret p else _)) = _
      rw [if_pos (show L.hidden req m p = true from hp)]
      exact fill_apply_pt hpt _ _ hp]
    refine hL.run_oracle req O'' HE c.main c.salts c.digests fun x hx => hoff x fun hxs => ?_
    obtain ⟨q, hq⟩ := inSalts_eq_some_iff.1 hxs
    rcases hx with hx | ⟨a, ha, hx⟩ | ⟨p, hp, hx⟩
    · rw [hx] at hq
      cases hq
    · rw [hx] at hq
      exact hg.pub a ha q (Option.some_injective _ hq).symm
    · rw [hx] at hq
      change some (if L.hidden req m p = true then t.secret p else (t.coins j).salts p) = _ at hq
      rw [if_neg (by rw [show L.hidden req m p = false from hp]; simp)] at hq
      exact hg.coins j p q (Option.some_injective _ hq)
  unfold rFill rMux kernelReply
  split_ifs
  · rw [hrun]
    exact ⟨rfl, fun x hx => ((hoff.reprogram _) x hx).symm⟩
  · exact ⟨rfl, fun x hx => (hoff x hx).symm⟩

/-- **On a good tape the oracles of steps 6 and 7 agree off the fresh inputs**, and their
responses agree. -/
theorem relD_step (hL : L.Laws nsalt pub) (j : Fin Q) {t : LeafTape X Y Cm Pos N Q}
    (hg : LeafGood pub t) (c : Fin Q) (req : ProofQuery Stmt Wit) {HE HD : X → Y}
    (h : AgreeOff (secretInputs nsalt t) HE HD) :
    ((envE rel L j).respond t c req HE).response = ((envD rel L nsalt j).respond t c req HD).response ∧
      AgreeOff (secretInputs nsalt t) ((envE rel L j).respond t c req HE).state
        ((envD rel L nsalt j).respond t c req HD).state := by
  by_cases hc : c = j
  · simp only [envE, envD, leafStepEnv, if_pos hc]
    exact rFill_rMux_kD rel L nsalt pub hL j hg req h
  · simp only [envE, envD, leafStepEnv, if_neg hc]
    exact (kernelLocal_hybKernel L nsalt pub hL j c).reply_agreeOff
      (secretInputs_foreign nsalt pub hg c) req h

theorem relD_oracleIn (hL : L.Laws nsalt pub) (j : Fin Q) {t : LeafTape X Y Cm Pos N Q}
    (hg : LeafGood pub t) (rs : List (ProofQuery Stmt Wit)) :
    AgreeOff (secretInputs nsalt t) ((envE rel L j).oracleIn t rs) ((envD rel L nsalt j).oracleIn t rs) :=
  Quantum.Env.oracleIn_rel (envE rel L j) (envD rel L nsalt j) (ω := t) (ω' := t)
    (fun _ HE HD => AgreeOff (secretInputs nsalt t) HE HD) (fun _ _ => rfl)
    (fun c hc req _ _ hR => (relD_step rel L nsalt pub hL j hg ⟨c, hc⟩ req hR).2)
    (fun _ _ _ _ hR => hR) rs

/-- Step 7's environment does not read the fresh salts. -/
theorem envE_respond_fresh (hL : L.Laws nsalt pub) (j : Fin Q)
    (v : (X → Y) × (Fin Q → LeafCoins Cm Pos N Y) × (X → Y)) (σ σ' : Pos → N) :
    (envE rel L j).respond (splitS.symm (v, σ)) = (envE rel L j).respond (splitS.symm (v, σ')) := by
  funext c req H
  by_cases hc : c = j
  · have key : L.kD req H (muxCoins L j (splitS.symm (v, σ)) req) =
        L.kD req H (muxCoins L j (splitS.symm (v, σ')) req) := by
      unfold LeafKernel.kD
      exact hL.run_salts _ _ _ _ _ _ fun p hp => by
        simp only [muxCoins, splitS, Equiv.coe_fn_symm_mk] at hp ⊢
        simp [hp]
    simp only [envE, leafStepEnv, if_pos hc, rMux, kernelReply, key]
  · simp only [envE, leafStepEnv, if_neg hc]
    rfl

/-- **O2H over the whole run** (step 7): the patched environment of step 6 and the uniform-digest
environment are at most `2 q √(n |Pos| / |N|)` apart, without a final unitary. -/
theorem abs_acceptProb_envE_sub_envD_patch_le (hL : L.Laws nsalt pub) (j : Fin Q) {q : ℕ}
    (bud : D.Budget q) :
    |D.acceptProb (envE rel L j) Quantum.noPost -
        D.acceptProb (patchEnv {t | LeafBad pub t} (envD rel L nsalt j) (envE rel L j)) Quantum.noPost| ≤
      2 * q * √(n * (Fintype.card Pos / Fintype.card N)) := by
  classical
  rw [← D.acceptProb_reindex Quantum.noPost (patchEnv {t | LeafBad pub t} (envD rel L nsalt j) (envE rel L j))
    splitS, ← D.acceptProb_reindex Quantum.noPost (envE rel L j) splitS]
  have hfreshO : ∀ v σ σ' (rs : List (ProofQuery Stmt Wit)),
      (envE rel L j).oracleIn (splitS.symm (v, σ)) rs =
        (envE rel L j).oracleIn (splitS.symm (v, σ')) rs := fun v σ σ' rs =>
    Quantum.Env.oracleIn_eq_of_agree (E := envE rel L j) (E' := envE rel L j) (ω := splitS.symm (v, σ)) (ω' := splitS.symm (v, σ')) rfl
      (envE_respond_fresh rel L nsalt pub hL j v σ σ') rs
  refine D.advantage_acceptProb_le_of_fresh_secret_budget bud
    ((envE rel L j).reindex splitS)
    ((patchEnv {t | LeafBad pub t} (envD rel L nsalt j) (envE rel L j)).reindex splitS)
    (μV := PMF.uniformOfFintype _) (ν := PMF.uniformOfFintype _)
    (T := fun σ => {y | inSalts nsalt σ y = some ()})
    (fun v σ => map_splitS_uniform_apply v σ) rfl ?_ ?_ (fun v σ σ' rs => hfreshO v σ σ' rs)
    (fun v σ σ' rs req => Quantum.Env.answerAfter_eq_of_agree (E := envE rel L j) (E' := envE rel L j) (ω := splitS.symm (v, σ)) (ω' := splitS.symm (v, σ')) rfl
      (envE_respond_fresh rel L nsalt pub hL j v σ σ') rs req)
    (toReal_inSalts_le nsalt)
  · intro ω rs req
    simp only [Quantum.Env.answerAfter_reindex]
    by_cases hb : splitS.symm ω ∈ {t | LeafBad pub t}
    · rw [patchEnv_answerAfter_of_mem hb]
    · rw [patchEnv_answerAfter_of_notMem hb]
      have hg := leafGood_of_not_bad pub hb
      exact Quantum.Env.answerAfter_eq_of_rel _ _ (fun _ HE HD => AgreeOff (secretInputs nsalt (splitS.symm ω)) HE HD)
        (relD_oracleIn rel L nsalt pub hL j hg)
        (fun c hc req H H' hR => (relD_step rel L nsalt pub hL j hg ⟨c, hc⟩ req hR).1) rs req
  · intro ω rs x hx
    simp only [Quantum.Env.oracleIn_reindex]
    by_cases hb : splitS.symm ω ∈ {t | LeafBad pub t}
    · rw [patchEnv_oracleIn_of_mem hb]
    · rw [patchEnv_oracleIn_of_notMem hb]
      exact relD_oracleIn rel L nsalt pub hL j (leafGood_of_not_bad pub hb) rs x hx

/-- **Two environments that agree before proof query `j`** (same initial oracle, same responses to
the proof queries before `j`) accept with the same probability on the branches that never make proof query
`j`. -/
theorem acceptProbOn_notMade_eq_of_before (j : Fin Q)
    (E E' : Quantum.Env (LeafTape X Y Cm Pos N Q) (ProofQuery Stmt Wit) Proof X Y Q) (hμ : E'.μ = E.μ)
    (h0 : ∀ t, E.oracle₀ t = E'.oracle₀ t)
    (hr : ∀ t (c : Fin Q), (c : ℕ) < j → E.respond t c = E'.respond t c) :
    D.acceptProbOn E post (Quantum.madeLogs (j : ℕ))ᶜ = D.acceptProbOn E' post (Quantum.madeLogs (j : ℕ))ᶜ := by
  have hrel : ∀ t (rs : List (ProofQuery Stmt Wit)), rs.length ≤ j → E.oracleIn t rs = E'.oracleIn t rs :=
    fun t rs hrs => Quantum.Env.oracleIn_rel E E' (ω := t) (ω' := t) (fun c H H' => c ≤ j → H = H')
      (fun _ => h0 t)
      (fun c hc req H H' hR hc' => by
        rw [hR (by omega), hr t ⟨c, hc⟩ (by simp; omega)])
      (fun c H H' hcQ _ h => absurd (h.trans_lt j.2) (by omega)) rs hrs
  rw [Quantum.Distinguisher.acceptProbOn, Quantum.Distinguisher.acceptProbOn, hμ]
  refine Finset.sum_congr rfl fun t _ => ?_
  congr 1
  have := D.acceptProbOnAt_notMade_eq E E' post (ω := t) (ω' := t) (j := j)
    (fun rs req hrs => by
      unfold Quantum.Env.answerAfter
      split_ifs with hQ
      · rw [hrel t rs hrs.le, hr t ⟨rs.length, hQ⟩ hrs]
      · rfl)
    (hrel t) Set.univ
  simpa using this

/-- **One step of the quantum leaf hybrid**: hybrids `j` and `j + 1` differ by at most two O2H
bounds, twice the probability of the bad tapes and the probability of a collision of the fresh
salts. -/
theorem abs_acceptProb_leafHyb_succ_le (hL : L.Laws nsalt pub) (j : Fin Q) {q : ℕ}
    (bud : D.Budget q) :
    |D.acceptProb (leafHybEnv (Q := Q) rel L (j : ℕ)) Quantum.noPost - D.acceptProb (leafHybEnv (Q := Q) rel L ((j : ℕ) + 1)) Quantum.noPost| ≤
      2 * (2 * q * √(n * (Fintype.card Pos / Fintype.card N))) +
        2 * ((PMF.uniformOfFintype (LeafTape X Y Cm Pos N Q)).toOuterMeasure {t | LeafBad pub t}).toReal +
        ∑ v : (X → Y) × ({i : Fin Q // i ≠ j} → LeafCoins Cm Pos N Y) × (Pos → N),
          (PMF.uniformOfFintype _ v).toReal * (if Function.Injective v.2.2 then 0 else 1) := by
  classical
  -- the hybrids as step environments
  have hA : leafHybEnv (Q := Q) rel L (j : ℕ) = leafStepEnv rel L j (·.oracle) (rCoins rel j L.kL) := by
    unfold leafHybEnv leafStepEnv
    congr 1
    funext t i
    split_ifs with h
    · subst h
      rw [hybKernel_of_ge L le_rfl]
      rfl
    · rfl
  have hE : leafHybEnv (Q := Q) rel L ((j : ℕ) + 1) = leafStepEnv rel L j (·.oracle) (rCoins rel j L.kD) := by
    unfold leafHybEnv leafStepEnv
    congr 1
    funext t i
    split_ifs with h
    · subst h
      rw [hybKernel_of_lt L (Nat.lt_succ_self _)]
      rfl
    · congr 1
      unfold hybKernel
      have : (i : ℕ) ≠ j := fun e => h (Fin.ext e)
      by_cases hi : (i : ℕ) < j
      · rw [if_pos hi, if_pos (by omega)]
      · rw [if_neg hi, if_neg (by omega)]
  -- the branches that never make proof query `j`
  have hnot : D.acceptProbOn (leafHybEnv (Q := Q) rel L (j : ℕ)) Quantum.noPost (Quantum.madeLogs (j : ℕ))ᶜ =
      D.acceptProbOn (leafHybEnv (Q := Q) rel L ((j : ℕ) + 1)) Quantum.noPost (Quantum.madeLogs (j : ℕ))ᶜ :=
    acceptProbOn_notMade_eq_of_before D Quantum.noPost j _ _ rfl (fun _ => rfl) fun t c hc => by
      simp only [leafHybEnv]
      rw [hybKernel_of_lt L hc, hybKernel_of_lt L (by omega)]
  -- the branches that make proof query `j`
  set M := Quantum.madeLogs (m := m) (Req := ProofQuery Stmt Wit) (j : ℕ)
  have h1 : D.acceptProbOn (leafHybEnv (Q := Q) rel L (j : ℕ)) Quantum.noPost M =
      D.acceptProbOn (envB rel L nsalt j) Quantum.noPost M := by
    rw [hA, acceptProbOn_rCoins_eq_rMux rel L D Quantum.noPost j L.kL M]
    exact acceptProbOn_shift_init rel L nsalt D Quantum.noPost j _ (fun _ => rfl) M
  have h2 := abs_acceptProbOn_patch_le pub D Quantum.noPost (envB rel L nsalt j) (envC rel L nsalt j) rfl M
  have h3 : |D.acceptProbOn (patchEnv {t | LeafBad pub t} (envB rel L nsalt j) (envC rel L nsalt j))
      Quantum.noPost M - D.acceptProbOn (envC rel L nsalt j) Quantum.noPost M| ≤
      2 * q * √(n * (Fintype.card Pos / Fintype.card N)) :=
    abs_acceptProbOn_envB_patch_sub_envC_le rel L nsalt pub D Quantum.noPost hL j bud
  have h4 : |D.acceptProbOn (envC rel L nsalt j) Quantum.noPost M - D.acceptProbOn (envD rel L nsalt j) Quantum.noPost M| ≤
      ∑ v : (X → Y) × ({i : Fin Q // i ≠ j} → LeafCoins Cm Pos N Y) × (Pos → N),
        (PMF.uniformOfFintype _ v).toReal * (if Function.Injective v.2.2 then 0 else 1) :=
    abs_acceptProbOn_rShift_sub_rFill_le rel L nsalt pub D Quantum.noPost hL j M
  have h5 := abs_acceptProbOn_patch_le pub D Quantum.noPost (envD rel L nsalt j) (envE rel L j) rfl M
  have h6full := abs_acceptProb_envE_sub_envD_patch_le rel L nsalt pub D hL j bud
  have h6not : D.acceptProbOn (envE rel L j) Quantum.noPost Mᶜ = D.acceptProbOn
      (patchEnv {t | LeafBad pub t} (envD rel L nsalt j) (envE rel L j)) Quantum.noPost Mᶜ :=
    acceptProbOn_notMade_eq_of_before D Quantum.noPost j _ _ rfl
      (fun t => by simp only [patchEnv, envD, envE, leafStepEnv]; split_ifs <;> rfl)
      fun t c hc => by
        have hne : c ≠ j := fun e => by rw [e] at hc; exact lt_irrefl _ hc
        by_cases hb : t ∈ {t | LeafBad pub t}
        · simp only [patchEnv, if_pos hb]
        · simp only [patchEnv, if_neg hb, envD, envE, leafStepEnv, if_neg hne]
  have h6 : |D.acceptProbOn (envE rel L j) Quantum.noPost M - D.acceptProbOn
      (patchEnv {t | LeafBad pub t} (envD rel L nsalt j) (envE rel L j)) Quantum.noPost M| ≤
      2 * q * √(n * (Fintype.card Pos / Fintype.card N)) := by
    rw [← Quantum.Distinguisher.acceptProbOn_univ, ← Quantum.Distinguisher.acceptProbOn_univ, D.acceptProbOn_eq_add Quantum.noPost _ Set.univ M,
      D.acceptProbOn_eq_add Quantum.noPost _ Set.univ M] at h6full
    simp only [Set.univ_inter] at h6full
    rw [h6not] at h6full
    simpa using h6full
  have h7 : D.acceptProbOn (envE rel L j) Quantum.noPost M =
      D.acceptProbOn (leafHybEnv (Q := Q) rel L ((j : ℕ) + 1)) Quantum.noPost M := by
    rw [hE]
    exact (acceptProbOn_rCoins_eq_rMux rel L D Quantum.noPost j L.kD M).symm
  rw [← Quantum.Distinguisher.acceptProbOn_univ, ← Quantum.Distinguisher.acceptProbOn_univ, D.acceptProbOn_eq_add Quantum.noPost _ Set.univ M,
    D.acceptProbOn_eq_add Quantum.noPost _ Set.univ M]
  simp only [Set.univ_inter]
  rw [hnot, h1, ← h7]
  have := abs_sub_le (D.acceptProbOn (envB rel L nsalt j) Quantum.noPost M)
    (D.acceptProbOn (patchEnv {t | LeafBad pub t} (envB rel L nsalt j) (envC rel L nsalt j)) Quantum.noPost M)
    (D.acceptProbOn (envE rel L j) Quantum.noPost M)
  have := abs_sub_le (D.acceptProbOn (patchEnv {t | LeafBad pub t} (envB rel L nsalt j) (envC rel L nsalt j)) Quantum.noPost M)
    (D.acceptProbOn (envC rel L nsalt j) Quantum.noPost M) (D.acceptProbOn (envE rel L j) Quantum.noPost M)
  have := abs_sub_le (D.acceptProbOn (envC rel L nsalt j) Quantum.noPost M)
    (D.acceptProbOn (envD rel L nsalt j) Quantum.noPost M) (D.acceptProbOn (envE rel L j) Quantum.noPost M)
  have := abs_sub_le (D.acceptProbOn (envD rel L nsalt j) Quantum.noPost M)
    (D.acceptProbOn (patchEnv {t | LeafBad pub t} (envD rel L nsalt j) (envE rel L j)) Quantum.noPost M)
    (D.acceptProbOn (envE rel L j) Quantum.noPost M)
  rw [abs_sub_comm] at h6
  have hsplit : D.acceptProbOn (envB rel L nsalt j) Quantum.noPost M + D.acceptProbOn
      (leafHybEnv (Q := Q) rel L ((j : ℕ) + 1)) Quantum.noPost Mᶜ - (D.acceptProbOn (envE rel L j) Quantum.noPost M +
        D.acceptProbOn (leafHybEnv (Q := Q) rel L ((j : ℕ) + 1)) Quantum.noPost Mᶜ) =
      D.acceptProbOn (envB rel L nsalt j) Quantum.noPost M - D.acceptProbOn (envE rel L j) Quantum.noPost M := by ring
  rw [hsplit]
  linarith

/-! ### The probability of the bad tapes -/

/-- The tape as the fresh salt of `q` and the rest. -/
def splitQ (q : Pos) : LeafTape X Y Cm Pos N Q ≃
    N × ((X → Y) × (Fin Q → LeafCoins Cm Pos N Y) × ({p : Pos // p ≠ q} → N) × (X → Y)) where
  toFun t := (t.secret q, (t.oracle, t.coins, fun p => t.secret p, t.table))
  invFun x := ⟨x.2.1, x.2.2.1, (Equiv.piSplitAt q _).symm (x.1, x.2.2.2.1), x.2.2.2.2⟩
  left_inv t := by
    obtain ⟨O, c, σ, T⟩ := t
    simp only [LeafTape.mk.injEq, true_and, and_true]
    exact (Equiv.piSplitAt q _).symm_apply_apply σ
  right_inv x := by
    obtain ⟨a, O, c, σ, T⟩ := x
    simp only [Prod.mk.injEq]
    refine ⟨?_, trivial, trivial, ?_, trivial⟩
    · simp [Equiv.piSplitAt]
    · funext p
      simp [Equiv.piSplitAt, p.2]

theorem toReal_toOuterMeasure_union_le {α : Type*} (μ : PMF α) (A B : Set α) :
    (μ.toOuterMeasure (A ∪ B)).toReal ≤ (μ.toOuterMeasure A).toReal + (μ.toOuterMeasure B).toReal := by
  have hfin : ∀ t, μ.toOuterMeasure t ≠ ⊤ := fun t =>
    ne_of_lt (lt_of_le_of_lt (PMF.toOuterMeasure_apply_le_one _ _) ENNReal.one_lt_top)
  rw [← ENNReal.toReal_add (hfin A) (hfin B)]
  exact ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hfin A, hfin B⟩)
    (MeasureTheory.measure_union_le A B)

theorem toReal_toOuterMeasure_mono {α : Type*} (μ : PMF α) {A B : Set α} (h : A ⊆ B) :
    (μ.toOuterMeasure A).toReal ≤ (μ.toOuterMeasure B).toReal :=
  ENNReal.toReal_mono (ne_of_lt (lt_of_le_of_lt (PMF.toOuterMeasure_apply_le_one _ _)
    ENNReal.one_lt_top)) (MeasureTheory.measure_mono h)

/-- **The bad tapes have probability at most `(|pub| |Pos| + Q |Pos|² + |Pos|²) / |N|`.** -/
theorem toReal_leafBad_le :
    ((PMF.uniformOfFintype (LeafTape X Y Cm Pos N Q)).toOuterMeasure {t | LeafBad pub t}).toReal ≤
      (pub.card * Fintype.card Pos + Q * Fintype.card Pos ^ 2 + Fintype.card Pos ^ 2) /
        Fintype.card N := by
  classical
  set μ := PMF.uniformOfFintype (LeafTape X Y Cm Pos N Q)
  have e1 : ∀ x : ↥pub × Pos, (μ.toOuterMeasure {t | t.secret x.2 = x.1}).toReal =
      (Fintype.card N : ℝ)⁻¹ := fun x =>
    Quantum.PMF.toReal_uniform_eq_fn (splitQ x.2) (fun _ => (x.1 : N))
  have e2 : ∀ x : Fin Q × Pos × Pos, (μ.toOuterMeasure
      {t | (t.coins x.1).salts x.2.1 = t.secret x.2.2}).toReal = (Fintype.card N : ℝ)⁻¹ := fun x => by
    rw [← Quantum.PMF.toReal_uniform_eq_fn (splitQ (Q := Q) (X := X) (Y := Y) (Cm := Cm) x.2.2)
      (fun r => (r.2.1 x.1).salts x.2.1)]
    congr 2
    ext t
    exact eq_comm
  have e3 : ∀ x : Pos × Pos, (μ.toOuterMeasure {t | x.1 ≠ x.2 ∧ t.secret x.1 = t.secret x.2}).toReal ≤
      (Fintype.card N : ℝ)⁻¹ := fun x => by
    by_cases h : x.1 = x.2
    · rw [show {t : LeafTape X Y Cm Pos N Q | x.1 ≠ x.2 ∧ t.secret x.1 = t.secret x.2} = ∅ by
        ext t; simp [h]]
      simp
    · refine le_of_eq ?_
      rw [← Quantum.PMF.toReal_uniform_eq_fn (splitQ (Q := Q) (X := X) (Y := Y) (Cm := Cm) x.2)
        (fun r => r.2.2.1 ⟨x.1, h⟩)]
      congr 2
      ext t
      simp [splitQ, h, eq_comm]
  have hsub : {t : LeafTape X Y Cm Pos N Q | LeafBad pub t} ⊆
      ((⋃ x : ↥pub × Pos, {t : LeafTape X Y Cm Pos N Q | t.secret x.2 = x.1}) ∪
      ⋃ x : Fin Q × Pos × Pos, {t : LeafTape X Y Cm Pos N Q | (t.coins x.1).salts x.2.1 = t.secret x.2.2}) ∪
      ⋃ x : Pos × Pos, {t : LeafTape X Y Cm Pos N Q | x.1 ≠ x.2 ∧ t.secret x.1 = t.secret x.2} := by
    rintro t (⟨a, ha, p, hp⟩ | ⟨i, p, q, h⟩ | hi)
    · exact Or.inl (Or.inl (Set.mem_iUnion.2 ⟨(⟨a, ha⟩, p), hp⟩))
    · exact Or.inl (Or.inr (Set.mem_iUnion.2 ⟨(i, p, q), h⟩))
    · simp only [Function.Injective, not_forall] at hi
      obtain ⟨p, q, h, hne⟩ := hi
      exact Or.inr (Set.mem_iUnion.2 ⟨(p, q), hne, h⟩)
  refine (toReal_toOuterMeasure_mono μ hsub).trans ?_
  refine (toReal_toOuterMeasure_union_le μ _ _).trans ?_
  refine (add_le_add (toReal_toOuterMeasure_union_le μ _ _) le_rfl).trans ?_
  refine (add_le_add (add_le_add (PMF.toReal_toOuterMeasure_iUnion_le μ _)
    (PMF.toReal_toOuterMeasure_iUnion_le μ _)) (PMF.toReal_toOuterMeasure_iUnion_le μ _)).trans ?_
  simp only [e1, e2]
  refine (add_le_add le_rfl (Finset.sum_le_sum fun x _ => e3 x)).trans_eq ?_
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_coe, Fintype.card_fin,
    nsmul_eq_mul]
  push_cast
  ring

/-- The average of a function of the part of the tape outside proof query `j`'s coins and table is
its average over the tape. -/
theorem sum_uniform_splitT_fst (j : Fin Q)
    (f : (X → Y) × ({i : Fin Q // i ≠ j} → LeafCoins Cm Pos N Y) × (Pos → N) → ℝ) :
    ∑ v, (PMF.uniformOfFintype _ v).toReal * f v =
      ∑ t : LeafTape X Y Cm Pos N Q, (PMF.uniformOfFintype _ t).toReal * f (splitT j t).1 := by
  have hcard : Fintype.card (LeafTape X Y Cm Pos N Q) =
      Fintype.card ((X → Y) × ({i : Fin Q // i ≠ j} → LeafCoins Cm Pos N Y) × (Pos → N)) *
        Fintype.card (LeafCoins Cm Pos N Y × (X → Y)) := by
    rw [Fintype.card_congr (splitT j), Fintype.card_prod]
  calc ∑ v, (PMF.uniformOfFintype _ v).toReal * f v
      = ∑ v, ∑ τ : LeafCoins Cm Pos N Y × (X → Y),
          (PMF.uniformOfFintype (LeafTape X Y Cm Pos N Q) ((splitT j).symm (v, τ))).toReal * f v :=
        Finset.sum_congr rfl fun v _ => by
          simp only [PMF.toReal_uniformOfFintype_apply, Finset.sum_const, Finset.card_univ,
            nsmul_eq_mul, hcard]
          have : (Fintype.card (LeafCoins Cm Pos N Y × (X → Y)) : ℝ) ≠ 0 := by simp
          push_cast
          field_simp
    _ = ∑ x : ((X → Y) × ({i : Fin Q // i ≠ j} → LeafCoins Cm Pos N Y) × (Pos → N)) ×
          (LeafCoins Cm Pos N Y × (X → Y)),
          (PMF.uniformOfFintype (LeafTape X Y Cm Pos N Q) ((splitT j).symm x)).toReal * f x.1 :=
        (Fintype.sum_prod_type (fun x : ((X → Y) × ({i : Fin Q // i ≠ j} → LeafCoins Cm Pos N Y) ×
          (Pos → N)) × (LeafCoins Cm Pos N Y × (X → Y)) =>
            (PMF.uniformOfFintype (LeafTape X Y Cm Pos N Q) ((splitT j).symm x)).toReal * f x.1)).symm
    _ = ∑ t : LeafTape X Y Cm Pos N Q, (PMF.uniformOfFintype _ t).toReal * f (splitT j t).1 := by
        rw [← Equiv.sum_comp (splitT j).symm
          (fun t => (PMF.uniformOfFintype (LeafTape X Y Cm Pos N Q) t).toReal * f (splitT j t).1)]
        simp only [Equiv.apply_symm_apply]

/-- The collision probability of the fresh salts is at most that of the bad tapes. -/
theorem sum_uniform_not_injective_le (j : Fin Q) :
    ∑ v : (X → Y) × ({i : Fin Q // i ≠ j} → LeafCoins Cm Pos N Y) × (Pos → N),
        (PMF.uniformOfFintype _ v).toReal * (if Function.Injective v.2.2 then 0 else 1) ≤
      ((PMF.uniformOfFintype (LeafTape X Y Cm Pos N Q)).toOuterMeasure {t | LeafBad pub t}).toReal := by
  classical
  rw [sum_uniform_splitT_fst, PMF.toReal_toOuterMeasure_apply]
  refine Finset.sum_le_sum fun t _ => ?_
  simp only [splitT, Equiv.coe_fn_mk]
  by_cases h1 : Function.Injective t.secret
  · simp only [h1, if_true, mul_zero]
    split_ifs <;> positivity
  · have hb : LeafBad pub t := Or.inr (Or.inr h1)
    simp [h1, hb]

/-! ### The theorem -/

/-- **The game of a kernel is hybrid `j` at the kernel of every proof query**: the leaf tape projects
to the tape of `progEnv`. -/
theorem acceptProb_progEnv_eq_leafHyb (K : Kernel X Y Stmt Wit Proof (LeafCoins Cm Pos N Y))
    (j : ℕ) (hK : ∀ i : Fin Q, hybKernel L j i = K) :
    D.acceptProb (progEnv rel K Q) Quantum.noPost = D.acceptProb (leafHybEnv (Q := Q) rel L j) Quantum.noPost := by
  let f : LeafTape X Y Cm Pos N Q → (X → Y) × (Fin Q → LeafCoins Cm Pos N Y) := fun t => (t.oracle, t.coins)
  have hμ : (progEnv rel K Q).μ = (PMF.uniformOfFintype (LeafTape X Y Cm Pos N Q)).map f := by
    let e : LeafTape X Y Cm Pos N Q ≃ ((X → Y) × (Fin Q → LeafCoins Cm Pos N Y)) × ((Pos → N) × (X → Y)) :=
      { toFun := fun t => ((t.oracle, t.coins), (t.secret, t.table))
        invFun := fun p => ⟨p.1.1, p.1.2, p.2.1, p.2.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    change tapeDist Q _ = _
    rw [tapeDist_uniformOfFintype, ← PMF.map_fst_uniformOfFintype
      (β := (Pos → N) × (X → Y)), ← PMF.map_uniformOfFintype_equiv e, PMF.map_comp]
    rfl
  exact (D.acceptProb_comap Quantum.noPost f hμ (fun _ => rfl) fun t => by
    funext i
    simp only [leafHybEnv, progEnv, hK i]
    rfl).symm

/-- **Hidden leaf digests against quantum distinguishers with every query counted** (module
docstring): for a leaf kernel with its laws, against a distinguisher with a budget of `q` query
slots and no final unitary, the games of `kL` and `kD` with `Q` proof queries differ by at most
`Q (4 q √(n |Pos| / |N|) + 3 (|pub| |Pos| + Q |Pos|² + |Pos|²) / |N|)`. -/
theorem abs_acceptProb_progEnv_kL_sub_kD_le (hL : L.Laws nsalt pub) {q : ℕ} (bud : D.Budget q) :
    |D.acceptProb (progEnv rel L.kL Q) Quantum.noPost - D.acceptProb (progEnv rel L.kD Q) Quantum.noPost| ≤
      Q * (4 * q * √(n * (Fintype.card Pos / Fintype.card N)) +
        3 * ((pub.card * Fintype.card Pos + Q * Fintype.card Pos ^ 2 + Fintype.card Pos ^ 2) /
          Fintype.card N)) := by
  rw [acceptProb_progEnv_eq_leafHyb rel L D L.kL 0 fun i => hybKernel_of_ge L (Nat.zero_le _),
    acceptProb_progEnv_eq_leafHyb rel L D L.kD Q fun i => hybKernel_of_lt L i.2]
  set a : ℕ → ℝ := fun j => D.acceptProb (leafHybEnv (Q := Q) rel L j) Quantum.noPost
  set c : ℝ := 4 * q * √(n * (Fintype.card Pos / Fintype.card N)) +
    3 * ((pub.card * Fintype.card Pos + Q * Fintype.card Pos ^ 2 + Fintype.card Pos ^ 2) /
      Fintype.card N)
  have hstep : ∀ j < Q, |a j - a (j + 1)| ≤ c := fun j hj => by
    have h := abs_acceptProb_leafHyb_succ_le rel L nsalt pub D hL ⟨j, hj⟩ bud
    have hinj := sum_uniform_not_injective_le (X := X) (Y := Y) (Cm := Cm) (Pos := Pos) (N := N) pub (⟨j, hj⟩ : Fin Q)
    have hbad := toReal_leafBad_le (X := X) (Y := Y) (Cm := Cm) (Q := Q) (Pos := Pos) (N := N) pub
    change |a j - a (j + 1)| ≤ _ at h
    simp only [c]
    linarith
  have : ∀ k ≤ Q, |a 0 - a k| ≤ k * c := fun k => by
    induction k with
    | zero => intro; simp
    | succ k ih =>
      intro hk
      have := abs_sub_le (a 0) (a k) (a (k + 1))
      have := ih (by omega)
      have := hstep k (by omega)
      push_cast
      linarith
  exact this Q le_rfl

end Game

end QROM

end GordieHowe
