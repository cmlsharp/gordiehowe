-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.QROM.SaltedZK
public import GordieHowe.Model.Quantum.O2H.SaltReprogram
public import GordieHowe.Model.Quantum.Interactive.SplitHybrid
public import GordieHowe.Foundations.ToMathlib.PMFFiber

@[expose] public section

/-!
# A prover reading the oracle at a hidden salt

A salted prover (`QROM.saltedReadProver emb e u core`) draws a salt `σ` uniformly from `S` and
other coins `c ← ζ`, never publishes `σ`, and reads the first components (under a split
`e : Y ≃ Y₁ × Y₂`) of the oracle's values on the range of an injective embedding
`emb : S × U → X` at the single point `emb (σ, u x)` of its statement `x`; otherwise it reads the
oracle only off that range and in the second components (`core`, congruent under
`AgreeOffRangeOn emb e`). The fresh-value prover (`QROM.freshReadProver core`) has a uniform
`y : Y₁` among its coins in place of the read. Against a distinguisher of the pure game with a
budget of `q` query slots of `n` parallel queries and no final unitary, answering `Q` proof
queries, the two real games differ by at most `C(Q, 2) / |S| + 2 q √(n Q / |S|)`
(`QROM.advantage_saltedRead_fresh_le`).

The proof has three parts.

- (`QROM.acceptProb_realEnv_saltedRead`) The real game of the salted prover is the salted
  challenger reading first components (`saltEnvOn`) with one salt per proof query.
- (`Distinguisher.advantage_saltOn_fresh_le_of_pi`) Replacing the reads at the salts by fresh
  functions `U → Y₁`, one per proof query, costs the bound above (one-way to hiding over the
  whole run).
- (`QROM.acceptProb_freshEnv_saltedRead`) The fresh challenger (`freshEnv`), which reads the fresh
  function of proof query `j` at the single point `u x` of its statement, has the acceptance
  probability of the real game of the fresh-value prover. The statement of proof query `j` is
  chosen by the distinguisher, in superposition, after its earlier queries; the equality holds
  because the logged request `j` is fixed before the fresh function of request `j` is read, and
  a uniform function read at one point is uniform there. This is the hybrid over the proof
  queries of `Distinguisher.acceptProbOn_drawEnv_eq`: in an environment with one independent draw
  per request (`drawEnv`), replacing each request's reply by one with the same law over that
  request's draw, at every request, keeps the acceptance probability.
-/

open Finset
open scoped BigOperators ENNReal

namespace GordieHowe.Quantum

/-! ### Environments read through a map of tapes, with the state kept -/

namespace Distinguisher

variable {W X Y Req A : Type*} [Fintype W] [Fintype X] [Fintype Y] [Fintype Req] [Fintype A]
  {n m : ℕ} (D : Distinguisher W X Y Req A n m) [DecidableEq Req] [DecidableEq A] [AddGroup Y]
  {Q : ℕ} (post : (X → Y) → QState (DReg W n X Y Req A) ≃ₗᵢ[ℂ] QState (DReg W n X Y Req A))

/-- **Relabelling the tape of environments that keep their state**: if the tape law of `E'` is
the image of that of `E` under `f`, both keep their state, and `E'` at `f ω` has the initial
state and the responses at that state of `E` at `ω`, the acceptance probabilities are equal. -/
theorem acceptProb_eq_of_map_keepsState {Ω Ω' : Type*} [Fintype Ω] [Fintype Ω']
    (E : Env Ω Req A X Y Q) (E' : Env Ω' Req A X Y Q) (hE : E.KeepsState) (hE' : E'.KeepsState)
    (f : Ω → Ω') (hμ : E'.μ = E.μ.map f) (h0 : ∀ ω, E.oracle₀ ω = E'.oracle₀ (f ω))
    (hr : ∀ ω i req, (E.respond ω i req (E.oracle₀ ω)).response =
      (E'.respond (f ω) i req (E'.oracle₀ (f ω))).response) :
    D.acceptProb E post = D.acceptProb E' post := by
  rw [acceptProb, acceptProb, hμ, PMF.sum_toReal_map_mul]
  refine sum_congr rfl fun ω _ => ?_
  refine congrArg (HMul.hMul _) ?_
  refine D.acceptProbAt_congr E E' (fun lg k => ?_) (fun lg => ?_) post
  · simp only [Env.answer]
    refine congrArg (Option.elim (lg k) none) (funext fun req => ?_)
    simp only [Env.answerAfter, Env.oracleIn_of_keepsState hE, Env.oracleIn_of_keepsState hE',
      hr]
  · simp only [Env.oracle, Env.oracleIn_of_keepsState hE, Env.oracleIn_of_keepsState hE', h0]

end Distinguisher

/-! ### One independent draw per request -/

section DrawEnv

variable {V R Req A X Y : Type*} {Q : ℕ} [Fintype R]

/-- **An environment with one independent draw per request**: the tape is `v ← μV` and draws
`d i ← ν` for the requests `i < Q`, all independent; the oracle is `o v` throughout, and request
number `i` with request `req` is answered by `r v (d i) i req H` at the oracle `H` in force. -/
noncomputable def drawEnv (μV : PMF V) (ν : PMF R) (o : V → X → Y)
    (r : V → R → Fin Q → Req → (X → Y) → Option A) : Env (V × (Fin Q → R)) Req A X Y Q where
  μ := prodLaw μV (PMF.pi fun _ => ν)
  oracle₀ ω := o ω.1
  respond ω i req s := ⟨r ω.1 (ω.2 i) i req s, s⟩

/-- An environment with one draw per request never changes the oracle. -/
theorem keepsState_drawEnv (μV : PMF V) (ν : PMF R) (o : V → X → Y)
    (r : V → R → Fin Q → Req → (X → Y) → Option A) : (drawEnv μV ν o r).KeepsState :=
  fun _ _ _ _ => rfl

end DrawEnv

namespace Distinguisher

variable {W X Y Req A : Type*} [Fintype W] [Fintype X] [Fintype Y] [Fintype Req] [Fintype A]
  {n m : ℕ} (D : Distinguisher W X Y Req A n m) [DecidableEq Req] [DecidableEq A] [AddGroup Y]
  {Q : ℕ} (post : (X → Y) → QState (DReg W n X Y Req A) ≃ₗᵢ[ℂ] QState (DReg W n X Y Req A))
  {V R : Type*} [Fintype V] [Fintype R] [DecidableEq X]

omit [DecidableEq X] in
/-- The game against an environment with one draw per request, as an average over `v` of an
average over the draws. -/
theorem acceptProbOn_drawEnv (μV : PMF V) (ν : PMF R) (o : V → X → Y)
    (r : V → R → Fin Q → Req → (X → Y) → Option A) (L : Set (LogReg Req m)) :
    D.acceptProbOn (drawEnv μV ν o r) post L = ∑ v, (μV v).toReal *
      ∑ d : Fin Q → R,
        (∏ i, (ν (d i)).toReal) * D.acceptProbOnAt (drawEnv μV ν o r) post L (v, d) := by
  rw [acceptProbOn, Fintype.sum_prod_type]
  refine sum_congr rfl fun v _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun d _ => ?_
  rw [show (drawEnv μV ν o r).μ (v, d) = μV v * PMF.pi (fun _ => ν) d from prodLaw_apply _ _ _ _,
    ENNReal.toReal_mul, PMF.toReal_pi_apply, mul_assoc]

/-- **Replacing one request's reply by one of the same law**: two environments with one draw per
request whose replies agree at every request other than number `j`, and whose replies to request
`j` have the same law over its draw at every `v` and request, have the same acceptance
probability on every set of logs. Request `j` may be chosen by the distinguisher after its
queries, in superposition (`abs_sum_withResponse_sub_le`). -/
theorem acceptProbOn_drawEnv_eq_of_step (μV : PMF V) (ν : PMF R) (o : V → X → Y)
    (r r' : V → R → Fin Q → Req → (X → Y) → Option A) (j : Fin Q)
    (hoff : ∀ v τ (i : Fin Q) req H, i ≠ j → r v τ i req H = r' v τ i req H)
    (hj : ∀ v req, ν.map (fun τ => r v τ j req (o v)) = ν.map (fun τ => r' v τ j req (o v)))
    (L : Set (LogReg Req m)) :
    D.acceptProbOn (drawEnv μV ν o r) post L = D.acceptProbOn (drawEnv μV ν o r') post L := by
  classical
  rw [acceptProbOn_drawEnv, acceptProbOn_drawEnv]
  refine sum_congr rfl fun v _ => ?_
  refine congrArg (HMul.hMul _) ?_
  rw [sum_prod_toReal_mul_eq_sum_update ν j
      (fun d => D.acceptProbOnAt (drawEnv μV ν o r) post L (v, d)),
    sum_prod_toReal_mul_eq_sum_update ν j
      (fun d => D.acceptProbOnAt (drawEnv μV ν o r') post L (v, d))]
  refine sum_congr rfl fun d _ => ?_
  refine congrArg (HMul.hMul _) ?_
  have hE : ∀ τ, D.acceptProbOnAt (drawEnv μV ν o r) post L (v, Function.update d j τ) =
      D.acceptProbOnAt ((drawEnv μV ν o r).withResponse (v, d) j
        ((drawEnv μV ν o r).respond (v, Function.update d j τ) j)) post L () := fun τ =>
    D.acceptProbOnAt_eq_withResponse post (drawEnv μV ν o r) (v, d) j (drawEnv μV ν o r)
      (ω := (v, Function.update d j τ)) rfl
      (fun c hc => by
        funext req s
        simp only [drawEnv, Function.update_of_ne hc]) L
  have hE' : ∀ τ, D.acceptProbOnAt (drawEnv μV ν o r') post L (v, Function.update d j τ) =
      D.acceptProbOnAt ((drawEnv μV ν o r).withResponse (v, d) j
        ((drawEnv μV ν o r').respond (v, Function.update d j τ) j)) post L () := fun τ =>
    D.acceptProbOnAt_eq_withResponse post (drawEnv μV ν o r) (v, d) j (drawEnv μV ν o r')
      (ω := (v, Function.update d j τ)) rfl
      (fun c hc => by
        funext req s
        simp only [drawEnv, Function.update_of_ne hc, hoff v (d c) c req s hc]) L
  simp only [hE, hE']
  refine sub_eq_zero.1 (abs_nonpos_iff.1 (D.abs_sum_withResponse_sub_le post (drawEnv μV ν o r)
    (v, d) j L (fun τ => (drawEnv μV ν o r).respond (v, Function.update d j τ) j)
    (fun τ => (drawEnv μV ν o r').respond (v, Function.update d j τ) j) le_rfl
    fun req rs _ => ?_))
  rw [Env.oracleIn_of_keepsState (keepsState_drawEnv μV ν o r),
    show (drawEnv μV ν o r).oracle₀ (v, d) = o v from rfl]
  have hmap : ∀ r₀ : V → R → Fin Q → Req → (X → Y) → Option A,
      ν.map (fun τ => (drawEnv μV ν o r₀).respond (v, Function.update d j τ) j req (o v)) =
        (ν.map fun τ => r₀ v τ j req (o v)).map fun a => (⟨a, o v⟩ : EnvReply A (X → Y)) :=
    fun r₀ => by
      rw [PMF.map_comp]
      refine congrArg (fun f => PMF.map f ν) ?_
      funext τ
      simp only [drawEnv, Function.update_self, Function.comp_apply]
  rw [hmap r, hmap r', hj, PMF.tvDist_self]

/-- **Replacing every request's reply by one of the same law** (the hybrid over the requests of
`acceptProbOn_drawEnv_eq_of_step`): two environments with one draw per request whose replies to
each request have the same law over that request's draw, at every `v`, request number and
request, have the same acceptance probability on every set of logs. -/
theorem acceptProbOn_drawEnv_eq (μV : PMF V) (ν : PMF R) (o : V → X → Y)
    (r r' : V → R → Fin Q → Req → (X → Y) → Option A)
    (h : ∀ v (i : Fin Q) req,
      ν.map (fun τ => r v τ i req (o v)) = ν.map (fun τ => r' v τ i req (o v)))
    (L : Set (LogReg Req m)) :
    D.acceptProbOn (drawEnv μV ν o r) post L = D.acceptProbOn (drawEnv μV ν o r') post L := by
  let hyb : ℕ → V → R → Fin Q → Req → (X → Y) → Option A :=
    fun k v τ i req H => if (i : ℕ) < k then r' v τ i req H else r v τ i req H
  have h0 : hyb 0 = r := by
    funext v τ i req H
    simp [hyb]
  have hQ : hyb Q = r' := by
    funext v τ i req H
    simp [hyb, i.2]
  have key : ∀ k ≤ Q, D.acceptProbOn (drawEnv μV ν o r) post L =
      D.acceptProbOn (drawEnv μV ν o (hyb k)) post L := by
    intro k
    induction k with
    | zero =>
      intro _
      rw [h0]
    | succ k ih =>
      intro hk
      rw [ih (by omega)]
      refine D.acceptProbOn_drawEnv_eq_of_step post μV ν o (hyb k) (hyb (k + 1)) ⟨k, hk⟩
        (fun v τ i req H hi => ?_) (fun v req => ?_) L
      · have hik : (i : ℕ) ≠ k := fun e => hi (Fin.ext e)
        by_cases h1 : (i : ℕ) < k
        · simp [hyb, h1, show (i : ℕ) < k + 1 by omega]
        · simp [hyb, h1, show ¬ (i : ℕ) < k + 1 by omega]
      · have h1 : (fun τ => hyb k v τ ⟨k, hk⟩ req (o v)) = fun τ => r v τ ⟨k, hk⟩ req (o v) :=
          funext fun τ => by simp [hyb]
        have h2 : (fun τ => hyb (k + 1) v τ ⟨k, hk⟩ req (o v)) =
            fun τ => r' v τ ⟨k, hk⟩ req (o v) :=
          funext fun τ => by simp [hyb]
        rw [h1, h2]
        exact h v ⟨k, hk⟩ req
  rw [key Q le_rfl, hQ]

/-- `acceptProbOn_drawEnv_eq` for the whole acceptance probability. -/
theorem acceptProb_drawEnv_eq (μV : PMF V) (ν : PMF R) (o : V → X → Y)
    (r r' : V → R → Fin Q → Req → (X → Y) → Option A)
    (h : ∀ v (i : Fin Q) req,
      ν.map (fun τ => r v τ i req (o v)) = ν.map (fun τ => r' v τ i req (o v))) :
    D.acceptProb (drawEnv μV ν o r) post = D.acceptProb (drawEnv μV ν o r') post := by
  rw [← acceptProbOn_univ, ← acceptProbOn_univ, D.acceptProbOn_drawEnv_eq post μV ν o r r' h]

end Distinguisher

end GordieHowe.Quantum

namespace GordieHowe.QROM

open Quantum

variable {X Y S U Y₁ Y₂ Stmt Wit Proof C : Type*}

section Provers

variable (emb : S × U → X) (e : Y ≃ Y₁ × Y₂) (u : Stmt → U)
  (core : (X → Y) → Stmt → Wit → Y₁ → C → Proof)

/-- **The salted reading prover**: with salt `σ` and other coins `c`, it computes
`core H x w y c` at the first component `y` of `H (emb (σ, u x))` under `e`. -/
def saltedReadProver : NARG.ProverFn X Y Stmt Wit Proof (SaltedCoins S C) where
  prove H x w c := core H x w (e (H (emb (c.salt, u x)))).1 c.coins

/-- **The fresh-value prover**: with coins `(y, c)` it computes `core H x w y c`. -/
def freshReadProver : NARG.ProverFn X Y Stmt Wit Proof (Y₁ × C) where
  prove H x w c := core H x w c.1 c.2

/-- **The law of the salted coins**: a uniform salt and other coins `c ← ζ`, independently. -/
noncomputable def saltedCoinLaw [Fintype S] [Nonempty S] (ζ : PMF C) : PMF (SaltedCoins S C) :=
  (prodLaw (PMF.uniformOfFintype S) ζ).map (SaltedCoins.equivProd S C).symm

/-- The law of the salted coins at `c` is the uniform probability of the salt times `ζ` at the
other coins. -/
theorem saltedCoinLaw_apply [Fintype S] [Nonempty S] (ζ : PMF C) (c : SaltedCoins S C) :
    saltedCoinLaw ζ c = PMF.uniformOfFintype S c.salt * ζ c.coins := by
  rw [saltedCoinLaw, map_equiv_apply, Equiv.symm_symm]
  exact prodLaw_apply _ _ _ _

/-- **The law of the fresh-value coins**: a uniform `y : Y₁` and other coins `c ← ζ`,
independently. -/
noncomputable def freshValueLaw [Fintype Y₁] [Nonempty Y₁] (ζ : PMF C) : PMF (Y₁ × C) :=
  prodLaw (PMF.uniformOfFintype Y₁) ζ

/-- Laws of the fresh-value coins with two laws of the other coins are within the distance of
those laws. -/
theorem tvDist_freshValueLaw_le [Fintype Y₁] [Nonempty Y₁] [Fintype C] (ζ ζ' : PMF C) :
    PMF.tvDist (freshValueLaw (Y₁ := Y₁) ζ) (freshValueLaw ζ') ≤ PMF.tvDist ζ ζ' := by
  rw [freshValueLaw, freshValueLaw, prodLaw, prodLaw]
  refine (PMF.tvDist_uniformOfFintype_bind_le _ _).trans ?_
  refine (Finset.expect_le_expect fun y _ => ?_).trans_eq (Fintype.expect_const _)
  exact PMF.tvDist_map_le _ _ _

variable (rel : Stmt → Wit → Prop) [DecidableRel rel]

/-- **The answers of the salted prover to `Q` proof queries, as a salted challenger's**: proof
query `j` with `(x, w)` is answered, if `rel x w`, by `core H x w (g j (u x)) (c j)` from the
values `g j` read on the slice of salt `j` and the other coins `c j` of proof query `j`. -/
def saltedReadAns (Q : ℕ) :
    (Fin Q → C) → Fin Q → ProofQuery Stmt Wit → (Fin Q → U → Y₁) → (X → Y) → Option Proof :=
  fun c j req g H =>
    if rel req.stmt req.wit then some (core H req.stmt req.wit (g j (u req.stmt)) (c j)) else none

end Provers

variable [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y]

/-- The tape law of the real game is the uniform oracle and the coins, independently. -/
theorem tapeDist_eq_prodLaw {Coins : Type*} [Fintype Coins] (Q : ℕ) (μ : PMF Coins) :
    tapeDist (X := X) (Y := Y) Q μ =
      prodLaw (PMF.uniformOfFintype (X → Y)) (PMF.pi fun _ : Fin Q => μ) :=
  rfl

/-- The real game never changes the oracle. -/
theorem keepsState_realEnv {Coins : Type*} [Fintype Coins]
    (rel : Stmt → Wit → Prop) [DecidableRel rel] {Q : ℕ}
    (P : NARG.ProverFn X Y Stmt Wit Proof Coins) (μ : PMF Coins) :
    (realEnv rel P μ Q).KeepsState :=
  fun _ _ _ _ => rfl

variable {W : Type*} [Fintype W] [Fintype Stmt] [DecidableEq Stmt] [Fintype Wit] [DecidableEq Wit]
  [Fintype Proof] [DecidableEq Proof] [AddGroup Y] {n m Q : ℕ}
  (D : Distinguisher W X Y (ProofQuery Stmt Wit) Proof n m)
  (post : (X → Y) → QState (DReg W n X Y (ProofQuery Stmt Wit) Proof) ≃ₗᵢ[ℂ]
    QState (DReg W n X Y (ProofQuery Stmt Wit) Proof))
  (emb : S × U → X) (e : Y ≃ Y₁ × Y₂) (u : Stmt → U)
  (core : (X → Y) → Stmt → Wit → Y₁ → C → Proof) (rel : Stmt → Wit → Prop) [DecidableRel rel]
  [Fintype S] [Nonempty S] [Fintype U] [DecidableEq U] [Fintype Y₁] [Nonempty Y₁] [Fintype C]

/-- **The real game of the salted reading prover is a salted challenger's game**: the salted
challenger reading first components (`saltEnvOn`) with one uniform salt and other coins `c ← ζ`
per proof query, answering by `saltedReadAns`. -/
theorem acceptProb_realEnv_saltedRead (ζ : PMF C) :
    D.acceptProb (realEnv rel (saltedReadProver emb e u core) (saltedCoinLaw ζ) Q) post =
      D.acceptProb (saltEnvOn (K := Q) emb e (saltedReadAns u core rel Q)
        (PMF.uniformOfFintype (X → Y)) (PMF.pi fun _ => ζ)
        (PMF.pi fun _ => PMF.uniformOfFintype S)) post := by
  let eT : ((X → Y) × (Fin Q → C)) × (Fin Q → S) ≃ (X → Y) × (Fin Q → SaltedCoins S C) :=
    { toFun := fun x => (x.1.1, fun i => ⟨x.2 i, x.1.2 i⟩)
      invFun := fun x => ((x.1, fun i => (x.2 i).coins), fun i => (x.2 i).salt)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  symm
  refine D.acceptProb_eq_of_map_keepsState post _ _ (keepsState_saltEnvOn _ _ _ _ _ _)
    (keepsState_realEnv rel _ _) (eT ∘ Prod.map (Prod.map id Prod.snd) id) ?_
    (fun _ => rfl) (fun _ _ _ => rfl)
  dsimp only [realEnv, saltEnvOn, saltLaw, vLaw]
  rw [← PMF.map_comp, map_prodLaw_prodMap, map_prodLaw_prodMap, map_snd_prodLaw, PMF.map_id,
    PMF.map_id, tapeDist_eq_prodLaw]
  ext ⟨H, cs⟩
  rw [map_equiv_apply]
  simp only [eT, Equiv.coe_fn_symm_mk, prodLaw_apply, PMF.pi_apply, saltedCoinLaw_apply,
    prod_mul_distrib]
  ring

omit [Nonempty S] in
/-- **The fresh challenger reading one point per proof query is the fresh-value prover's real
game**: the fresh challenger (`freshEnv`) answering by `saltedReadAns`, which reads the fresh
function of proof query `j` only at the point `u x` of its statement, has the acceptance
probability of the real game of the fresh-value prover with a uniform value and other coins
`c ← ζ` per proof query, for any law `ν` of the salts. -/
theorem acceptProb_freshEnv_saltedRead (ζ : PMF C) (ν : PMF (Fin Q → S)) :
    D.acceptProb (freshEnv (K := Q) (saltedReadAns u core rel Q)
        (PMF.uniformOfFintype (X → Y)) (PMF.pi fun _ => ζ) ν) post =
      D.acceptProb (realEnv rel (freshReadProver core) (freshValueLaw ζ) Q) post := by
  let rF : (X → Y) × (Fin Q → S) → (U → Y₁) × Y₁ × C → Fin Q → ProofQuery Stmt Wit →
      (X → Y) → Option Proof := fun v τ _ req _ =>
    if rel req.stmt req.wit then some (core v.1 req.stmt req.wit (τ.1 (u req.stmt)) τ.2.2)
    else none
  let rR : (X → Y) × (Fin Q → S) → (U → Y₁) × Y₁ × C → Fin Q → ProofQuery Stmt Wit →
      (X → Y) → Option Proof := fun _ τ _ req H =>
    if rel req.stmt req.wit then some (core H req.stmt req.wit τ.2.1 τ.2.2) else none
  let eT : ((X → Y) × (Fin Q → S)) × (Fin Q → (U → Y₁) × C) ≃
      ((X → Y) × (Fin Q → U → Y₁) × (Fin Q → C)) × (Fin Q → S) :=
    { toFun := fun x => ((x.1.1, fun i => (x.2 i).1, fun i => (x.2 i).2), x.1.2)
      invFun := fun x => ((x.1.1, x.2), fun i => (x.1.2.1 i, x.1.2.2 i))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hF : D.acceptProb (drawEnv (prodLaw (PMF.uniformOfFintype (X → Y)) ν)
      (prodLaw (PMF.uniformOfFintype (U → Y₁)) (prodLaw (PMF.uniformOfFintype Y₁) ζ))
        Prod.fst rF) post =
      D.acceptProb (freshEnv (K := Q) (saltedReadAns u core rel Q)
        (PMF.uniformOfFintype (X → Y)) (PMF.pi fun _ => ζ) ν) post := by
    refine D.acceptProb_eq_of_map_keepsState post _ _ (keepsState_drawEnv _ _ _ _)
      (keepsState_freshEnv _ _ _ _) (eT ∘ Prod.map id fun d i => Prod.map id Prod.snd (d i)) ?_
      (fun _ => rfl) (fun _ _ _ => rfl)
    dsimp only [freshEnv, drawEnv, saltLaw, vLaw]
    rw [← PMF.map_comp, map_prodLaw_prodMap, PMF.map_id, PMF.pi_map,
      map_prodLaw_prodMap, PMF.map_id, map_snd_prodLaw,
      ← PMF.pi_uniformOfFintype (β := fun _ : Fin Q => U → Y₁)]
    ext ⟨⟨H, Z, c⟩, ρ⟩
    rw [map_equiv_apply]
    simp only [eT, Equiv.coe_fn_symm_mk, prodLaw_apply, PMF.pi_apply, prod_mul_distrib]
    ring
  have hR : D.acceptProb (drawEnv (prodLaw (PMF.uniformOfFintype (X → Y)) ν)
      (prodLaw (PMF.uniformOfFintype (U → Y₁)) (prodLaw (PMF.uniformOfFintype Y₁) ζ))
        Prod.fst rR) post =
      D.acceptProb (realEnv rel (freshReadProver core) (freshValueLaw ζ) Q) post := by
    refine D.acceptProb_eq_of_map_keepsState post _ _ (keepsState_drawEnv _ _ _ _)
      (keepsState_realEnv rel _ _) (Prod.map Prod.fst fun d i => (d i).2) ?_
      (fun _ => rfl) (fun _ _ _ => rfl)
    dsimp only [realEnv, drawEnv]
    rw [map_prodLaw_prodMap, map_fst_prodLaw, PMF.pi_map, map_snd_prodLaw, tapeDist_eq_prodLaw,
      freshValueLaw]
  rw [← hF, ← hR]
  refine D.acceptProb_drawEnv_eq post _ _ Prod.fst rF rR fun v i req => ?_
  have hl : (fun τ : (U → Y₁) × Y₁ × C => rF v τ i req v.1) =
      (fun p : Y₁ × C => rR v (Classical.arbitrary (U → Y₁), p) i req v.1) ∘
        Prod.map (fun z => z (u req.stmt)) Prod.snd := rfl
  have hr : (fun τ : (U → Y₁) × Y₁ × C => rR v τ i req v.1) =
      (fun p : Y₁ × C => rR v (Classical.arbitrary (U → Y₁), p) i req v.1) ∘ Prod.snd := rfl
  rw [hl, hr, ← PMF.map_comp, ← PMF.map_comp, map_prodLaw_prodMap, map_snd_prodLaw,
    map_snd_prodLaw, PMF.uniformOfFintype_map_eval]

/-- **A prover reading the oracle at a hidden salt against the prover with a fresh value.** Let
`emb : S × U → X` be injective, `e : Y ≃ Y₁ × Y₂` a split of the oracle's values, `u` a point
map of statements, and `core` read the oracle only off the range of `emb` and in the second
components (congruent under `AgreeOffRangeOn emb e`). The real game of the salted reading prover
(a uniform hidden salt `σ`, other coins `c ← ζ`, the read `(e (H (emb (σ, u x)))).1`) and that of
the fresh-value prover (a uniform value in place of the read), against a distinguisher of the
pure game with a budget of `q` query slots of `n` parallel queries and no final unitary,
answering `Q` proof queries, differ by at most `C(Q, 2) / |S| + 2 q √(n Q / |S|)`. Invalid proof
queries are answered by `none` in both games. The proof: the salted game is a salted challenger's
(`acceptProb_realEnv_saltedRead`), hidden-salt reprogramming over the whole run
(`Distinguisher.advantage_saltOn_fresh_le_of_pi`) replaces the reads by fresh functions, and the
fresh functions read at one point per proof query are fresh values
(`acceptProb_freshEnv_saltedRead`). -/
theorem advantage_saltedRead_fresh_le [DecidableEq S] (hemb : Function.Injective emb)
    (hcore : ∀ H H', AgreeOffRangeOn emb e H H' → ∀ x w y c, core H x w y c = core H' x w y c)
    (ζ : PMF C) {q : ℕ} (bud : D.Budget q) :
    GordieHowe.advantage
        (D.acceptProb (realEnv rel (saltedReadProver emb e u core) (saltedCoinLaw ζ) Q) noPost)
        (D.acceptProb (realEnv rel (freshReadProver core) (freshValueLaw ζ) Q) noPost) ≤
      Q.choose 2 / Fintype.card S + 2 * q * √(n * (Q / Fintype.card S)) := by
  have hans : ReadsOffRangeOn emb e (saltedReadAns u core rel Q) := by
    intro c j req g H H' h
    simp only [saltedReadAns, hcore H H' h]
  rw [acceptProb_realEnv_saltedRead, ← acceptProb_freshEnv_saltedRead D noPost u core rel ζ
    (PMF.pi fun _ => PMF.uniformOfFintype S), div_eq_mul_inv, div_eq_mul_inv]
  exact D.advantage_saltOn_fresh_le_of_pi e _ _ _ hemb
    ((isUniformOnRange_uniform (emb := emb)).isUniformOnRangeOn) hans bud _
    fun _ s => (PMF.toReal_uniformOfFintype_apply s).le

end GordieHowe.QROM
