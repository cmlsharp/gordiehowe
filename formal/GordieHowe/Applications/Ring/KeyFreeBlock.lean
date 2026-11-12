-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Ring.KeyFreeSE
public import GordieHowe.Model.Quantum.Interactive.AbsorbTabBlock

@[expose] public section

/-!
# The simulation-extraction relay does not see a witness swap

The relay of the simulation-extraction step (`seTwoKF`) does not see a permutation `σR` of the
proof queries that keeps their statements and whether their witnesses are in the relation
(`seTwoKF_swapInv`): the multi-user requests are kept, a tagged statement keeps its statement,
and the replies are the same. The block hypotheses survive a change of output
(`AdaptiveIAlg.BlockRel.mapOut`, `AdaptiveIAlg.BlockNone.mapOut`).
-/

namespace GordieHowe

open Quantum Signature QROM

namespace Quantum.AdaptiveIAlg

variable {X Y Req Resp O O' L : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp]
  {shA : AlgShape X Y Req Resp} {A : AdaptiveIAlg shA O}
  {st' : StepIdx A.slots A.post → KrausMap A.R (DReg A.W A.width X Y Req Resp)
    (DReg A.W A.width X Y Req Resp)}

/-- **The adversary with other Kraus maps, with another output**, is the adversary with another
output, with the other Kraus maps. -/
theorem mapOut_withStep (g : O → O') : (A.withStep st').mapOut g = (A.mapOut g).withStep st' :=
  rfl

/-- **The block hypotheses after a change of output.** -/
theorem BlockRel.mapOut {ℓ : A.W → Option L} {G G' : ℕ → Set (A.W × Req × Option Resp)}
    {G₀ G₀' : Set (A.W × Req × Option Resp)} {σ : ℕ → Equiv.Perm (A.W × Req × Option Resp)}
    {σ₀ : Equiv.Perm (A.W × Req × Option Resp)} {r : L}
    (h : A.BlockRel st' ℓ G G' G₀ G₀' σ σ₀ r) (g : O → O') :
    (A.mapOut g).BlockRel st' ℓ G G' G₀ G₀' σ σ₀ r where
  label_eq := h.label_eq
  label_eq₀ := h.label_eq₀
  kind_eq := h.kind_eq
  set_eq := h.set_eq
  set_eq₀ := h.set_eq₀
  keepsSet := h.keepsSet
  keepsSet' := h.keepsSet'
  keeps := h.keeps
  keeps' := h.keeps'
  hop := h.hop
  init_supp := h.init_supp
  init_supp' := h.init_supp'
  init_eq := h.init_eq

/-- **The `none`-block hypotheses after a change of output.** -/
theorem BlockNone.mapOut [DecidableEq L] {ℓ : A.W → Option L}
    {G G' : ℕ → Set (A.W × Req × Option Resp)} {G₀ G₀' : Set (A.W × Req × Option Resp)}
    (h : A.BlockNone st' ℓ G G' G₀ G₀') (g : O → O') : (A.mapOut g).BlockNone st' ℓ G G' G₀ G₀'
    where
  none_eq := h.none_eq
  none_eq₀ := h.none_eq₀
  keepsSet := h.keepsSet
  keepsSet' := h.keepsSet'
  keeps := h.keeps
  keeps' := h.keeps'
  row_none_eq := h.row_none_eq
  gram_eq := h.gram_eq
  init_supp := h.init_supp
  init_supp' := h.init_supp'

end Quantum.AdaptiveIAlg

namespace RingSignature.KeyFree

variable {X Y Xb Yb : Type} {N n : ℕ} {T : Signature.SchemeTypes} {RMsg : Type}
  (B : BaseSigner Xb Yb N T RMsg) {Stmt Wit Proof R : Type}
  (rel : Stmt → Wit → Prop) [DecidableRel rel]
  (enc : MURequest (SignOracle.none B.core) n ⊕ R → ProofQuery Stmt Wit) (dummyS : Stmt)

/-- **The statement sent for a swapped proof query** is the statement sent for the query, for a
swap keeping the statements and the relation. -/
theorem stmtOf_sumCongr {σR : Equiv.Perm R}
    (hstmt : ∀ q, (enc (.inr (σR q))).stmt = (enc (.inr q)).stmt)
    (hrel : ∀ q, rel (enc (.inr (σR q))).stmt (enc (.inr (σR q))).wit ↔
      rel (enc (.inr q)).stmt (enc (.inr q)).wit)
    (r : MURequest (SignOracle.none B.core) n ⊕ R) :
    stmtOf B rel enc dummyS (Equiv.sumCongr (Equiv.refl _) σR r) = stmtOf B rel enc dummyS r := by
  rcases r with m | q
  · rfl
  · simp only [Equiv.sumCongr_apply, Sum.map_inr, stmtOf]
    exact if_congr (hrel q) (hstmt q) rfl

/-- **The simulation-extraction relay does not see a swap of the proof queries** keeping their
statements and whether their witnesses are in the relation: with `sw` the swap on the right
summand and `σ₁` the swap on the tagged statement's request, when `σ₁` fixes the blank inner
request. -/
theorem seTwoKF_swapInv [Inhabited (Stmt × (MURequest (SignOracle.none B.core) n ⊕ R))]
    (pks : Fin n → B.PK) (Q : ℕ) {σR : Equiv.Perm R}
    (hstmt : ∀ q, (enc (.inr (σR q))).stmt = (enc (.inr q)).stmt)
    (hrel : ∀ q, rel (enc (.inr (σR q))).stmt (enc (.inr (σR q))).wit ↔
      rel (enc (.inr q)).stmt (enc (.inr q)).wit)
    (hdef : ((Equiv.refl Stmt).prodCongr (Equiv.sumCongr (Equiv.refl _) σR))
      (default : Stmt × (MURequest (SignOracle.none B.core) n ⊕ R)) = default) :
    (seTwoKF (Proof := Proof) B rel enc dummyS pks Q).SwapInv
      (Equiv.sumCongr (Equiv.refl _) σR)
      ((Equiv.refl Stmt).prodCongr (Equiv.sumCongr (Equiv.refl _) σR)) where
  route c r := by
    simp only [seTwoKF, Equiv.prodCongr_apply, Equiv.coe_refl, Prod.map_apply, id_eq,
      stmtOf_sumCongr B rel enc dummyS hstmt hrel]
  outer c r := by
    rcases r with m | q
    · rfl
    · rfl
  answer₁ c r a := by
    rcases r with m | q
    · rfl
    · simp only [seTwoKF, Equiv.sumCongr_apply, Sum.map_inr]
      exact if_congr (hrel q) rfl rfl
  answer₂ c r b := rfl
  default := hdef

end RingSignature.KeyFree

end GordieHowe
