-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Ring.KeyFreeSE
public import GordieHowe.Applications.Ring.RingForgerTableSplitWin
public import GordieHowe.Model.Signature.NMA
public import GordieHowe.Model.Quantum.Interactive.AbsorbAssign
public import GordieHowe.Model.Quantum.Interactive.BaseShiftBridgeSide
public import GordieHowe.Model.Quantum.Interactive.BaseShiftBridgePre
public import GordieHowe.Model.Quantum.Interactive.BaseShiftPreChain

@[expose] public section

/-!
# The key-free route's MU-EUF-NMA^corr forger

The extraction runs of the key-free unforgeability route
(`GordieHowe/Applications/Ring/KeyFreeChain.lean`: the simulation-extraction adversary `seAlgKF` of
the absorbed adversary at a base component `ω`) bounded by MU-EUF-NMA^corr of an explicit forger,
the split table forger of `GordieHowe/Applications/Ring/RingForgerTableSplit.lean`
(`tableForgerSplit`) at the signing oracle without messages (`SignOracle.none`), the
simulation-extraction challenger, the relay `seTwoKF` and the dummy request `publicKey 0`, which is
never an outer request of `seTwoKF` (its outer requests are corruptions, `seTwoKF_outer_eq`).

The table forger's expansion and default depend on the public keys and the auxiliary input only,
while those of the extraction run of `seAlgKF` (`simProb_extAdv_seAlgKF_eq`) are named through the
table `keyReplyNone keys` and the adversary at `ω`. Both read only the claim, the challenger's
registers and the adversary's shape (workspace, width, slots and budget), so they are named here
through the shape.

- `mem_take_requests_of_logs`: a logged request with fewer than `Q` requests before it is among
  the first `Q` requests.
- `kfExpansion`, `next_insertTabM_eq`: the extraction expansion on the table-free registers.
- `kfDefault`, `dropTabM_defaultOut_eq`: the default registers, the table dropped.
- `simProb_extAdv_absorbTab_eq`: the extraction run of an adversary absorbed with a table as an
  extraction run of the table form, for an event invariant under the table.
- `kfExpansionAt`, `kfDefaultAt`, `kfForger`, `kfDrop`, `kfIns`: the forger and its bridge.
- `simProb_seAlgKF_eq_extRun`, `simLaw_extRun_kfShape`: one extraction run of `seAlgKF` in the
  table forger's form.
- `simProb_seAlgKF_eq_extRun_withStep`, `simLaw_extRun_kfShape_withStep`,
  `simProb_seAlgKF_restrictAt_eq_withStep`: the same for the restricted adversary with other Kraus
  maps.
- `kfBridge`, `kfStepAdv`, `kfForgerAdds`, `kfDropAdds`, `kfInsAdds`,
  `kfExtAdds_le_muEufNmaProb`: the extraction runs of the restricted adversaries with additions
  after their Kraus maps, at most the MU-EUF-NMA^corr success probability of the forger at
  additions on the bridge.
- `kfExt_le_muEufNmaProb`: its instance without side reads; the extraction runs' events at most
  the forger's MU-EUF-NMA^corr success probability.
- `restrictAt_mapOut_alg`: restricting and reading the output commute.
- `kfAbsAux`, `kfAbsAux.fst`, `kfAbsAux.coins`, `kfAbsAuxLaw`, `tsum_kfAbsAuxLaw_mul`,
  `tsum_kfAbsAuxLaw_avg`, `kfAbsAdv`, `tracePreserving_kfAbsAdv`: the absorbed adversaries of the
  key-free chain with the side coins in the auxiliary input.
-/

namespace GordieHowe

open Quantum Signature QROM RingSignature RingSignature.OracleSplit
open scoped ENNReal

namespace RingSignature.KeyFree

open GordieHowe.SPBCS IOP SPTerm RingSignature.Insider

/-- **A logged request numbered below `Q` is among the first `Q` requests**: the request `r` of
slot `j`, with fewer than `Q` requests logged before it, is a request of `(requests lg).take Q`. -/
theorem mem_take_requests_of_logs {Req : Type} {m Q : ℕ} (lg : LogReg Req m) (j : Fin m) {r : Req}
    (hr : lg j = some r) (hc : (requestsBefore lg j).length < Q) :
    r ∈ (requests lg).take Q := by
  obtain ⟨t, ht⟩ := requestsBefore_prefix lg (k := j + 1) j.2
  rw [requests, ← ht, requestsBefore_succ_of_lt lg j.2]
  simp only [Fin.eta, hr, Option.toList_some]
  rw [List.take_append, List.take_of_length_le (by simp; omega)]
  exact List.mem_append_left _ (List.mem_append_right _ (List.mem_singleton_self _))

section Generic

variable {k kN kS L e : ℕ} {ι : Type} {τ : SPTerm ι} {Mg : Merges τ} {nr : ι → ℕ}
  {P : (j : ι) → ProtocolSpec (nr j)} [∀ j i, Fintype ((P j).Challenge i)]
  [∀ j i, DecidableEq ((P j).Challenge i)] [∀ j i, Nonempty ((P j).Challenge i)]
  {X₀ : Type} {M : SPBCS Mg P X₀ k kN kS L e} {b : ℕ}
  [∀ j i, Fintype ((M.comp j).MessageWrite i)]
  {Vr : X₀ → FullTr P τ → Bool} (Qs : ∀ x, M.IOPQueries Vr x)
  {X' : Type} [Fintype X'] [DecidableEq X'] [Inhabited X'] {SC' : Type} [Fintype SC']
  [DecidableEq SC'] {Req Resp Req₂ Resp₂ O : Type} [Fintype Req] [DecidableEq Req]
  [Fintype Resp] [DecidableEq Resp] [Fintype Req₂] [DecidableEq Req₂] [Fintype Resp₂]
  [DecidableEq Resp₂]

local notation "Xq" => Bits (queryBits k kN kS L)

/-- **The extraction expansion on the table-free registers** of an adversary with workspace `W`,
width `width`, `slots` slots and budget `budget`: the next query of the expansion of the control
(`SPBCS.ctrlExpansionAt`) at the claim `cl` of the adversary's workspace and the challenger's
registers. -/
noncomputable def kfExpansion {W : Type} (width slots budget : ℕ) (cl : W → Claim X₀ M.NIProof)
    (Psim : NARG.Simulator Xq (XOut k e) X' (M.Response b) SC') (Q : ℕ) :
    Expansion Xq (Out k e) (CWork (AbsorbedWork W Req Resp (M.Response b) slots ×
      Fin (budget + 2)) width Xq (XOut k e) X' (M.Response b) slots (simExtChallenger Psim Q).q
      (simExtChallenger Psim Q).Coins) :=
  ⟨fun r => (ctrlExpansionAt Psim Q Qs slots).next (cl r.adv.1.1.1.work, r.chal)⟩

/-- **The extraction expansion of the adversary absorbed with a table, at the reinserted table,
is `kfExpansion`** at the adversary's shape and output (`SPBCS.comapIn_ctrlExpansion`). -/
theorem next_insertTabM_eq {shA : AlgShape Xq (XOut k e) Req Resp} (A : AdaptiveIAlg shA O)
    (F : TwoRelay Req Resp X' (M.Response b) Req₂ Resp₂) (tab : A.OuterTab Req₂ Resp₂)
    (f : O → Claim X₀ M.NIProof)
    (Psim : NARG.Simulator Xq (XOut k e) X' (M.Response b) SC') (Q : ℕ)
    (r : ExtReg A (simExtChallenger Psim Q) Req₂ Resp₂) :
    (simExtractionExpansion ((A.absorbTab F tab).mapOut f).toTPKindAlg Psim Q Qs).next
        (Quantum.AdaptiveIAlg.insertTabM A (simExtChallenger Psim Q) F tab f r) =
      (kfExpansion Qs A.width A.slots A.budget (fun w => f (A.out w)) Psim Q).next r := by
  rw [← comapIn_ctrlExpansion]
  rfl

/-- **The default registers of the extraction run, the table dropped**, for an adversary with
workspace `W`, width `width`, `slots` slots and budget `budget`: read from the chosen element of
the composed register type (`Alg.defaultOut`), whose nonemptiness `h` is given. -/
noncomputable def kfDefault {W : Type} (width slots budget : ℕ)
    (Psim : NARG.Simulator Xq (XOut k e) X' (M.Response b) SC') (Q : ℕ)
    (h : Nonempty (QueryReg (CWork ((AbsorbedWork W Req Resp (M.Response b) slots ×
      (Fin slots → Req₂ → Option Resp₂)) × Fin (budget + 2)) width Xq (XOut k e) X'
      (M.Response b) slots (simExtChallenger Psim Q).q (simExtChallenger Psim Q).Coins ×
      (Xq × XOut k e × Bool)) 1 Xq (XOut k e))) :
    CWork (AbsorbedWork W Req Resp (M.Response b) slots × Fin (budget + 2)) width Xq (XOut k e)
      X' (M.Response b) slots (simExtChallenger Psim Q).q (simExtChallenger Psim Q).Coins :=
  let v := (Classical.choice h).1.1
  ⟨(((v.adv.1.1.1.1, v.adv.1.1.2), v.adv.1.2), v.adv.2), v.chal⟩

omit [∀ j i, Nonempty ((P j).Challenge i)] in
/-- **The default of the extraction run with the table dropped is `kfDefault`** at the
adversary's shape, at every table (`Quantum.AdaptiveIAlg.dropTabM_defaultOut_congr`). -/
theorem dropTabM_defaultOut_eq {shA : AlgShape Xq (XOut k e) Req Resp} (A : AdaptiveIAlg shA O)
    (F : TwoRelay Req Resp X' (M.Response b) Req₂ Resp₂) (tab : A.OuterTab Req₂ Resp₂)
    (f : O → Claim X₀ M.NIProof)
    (Psim : NARG.Simulator Xq (XOut k e) X' (M.Response b) SC') (Q : ℕ) :
    Quantum.AdaptiveIAlg.dropTabM A (simExtChallenger Psim Q) F tab f
        ((((A.absorbTab F tab).mapOut f).toTPKindAlg.composeBothOut
          (simExtChallenger Psim Q) id).defaultOut) =
      kfDefault (W := A.W) A.width A.slots A.budget Psim Q
        (((A.absorbTab F (tab₀ A)).mapOut f).toTPKindAlg.composeBothOut
          (simExtChallenger Psim Q) id).init.nonempty := by
  rw [Quantum.AdaptiveIAlg.dropTabM_defaultOut_congr A _ F tab (tab₀ A) f]
  rfl

/-- **The extraction run of the adversary absorbed with a table as an extraction run of the table
form**, for an event `W` invariant under dropping and reinserting the table (`hW`), with the
expansion `kfExpansion` and the default `kfDefault` (`simProb_expandAdv_mapOut_cross`). -/
theorem simProb_extAdv_absorbTab_eq {shA : AlgShape Xq (XOut k e) Req Resp} (A : AdaptiveIAlg shA O)
    (F : TwoRelay Req Resp X' (M.Response b) Req₂ Resp₂) (tab : A.OuterTab Req₂ Resp₂)
    (f : O → Claim X₀ M.NIProof)
    (Psim : NARG.Simulator Xq (XOut k e) X' (M.Response b) SC') (Q kq : ℕ)
    (W : SPBCS.Reg ((A.absorbTab F tab).mapOut f) Psim Q → DB Xq (Out k e) → Prop)
    (hW : ∀ c D, W (Quantum.AdaptiveIAlg.insertTabM A (simExtChallenger Psim Q) F tab f
      (dropTabCW A (simExtChallenger Psim Q) F tab c)) D ↔ W c D) :
    simProb (outEquiv k e) (extAdv Qs ((A.absorbTab F tab).mapOut f) Psim Q kq) W =
      simLaw (outEquiv k e) (extRun (outEquiv k e) A (simExtChallenger Psim Q) F
          (kfExpansion Qs A.width A.slots A.budget (fun w => f (A.out w)) Psim Q) (kq + Q * Psim.q)
          (kfDefault (W := A.W) A.width A.slots A.budget Psim Q
            (((A.absorbTab F (tab₀ A)).mapOut f).toTPKindAlg.composeBothOut
              (simExtChallenger Psim Q) id).init.nonempty) tab)
        {x | W (Quantum.AdaptiveIAlg.insertTabM A (simExtChallenger Psim Q) F tab f x.1.out)
          x.2} := by
  have h := Quantum.AdaptiveIAlg.simProb_expandAdv_mapOut_cross (A.absorbTab F tab) f
    (simExtChallenger Psim Q)
    (simExtractionExpansion ((A.absorbTab F tab).mapOut f).toTPKindAlg Psim Q Qs)
    (kq + Q * Psim.q)
    ((((A.absorbTab F tab).mapOut f).toTPKindAlg.composeBothOut
      (simExtChallenger Psim Q) id).defaultOut)
    W (dropTabCW A (simExtChallenger Psim Q) F tab)
    (Quantum.AdaptiveIAlg.insertTabM A (simExtChallenger Psim Q) F tab f)
    (extOut A (simExtChallenger Psim Q) F (kfDefault (W := A.W) A.width A.slots A.budget Psim Q
      (((A.absorbTab F (tab₀ A)).mapOut f).toTPKindAlg.composeBothOut
        (simExtChallenger Psim Q) id).init.nonempty) tab)
    (fun o => by
      cases o
      · exact (dropTabM_defaultOut_eq A F tab f Psim Q).symm
      · rfl)
    (fun c => SPBCS.simExtractionExpansion_mapOut_next_congr Qs _ f Psim Q _ c rfl rfl) hW
  refine h.trans ?_
  have hE : (⟨fun r => (simExtractionExpansion ((A.absorbTab F tab).mapOut f).toTPKindAlg Psim Q
      Qs).next (Quantum.AdaptiveIAlg.insertTabM A (simExtChallenger Psim Q) F tab f r)⟩ :
      Expansion Xq (Out k e) (ExtReg A (simExtChallenger Psim Q) Req₂ Resp₂)) =
      kfExpansion Qs A.width A.slots A.budget (fun w => f (A.out w)) Psim Q :=
    congrArg Expansion.mk (funext fun r => next_insertTabM_eq Qs A F tab f Psim Q r)
  rw [hE]
  rfl

end Generic

section Forger

variable {k kN kS L e N n : ℕ} {Y Y₁ : Type} [AddGroup Y] [AddGroup Y₁] [Fintype Y]
  [DecidableEq Y] [Nonempty Y] [Fintype Y₁] [DecidableEq Y₁] [Nonempty Y₁]
  (sp : OracleSplit Y Y₁ (XOut k e)) {TB : BaseTypes} [Fintype TB.PK] [DecidableEq TB.PK]
  [Fintype TB.BSig]
  [DecidableEq TB.BSig] [Fintype TB.KeyCoins]
  [DecidableEq TB.KeyCoins]
  {B : BaseSigner (Bits (queryBits k kN kS L)) Y N TB} [NeZero n]
  {ι : Type} {τ : SPTerm ι} {Mg : Merges τ} {nr : ι → ℕ}
  {P : (j : ι) → ProtocolSpec (nr j)} [∀ j i, Fintype ((P j).Challenge i)]
  [∀ j i, DecidableEq ((P j).Challenge i)] [∀ j i, Nonempty ((P j).Challenge i)]
  {X₀ : Type} {M : SPBCS Mg P X₀ k kN kS L e} {b : ℕ}
  [∀ j i, Fintype ((M.comp j).MessageWrite i)]
  {Vr : X₀ → FullTr P τ → Bool} (Qs : ∀ x, M.IOPQueries Vr x)
  {Stmt Wit R Frg : Type} [Fintype Stmt] [DecidableEq Stmt] [Inhabited Stmt]
  [Fintype R] [DecidableEq R] [Inhabited R]
  (rel : Stmt → Wit → Prop) [DecidableRel rel]
  (enc : (Fin n → B.PK) → MURequest (SignOracle.none B.core) n ⊕ R → ProofQuery Stmt Wit)
  (dummyS : Stmt)
  [Inhabited M.NIProof] {SC' : Type} [Fintype SC'] [DecidableEq SC']

local notation "Xq" => Bits (queryBits k kN kS L)

local notation "MUR" => MURequest (SignOracle.none B.core) n


/-- **The expansion of the key-free extraction runs** at the public keys `pks` and the auxiliary
input `p` (`kfExpansion` at the shape of `(A pks p).restrictAt sp 0`). -/
noncomputable def kfExpansionAt
    (Aux : (Fin n → B.PK) → Type)
    {shA : ∀ pks, Aux pks → AlgShape Xq Y (MUR ⊕ R) (MUResponse B.core ⊕ M.Response b)} (A : ∀ pks (aux : Aux pks), AdaptiveIAlg (shA pks aux) (Frg × X₀))
    (prf : Frg → Option M.NIProof)
    (Psim : NARG.Simulator Xq (XOut k e) (Stmt × (MUR ⊕ R)) (M.Response b) SC') (Q : ℕ)
    (pks : Fin n → B.PK) (p : Aux pks) :
    Expansion Xq (Out k e)
      (ExtReg ((A pks p).restrictAt sp 0) (simExtChallenger Psim Q) MUR (MUResponse B.core)) :=
  kfExpansion Qs (W := (A pks p).W × (Fin (A pks p).width → Y₁)) (A pks p).width (A pks p).slots
    (A pks p).budget (fun w => claimOfOutX prf ((A pks p).out w.1)) Psim Q


/-- **The default of the key-free extraction runs** at the public keys `pks` and the auxiliary
input `p` (`kfDefault` at the shape of `(A pks p).restrictAt sp 0`). -/
noncomputable def kfDefaultAt
    (Aux : (Fin n → B.PK) → Type)
    {shA : ∀ pks, Aux pks → AlgShape Xq Y (MUR ⊕ R) (MUResponse B.core ⊕ M.Response b)} (A : ∀ pks (aux : Aux pks), AdaptiveIAlg (shA pks aux) (Frg × X₀))
    (prf : Frg → Option M.NIProof)
    (Psim : NARG.Simulator Xq (XOut k e) (Stmt × (MUR ⊕ R)) (M.Response b) SC') (Q : ℕ)
    (pks : Fin n → B.PK) (p : Aux pks) :
    ExtReg ((A pks p).restrictAt sp 0) (simExtChallenger Psim Q) MUR (MUResponse B.core) :=
  kfDefault (W := (A pks p).W × (Fin (A pks p).width → Y₁)) (A pks p).width (A pks p).slots
    (A pks p).budget Psim Q
    (((((A pks p).restrictAt sp 0).absorbTab (seTwoKF (Proof := M.Response b) B rel (enc pks) dummyS
      pks Q) (tab₀ _)).mapOut (claimOfOutX prf)).toTPKindAlg.composeBothOut
      (simExtChallenger Psim Q) id).init.nonempty


/-- **The key-free route's MU-EUF-NMA^corr forger**: the split table forger
(`tableForgerSplit`) at the signing oracle without messages, the simulation-extraction challenger
of `Psim`, the relay `seTwoKF` at the public keys with the encoding `enc pks`
of the public keys it receives,
the dummy request `publicKey 0`, the expansion and default of the key-free extraction runs, and
the readout `g`. -/
noncomputable abbrev kfForger
    (Aux : (Fin n → B.PK) → Type) (aux : ∀ pks, PMF (Aux pks))
    {shA : ∀ pks, Aux pks → AlgShape Xq Y (MUR ⊕ R) (MUResponse B.core ⊕ M.Response b)} (A : ∀ pks (aux : Aux pks), AdaptiveIAlg (shA pks aux) (Frg × X₀))
    (prf : Frg → Option M.NIProof)
    (Psim : NARG.Simulator Xq (XOut k e) (Stmt × (MUR ⊕ R)) (M.Response b) SC') (Q : ℕ)
    (kq : ℕ)
    (g : ∀ pks p, BaseGame.Tuple Xq (Out k e)
      (ExtReg ((A pks p).restrictAt sp 0) (simExtChallenger Psim Q) MUR (MUResponse B.core))
        (kq + Q * Psim.q) × DB Xq (Out k e) → B.PK × B.BMsg × B.BSig) (t' : ℕ)
    (ht : ∀ pks p, bT ((A pks p).restrictAt sp 0) (simExtChallenger Psim Q)
      (seTwoKF (Proof := M.Response b) B rel (enc pks) dummyS pks Q) (kq + Q * Psim.q) + 1 ≤ t') :
    MUAdversary (SignOracle.none B.core) n (OracleView.queriesOnly Xq Y) t' :=
  tableForgerSplit sp (SignOracle.none B.core) (outEquiv k e) Aux aux A
    (fun _ _ => simExtChallenger Psim Q)
    (fun pks _ => seTwoKF (Proof := M.Response b) B rel (enc pks) dummyS pks Q) (.publicKey 0)
    (kfExpansionAt sp Qs Aux A prf Psim Q) (kq + Q * Psim.q)
    (kfDefaultAt sp rel enc dummyS Aux A prf Psim Q) g t' ht

/-- **The bridge with the drops of the key-free extraction runs** at the users' key coins `keys`,
the auxiliary input `p` and the base component `ω` (`splitDrop`). -/
noncomputable abbrev kfDrop
    (Aux : (Fin n → B.PK) → Type)
    {shA : ∀ pks, Aux pks → AlgShape Xq Y (MUR ⊕ R) (MUResponse B.core ⊕ M.Response b)} (A : ∀ pks (aux : Aux pks), AdaptiveIAlg (shA pks aux) (Frg × X₀))
    (prf : Frg → Option M.NIProof)
    (Psim : NARG.Simulator Xq (XOut k e) (Stmt × (MUR ⊕ R)) (M.Response b) SC') (Q : ℕ)
    (kq : ℕ)
    (keys : Fin n → B.KeyCoins) (p : Aux fun i => B.pk (keys i))
    (ω : Xq → Y₁) :=
  splitDrop sp (SignOracle.none B.core) (outEquiv k e) Aux A (fun _ _ => simExtChallenger Psim Q)
    (fun pks _ => seTwoKF (Proof := M.Response b) B rel (enc pks) dummyS pks Q) (.publicKey 0)
    (kfExpansionAt sp Qs Aux A prf Psim Q) (kq + Q * Psim.q)
    (kfDefaultAt sp rel enc dummyS Aux A prf Psim Q) (fun i => B.pk (keys i)) p ω

omit [Nonempty Y] [Nonempty Y₁] [NeZero n] in
/-- **One key-free extraction run in the table forger's form**
(`simProb_extAdv_absorbTab_eq` at `seAlgKF`): the extraction run of `seAlgKF` for
`A₀.restrictAt sp ω` is the extraction run of the table form, with the expansion and the default
named through `A₀`'s shape. -/
theorem simProb_seAlgKF_eq_extRun
    {shA₀ : AlgShape Xq Y (MUR ⊕ R) (MUResponse B.core ⊕ M.Response b)} (A₀ : AdaptiveIAlg shA₀ (Frg × X₀))
    (prf : Frg → Option M.NIProof)
    (Psim : NARG.Simulator Xq (XOut k e) (Stmt × (MUR ⊕ R)) (M.Response b) SC') (Q kq : ℕ)
    (keys : Fin n → B.KeyCoins) (ω : Xq → Y₁)
    (W : SPBCS.Reg (seAlgKF (rel := rel) (enc := enc (fun i => B.pk (keys i))) (dummyS := dummyS)
        prf keys Q
        (A₀.restrictAt sp ω)) Psim Q → DB Xq (Out k e) → Prop)
    (hW : ∀ c D, W (Quantum.AdaptiveIAlg.insertTabM (A₀.restrictAt sp ω) (simExtChallenger Psim Q)
      (seTwoKF (Proof := M.Response b) B rel (enc (B.pk ∘ keys)) dummyS (B.pk ∘ keys) Q)
      (fun _ => keyReplyNone B keys) (claimOfOutX prf)
      (dropTabCW (A₀.restrictAt sp ω) (simExtChallenger Psim Q)
        (seTwoKF (Proof := M.Response b) B rel (enc (B.pk ∘ keys)) dummyS (B.pk ∘ keys) Q)
        (fun _ => keyReplyNone B keys) c)) D ↔ W c D) :
    simProb (outEquiv k e) (extAdv Qs (seAlgKF (rel := rel) (enc := enc (fun i => B.pk (keys i)))
        (dummyS := dummyS)
        prf keys Q (A₀.restrictAt sp ω)) Psim Q kq) W =
      simLaw (outEquiv k e) (extRun (outEquiv k e) (A₀.restrictAt sp ω) (simExtChallenger Psim Q)
          (seTwoKF (Proof := M.Response b) B rel (enc (B.pk ∘ keys)) dummyS (B.pk ∘ keys) Q)
          (kfExpansion Qs (A₀.restrictAt sp ω).width (A₀.restrictAt sp ω).slots
            (A₀.restrictAt sp ω).budget
            (fun w => claimOfOutX prf ((A₀.restrictAt sp ω).out w)) Psim Q) (kq + Q * Psim.q)
          (kfDefault (W := (A₀.restrictAt sp ω).W) (A₀.restrictAt sp ω).width
            (A₀.restrictAt sp ω).slots (A₀.restrictAt sp ω).budget Psim Q
            ((((A₀.restrictAt sp ω).absorbTab
              (seTwoKF (Proof := M.Response b) B rel (enc (B.pk ∘ keys)) dummyS (B.pk ∘ keys) Q)
              (tab₀ _)).mapOut (claimOfOutX prf)).toTPKindAlg.composeBothOut
              (simExtChallenger Psim Q) id).init.nonempty)
          (fun _ => keyReplyNone B keys))
        {x | W (Quantum.AdaptiveIAlg.insertTabM (A₀.restrictAt sp ω) (simExtChallenger Psim Q)
          (seTwoKF (Proof := M.Response b) B rel (enc (B.pk ∘ keys)) dummyS (B.pk ∘ keys) Q)
          (fun _ => keyReplyNone B keys) (claimOfOutX prf) x.1.out) x.2} := by
  have h := simProb_extAdv_absorbTab_eq Qs (A₀.restrictAt sp ω)
    (seTwoKF (Proof := M.Response b) B rel (enc (B.pk ∘ keys)) dummyS (B.pk ∘ keys) Q)
    (fun _ => keyReplyNone B keys) (claimOfOutX prf) Psim Q kq W hW
  refine h.trans ?_
  congr 1

omit [Nonempty Y] [Nonempty Y₁] [NeZero n] in
/-- **One key-free extraction run in the table forger's form**
for the restricted adversary with other Kraus maps (`simProb_extAdv_absorbTab_eq` at `seAlgKF`):
the extraction run of `seAlgKF` for `A₀.restrictAt sp 0` with the Kraus maps `st` is the
extraction run of the table form. -/
theorem simProb_seAlgKF_eq_extRun_withStep
    {shA₀ : AlgShape Xq Y (MUR ⊕ R) (MUResponse B.core ⊕ M.Response b)} (A₀ : AdaptiveIAlg shA₀ (Frg × X₀))
    (prf : Frg → Option M.NIProof)
    (Psim : NARG.Simulator Xq (XOut k e) (Stmt × (MUR ⊕ R)) (M.Response b) SC') (Q kq : ℕ)
    (keys : Fin n → B.KeyCoins)
    (st : StepIdx (A₀.restrictAt sp 0).slots (A₀.restrictAt sp 0).post →
      KrausMap (A₀.restrictAt sp 0).R
        (DReg (A₀.restrictAt sp 0).W (A₀.restrictAt sp 0).width Xq (XOut k e) (MUR ⊕ R)
          (MUResponse B.core ⊕ M.Response b))
        (DReg (A₀.restrictAt sp 0).W (A₀.restrictAt sp 0).width Xq (XOut k e) (MUR ⊕ R)
          (MUResponse B.core ⊕ M.Response b)))
    (W : SPBCS.Reg (seAlgKF (rel := rel) (enc := enc (fun i => B.pk (keys i))) (dummyS := dummyS)
        prf keys Q
        ((A₀.restrictAt sp 0).withStep st)) Psim Q → DB Xq (Out k e) → Prop)
    (hW : ∀ c D, W (Quantum.AdaptiveIAlg.insertTabM ((A₀.restrictAt sp 0).withStep st)
      (simExtChallenger Psim Q)
      (seTwoKF (Proof := M.Response b) B rel (enc (B.pk ∘ keys)) dummyS (B.pk ∘ keys) Q)
      (fun _ => keyReplyNone B keys) (claimOfOutX prf)
      (dropTabCW ((A₀.restrictAt sp 0).withStep st) (simExtChallenger Psim Q)
        (seTwoKF (Proof := M.Response b) B rel (enc (B.pk ∘ keys)) dummyS (B.pk ∘ keys) Q)
        (fun _ => keyReplyNone B keys) c)) D ↔ W c D) :
    simProb (outEquiv k e) (extAdv Qs (seAlgKF (rel := rel) (enc := enc (fun i => B.pk (keys i)))
        (dummyS := dummyS)
        prf keys Q ((A₀.restrictAt sp 0).withStep st)) Psim Q kq) W =
      simLaw (outEquiv k e) (extRun (outEquiv k e) ((A₀.restrictAt sp 0).withStep st)
        (simExtChallenger Psim Q)
          (seTwoKF (Proof := M.Response b) B rel (enc (B.pk ∘ keys)) dummyS (B.pk ∘ keys) Q)
          (kfExpansion Qs ((A₀.restrictAt sp 0).withStep st).width ((A₀.restrictAt sp 0).withStep
            st).slots
            ((A₀.restrictAt sp 0).withStep st).budget
            (fun w => claimOfOutX prf (((A₀.restrictAt sp 0).withStep st).out w)) Psim Q) (kq + Q
              * Psim.q)
          (kfDefault (W := ((A₀.restrictAt sp 0).withStep st).W) ((A₀.restrictAt sp 0).withStep
            st).width
            ((A₀.restrictAt sp 0).withStep st).slots ((A₀.restrictAt sp 0).withStep st).budget
              Psim Q
            (((((A₀.restrictAt sp 0).withStep st).absorbTab
              (seTwoKF (Proof := M.Response b) B rel (enc (B.pk ∘ keys)) dummyS (B.pk ∘ keys) Q)
              (tab₀ _)).mapOut (claimOfOutX prf)).toTPKindAlg.composeBothOut
              (simExtChallenger Psim Q) id).init.nonempty)
          (fun _ => keyReplyNone B keys))
        {x | W (Quantum.AdaptiveIAlg.insertTabM ((A₀.restrictAt sp 0).withStep st)
          (simExtChallenger Psim Q)
          (seTwoKF (Proof := M.Response b) B rel (enc (B.pk ∘ keys)) dummyS (B.pk ∘ keys) Q)
          (fun _ => keyReplyNone B keys) (claimOfOutX prf) x.1.out) x.2} := by
  have h := simProb_extAdv_absorbTab_eq Qs ((A₀.restrictAt sp 0).withStep st)
    (seTwoKF (Proof := M.Response b) B rel (enc (B.pk ∘ keys)) dummyS (B.pk ∘ keys) Q)
    (fun _ => keyReplyNone B keys) (claimOfOutX prf) Psim Q kq W hW
  refine h.trans ?_
  congr 1

omit [Nonempty Y] [Nonempty Y₁] [NeZero n] [∀ j i, Nonempty ((P j).Challenge i)] in
/-- **The key-free extraction run with the expansion and the default named through the
unrestricted adversary's shape**: `A₀.restrictAt sp ω` has `A₀`'s width, slots and budget, and its
output reads `A₀`'s. -/
theorem simLaw_extRun_kfShape
    {shA₀ : AlgShape Xq Y (MUR ⊕ R) (MUResponse B.core ⊕ M.Response b)} (A₀ : AdaptiveIAlg shA₀ (Frg × X₀))
    (prf : Frg → Option M.NIProof)
    (Psim : NARG.Simulator Xq (XOut k e) (Stmt × (MUR ⊕ R)) (M.Response b) SC') (Q kq : ℕ)
    (keys : Fin n → B.KeyCoins) (ω : Xq → Y₁)
    (S : Set (BaseGame.Tuple Xq (Out k e)
      (ExtReg (A₀.restrictAt sp ω) (simExtChallenger Psim Q) MUR (MUResponse B.core))
        (kq + Q * Psim.q) × DB Xq (Out k e)))
    (h₂ : Nonempty (QueryReg (CWork ((AbsorbedWork (A₀.W × (Fin A₀.width → Y₁)) (MUR ⊕ R)
      (MUResponse B.core ⊕ M.Response b) (M.Response b) A₀.slots ×
      (Fin A₀.slots → MUR → Option (MUResponse B.core))) × Fin (A₀.budget + 2)) A₀.width Xq (XOut k e)
      (Stmt × (MUR ⊕ R)) (M.Response b) A₀.slots (simExtChallenger Psim Q).q
      (simExtChallenger Psim Q).Coins × (Xq × XOut k e × Bool)) 1 Xq (XOut k e))) :
    simLaw (outEquiv k e) (extRun (outEquiv k e) (A₀.restrictAt sp ω) (simExtChallenger Psim Q)
          (seTwoKF (Proof := M.Response b) B rel (enc (B.pk ∘ keys)) dummyS (B.pk ∘ keys) Q)
          (kfExpansion Qs (A₀.restrictAt sp ω).width (A₀.restrictAt sp ω).slots
            (A₀.restrictAt sp ω).budget
            (fun w => claimOfOutX prf ((A₀.restrictAt sp ω).out w)) Psim Q) (kq + Q * Psim.q)
          (kfDefault (W := (A₀.restrictAt sp ω).W) (A₀.restrictAt sp ω).width
            (A₀.restrictAt sp ω).slots (A₀.restrictAt sp ω).budget Psim Q
            ((((A₀.restrictAt sp ω).absorbTab
              (seTwoKF (Proof := M.Response b) B rel (enc (B.pk ∘ keys)) dummyS (B.pk ∘ keys) Q)
              (tab₀ _)).mapOut (claimOfOutX prf)).toTPKindAlg.composeBothOut
              (simExtChallenger Psim Q) id).init.nonempty)
          (fun _ => keyReplyNone B keys)) S =
      simLaw (outEquiv k e) (extRun (outEquiv k e) (A₀.restrictAt sp ω) (simExtChallenger Psim Q)
          (seTwoKF (Proof := M.Response b) B rel (enc (fun i => B.pk (keys i))) dummyS (fun i =>
              B.pk (keys i)) Q)
          (kfExpansion Qs (W := A₀.W × (Fin A₀.width → Y₁)) A₀.width A₀.slots A₀.budget
            (fun w => claimOfOutX prf (A₀.out w.1)) Psim Q) (kq + Q * Psim.q)
          (kfDefault (W := A₀.W × (Fin A₀.width → Y₁)) A₀.width A₀.slots A₀.budget Psim Q h₂)
          (fun _ => keyReplyNone B keys)) S :=
  rfl

omit [Nonempty Y] [Nonempty Y₁] [NeZero n] [∀ j i, Nonempty ((P j).Challenge i)] in
/-- **`simLaw_extRun_kfShape` for the restricted adversary with other Kraus maps**:
`A₀.restrictAt sp 0` with other Kraus maps has `A₀`'s width, slots and budget, and its output
reads `A₀`'s. -/
theorem simLaw_extRun_kfShape_withStep
    {shA₀ : AlgShape Xq Y (MUR ⊕ R) (MUResponse B.core ⊕ M.Response b)} (A₀ : AdaptiveIAlg shA₀ (Frg × X₀))
    (prf : Frg → Option M.NIProof)
    (Psim : NARG.Simulator Xq (XOut k e) (Stmt × (MUR ⊕ R)) (M.Response b) SC') (Q kq : ℕ)
    (keys : Fin n → B.KeyCoins)
    (st : StepIdx (A₀.restrictAt sp 0).slots (A₀.restrictAt sp 0).post →
      KrausMap (A₀.restrictAt sp 0).R
        (DReg (A₀.restrictAt sp 0).W (A₀.restrictAt sp 0).width Xq (XOut k e) (MUR ⊕ R)
          (MUResponse B.core ⊕ M.Response b))
        (DReg (A₀.restrictAt sp 0).W (A₀.restrictAt sp 0).width Xq (XOut k e) (MUR ⊕ R)
          (MUResponse B.core ⊕ M.Response b)))
    (S : Set (BaseGame.Tuple Xq (Out k e)
      (ExtReg ((A₀.restrictAt sp 0).withStep st) (simExtChallenger Psim Q) MUR (MUResponse B.core))
        (kq + Q * Psim.q) × DB Xq (Out k e)))
    (h₂ : Nonempty (QueryReg (CWork ((AbsorbedWork (A₀.W × (Fin A₀.width → Y₁)) (MUR ⊕ R)
      (MUResponse B.core ⊕ M.Response b) (M.Response b) A₀.slots ×
      (Fin A₀.slots → MUR → Option (MUResponse B.core))) × Fin (A₀.budget + 2)) A₀.width Xq (XOut k e)
      (Stmt × (MUR ⊕ R)) (M.Response b) A₀.slots (simExtChallenger Psim Q).q
      (simExtChallenger Psim Q).Coins × (Xq × XOut k e × Bool)) 1 Xq (XOut k e))) :
    simLaw (outEquiv k e) (extRun (outEquiv k e) ((A₀.restrictAt sp 0).withStep st)
      (simExtChallenger Psim Q)
          (seTwoKF (Proof := M.Response b) B rel (enc (B.pk ∘ keys)) dummyS (B.pk ∘ keys) Q)
          (kfExpansion Qs ((A₀.restrictAt sp 0).withStep st).width ((A₀.restrictAt sp 0).withStep
            st).slots
            ((A₀.restrictAt sp 0).withStep st).budget
            (fun w => claimOfOutX prf (((A₀.restrictAt sp 0).withStep st).out w)) Psim Q) (kq + Q
              * Psim.q)
          (kfDefault (W := ((A₀.restrictAt sp 0).withStep st).W) ((A₀.restrictAt sp 0).withStep
            st).width
            ((A₀.restrictAt sp 0).withStep st).slots ((A₀.restrictAt sp 0).withStep st).budget
              Psim Q
            (((((A₀.restrictAt sp 0).withStep st).absorbTab
              (seTwoKF (Proof := M.Response b) B rel (enc (B.pk ∘ keys)) dummyS (B.pk ∘ keys) Q)
              (tab₀ _)).mapOut (claimOfOutX prf)).toTPKindAlg.composeBothOut
              (simExtChallenger Psim Q) id).init.nonempty)
          (fun _ => keyReplyNone B keys)) S =
      simLaw (outEquiv k e) (extRun (outEquiv k e) ((A₀.restrictAt sp 0).withStep st)
        (simExtChallenger Psim Q)
          (seTwoKF (Proof := M.Response b) B rel (enc (fun i => B.pk (keys i))) dummyS (fun i =>
              B.pk (keys i)) Q)
          (kfExpansion Qs (W := A₀.W × (Fin A₀.width → Y₁)) A₀.width A₀.slots A₀.budget
            (fun w => claimOfOutX prf (A₀.out w.1)) Psim Q) (kq + Q * Psim.q)
          (kfDefault (W := A₀.W × (Fin A₀.width → Y₁)) A₀.width A₀.slots A₀.budget Psim Q h₂)
          (fun _ => keyReplyNone B keys)) S :=
  rfl

omit [Nonempty Y] [Nonempty Y₁] [NeZero n] [∀ j i, Nonempty ((P j).Challenge i)] in
/-- **The simulation-extraction adversary for `A₀.restrictAt sp ω`** is that for
`A₀.restrictAt sp 0` with the Kraus maps of `A₀.restrictAt sp ω`. -/
theorem simProb_seAlgKF_restrictAt_eq_withStep
    {shA₀ : AlgShape Xq Y (MUR ⊕ R) (MUResponse B.core ⊕ M.Response b)} (A₀ : AdaptiveIAlg shA₀ (Frg × X₀))
    (prf : Frg → Option M.NIProof)
    (Psim : NARG.Simulator Xq (XOut k e) (Stmt × (MUR ⊕ R)) (M.Response b) SC') (Q kq : ℕ)
    (keys : Fin n → B.KeyCoins) (ω : Xq → Y₁)
    (W : SPBCS.Reg (seAlgKF (rel := rel) (enc := enc (fun i => B.pk (keys i))) (dummyS := dummyS)
        prf keys Q
        (A₀.restrictAt sp ω)) Psim Q → DB Xq (Out k e) → Prop) :
    simProb (outEquiv k e) (extAdv Qs (seAlgKF (rel := rel) (enc := enc (fun i => B.pk (keys i)))
        (dummyS := dummyS)
        prf keys Q (A₀.restrictAt sp ω)) Psim Q kq) W =
      simProb (outEquiv k e) (extAdv Qs (seAlgKF (rel := rel) (enc := enc (fun i => B.pk (keys i)))
          (dummyS := dummyS)
        prf keys Q ((A₀.restrictAt sp 0).withStep (A₀.restrictAt sp ω).step)) Psim Q kq) W :=
  rfl

/-- **The reinsertion of the table `keyReplyNone keys`** into the registers of the extraction
run of `(A pks p).restrictAt sp ω` (`Quantum.AdaptiveIAlg.insertTabM`), at the public keys of
`keys`. -/
noncomputable abbrev kfIns
    (Aux : (Fin n → B.PK) → Type)
    {shA : ∀ pks, Aux pks → AlgShape Xq Y (MUR ⊕ R) (MUResponse B.core ⊕ M.Response b)} (A : ∀ pks (aux : Aux pks), AdaptiveIAlg (shA pks aux) (Frg × X₀))
    (prf : Frg → Option M.NIProof)
    (Psim : NARG.Simulator Xq (XOut k e) (Stmt × (MUR ⊕ R)) (M.Response b) SC') (Q : ℕ)
    (keys : Fin n → B.KeyCoins) (p : Aux fun i => B.pk (keys i)) (ω : Xq → Y₁) :=
  Quantum.AdaptiveIAlg.insertTabM ((A _ p).restrictAt sp ω) (simExtChallenger Psim Q)
    (seTwoKF (Proof := M.Response b) B rel (enc (B.pk ∘ keys)) dummyS (B.pk ∘ keys) Q)
    (fun _ => keyReplyNone B keys) (claimOfOutX prf)

/-! ### The key-free extraction runs with additions after the restricted Kraus maps -/

/-- **The bridge of the key-free extraction runs** at the public keys `pks` and the auxiliary
input `p`: the bridge algorithm of the extraction run of `(A pks p).restrictAt sp 0`. -/
noncomputable abbrev kfBridge
    (Aux : (Fin n → B.PK) → Type)
    {shA : ∀ pks, Aux pks → AlgShape Xq Y (MUR ⊕ R) (MUResponse B.core ⊕ M.Response b)} (A : ∀ pks (aux : Aux pks), AdaptiveIAlg (shA pks aux) (Frg × X₀))
    (prf : Frg → Option M.NIProof)
    (Psim : NARG.Simulator Xq (XOut k e) (Stmt × (MUR ⊕ R)) (M.Response b) SC') (Q kq : ℕ)
    (pks : Fin n → B.PK) (p : Aux pks) :=
  bridgeAlg (outEquiv k e) ((A pks p).restrictAt sp 0) (simExtChallenger Psim Q)
    (seTwoKF (Proof := M.Response b) B rel (enc pks) dummyS pks Q) (.publicKey 0)
    (kfExpansionAt sp Qs Aux A prf Psim Q pks p) (kq + Q * Psim.q)
    (kfDefaultAt sp rel enc dummyS Aux A prf Psim Q pks p)

/-- **The restricted adversary with other Kraus maps**: `(A pks p).restrictAt sp 0` with the
Kraus maps `st keys p ω`, at the public keys of `keys`.

Running time: that of `(A pks p).restrictAt sp 0` (its paragraph) with each Kraus map replaced by
`st keys p ω`; polynomial when those are. This running time is argued here, not proved in Lean. -/
abbrev kfStepAdv
    (Aux : (Fin n → B.PK) → Type)
    {shA : ∀ pks, Aux pks → AlgShape Xq Y (MUR ⊕ R) (MUResponse B.core ⊕ M.Response b)} (A : ∀ pks (aux : Aux pks), AdaptiveIAlg (shA pks aux) (Frg × X₀))
    (st : ∀ (keys : Fin n → B.KeyCoins) (p : Aux fun i => B.pk (keys i)) (_ : Xq → Y₁),
      StepIdx ((A _ p).restrictAt sp 0).slots ((A _ p).restrictAt sp 0).post →
        KrausMap ((A _ p).restrictAt sp 0).R
          (DReg ((A _ p).restrictAt sp 0).W ((A _ p).restrictAt sp 0).width Xq (XOut k e)
            (MUR ⊕ R) (MUResponse B.core ⊕ M.Response b))
          (DReg ((A _ p).restrictAt sp 0).W ((A _ p).restrictAt sp 0).width Xq (XOut k e)
            (MUR ⊕ R) (MUResponse B.core ⊕ M.Response b)))
    (keys : Fin n → B.KeyCoins) (p : Aux fun i => B.pk (keys i)) (ω : Xq → Y₁) :=
  ((A _ p).restrictAt sp 0).withStep (st keys p ω)

/-- **The key-free route's MU-EUF-NMA^corr forger at additions on the bridge**
(`tableForgerAdds`): as `kfForger`, the drops made by the additions `Pb`.

Running time: that of `tableForgerAdds` (its paragraph) at these arguments, plus one evaluation
of `enc` at the public keys the forger receives. This running time is argued here, not proved in
Lean. -/
noncomputable abbrev kfForgerAdds
    (Aux : (Fin n → B.PK) → Type) (aux : ∀ pks, PMF (Aux pks))
    {shA : ∀ pks, Aux pks → AlgShape Xq Y (MUR ⊕ R) (MUResponse B.core ⊕ M.Response b)} (A : ∀ pks (aux : Aux pks), AdaptiveIAlg (shA pks aux) (Frg × X₀))
    (prf : Frg → Option M.NIProof)
    (Psim : NARG.Simulator Xq (XOut k e) (Stmt × (MUR ⊕ R)) (M.Response b) SC') (Q : ℕ)
    (kq : ℕ)
    (g : ∀ pks p, BaseGame.Tuple Xq (Out k e)
      (ExtReg ((A pks p).restrictAt sp 0) (simExtChallenger Psim Q) MUR (MUResponse B.core))
        (kq + Q * Psim.q) × DB Xq (Out k e) → B.PK × B.BMsg × B.BSig)
    (Pb : ∀ pks p, StepAdds (QueryReg (kfBridge sp Qs rel enc dummyS Aux A prf Psim Q kq pks p).W 1
      Xq (XOut k e)) (Fin (bT ((A pks p).restrictAt sp 0) (simExtChallenger Psim Q)
        (seTwoKF (Proof := M.Response b) B rel (enc pks) dummyS pks Q) (kq + Q * Psim.q) + 1)) Xq
            Y₁)
    (t' : ℕ)
    (ht : ∀ pks p, CoSimSchedule.slotQ (Pb pks p).nb (bT ((A pks p).restrictAt sp 0)
      (simExtChallenger Psim Q) (seTwoKF (Proof := M.Response b) B rel (enc pks) dummyS pks Q)
        (kq + Q * Psim.q) + 1) ≤ t') :
    MUAdversary (SignOracle.none B.core) n (OracleView.queriesOnly Xq Y) t' :=
  tableForgerAdds sp (SignOracle.none B.core) (outEquiv k e) Aux aux (fun pks p => (A pks p).restrictAt
    sp 0)
    (fun _ _ => simExtChallenger Psim Q)
    (fun pks _ => seTwoKF (Proof := M.Response b) B rel (enc pks) dummyS pks Q) (.publicKey 0)
    (kfExpansionAt sp Qs Aux A prf Psim Q) (kq + Q * Psim.q)
    (kfDefaultAt sp rel enc dummyS Aux A prf Psim Q) g Pb t' ht

/-- **The bridge with the drops of the additions `P` at `ω`** of the key-free extraction runs
(`bridgeAlgAdds`). -/
noncomputable abbrev kfDropAdds
    (Aux : (Fin n → B.PK) → Type)
    {shA : ∀ pks, Aux pks → AlgShape Xq Y (MUR ⊕ R) (MUResponse B.core ⊕ M.Response b)} (A : ∀ pks (aux : Aux pks), AdaptiveIAlg (shA pks aux) (Frg × X₀))
    (prf : Frg → Option M.NIProof)
    (Psim : NARG.Simulator Xq (XOut k e) (Stmt × (MUR ⊕ R)) (M.Response b) SC') (Q : ℕ)
    (kq : ℕ) (P : ∀ pks p, ((A pks p).restrictAt sp 0).AddsW Y₁)
    (keys : Fin n → B.KeyCoins) (p : Aux fun i => B.pk (keys i)) (ω : Xq → Y₁) :=
  bridgeAlgAdds (outEquiv k e) ((A _ p).restrictAt sp 0) (simExtChallenger Psim Q)
    (seTwoKF (Proof := M.Response b) B rel (enc (fun i => B.pk (keys i))) dummyS (fun i => B.pk
        (keys i)) Q) (.publicKey 0)
    (kfExpansionAt sp Qs Aux A prf Psim Q _ p) (kq + Q * Psim.q)
    (kfDefaultAt sp rel enc dummyS Aux A prf Psim Q _ p) (P _ p) ω

/-- **The reinsertion of the table** into the registers of the extraction run of the restricted
adversary with other Kraus maps. -/
noncomputable abbrev kfInsAdds
    (Aux : (Fin n → B.PK) → Type)
    {shA : ∀ pks, Aux pks → AlgShape Xq Y (MUR ⊕ R) (MUResponse B.core ⊕ M.Response b)} (A : ∀ pks (aux : Aux pks), AdaptiveIAlg (shA pks aux) (Frg × X₀))
    (prf : Frg → Option M.NIProof)
    (Psim : NARG.Simulator Xq (XOut k e) (Stmt × (MUR ⊕ R)) (M.Response b) SC') (Q : ℕ)
    (st : ∀ (keys : Fin n → B.KeyCoins) (p : Aux fun i => B.pk (keys i)) (_ : Xq → Y₁),
      StepIdx ((A _ p).restrictAt sp 0).slots ((A _ p).restrictAt sp 0).post →
        KrausMap ((A _ p).restrictAt sp 0).R
          (DReg ((A _ p).restrictAt sp 0).W ((A _ p).restrictAt sp 0).width Xq (XOut k e)
            (MUR ⊕ R) (MUResponse B.core ⊕ M.Response b))
          (DReg ((A _ p).restrictAt sp 0).W ((A _ p).restrictAt sp 0).width Xq (XOut k e)
            (MUR ⊕ R) (MUResponse B.core ⊕ M.Response b)))
    (keys : Fin n → B.KeyCoins) (p : Aux fun i => B.pk (keys i)) (ω : Xq → Y₁) :=
  Quantum.AdaptiveIAlg.insertTabM (kfStepAdv sp Aux A st keys p ω) (simExtChallenger Psim Q)
    (seTwoKF (Proof := M.Response b) B rel (enc (B.pk ∘ keys)) dummyS (B.pk ∘ keys) Q)
    (fun _ => keyReplyNone B keys) (claimOfOutX prf)

omit [Nonempty Y] [Nonempty Y₁] [NeZero n] in
/-- **One key-free extraction run with additions in the table forger's form**
(`simProb_seAlgKF_eq_extRun_withStep` and `simLaw_extRun_kfShape_withStep` at `kfStepAdv`): the
extraction run of `seAlgKF` for `kfStepAdv sp Aux A st keys p ω` is the extraction run of the table
form, with the expansion `kfExpansionAt` and the default `kfDefaultAt`. -/
theorem simProb_seAlgKF_kfStepAdv_eq_extRun
    (Aux : (Fin n → B.PK) → Type)
    {shA : ∀ pks, Aux pks → AlgShape Xq Y (MUR ⊕ R) (MUResponse B.core ⊕ M.Response b)} (A : ∀ pks (aux : Aux pks), AdaptiveIAlg (shA pks aux) (Frg × X₀))
    (prf : Frg → Option M.NIProof)
    (Psim : NARG.Simulator Xq (XOut k e) (Stmt × (MUR ⊕ R)) (M.Response b) SC') (Q kq : ℕ)
    (st : ∀ (keys : Fin n → B.KeyCoins) (p : Aux fun i => B.pk (keys i)) (_ : Xq → Y₁),
      StepIdx ((A _ p).restrictAt sp 0).slots ((A _ p).restrictAt sp 0).post →
        KrausMap ((A _ p).restrictAt sp 0).R
          (DReg ((A _ p).restrictAt sp 0).W ((A _ p).restrictAt sp 0).width Xq (XOut k e)
            (MUR ⊕ R) (MUResponse B.core ⊕ M.Response b))
          (DReg ((A _ p).restrictAt sp 0).W ((A _ p).restrictAt sp 0).width Xq (XOut k e)
            (MUR ⊕ R) (MUResponse B.core ⊕ M.Response b)))
    (keys : Fin n → B.KeyCoins) (p : Aux fun i => B.pk (keys i)) (ω : Xq → Y₁)
    (W : SPBCS.Reg (seAlgKF (rel := rel) (enc := enc (fun i => B.pk (keys i))) (dummyS := dummyS) prf
          keys Q
        (kfStepAdv sp Aux A st keys p ω)) Psim Q → DB Xq (Out k e) → Prop)
    (hW : ∀ c D, W (kfInsAdds sp rel enc dummyS Aux A prf Psim Q st keys p ω
      (dropTabCW (kfStepAdv sp Aux A st keys p ω) (simExtChallenger Psim Q)
        (seTwoKF (Proof := M.Response b) B rel (enc (B.pk ∘ keys)) dummyS (B.pk ∘ keys) Q)
        (fun _ => keyReplyNone B keys) c)) D ↔ W c D) :
    simProb (outEquiv k e) (extAdv Qs (seAlgKF (rel := rel) (enc := enc (fun i => B.pk (keys
        i))) (dummyS := dummyS) prf keys Q (kfStepAdv sp Aux A st keys p ω)) Psim Q kq) W =
      simLaw (outEquiv k e)
        (Quantum.extRun (outEquiv k e) (((A _ p).restrictAt sp 0).withStep (st keys p ω))
          (simExtChallenger Psim Q)
          (seTwoKF (Proof := M.Response b) B rel (enc fun i => B.pk (keys i)) dummyS
            (fun i => B.pk (keys i)) Q)
          (kfExpansionAt sp Qs Aux A prf Psim Q (fun i => B.pk (keys i)) p) (kq + Q * Psim.q)
          (kfDefaultAt sp rel enc dummyS Aux A prf Psim Q (fun i => B.pk (keys i)) p)
          fun _ => keyReplyNone B keys)
        {x | W (kfInsAdds sp rel enc dummyS Aux A prf Psim Q st keys p ω x.1.out) x.2} := by
  have h1 := simProb_seAlgKF_eq_extRun_withStep sp Qs rel enc dummyS (A _ p) prf Psim Q kq keys
    (st keys p ω) W hW
  -- TODO(unbundle-M4): `h1` names `kfStepAdv` unfolded; the goal's nested `NeZero` proof (of
  -- `ZMod.fintype 2`) is the abstracted `kfDefaultAt._proof_1`, so the abbrev chain
  -- `extAdv`/`seAlgKF` unfolds before proof irrelevance applies; `with_reducible` bounds it.
  with_reducible refine h1.trans ?_
  refine ((simLaw_extRun_kfShape_withStep sp Qs rel enc dummyS (A _ p) prf Psim Q kq
    keys (st keys p ω) _ (((((A _ p).restrictAt sp 0).absorbTab
      (seTwoKF (Proof := M.Response b) B rel (enc (fun i => B.pk (keys i))) dummyS (fun i => B.pk
          (keys i)) Q)
      (tab₀ _)).mapOut (claimOfOutX prf)).toTPKindAlg.composeBothOut
      (simExtChallenger Psim Q) id).init.nonempty).trans ?_)
  refine congrArg₂ (fun μ S => (simLaw (outEquiv k e) μ) S) ?_ ?_
  · simp only [kfExpansionAt, kfDefaultAt]
  · rfl

variable [Nonempty TB.KeyCoins]

/-- **The key-free extraction runs with additions after the restricted Kraus maps as
MU-EUF-NMA^corr** (`sum_simLaw_extRun_le_muEufProb_tableForgerAdds` at the signing oracle without
messages): averaged over the users' key coins, the auxiliary input and a uniform base component
`ω`, the probability of an event `W` of the extraction run of the simulation-extraction adversary
`seAlgKF` for `(A pks p).restrictAt sp 0` with the Kraus maps `st keys p ω` is at most the success
probability of `kfForgerAdds` in MU-EUF-NMA^corr with `Q'` requests. Hypotheses: the adversaries
are trace preserving (`hTP`), and so are those with the Kraus maps `st` (`hTP'`); the Kraus maps
`st keys p ω` are those of `(A pks p).restrictAt sp 0` followed by the sorted list of additions
`P` at `ω` (`hst`), none after the last Kraus map (`hlast`); the additions `Pb` on the bridge's
registers act as the drops of `P` (`hPb`); the forger makes at most `t'` queries (`ht`) and at most
`Q'` request points (`hQ`); `W` is invariant under dropping and reinserting the table (`hW`); on
every basis state of nonzero amplitude of the bridge with the drops of `P`, at an output in `W`,
the readout `g` verifies at the oracle joined from `ω` and any second component (`hver`) under the
key of a user whose corruption the absorbed adversary did not log among its first `Q` requests
(`hhon`). -/
theorem kfExtAdds_le_muEufNmaProb
    (Aux : (Fin n → B.PK) → Type) (aux : ∀ pks, PMF (Aux pks))
    {shA : ∀ pks, Aux pks → AlgShape Xq Y (MUR ⊕ R) (MUResponse B.core ⊕ M.Response b)} (A : ∀ pks (aux : Aux pks), AdaptiveIAlg (shA pks aux) (Frg × X₀))
    (prf : Frg → Option M.NIProof)
    (Psim : NARG.Simulator Xq (XOut k e) (Stmt × (MUR ⊕ R)) (M.Response b) SC') (Q : ℕ)
    (kq : ℕ) (hTP : ∀ pks p, (A pks p).TracePreserving)
    (P : ∀ pks p, ((A pks p).restrictAt sp 0).AddsW Y₁) (hlast : ∀ pks p, (P pks p).Off lastStep)
    (Pb : ∀ pks p, StepAdds (QueryReg (kfBridge sp Qs rel enc dummyS Aux A prf Psim Q kq pks p).W 1
      Xq (XOut k e)) (Fin (bT ((A pks p).restrictAt sp 0) (simExtChallenger Psim Q)
        (seTwoKF (Proof := M.Response b) B rel (enc pks) dummyS pks Q) (kq + Q * Psim.q) + 1)) Xq
            Y₁)
    (hPb : ∀ pks p ω j, (Pb pks p).perm ω j =
      bridgeDropAdds (outEquiv k e) ((A pks p).restrictAt sp 0) (simExtChallenger Psim Q)
        (seTwoKF (Proof := M.Response b) B rel (enc pks) dummyS pks Q) (.publicKey 0)
        (kfExpansionAt sp Qs Aux A prf Psim Q pks p) (kq + Q * Psim.q)
        (kfDefaultAt sp rel enc dummyS Aux A prf Psim Q pks p) (P pks p) ω j)
    (st : ∀ (keys : Fin n → B.KeyCoins) (p : Aux fun i => B.pk (keys i)) (_ : Xq → Y₁),
      StepIdx ((A _ p).restrictAt sp 0).slots ((A _ p).restrictAt sp 0).post →
        KrausMap ((A _ p).restrictAt sp 0).R
          (DReg ((A _ p).restrictAt sp 0).W ((A _ p).restrictAt sp 0).width Xq (XOut k e)
            (MUR ⊕ R) (MUResponse B.core ⊕ M.Response b))
          (DReg ((A _ p).restrictAt sp 0).W ((A _ p).restrictAt sp 0).width Xq (XOut k e)
            (MUR ⊕ R) (MUResponse B.core ⊕ M.Response b)))
    (hst : ∀ keys p ω j, KrausMap.LeftPerm ((P _ p).toStepAdds.perm ω j) (st keys p ω j)
      (((A _ p).restrictAt sp 0).step j))
    (hTP' : ∀ keys p ω, (kfStepAdv sp Aux A st keys p ω).TracePreserving)
    (g : ∀ pks p, BaseGame.Tuple Xq (Out k e)
      (ExtReg ((A pks p).restrictAt sp 0) (simExtChallenger Psim Q) MUR (MUResponse B.core))
        (kq + Q * Psim.q) × DB Xq (Out k e) → B.PK × B.BMsg × B.BSig) (t' : ℕ)
    (ht : ∀ pks p, CoSimSchedule.slotQ (Pb pks p).nb (bT ((A pks p).restrictAt sp 0)
      (simExtChallenger Psim Q) (seTwoKF (Proof := M.Response b) B rel (enc pks) dummyS pks Q)
        (kq + Q * Psim.q) + 1) ≤ t')
    {Q' : ℕ} (hQ : ∀ pks p, bT ((A pks p).restrictAt sp 0) (simExtChallenger Psim Q)
      (seTwoKF (Proof := M.Response b) B rel (enc pks) dummyS pks Q) (kq + Q * Psim.q) + 1 ≤ Q')
    (W : ∀ (keys : Fin n → B.KeyCoins) (p : Aux fun i => B.pk (keys i)) (ω : Xq → Y₁),
      SPBCS.Reg (seAlgKF (rel := rel) (enc := enc (fun i => B.pk (keys i))) (dummyS := dummyS) prf
          keys Q
        (kfStepAdv sp Aux A st keys p ω)) Psim Q → DB Xq (Out k e) → Prop)
    (hW : ∀ keys p ω c D, W keys p ω (kfInsAdds sp rel enc dummyS Aux A prf Psim Q st keys p ω
      (dropTabCW (kfStepAdv sp Aux A st keys p ω) (simExtChallenger Psim Q)
        (seTwoKF (Proof := M.Response b) B rel (enc (B.pk ∘ keys)) dummyS (B.pk ∘ keys) Q)
        (fun _ => keyReplyNone B keys) c)) D ↔ W keys p ω c D)
    (hver : ∀ keys p ω (h : Xq → XOut k e) (c : Fin Q' → (SignOracle.none B.core).Coins) v,
      simState (outEquiv k e) ((kfDropAdds sp Qs rel enc dummyS Aux A prf Psim Q kq P keys p ω).inst
        (muReplyAt sp (SignOracle.none B.core) ω keys Q' c)) v ≠ 0 →
      W keys p ω (kfInsAdds sp rel enc dummyS Aux A prf Psim Q st keys p ω
          ((kfDropAdds sp Qs rel enc dummyS Aux A prf Psim Q kq P keys p ω).out v.1.1.1).out)
        (slotsDB (outEquiv k e) v.2) →
      B.bverify (join sp ω h)
        (g _ p ((kfDropAdds sp Qs rel enc dummyS Aux A prf Psim Q kq P keys p ω).out v.1.1.1,
          slotsDB (outEquiv k e) v.2)).1
        (g _ p ((kfDropAdds sp Qs rel enc dummyS Aux A prf Psim Q kq P keys p ω).out v.1.1.1,
          slotsDB (outEquiv k e) v.2)).2.1
        (g _ p ((kfDropAdds sp Qs rel enc dummyS Aux A prf Psim Q kq P keys p ω).out v.1.1.1,
          slotsDB (outEquiv k e) v.2)).2.2 = true)
    (hhon : ∀ keys p ω (c : Fin Q' → (SignOracle.none B.core).Coins) v,
      simState (outEquiv k e) ((kfDropAdds sp Qs rel enc dummyS Aux A prf Psim Q kq P keys p ω).inst
        (muReplyAt sp (SignOracle.none B.core) ω keys Q' c)) v ≠ 0 →
      W keys p ω (kfInsAdds sp rel enc dummyS Aux A prf Psim Q st keys p ω
          ((kfDropAdds sp Qs rel enc dummyS Aux A prf Psim Q kq P keys p ω).out v.1.1.1).out)
        (slotsDB (outEquiv k e) v.2) →
      ∃ i, B.pk (keys i) = (g _ p ((kfDropAdds sp Qs rel enc dummyS Aux A prf Psim Q kq P keys p
        ω).out v.1.1.1, slotsDB (outEquiv k e) v.2)).1 ∧
        (.inl (.corrupt i) : MUR ⊕ R) ∉ (Quantum.requests (extLogs
          ((kfDropAdds sp Qs rel enc dummyS Aux A prf Psim Q kq P keys p ω).out
            v.1.1.1).out)).take Q) :
    ∑' keys, PMF.uniformOfFintype (Fin n → B.KeyCoins) keys *
      ∑' p, aux (fun i => B.pk (keys i)) p *
        ∑' ω, PMF.uniformOfFintype (Xq → Y₁) ω *
          simProb (outEquiv k e) (extAdv Qs (seAlgKF (rel := rel) (enc := enc (fun i => B.pk (keys
              i))) (dummyS := dummyS)
            prf keys Q (kfStepAdv sp Aux A st keys p ω)) Psim Q kq) (W keys p ω) ≤
      muEufNmaProb (kfForgerAdds sp Qs rel enc dummyS Aux aux A prf Psim Q kq g Pb t' ht) Q' := by
  refine le_of_eq_of_le ?_ (sum_simLaw_extRun_le_muEufProb_tableForgerAdds sp
    (SignOracle.none B.core) (outEquiv k e) Aux aux (fun pks p => (A pks p).restrictAt sp 0)
    (fun _ _ => simExtChallenger Psim Q)
    (fun pks _ => seTwoKF (Proof := M.Response b) B rel (enc pks) dummyS pks Q) (.publicKey 0)
    (kfExpansionAt sp Qs Aux A prf Psim Q) (kq + Q * Psim.q)
    (kfDefaultAt sp rel enc dummyS Aux A prf Psim Q) g (fun _ sm => sm.elim)
    (fun pks p => (A pks p).tracePreserving_restrictAt sp 0 (hTP pks p))
    (fun pks _ c r q h hq => ?_) (fun _ sm => sm.elim) P hlast Pb hPb st hst hTP' t' ht hQ
    (fun keys _ _ _ _ => keyReplyNone B keys) (fun keys p ω c j q _ => ?_)
    (fun keys p ω => {x | W keys p ω
      (kfInsAdds sp rel enc dummyS Aux A prf Psim Q st keys p ω x.1.out) x.2})
    (fun keys p ω h c v hv hx => ⟨hver keys p ω h c v hv hx, ?_⟩))
  · refine tsum_congr fun keys => congrArg _ (tsum_congr fun p => congrArg _
      (tsum_congr fun ω => congrArg _ ?_))
    rw [← Finset.sum_mul, PMF.sum_coe, one_mul]
    -- TODO(unbundle-M4): the summand's shapes are the instantiated `restrictAt` literals, and
    -- `exact` unfolds the `extAdv`/`seAlgKF` abbrevs before comparing arguments; `convert`
    -- compares them argument-wise.
    convert simProb_seAlgKF_kfStepAdv_eq_extRun sp Qs rel enc dummyS Aux A prf Psim Q kq st keys
      p ω (W keys p ω) (hW keys p ω) using 3
  · obtain ⟨i, -, rfl⟩ := seTwoKF_outer_eq B rel (enc pks) dummyS pks h
    cases hq
  · have h1 : (bridgeCompose ((A _ p).restrictAt sp 0) (simExtChallenger Psim Q)
        (seTwoKF (Proof := M.Response b) B rel (enc (fun i => B.pk (keys i))) dummyS (fun i => B.pk
            (keys i)) Q)).depth +
          (kq + Q * Psim.q) + 1 ≤ Q' := hQ _ p
    rw [depth_bridgeCompose] at h1
    have hw := ((A _ p).restrictAt sp 0).width_pos
    have hle : ((A _ p).restrictAt sp 0).slots ≤ ((A _ p).restrictAt sp 0).slots *
        ((simExtChallenger Psim Q).q + ((A _ p).restrictAt sp 0).width) :=
      Nat.le_mul_of_pos_right _ (by omega)
    have hjs : (j : ℕ) < ((A _ p).restrictAt sp 0).slots := j.isLt
    have hj : (j : ℕ) < Q' := by omega
    unfold muReplyAt
    simp only [hj, ↓reduceDIte]
    rcases q with i | ⟨i, sm⟩ | i
    · rfl
    · exact sm.elim
    · rfl
  · obtain ⟨i, hi, hni⟩ := hhon keys p ω c v hv hx
    refine ⟨i, hi, fun hc => hni ?_, fun sm _ => sm.elim⟩
    obtain ⟨j, hj⟩ := (mem_requests_iff _ _).1 hc
    rcases bridgeAlgAdds_logs (outEquiv k e) ((A _ p).restrictAt sp 0) (simExtChallenger Psim Q)
      (seTwoKF (Proof := M.Response b) B rel (enc (fun i => B.pk (keys i))) dummyS (fun i => B.pk
          (keys i)) Q) (.publicKey 0)
      (kfExpansionAt sp Qs Aux A prf Psim Q _ p) (kq + Q * Psim.q)
      (kfDefaultAt sp rel enc dummyS Aux A prf Psim Q _ p) ω (P _ p)
      ((A _ p).tracePreserving_restrictAt sp 0 (hTP _ p)) _ hv hj with hq | ⟨j', r, hr, ho⟩
    · cases hq
    · obtain ⟨i', rfl, hq⟩ := seTwoKF_outer_eq B rel (enc _) dummyS _ ho
      have key : ∀ c (i : Fin n) q, (seTwoKF (Proof := M.Response b) B rel (enc (fun i => B.pk (keys
          i))) dummyS
          (fun i => B.pk (keys i)) Q).outer c (.inl (.corrupt i)) = some q → c < Q :=
        fun c i q h => by
          by_contra hc
          simp [seTwoKF, hc] at h
      have hlt := key _ _ _ ho
      cases hq
      exact mem_take_requests_of_logs _ j' hr hlt

omit [Nonempty Y₁] [Nonempty TB.KeyCoins] in
/-- **A corruption logged by the bridge read after drops is among the absorbed adversary's first
`Q` requests**: on every basis state of nonzero amplitude of the instance of the bridge read after
drops `β` that keep the absorbed logs, the halting flag and the ancilla (`hβ`), a logged
corruption request is the outer request of a logged corruption among the first `Q` requests of
the output's absorbed logs. -/
theorem kfDrops_corrupt_mem (keys : Fin n → B.KeyCoins) (Q kq' : ℕ)
    (Psim : NARG.Simulator Xq (XOut k e) (Stmt × (MUR ⊕ R)) (M.Response b) SC')
    {shAr : AlgShape Xq (XOut k e) (MUR ⊕ R) (MUResponse B.core ⊕ M.Response b)} (Ar : AdaptiveIAlg shAr (Frg × X₀))
    (E : Expansion Xq (Out k e) (ExtReg Ar (simExtChallenger Psim Q) MUR (MUResponse B.core)))
    (d₀ : ExtReg Ar (simExtChallenger Psim Q) MUR (MUResponse B.core))
    (β : ℕ → Equiv.Perm (ReprogrammedQueryReg ((Ar.absorbTab
      (seTwoKF (Proof := M.Response b) B rel (enc (fun i => B.pk (keys i))) dummyS (fun i => B.pk
          (keys i)) Q)
      (tab₀ Ar)).toTPKindAlg.CW (simExtChallenger Psim Q)) Xq (XOut k e)))
    (hβ : ∀ n x, (β n x).1.1.adv.workspace.1.1.logs = x.1.1.adv.workspace.1.1.logs ∧
      (β n x).1.2 = x.1.2 ∧ (β n x).2 = x.2)
    (π : Fin (bT Ar (simExtChallenger Psim Q)
      (seTwoKF (Proof := M.Response b) B rel (enc (fun i => B.pk (keys i))) dummyS (fun i => B.pk
          (keys i)) Q) kq' + 1) →
      Equiv.Perm (QueryReg (bridgeAlg (outEquiv k e) Ar (simExtChallenger Psim Q)
        (seTwoKF (Proof := M.Response b) B rel (enc (fun i => B.pk (keys i))) dummyS (fun i => B.pk
            (keys i)) Q)
        (.publicKey 0) E kq' d₀).W 1 Xq (XOut k e)))
    (hπ : π = bridgeDropPerms (outEquiv k e) Ar (simExtChallenger Psim Q)
      (seTwoKF (Proof := M.Response b) B rel (enc (fun i => B.pk (keys i))) dummyS (fun i => B.pk
          (keys i)) Q) (.publicKey 0)
      E kq' d₀ β)
    (hA : Ar.TracePreserving) (a : ℕ → MUR → Option (MUResponse B.core))
    {v : SimRegister (((bridgeAlg (outEquiv k e) Ar (simExtChallenger Psim Q)
      (seTwoKF (Proof := M.Response b) B rel (enc (fun i => B.pk (keys i))) dummyS (fun i => B.pk
          (keys i)) Q)
      (.publicKey 0) E kq' d₀).withPerm π).inst a).W _ _ _ _}
    (hv : simState (outEquiv k e) (((bridgeAlg (outEquiv k e) Ar (simExtChallenger Psim Q)
      (seTwoKF (Proof := M.Response b) B rel (enc (fun i => B.pk (keys i))) dummyS (fun i => B.pk
          (keys i)) Q)
      (.publicKey 0) E kq' d₀).withPerm π).inst a) v ≠ 0)
    (i : Fin n) (hc : MURequest.corrupt i ∈ Quantum.requests v.1.1.2) :
    (.inl (.corrupt i) : MUR ⊕ R) ∈ (Quantum.requests (extLogs
      (((bridgeAlg (outEquiv k e) Ar (simExtChallenger Psim Q)
        (seTwoKF (Proof := M.Response b) B rel (enc (fun i => B.pk (keys i))) dummyS (fun i => B.pk
            (keys i)) Q)
        (.publicKey 0) E kq' d₀).withPerm π).out v.1.1.1).out)).take Q := by
  subst hπ
  obtain ⟨j, hj⟩ := (mem_requests_iff _ _).1 hc
  rcases bridgeAlgDrops_logs (outEquiv k e) Ar (simExtChallenger Psim Q)
    (seTwoKF (Proof := M.Response b) B rel (enc (fun i => B.pk (keys i))) dummyS (fun i => B.pk
        (keys i)) Q) (.publicKey 0)
    E kq' d₀ β hβ hA a hv hj with hq | ⟨j', r, hr, ho⟩
  · cases hq
  · obtain ⟨i', rfl, hq⟩ := seTwoKF_outer_eq B rel (enc _) dummyS _ ho
    have key : ∀ c (i : Fin n) q, (seTwoKF (Proof := M.Response b) B rel (enc (fun i => B.pk (keys
        i))) dummyS
        (fun i => B.pk (keys i)) Q).outer c (.inl (.corrupt i)) = some q → c < Q :=
      fun c i q h => by
        by_contra hc
        simp [seTwoKF, hc] at h
    have hlt := key _ _ _ ho
    cases hq
    exact mem_take_requests_of_logs _ j' hr hlt

/-- **The bridge read after additions `Pb` at `ω`**, at the public keys of `keys`. -/
noncomputable abbrev kfDropPb
    (Aux : (Fin n → B.PK) → Type)
    {shA : ∀ pks, Aux pks → AlgShape Xq Y (MUR ⊕ R) (MUResponse B.core ⊕ M.Response b)} (A : ∀ pks (aux : Aux pks), AdaptiveIAlg (shA pks aux) (Frg × X₀))
    (prf : Frg → Option M.NIProof)
    (Psim : NARG.Simulator Xq (XOut k e) (Stmt × (MUR ⊕ R)) (M.Response b) SC') (Q kq : ℕ)
    (Pb : ∀ pks p, StepAdds (QueryReg (kfBridge sp Qs rel enc dummyS Aux A prf Psim Q kq pks p).W 1
      Xq (XOut k e)) (Fin (bT ((A pks p).restrictAt sp 0) (simExtChallenger Psim Q)
        (seTwoKF (Proof := M.Response b) B rel (enc pks) dummyS pks Q) (kq + Q * Psim.q) + 1)) Xq
            Y₁)
    (keys : Fin n → B.KeyCoins) (p : Aux fun i => B.pk (keys i)) (ω : Xq → Y₁) :=
  (kfBridge sp Qs rel enc dummyS Aux A prf Psim Q kq (fun i => B.pk (keys i)) p).withPerm
    ((Pb _ p).perm ω)

/-- **The key-free extraction runs with additions before and after the restricted Kraus maps
as MU-EUF-NMA^corr** (`AdaptiveIAlg.AddsW.simLaw_extRun_instLog_pre`,
`sum_simLaw_le_muEufProb_tableForgerAdds`): as `kfExtAdds_le_muEufNmaProb`, for Kraus maps
`st keys p ω` that are `s₀ pks p ω` followed by `P` (`hst`), where `s₀` are the restricted Kraus
maps read after `σ` (`hst₀`, `σ` keeping the query pairs, `hσ`), trace preserving (`hTP₀`), and
additions `Pb` on the bridge acting as the drops of `P` and then the lifted `σ` at the starts of
the query intervals (`hPb`); the bridge of `hver` and `hhon` is read after `Pb` (`kfDropPb`). -/
theorem kfExtPre_le_muEufNmaProb
    (Aux : (Fin n → B.PK) → Type) (aux : ∀ pks, PMF (Aux pks))
    {shA : ∀ pks, Aux pks → AlgShape Xq Y (MUR ⊕ R) (MUResponse B.core ⊕ M.Response b)} (A : ∀ pks (aux : Aux pks), AdaptiveIAlg (shA pks aux) (Frg × X₀))
    (prf : Frg → Option M.NIProof)
    (Psim : NARG.Simulator Xq (XOut k e) (Stmt × (MUR ⊕ R)) (M.Response b) SC') (Q : ℕ)
    (kq : ℕ) (hTP : ∀ pks p, (A pks p).TracePreserving)
    (P : ∀ pks p, ((A pks p).restrictAt sp 0).AddsW Y₁) (hlast : ∀ pks p, (P pks p).Off lastStep)
    (Pb : ∀ pks p, StepAdds (QueryReg (kfBridge sp Qs rel enc dummyS Aux A prf Psim Q kq pks p).W 1
      Xq (XOut k e)) (Fin (bT ((A pks p).restrictAt sp 0) (simExtChallenger Psim Q)
        (seTwoKF (Proof := M.Response b) B rel (enc pks) dummyS pks Q) (kq + Q * Psim.q) + 1)) Xq
            Y₁)
    (σ : ∀ pks p, (Xq → Y₁) → StepIdx ((A pks p).restrictAt sp 0).slots
      ((A pks p).restrictAt sp 0).post → Equiv.Perm (DReg ((A pks p).restrictAt sp 0).W
        ((A pks p).restrictAt sp 0).width Xq (XOut k e) (MUR ⊕ R) (MUResponse B.core ⊕ M.Response b)))
    (hσ : ∀ pks p ω j x, (σ pks p ω j x).2 = x.2)
    (hPb : ∀ pks p ω j, (Pb pks p).perm ω j =
      bridgeDropPerms (outEquiv k e) ((A pks p).restrictAt sp 0) (simExtChallenger Psim Q)
        (seTwoKF (Proof := M.Response b) B rel (enc pks) dummyS pks Q) (.publicKey 0)
        (kfExpansionAt sp Qs Aux A prf Psim Q pks p) (kq + Q * Psim.q)
        (kfDefaultAt sp rel enc dummyS Aux A prf Psim Q pks p)
        (fun j => (addsDrop (simExtChallenger Psim Q)
          (seTwoKF (Proof := M.Response b) B rel (enc pks) dummyS pks Q) ω (P pks p)
          (tab₀ ((A pks p).restrictAt sp 0)) j).trans
          (KindAlg.prePerms (simExtChallenger Psim Q) (((A pks p).restrictAt sp 0).preT
            (seTwoKF (Proof := M.Response b) B rel (enc pks) dummyS pks Q) (σ pks p ω)) j)) j)
    (s₀ : ∀ pks p, (Xq → Y₁) → StepIdx ((A pks p).restrictAt sp 0).slots
      ((A pks p).restrictAt sp 0).post → KrausMap ((A pks p).restrictAt sp 0).R
        (DReg ((A pks p).restrictAt sp 0).W ((A pks p).restrictAt sp 0).width Xq (XOut k e)
          (MUR ⊕ R) (MUResponse B.core ⊕ M.Response b))
        (DReg ((A pks p).restrictAt sp 0).W ((A pks p).restrictAt sp 0).width Xq (XOut k e)
          (MUR ⊕ R) (MUResponse B.core ⊕ M.Response b)))
    (hst₀ : ∀ pks p ω j, KrausMap.RightPerm (σ pks p ω j) (s₀ pks p ω j)
      (((A pks p).restrictAt sp 0).step j))
    (hTP₀ : ∀ pks p ω, (((A pks p).restrictAt sp 0).withStep (s₀ pks p ω)).TracePreserving)
    (st : ∀ (keys : Fin n → B.KeyCoins) (p : Aux fun i => B.pk (keys i)) (_ : Xq → Y₁),
      StepIdx ((A _ p).restrictAt sp 0).slots ((A _ p).restrictAt sp 0).post →
        KrausMap ((A _ p).restrictAt sp 0).R
          (DReg ((A _ p).restrictAt sp 0).W ((A _ p).restrictAt sp 0).width Xq (XOut k e)
            (MUR ⊕ R) (MUResponse B.core ⊕ M.Response b))
          (DReg ((A _ p).restrictAt sp 0).W ((A _ p).restrictAt sp 0).width Xq (XOut k e)
            (MUR ⊕ R) (MUResponse B.core ⊕ M.Response b)))
    (hst : ∀ keys p ω j, KrausMap.LeftPerm ((P _ p).toStepAdds.perm ω j) (st keys p ω j)
      (s₀ _ p ω j))
    (hTP' : ∀ keys p ω, (kfStepAdv sp Aux A st keys p ω).TracePreserving)
    (g : ∀ pks p, BaseGame.Tuple Xq (Out k e)
      (ExtReg ((A pks p).restrictAt sp 0) (simExtChallenger Psim Q) MUR (MUResponse B.core))
        (kq + Q * Psim.q) × DB Xq (Out k e) → B.PK × B.BMsg × B.BSig) (t' : ℕ)
    (ht : ∀ pks p, CoSimSchedule.slotQ (Pb pks p).nb (bT ((A pks p).restrictAt sp 0)
      (simExtChallenger Psim Q) (seTwoKF (Proof := M.Response b) B rel (enc pks) dummyS pks Q)
        (kq + Q * Psim.q) + 1) ≤ t')
    {Q' : ℕ} (hQ : ∀ pks p, bT ((A pks p).restrictAt sp 0) (simExtChallenger Psim Q)
      (seTwoKF (Proof := M.Response b) B rel (enc pks) dummyS pks Q) (kq + Q * Psim.q) + 1 ≤ Q')
    (W : ∀ (keys : Fin n → B.KeyCoins) (p : Aux fun i => B.pk (keys i)) (ω : Xq → Y₁),
      SPBCS.Reg (seAlgKF (rel := rel) (enc := enc (fun i => B.pk (keys i))) (dummyS := dummyS) prf
          keys Q
        (kfStepAdv sp Aux A st keys p ω)) Psim Q → DB Xq (Out k e) → Prop)
    (hW : ∀ keys p ω c D, W keys p ω (kfInsAdds sp rel enc dummyS Aux A prf Psim Q st keys p ω
      (dropTabCW (kfStepAdv sp Aux A st keys p ω) (simExtChallenger Psim Q)
        (seTwoKF (Proof := M.Response b) B rel (enc (B.pk ∘ keys)) dummyS (B.pk ∘ keys) Q)
        (fun _ => keyReplyNone B keys) c)) D ↔ W keys p ω c D)
    (hver : ∀ keys p ω (h : Xq → XOut k e) (c : Fin Q' → (SignOracle.none B.core).Coins) v,
      simState (outEquiv k e) ((kfDropPb sp Qs rel enc dummyS Aux A prf Psim Q kq Pb keys p ω).inst
        (muReplyAt sp (SignOracle.none B.core) ω keys Q' c)) v ≠ 0 →
      W keys p ω (kfInsAdds sp rel enc dummyS Aux A prf Psim Q st keys p ω
          ((kfDropPb sp Qs rel enc dummyS Aux A prf Psim Q kq Pb keys p ω).out v.1.1.1).out)
        (slotsDB (outEquiv k e) v.2) →
      B.bverify (join sp ω h)
        (g _ p ((kfDropPb sp Qs rel enc dummyS Aux A prf Psim Q kq Pb keys p ω).out v.1.1.1,
          slotsDB (outEquiv k e) v.2)).1
        (g _ p ((kfDropPb sp Qs rel enc dummyS Aux A prf Psim Q kq Pb keys p ω).out v.1.1.1,
          slotsDB (outEquiv k e) v.2)).2.1
        (g _ p ((kfDropPb sp Qs rel enc dummyS Aux A prf Psim Q kq Pb keys p ω).out v.1.1.1,
          slotsDB (outEquiv k e) v.2)).2.2 = true)
    (hhon : ∀ keys p ω (c : Fin Q' → (SignOracle.none B.core).Coins) v,
      simState (outEquiv k e) ((kfDropPb sp Qs rel enc dummyS Aux A prf Psim Q kq Pb keys p ω).inst
        (muReplyAt sp (SignOracle.none B.core) ω keys Q' c)) v ≠ 0 →
      W keys p ω (kfInsAdds sp rel enc dummyS Aux A prf Psim Q st keys p ω
          ((kfDropPb sp Qs rel enc dummyS Aux A prf Psim Q kq Pb keys p ω).out v.1.1.1).out)
        (slotsDB (outEquiv k e) v.2) →
      ∃ i, B.pk (keys i) = (g _ p ((kfDropPb sp Qs rel enc dummyS Aux A prf Psim Q kq Pb keys
        p ω).out v.1.1.1, slotsDB (outEquiv k e) v.2)).1 ∧
        (.inl (.corrupt i) : MUR ⊕ R) ∉ (Quantum.requests (extLogs
          ((kfDropPb sp Qs rel enc dummyS Aux A prf Psim Q kq Pb keys p ω).out
            v.1.1.1).out)).take Q) :
    ∑' keys, PMF.uniformOfFintype (Fin n → B.KeyCoins) keys *
      ∑' p, aux (fun i => B.pk (keys i)) p *
        ∑' ω, PMF.uniformOfFintype (Xq → Y₁) ω *
          simProb (outEquiv k e) (extAdv Qs (seAlgKF (rel := rel) (enc := enc (fun i => B.pk (keys
              i))) (dummyS := dummyS)
            prf keys Q (kfStepAdv sp Aux A st keys p ω)) Psim Q kq) (W keys p ω) ≤
      muEufNmaProb (kfForgerAdds sp Qs rel enc dummyS Aux aux A prf Psim Q kq g Pb t' ht) Q' := by
  have hβ : ∀ (keys : Fin n → B.KeyCoins) (p : Aux fun i => B.pk (keys i)) (ω : Xq → Y₁),
      (Pb _ p).perm ω = _ := fun keys p ω => funext (hPb _ p ω)
  refine le_of_eq_of_le ?_ (sum_simLaw_le_muEufProb_tableForgerAdds sp
    (SignOracle.none B.core) (outEquiv k e) Aux aux (fun pks p => (A pks p).restrictAt sp 0)
    (fun _ _ => simExtChallenger Psim Q)
    (fun pks _ => seTwoKF (Proof := M.Response b) B rel (enc pks) dummyS pks Q) (.publicKey 0)
    (kfExpansionAt sp Qs Aux A prf Psim Q) (kq + Q * Psim.q)
    (kfDefaultAt sp rel enc dummyS Aux A prf Psim Q) g (fun _ sm => sm.elim) (fun _ sm => sm.elim)
    Pb t' ht hQ (fun keys _ _ _ _ => keyReplyNone B keys) (fun keys p ω c j q _ => ?_)
    (fun keys p ω => {x | W keys p ω
      (kfInsAdds sp rel enc dummyS Aux A prf Psim Q st keys p ω x.1.out) x.2})
    _ (fun keys p ω c => (AdaptiveIAlg.AddsW.simLaw_extRun_instLog_pre (outEquiv k e)
      ((A _ p).restrictAt sp 0) (simExtChallenger Psim Q)
      (seTwoKF (Proof := M.Response b) B rel (enc (fun i => B.pk (keys i))) dummyS (fun i => B.pk
          (keys i)) Q) (.publicKey 0)
      ω (P _ p) (σ _ p ω) (s₀ _ p ω) (st keys p ω) (hst₀ _ p ω) (hst keys p ω)
      ((A _ p).tracePreserving_restrictAt sp 0 (hTP _ p)) (hTP₀ _ p ω) (hTP' keys p ω) (hlast _ p)
      (fun c r q h hq => by
        obtain ⟨i, -, rfl⟩ := seTwoKF_outer_eq B rel (enc _) dummyS _ h
        cases hq) (kfExpansionAt sp Qs Aux A prf Psim Q _ p) (kq + Q * Psim.q)
      (kfDefaultAt sp rel enc dummyS Aux A prf Psim Q _ p) fun _ => keyReplyNone B keys).trans
        (by
          unfold bridgeAlgDrops
          rw [← hβ keys p ω]))
    (fun keys p ω h c v hv hx => ⟨hver keys p ω h c v hv hx, ?_⟩))
  · refine tsum_congr fun keys => congrArg _ (tsum_congr fun p => congrArg _
      (tsum_congr fun ω => congrArg _ ?_))
    rw [← Finset.sum_mul, PMF.sum_coe, one_mul]
    -- TODO(unbundle-M4): the summand's shapes are the instantiated `restrictAt` literals, and
    -- `exact` unfolds the `extAdv`/`seAlgKF` abbrevs before comparing arguments; `convert`
    -- compares them argument-wise.
    convert simProb_seAlgKF_kfStepAdv_eq_extRun sp Qs rel enc dummyS Aux A prf Psim Q kq st keys
      p ω (W keys p ω) (hW keys p ω) using 3
  · have h1 : (bridgeCompose ((A _ p).restrictAt sp 0) (simExtChallenger Psim Q)
        (seTwoKF (Proof := M.Response b) B rel (enc (fun i => B.pk (keys i))) dummyS (fun i => B.pk
            (keys i)) Q)).depth +
          (kq + Q * Psim.q) + 1 ≤ Q' := hQ _ p
    rw [depth_bridgeCompose] at h1
    have hw := ((A _ p).restrictAt sp 0).width_pos
    have hle : ((A _ p).restrictAt sp 0).slots ≤ ((A _ p).restrictAt sp 0).slots *
        ((simExtChallenger Psim Q).q + ((A _ p).restrictAt sp 0).width) :=
      Nat.le_mul_of_pos_right _ (by omega)
    have hjs : (j : ℕ) < ((A _ p).restrictAt sp 0).slots := j.isLt
    have hj : (j : ℕ) < Q' := by omega
    unfold muReplyAt
    simp only [hj, ↓reduceDIte]
    rcases q with i | ⟨i, sm⟩ | i
    · rfl
    · exact sm.elim
    · rfl
  · have hh := hhon keys p ω c v hv hx
    obtain ⟨i, hrest⟩ := hh
    refine ⟨i, ?_, ?_⟩
    · exact hrest.1
    · refine ⟨fun hc => ?_, fun sm _ => sm.elim⟩
      apply hrest.2
      have hkeep : ∀ n' x, (((addsDrop (simExtChallenger Psim Q)
          (seTwoKF (Proof := M.Response b) B rel (enc (fun i => B.pk (keys i))) dummyS (fun i =>
              B.pk (keys i)) Q) ω (P _ p)
          (tab₀ ((A _ p).restrictAt sp 0)) n').trans
          (KindAlg.prePerms (simExtChallenger Psim Q) (((A _ p).restrictAt sp 0).preT
            (seTwoKF (Proof := M.Response b) B rel (enc (fun i => B.pk (keys i))) dummyS (fun i =>
                B.pk (keys i)) Q)
            (σ _ p ω)) n')) x).1.1.adv.workspace.1.1.logs = x.1.1.adv.workspace.1.1.logs ∧
          (((addsDrop (simExtChallenger Psim Q)
          (seTwoKF (Proof := M.Response b) B rel (enc (fun i => B.pk (keys i))) dummyS (fun i =>
              B.pk (keys i)) Q) ω (P _ p)
          (tab₀ ((A _ p).restrictAt sp 0)) n').trans
          (KindAlg.prePerms (simExtChallenger Psim Q) (((A _ p).restrictAt sp 0).preT
            (seTwoKF (Proof := M.Response b) B rel (enc (fun i => B.pk (keys i))) dummyS (fun i =>
                B.pk (keys i)) Q)
            (σ _ p ω)) n')) x).1.2 = x.1.2 ∧
          (((addsDrop (simExtChallenger Psim Q)
          (seTwoKF (Proof := M.Response b) B rel (enc (fun i => B.pk (keys i))) dummyS (fun i =>
              B.pk (keys i)) Q) ω (P _ p)
          (tab₀ ((A _ p).restrictAt sp 0)) n').trans
          (KindAlg.prePerms (simExtChallenger Psim Q) (((A _ p).restrictAt sp 0).preT
            (seTwoKF (Proof := M.Response b) B rel (enc (fun i => B.pk (keys i))) dummyS (fun i =>
                B.pk (keys i)) Q)
            (σ _ p ω)) n')) x).2 = x.2 := fun n' x => by
        have ha := addsDrop_keeps ((A _ p).restrictAt sp 0) (simExtChallenger Psim Q)
          (seTwoKF (Proof := M.Response b) B rel (enc (fun i => B.pk (keys i))) dummyS (fun i =>
              B.pk (keys i)) Q) ω (P _ p)
          n' x
        have hp := ((A _ p).restrictAt sp 0).prePerms_keeps (simExtChallenger Psim Q)
          (seTwoKF (Proof := M.Response b) B rel (enc (fun i => B.pk (keys i))) dummyS (fun i =>
              B.pk (keys i)) Q) (σ _ p ω)
          (hσ _ p ω) n' (addsDrop (simExtChallenger Psim Q)
            (seTwoKF (Proof := M.Response b) B rel (enc (fun i => B.pk (keys i))) dummyS (fun i =>
                B.pk (keys i)) Q) ω (P _ p)
            (tab₀ ((A _ p).restrictAt sp 0)) n' x)
        exact ⟨(((A _ p).restrictAt sp 0).prePerms_logs (simExtChallenger Psim Q)
          (seTwoKF (Proof := M.Response b) B rel (enc (fun i => B.pk (keys i))) dummyS (fun i =>
              B.pk (keys i)) Q) (σ _ p ω)
          n' _).trans ha.1, hp.1.trans ha.2.1, hp.2.trans ha.2.2⟩
      exact kfDrops_corrupt_mem (rel := rel) (enc := enc) (dummyS := dummyS) keys Q
        (kq + Q * Psim.q) Psim
        ((A _ p).restrictAt sp 0) (kfExpansionAt sp Qs Aux A prf Psim Q _ p)
        (kfDefaultAt sp rel enc dummyS Aux A prf Psim Q _ p) _ hkeep _ (hβ keys p ω)
        ((A _ p).tracePreserving_restrictAt sp 0 (hTP _ p)) _ hv i hc

/-- **The key-free extraction runs as MU-EUF-NMA^corr**
(`kfExtAdds_le_muEufNmaProb` at the local queries of the restriction, `bridgeDropData`):
averaged over the users' key coins, the auxiliary input and a uniform base component `ω`, the
probability of an event `W` of the extraction run of the simulation-extraction adversary
`seAlgKF` for `(A pks p).restrictAt sp ω` is at most the success probability of `kfForger` in
MU-EUF-NMA^corr with `Q'` requests. Hypotheses: the adversaries are trace preserving (`hTP`); the
forger's bridge makes at most `t'` queries (`ht`) and at most `Q'` request points (`hQ`); `W` is
invariant under dropping and reinserting the table (`hW`); on every basis state of nonzero
amplitude of the bridge with the drops, at an output in `W`, the readout `g` verifies at the
oracle joined from `ω` and any second component (`hver`) under the key of a user whose corruption
the absorbed adversary did not log among its first `Q` requests (`hhon`). -/
theorem kfExt_le_muEufNmaProb
    (Aux : (Fin n → B.PK) → Type) (aux : ∀ pks, PMF (Aux pks))
    {shA : ∀ pks, Aux pks → AlgShape Xq Y (MUR ⊕ R) (MUResponse B.core ⊕ M.Response b)} (A : ∀ pks (aux : Aux pks), AdaptiveIAlg (shA pks aux) (Frg × X₀))
    (prf : Frg → Option M.NIProof)
    (Psim : NARG.Simulator Xq (XOut k e) (Stmt × (MUR ⊕ R)) (M.Response b) SC') (Q : ℕ)
    (kq : ℕ) (hTP : ∀ pks p, (A pks p).TracePreserving)
    (g : ∀ pks p, BaseGame.Tuple Xq (Out k e)
      (ExtReg ((A pks p).restrictAt sp 0) (simExtChallenger Psim Q) MUR (MUResponse B.core))
        (kq + Q * Psim.q) × DB Xq (Out k e) → B.PK × B.BMsg × B.BSig) (t' : ℕ)
    (ht : ∀ pks p, bT ((A pks p).restrictAt sp 0) (simExtChallenger Psim Q)
      (seTwoKF (Proof := M.Response b) B rel (enc pks) dummyS pks Q) (kq + Q * Psim.q) + 1 ≤ t')
    {Q' : ℕ} (hQ : ∀ pks p, bT ((A pks p).restrictAt sp 0) (simExtChallenger Psim Q)
      (seTwoKF (Proof := M.Response b) B rel (enc pks) dummyS pks Q) (kq + Q * Psim.q) + 1 ≤ Q')
    (W : ∀ (keys : Fin n → B.KeyCoins) (p : Aux fun i => B.pk (keys i)) (ω : Xq → Y₁),
      SPBCS.Reg (seAlgKF (rel := rel) (enc := enc (fun i => B.pk (keys i))) (dummyS := dummyS) prf
          keys Q
        ((A _ p).restrictAt sp ω)) Psim Q → DB Xq (Out k e) → Prop)
    (hW : ∀ keys p ω c D, W keys p ω (kfIns sp rel enc dummyS Aux A prf Psim Q keys p ω
      (dropTabCW ((A _ p).restrictAt sp ω) (simExtChallenger Psim Q)
        (seTwoKF (Proof := M.Response b) B rel (enc (B.pk ∘ keys)) dummyS (B.pk ∘ keys) Q)
        (fun _ => keyReplyNone B keys) c)) D ↔ W keys p ω c D)
    (hver : ∀ keys p ω (h : Xq → XOut k e) (c : Fin Q' → (SignOracle.none B.core).Coins) v,
      simState (outEquiv k e) ((kfDrop sp Qs rel enc dummyS Aux A prf Psim Q kq keys p ω).inst
        (muReplyAt sp (SignOracle.none B.core) ω keys Q' c)) v ≠ 0 →
      W keys p ω (kfIns sp rel enc dummyS Aux A prf Psim Q keys p ω
          ((kfDrop sp Qs rel enc dummyS Aux A prf Psim Q kq keys p ω).out v.1.1.1).out)
        (slotsDB (outEquiv k e) v.2) →
      B.bverify (join sp ω h)
        (g _ p ((kfDrop sp Qs rel enc dummyS Aux A prf Psim Q kq keys p ω).out v.1.1.1,
          slotsDB (outEquiv k e) v.2)).1
        (g _ p ((kfDrop sp Qs rel enc dummyS Aux A prf Psim Q kq keys p ω).out v.1.1.1,
          slotsDB (outEquiv k e) v.2)).2.1
        (g _ p ((kfDrop sp Qs rel enc dummyS Aux A prf Psim Q kq keys p ω).out v.1.1.1,
          slotsDB (outEquiv k e) v.2)).2.2 = true)
    (hhon : ∀ keys p ω (c : Fin Q' → (SignOracle.none B.core).Coins) v,
      simState (outEquiv k e) ((kfDrop sp Qs rel enc dummyS Aux A prf Psim Q kq keys p ω).inst
        (muReplyAt sp (SignOracle.none B.core) ω keys Q' c)) v ≠ 0 →
      W keys p ω (kfIns sp rel enc dummyS Aux A prf Psim Q keys p ω
          ((kfDrop sp Qs rel enc dummyS Aux A prf Psim Q kq keys p ω).out v.1.1.1).out)
        (slotsDB (outEquiv k e) v.2) →
      ∃ i, B.pk (keys i) =
          (g _ p ((kfDrop sp Qs rel enc dummyS Aux A prf Psim Q kq keys p ω).out v.1.1.1,
            slotsDB (outEquiv k e) v.2)).1 ∧
        (.inl (.corrupt i) : MUR ⊕ R) ∉ (Quantum.requests (extLogs
          ((kfDrop sp Qs rel enc dummyS Aux A prf Psim Q kq keys p ω).out v.1.1.1).out)).take Q) :
    ∑' keys, PMF.uniformOfFintype (Fin n → B.KeyCoins) keys *
      ∑' p, aux (fun i => B.pk (keys i)) p *
        ∑' ω, PMF.uniformOfFintype (Xq → Y₁) ω *
          simProb (outEquiv k e) (extAdv Qs (seAlgKF (rel := rel) (enc := enc (fun i => B.pk (keys
              i))) (dummyS := dummyS)
            prf keys Q ((A _ p).restrictAt sp ω)) Psim Q kq) (W keys p ω) ≤
      muEufNmaProb (kfForger sp Qs rel enc dummyS Aux aux A prf Psim Q kq g t' ht) Q' := by
  have h := kfExtAdds_le_muEufNmaProb sp Qs rel enc dummyS Aux aux A prf Psim Q kq hTP
    (fun pks p => ((A pks p).restrictBaseW sp).toAddsW)
    (fun pks p _ w => AdaptiveIAlg.stepOn_lastStep (A pks p) w.1)
    (fun pks p => bridgeDropData (outEquiv k e) ((A pks p).restrictAt sp 0)
      (simExtChallenger Psim Q) (seTwoKF (Proof := M.Response b) B rel (enc pks) dummyS pks Q)
      (.publicKey 0) (kfExpansionAt sp Qs Aux A prf Psim Q pks p) (kq + Q * Psim.q)
      (kfDefaultAt sp rel enc dummyS Aux A prf Psim Q pks p) ((A pks p).restrictBaseW sp))
    (fun pks p ω j => bridgeDropData_perm (outEquiv k e) ((A pks p).restrictAt sp 0)
      (simExtChallenger Psim Q) (seTwoKF (Proof := M.Response b) B rel (enc pks) dummyS pks Q)
      (.publicKey 0) (kfExpansionAt sp Qs Aux A prf Psim Q pks p) (kq + Q * Psim.q)
      (kfDefaultAt sp rel enc dummyS Aux A prf Psim Q pks p) ((A pks p).restrictBaseW sp) ω j)
    (fun keys p ω => ((A _ p).restrictAt sp ω).step)
    (fun keys p ω j => by
      rw [AdaptiveIAlg.BaseW.toStepAdds_perm]
      exact leftPerm_restrictAt_step sp ω (A _ p) j)
    (fun keys p ω => (A _ p).tracePreserving_restrictAt sp ω (hTP _ p)) g t'
    (fun pks p => (CoSimSchedule.slotQ_one _ le_rfl).le.trans (ht pks p)) hQ W hW hver hhon
  refine (le_of_eq ?_).trans (h.trans (le_of_eq rfl))
  refine tsum_congr fun keys => congrArg _ (tsum_congr fun p => congrArg _
    (tsum_congr fun ω => congrArg _ ?_))
  exact simProb_seAlgKF_restrictAt_eq_withStep sp Qs rel enc dummyS (A _ p) prf Psim Q kq keys ω
    (W keys p ω)

/-- **The restricted Kraus maps of the absorbed adversaries at the base component `ω`**: those of
`((A pks p).withStep (stω pks p ω)).restrictAt sp ω`. -/
noncomputable abbrev kfSideSt
    (Aux : (Fin n → B.PK) → Type)
    {shA : ∀ pks, Aux pks → AlgShape Xq Y (MUR ⊕ R) (MUResponse B.core ⊕ M.Response b)} (A : ∀ pks (aux : Aux pks), AdaptiveIAlg (shA pks aux) (Frg × X₀))
    (stω : ∀ pks (p : Aux pks), (Xq → Y₁) → StepIdx (A pks p).slots (A pks p).post →
      KrausMap (A pks p).R (DReg (A pks p).W (A pks p).width Xq Y (MUR ⊕ R)
        (MUResponse B.core ⊕ M.Response b)) (DReg (A pks p).W (A pks p).width Xq Y (MUR ⊕ R)
        (MUResponse B.core ⊕ M.Response b)))
    (keys : Fin n → B.KeyCoins) (p : Aux fun i => B.pk (keys i)) (ω : Xq → Y₁) :
    StepIdx ((A _ p).restrictAt sp 0).slots ((A _ p).restrictAt sp 0).post →
      KrausMap ((A _ p).restrictAt sp 0).R
        (DReg ((A _ p).restrictAt sp 0).W ((A _ p).restrictAt sp 0).width Xq (XOut k e)
          (MUR ⊕ R) (MUResponse B.core ⊕ M.Response b))
        (DReg ((A _ p).restrictAt sp 0).W ((A _ p).restrictAt sp 0).width Xq (XOut k e)
          (MUR ⊕ R) (MUResponse B.core ⊕ M.Response b)) :=
  (((A _ p).withStep (stω _ p ω)).restrictAt sp ω).step

/-- **The forger's additions for absorbed adversaries with side reads**: the local queries of the
restriction (`bridgeDropData`), then the side reads lifted to the starts of the query intervals
(`bridgePreData` of `SideSteps.splitAdds`). -/
noncomputable abbrev kfSidePb
    (Aux : (Fin n → B.PK) → Type)
    {shA : ∀ pks, Aux pks → AlgShape Xq Y (MUR ⊕ R) (MUResponse B.core ⊕ M.Response b)} (A : ∀ pks (aux : Aux pks), AdaptiveIAlg (shA pks aux) (Frg × X₀))
    (prf : Frg → Option M.NIProof)
    (Psim : NARG.Simulator Xq (XOut k e) (Stmt × (MUR ⊕ R)) (M.Response b) SC') (Q kq : ℕ)
    (stω : ∀ pks (p : Aux pks), (Xq → Y₁) → StepIdx (A pks p).slots (A pks p).post →
      KrausMap (A pks p).R (DReg (A pks p).W (A pks p).width Xq Y (MUR ⊕ R)
        (MUResponse B.core ⊕ M.Response b)) (DReg (A pks p).W (A pks p).width Xq Y (MUR ⊕ R)
        (MUResponse B.core ⊕ M.Response b)))
    (hside : ∀ pks p, (A pks p).SideSteps (stω pks p))
    (pks : Fin n → B.PK) (p : Aux pks) :=
  (bridgeDropData (outEquiv k e) ((A pks p).restrictAt sp 0) (simExtChallenger Psim Q)
    (seTwoKF (Proof := M.Response b) B rel (enc pks) dummyS pks Q) (.publicKey 0)
    (kfExpansionAt sp Qs Aux A prf Psim Q pks p) (kq + Q * Psim.q)
    (kfDefaultAt sp rel enc dummyS Aux A prf Psim Q pks p) ((A pks p).restrictBaseW sp)).append
  (bridgePreData (outEquiv k e) ((A pks p).restrictAt sp 0) (simExtChallenger Psim Q)
    (seTwoKF (Proof := M.Response b) B rel (enc pks) dummyS pks Q) (.publicKey 0)
    (kfExpansionAt sp Qs Aux A prf Psim Q pks p) (kq + Q * Psim.q)
    (kfDefaultAt sp rel enc dummyS Aux A prf Psim Q pks p) ((hside pks p).splitAdds sp))

omit [Nonempty TB.KeyCoins] in
/-- **The forger's query count for absorbed adversaries with side reads**: one per bridge step
for the restriction's local queries, and at most the number of side reads. -/
theorem slotQ_kfSidePb_le
    (Aux : (Fin n → B.PK) → Type)
    {shA : ∀ pks, Aux pks → AlgShape Xq Y (MUR ⊕ R) (MUResponse B.core ⊕ M.Response b)} (A : ∀ pks (aux : Aux pks), AdaptiveIAlg (shA pks aux) (Frg × X₀))
    (prf : Frg → Option M.NIProof)
    (Psim : NARG.Simulator Xq (XOut k e) (Stmt × (MUR ⊕ R)) (M.Response b) SC') (Q kq : ℕ)
    (stω : ∀ pks (p : Aux pks), (Xq → Y₁) → StepIdx (A pks p).slots (A pks p).post →
      KrausMap (A pks p).R (DReg (A pks p).W (A pks p).width Xq Y (MUR ⊕ R)
        (MUResponse B.core ⊕ M.Response b)) (DReg (A pks p).W (A pks p).width Xq Y (MUR ⊕ R)
        (MUResponse B.core ⊕ M.Response b)))
    (hside : ∀ pks p, (A pks p).SideSteps (stω pks p)) (pks : Fin n → B.PK) (p : Aux pks) :
    CoSimSchedule.slotQ (kfSidePb sp Qs rel enc dummyS Aux A prf Psim Q kq stω hside pks p).nb
        (bT ((A pks p).restrictAt sp 0) (simExtChallenger Psim Q)
          (seTwoKF (Proof := M.Response b) B rel (enc pks) dummyS pks Q) (kq + Q * Psim.q) + 1) ≤
      bT ((A pks p).restrictAt sp 0) (simExtChallenger Psim Q)
          (seTwoKF (Proof := M.Response b) B rel (enc pks) dummyS pks Q) (kq + Q * Psim.q) + 1 +
        ∑ j, (hside pks p).S.nb j := by
  rw [show (kfSidePb sp Qs rel enc dummyS Aux A prf Psim Q kq stω hside pks p).nb =
      fun j => 1 + (bridgePreData (outEquiv k e) ((A pks p).restrictAt sp 0)
        (simExtChallenger Psim Q) (seTwoKF (Proof := M.Response b) B rel (enc pks) dummyS pks Q)
        (.publicKey 0) (kfExpansionAt sp Qs Aux A prf Psim Q pks p) (kq + Q * Psim.q)
        (kfDefaultAt sp rel enc dummyS Aux A prf Psim Q pks p)
        ((hside pks p).splitAdds sp)).nb j from rfl,
    CoSimSchedule.slotQ_add, CoSimSchedule.slotQ_one _ le_rfl]
  exact Nat.add_le_add_left (slotQ_bridgePreData_le (outEquiv k e) ((A pks p).restrictAt sp 0)
    (simExtChallenger Psim Q) (seTwoKF (Proof := M.Response b) B rel (enc pks) dummyS pks Q)
    (.publicKey 0) (kfExpansionAt sp Qs Aux A prf Psim Q pks p) (kq + Q * Psim.q)
    (kfDefaultAt sp rel enc dummyS Aux A prf Psim Q pks p) ((hside pks p).splitAdds sp)) _

/-- **The bridge read after the forger's additions for absorbed adversaries with side reads**
(`kfDropPb` at `kfSidePb`). -/
noncomputable abbrev kfSideDrop
    (Aux : (Fin n → B.PK) → Type)
    {shA : ∀ pks, Aux pks → AlgShape Xq Y (MUR ⊕ R) (MUResponse B.core ⊕ M.Response b)} (A : ∀ pks (aux : Aux pks), AdaptiveIAlg (shA pks aux) (Frg × X₀))
    (prf : Frg → Option M.NIProof)
    (Psim : NARG.Simulator Xq (XOut k e) (Stmt × (MUR ⊕ R)) (M.Response b) SC') (Q kq : ℕ)
    (stω : ∀ pks (p : Aux pks), (Xq → Y₁) → StepIdx (A pks p).slots (A pks p).post →
      KrausMap (A pks p).R (DReg (A pks p).W (A pks p).width Xq Y (MUR ⊕ R)
        (MUResponse B.core ⊕ M.Response b)) (DReg (A pks p).W (A pks p).width Xq Y (MUR ⊕ R)
        (MUResponse B.core ⊕ M.Response b)))
    (hside : ∀ pks p, (A pks p).SideSteps (stω pks p))
    (keys : Fin n → B.KeyCoins) (p : Aux fun i => B.pk (keys i)) (ω : Xq → Y₁) :=
  kfDropPb sp Qs rel enc dummyS Aux A prf Psim Q kq
    (kfSidePb sp Qs rel enc dummyS Aux A prf Psim Q kq stω hside) keys p ω

/-- **The key-free extraction runs of absorbed adversaries with side reads as
MU-EUF-NMA^corr** (`kfExtPre_le_muEufNmaProb` at the side reads before the Kraus maps and the
restriction's local queries after them, `kfSidePb`): for base adversaries `A pks p` whose Kraus maps
at the base component `ω` are `stω pks p ω`, `A`'s read after side reads on the registers
(`AdaptiveIAlg.SideSteps`, `hside`), averaged over the users' key coins, the auxiliary input and a
uniform base component `ω`, the probability of an event `W` of the extraction run of `seAlgKF` for
`((A pks p).withStep (stω pks p ω)).restrictAt sp ω` (written as `A.restrictAt sp 0` with its
Kraus maps, `AdaptiveIAlg.withStep_restrictAt_eq`) is at most the success probability of
`kfForgerAdds` at `kfSidePb` in MU-EUF-NMA^corr with `Q'` requests. The forger makes `bT + 1`
queries for the restriction's local queries and at most one per side read (`ht`,
`slotQ_kfSidePb_le`). The other hypotheses are those of `kfExt_le_muEufNmaProb`, at the bridge read
after `kfSidePb` (`kfDropPb`). -/
theorem kfExtSide_le_muEufNmaProb
    (Aux : (Fin n → B.PK) → Type) (aux : ∀ pks, PMF (Aux pks))
    {shA : ∀ pks, Aux pks → AlgShape Xq Y (MUR ⊕ R) (MUResponse B.core ⊕ M.Response b)} (A : ∀ pks (aux : Aux pks), AdaptiveIAlg (shA pks aux) (Frg × X₀))
    (prf : Frg → Option M.NIProof)
    (Psim : NARG.Simulator Xq (XOut k e) (Stmt × (MUR ⊕ R)) (M.Response b) SC') (Q : ℕ)
    (kq : ℕ) (hTP : ∀ pks p, (A pks p).TracePreserving)
    (stω : ∀ pks (p : Aux pks), (Xq → Y₁) → StepIdx (A pks p).slots (A pks p).post →
      KrausMap (A pks p).R (DReg (A pks p).W (A pks p).width Xq Y (MUR ⊕ R)
        (MUResponse B.core ⊕ M.Response b)) (DReg (A pks p).W (A pks p).width Xq Y (MUR ⊕ R)
        (MUResponse B.core ⊕ M.Response b)))
    (hside : ∀ pks p, (A pks p).SideSteps (stω pks p))
    (g : ∀ pks p, BaseGame.Tuple Xq (Out k e)
      (ExtReg ((A pks p).restrictAt sp 0) (simExtChallenger Psim Q) MUR (MUResponse B.core))
        (kq + Q * Psim.q) × DB Xq (Out k e) → B.PK × B.BMsg × B.BSig) (t' : ℕ)
    (ht : ∀ pks p, bT ((A pks p).restrictAt sp 0) (simExtChallenger Psim Q)
      (seTwoKF (Proof := M.Response b) B rel (enc pks) dummyS pks Q) (kq + Q * Psim.q) + 1 +
        ∑ j, (hside pks p).S.nb j ≤ t')
    {Q' : ℕ} (hQ : ∀ pks p, bT ((A pks p).restrictAt sp 0) (simExtChallenger Psim Q)
      (seTwoKF (Proof := M.Response b) B rel (enc pks) dummyS pks Q) (kq + Q * Psim.q) + 1 ≤ Q')
    (W : ∀ (keys : Fin n → B.KeyCoins) (p : Aux fun i => B.pk (keys i)) (ω : Xq → Y₁),
      SPBCS.Reg (seAlgKF (rel := rel) (enc := enc (fun i => B.pk (keys i))) (dummyS := dummyS) prf
          keys Q
        (kfStepAdv sp Aux A (kfSideSt sp Aux A stω) keys p ω)) Psim Q → DB Xq (Out k e) → Prop)
    (hW : ∀ keys p ω c D, W keys p ω (kfInsAdds sp rel enc dummyS Aux A prf Psim Q (kfSideSt sp
      Aux A stω) keys p ω
      (dropTabCW (kfStepAdv sp Aux A (kfSideSt sp Aux A stω) keys p ω) (simExtChallenger Psim Q)
        (seTwoKF (Proof := M.Response b) B rel (enc (B.pk ∘ keys)) dummyS (B.pk ∘ keys) Q)
        (fun _ => keyReplyNone B keys) c)) D ↔ W keys p ω c D)
    (hver : ∀ keys p ω (h : Xq → XOut k e) (c : Fin Q' → (SignOracle.none B.core).Coins) v,
      simState (outEquiv k e) ((kfSideDrop sp Qs rel enc dummyS Aux A prf Psim Q kq stω hside keys p
        ω).inst (muReplyAt sp (SignOracle.none B.core) ω keys Q' c)) v ≠ 0 →
      W keys p ω (kfInsAdds sp rel enc dummyS Aux A prf Psim Q (kfSideSt sp Aux A stω) keys p ω
          ((kfSideDrop sp Qs rel enc dummyS Aux A prf Psim Q kq stω hside keys p ω).out
            v.1.1.1).out)
        (slotsDB (outEquiv k e) v.2) →
      B.bverify (join sp ω h)
        (g _ p ((kfSideDrop sp Qs rel enc dummyS Aux A prf Psim Q kq stω hside keys p ω).out
          v.1.1.1, slotsDB (outEquiv k e) v.2)).1
        (g _ p ((kfSideDrop sp Qs rel enc dummyS Aux A prf Psim Q kq stω hside keys p ω).out
          v.1.1.1, slotsDB (outEquiv k e) v.2)).2.1
        (g _ p ((kfSideDrop sp Qs rel enc dummyS Aux A prf Psim Q kq stω hside keys p ω).out
          v.1.1.1, slotsDB (outEquiv k e) v.2)).2.2 = true)
    (hhon : ∀ keys p ω (c : Fin Q' → (SignOracle.none B.core).Coins) v,
      simState (outEquiv k e) ((kfSideDrop sp Qs rel enc dummyS Aux A prf Psim Q kq stω hside keys p
        ω).inst (muReplyAt sp (SignOracle.none B.core) ω keys Q' c)) v ≠ 0 →
      W keys p ω (kfInsAdds sp rel enc dummyS Aux A prf Psim Q (kfSideSt sp Aux A stω) keys p ω
          ((kfSideDrop sp Qs rel enc dummyS Aux A prf Psim Q kq stω hside keys p ω).out
            v.1.1.1).out)
        (slotsDB (outEquiv k e) v.2) →
      ∃ i, B.pk (keys i) = (g _ p ((kfSideDrop sp Qs rel enc dummyS Aux A prf Psim Q kq stω hside
        keys p ω).out v.1.1.1, slotsDB (outEquiv k e) v.2)).1 ∧
        (.inl (.corrupt i) : MUR ⊕ R) ∉ (Quantum.requests (extLogs
          ((kfSideDrop sp Qs rel enc dummyS Aux A prf Psim Q kq stω hside keys p ω).out
            v.1.1.1).out)).take Q) :
    ∑' keys, PMF.uniformOfFintype (Fin n → B.KeyCoins) keys *
      ∑' p, aux (fun i => B.pk (keys i)) p *
        ∑' ω, PMF.uniformOfFintype (Xq → Y₁) ω *
          simProb (outEquiv k e) (extAdv Qs (seAlgKF (rel := rel) (enc := enc (fun i => B.pk (keys
              i))) (dummyS := dummyS)
            prf keys Q (kfStepAdv sp Aux A (kfSideSt sp Aux A stω) keys p ω)) Psim Q kq) (W keys p
              ω) ≤
      muEufNmaProb (kfForgerAdds sp Qs rel enc dummyS Aux aux A prf Psim Q kq g
        (kfSidePb sp Qs rel enc dummyS Aux A prf Psim Q kq stω hside) t' fun pks p =>
          (slotQ_kfSidePb_le sp Qs rel enc dummyS Aux A prf Psim Q kq stω hside pks p).trans
            (ht pks p)) Q'
:=
  kfExtPre_le_muEufNmaProb sp Qs rel enc dummyS Aux aux A prf Psim Q kq hTP
    (fun pks p => ((A pks p).restrictBaseW sp).toAddsW)
    (fun pks p _ w => AdaptiveIAlg.stepOn_lastStep (A pks p) w.1)
    (kfSidePb sp Qs rel enc dummyS Aux A prf Psim Q kq stω hside)
    (fun pks p ω j => (splitReg sp (A pks p).W (A pks p).width Xq (MUR ⊕ R)
      (MUResponse B.core ⊕ M.Response b)).symm.permCongr ((hside pks p).S.perm ω j))
    (fun pks p ω j x => by
      have h := (hside pks p).keeps_pairs ω j (splitReg sp (A pks p).W (A pks p).width Xq
        (MUR ⊕ R) (MUResponse B.core ⊕ M.Response b) x)
      change (fun i => ((((hside pks p).S.perm ω j (splitReg sp (A pks p).W (A pks p).width Xq
        (MUR ⊕ R) (MUResponse B.core ⊕ M.Response b) x)).2 i).1, (sp (((hside pks p).S.perm ω j
          (splitReg sp (A pks p).W (A pks p).width Xq (MUR ⊕ R) (MUResponse B.core ⊕ M.Response b)
            x)).2 i).2).2)) = x.2
      rw [h]
      funext i
      simp [splitReg])
    (fun pks p ω j => bridgePreData_restrict_perm (e := outEquiv k e) (d₂ := .publicKey 0)
      (kq := kq + Q * Psim.q) sp (hside pks p) (simExtChallenger Psim Q)
      (seTwoKF (Proof := M.Response b) B rel (enc pks) dummyS pks Q)
      (kfExpansionAt sp Qs Aux A prf Psim Q pks p)
      (kfDefaultAt sp rel enc dummyS Aux A prf Psim Q pks p) ((A pks p).restrictBaseW sp).toAddsW
      _ (fun ω' n' => bridgeDropData_perm (outEquiv k e) ((A pks p).restrictAt sp 0)
        (simExtChallenger Psim Q) (seTwoKF (Proof := M.Response b) B rel (enc pks) dummyS pks Q)
        (.publicKey 0) (kfExpansionAt sp Qs Aux A prf Psim Q pks p) (kq + Q * Psim.q)
        (kfDefaultAt sp rel enc dummyS Aux A prf Psim Q pks p) ((A pks p).restrictBaseW sp) ω' n')
      ω j)
    (fun pks p ω => (((A pks p).withStep (stω pks p ω)).restrictAt sp 0).step)
    (fun pks p ω j => AdaptiveIAlg.rightPerm_restrictAt_withStep sp (A pks p) 0 (stω pks p ω) j
      ((hside pks p).rightPerm ω j))
    (fun pks p ω => ((A pks p).withStep (stω pks p ω)).tracePreserving_restrictAt sp 0
      ((hside pks p).tracePreserving ω))
    (kfSideSt sp Aux A stω)
    (fun keys p ω j => by
      rw [AdaptiveIAlg.BaseW.toStepAdds_perm]
      exact leftPerm_restrictAt_step sp ω ((A _ p).withStep (stω _ p ω)) j)
    (fun keys p ω => ((A _ p).withStep (stω _ p ω)).tracePreserving_restrictAt sp ω
      ((hside _ p).tracePreserving ω))
    g t' _ hQ W hW hver hhon

/-! ### The absorbed adversaries of the key-free chain -/

omit [Nonempty Y₁] [NeZero n] [∀ j i, Nonempty ((P j).Challenge i)] [Inhabited M.NIProof] in
/-- **Restricting and reading the output commute** (the order of the key-free chain against that
of `kfAbsAdv`): the algorithm of the restricted `t`-query adversary with its output read through
`f`, at an auxiliary value, is the restriction of the algorithm of the adversary with its output
read through `f`. -/
theorem restrictAt_mapOut_alg {Rq Rs O O' : Type} [Fintype Rq] [DecidableEq Rq] [Fintype Rs]
    [DecidableEq Rs] {t : ℕ} (𝒜 : QueryBoundedAdversary Xq Y Rq Rs O t) (f : O → O')
    (ω : Xq → Y₁) (a : 𝒜.Aux) :
    ((𝒜.restrictAt sp ω).mapOut f).alg a = ((𝒜.mapOut f).alg a).restrictAt sp ω :=
  rfl

omit [Nonempty Y₁] [NeZero n] [∀ j i, Nonempty ((P j).Challenge i)] [Inhabited M.NIProof] in
/-- **Reading the output and restricting commute** for one algorithm. -/
theorem mapOut_restrictAt_eq {Rq Rs O O' : Type} [Fintype Rq] [DecidableEq Rq] [Fintype Rs]
    [DecidableEq Rs] {shA₀ : AlgShape Xq Y Rq Rs} (A₀ : AdaptiveIAlg shA₀ O) (f : O → O') (ω : Xq → Y₁) :
    (A₀.mapOut f).restrictAt sp ω = (A₀.restrictAt sp ω).mapOut f :=
  rfl

/-- **The auxiliary input of the absorbed adversaries**: an auxiliary input of the absorbed
adversary (`QueryBoundedAdversary.absorbAssign`, the adversary's with the unit side coin) and the
key-free side coins `sc`. -/
abbrev kfAbsAux {Rq Rs : Type} [Fintype Rq] [DecidableEq Rq] [Fintype Rs]
    [DecidableEq Rs] {t : ℕ} (𝒜 : QueryBoundedAdversary Xq Y Rq Rs (Frg × X₀) t)
    (SC : Type) (Q : ℕ) : Type :=
  (𝒜.Aux × Unit) × (Fin Q → SC)

/-- **The absorbed adversary's auxiliary input** in an auxiliary input of the absorbed
adversaries.

Statements read it through this name, not as `p.1`: the projection elaborates at the unfolded
`kfAbsAux`, whose body spells the `Nonempty` instance of the queries as an abstracted proof, and
comparing that spelling with a statement's runs through the absorbed shapes. -/
def kfAbsAux.fst {Rq Rs : Type} [Fintype Rq] [DecidableEq Rq] [Fintype Rs] [DecidableEq Rs]
    {t : ℕ} {𝒜 : QueryBoundedAdversary Xq Y Rq Rs (Frg × X₀) t} {SC : Type} {Q : ℕ}
    (p : kfAbsAux 𝒜 SC Q) : 𝒜.Aux × Unit :=
  p.1

/-- **The side coins** in an auxiliary input of the absorbed adversaries (read through this name,
as `kfAbsAux.fst`). -/
def kfAbsAux.coins {Rq Rs : Type} [Fintype Rq] [DecidableEq Rq] [Fintype Rs] [DecidableEq Rs]
    {t : ℕ} {𝒜 : QueryBoundedAdversary Xq Y Rq Rs (Frg × X₀) t} {SC : Type} {Q : ℕ}
    (p : kfAbsAux 𝒜 SC Q) : Fin Q → SC :=
  p.2

/-- **The law of the auxiliary input of the absorbed adversaries**: the absorbed adversary's
auxiliary input and, independently, the side coins drawn from `scLaw`. -/
noncomputable def kfAbsAuxLaw {Rq Rs : Type} [Fintype Rq] [DecidableEq Rq] [Fintype Rs]
    [DecidableEq Rs] {t : ℕ}
    (𝒜 : QueryBoundedAdversary Xq Y Rq Rs (Frg × X₀) t) {SC : Type} {Q : ℕ}
    (scLaw : PMF (Fin Q → SC)) : PMF (kfAbsAux 𝒜 SC Q) :=
  (𝒜.aux.bind fun a => (PMF.pure ()).map fun s => (a, s)).bind fun a => scLaw.map (Prod.mk a)

/-- **An average over the auxiliary input of the absorbed adversaries** is the average over the
side coins and the absorbed adversary's auxiliary input. -/
theorem tsum_kfAbsAuxLaw_mul {Rq Rs : Type} [Fintype Rq] [DecidableEq Rq] [Fintype Rs]
    [DecidableEq Rs] {t : ℕ}
    (𝒜 : QueryBoundedAdversary Xq Y Rq Rs (Frg × X₀) t) {SC : Type} {Q : ℕ}
    (scLaw : PMF (Fin Q → SC)) (f : kfAbsAux 𝒜 SC Q → ℝ≥0∞) :
    ∑' p, kfAbsAuxLaw 𝒜 scLaw p * f p =
      ∑' sc, scLaw sc * ∑' a, (𝒜.aux.bind fun a => (PMF.pure ()).map fun s => (a, s)) a *
        f (a, sc) := by
  rw [ENNReal.tsum_prod', ENNReal.tsum_comm]
  refine tsum_congr fun sc => ?_
  rw [← ENNReal.tsum_mul_left]
  refine tsum_congr fun a => ?_
  rw [kfAbsAuxLaw, PMF.bind_map_prodMk_apply]
  ring

/-- **An average over the side coins, a base component and the absorbed adversary's auxiliary
input is an average over the auxiliary input of the absorbed adversaries** (`kfAbsAuxLaw`), read
through `kfAbsAux.fst` and `kfAbsAux.coins`. -/
theorem tsum_kfAbsAuxLaw_avg {Rq Rs Ω : Type} [Fintype Rq] [DecidableEq Rq] [Fintype Rs]
    [DecidableEq Rs] {t : ℕ}
    (𝒜 : QueryBoundedAdversary Xq Y Rq Rs (Frg × X₀) t) {SC : Type} {Q : ℕ}
    (scLaw : PMF (Fin Q → SC)) (ν : Ω → ℝ≥0∞) (F : 𝒜.Aux × Unit → (Fin Q → SC) → Ω → ℝ≥0∞) :
    ∑' sc, scLaw sc * ∑' ω, ν ω *
        ∑' a, (𝒜.aux.bind fun a => (PMF.pure ()).map fun s => (a, s)) a * F a sc ω =
      ∑' p, kfAbsAuxLaw 𝒜 scLaw p * ∑' ω, ν ω * F (kfAbsAux.fst p) (kfAbsAux.coins p) ω := by
  rw [tsum_kfAbsAuxLaw_mul]
  refine tsum_congr fun sc => congrArg _ ?_
  simp only [← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun a => tsum_congr fun ω => ?_
  change _ = _ * (ν ω * F a sc ω)
  ring

/-- **The absorbed adversaries of the key-free chain**: at the public keys `pks` and the
auxiliary input `(a, sc)`, the adversary `𝒜` with the assigning relay `G pks sc` absorbed
(`QueryBoundedAdversary.absorbAssign`, with the unit side coin) at `a`, its output's table of
assignments dropped. -/
noncomputable abbrev kfAbsAdv {Rq Rs : Type} [Fintype Rq] [DecidableEq Rq] [Fintype Rs]
    [DecidableEq Rs] [Inhabited Rq] {t : ℕ} (𝒜 : QueryBoundedAdversary Xq Y Rq Rs (Frg × X₀) t)
    {SC : Type} {Q : ℕ}
    (G : (Fin n → B.PK) → (Fin Q → SC) →
      AssignRelay Xq Y Rq Rs (MUR ⊕ R) (MUResponse B.core ⊕ M.Response b))
    (qG : ℕ) (hG : ∀ pks sc, (G pks sc).qG ≤ qG) (pks : Fin n → B.PK) (p : kfAbsAux 𝒜 SC Q) :=
  ((𝒜.absorbAssign (PMF.pure ()) (fun _ => G pks p.2) qG (fun _ => hG pks p.2)
    0 (AssignRelay.qP_le_zero _) Q).mapOut
    Prod.fst).alg p.1

omit [NeZero n] [∀ j i, Nonempty ((P j).Challenge i)] [Inhabited M.NIProof] [Nonempty TB.KeyCoins]
  in
/-- **The absorbed adversaries are trace preserving.** -/
theorem tracePreserving_kfAbsAdv {Rq Rs : Type} [Fintype Rq] [DecidableEq Rq] [Fintype Rs]
    [DecidableEq Rs] [Inhabited Rq] {t : ℕ} (𝒜 : QueryBoundedAdversary Xq Y Rq Rs (Frg × X₀) t)
    {SC : Type} {Q : ℕ}
    (G : (Fin n → B.PK) → (Fin Q → SC) →
      AssignRelay Xq Y Rq Rs (MUR ⊕ R) (MUResponse B.core ⊕ M.Response b))
    (qG : ℕ) (hG : ∀ pks sc, (G pks sc).qG ≤ qG) (pks : Fin n → B.PK) (p : kfAbsAux 𝒜 SC Q) :
    (kfAbsAdv 𝒜 G qG hG pks p).TracePreserving :=
  ((𝒜.absorbAssign (PMF.pure ()) (fun _ => G pks p.2) qG (fun _ => hG pks p.2)
    0 (AssignRelay.qP_le_zero _) Q).mapOut
    Prod.fst).tracePreserving p.1

end Forger

end RingSignature.KeyFree

end GordieHowe
