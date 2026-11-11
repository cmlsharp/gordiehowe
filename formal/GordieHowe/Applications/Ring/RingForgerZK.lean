-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Ring.RingInsider
public import GordieHowe.Applications.Ring.RingForgerMUBound
public import GordieHowe.Model.Signature.MultiUserTableForger

@[expose] public section

/-!
# The zero-knowledge route's forger as a multi-user forger

The success probability of the forger of the zero-knowledge route (`zkForgerTerm`,
`zkForgerSuccess`, `GordieHowe/Applications/Ring/RingInsider.lean`) bounded by the success
probability in MU-EUF-CMA^corr of an explicit multi-user forger (`zkForger`), by the bridge
statement (`Quantum.extBridge`). The simulation-extraction adversary `seAlg` is the
adversary absorbed with the table of the users' key coins through `seTwo`, its output read as a
claim; its extraction run (`SPBCS.extAdv`) is the extraction run of the table form
(`Quantum.extRun`) of the adversary at that table, with the expansion and the default read at the
empty table, so that only the table holds key coins; the multi-user forger runs the
compressed-oracle simulation of its bridge (`Signature.tableForger`), the corruptions among the
adversary's first `Q` requests asked of the multi-user challenger.

- `Quantum.AdaptiveIAlg.simProb_expandAdv_composeBothOut_mapOut`,
  `Quantum.AdaptiveIAlg.simProb_expandAdv_mapOut_cross`, `Quantum.AdaptiveIAlg.insertTabM`,
  `Quantum.AdaptiveIAlg.dropTabM`, `SPBCS.simExtractionExpansion_mapOut_next_congr`: the crossing
  from the registers of an adversary with its output read through a map to the adversary's.
- `Quantum.AdaptiveIAlg.choice_comp_congr`, `Quantum.AdaptiveIAlg.dropTabM_defaultOut_congr`,
  `SPBCS.simExtractionExpansion_absorbTab_next_congr`: the default output and the extraction
  expansion of the table form do not depend on the table.
- `RingSignature.Insider.simProb_extAdv_seAlg_eq`: one term of `zkForgerSuccess` as an extraction
  run of the table form.
- `seAlgQ`, `forgerWinsQ`, `zkExp`, `zkDefault`, `simProb_extAdv_seAlg_eq_zk`: the objects at any
  adversary, and the term with the expansion and the default at the empty table.
- `zk_bridge_requests`: every multi-user request of the forger is `publicKey 0` or a corruption
  among the adversary's first `Q` requests.
- `ZKCand`, `zkCands`, `zkCandTest`, `zkReadout`, `zkCand_of_forgerWinsQ`, `forgesReq_zkReadout`:
  the forger's readout (the first extracted candidate passing a decided test) and its win.
- `zkAux`, `zkForger`, `zkSum`, `sum_simProb_extAdv_le_muEufProb`: the multi-user forger and the
  bound on the averaged win.
- `zkPsim`, `zkQ'`, `zkForgerTerm_le_muEufProb`: `zkForgerTerm` bounded by
  `muEufProb zkForger` with `zkQ'` requests from a schedule bound.
- `insiderForgeProb_le_zk_muEufProb`: `insiderForgeProb_le_zk` with the multi-user forger;
  `insiderForgeProb_le_zk_muEufProb_spbcs` at the identity reading (`spbcsProofSystem`);
  `insiderForgeProb_le_zk_muEufProb_refuseAt`, `insiderForgeProb_le_zk_muEufProb_refuseAvg`: the same
  for a base signer whose refusals are bounded per key or on average over the key coins.
-/

namespace GordieHowe

open Quantum QROM SPBCS IOP
open scoped ENNReal

namespace Quantum.AdaptiveIAlg

variable {m k e : ℕ} {Req Resp O O' : Type} [Fintype Req] [DecidableEq Req] [Fintype Resp]
  [DecidableEq Resp]

/-- **The extraction run of an adversary with its output read through a map** is that of the
adversary (`composeBothOut_mapOut_tp`: the trace-preserving composition does not read the
output). -/
theorem simProb_expandAdv_composeBothOut_mapOut
    {shA : AlgShape (Bits m) (XOut k e) Req Resp} (A : AdaptiveIAlg shA O) (f : O → O')
    (C : Challenger (Bits m) (XOut k e) Req Resp)
    (Ex : Expansion (Bits m) (Out k e) ((A.mapOut f).toTPKindAlg.CW C)) (kq : ℕ)
    (d : (A.mapOut f).toTPKindAlg.CW C)
    (W : (A.mapOut f).toTPKindAlg.CW C → DB (Bits m) (Out k e) → Prop) :
    simProb (outEquiv k e) (expandAdv (outEquiv k e) Ex kq
        ((((A.mapOut f).toTPKindAlg.composeBothOut C id).toQueryAlgCoh).mapOut (·.getD d))) W =
      simProb (outEquiv k e) (expandAdv (outEquiv k e) Ex kq
        (((A.toTPKindAlg.composeBothOut C id).toQueryAlgCoh).mapOut (·.getD d))) W := by
  rw [composeBothOut_mapOut_tp]

/-- **The extraction run of an adversary with its output read through a map, crossed to the
adversary's registers**: for an expansion `Ex` and an event `W` of the registers of `A.mapOut f`,
a map `drop` of `A`'s registers and a reinsertion `insM` back into those of `A.mapOut f` under
which `Ex` and `W` are invariant (`hEx`, `hW`), and `g o = drop (o.getD d)`, the probability of
`W` is that of `W ∘ insM` of `A`'s run read through `g` and expanded by `Ex ∘ insM`. -/
theorem simProb_expandAdv_mapOut_cross {shA : AlgShape (Bits m) (XOut k e) Req Resp} (A : AdaptiveIAlg shA O)
    (f : O → O') (C : Challenger (Bits m) (XOut k e) Req Resp)
    (Ex : Expansion (Bits m) (Out k e) ((A.mapOut f).toTPKindAlg.CW C)) (kq : ℕ)
    (d : (A.mapOut f).toTPKindAlg.CW C)
    (W : (A.mapOut f).toTPKindAlg.CW C → DB (Bits m) (Out k e) → Prop) {R : Type}
    (drop : A.toTPKindAlg.CW C → R) (insM : R → (A.mapOut f).toTPKindAlg.CW C)
    (g : Option (A.toTPKindAlg.CW C) → R) (hg : ∀ o, g o = drop (o.getD d))
    (hEx : ∀ c : A.toTPKindAlg.CW C, Ex.next (insM (drop c)) = Ex.next c)
    (hW : ∀ (c : A.toTPKindAlg.CW C) D, W (insM (drop c)) D ↔ W c D) :
    simProb (outEquiv k e) (expandAdv (outEquiv k e) Ex kq
        ((((A.mapOut f).toTPKindAlg.composeBothOut C id).toQueryAlgCoh).mapOut (·.getD d))) W =
      simProb (outEquiv k e) (expandAdv (outEquiv k e) ⟨fun r => Ex.next (insM r)⟩ kq
        (((A.toTPKindAlg.composeBothOut C id).toQueryAlgCoh).mapOut g))
        (fun r D => W (insM r) D) := by
  rw [simProb_expandAdv_composeBothOut_mapOut]
  exact simProb_expandAdv_mapOut_ins _ drop insM d g hg Ex hEx kq W hW

section Insert

variable {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  {Req₁ Resp₁ Req₂ Resp₂ : Type} [Fintype Req₁] [DecidableEq Req₁] [Fintype Resp₁]
  [DecidableEq Resp₁] [Fintype Req₂] [DecidableEq Req₂] [Fintype Resp₂] [DecidableEq Resp₂]
  [Inhabited Req₁]

/-- **The composed registers of the adversary absorbed with a table, its output read through a
map**, from the table-free registers: the table register set to `tab` (`insertTab` at the
registers of `(A₀.absorbTab F tab).mapOut f`). -/
def insertTabM {shA₀ : AlgShape (Bits m) (XOut k e) Req Resp} (A₀ : AdaptiveIAlg shA₀ O)
    (C₁ : Challenger (Bits m) (XOut k e) Req₁ Resp₁)
    (F : TwoRelay Req Resp Req₁ Resp₁ Req₂ Resp₂) (tab : A₀.OuterTab Req₂ Resp₂) (f : O → O')
    (c : ExtReg A₀ C₁ Req₂ Resp₂) : ((A₀.absorbTab F tab).mapOut f).toTPKindAlg.CW C₁ :=
  ⟨((((c.adv.1.1.1, tab), c.adv.1.1.2), c.adv.1.2), c.adv.2), c.chal⟩

/-- **The table-free registers of the adversary absorbed with a table, its output read through a
map** (`dropTabCW` at the registers of `(A₀.absorbTab F tab).mapOut f`). -/
def dropTabM {shA₀ : AlgShape (Bits m) (XOut k e) Req Resp} (A₀ : AdaptiveIAlg shA₀ O)
    (C₁ : Challenger (Bits m) (XOut k e) Req₁ Resp₁)
    (F : TwoRelay Req Resp Req₁ Resp₁ Req₂ Resp₂) (tab : A₀.OuterTab Req₂ Resp₂) (f : O → O')
    (v : ((A₀.absorbTab F tab).mapOut f).toTPKindAlg.CW C₁) : ExtReg A₀ C₁ Req₂ Resp₂ :=
  ⟨(((v.adv.1.1.1.1, v.adv.1.1.2), v.adv.1.2), v.adv.2), v.chal⟩

/-- **A function of a chosen element, across equal types**: for `h : α = β`, functions `φ` and
`ψ` agreeing along the cast give the same value at the chosen elements. -/
theorem choice_comp_congr {α β Z : Type} (h : α = β) (hα : Nonempty α) (hβ : Nonempty β)
    (φ : α → Z) (ψ : β → Z) (hφ : ∀ a, φ a = ψ (cast h a)) :
    φ (Classical.choice hα) = ψ (Classical.choice hβ) := by
  subst h
  exact hφ _

/-- **The default output of the extraction run with the table dropped does not depend on the
table.** -/
theorem dropTabM_defaultOut_congr {shA₀ : AlgShape (Bits m) (XOut k e) Req Resp} (A₀ : AdaptiveIAlg shA₀ O)
    (C₁ : Challenger (Bits m) (XOut k e) Req₁ Resp₁)
    (F : TwoRelay Req Resp Req₁ Resp₁ Req₂ Resp₂) (tab tab' : A₀.OuterTab Req₂ Resp₂)
    (f : O → O') :
    dropTabM A₀ C₁ F tab f
        ((((A₀.absorbTab F tab).mapOut f).toTPKindAlg.composeBothOut C₁ id).defaultOut) =
      dropTabM A₀ C₁ F tab' f
        ((((A₀.absorbTab F tab').mapOut f).toTPKindAlg.composeBothOut C₁ id).defaultOut) := by
  show dropTabM A₀ C₁ F tab f
      ((((A₀.absorbTab F tab).mapOut f).toTPKindAlg.composeBothOut C₁ id).out
        (Classical.choice (((A₀.absorbTab F tab).mapOut f).toTPKindAlg.composeBothOut C₁
          id).init.nonempty).1) =
    dropTabM A₀ C₁ F tab' f
      ((((A₀.absorbTab F tab').mapOut f).toTPKindAlg.composeBothOut C₁ id).out
        (Classical.choice (((A₀.absorbTab F tab').mapOut f).toTPKindAlg.composeBothOut C₁
          id).init.nonempty).1)
  exact choice_comp_congr
    (α := QueryReg (((A₀.absorbTab F tab).mapOut f).toTPKindAlg.composeBothOut C₁ id).V 1
      (Bits m) (XOut k e))
    (β := QueryReg (((A₀.absorbTab F tab').mapOut f).toTPKindAlg.composeBothOut C₁ id).V 1
      (Bits m) (XOut k e)) rfl _ _
    (fun a => dropTabM A₀ C₁ F tab f
      ((((A₀.absorbTab F tab).mapOut f).toTPKindAlg.composeBothOut C₁ id).out a.1))
    (fun a => dropTabM A₀ C₁ F tab' f
      ((((A₀.absorbTab F tab').mapOut f).toTPKindAlg.composeBothOut C₁ id).out a.1))
    fun _ => rfl

end Insert

end Quantum.AdaptiveIAlg

/-! ### The extraction expansion reads the claim and the challenger's registers -/

namespace SPBCS

open IOP.SPTerm

variable {k kN kS L e : ℕ} {ι : Type} {n : ι → ℕ} {P : (j : ι) → ProtocolSpec (n j)}
  [∀ j i, Fintype ((P j).Challenge i)] [∀ j i, DecidableEq ((P j).Challenge i)]
  [∀ j i, Nonempty ((P j).Challenge i)] {t : SPTerm ι} {Mg : Merges t} {X : Type}
  {M : SPBCS Mg P X k kN kS L e} {Bf : ℕ} [∀ j i, Fintype ((M.comp j).MessageWrite i)]
  {V : X → FullTr P t → Bool} (Qs : ∀ x, M.IOPQueries V x) {X' : Type} [Fintype X']
  [DecidableEq X'] {SC : Type} [Fintype SC] [DecidableEq SC] {O : Type}

omit [∀ j i, Nonempty ((P j).Challenge i)] in
/-- **The extraction expansion of an adversary with its output read through a map sees only the
claim and the challenger's registers**: two composed registers, of `A.mapOut f` and of `A`, with
the same claim and the same challenger's registers have the same next queries. -/
theorem simExtractionExpansion_mapOut_next_congr
    {shA : AlgShape (Bits (queryBits k kN kS L)) (XOut k e) X' (M.Response Bf)} (A : AdaptiveIAlg shA O)
    (f : O → Claim X M.NIProof)
    (Psim : NARG.Simulator (Bits (queryBits k kN kS L)) (XOut k e) X' (M.Response Bf) SC) (Q : ℕ)
    (v : (A.mapOut f).toTPKindAlg.CW (simExtChallenger Psim Q))
    (v' : A.toTPKindAlg.CW (simExtChallenger Psim Q))
    (h1 : f (A.out v.adv.workspace.1) = f (A.out v'.adv.workspace.1)) (h2 : v.chal = v'.chal) :
    (simExtractionExpansion (A.mapOut f).toTPKindAlg Psim Q Qs).next v =
      (simExtractionExpansion (A.mapOut f).toTPKindAlg Psim Q Qs).next v' := by
  have ha : advOut (A.mapOut f).toTPKindAlg Psim Q v = advOut (A.mapOut f).toTPKindAlg Psim Q v' :=
    h1
  have hp : extractionProg (A.mapOut f).toTPKindAlg Psim Q Qs v =
      extractionProg (A.mapOut f).toTPKindAlg Psim Q Qs v' := by
    unfold extractionProg finalAnswer assBytes finalAss simQueryInputs
    rw [ha, h2]
  change (fun ans => (extractionProg (A.mapOut f).toTPKindAlg Psim Q Qs v).next padQuery ans) =
    fun ans => (extractionProg (A.mapOut f).toTPKindAlg Psim Q Qs v').next padQuery ans
  rw [hp]

omit [∀ j i, Nonempty ((P j).Challenge i)] in
/-- **The extraction expansion of an adversary absorbed with a table, its output read through a
map, does not depend on the table**: at two tables, two composed registers with the same claim
and the same challenger's registers have the same next queries. -/
theorem simExtractionExpansion_absorbTab_next_congr [Inhabited X'] {Req₂ Resp₂ : Type}
    [Fintype Req₂]
    [DecidableEq Req₂] [Fintype Resp₂] [DecidableEq Resp₂]
    {shA₀ : AlgShape (Bits (queryBits k kN kS L)) (XOut k e) X' (M.Response Bf)} (A₀ : AdaptiveIAlg shA₀ O)
    (F : TwoRelay X' (M.Response Bf) X' (M.Response Bf) Req₂ Resp₂)
    (tab tab' : A₀.OuterTab Req₂ Resp₂) (f : O → Claim X M.NIProof)
    (Psim : NARG.Simulator (Bits (queryBits k kN kS L)) (XOut k e) X' (M.Response Bf) SC) (Q : ℕ)
    (v : ((A₀.absorbTab F tab).mapOut f).toTPKindAlg.CW (simExtChallenger Psim Q))
    (v' : ((A₀.absorbTab F tab').mapOut f).toTPKindAlg.CW (simExtChallenger Psim Q))
    (h1 : advOut _ Psim Q v = advOut _ Psim Q v') (h2 : v.chal = v'.chal) :
    (simExtractionExpansion ((A₀.absorbTab F tab).mapOut f).toTPKindAlg Psim Q Qs).next v =
      (simExtractionExpansion ((A₀.absorbTab F tab').mapOut f).toTPKindAlg Psim Q Qs).next v' := by
  have hp : extractionProg ((A₀.absorbTab F tab).mapOut f).toTPKindAlg Psim Q Qs v =
      extractionProg ((A₀.absorbTab F tab').mapOut f).toTPKindAlg Psim Q Qs v' := by
    unfold extractionProg finalAnswer assBytes finalAss simQueryInputs
    rw [h1, h2]
    rfl
  change (fun ans => (extractionProg ((A₀.absorbTab F tab).mapOut f).toTPKindAlg Psim Q Qs v).next
      padQuery ans) = fun ans =>
    (extractionProg ((A₀.absorbTab F tab').mapOut f).toTPKindAlg Psim Q Qs v').next padQuery ans
  rw [hp]

end SPBCS

/-! ### One term of `zkForgerSuccess` as an extraction run of the table form -/

namespace RingSignature.Insider

open IOP.SPTerm Signature

section ZK

variable {k kN kS L e N n t : ℕ} {TB : BaseTypes} [Fintype TB.PK] [DecidableEq TB.PK]
  [Fintype TB.Msg] [DecidableEq TB.Msg]
  [Fintype TB.Pub] [DecidableEq TB.Pub] [Fintype TB.KeyCoins]
  [DecidableEq TB.KeyCoins]
  {B : BaseSigner (Bits (queryBits k kN kS L)) (XOut k e) N TB}
  {ι : Type} {τ : SPTerm ι} {Mg : Merges τ} {nr : ι → ℕ}
  {P : (j : ι) → ProtocolSpec (nr j)} [∀ j i, Fintype ((P j).Challenge i)]
  [∀ j i, DecidableEq ((P j).Challenge i)] [∀ j i, Nonempty ((P j).Challenge i)]
  {X₀ Wit₀ : Type} [DecidableEq X₀] {M : SPBCS Mg P X₀ k kN kS L e} {Λ : SiteLayout Mg} {b : ℕ}
  [∀ j i, Fintype ((M.comp j).MessageWrite i)] {E : (j : ι) → (M.comp j).Encoder}
  {Vr : X₀ → FullTr P τ → Bool} {Qs : ∀ x, M.IOPQueries Vr x}
  {hb : M.FormatBounds Qs b b} {R : Type} [Fintype R] [DecidableEq R] [Nonempty R]
  {honest : Wit₀ → R → CausalProver P τ X₀} {stmt : RingStmt B → X₀} {check : RingStmt B → Bool}
  {input : RingStmt B → RingWit B → Option Wit₀}
  {adm : KeyRing B.PK N → Prop} [DecidablePred adm] {WitK : Type}
  {wit : RingStmt B → WitK → RingWit B}
  (A : InsiderAdversary (ofBase B (Ring.spbcsComapProofSystem M Λ E hb honest stmt check input)
    adm) n (OracleView.queriesOnly (Bits (queryBits k kN kS L)) (XOut k e)) t)
  [Nonempty B.Msg] [Nonempty B.Pub] [Nonempty B.BSig] [Nonempty M.NIProof] [NeZero n]
  [ert : EmptyRingTest stmt]

local notation "𝒫" => Ring.spbcsComapProofSystem M Λ E hb honest stmt check input

local notation "ZAdv" => QueryBoundedAdversary (Bits (queryBits k kN kS L)) (XOut k e)
  (UnforgeRequest n (SideOracle.none (ofBase B 𝒫 adm)))
  (UnforgeResponse (SideOracle.none (ofBase B 𝒫 adm)))
  (KeyRing (RingScheme.PK (ofBase B 𝒫 adm)) N × RingScheme.Msg (ofBase B 𝒫 adm) ×
    RingScheme.Sig (ofBase B 𝒫 adm)) t

variable [Fintype TB.BSig] [DecidableEq TB.BSig]

omit [Nonempty B.BSig] ert [Fintype R] [DecidableEq R] [Nonempty R] in
/-- **One term of `zkForgerSuccess` as an extraction run of the table form**: the extraction run
of the simulation-extraction adversary `seAlg` (`extAdv`) is the extraction run (`extRun`) of the
adversary at the table `keyReply keys` through `seTwo`, with the expansion and the win read
through the reinsertion of the table (`insertTabM`) and the default with the table dropped. -/
theorem simProb_extAdv_seAlg_eq (refuses : KeyRing B.PK N → ℕ → B.Msg → B.Coins → Prop)
    (pubOf : B.Coins → B.Pub) (keys : Fin n → B.KeyCoins) (Q : ℕ) (a : (A.at keys).Aux)
    (ds : Fin Q → B.Coins) {SC : Type} [Fintype SC] [DecidableEq SC]
    (Psim : NARG.Simulator (Bits (queryBits k kN kS L)) (XOut k e)
      (RelayStmt B 𝒫 adm n)
      (M.Response b) SC)
    (Ext : CausalExtractor P τ X₀ WitK) (kq : ℕ) :
    simProb (outEquiv k e) (extAdv Qs (seAlg A refuses pubOf keys Q a ds) Psim Q kq)
        (forgerWins A wit refuses pubOf keys Q a ds Psim Ext) =
      simProb (outEquiv k e) (extRun (outEquiv k e) ((A.at keys).alg a) (simExtChallenger Psim Q)
          (seTwo B (fun i => B.pk (keys i)) refuses pubOf ds)
          ⟨fun r => (simExtractionExpansion (seAlg A refuses pubOf keys Q a ds).toTPKindAlg Psim Q
            Qs).next (Quantum.AdaptiveIAlg.insertTabM ((A.at keys).alg a) (simExtChallenger Psim Q)
              (seTwo B (fun i => B.pk (keys i)) refuses pubOf ds) (fun _ => keyReply B keys)
              claimOfOut r)⟩
          (kq + Q * Psim.q)
          (Quantum.AdaptiveIAlg.dropTabM ((A.at keys).alg a) (simExtChallenger Psim Q)
            (seTwo B (fun i => B.pk (keys i)) refuses pubOf ds) (fun _ => keyReply B keys)
            claimOfOut
            (((seAlg A refuses pubOf keys Q a ds).toTPKindAlg.composeBothOut
              (simExtChallenger Psim Q) id).defaultOut))
          (fun _ => keyReply B keys))
        (fun r D => forgerWins A wit refuses pubOf keys Q a ds Psim Ext
          (Quantum.AdaptiveIAlg.insertTabM ((A.at keys).alg a) (simExtChallenger Psim Q)
            (seTwo B (fun i => B.pk (keys i)) refuses pubOf ds) (fun _ => keyReply B keys)
            claimOfOut r) D) := by
  have h :=
    Quantum.AdaptiveIAlg.simProb_expandAdv_mapOut_cross
    (((A.at keys).alg a).absorbTab (seTwo B (fun i => B.pk (keys i)) refuses pubOf ds)
      (fun _ => keyReply B keys)) claimOfOut (simExtChallenger Psim Q)
    (simExtractionExpansion (seAlg A refuses pubOf keys Q a ds).toTPKindAlg Psim Q Qs)
    (kq + Q * Psim.q)
    (((seAlg A refuses pubOf keys Q a ds).toTPKindAlg.composeBothOut
      (simExtChallenger Psim Q) id).defaultOut)
    (forgerWins A wit refuses pubOf keys Q a ds Psim Ext)
    (dropTabCW ((A.at keys).alg a) (simExtChallenger Psim Q)
      (seTwo B (fun i => B.pk (keys i)) refuses pubOf ds) (fun _ => keyReply B keys))
    (Quantum.AdaptiveIAlg.insertTabM ((A.at keys).alg a) (simExtChallenger Psim Q)
      (seTwo B (fun i => B.pk (keys i)) refuses pubOf ds) (fun _ => keyReply B keys) claimOfOut)
    (extOut ((A.at keys).alg a) (simExtChallenger Psim Q)
      (seTwo B (fun i => B.pk (keys i)) refuses pubOf ds)
      (Quantum.AdaptiveIAlg.dropTabM ((A.at keys).alg a) (simExtChallenger Psim Q)
        (seTwo B (fun i => B.pk (keys i)) refuses pubOf ds) (fun _ => keyReply B keys)
        claimOfOut
        (((seAlg A refuses pubOf keys Q a ds).toTPKindAlg.composeBothOut
          (simExtChallenger Psim Q) id).defaultOut))
      (fun _ => keyReply B keys))
    (fun o => by cases o <;> rfl)
    (fun c => SPBCS.simExtractionExpansion_mapOut_next_congr Qs _ claimOfOut Psim Q _ c rfl rfl)
    (fun _ _ => Iff.rfl)
  exact h

/-! ### The objects at any adversary -/

/-- **The simulation-extraction adversary of an adversary `𝒜`** (`seAlg` at `𝒜`): `𝒜` absorbed
with the table `keyReply keys` through `seTwo`, its output read as a claim. `seAlg` is `seAlgQ` at
`A.at keys`. -/
noncomputable abbrev seAlgQ (𝒜 : ZAdv)
    (refuses : KeyRing B.PK N → ℕ → B.Msg → B.Coins → Prop) (pubOf : B.Coins → B.Pub)
    (keys : Fin n → B.KeyCoins) (Q : ℕ) (a : 𝒜.Aux) (ds : Fin Q → B.Coins) :=
  (AdaptiveIAlg.absorbTab (Req₁ := RelayStmt B 𝒫 adm n) (Resp₁ := (𝒫).Proof) (𝒜.alg a)
    (seTwo B (fun i => B.pk (keys i)) refuses pubOf ds) (fun _ => keyReply B keys)).mapOut
    claimOfOut

/-- **The forger's win in one extraction run at an adversary `𝒜`** (`forgerWins` at `𝒜`):
`forgerWins` is `forgerWinsQ` at `A.at keys`. -/
def forgerWinsQ (𝒜 : ZAdv)
    (refuses : KeyRing B.PK N → ℕ → B.Msg → B.Coins → Prop) (pubOf : B.Coins → B.Pub)
    (keys : Fin n → B.KeyCoins) (Q : ℕ) (a : 𝒜.Aux) (ds : Fin Q → B.Coins) {SC : Type}
    [Fintype SC] [DecidableEq SC] (Psim : NARG.Simulator (Bits (queryBits k kN kS L)) (XOut k e)
      (RelayStmt B 𝒫 adm n) (M.Response b) SC)
    (Ext : CausalExtractor P τ X₀ WitK) (c : SPBCS.Reg (seAlgQ 𝒜 refuses pubOf keys Q a ds) Psim Q)
    (D : DB (Bits (queryBits k kN kS L)) (Out k e)) : Prop :=
  ∃ w ∈ M.dbExtractBits Ext (stmt (outStmt ((𝒜.alg a).out
      (SPBCS.advWorkspace (seAlgQ 𝒜 refuses pubOf keys Q a ds).toTPKindAlg Psim Q c).1.1.work))) D,
    ∃ f ∈ decodeWit (outStmt ((𝒜.alg a).out
        (SPBCS.advWorkspace (seAlgQ 𝒜 refuses pubOf keys Q a ds).toTPKindAlg Psim Q c).1.1.work))
      (wit (outStmt ((𝒜.alg a).out
        (SPBCS.advWorkspace (seAlgQ 𝒜 refuses pubOf keys Q a ds).toTPKindAlg Psim Q
          c).1.1.work)) w),
      ∀ H, Signature.Forges keys H f (corruptHist ((Quantum.requests
        (SPBCS.advWorkspace (seAlgQ 𝒜 refuses pubOf keys Q a ds).toTPKindAlg Psim Q
          c).1.1.logs).take Q))

/-- **The expansion of the extraction run at an adversary `𝒜`**: the extraction expansion of the
simulation-extraction adversary at the empty table (`tab₀`), through the reinsertion of the
table; it reads no key coins (`simExtractionExpansion_absorbTab_next_congr`). -/
noncomputable def zkExp (𝒜 : ZAdv)
    (refuses : KeyRing B.PK N → ℕ → B.Msg → B.Coins → Prop) (pubOf : B.Coins → B.Pub)
    (pks : Fin n → B.PK) (Q : ℕ) (a : 𝒜.Aux) (ds : Fin Q → B.Coins) {SC : Type} [Fintype SC]
    [DecidableEq SC] (Psim : NARG.Simulator (Bits (queryBits k kN kS L)) (XOut k e)
      (RelayStmt B 𝒫 adm n) (M.Response b) SC) :
    Expansion (Bits (queryBits k kN kS L)) (Out k e)
      (ExtReg (𝒜.alg a) (simExtChallenger Psim Q) (MURequest (SignOracle.ring B) n)
        (MUResponse B.core)) :=
  ⟨fun r => (simExtractionExpansion (((𝒜.alg a).absorbTab (seTwo B pks refuses pubOf ds)
      (tab₀ (𝒜.alg a))).mapOut claimOfOut).toTPKindAlg Psim Q Qs).next
    (Quantum.AdaptiveIAlg.insertTabM (𝒜.alg a) (simExtChallenger Psim Q)
      (seTwo B pks refuses pubOf ds) (tab₀ (𝒜.alg a)) claimOfOut r)⟩

/-- **The default output of the extraction run at an adversary `𝒜`**: that of the run at the
empty table, the table dropped (`dropTabM_defaultOut_congr`: the same at every table). -/
noncomputable def zkDefault (𝒜 : ZAdv)
    (refuses : KeyRing B.PK N → ℕ → B.Msg → B.Coins → Prop) (pubOf : B.Coins → B.Pub)
    (pks : Fin n → B.PK) (Q : ℕ) (a : 𝒜.Aux) (ds : Fin Q → B.Coins) {SC : Type} [Fintype SC]
    [DecidableEq SC] (Psim : NARG.Simulator (Bits (queryBits k kN kS L)) (XOut k e)
      (RelayStmt B 𝒫 adm n) (M.Response b) SC) :
    ExtReg (𝒜.alg a) (simExtChallenger Psim Q) (MURequest (SignOracle.ring B) n)
      (MUResponse B.core) :=
  Quantum.AdaptiveIAlg.dropTabM (𝒜.alg a) (simExtChallenger Psim Q)
    (seTwo B pks refuses pubOf ds) (tab₀ (𝒜.alg a)) claimOfOut
    ((((𝒜.alg a).absorbTab (seTwo B pks refuses pubOf ds) (tab₀ (𝒜.alg a))).mapOut
      claimOfOut).toTPKindAlg.composeBothOut (simExtChallenger Psim Q) id).defaultOut

omit [Nonempty B.BSig] ert [Fintype R] [DecidableEq R] [Nonempty R] in
/-- **One term of `zkForgerSuccess` as an extraction run at the adversary**
(`simProb_extAdv_seAlg_eq` with the expansion and the default read at the empty table, the win at
`A.at keys`): only the table, `keyReply keys`, holds the users' key coins. -/
theorem simProb_extAdv_seAlg_eq_zk (refuses : KeyRing B.PK N → ℕ → B.Msg → B.Coins → Prop)
    (pubOf : B.Coins → B.Pub) (keys : Fin n → B.KeyCoins) (Q : ℕ) (a : (A.at keys).Aux)
    (ds : Fin Q → B.Coins) {SC : Type} [Fintype SC] [DecidableEq SC]
    (Psim : NARG.Simulator (Bits (queryBits k kN kS L)) (XOut k e)
      (RelayStmt B 𝒫 adm n) (M.Response b) SC)
    (Ext : CausalExtractor P τ X₀ WitK) (kq : ℕ) :
    simProb (outEquiv k e) (extAdv Qs (seAlg A refuses pubOf keys Q a ds) Psim Q kq)
        (forgerWins A wit refuses pubOf keys Q a ds Psim Ext) =
      simLaw (outEquiv k e) (extRun (outEquiv k e) ((A.at keys).alg a)
          (simExtChallenger Psim Q) (seTwo B (fun i => B.pk (keys i)) refuses pubOf ds)
          (zkExp (A.at keys) refuses pubOf (fun i => B.pk (keys i)) Q a ds Psim) (kq + Q * Psim.q)
          (zkDefault (A.at keys) refuses pubOf (fun i => B.pk (keys i)) Q a ds Psim)
          (fun _ => keyReply B keys))
        {x | forgerWinsQ (wit := wit) (A.at keys) refuses pubOf keys Q a ds Psim Ext
          (Quantum.AdaptiveIAlg.insertTabM ((A.at keys).alg a) (simExtChallenger Psim Q)
            (seTwo B (fun i => B.pk (keys i)) refuses pubOf ds) (fun _ => keyReply B keys)
            claimOfOut x.1.out) x.2} := by
  rw [simProb_extAdv_seAlg_eq]
  have hE : (⟨fun r => (simExtractionExpansion (seAlg A refuses pubOf keys Q a ds).toTPKindAlg
      Psim Q Qs).next (Quantum.AdaptiveIAlg.insertTabM ((A.at keys).alg a)
        (simExtChallenger Psim Q) (seTwo B (fun i => B.pk (keys i)) refuses pubOf ds)
        (fun _ => keyReply B keys) claimOfOut r)⟩ :
      Expansion (Bits (queryBits k kN kS L)) (Out k e) (ExtReg ((A.at keys).alg a)
        (simExtChallenger Psim Q) (MURequest (SignOracle.ring B) n) (MUResponse B.core))) =
      zkExp (A.at keys) refuses pubOf (fun i => B.pk (keys i)) Q a ds Psim := by
    unfold zkExp
    congr 1
  have hd : Quantum.AdaptiveIAlg.dropTabM ((A.at keys).alg a) (simExtChallenger Psim Q)
      (seTwo B (fun i => B.pk (keys i)) refuses pubOf ds) (fun _ => keyReply B keys) claimOfOut
      (((seAlg A refuses pubOf keys Q a ds).toTPKindAlg.composeBothOut
        (simExtChallenger Psim Q) id).defaultOut) =
      zkDefault (A.at keys) refuses pubOf (fun i => B.pk (keys i)) Q a ds Psim :=
    Quantum.AdaptiveIAlg.dropTabM_defaultOut_congr ((A.at keys).alg a)
      (simExtChallenger Psim Q) (seTwo B (fun i => B.pk (keys i)) refuses pubOf ds)
      (fun _ => keyReply B keys) (tab₀ _) claimOfOut
  -- TODO(unbundle-M4): `hd`'s left side is stated at `seAlg`'s scheme shape, not the goal's; go
  -- back to `rw [hE, hd]` once the shapes agree
  rw [hE, ← hd]
  rfl

omit [Nonempty B.BSig] [DecidableEq X₀] ert [Fintype R] [DecidableEq R] [Nonempty R] in
/-- **Every multi-user request of the zero-knowledge forger is the dummy or a corruption among
the adversary's first `Q` requests**: on every basis state of nonzero amplitude of the
compressed-oracle simulation of the bridge at an adversary `𝒜` (against any replies `rep`), every
logged multi-user request is `publicKey 0`, or `corrupt i` with `corrupt i` among the first `Q`
requests the adversary logged (`seTwo` forwards corruptions numbered below `Q` only). -/
theorem zk_bridge_requests (𝒜 : ZAdv)
    (refuses : KeyRing B.PK N → ℕ → B.Msg → B.Coins → Prop) (pubOf : B.Coins → B.Pub)
    (pks : Fin n → B.PK) (Q : ℕ) (a : 𝒜.Aux) (ds : Fin Q → B.Coins) {SC : Type} [Fintype SC]
    [DecidableEq SC] (Psim : NARG.Simulator (Bits (queryBits k kN kS L)) (XOut k e)
      (RelayStmt B 𝒫 adm n) (M.Response b) SC) (kq : ℕ)
    (rep : ℕ → MURequest (SignOracle.ring B) n → Option (MUResponse B.core)) {bs}
    (hbs : simState (outEquiv k e) ((bridgeAlg (outEquiv k e) (𝒜.alg a)
      (simExtChallenger Psim Q) (seTwo B pks refuses pubOf ds) (.publicKey 0)
      (zkExp 𝒜 refuses pubOf pks Q a ds Psim) kq (zkDefault 𝒜 refuses pubOf pks Q a ds Psim)).inst
        rep) bs ≠ 0)
    {q : MURequest (SignOracle.ring B) n} (hq : q ∈ requests bs.1.1.2) :
    q = .publicKey 0 ∨ ∃ i, q = .corrupt i ∧ UnforgeRequest.corrupt i ∈
      (requests (GordieHowe.extLogs ((bridgeAlg (outEquiv k e) (𝒜.alg a)
        (simExtChallenger Psim Q) (seTwo B pks refuses pubOf ds) (.publicKey 0)
        (zkExp 𝒜 refuses pubOf pks Q a ds Psim) kq
        (zkDefault 𝒜 refuses pubOf pks Q a ds Psim)).out bs.1.1.1).out)).take Q := by
  obtain ⟨i, hi⟩ := (mem_requests_iff _ q).1 hq
  rcases bridgeLogsAt_of_tracePreserving (outEquiv k e) (𝒜.tracePreserving a) _ _ _ _
    _ _ rep bs hbs i q hi with h | ⟨j, r, hj, ho⟩
  · exact Or.inl h
  · right
    cases r with
    | corrupt i' =>
      simp only [seTwo] at ho
      split_ifs at ho with hc
      cases ho
      exact ⟨i', rfl, mem_take_requests_of_log _ j hj hc⟩
    | sign s R m => simp [seTwo] at ho
    | sideSign _ bm => exact bm.elim

/-! ### The readout of the multi-user forger -/

/-- **A candidate forgery read from the extraction run's registers `r` and database `D`** at an
adversary `𝒜` and the public keys `pks`: the decoding of the ring witness of a witness that `Ext`
extracts for the forgery's statement; it verifies at every oracle, under the key of a user with no
corruption among the first `Q` logged requests. -/
def ZKCand (𝒜 : ZAdv) (Ext : CausalExtractor P τ X₀ WitK) (pks : Fin n → B.PK) (Q : ℕ)
    {a : 𝒜.Aux}
    {C₁ : Challenger (Bits (queryBits k kN kS L)) (XOut k e) (RelayStmt B 𝒫 adm n) (M.Response b)}
    (r : ExtReg (𝒜.alg a) C₁ (MURequest (SignOracle.ring B) n) (MUResponse B.core))
    (D : DB (Bits (queryBits k kN kS L)) (Out k e)) (f : B.PK × B.BMsg × B.BSig) : Prop :=
  ∃ w ∈ M.dbExtractBits Ext (stmt (outStmt (extForgery r))) D,
    f ∈ decodeWit (outStmt (extForgery r)) (wit (outStmt (extForgery r)) w) ∧
    ∀ H, B.bverify H f.1 f.2.1 f.2.2 = true ∧
      ∃ i, pks i = f.1 ∧ UnforgeRequest.corrupt i ∉ (requests (GordieHowe.extLogs r)).take Q

variable [Fintype TB.Coins] [DecidableEq TB.Coins] [Nonempty TB.Coins]

variable [Nonempty TB.KeyCoins]

variable (B) in
/-- **The ring statement of a forgery** `(R, m, (y, π))`: `(R, m, y)`. -/
abbrev forgeryStmt {Prf : Type} (o : KeyRing B.PK N × B.Msg × (B.Pub × Prf)) : RingStmt B :=
  ⟨o.1, o.2.1, o.2.2.1⟩

/-- **The candidate forgeries read from the extraction run's registers `r` and database `D`**: the
decodings of the ring witnesses (`wit`) of the witnesses that `Ext` extracts for the forgery's
statement, in the order of `SPBCS.dbExtractBitsList`.

Running time: one run of `SPBCS.dbExtractBitsList`, then one application of `wit` and one decoding
per witness. This running time is argued here, not proved in Lean. -/
def zkCands {TPS : PSTypes} [Fintype TPS.Proof] [DecidableEq TPS.Proof] {PS : ProofSystem (Bits (queryBits k kN kS L)) (XOut k e) (RingStmt B) (RingWit B) TPS}
    (𝒜 : QueryBoundedAdversary (Bits (queryBits k kN kS L)) (XOut k e)
      (UnforgeRequest n (SideOracle.none (ofBase B PS adm)))
      (UnforgeResponse (SideOracle.none (ofBase B PS adm)))
      (KeyRing (RingScheme.PK (ofBase B PS adm)) N × RingScheme.Msg (ofBase B PS adm) ×
        RingScheme.Sig (ofBase B PS adm)) t)
    (Ext : CausalExtractor P τ X₀ WitK) {a : 𝒜.Aux}
    {C₁ : Challenger (Bits (queryBits k kN kS L)) (XOut k e) (RelayStmt B PS adm n) (M.Response b)}
    (r : ExtReg (𝒜.alg a) C₁ (MURequest (SignOracle.ring B) n) (MUResponse B.core))
    (D : DB (Bits (queryBits k kN kS L)) (Out k e)) : List (B.PK × B.BMsg × B.BSig) :=
  (M.dbExtractBitsList Ext (stmt (forgeryStmt B (extForgery r))) D).filterMap fun w =>
    decodeWit (forgeryStmt B (extForgery r)) (wit (forgeryStmt B (extForgery r)) w)

/-- **The test of a candidate forgery** at the public keys `pks`: it verifies at the zero oracle,
under the key of a user with no corruption among the first `Q` logged requests of `r`.

Running time: one base verification, then at most `n` comparisons of keys and `n` searches of the
first `Q` logged requests. This running time is argued here, not proved in Lean. -/
def zkCandTest {TPS : PSTypes} [Fintype TPS.Proof] [DecidableEq TPS.Proof] {PS : ProofSystem (Bits (queryBits k kN kS L)) (XOut k e) (RingStmt B) (RingWit B) TPS}
    (𝒜 : QueryBoundedAdversary (Bits (queryBits k kN kS L)) (XOut k e)
      (UnforgeRequest n (SideOracle.none (ofBase B PS adm)))
      (UnforgeResponse (SideOracle.none (ofBase B PS adm)))
      (KeyRing (RingScheme.PK (ofBase B PS adm)) N × RingScheme.Msg (ofBase B PS adm) ×
        RingScheme.Sig (ofBase B PS adm)) t)
    (pks : Fin n → B.PK) (Q : ℕ) {a : 𝒜.Aux}
    {C₁ : Challenger (Bits (queryBits k kN kS L)) (XOut k e) (RelayStmt B PS adm n) (M.Response b)}
    (r : ExtReg (𝒜.alg a) C₁ (MURequest (SignOracle.ring B) n) (MUResponse B.core))
    (f : B.PK × B.BMsg × B.BSig) : Bool :=
  decide (B.bverify 0 f.1 f.2.1 f.2.2 = true ∧
    ∃ i, pks i = f.1 ∧ UnforgeRequest.corrupt i ∉ (requests (GordieHowe.extLogs r)).take Q)

/-- **The readout of the multi-user forger**: the first candidate (`zkCands`) passing the test
(`zkCandTest`), `f₀` if there is none. It reads the public keys, not the key coins.

Running time: that of `zkCands` and one run of `zkCandTest` per candidate. This running time is
argued here, not proved in Lean. -/
def zkReadout {TPS : PSTypes} [Fintype TPS.Proof] [DecidableEq TPS.Proof] {PS : ProofSystem (Bits (queryBits k kN kS L)) (XOut k e) (RingStmt B) (RingWit B) TPS}
    (𝒜 : QueryBoundedAdversary (Bits (queryBits k kN kS L)) (XOut k e)
      (UnforgeRequest n (SideOracle.none (ofBase B PS adm)))
      (UnforgeResponse (SideOracle.none (ofBase B PS adm)))
      (KeyRing (RingScheme.PK (ofBase B PS adm)) N × RingScheme.Msg (ofBase B PS adm) ×
        RingScheme.Sig (ofBase B PS adm)) t)
    (Ext : CausalExtractor P τ X₀ WitK) (pks : Fin n → B.PK) (Q : ℕ) {a : 𝒜.Aux}
    {C₁ : Challenger (Bits (queryBits k kN kS L)) (XOut k e) (RelayStmt B PS adm n) (M.Response b)}
    {kq : ℕ}
    (f₀ : B.PK × B.BMsg × B.BSig)
    (o : BaseGame.Tuple (Bits (queryBits k kN kS L)) (Out k e)
      (ExtReg (𝒜.alg a) C₁ (MURequest (SignOracle.ring B) n) (MUResponse B.core)) kq ×
        DB (Bits (queryBits k kN kS L)) (Out k e)) : B.PK × B.BMsg × B.BSig :=
  ((zkCands (stmt := stmt) (wit := wit) 𝒜 Ext o.1.out o.2).find?
    (zkCandTest 𝒜 pks Q o.1.out)).getD f₀

omit [Nonempty B.BSig] ert [Fintype R] [DecidableEq R] [Nonempty R] [Nonempty TB.KeyCoins]
  [Fintype TB.Coins] [DecidableEq TB.Coins] [Nonempty TB.Coins] in
/-- **The forger's win in the extraction run gives a candidate.** -/
theorem zkCand_of_forgerWinsQ (𝒜 : ZAdv)
    (refuses : KeyRing B.PK N → ℕ → B.Msg → B.Coins → Prop) (pubOf : B.Coins → B.Pub)
    (keys : Fin n → B.KeyCoins) (Q : ℕ) (a : 𝒜.Aux) (ds : Fin Q → B.Coins) {SC : Type}
    [Fintype SC] [DecidableEq SC] (Psim : NARG.Simulator (Bits (queryBits k kN kS L)) (XOut k e)
      (RelayStmt B 𝒫 adm n) (M.Response b) SC) (Ext : CausalExtractor P τ X₀ WitK)
    (r : ExtReg (𝒜.alg a) (simExtChallenger Psim Q) (MURequest (SignOracle.ring B) n)
      (MUResponse B.core)) (D : DB (Bits (queryBits k kN kS L)) (Out k e))
    (h : forgerWinsQ (wit := wit) 𝒜 refuses pubOf keys Q a ds Psim Ext
      (Quantum.AdaptiveIAlg.insertTabM (𝒜.alg a) (simExtChallenger Psim Q)
        (seTwo B (fun i => B.pk (keys i)) refuses pubOf ds) (fun _ => keyReply B keys)
        claimOfOut r) D) :
    ∃ f, ZKCand (wit := wit) 𝒜 Ext (fun i => B.pk (keys i)) Q r D f := by
  obtain ⟨w, hw, f, hf, hF⟩ := h
  refine ⟨f, w, hw, hf, fun H => ⟨(hF H).verify_eq, ?_⟩⟩
  obtain ⟨i, hi, hc, -⟩ := (hF H).exists_user
  exact ⟨i, hi, fun hm => hc (corrupted_corruptHist.2 hm)⟩

omit [Nonempty B.BSig] [Nonempty B.Msg] [Nonempty B.Pub] [Nonempty M.NIProof] ert [Fintype R]
  [DecidableEq R] [Nonempty R] [Fintype TB.BSig] [DecidableEq TB.BSig] [Nonempty TB.KeyCoins]
  [Fintype TB.Coins] [DecidableEq TB.Coins] [Nonempty TB.Coins] in
/-- **The readout is a forgery for the multi-user requests of the forger**: when there is a
candidate, for multi-user requests `mrs` that are `publicKey 0` or corruptions among the first
`Q` logged requests (`zk_bridge_requests`), the readout is a forgery of MU-EUF-CMA^corr for
`mrs` at every oracle, for a base signer verifying without the oracle (`hB`). -/
theorem forgesReq_zkReadout (𝒜 : ZAdv) (Ext : CausalExtractor P τ X₀ WitK)
    (keys : Fin n → B.KeyCoins) (Q : ℕ) {a : 𝒜.Aux}
    {C₁ : Challenger (Bits (queryBits k kN kS L)) (XOut k e) (RelayStmt B 𝒫 adm n) (M.Response b)}
    {kq : ℕ}
    (f₀ : B.PK × B.BMsg × B.BSig)
    (o : BaseGame.Tuple (Bits (queryBits k kN kS L)) (Out k e)
      (ExtReg (𝒜.alg a) C₁ (MURequest (SignOracle.ring B) n) (MUResponse B.core)) kq ×
        DB (Bits (queryBits k kN kS L)) (Out k e))
    (hc : ∃ f, ZKCand (wit := wit) 𝒜 Ext (fun i => B.pk (keys i)) Q o.1.out o.2 f)
    (mrs : List (MURequest (SignOracle.ring B) n))
    (hmrs : ∀ q ∈ mrs, q = .publicKey 0 ∨ ∃ i, q = .corrupt i ∧
      UnforgeRequest.corrupt i ∈ (requests (GordieHowe.extLogs o.1.out)).take Q)
    (H : Bits (queryBits k kN kS L) → XOut k e) (hB : B.VerifiesWithoutOracle) :
    ForgesReq keys H
      (zkReadout (stmt := stmt) (wit := wit) 𝒜 Ext (fun i => B.pk (keys i)) Q f₀ o) mrs := by
  obtain ⟨f, w, hw, hf, hF⟩ := hc
  have hmem : f ∈ zkCands (stmt := stmt) (wit := wit) 𝒜 Ext o.1.out o.2 := by
    refine List.mem_filterMap.2 ⟨w, ?_, hf⟩
    rw [← Multiset.mem_coe, coe_dbExtractBitsList]
    exact hw
  have htf : zkCandTest 𝒜 (fun i => B.pk (keys i)) Q o.1.out f = true := by
    rw [zkCandTest, decide_eq_true_iff]
    exact ⟨(hF 0).1, (hF 0).2⟩
  have hsome := List.find?_isSome.2 ⟨f, hmem, htf⟩
  obtain ⟨f', hf'⟩ := Option.isSome_iff_exists.1 hsome
  have hT := List.find?_some hf'
  rw [zkCandTest, decide_eq_true_iff] at hT
  rw [zkReadout, hf', Option.getD_some]
  obtain ⟨hv, i, hi, hcor⟩ := hT
  refine ⟨by rw [hB.bverify_eq H 0]; exact hv, i, hi, fun hm => ?_, fun sm hm => ?_⟩
  · rcases hmrs _ hm with h | ⟨i', h, hi'⟩
    · cases h
    · cases h
      exact hcor hi'
  · rcases hmrs _ hm with h | ⟨i', h, -⟩ <;> cases h

/-! ### The multi-user forger and the bound -/

variable (B) in
/-- **The multi-user forger's auxiliary input** at the public keys: the adversary's auxiliary input
and uniform signing coins for `Q` requests. -/
noncomputable def zkAux (Q : ℕ) (pks : Fin n → B.PK) :
    PMF ((A (pks, ())).Aux × (Fin Q → B.Coins)) :=
  (A (pks, ())).aux.bind fun a => (PMF.uniformOfFintype (Fin Q → B.Coins)).map fun ds => (a, ds)

omit ert [Fintype TB.BSig] [DecidableEq TB.BSig] [DecidableEq TB.Coins] [Nonempty B.Msg]
  [Nonempty B.Pub] [Nonempty B.BSig] [Nonempty M.NIProof] [NeZero n] [DecidableEq X₀] [Fintype R]
  [DecidableEq R] [Nonempty R] [Nonempty TB.KeyCoins] in
/-- **The auxiliary input is the product of the adversary's and the uniform coins.** -/
theorem zkAux_apply (Q : ℕ) (pks : Fin n → B.PK) (p : (A (pks, ())).Aux × (Fin Q → B.Coins)) :
    zkAux B A Q pks p = (A (pks, ())).aux p.1 * PMF.uniformOfFintype (Fin Q → B.Coins) p.2 := by
  classical
  rw [zkAux, PMF.bind_apply, tsum_eq_single p.1 fun a ha => ?_]
  · congr 1
    rw [PMF.map_apply, tsum_eq_single p.2 fun ρ hρ => ?_]
    · simp
    · simp only [ite_eq_right_iff]
      intro h
      exact absurd (congrArg Prod.snd h) (Ne.symm hρ)
  · rw [PMF.map_apply]
    refine mul_eq_zero_of_right _ (ENNReal.tsum_eq_zero.2 fun ρ => ?_)
    simp only [ite_eq_right_iff]
    intro h
    exact absurd (congrArg Prod.fst h) (Ne.symm ha)

/-- **The multi-user forger of the zero-knowledge route** (`Signature.tableForger`): on the
public keys it draws the adversary's auxiliary input and signing coins (`zkAux`), runs the
compressed-oracle simulation of the bridge of the adversary's extraction run (through `seTwo`, the
expansion `zkExp`, the default `zkDefault`) with its request points sent to the multi-user
challenger, and outputs the candidate read from the output and the measured database
(`zkReadout`). -/
noncomputable def zkForger (refuses : KeyRing B.PK N → ℕ → B.Msg → B.Coins → Prop)
    (pubOf : B.Coins → B.Pub) (Q : ℕ) {SC : Type} [Fintype SC] [DecidableEq SC]
    (Psim : NARG.Simulator (Bits (queryBits k kN kS L)) (XOut k e)
      (RelayStmt B 𝒫 adm n) (M.Response b) SC)
    (Ext : CausalExtractor P τ X₀ WitK) (kq : ℕ) (f₀ : B.PK × B.BMsg × B.BSig) :
    MUAdversary (SignOracle.ring B) n (OracleView.queriesOnly (Bits (queryBits k kN kS L))
      (XOut k e)) 0 :=
  tableForger (SignOracle.ring B) (outEquiv k e) (fun pks => (A (pks, ())).Aux × (Fin Q → B.Coins))
    (zkAux B A Q) (fun pks p => (A (pks, ())).alg p.1) (fun _ _ => simExtChallenger Psim Q)
    (fun pks p => seTwo B pks refuses pubOf p.2) (.publicKey 0)
    (fun pks p => zkExp (A (pks, ())) refuses pubOf pks Q p.1 p.2 Psim) (kq + Q * Psim.q)
    (fun pks p => zkDefault (A (pks, ())) refuses pubOf pks Q p.1 p.2 Psim)
    (fun pks _ => zkReadout (stmt := stmt) (wit := wit) (A (pks, ())) Ext pks Q f₀)

/-- **The extraction-run sum at an adversary `𝒜`**: the average over the signing coins and the
auxiliary input of the probability of the win in the extraction run of the table form. -/
noncomputable def zkSum (refuses : KeyRing B.PK N → ℕ → B.Msg → B.Coins → Prop)
    (pubOf : B.Coins → B.Pub) (keys : Fin n → B.KeyCoins) (Q : ℕ) {SC : Type} [Fintype SC]
    [DecidableEq SC] (Psim : NARG.Simulator (Bits (queryBits k kN kS L)) (XOut k e)
      (RelayStmt B 𝒫 adm n) (M.Response b) SC) (Ext : CausalExtractor P τ X₀ WitK) (kq : ℕ)
    (𝒜 : ZAdv) : ℝ≥0∞ :=
  ∑' ds, PMF.uniformOfFintype (Fin Q → B.Coins) ds * ∑' a, 𝒜.aux a *
    simLaw (outEquiv k e) (extRun (outEquiv k e) (𝒜.alg a)
        (simExtChallenger Psim Q) (seTwo B (fun i => B.pk (keys i)) refuses pubOf ds)
        (zkExp 𝒜 refuses pubOf (fun i => B.pk (keys i)) Q a ds Psim) (kq + Q * Psim.q)
        (zkDefault 𝒜 refuses pubOf (fun i => B.pk (keys i)) Q a ds Psim)
        (fun _ => keyReply B keys))
      {x | forgerWinsQ (wit := wit) 𝒜 refuses pubOf keys Q a ds Psim Ext
        (Quantum.AdaptiveIAlg.insertTabM (𝒜.alg a) (simExtChallenger Psim Q)
          (seTwo B (fun i => B.pk (keys i)) refuses pubOf ds) (fun _ => keyReply B keys)
          claimOfOut x.1.out) x.2}

section

-- Two extraction runs below compare by their arguments.
set_option allowUnsafeReducibility true in
attribute [local irreducible] Quantum.extRun

omit [Nonempty B.BSig] ert [Fintype R] [DecidableEq R] [Nonempty R] in
/-- **The zero-knowledge route's forger is a multi-user forger**: for a signing oracle without
queries (`hB`), with `Q'` at least the bridge's request points (`hQ`) and the adversary's slots
(`hslots`), the average over the key coins, the signing coins and the auxiliary input of the
forger's win in the simulation-extraction game is at most the success probability of `zkForger` in
MU-EUF-CMA^corr with the ring-aware signing oracle and `Q'` requests. -/
theorem sum_simProb_extAdv_le_muEufProb (hB : B.OracleFree)
    (refuses : KeyRing B.PK N → ℕ → B.Msg → B.Coins → Prop) (pubOf : B.Coins → B.Pub) (Q : ℕ)
    {SC : Type} [Fintype SC] [DecidableEq SC]
    (Psim : NARG.Simulator (Bits (queryBits k kN kS L)) (XOut k e)
      (RelayStmt B 𝒫 adm n) (M.Response b) SC)
    (Ext : CausalExtractor P τ X₀ WitK) (kq : ℕ) (f₀ : B.PK × B.BMsg × B.BSig) {Q' : ℕ}
    (hQ : ∀ pks (p : (A (pks, ())).Aux × (Fin Q → B.Coins)),
      (((((A (pks, ())).alg p.1).absorbTab (seTwo B pks refuses pubOf p.2)
        (tab₀ ((A (pks, ())).alg p.1))).toTPKindAlg.composeBothOut (simExtChallenger Psim Q)
          id).depth) + (kq + Q * Psim.q) + 1 ≤ Q')
    (hslots : ∀ pks (a : (A (pks, ())).Aux), ((A (pks, ())).alg a).slots ≤ Q') :
    ∑' keys, PMF.uniformOfFintype (Fin n → B.KeyCoins) keys *
      ∑ ds, PMF.uniformOfFintype (Fin Q → B.Coins) ds * ∑' a, (A.at keys).aux a *
        simProb (outEquiv k e) (extAdv Qs (seAlg A refuses pubOf keys Q a ds) Psim Q kq)
          (forgerWins A wit refuses pubOf keys Q a ds Psim Ext) ≤
      muEufProb (zkForger A (wit := wit) refuses pubOf Q Psim Ext kq f₀) Q' := by
  have htab : ∀ (keys : Fin n → B.KeyCoins) (p : (A (fun i => B.pk (keys i), ())).Aux ×
      (Fin Q → B.Coins)) (ω : Fin Q' → (SignOracle.ring B).Coins)
      (j : Fin ((A (fun i => B.pk (keys i), ())).alg p.1).slots)
      (q : MURequest (SignOracle.ring B) n),
      (q = .publicKey 0 ∨ ∃ c r, (seTwo B (PS := 𝒫) (adm := adm) (fun i => B.pk (keys i))
        refuses pubOf p.2).outer c r = some q) →
      keyReply B keys q = muReplyAfter (SignOracle.ring B) keys Q' ω j q := by
    intro keys p ω j q hq
    have hj : (j : ℕ) < Q' := lt_of_lt_of_le j.2 (hslots _ p.1)
    rcases hq with rfl | ⟨c, r, hr⟩
    · simp [keyReply, muReplyAfter, hj]
    · cases r with
      | corrupt i =>
        simp only [seTwo] at hr
        split_ifs at hr
        cases hr
        simp [keyReply, muReplyAfter, hj]
      | sign s R m => simp [seTwo] at hr
      | sideSign _ bm => exact bm.elim
  have hT := sum_simLaw_extRun_le_muEufProb_tableForger (SignOracle.ring B)
    (outEquiv k e) (fun pks => (A (pks, ())).Aux × (Fin Q → B.Coins)) (zkAux B A Q)
    (fun pks p => (A (pks, ())).alg p.1) (fun _ _ => simExtChallenger Psim Q)
    (fun pks p => seTwo B pks refuses pubOf p.2) (.publicKey 0)
    (fun pks p => zkExp (A (pks, ())) refuses pubOf pks Q p.1 p.2 Psim) (kq + Q * Psim.q)
    (fun pks p => zkDefault (A (pks, ())) refuses pubOf pks Q p.1 p.2 Psim)
    (fun pks _ => zkReadout (stmt := stmt) (wit := wit) (A (pks, ())) Ext pks Q f₀)
    (SignOracle.noQuery_ring hB) (fun pks p => (A (pks, ())).tracePreserving p.1)
    (fun pks p => seTwo_outer_ne B pks refuses pubOf p.2) (fun _ _ h => by cases h) hQ
    (fun keys _ => fun _ => keyReply B keys) htab
    (fun keys p => {x | forgerWinsQ (wit := wit) (A (fun i => B.pk (keys i), ())) refuses pubOf
      keys Q p.1 p.2 Psim Ext (Quantum.AdaptiveIAlg.insertTabM
        ((A (fun i => B.pk (keys i), ())).alg p.1) (simExtChallenger Psim Q)
        (seTwo B (fun i => B.pk (keys i)) refuses pubOf p.2) (fun _ => keyReply B keys)
        claimOfOut x.1.out) x.2})
    (fun keys p H c bs hbs hW => forgesReq_zkReadout (A (fun i => B.pk (keys i), ())) Ext keys Q
      f₀ _ (zkCand_of_forgerWinsQ (A (fun i => B.pk (keys i), ())) refuses pubOf keys Q p.1 p.2
        Psim Ext _ _ hW) _
      (fun q hq => zk_bridge_requests (A (fun i => B.pk (keys i), ())) refuses pubOf _ Q p.1 p.2
        Psim _ _ hbs hq) H hB.verifiesWithoutOracle)
  refine le_trans (le_of_eq ?_) hT
  refine tsum_congr fun keys => congrArg _ ?_
  have h1 : ∑ ds, PMF.uniformOfFintype (Fin Q → B.Coins) ds * ∑' a, (A.at keys).aux a *
      simProb (outEquiv k e) (extAdv Qs (seAlg A refuses pubOf keys Q a ds) Psim Q kq)
        (forgerWins A wit refuses pubOf keys Q a ds Psim Ext) =
      zkSum (wit := wit) refuses pubOf keys Q Psim Ext kq (A.at keys) := by
    rw [zkSum, ← tsum_fintype (L := .unconditional _)]
    refine tsum_congr fun ds => congrArg _ (tsum_congr fun a => congrArg _ ?_)
    have h := simProb_extAdv_seAlg_eq_zk A (wit := wit) refuses pubOf keys Q a ds Psim Ext kq
    convert h using 1
  -- the public keys spelled at `BitStr` as in `sum_simLaw_extRun_le_muEufProb_tableForger`
  have h2 : zkSum (wit := wit) refuses pubOf keys Q Psim Ext kq (A.at keys) =
      zkSum (wit := wit) refuses pubOf keys Q Psim Ext kq
        (A (fun i => @Signature.BaseScheme.pk _ (BitStr (Fin (k + e)) (Fin 8)) _ B.core (keys i), ())) :=
    congrArg (zkSum (wit := wit) refuses pubOf keys Q Psim Ext kq) rfl
  refine h1.trans (h2.trans ?_)
  rw [zkSum, ENNReal.tsum_prod']
  simp only [zkAux_apply, mul_assoc, ENNReal.tsum_mul_left]
  rw [tsum_mul_tsum_mul_comm]

end

end ZK

/-! ### The zero-knowledge route's term from MU-EUF-CMA^corr -/

section ZKBound

variable {k kN kS L e N n t : ℕ} {TB : BaseTypes} [Fintype TB.PK] [DecidableEq TB.PK]
  [Fintype TB.Msg] [DecidableEq TB.Msg]
  [Fintype TB.Pub] [DecidableEq TB.Pub] [Fintype TB.KeyCoins]
  [DecidableEq TB.KeyCoins]
  {B : BaseSigner (Bits (queryBits k kN kS L)) (XOut k e) N TB}
  {ι : Type} {τ : SPTerm ι} {Mg : Merges τ} {nr : ι → ℕ}
  {P : (j : ι) → ProtocolSpec (nr j)} [∀ j i, Fintype ((P j).Challenge i)]
  [∀ j i, DecidableEq ((P j).Challenge i)] [∀ j i, Nonempty ((P j).Challenge i)]
  {X₀ Wit₀ : Type} [DecidableEq X₀] {M : SPBCS Mg P X₀ k kN kS L e} {Λ : SiteLayout Mg} {b : ℕ}
  [∀ j i, Fintype ((M.comp j).MessageWrite i)] {E : (j : ι) → (M.comp j).Encoder}
  {Vr : X₀ → FullTr P τ → Bool} {Qs : ∀ x, M.IOPQueries Vr x}
  {hb : M.FormatBounds Qs b b} {R : Type} [Fintype R] [DecidableEq R] [Nonempty R]
  {honest : Wit₀ → R → CausalProver P τ X₀} {stmt : RingStmt B → X₀} {check : RingStmt B → Bool}
  {input : RingStmt B → RingWit B → Option Wit₀}
  {adm : KeyRing B.PK N → Prop} [DecidablePred adm] {W' : Type} [Fintype W'] [DecidableEq W']
  {fw : W' → Wit₀} {enc : RingStmt B → RelayWit B → Option W'}
  {relH : Set (X₀ × Wit₀)} {WitK : Type} {rel : Set (X₀ × WitK)}
  {wit : RingStmt B → WitK → RingWit B}
  (A : InsiderAdversary (ofBase B (Ring.spbcsComapProofSystem M Λ E hb honest stmt check input)
    adm) n (OracleView.queriesOnly (Bits (queryBits k kN kS L)) (XOut k e)) t)
  [Nonempty B.Msg] [Nonempty B.Pub] [Nonempty B.BSig] [ert : EmptyRingTest stmt]

local notation "𝒫" => Ring.spbcsComapProofSystem M Λ E hb honest stmt check input

local notation "ZAdv" => QueryBoundedAdversary (Bits (queryBits k kN kS L)) (XOut k e)
  (UnforgeRequest n (SideOracle.none (ofBase B 𝒫 adm)))
  (UnforgeResponse (SideOracle.none (ofBase B 𝒫 adm)))
  (KeyRing (RingScheme.PK (ofBase B 𝒫 adm)) N × RingScheme.Msg (ofBase B 𝒫 adm) ×
    RingScheme.Sig (ofBase B 𝒫 adm)) t

variable (Λ hb honest stmt check input adm n) in
/-- The simulator of `zkForgerSuccess`: the spBCS joint simulator `seSim` read at the statements of
the relayed requests.

Running time: that of `seSim` at the statement of the relayed request. This running time is
argued here, not proved in Lean. -/
abbrev zkPsim (VE : M.ViewEncoder E Qs) {Pub : Type} (pub : X₀ → Pub)
    (Sim : CausalJointSimulator VE.MV Pub) (T : M.Preimages) :
    NARG.Simulator (Bits (queryBits k kN kS L)) (XOut k e) (RelayStmt B 𝒫 adm n)
      (M.Response b) (SaltedCoins (FiatShamirSalt kS) (M.JointSimCoins VE.toViewRead Sim T)) :=
  (seSim (Λ := Λ) (hb := hb) (honest := honest) (stmt := stmt) (check := check) (input := input)
    VE pub Sim T).comap (stmt ∘ Prod.fst)

variable (Λ hb honest stmt check input adm n) in
/-- **The number of multi-user requests of the zero-knowledge forger** for `Q` requests and the
schedule bound `S`, `w`, `P'` (`GameAdversary.ScheduleLE`): the bridge's request points
`S · (q + w) + w · P' + kq + 1`, with `q` the simulator's queries per request and
`kq = kqOf Mg nr b b + Q · q`. -/
noncomputable def zkQ' (VE : M.ViewEncoder E Qs) {Pub : Type} (pub : X₀ → Pub)
    (Sim : CausalJointSimulator VE.MV Pub) (T : M.Preimages) (Q S w P' : ℕ) : ℕ :=
  S * ((zkPsim n Λ hb honest stmt check input adm VE pub Sim T).q + w) + w * P' +
    (kqOf Mg nr b b + Q * (zkPsim n Λ hb honest stmt check input adm VE pub Sim T).q) + 1

variable [Fintype TB.BSig] [DecidableEq TB.BSig] [Nonempty TB.KeyCoins] [Fintype TB.Coins]
  [DecidableEq TB.Coins] [Nonempty TB.Coins]

omit [Nonempty B.BSig] [Fintype R] [DecidableEq R] [Nonempty R] in
/-- **The zero-knowledge route's term is bounded by MU-EUF-CMA^corr**: for an oracle-free base
signer (`hB`) and an adversary with the schedule bound `S`, `w`, `P'` (`hS`), `zkForgerTerm` is at
most the success probability of the explicit multi-user forger `zkForger` in MU-EUF-CMA^corr with
the ring-aware signing oracle and `zkQ'` requests. -/
theorem zkForgerTerm_le_muEufProb [NeZero n] [Nonempty M.NIProof] (hB : B.OracleFree)
    (refuses : KeyRing B.PK N → ℕ → B.Msg → B.Coins → Prop) (pubOf : B.Coins → B.Pub)
    (VE : M.ViewEncoder E Qs) {Pub : Type} (pub : X₀ → Pub)
    (Sim : CausalJointSimulator VE.MV Pub) (T : M.Preimages) (Ext : CausalExtractor P τ X₀ WitK)
    (Q : ℕ) (f₀ : B.PK × B.BMsg × B.BSig) {S w P' : ℕ} (hS : GameAdversary.ScheduleLE A S w P') :
    zkForgerTerm A wit refuses pubOf VE pub Sim T Ext Q ≤
      muEufProb (zkForger A (wit := wit) refuses pubOf Q
          (zkPsim n Λ hb honest stmt check input adm VE pub Sim T) Ext (kqOf Mg nr b b) f₀)
        (zkQ' n Λ hb honest stmt check input adm VE pub Sim T Q S w P') := by
  have hQ : ∀ pks (p : (A (pks, ())).Aux × (Fin Q → B.Coins)),
      (((((A (pks, ())).alg p.1).absorbTab (seTwo B pks refuses pubOf p.2)
        (tab₀ ((A (pks, ())).alg p.1))).toTPKindAlg.composeBothOut
          (simExtChallenger (zkPsim n Λ hb honest stmt check input adm VE pub Sim T) Q) id).depth) +
        (kqOf Mg nr b b + Q * (zkPsim n Λ hb honest stmt check input adm VE pub Sim T).q) + 1 ≤
        zkQ' n Λ hb honest stmt check input adm VE pub Sim T Q S w P' := by
    intro pks p
    erw [KindAlg.composeBothOut_depth]
    rw [zkQ']
    change ((A (pks, ())).alg p.1).slots *
        ((zkPsim n Λ hb honest stmt check input adm VE pub Sim T).q +
          ((A (pks, ())).alg p.1).width) +
      ((A (pks, ())).alg p.1).width * ((A (pks, ())).alg p.1).post + _ + 1 ≤ _
    have h1 := hS.slots_le (pks, ()) p.1
    have h2 := hS.width_le (pks, ()) p.1
    have h3 := hS.post_le (pks, ()) p.1
    have := Nat.mul_le_mul h1
      (Nat.add_le_add_left h2 (zkPsim n Λ hb honest stmt check input adm VE pub Sim T).q)
    have := Nat.mul_le_mul h2 h3
    omega
  have hslots : ∀ pks (a : (A (pks, ())).Aux), ((A (pks, ())).alg a).slots ≤
      zkQ' n Λ hb honest stmt check input adm VE pub Sim T Q S w P' := by
    intro pks a
    have h1 := hS.slots_le (pks, ()) a
    have h2 := hS.width_le (pks, ()) a
    have hw : 1 ≤ w := le_trans ((A (pks, ())).alg a).width_pos h2
    rw [zkQ']
    have : S ≤ S * ((zkPsim n Λ hb honest stmt check input adm VE pub Sim T).q + w) :=
      Nat.le_mul_of_pos_right _ (by omega)
    omega
  rw [zkForgerTerm, dif_pos ⟨inferInstance, inferInstance⟩]
  have h := sum_simProb_extAdv_le_muEufProb A (wit := wit) hB refuses pubOf Q
    (zkPsim n Λ hb honest stmt check input adm VE pub Sim T) Ext (kqOf Mg nr b b) f₀ hQ
    hslots
  exact h

open Classical in
/-- **BKM06 Definition 7 for the ring signature compiled by spBCS at a program's statements, from
zero knowledge, simulation extraction and MU-EUF-CMA^corr**:
`insiderForgeProb_le_zk` with `zkForgerTerm` bounded by the success probability of the explicit
multi-user forger `zkForger` (`zkForgerTerm_le_muEufProb`), for an adversary with the schedule
bound `S`, `w`, `P'` (`hS`) and `zkQ'` multi-user requests. The forger's multi-user requests are
`publicKey 0` or corruptions among the adversary's first `Q` requests (`zk_bridge_requests`). -/
@[headline]
theorem insiderForgeProb_le_zk_muEufProb [NeZero n] [Nonempty M.NIProof] (hk : 0 < k)
    (hB : B.OracleFree)
    {refuses : KeyRing B.PK N → ℕ → B.Msg → B.Coins → Prop} {pubOf : B.Coins → B.Pub}
    (hpub : B.PubOfCoins pubOf) (href : B.RefusalOfCoins refuses) {εc : ℝ≥0∞}
    (hcorr : B.CorrectWithin εc) (hz : ZKRingHyps B adm stmt check input fw enc relH rel wit)
    (VE : M.ViewEncoder E Qs) {Pub : Type} (pub : X₀ → Pub)
    (Sim : CausalJointSimulator VE.MV Pub) (T : M.Preimages) {δ : NNReal}
    (hvzk : CausalHVZK VE.MV relH honest pub Sim δ)
    {Ext : CausalExtractor P τ X₀ WitK} {St : CausalStateFn P τ X₀}
    {ε : ChIdx P τ → NNReal} (hrbr : CausalRBRKnowledgeSound rel Vr Ext St ε)
    (Q : ℕ) (f₀ : B.PK × B.BMsg × B.BSig) {S w P' : ℕ} (hS : GameAdversary.ScheduleLE A S w P') :
    insiderForgeProb A Q ≤
      muEufProb (zkForger A (wit := wit) refuses pubOf Q
          (zkPsim n Λ hb honest stmt check input adm VE pub Sim T) Ext (kqOf Mg nr b b) f₀)
        (zkQ' n Λ hb honest stmt check input adm VE pub Sim T Q S w P') +
        ENNReal.ofReal (M.zkError δ t Q) +
        M.simExtractionError (kqOf Mg nr b b) (maxError ε)
          (M.niJointSimulatorProg Λ VE.toViewRead b pub Sim T).q t Q +
        SPBCS.knowledgeError k e (kqOf Mg nr b b)
          (t + Q * (ofBase B 𝒫 adm).q +
            kqOf Mg nr b b) M.senc.digestsPerInput Mg.nJ (maxError ε) +
        2 * Q * εc := by
  refine (insiderForgeProb_le_zk A hk hB hpub href hcorr hz VE pub Sim T hvzk hrbr Q).trans ?_
  gcongr
  exact zkForgerTerm_le_muEufProb A hB refuses pubOf VE pub Sim T Ext Q f₀ hS


open Classical in
/-- **BKM06 Definition 7 from zero knowledge, simulation extraction and MU-EUF-CMA^corr, for a base
signer whose refusals are bounded per key**: `insiderForgeProb_le_zk_refuseAt` with `zkForgerTerm`
bounded by the success probability of the explicit multi-user forger `zkForger` at the empty refusal
predicate (`zkForgerTerm_le_muEufProb`), for an adversary with the schedule bound `S`, `w`, `P'`
(`hS`) and `zkQ'` multi-user requests. -/
theorem insiderForgeProb_le_zk_muEufProb_refuseAt [NeZero n] [Nonempty M.NIProof] (hk : 0 < k)
    (hB : B.OracleFree)
    {pubOf : B.Coins → B.Pub} (hpub : B.PubOfCoins pubOf) {ρ : ℝ≥0∞} (hρ : B.RefuseAtWithin adm ρ)
    {εc : ℝ≥0∞}
    (hcorr : B.CorrectWithin εc) (hz : ZKRingHyps B adm stmt check input fw enc relH rel wit)
    (VE : M.ViewEncoder E Qs) {Pub : Type} (pub : X₀ → Pub)
    (Sim : CausalJointSimulator VE.MV Pub) (T : M.Preimages) {δ : NNReal}
    (hvzk : CausalHVZK VE.MV relH honest pub Sim δ)
    {Ext : CausalExtractor P τ X₀ WitK} {St : CausalStateFn P τ X₀}
    {ε : ChIdx P τ → NNReal} (hrbr : CausalRBRKnowledgeSound rel Vr Ext St ε)
    (Q : ℕ) (f₀ : B.PK × B.BMsg × B.BSig) {S w P' : ℕ} (hS : GameAdversary.ScheduleLE A S w P') :
    insiderForgeProb A Q ≤
      muEufProb (zkForger A (wit := wit) (fun _ _ _ _ => False) pubOf Q
          (zkPsim n Λ hb honest stmt check input adm VE pub Sim T) Ext (kqOf Mg nr b b) f₀)
        (zkQ' n Λ hb honest stmt check input adm VE pub Sim T Q S w P') +
        ENNReal.ofReal (M.zkError δ t Q) +
        M.simExtractionError (kqOf Mg nr b b) (maxError ε)
          (M.niJointSimulatorProg Λ VE.toViewRead b pub Sim T).q t Q +
        SPBCS.knowledgeError k e (kqOf Mg nr b b)
          (t + Q * (ofBase B 𝒫 adm).q +
            kqOf Mg nr b b) M.senc.digestsPerInput Mg.nJ (maxError ε) +
        2 * Q * εc + Q * ρ := by
  refine (insiderForgeProb_le_zk_refuseAt A hk hB hpub hρ hcorr hz VE pub Sim T hvzk hrbr Q).trans ?_
  gcongr
  exact zkForgerTerm_le_muEufProb A hB (fun _ _ _ _ => False) pubOf VE pub Sim T Ext Q f₀ hS

open Classical in
/-- **BKM06 Definition 7 from zero knowledge, simulation extraction and MU-EUF-CMA^corr, for a base
signer whose refusal rate is bounded on average over the honest key coins**:
`insiderForgeProb_le_zk_refuseAvg` with `zkForgerTerm` bounded by the success probability of the
explicit multi-user forger `zkForger` at the empty refusal predicate (`zkForgerTerm_le_muEufProb`),
for an adversary with the schedule bound `S`, `w`, `P'` (`hS`) and `zkQ'` multi-user requests. -/
theorem insiderForgeProb_le_zk_muEufProb_refuseAvg [NeZero n] [Nonempty M.NIProof] (hk : 0 < k)
    (hB : B.OracleFree)
    {pubOf : B.Coins → B.Pub} (hpub : B.PubOfCoins pubOf) {ρ : ℝ≥0∞} (hρ : B.RefuseAvgWithin adm ρ)
    {εc : ℝ≥0∞}
    (hcorr : B.CorrectWithin εc) (hz : ZKRingHyps B adm stmt check input fw enc relH rel wit)
    (VE : M.ViewEncoder E Qs) {Pub : Type} (pub : X₀ → Pub)
    (Sim : CausalJointSimulator VE.MV Pub) (T : M.Preimages) {δ : NNReal}
    (hvzk : CausalHVZK VE.MV relH honest pub Sim δ)
    {Ext : CausalExtractor P τ X₀ WitK} {St : CausalStateFn P τ X₀}
    {ε : ChIdx P τ → NNReal} (hrbr : CausalRBRKnowledgeSound rel Vr Ext St ε)
    (Q : ℕ) (f₀ : B.PK × B.BMsg × B.BSig) {S w P' : ℕ} (hS : GameAdversary.ScheduleLE A S w P') :
    insiderForgeProb A Q ≤
      muEufProb (zkForger A (wit := wit) (fun _ _ _ _ => False) pubOf Q
          (zkPsim n Λ hb honest stmt check input adm VE pub Sim T) Ext (kqOf Mg nr b b) f₀)
        (zkQ' n Λ hb honest stmt check input adm VE pub Sim T Q S w P') +
        ENNReal.ofReal (M.zkError δ t Q) +
        M.simExtractionError (kqOf Mg nr b b) (maxError ε)
          (M.niJointSimulatorProg Λ VE.toViewRead b pub Sim T).q t Q +
        SPBCS.knowledgeError k e (kqOf Mg nr b b)
          (t + Q * (ofBase B 𝒫 adm).q +
            kqOf Mg nr b b) M.senc.digestsPerInput Mg.nJ (maxError ε) +
        2 * Q * εc + Q * (n * ρ) := by
  refine (insiderForgeProb_le_zk_refuseAvg A hk hB hpub hρ hcorr hz VE pub Sim T hvzk hrbr Q).trans ?_
  gcongr
  exact zkForgerTerm_le_muEufProb A hB (fun _ _ _ _ => False) pubOf VE pub Sim T Ext Q f₀ hS

end ZKBound

/-! ### The identity reading -/

section Identity

variable {k kN kS L e N n t : ℕ} {TB : BaseTypes}
  {B : BaseSigner (Bits (queryBits k kN kS L)) (XOut k e) N TB}
  {ι : Type} {τ : SPTerm ι} {Mg : Merges τ} {nr : ι → ℕ}
  {P : (j : ι) → ProtocolSpec (nr j)} [∀ j i, Fintype ((P j).Challenge i)]
  [∀ j i, DecidableEq ((P j).Challenge i)] [∀ j i, Nonempty ((P j).Challenge i)]
  {M : SPBCS Mg P (RingStmt B) k kN kS L e} {Λ : SiteLayout Mg} {b : ℕ}
  [∀ j i, Fintype ((M.comp j).MessageWrite i)] {E : (j : ι) → (M.comp j).Encoder}
  {Vr : RingStmt B → FullTr P τ → Bool} {Qs : ∀ x, M.IOPQueries Vr x}
  {hb : M.FormatBounds Qs b b} {R : Type} [Fintype R] [DecidableEq R] [Nonempty R]
  {honest : RingWit B → R → CausalProver P τ (RingStmt B)}
  {adm : KeyRing B.PK N → Prop} [DecidablePred adm]
  [Nonempty B.Msg] [Nonempty B.Pub] [Nonempty B.BSig]

variable [Fintype TB.PK] [DecidableEq TB.PK] [Fintype TB.Msg] [DecidableEq TB.Msg] [Fintype TB.BSig]
  [DecidableEq TB.BSig] [Fintype TB.Pub] [DecidableEq TB.Pub] [Fintype TB.KeyCoins]
  [DecidableEq TB.KeyCoins] [Nonempty TB.KeyCoins] [Fintype TB.Coins] [DecidableEq TB.Coins]
  [Nonempty TB.Coins]

open Classical in
/-- **BKM06 Definition 7 for the ring signature compiled by spBCS (`spbcsProofSystem`), from zero
knowledge, simulation extraction and MU-EUF-CMA^corr**: `insiderForgeProb_le_zk_muEufProb` at the
identity reading of ring statements (`zkRingHyps_id`), the composite over ring statements
honest-verifier zero knowledge and round-by-round knowledge sound for the ring relation, for an
adversary with the schedule bound `S`, `w`, `P'` (`hS`) and `zkQ'` multi-user requests. The forger's
multi-user requests are `publicKey 0` or corruptions among the adversary's first `Q` requests
(`zk_bridge_requests`). -/
@[headline]
theorem insiderForgeProb_le_zk_muEufProb_spbcs [NeZero n] [Nonempty M.NIProof] (hk : 0 < k)
    (hB : B.OracleFree)
    {refuses : KeyRing B.PK N → ℕ → B.Msg → B.Coins → Prop} {pubOf : B.Coins → B.Pub}
    (hpub : B.PubOfCoins pubOf) (href : B.RefusalOfCoins refuses) {εc : ℝ≥0∞}
    (hcorr : B.CorrectWithin εc) (VE : M.ViewEncoder E Qs) {Pub : Type} (pub : RingStmt B → Pub)
    (Sim : CausalJointSimulator VE.MV Pub) (T : M.Preimages) {δ : NNReal}
    (hvzk : CausalHVZK VE.MV (ringRel B adm 0) honest pub Sim δ)
    {Ext : CausalExtractor P τ (RingStmt B) (RingWit B)} {St : CausalStateFn P τ (RingStmt B)}
    {ε : ChIdx P τ → NNReal} (hrbr : CausalRBRKnowledgeSound (ringRel B adm 0) Vr Ext St ε)
    (A : InsiderAdversary (ofBase B (Ring.spbcsProofSystem M Λ E hb honest) adm) n
      (OracleView.queriesOnly (Bits (queryBits k kN kS L)) (XOut k e)) t) (Q : ℕ)
    (f₀ : B.PK × B.BMsg × B.BSig) {S w P' : ℕ} (hS : GameAdversary.ScheduleLE A S w P') :
    insiderForgeProb A Q ≤
      muEufProb (zkForger (stmt := id) (check := fun _ => true) (input := fun _ w => some w) A
          (wit := fun _ w => w) refuses pubOf Q
          (zkPsim n Λ hb honest id (fun _ => true) (fun _ w => some w) adm VE pub Sim T) Ext
          (kqOf Mg nr b b) f₀)
        (zkQ' n Λ hb honest id (fun _ => true) (fun _ w => some w) adm VE pub Sim T Q S w P') +
        ENNReal.ofReal (M.zkError δ t Q) +
        M.simExtractionError (kqOf Mg nr b b) (maxError ε)
          (M.niJointSimulatorProg Λ VE.toViewRead b pub Sim T).q t Q +
        SPBCS.knowledgeError k e (kqOf Mg nr b b)
          (t + Q * (ofBase B (Ring.spbcsProofSystem M Λ E hb honest) adm).q + kqOf Mg nr b b)
          M.senc.digestsPerInput Mg.nJ (maxError ε) +
        2 * Q * εc :=
  insiderForgeProb_le_zk_muEufProb (stmt := id) (check := fun _ => true)
    (input := fun _ w => some w) A hk hB hpub href hcorr (zkRingHyps_id B adm) VE pub Sim T hvzk
    hrbr Q f₀ hS

end Identity

end RingSignature.Insider

end GordieHowe
