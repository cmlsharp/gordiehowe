-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Interactive.RelayBlockInner
public import GordieHowe.Model.Quantum.Interactive.RelayBlockAdv
public import GordieHowe.Applications.Ring.KeyFreeBlock

@[expose] public section

/-!
# The block hypotheses of the absorbed adversary

For assigning relays `G`, `G'` whose multi-request relays differ by the programs `p'`
(`G'.relayOf Q = (G.relayOf Q).withProg p'`), the adversary with `G'` absorbed is the adversary
with `G` absorbed with the aborting steps of `relayAdv_withProg`
(`AdaptiveIAlg.absorbAssign_eq_withStep`). At the base part and with another output, the two
satisfy the block hypotheses (`AdaptiveIAlg.blockRel_absorbAssign`,
`AdaptiveIAlg.blockNone_absorbAssign`), along the inner tower of `RelayBlockInner`.
-/

namespace GordieHowe.Quantum

open GordieHowe.QROM

/-- **A permutation mapping a set of a finite type into itself maps it onto itself.** -/
theorem perm_mem_iff_of_mapsTo {α : Type} [Finite α] (π : Equiv.Perm α) {S : Set α}
    (h : ∀ x ∈ S, π x ∈ S) (x : α) : π x ∈ S ↔ x ∈ S := by
  refine ⟨fun hx => ?_, h x⟩
  have hb := (S.toFinite.injOn_iff_bijOn_of_mapsTo h).1 π.injective.injOn
  obtain ⟨z, hz, hzx⟩ := hb.surjOn hx
  rwa [π.injective hzx] at hz

/-- **The swap condition of a distinguisher does not depend on the equality decision of its
workspace.** -/
theorem innerSwap_inst {W X Y Req Resp : Type} [Fintype W] [Fintype X] [DecidableEq X] [Fintype Y]
    [DecidableEq Y] [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp] {n m : ℕ}
    (i i' : DecidableEq W) {D : Distinguisher W X Y Req Resp n m}
    {πin : List (Option Req) → Equiv.Perm (W × Req × Option Resp)}
    {Gin : List (Option Req) → Set (W × Req × Option Resp)}
    (h : letI := i; Distinguisher.InnerSwap D πin Gin) :
    letI := i'; Distinguisher.InnerSwap D πin Gin := by
  cases Subsingleton.elim i i'
  exact h

namespace AdaptiveIAlg

open Distinguisher

section Generic

variable {X Y Req Resp O : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp]
  {shA : AlgShape X Y Req Resp} (A : AdaptiveIAlg shA O) [AddGroup Y]

open Classical

variable {Req' Resp' O' Xs Ys : Type} [Fintype Req'] [DecidableEq Req'] [Fintype Resp']
  [DecidableEq Resp'] [Inhabited X] [Inhabited Req'] [AddGroup Ys] [Fintype Ys] [DecidableEq Ys]
  (F : MultiRelay X Y Req Resp Req' Resp' Xs Ys) (Q : ℕ)
  (p' : Req → OracleProg ((X ⊕ Xs) ⊕ Req') ((Y ⊕ Ys) ⊕ Option Resp') (Option Resp))
  (out' : A.RelayWS F → O')

/-- **The steps of the relayed adversary with the programs `p'`**, read on the relayed adversary
with `F`'s programs (`relayAdv_withProg`). -/
noncomputable def relayStepWith : StepIdx (A.relayAdv F Q out').slots (A.relayAdv F Q out').post →
    KrausMap (A.relayAdv F Q out').R
      (DReg (A.relayAdv F Q out').W (A.relayAdv F Q out').width X Y Req' Resp')
      (DReg (A.relayAdv F Q out').W (A.relayAdv F Q out').width X Y Req' Resp') :=
  ((A.relayD F Q).toAdaptive Nat.one_pos (A.relayBudget F Q) out').abortStep
    ((A.relayD (F.withProg p') Q).toAdaptive Nat.one_pos (A.relayBudget F Q) out').step

variable (p'' : Req → OracleProg ((X ⊕ Xs) ⊕ Req') ((Y ⊕ Ys) ⊕ Option Resp') (Option Resp))
  (J : Req → Bool)
  (Gin : List (Option Req) → Set (((A.toTPKindAlg true).unitOut.DW × Bool) × Req × Option Resp))

/-- **The well-formed registers of the relayed adversary after step `k`** for the programs `p''`
(`GoodAt`, with the query counter). -/
noncomputable def relayGoodAt (k : ℕ) :
    Set ((A.relayAdv F Q out').W × Req' × Option Resp') :=
  ((A.relayD F Q).toAdaptive Nat.one_pos (A.relayBudget F Q) out').cntSet
    (GoodAt (F.withProg p'') (A.budget + A.post) Q J Gin k)

/-- **The well-formed initial registers of the relayed adversary** for the programs `p''` (`Good₀`,
with the query counter). -/
noncomputable def relayGood₀ : Set ((A.relayAdv F Q out').W × Req' × Option Resp') :=
  ((A.relayD F Q).toAdaptive Nat.one_pos (A.relayBudget F Q) out').cntSet
    (Good₀ (F.withProg p'') Gin)

/-- **The swap of the relayed adversary's registers** (`relSwT`, with the query counter). -/
noncomputable def relaySwap (P : Req → Prop) [DecidablePred P] (sw : Equiv.Perm Req')
    (πin : List (Option Req) →
      Equiv.Perm (((A.toTPKindAlg true).unitOut.DW × Bool) × Req × Option Resp)) :
    Equiv.Perm ((A.relayAdv F Q out').W × Req' × Option Resp') :=
  ((A.relayD F Q).toAdaptive Nat.one_pos (A.relayBudget F Q) out').cntOne
    (relSwT F p' (A.budget + A.post) Q J P sw πin)

/-- `relayGoodAt` at `F`'s own programs. -/
theorem relayGoodAt_prog (k : ℕ) : A.relayGoodAt F Q out' F.prog J Gin k =
    ((A.relayD F Q).toAdaptive Nat.one_pos (A.relayBudget F Q) out').cntSet
      (GoodAt F (A.budget + A.post) Q J Gin k) :=
  rfl

/-- `relayGood₀` at `F`'s own programs. -/
theorem relayGood₀_prog : A.relayGood₀ F Q out' F.prog Gin =
    ((A.relayD F Q).toAdaptive Nat.one_pos (A.relayBudget F Q) out').cntSet (Good₀ F Gin) :=
  rfl

end Generic

open Classical

variable {X Y Req Resp O O' Req' Resp' Xs Ys : Type} [Fintype X] [DecidableEq X] [Fintype Y]
  [DecidableEq Y] [AddGroup Ys] [Fintype Ys] [DecidableEq Ys]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp] [Fintype Req']
  [DecidableEq Req'] [Fintype Resp'] [DecidableEq Resp'] [Inhabited Req] [Inhabited X]
  [Inhabited Req'] [Nonempty X] [AddGroup Y] [Nonempty Y]
  {shA : AlgShape X Y Req Resp} (A : AdaptiveIAlg shA O) {G G' : AssignRelay X Y Req Resp Req' Resp' Xs Ys} {Q : ℕ}
  {p' : (Req × Fin (Q + 1)) × (X → Option Y) → OracleProg ((X ⊕ Xs) ⊕ Req') ((Y ⊕ Ys) ⊕
    Option Resp') (Option (AssignRelay.RespD X Y Resp Req' Resp'))}

set_option quotPrecheck false in
/-- The relayed absorbed adversary's steps with the programs `p'`. -/
local notation "STp" => (A.absorbAssignP Req' Resp' Q).relayStepWith (G.relayOf Q) Q p'
  ((A.absorbAssignP Req' Resp' Q).relayOut (G.relayOf Q))

set_option quotPrecheck false in
/-- The output of the relayed absorbed adversary. -/
local notation "OUT" => (A.absorbAssignP Req' Resp' Q).relayOut (G.relayOf Q)

set_option quotPrecheck false in
/-- The query bound of the absorbed adversary's relay. -/
local notation "BR" => (A.absorbAssignP Req' Resp' Q).budget + (A.absorbAssignP Req' Resp' Q).post

-- TODO(unbundle-M4): instance at `absorbAssignP`; state over {W} {n} (R6) or register the instance
-- on M1b's named type
omit [AddGroup Ys] [Inhabited Req] [Inhabited X] [Inhabited Req'] [Nonempty X] [AddGroup Y]
  [Nonempty Y] in
/-- The ancilla of the dilated frozen trace-preserving form of `absorbAssignP`, with the halting
flag, is finite, as one instance built in steps (one instance search for it exceeds the default
size limit of instance search). -/
noncomputable instance instFintypeAbsDAnc (Q : ℕ) :
    Fintype (Bool × ((A.absorbAssignP Req' Resp' Q).toTPKindAlg true).unitOut.DAnc) :=
  haveI : Fintype ((A.absorbAssignP Req' Resp' Q).toTPKindAlg true).unitOut.G := inferInstance
  inferInstance

omit [AddGroup Ys] [Inhabited Req] [Inhabited X] [Inhabited Req'] [Nonempty X] [AddGroup Y]
  [Nonempty Y] in
/-- **The shape of the adversary with `G'` absorbed is that with `G` absorbed**, for relays of `G'`
that are `G`'s with other programs (`withProg` keeps the read, side read and pad numbers). -/
theorem absorbAssignS_eq_of_relayOf (hG : G'.relayOf Q = (G.relayOf Q).withProg p') :
    shA.absorbAssignS (Req' := Req') (Resp' := Resp') Ys Q G'.qG G'.qP G'.qS =
      shA.absorbAssignS Ys Q G.qG G.qP G.qS := by
  have h₁ : G'.qG = G.qG := congrArg MultiRelay.qR hG
  have h₂ : G'.qP = G.qP := congrArg MultiRelay.qP hG
  have h₃ : G'.qS = G.qS := congrArg MultiRelay.qS hG
  rw [h₁, h₂, h₃]

/-- **The adversary with `G'` absorbed is the adversary with `G` absorbed with other steps**, the
aborting steps of `relayAdv_withProg`, for relays of `G'` with the programs `p'` of the same
shape. -/
-- TODO(unbundle-M4): the shape of `absorbAssign G'` carries `G'`'s numbers, equal to `G`'s only
-- propositionally, so the two adversaries have different types and are compared by `HEq`
theorem absorbAssign_eq_withStep (hG : G'.relayOf Q = (G.relayOf Q).withProg p')
    (hS : (G.relayOf Q).SameShape p') :
    A.absorbAssign G' Q ≍ (A.absorbAssign G Q).withStep STp := by
  have key : ∀ F', F' = (G.relayOf Q).withProg p' →
      (A.absorbAssignP Req' Resp' Q).relayAdv F' Q ((A.absorbAssignP Req' Resp' Q).relayOut F') ≍
        (A.absorbAssign G Q).withStep STp := by
    rintro F' rfl
    exact heq_of_eq (relayAdv_withProg (A.absorbAssignP Req' Resp' Q) Q hS _)
  exact key _ hG

variable {Y₁ Y₂ : Type} [Fintype Y₁] [DecidableEq Y₁] [Fintype Y₂] [DecidableEq Y₂]
  [AddGroup Y₁] [AddGroup Y₂] (sp : Y ≃+ Y₁ × Y₂) (H₁ : X → Y₁) (f : O × (X → Option Y) → O')
  {j : ℕ} {sw : Equiv.Perm Req'} {swO : Equiv.Perm (AssignRelay.RespD X Y Resp Req' Resp')}
  {r₀ : (Req × Fin (Q + 1)) × (X → Option Y)}

set_option quotPrecheck false in
/-- The inner swap of the absorbed adversary's relay. -/
local notation "PI" =>
  A.innerπ Q (E := Bool × ((A.absorbAssignP Req' Resp' Q).toTPKindAlg true).unitOut.DAnc)
  (c := (A.absorbAssignP Req' Resp' Q).budget + 2) j BR swO

/-- **The block hypotheses of the absorbed adversaries** with `G`'s and with `p'`'s programs, at
the base part `H₁` and with the output `f`, for a trace-preserving `A`, a block `j < Q` and a swap
`sw`, `swO` of the programs on the request `r₀` (`blockRel_relayAdv` on the inner tower). -/
theorem blockRel_absorbAssign (h : A.TracePreserving) (hj : j < Q)
    (hS : (G.relayOf Q).SameShape p')
    (hP : (G.relayOf Q).ProgSwap p' (jTest Q j) (· = r₀) sw swO)
    (hidle : sw (G.relayOf Q).idle = (G.relayOf Q).idle) (hdef : sw default = default)
    (hswO : ∀ x, (swO x).1 = x.1 ∧ (swO x).2.1 = x.2.1) :
    ((A.absorbAssign G Q).restrictAt sp H₁).mapOut f |>.BlockRel
      ((A.absorbAssign G Q).restrictStep STp sp H₁)
      (fun w => jLabel (G.relayOf Q) (jTest Q j) w.1.1)
      (fun n => (A.absorbAssign G Q).restrictSet sp H₁
        ((A.absorbAssignP Req' Resp' Q).relayGoodAt (G.relayOf Q) Q OUT (G.relayOf Q).prog (jTest Q
            j)
          (A.innerGin Req' Resp' Q j) n))
      (fun n => (A.absorbAssign G Q).restrictSet sp H₁
        ((A.absorbAssignP Req' Resp' Q).relayGoodAt (G.relayOf Q) Q OUT p' (jTest Q j)
          (A.innerGin Req' Resp' Q j) n))
      ((A.absorbAssign G Q).restrictSet sp H₁
        ((A.absorbAssignP Req' Resp' Q).relayGood₀ (G.relayOf Q) Q OUT (G.relayOf Q).prog
          (A.innerGin Req' Resp' Q j)))
      ((A.absorbAssign G Q).restrictSet sp H₁
        ((A.absorbAssignP Req' Resp' Q).relayGood₀ (G.relayOf Q) Q OUT p' (A.innerGin Req' Resp' Q
            j)))
      (fun _ => (A.absorbAssign G Q).restrictTrip sp H₁
        ((A.absorbAssignP Req' Resp' Q).relaySwap (G.relayOf Q) Q p' OUT (jTest Q j) (· = r₀) sw
          (PI)))
      ((A.absorbAssign G Q).restrictTrip sp H₁
        ((A.absorbAssignP Req' Resp' Q).relaySwap (G.relayOf Q) Q p' OUT (jTest Q j) (· = r₀) sw
          (PI))) r₀ := by
  have hR := blockRel_relayAdv (A := A.absorbAssignP Req' Resp' Q) (F := G.relayOf Q) (Q := Q)
    (J := jTest Q j)
    (Gin := A.innerGin Req' Resp' Q j)
    (πin := PI)
    ((A.absorbAssignP Req' Resp' Q).toTPKindAlg true).unitOut.width_pos
    (by convert A.innerSupp_pureD (Req' := Req') (Resp' := Resp') Q j h hj)
    (innerSwap_inst _ _ <| A.innerSwap_pureD Q j (BR) swO h hj hswO)
    hS hP hidle hdef
    (A.respSw_innerπ Q
      (E := Bool × ((A.absorbAssignP Req' Resp' Q).toTPKindAlg true).unitOut.DAnc)
      (c := (A.absorbAssignP Req' Resp' Q).budget + 2) j (BR) swO)
    (A.innerπ_kind_pureD Q j (BR) swO)
    (fun es w q a => A.innerπ_request Q
      (E := Bool × ((A.absorbAssignP Req' Resp' Q).toTPKindAlg true).unitOut.DAnc)
      (c := (A.absorbAssignP Req' Resp' Q).budget + 2) j (BR) swO es (w, q, a))
    (fun es x => perm_mem_iff_of_mapsTo _
      (A.innerGin_innerπ Q j (BR) swO (fun x => (hswO x).2) es)
      x)
    (fun x => by rw [A.innerπ_nil]; rfl) OUT
  simp -proj only [relayGoodAt_prog, relayGood₀_prog]
  unfold absorbAssign relayStepWith relayGoodAt relayGood₀ relaySwap
  exact (BlockRel.restrictAt sp H₁ hR).mapOut f

/-- **The block hypotheses without a label of the absorbed adversaries** with `G`'s and with
`p'`'s programs, at the base part `H₁` and with the output `f`, for a trace-preserving `A`, a
block `j < Q` and programs `p'` equal to `G`'s off the test (`blockNone_relayAdv`). -/
theorem blockNone_absorbAssign (h : A.TracePreserving) (hj : j < Q)
    (hS : (G.relayOf Q).SameShape p')
    (hoff : ∀ r, jTest Q j r = false → p' r = (G.relayOf Q).prog r) :
    ((A.absorbAssign G Q).restrictAt sp H₁).mapOut f |>.BlockNone
      ((A.absorbAssign G Q).restrictStep STp sp H₁)
      (fun w => jLabel (G.relayOf Q) (jTest Q j) w.1.1)
      (fun n => (A.absorbAssign G Q).restrictSet sp H₁
        ((A.absorbAssignP Req' Resp' Q).relayGoodAt (G.relayOf Q) Q OUT (G.relayOf Q).prog (jTest Q
            j)
          (A.innerGin Req' Resp' Q j) n))
      (fun n => (A.absorbAssign G Q).restrictSet sp H₁
        ((A.absorbAssignP Req' Resp' Q).relayGoodAt (G.relayOf Q) Q OUT p' (jTest Q j)
          (A.innerGin Req' Resp' Q j) n))
      ((A.absorbAssign G Q).restrictSet sp H₁
        ((A.absorbAssignP Req' Resp' Q).relayGood₀ (G.relayOf Q) Q OUT (G.relayOf Q).prog
          (A.innerGin Req' Resp' Q j)))
      ((A.absorbAssign G Q).restrictSet sp H₁
        ((A.absorbAssignP Req' Resp' Q).relayGood₀ (G.relayOf Q) Q OUT p' (A.innerGin Req' Resp' Q
            j))) := by
  have hR := blockNone_relayAdv (A := A.absorbAssignP Req' Resp' Q) (F := G.relayOf Q) (Q := Q)
    (J := jTest Q j)
    (Gin := A.innerGin Req' Resp' Q j) ((A.absorbAssignP Req' Resp' Q).toTPKindAlg
        true).unitOut.width_pos
    (by convert A.innerSupp_pureD (Req' := Req') (Resp' := Resp') Q j h hj) hS hoff OUT
  simp -proj only [relayGoodAt_prog, relayGood₀_prog]
  exact (BlockNone.restrictAt sp H₁ hR).mapOut f

end AdaptiveIAlg

end GordieHowe.Quantum
