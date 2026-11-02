-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Interactive.RelayBlockRel
public import GordieHowe.Model.Quantum.Interactive.AbortBlock
public import GordieHowe.Model.Quantum.Interactive.MultiRelay

@[expose] public section

/-!
# The relayed distinguisher with programs of the same shape

For programs `p'` of the same shape as a relay `F`'s (`MultiRelay.SameShape`), the relayed
distinguisher with `p'` as an adversary is the one with `F`'s programs with other Kraus maps, and
so is the relayed adversary (`AdaptiveIAlg.relayAdv`, its aborting completion):

- `Distinguisher.toAdaptive_relay_withProg`, `AdaptiveIAlg.relayAdv_withProg`: the relayed
  distinguisher as an adversary, and the relayed adversary, with `p'`'s programs.
- **`AdaptiveIAlg.blockRel_relayAdv`**, **`AdaptiveIAlg.blockNone_relayAdv`**: the block
  hypotheses (`Distinguisher.blockRel_relay`, `Distinguisher.blockNone_relay`) of the relayed
  adversaries of an adversary `A`, through the aborting completion (`AdaptiveIAlg.BlockRel.toTP`,
  `AdaptiveIAlg.BlockNone.toTP`), the label, sets and permutations read past the query counter.
-/

set_option linter.unusedSectionVars false

namespace GordieHowe.Quantum

open GordieHowe.QROM

namespace Distinguisher

variable {W X Y Req Resp Req' Resp' Xs Ys : Type} [Fintype W] [DecidableEq W] [Fintype X]
  [DecidableEq X] [Fintype Y] [DecidableEq Y] [Fintype Req] [DecidableEq Req] [Fintype Resp]
  [DecidableEq Resp] [Fintype Req'] [DecidableEq Req'] [Fintype Resp'] [DecidableEq Resp']
  [Inhabited X] [Inhabited Req'] [AddGroup Y] [AddGroup Ys] [Fintype Ys] [DecidableEq Ys] {n m : ℕ}
  (D : Distinguisher W X Y Req Resp n m) {F : MultiRelay X Y Req Resp Req' Resp' Xs Ys} (b Q : ℕ)

/-- **The relayed distinguisher with programs of the same shape**, as an adversary, is the one
with `F`'s programs with other Kraus maps. -/
theorem toAdaptive_relay_withProg
    {p' : Req → OracleProg ((X ⊕ Xs) ⊕ Req') ((Y ⊕ Ys) ⊕ Option Resp') (Option Resp)}
    (hS : F.SameShape p') (q : ℕ) {O : Type}
    (out : RelayW (DReg W n X Y Req Resp) Req Resp' X Y m (relaySlots n m F) (Fin F.qS → Ys) → O) :
    (D.relay (F.withProg p') b Q).toAdaptive Nat.one_pos q out =
      ((D.relay F b Q).toAdaptive Nat.one_pos q out).withStep
        ((D.relay (F.withProg p') b Q).toAdaptive Nat.one_pos q out).step := by
  have hk : (D.relay (F.withProg p') b Q).kind = (D.relay F b Q).kind :=
    funext fun w => MultiRelay.isAsk_actAt_shape hS w.record w.store w.side w.time
  unfold toAdaptive AdaptiveIAlg.withStep
  simp only
  rw [hk]
  rfl

end Distinguisher

namespace AdaptiveIAlg

open Distinguisher

variable {X Y Req Resp O : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp]
  {shA : AlgShape X Y Req Resp} (A : AdaptiveIAlg shA O) [AddGroup Y]


variable {Req' Resp' O' Xs Ys : Type} [Fintype Req'] [DecidableEq Req'] [Fintype Resp']
  [DecidableEq Resp'] [Inhabited X] [Inhabited Req'] [AddGroup Ys] [Fintype Ys] [DecidableEq Ys]
  {F : MultiRelay X Y Req Resp Req' Resp' Xs Ys} (Q : ℕ)
  {p' : Req → OracleProg ((X ⊕ Xs) ⊕ Req') ((Y ⊕ Ys) ⊕ Option Resp') (Option Resp)}

/-- **The relayed adversary with programs of the same shape** is the one with `F`'s programs with
the steps of the relayed distinguisher with `p'`'s read through the aborting completion. -/
theorem relayAdv_withProg (hS : F.SameShape p') (out' : A.RelayWS F → O') :
    A.relayAdv (F.withProg p') Q out' = (A.relayAdv F Q out').withStep
      (((A.relayD F Q).toAdaptive Nat.one_pos (A.relayBudget F Q) out').abortStep
        ((A.relayD (F.withProg p') Q).toAdaptive Nat.one_pos (A.relayBudget F Q) out').step) := by
  rw [A.relayAdv_eq (F.withProg p') Q out', A.relayAdv_eq F Q out']
  rw [A.relayD_eq F Q, A.relayD_eq (F.withProg p') Q]
  exact (congrArg AdaptiveIAlg.abortAlg (toAdaptive_relay_withProg A.pureD (A.budget + A.post) Q
    hS (A.relayBudget F Q) out')).trans (abortAlg_withStep _ _)

variable {J : Req → Bool} {sw : Equiv.Perm Req'} {swO : Equiv.Perm Resp}
  {Gin : List (Option Req) → Set (((A.toTPKindAlg true).unitOut.DW × Bool) × Req × Option Resp)}
  {πin : List (Option Req) → Equiv.Perm (((A.toTPKindAlg true).unitOut.DW × Bool) × Req × Option Resp)}

/-- **The block hypotheses of the relayed adversaries** of `A` with `F`'s and with `p'`'s programs
(`Distinguisher.blockRel_relay`, through the aborting completion): the second is the first with
the steps of `relayAdv_withProg`. -/
theorem blockRel_relayAdv (hn : 0 < (A.toTPKindAlg true).unitOut.width) (hI : InnerSupp J Gin A.pureD)
    (hIH : InnerSwap A.pureD πin Gin) (hS : F.SameShape p') {r₀ : Req}
    (h : F.ProgSwap p' J (· = r₀) sw swO) (hidle : sw F.idle = F.idle)
    (hdef : sw default = default) (hπ : RespSw (A.budget + A.post) Q J swO πin)
    (hk : ∀ es w q a, A.pureD.kind (πin es (w, q, a)).1 = A.pureD.kind w)
    (hrq : ∀ es w q a, (πin es (w, q, a)).2.1 = q)
    (hGπ : ∀ es x, πin es x ∈ Gin es ↔ x ∈ Gin es) (hπ0 : ∀ x, πin [] x = x)
    (out' : A.RelayWS F → O') :
    (A.relayAdv F Q out').BlockRel
      (((A.relayD F Q).toAdaptive Nat.one_pos (A.relayBudget F Q) out').abortStep
        ((A.relayD (F.withProg p') Q).toAdaptive Nat.one_pos (A.relayBudget F Q) out').step)
      (fun w => jLabel F J w.1)
      (fun k => ((A.relayD F Q).toAdaptive Nat.one_pos (A.relayBudget F Q) out').cntSet
        (GoodAt F (A.budget + A.post) Q J Gin k))
      (fun k => ((A.relayD F Q).toAdaptive Nat.one_pos (A.relayBudget F Q) out').cntSet
        (GoodAt (F.withProg p') (A.budget + A.post) Q J Gin k))
      (((A.relayD F Q).toAdaptive Nat.one_pos (A.relayBudget F Q) out').cntSet (Good₀ F Gin))
      (((A.relayD F Q).toAdaptive Nat.one_pos (A.relayBudget F Q) out').cntSet
        (Good₀ (F.withProg p') Gin))
      (fun _ => ((A.relayD F Q).toAdaptive Nat.one_pos (A.relayBudget F Q) out').cntOne
        (relSwT F p' (A.budget + A.post) Q J (· = r₀) sw πin))
      (((A.relayD F Q).toAdaptive Nat.one_pos (A.relayBudget F Q) out').cntOne
        (relSwT F p' (A.budget + A.post) Q J (· = r₀) sw πin)) r₀ := by
  simp only [AdaptiveIAlg.relayAdv_eq]
  rw [A.relayD_eq F Q, A.relayD_eq (F.withProg p') Q]
  have hB := blockRel_relay (F := F) (b := A.budget + A.post) (Q := Q) A.pureD hn hI hIH hS h
    hidle hdef hπ hk hrq hGπ hπ0 (A.relayBudget F Q) out' out'
  have hA' : (((A.relayD F Q).toAdaptive Nat.one_pos (A.relayBudget F Q) out').withStep
      ((A.relayD (F.withProg p') Q).toAdaptive Nat.one_pos (A.relayBudget F Q)
        out').step).TracePreserving := by
    rw [A.relayD_eq F Q, A.relayD_eq (F.withProg p') Q]
    erw [← toAdaptive_relay_withProg A.pureD (A.budget + A.post) Q hS]
    exact toAdaptive_tracePreserving _ _ _ _
  rw [A.relayD_eq F Q, A.relayD_eq (F.withProg p') Q] at hA'
  exact AdaptiveIAlg.BlockRel.toTP (hA := toAdaptive_tracePreserving _ _ _ _) (hA' := hA')
    (h := hB)

/-- **The `none`-block hypotheses of the relayed adversaries** of `A` with `F`'s and with `p'`'s
programs, equal off `J` (`Distinguisher.blockNone_relay`, through the aborting completion). -/
theorem blockNone_relayAdv (hn : 0 < (A.toTPKindAlg true).unitOut.width) (hI : InnerSupp J Gin A.pureD)
    (hS : F.SameShape p') (hoff : ∀ r, J r = false → p' r = F.prog r)
    (out' : A.RelayWS F → O') :
    (A.relayAdv F Q out').BlockNone
      (((A.relayD F Q).toAdaptive Nat.one_pos (A.relayBudget F Q) out').abortStep
        ((A.relayD (F.withProg p') Q).toAdaptive Nat.one_pos (A.relayBudget F Q) out').step)
      (fun w => jLabel F J w.1)
      (fun k => ((A.relayD F Q).toAdaptive Nat.one_pos (A.relayBudget F Q) out').cntSet
        (GoodAt F (A.budget + A.post) Q J Gin k))
      (fun k => ((A.relayD F Q).toAdaptive Nat.one_pos (A.relayBudget F Q) out').cntSet
        (GoodAt (F.withProg p') (A.budget + A.post) Q J Gin k))
      (((A.relayD F Q).toAdaptive Nat.one_pos (A.relayBudget F Q) out').cntSet (Good₀ F Gin))
      (((A.relayD F Q).toAdaptive Nat.one_pos (A.relayBudget F Q) out').cntSet
        (Good₀ (F.withProg p') Gin)) := by
  simp only [AdaptiveIAlg.relayAdv_eq]
  rw [A.relayD_eq F Q, A.relayD_eq (F.withProg p') Q]
  have hB := blockNone_relay (F := F) (b := A.budget + A.post) (Q := Q) A.pureD hn hI hoff
    (A.relayBudget F Q) out' out'
  have hA' : (((A.relayD F Q).toAdaptive Nat.one_pos (A.relayBudget F Q) out').withStep
      ((A.relayD (F.withProg p') Q).toAdaptive Nat.one_pos (A.relayBudget F Q)
        out').step).TracePreserving := by
    rw [A.relayD_eq F Q, A.relayD_eq (F.withProg p') Q]
    erw [← toAdaptive_relay_withProg A.pureD (A.budget + A.post) Q hS]
    exact toAdaptive_tracePreserving _ _ _ _
  rw [A.relayD_eq F Q, A.relayD_eq (F.withProg p') Q] at hA'
  exact AdaptiveIAlg.BlockNone.toTP (hA := toAdaptive_tracePreserving _ _ _ _) (hA' := hA')
    (h := hB)

end AdaptiveIAlg

end GordieHowe.Quantum
