-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Interactive.ExtRunLogs
public import GordieHowe.Model.Quantum.Interactive.RelayBlockRel

@[expose] public section

/-!
# The well-formed registers of the relayed adversary, on its own steps

For a test `J` of the requests and sets `Gin` of the distinguisher's registers carried by its
steps (`Distinguisher.InnerSupp`), the relayed adversary's own steps keep the relay's well-formed
registers (`Distinguisher.GoodAt`, `Distinguisher.relay_step_good`), read past the aborting
completion's counter. In particular the relay's record is tagged (`MultiRelay.JTagged`): at
most one of its entries is a request satisfying `J`.

- `LogInvRaw.inter`: sets carried by the steps are carried together.
- `AdaptiveIAlg.RelayGood`: the well-formed registers before each step, on the workspace and the
  request register.
- `AdaptiveIAlg.relayAdv_step_unitary`: a nonzero entry of a step of the relayed adversary is one
  of the relayed distinguisher's step, the counter dropped.
- `AdaptiveIAlg.relayAdv_logInvRaw_good`: the steps carry `RelayGood`.
- `AdaptiveIAlg.jTagged_of_relayGood`: after the first step, the record is tagged.
-/

open Matrix
open scoped BigOperators

namespace GordieHowe.Quantum

open GordieHowe.QROM

namespace AdaptiveIAlg

/-- **Sets carried by the adversary's steps are carried together.** -/
theorem LogInvRaw.inter {X Y Req Resp O : Type} [Fintype X] [DecidableEq X] [Fintype Y]
    [DecidableEq Y] [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp]
    {shA : AlgShape X Y Req Resp} {A : AdaptiveIAlg shA O} {T T' : ℕ → Set ((A.W × Req) × LogReg Req A.slots)}
    (hT : A.LogInvRaw T) (hT' : A.LogInvRaw T') : A.LogInvRaw fun n => T n ∩ T' n :=
  ⟨fun c c' h => ⟨hT.init c c' h, hT'.init c c' h⟩,
    fun j r a b lx ly h hlog hx => ⟨hT.slot j r a b lx ly h hlog hx.1,
      hT'.slot j r a b lx ly h hlog hx.2⟩,
    fun k hk r a b lx h hx => ⟨hT.post k hk r a b lx h hx.1, hT'.post k hk r a b lx h hx.2⟩⟩

section Relay

open Classical Distinguisher

variable {X Y Req Resp O : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp]
  {shA : AlgShape X Y Req Resp} (A : AdaptiveIAlg shA O) [AddGroup Y]
  {Req' Resp' O' : Type} [Fintype Req'] [DecidableEq Req'] [Fintype Resp'] [DecidableEq Resp']
  [Inhabited X] [Inhabited Req'] {Xs Ys : Type} [AddGroup Ys] [Fintype Ys] [DecidableEq Ys]
  (F : MultiRelay X Y Req Resp Req' Resp' Xs Ys) (Q : ℕ)
  (out' : A.RelayWS F → O') (J : Req → Bool)
  (Gin : List (Option Req) →
    Set (((A.toTPKindAlg true).unitOut.DW × Bool) × Req × Option Resp))

/-- **The well-formed registers of the relayed adversary before step `t`** (proof-internal), on
its workspace and request register: with some response register, the relay's well-formed
registers before step `t` (`Good₀` before step `0`, `GoodAt (t - 1)` after). -/
def RelayGood (t : ℕ) : Set (((A.relayAdv F Q out').W × Req') ×
    LogReg Req' (A.relayAdv F Q out').slots) :=
  {x | ∃ o, (x.1.1.1, x.1.2, o) ∈
    prevSeq (fun k => GoodAt F (A.budget + A.post) Q J Gin k) (Good₀ F Gin) t}

variable {F Q J Gin} in
/-- The well-formed registers do not read the response register. -/
theorem prevSeq_good_resp {t : ℕ}
    {x : RelayW (DReg ((A.toTPKindAlg true).unitOut.DW × Bool) (A.toTPKindAlg true).unitOut.width
      X Y Req Resp) Req Resp' X Y ((A.toTPKindAlg true).unitOut.slots + A.post)
      (relaySlots (A.toTPKindAlg true).unitOut.width ((A.toTPKindAlg true).unitOut.slots + A.post)
        F) (Fin F.qS → Ys) × Req' × Option Resp'}
    (o : Option Resp')
    (h : x ∈ prevSeq (fun k => GoodAt F (A.budget + A.post) Q J Gin k) (Good₀ F Gin) t) :
    (x.1, x.2.1, o) ∈ prevSeq (fun k => GoodAt F (A.budget + A.post) Q J Gin k)
      (Good₀ F Gin) t := by
  unfold prevSeq at h ⊢
  split_ifs at h ⊢ <;> exact h

/-- **A nonzero entry of a step of the relayed adversary** is, on the relayed distinguisher's
registers (the counter dropped), a nonzero entry of the relayed distinguisher's step. -/
theorem relayAdv_step_unitary
    {k : StepIdx (A.relayAdv F Q out').slots (A.relayAdv F Q out').post}
    {r : (A.relayAdv F Q out').R}
    {a b : DReg (A.relayAdv F Q out').W (A.relayAdv F Q out').width X Y Req' Resp'}
    (h : ((A.relayAdv F Q out').step k).op r a b ≠ 0) :
    unitaryMat ((A.relayD F Q).step ⟨k, k.isLt⟩) ((A.relayA F Q out').cntSplit a).1
      ((A.relayA F Q out').cntSplit b).1 ≠ 0 := by
  obtain ⟨r', hr'⟩ := (A.relayA F Q out').toTPKindAlg_op_ne_zero
    (fun k => TracePreserving.haltOp_eq_zero
      (Distinguisher.toAdaptive_tracePreserving _ _ _ _) k) h
  simp only [relayA, Distinguisher.toAdaptive_step, KrausChannel.toKrausMap,
    KrausChannel.ofUnitary] at hr'
  rw [Distinguisher.stepAt] at hr'
  split_ifs at hr' with hk
  · convert hr' using 2
  · exact absurd k.isLt hk

/-- **The relayed adversary's own steps carry `RelayGood`** (`relay_step_good`), for sets `Gin`
carried by the distinguisher's steps (`hI`). -/
theorem relayAdv_logInvRaw_good (hI : InnerSupp J Gin A.pureD) :
    (A.relayAdv F Q out').LogInvRaw (A.RelayGood F Q out' J Gin) := by
  have hn : 0 < (A.toTPKindAlg true).unitOut.width := (A.toTPKindAlg true).unitOut.width_pos
  -- a step `k` carries `RelayGood k` into `RelayGood (k + 1)`
  have hstep : ∀ (k : StepIdx (A.relayAdv F Q out').slots (A.relayAdv F Q out').post) r
      (a b : DReg (A.relayAdv F Q out').W (A.relayAdv F Q out').width X Y Req' Resp')
      (lx ly : LogReg Req' (A.relayAdv F Q out').slots),
      ((A.relayAdv F Q out').step k).op r a b ≠ 0 →
      ((b.1.1, b.1.2.1), lx) ∈ A.RelayGood F Q out' J Gin k →
      ((a.1.1, a.1.2.1), ly) ∈ A.RelayGood F Q out' J Gin (k + 1) := by
    intro k r a b lx ly h hx
    obtain ⟨o, ho⟩ := hx
    have hu := A.relayAdv_step_unitary F Q out' h
    rw [A.relayD_step] at hu
    have hc : (((A.relayA F Q out').cntSplit b).1).1 ∈
        prevSeq (fun k => GoodAt F (A.budget + A.post) Q J Gin k) (Good₀ F Gin) k :=
      prevSeq_good_resp A (((A.relayA F Q out').cntSplit b).1).1.2.2 ho
    have hg := relay_step_good (F := F) (b := A.budget + A.post) (Q := Q) J Gin A.pureD hn hI
      ⟨k, k.isLt⟩ (((A.relayA F Q out').cntSplit a).1) (((A.relayA F Q out').cntSplit b).1) hc
      (by convert hu using 2; try congr 1)
    refine ⟨(((A.relayA F Q out').cntSplit a).1).1.2.2, ?_⟩
    simp only [prevSeq, Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
    exact hg
  refine ⟨fun c c' h => ?_, fun j r a b lx ly h _ hx => hstep (slotStep j) r a b lx ly h hx,
    fun k _ r a b lx h hx => hstep k r a b lx lx h hx⟩
  erw [MState.reindex_tensorKet_mat] at h
  obtain ⟨c₀, c₀', rfl, -, hc⟩ := embed_ne_zero_exists h
  have hv : (A.relayD F Q).init c₀ ≠ 0 := by
    intro h0
    apply hc
    rw [Distinguisher.toAdaptive_init_mat]
    change (A.relayD F Q).init c₀ * star ((A.relayD F Q).init c₀') = 0
    rw [h0, zero_mul]
  rw [A.relayD_init] at hv
  exact ⟨c₀.1.2.2, good₀_of_init (D := A.pureD) (b := A.budget + A.post) (Q := Q) hI c₀ hv⟩

variable {A F Q out' J Gin} in
/-- **After the first step, the relay's record is tagged**: at most one of its entries is a
request satisfying `J`. -/
theorem jTagged_of_relayGood {t : ℕ} {x} (hx : x ∈ A.RelayGood F Q out' J Gin (t + 1)) :
    MultiRelay.JTagged J (MultiRelay.recList x.1.1.1.record) := by
  obtain ⟨o, ho⟩ := hx
  simp only [prevSeq, Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel] at ho
  obtain ⟨es, -, hrec, -, -, hJ, -⟩ := ho
  have hl : MultiRelay.recList x.1.1.1.record = es := by
    rw [hrec.2.1]
    exact MultiRelay.recList_getElem? es hrec.1
  rw [hl]
  exact hJ

end Relay

end AdaptiveIAlg

end GordieHowe.Quantum
