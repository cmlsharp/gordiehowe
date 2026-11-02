-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Interactive.RelayBlockGood
public import GordieHowe.Model.Quantum.Interactive.BlockRel
public import GordieHowe.Model.Quantum.Interactive.FromDistinguisher

@[expose] public section

/-!
# The block hypotheses of the relayed distinguisher

For a relay `F`, other programs `p'` of the same shape (`MultiRelay.SameShape`) whose resolved
forms move the main requests and results of the request `r₀` of the test `J` by `sw` and `swO`
(`MultiRelay.ProgSwap`), and a distinguisher `D` whose steps agree along permutations `πin es` of
its registers read from its started slots (`InnerSwap`), the relayed distinguishers with `F`'s and
with `p'`'s programs, as adversaries (`Distinguisher.toAdaptive`), satisfy the block hypotheses
(`AdaptiveIAlg.BlockRel`) of the label `jLabel` (the first started request satisfying `J`) at
`r₀`, along `relSwT` (which also exchanges the side stores read from the record with `F`'s and
with `p'`'s programs) and the well-formed sets `GoodAt`.

- `Distinguisher.relSw_eq_relSwT`: `relSw` is `relSwT` with the query pair kept.
- `Distinguisher.InnerSwap`: the distinguisher's steps along `πin` of its started slots.
- `Distinguisher.recList_row`, `Distinguisher.ctrl_relSw`: the record of a row, and the controlled
  step along `πin` from `InnerSwap`.
- `Distinguisher.goodAt_relSwT`, `Distinguisher.good₀_of_init`, `Distinguisher.prev_good`: the
  well-formed registers along `relSwT` on the block, the initial ones, and the columns before a
  step.
- **`Distinguisher.blockRel_relay`**: `AdaptiveIAlg.BlockRel` of the two relayed adversaries.
- `Distinguisher.goodAt_off`, `Distinguisher.preFun_withProg_off`, `Distinguisher.sum_label_relay`,
  `Distinguisher.sum_label_relay_off`: with other programs off `J`, the same well-formed registers
  and tear-down without requests satisfying `J`, and the overlaps into a block read through the
  record and set-up undone.
- **`Distinguisher.blockNone_relay`**: `AdaptiveIAlg.BlockNone` of the two relayed adversaries
  for programs equal off `J`.
- Auxiliary: `MultiRelay.firstJ_append`, `SubAct.askOf_mapAsk`, `Distinguisher.curSw_blank`,
  `Distinguisher.relSwT_blank`, `Distinguisher.getD_of_inBlock`, `Distinguisher.getD_of_none`,
  `Distinguisher.toAdaptive_op`, `Distinguisher.toAdaptive_op_fin`,
  `Distinguisher.stepAt_of_lt`, `Distinguisher.opRelOn₂_prevSeq_const`,
  `Distinguisher.curSw_refl`, `Distinguisher.lastSwO_refl`, `Distinguisher.sideSw_blank`,
  `Distinguisher.prog_eq_of_off`, `Distinguisher.sideSw_off`, `Distinguisher.relSw_refl`,
  `Distinguisher.respSw_refl`, `Distinguisher.progSwap_off`, `Distinguisher.innerMap_off`.
-/

set_option linter.unusedSectionVars false

namespace GordieHowe.Quantum

open GordieHowe.QROM

namespace MultiRelay

variable {Req : Type} {J : Req → Bool}

/-- **The first request satisfying `J` stays first after one more entry.** -/
theorem firstJ_append {es : List (Option Req)} {r : Req} (h : firstJ J es = some r)
    (e : Option Req) : firstJ J (es ++ [e]) = some r := by
  unfold firstJ at h ⊢
  rcases hf : es.find? (fun e => e.any J) with _ | e'
  · rw [hf] at h
    exact absurd h (by simp)
  · rw [List.find?_append, hf]
    rw [hf] at h
    exact h

end MultiRelay

namespace SubAct

variable {X Req' : Type} [Inhabited Req'] {n : ℕ}

/-- **The main request of a moved action** is the moved main request, for a move keeping the
blank one. -/
theorem askOf_mapAsk (f : Equiv.Perm Req') (hf : f default = default) (a : SubAct X Req' n) :
    Distinguisher.askOf (a.mapAsk f) = f (Distinguisher.askOf a) := by
  rcases a with i | x | r' <;> simp [mapAsk, Distinguisher.askOf, hf]

end SubAct

namespace Distinguisher

variable {W X Y Req Resp Req' Resp' Xs Ys : Type} [Fintype W] [DecidableEq W] [Fintype X]
  [DecidableEq X] [Fintype Y] [DecidableEq Y] [Fintype Req] [DecidableEq Req] [Fintype Resp]
  [DecidableEq Resp] [Fintype Req'] [DecidableEq Req'] [Fintype Resp'] [DecidableEq Resp']
  [Inhabited X] [Inhabited Req'] [AddGroup Y] [AddGroup Ys] [Fintype Ys] [DecidableEq Ys] {n m : ℕ}
  (F : MultiRelay X Y Req Resp Req' Resp' Xs Ys)
  (p' : Req → OracleProg ((X ⊕ Xs) ⊕ Req') ((Y ⊕ Ys) ⊕ Option Resp') (Option Resp)) (b Q : ℕ)
  (J : Req → Bool) (P : Req → Prop) [DecidablePred P] (sw : Equiv.Perm Req')
  (πin : List (Option Req) → Equiv.Perm (W × Req × Option Resp))

local notation "RR" => RelayReg W X Y Req Resp Req' Resp' n m (relaySlots n m F) (Fin F.qS → Ys)

local notation "RT" => RelayW (DReg W n X Y Req Resp) Req Resp' X Y m (relaySlots n m F) (Fin F.qS →
    Ys) ×
  Req' × Option Resp'

theorem relSw_eq_relSwT (x : RR) :
    relSw F p' b Q J P sw πin x = (relSwT F p' b Q J P sw πin x.1, x.2) :=
  rfl

variable {F p' b Q J P sw πin}

/-- The current slot's permutation of a blank record is the identity. -/
theorem curSw_blank (t : ℕ) :
    F.curSw J sw n b Q (fun _ : Fin m => (none : Option (Option Req))) t = Equiv.refl _ := by
  unfold MultiRelay.curSw MultiRelay.curBlk
  have : MultiRelay.recList (fun _ : Fin m => (none : Option (Option Req))) = [] := by
    unfold MultiRelay.recList
    rcases m with _ | m
    · rfl
    · simp [List.finRange_succ]
  simp [this]

/-- **The distinguisher's steps along `πin`**: step `es.length`, at a column in `Gin es`, read along
`πin` of the list with the row's entry (when a slot is left to start) on the rows and `πin es` on
the columns, is the step. -/
def InnerSwap (D : Distinguisher W X Y Req Resp n m)
    (πin : List (Option Req) → Equiv.Perm (W × Req × Option Resp))
    (Gin : List (Option Req) → Set (W × Req × Option Resp)) : Prop :=
  ∀ es (y x : DReg W n X Y Req Resp), x.1 ∈ Gin es →
    unitaryMat (D.stepAt es.length)
      ((πin (if es.length < m then es ++ [entryOf D.kind y] else es)).prodCongr (Equiv.refl _) y)
      ((πin es).prodCongr (Equiv.refl _) x) = unitaryMat (D.stepAt es.length) y x

variable (D : Distinguisher W X Y Req Resp n m)

/-- **The record of a row**: the column's list, with the entry of the distinguisher's registers
when a slot starts at the clock. -/
theorem recList_row (hn : 0 < n) (k : ℕ) (a c : RR) {es : List (Option Req)} (hl : es.length ≤ m)
    (hrc : c.1.1.record = fun i : Fin m => es[(i : ℕ)]?)
    (hs : ∀ i < es.length, F.startAt n b Q es i < (preFun F b Q k c).1.1.time)
    (hrest : rest F (recordFun F b Q D.kind (setupFun F b Q a)) = rest F
        (preFun F b Q k c)) :
    MultiRelay.recList a.1.1.record =
      if F.startAt n b Q es es.length = (preFun F b Q k c).1.1.time ∧ es.length < m then
        es ++ [entryOf D.kind (recordFun F b Q D.kind (setupFun F b Q a)).1.1.inner] else es := by
  set z := recordFun F b Q D.kind (setupFun F b Q a) with hz
  have hza : setupFun F b Q (recordFun F b Q D.kind z) = a := by
    rw [hz, recordFun_recordFun, setupFun_setupFun]
  have hzr : z.1.1.record = c.1.1.record :=
    (congrArg (fun r => r.1) hrest).trans (preFun_record_inner (F := F) (b := b) (Q := Q) k c).1
  have hzt : z.1.1.time = (preFun F b Q k c).1.1.time := congrArg (fun r => r.2.2.2.1) hrest
  have hrecz := recordFun_record_ofList hn D.kind z hl (hzr.trans hrc) (by rw [hzt]; exact hs)
  have harec : a.1.1.record = (recordFun F b Q D.kind z).1.1.record := by
    conv_lhs => rw [← hza]
    exact setupFun_record _
  rw [harec, hrecz, hzt, MultiRelay.recList_getElem?]
  split_ifs with hf
  · simp only [List.length_append, List.length_singleton]
    omega
  · exact hl

/-- **The controlled step along `πin`** (the hypothesis `hctrl` of
`unitaryMat_relay_step_relSw`), from the distinguisher's steps along `πin` (`InnerSwap`), on a
column whose record is a list `es` with its distinguisher's registers in `Gin es` when the
distinguisher's step applies. -/
theorem ctrl_relSw (hn : 0 < n) {Gin : List (Option Req) → Set (W × Req × Option Resp)}
    (hIH : InnerSwap D πin Gin) (k : ℕ) (a c : RR) {es : List (Option Req)} (hl : es.length ≤ m)
    (hrc : c.1.1.record = fun i : Fin m => es[(i : ℕ)]?)
    (hs : ∀ i < es.length, F.startAt n b Q es i < (preFun F b Q k c).1.1.time)
    (hxin : F.startAt n b Q es es.length = ((preFun F b Q k c).1.1.time : ℕ) →
      (preFun F b Q k c).1.1.inner.1 ∈ Gin es) :
    rest F (recordFun F b Q D.kind (setupFun F b Q a)) = rest F (preFun F b
        Q k c) →
      unitaryMat (D.ctrlU F b Q (rest F (preFun F b Q k c)))
        (((πin (MultiRelay.recList a.1.1.record)).prodCongr (Equiv.refl _))
          (relaySplit W X Y Req Resp Req' Resp' n m (relaySlots n m F) (Fin F.qS → Ys)
            (recordFun F b Q D.kind (setupFun F b Q a))).1)
        (((πin (MultiRelay.recList c.1.1.record)).prodCongr (Equiv.refl _))
          (relaySplit W X Y Req Resp Req' Resp' n m (relaySlots n m F) (Fin F.qS → Ys) (preFun F b Q
              k c)).1) =
      unitaryMat (D.ctrlU F b Q (rest F (preFun F b Q k c)))
        (relaySplit W X Y Req Resp Req' Resp' n m (relaySlots n m F) (Fin F.qS → Ys)
          (recordFun F b Q D.kind (setupFun F b Q a))).1
        (relaySplit W X Y Req Resp Req' Resp' n m (relaySlots n m F) (Fin F.qS → Ys) (preFun F b Q k
            c)).1 := by
  intro hrest
  have hrow := recList_row (F := F) (b := b) (Q := Q) D hn k a c hl hrc hs hrest
  have hcl : MultiRelay.recList c.1.1.record = es := by
    rw [hrc, MultiRelay.recList_getElem? es hl]
  have hxl : MultiRelay.recList (preFun F b Q k c).1.1.record = es := by
    rw [(preFun_record_inner (F := F) (b := b) (Q := Q) k c).1, hcl]
  rw [hrow, hcl]
  unfold ctrlU
  change unitaryMat (if F.startAt n b Q (MultiRelay.recList (preFun F b Q k c).1.1.record)
      (MultiRelay.recList (preFun F b Q k c).1.1.record).length =
        ((preFun F b Q k c).1.1.time : ℕ) then
        D.stepAt (MultiRelay.recList (preFun F b Q k c).1.1.record).length
      else LinearIsometryEquiv.refl ℂ _) _ _ = unitaryMat (if F.startAt n b Q
        (MultiRelay.recList (preFun F b Q k c).1.1.record)
      (MultiRelay.recList (preFun F b Q k c).1.1.record).length =
        ((preFun F b Q k c).1.1.time : ℕ) then
        D.stepAt (MultiRelay.recList (preFun F b Q k c).1.1.record).length
      else LinearIsometryEquiv.refl ℂ _) _ _
  rw [hxl]
  by_cases hf : F.startAt n b Q es es.length = ((preFun F b Q k c).1.1.time : ℕ)
  · simp only [hf, true_and, ↓reduceIte]
    exact hIH es _ _ (hxin hf)
  · simp only [hf, false_and, ↓reduceIte, unitaryMat_refl]
    simp only [Matrix.one_apply, EmbeddingLike.apply_eq_iff_eq]

variable {D}

/-- `sideSw` of a blank record is the identity. -/
theorem sideSw_blank (store : Fin (relaySlots n m F) → Option Resp' × (X × Y)) (t : ℕ) :
    sideSw F p' b Q J P (fun _ : Fin m => (none : Option (Option Req))) store t =
      Equiv.refl _ := by
  refine Equiv.ext fun v => funext fun i => ?_
  rw [sideSw_apply, F.consSide_blank, (F.withProg p').consSide_blank]
  have hz : ∀ x : Fin F.qS → Ys, Equiv.swap ((0 : Fin m → Fin F.qS → Ys) i) 0 x = x := fun x => by
    simp
  split_ifs
  · exact hz _
  · rfl

/-- `relSwT` keeps the registers of a blank record when `πin []` is the identity. -/
theorem relSwT_blank (hπ0 : ∀ x, πin [] x = x) (x : RT)
    (hx : x.1.record = fun _ => none) : relSwT F p' b Q J P sw πin x = x := by
  obtain ⟨⟨⟨w, p⟩, rec, store, side, t⟩, q, a⟩ := x
  change rec = _ at hx
  subst hx
  have hl : MultiRelay.recList (fun _ : Fin m => (none : Option (Option Req))) = [] := by
    unfold MultiRelay.recList
    rcases m with _ | m
    · rfl
    · simp [List.finRange_succ]
  change ((RelayW.mk (πin (MultiRelay.recList (fun _ : Fin m => (none : Option (Option Req)))) w, p)
      (fun _ => none) store (sideSw F p' b Q J P (fun _ => none) store t side) t :
      RelayW (DReg W n X Y Req Resp) Req Resp' X Y m (relaySlots n m F) (Fin F.qS → Ys)),
    F.curSw J sw n b Q (fun _ : Fin m => (none : Option (Option Req))) t q, a) = _
  rw [hl, hπ0, curSw_blank, sideSw_blank]
  rfl

/-- **The started requests satisfying `J` are `r₀`** on a tagged record of label `none` or
`some r₀`. -/
theorem getD_of_inBlock {es : List (Option Req)} (hJ : MultiRelay.JTagged J es)
    {r₀ : Req} (hb : MultiRelay.firstJ J es = none ∨ MultiRelay.firstJ J es = some r₀) :
    ∀ i r, es.getD i none = some r → J r = true → r = r₀ := fun i r hi hr => by
  have hi' : es[i]? = some (some r) := by
    rw [List.getD_eq_getElem?_getD] at hi
    rcases h : es[i]? with _ | e
    · rw [h] at hi
      exact absurd hi (by simp)
    · rw [h] at hi
      simp only [Option.getD_some] at hi
      rw [hi]
  rcases hb with hb | hb
  · exact absurd (MultiRelay.not_J_of_firstJ_none hb hi') (by simp [hr])
  · exact MultiRelay.eq_of_firstJ hJ hb hi' hr

omit [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [Inhabited X] [AddGroup Y] in
/-- A constant sequence of permutations reads the same before every step. -/
theorem opRelOn₂_prevSeq_const {α ι R' : Type*} [Fintype ι] [DecidableEq ι] [Fintype R']
    (f : α → Equiv.Perm ι) {π : α} {Sr Sc : Set ι} {K K' : KrausMap R' ι ι} (k : ℕ)
    (h : OpRelOn₂ (f π) (f π) Sr Sc K K') :
    OpRelOn₂ (f π) (f (prevSeq (fun _ => π) π k)) Sr Sc K K' := by
  have : prevSeq (fun _ => π) π k = π := by
    unfold prevSeq
    split_ifs <;> rfl
  rw [this]
  exact h

/-- The steps of the adversary of a distinguisher are its unitaries, by number. -/
theorem toAdaptive_op_fin {W' Req₁ Resp₁ O : Type} [Fintype W'] [DecidableEq W'] [Fintype Req₁]
    [DecidableEq Req₁] [Fintype Resp₁] [DecidableEq Resp₁] {n' m' : ℕ}
    (D' : Distinguisher W' X Y Req₁ Resp₁ n' m') (hn : 0 < n') (q : ℕ) (out : W' → O)
    (k : StepIdx m' 0) (i : Unit) :
    ((D'.toAdaptive hn q out).step k).op i = unitaryMat (D'.step ⟨k, k.isLt⟩) := by
  rw [toAdaptive_op]
  unfold stepAt
  simp only [k.isLt, ↓reduceDIte]

/-- The step of a distinguisher at a number within its steps. -/
theorem stepAt_of_lt {W' Req₁ Resp₁ : Type} [Fintype W'] [DecidableEq W'] [Fintype Req₁]
    [DecidableEq Req₁] [Fintype Resp₁] [DecidableEq Resp₁] {n' m' : ℕ}
    (D' : Distinguisher W' X Y Req₁ Resp₁ n' m') (k : ℕ) (hk : k < m' + 1) :
    D'.stepAt k = D'.step ⟨k, hk⟩ := by
  unfold stepAt
  simp only [hk, ↓reduceDIte]

/-- **The initial registers of the relayed distinguisher are well formed.** -/
theorem good₀_of_init {Gin : List (Option Req) → Set (W × Req × Option Resp)}
    (hI : InnerSupp J Gin D) (a : RR) (ha : (D.relay F b Q).init a ≠ 0) :
    a.1 ∈ Good₀ F Gin := by
  have hmem : a ∈ Set.range
      (relayInit (W := W) (Req := Req) (Resp := Resp) (n := n) (m := m) F) := by
    by_contra hn
    exact ha (embV_apply_of_notMem _ hn)
  obtain ⟨d, rfl⟩ := hmem
  have hd : D.init d ≠ 0 := by
    have := ha
    change embV (relayInit F) D.init (relayInit F d) ≠ 0 at this
    rwa [embV_apply_self (relayInit_injective F)] at this
  exact ⟨rfl, rfl, rfl, hI.init d hd, rfl⟩

variable (D) {swO : Equiv.Perm Resp} {Gin : List (Option Req) → Set (W × Req × Option Resp)}

/-- **The well-formed registers along `relSwT`**: on the block `r₀`, the registers moved by
`relSwT` are well formed with `p'`'s programs exactly when they are with `F`'s. -/
theorem goodAt_relSwT {r₀ : Req} (h : F.ProgSwap p' J (· = r₀) sw swO)
    (hidle : sw F.idle = F.idle) (hdef : sw default = default)
    (hGπ : ∀ es x, πin es x ∈ Gin es ↔ x ∈ Gin es) (k : ℕ) (x : RT)
    (hx : InBlock (jLabel F J) r₀ x.1) :
    relSwT F p' b Q J (· = r₀) sw πin x ∈ GoodAt (F.withProg p') b Q J Gin k ↔
      x ∈ GoodAt F b Q J Gin k := by
  obtain ⟨⟨⟨w, p⟩, rec, store, side, t⟩, q, a⟩ := x
  have key : ∀ es, RecAt (n := n) F b Q rec es k → MultiRelay.JTagged J es →
      side = F.consSide n b Q rec store t →
      ((F.curSw J sw n b Q rec t q = Distinguisher.askOf
        ((F.withProg p').actAt n b Q rec store (sideSw F p' b Q J (· = r₀) rec store t side) t) ↔
        q = Distinguisher.askOf (F.actAt n b Q rec store side t)) ∧
      (πin (MultiRelay.recList rec) w ∈ Gin es ↔ w ∈ Gin es)) := fun es hrec hJ hs => by
    have hl : MultiRelay.recList rec = es := by
      rw [hrec.2.1, MultiRelay.recList_getElem? es hrec.1]
    have hrec' : ∀ i r, (MultiRelay.recList rec).getD i none = some r → J r = true → r = r₀ := by
      rw [hl]
      exact getD_of_inBlock hJ (by rw [← hl]; exact hx)
    subst hs
    rw [actAt_relSw h hidle hrec' store t, SubAct.askOf_mapAsk _ (curSw_default hdef rec t), hl]
    exact ⟨(F.curSw J sw n b Q rec t).injective.eq_iff, hGπ es w⟩
  have hS : ∀ es, RecAt (n := n) F b Q rec es k → MultiRelay.JTagged J es →
      (sideSw F p' b Q J (· = r₀) rec store t side =
        (F.withProg p').consSide n b Q rec store t ↔ side = F.consSide n b Q rec store t) :=
    fun es hrec hJ => by
      have hl : MultiRelay.recList rec = es := by
        rw [hrec.2.1, MultiRelay.recList_getElem? es hrec.1]
      refine sideSw_eq_consSide_iff (fun i r he hr => ?_) store t side
      rw [hl] at he
      exact getD_of_inBlock hJ (by rw [← hl]; exact hx) i r he hr
  constructor
  · rintro ⟨es, ht, hrec, hq, hs, hJ, hin⟩
    have hs' := (hS es hrec hJ).1 hs
    obtain ⟨k1, k2⟩ := key es hrec hJ hs'
    exact ⟨es, ht, hrec, k1.1 hq, hs', hJ, hin.imp_left k2.1⟩
  · rintro ⟨es, ht, hrec, hq, hs, hJ, hin⟩
    obtain ⟨k1, k2⟩ := key es hrec hJ hs
    exact ⟨es, ht, hrec, k1.2 hq, (hS es hrec hJ).2 hs, hJ, hin.imp_left k2.2⟩

/-- **The columns before a step**: before step `k ≠ 0`, their main request registers hold their
actions' main requests and their side stores are read from their records at a clock `k - 1 < S`;
before step `0`, their main request registers are blank. -/
theorem prev_good (k : Fin (relaySlots n m F + 1)) (c : RR)
    (hc : c.1 ∈ prevSeq (fun k => GoodAt F b Q J Gin k) (Good₀ F Gin) k) :
    ((k : ℕ) ≠ 0 → c.1.2.1 = askOf (F.actAt n b Q c.1.1.record c.1.1.store c.1.1.side
        c.1.1.time) ∧ c.1.1.side = F.consSide n b Q c.1.1.record c.1.1.store c.1.1.time ∧
      (∃ es, RecAt (n := n) F b Q c.1.1.record es c.1.1.time) ∧
      (c.1.1.time : ℕ) < relaySlots n m F) ∧ ((k : ℕ) = 0 → c.1.2.1 = default) := by
  refine ⟨fun hk0 => ?_, fun hk0 => ?_⟩
  · simp only [prevSeq, hk0, ↓reduceIte] at hc
    obtain ⟨es, ht, hrec, hq, hs, -, -⟩ := hc
    have := k.isLt
    exact ⟨hq, hs, ⟨es, by rw [ht]; exact hrec⟩, by rw [ht]; omega⟩
  · simp only [prevSeq, hk0, ↓reduceIte] at hc
    exact hc.2.2.1

/-- **The block hypotheses of the relayed distinguisher** (module docstring): the adversaries of
the relayed distinguishers with `F`'s and with `p'`'s programs agree on the block `r₀` of the
first started request satisfying `J`, along `relSwT` and the well-formed sets. -/
theorem blockRel_relay (hn : 0 < n) (hI : InnerSupp J Gin D) (hIH : InnerSwap D πin Gin)
    (hS : F.SameShape p') {r₀ : Req} (h : F.ProgSwap p' J (· = r₀) sw swO)
    (hidle : sw F.idle = F.idle)
    (hdef : sw default = default) (hπ : RespSw b Q J swO πin)
    (hk : ∀ es w q a, D.kind (πin es (w, q, a)).1 = D.kind w)
    (hrq : ∀ es w q a, (πin es (w, q, a)).2.1 = q)
    (hGπ : ∀ es x, πin es x ∈ Gin es ↔ x ∈ Gin es) (hπ0 : ∀ x, πin [] x = x) (q₀ : ℕ)
    {O : Type} (out : RelayW (DReg W n X Y Req Resp) Req Resp' X Y m (relaySlots n m F) (Fin F.qS →
        Ys) → O)
    (out' : RelayW (DReg W n X Y Req Resp) Req Resp' X Y m (relaySlots n m F) (Fin F.qS → Ys) → O) :
    ((D.relay F b Q).toAdaptive Nat.one_pos q₀ out).BlockRel
      ((D.relay (F.withProg p') b Q).toAdaptive Nat.one_pos q₀ out').step (jLabel F J)
      (fun k => GoodAt F b Q J Gin k) (fun k => GoodAt (F.withProg p') b Q J Gin k)
      (Good₀ F Gin) (Good₀ (F.withProg p') Gin) (fun _ => relSwT F p' b Q J (· = r₀) sw πin)
      (relSwT F p' b Q J (· = r₀) sw πin) r₀ where
  label_eq _ _ := rfl
  label_eq₀ _ := rfl
  kind_eq _ x := isAsk_actAt_sideSw (n := n) (b := b) (Q := Q) hS h hidle x.1.record x.1.store
    x.1.side x.1.time
  set_eq n x hx := goodAt_relSwT h hidle hdef hGπ n x hx
  set_eq₀ x hx := by
    constructor
    · intro h0
      have hr : x.1.record = fun _ => none := h0.2.1
      erw [relSwT_blank hπ0 x hr] at h0
      exact h0
    · intro h0
      erw [relSwT_blank hπ0 x h0.2.1]
      exact h0
  keepsSet k i a c hc hne := by
    rw [toAdaptive_op] at hne
    change unitaryMat ((D.relay F b Q).stepAt k) a c ≠ 0 at hne
    erw [stepAt_of_lt _ k k.isLt] at hne
    exact relay_step_good J Gin D hn hI ⟨k, k.isLt⟩ a c hc hne
  keepsSet' k i a c hc hne := by
    -- TODO(unbundle-M4): `rw` does not match `toAdaptive_op` against the adversary at
    -- `F.withProg p'`: its implicit shape and instance arguments are spelled through
    -- `F.withProg p'`, the lemma's through the synthesized ones (not isolated); `erw`
    -- bridges the two spellings.
    erw [toAdaptive_op] at hne
    change unitaryMat ((D.relay (F.withProg p') b Q).stepAt k) a c ≠ 0 at hne
    erw [stepAt_of_lt _ k k.isLt] at hne
    exact relay_step_good (F := F.withProg p') J Gin D hn hI ⟨k, k.isLt⟩ a c hc hne
  keeps k i r' a c hcG hc hne := by
    rw [toAdaptive_op] at hne
    change unitaryMat ((D.relay F b Q).stepAt k) a c ≠ 0 at hne
    erw [stepAt_of_lt _ k k.isLt] at hne
    obtain ⟨-, es, hes, ha, -⟩ := relay_step_good_rec J Gin D hn hI ⟨k, k.isLt⟩ a c hcG hne
    change MultiRelay.firstJ J (MultiRelay.recList c.1.1.record) = some r' at hc
    change MultiRelay.firstJ J (MultiRelay.recList a.1.1.record) = some r'
    rw [hes] at hc
    rcases ha with ha | ⟨e, ha, -⟩
    · rw [ha]
      exact hc
    · rw [ha]
      exact MultiRelay.firstJ_append hc e
  keeps' k i r' a c hcG hc hne := by
    -- TODO(unbundle-M4): `rw` does not match `toAdaptive_op` against the adversary at
    -- `F.withProg p'`: its implicit shape and instance arguments are spelled through
    -- `F.withProg p'`, the lemma's through the synthesized ones (not isolated); `erw`
    -- bridges the two spellings.
    erw [toAdaptive_op] at hne
    change unitaryMat ((D.relay (F.withProg p') b Q).stepAt k) a c ≠ 0 at hne
    erw [stepAt_of_lt _ k k.isLt] at hne
    obtain ⟨-, es, hes, ha, -⟩ := relay_step_good_rec (F := F.withProg p') J Gin D hn hI
      ⟨k, k.isLt⟩ a c hcG hne
    change MultiRelay.firstJ J (MultiRelay.recList c.1.1.record) = some r' at hc
    change MultiRelay.firstJ J (MultiRelay.recList a.1.1.record) = some r'
    rw [hes] at hc
    rcases ha with ha | ⟨e, ha, -⟩
    · rw [ha]
      exact hc
    · rw [ha]
      exact MultiRelay.firstJ_append hc e
  hop k := by
    refine opRelOn₂_prevSeq_const AdaptiveIAlg.tripPerm k fun i a c ha hc => ?_
    suffices hs : unitaryMat ((D.relay (F.withProg p') b Q).step ⟨k, k.isLt⟩)
        (relSw F p' b Q J (· = r₀) sw πin a) (relSw F p' b Q J (· = r₀) sw πin c) =
          unitaryMat ((D.relay F b Q).step ⟨k, k.isLt⟩) a c by
      have e1 := toAdaptive_op_fin (D.relay (F.withProg p') b Q) Nat.one_pos q₀ out' k i
      have e2 := toAdaptive_op_fin (D.relay F b Q) Nat.one_pos q₀ out k i
      exact (congrFun (congrFun e1 _) _).trans (hs.trans (congrFun (congrFun e2 a) c).symm)
    obtain ⟨hab, esa, -, hreca, hqa, hsa, hJa, -⟩ := ha
    have hla : MultiRelay.recList a.1.1.record = esa := by
      rw [hreca.2.1, MultiRelay.recList_getElem? esa hreca.1]
    have hrecA : ∀ i r, (MultiRelay.recList a.1.1.record).getD i none = some r → J r = true →
        r = r₀ := by
      rw [hla]
      exact getD_of_inBlock hJa (by rw [← hla]; exact hab)
    obtain ⟨hcb, hcG⟩ := hc
    have hgc := prev_good (Gin := Gin) ⟨k, k.isLt⟩ c hcG
    by_cases hk0 : (k : ℕ) = 0
    · simp only [prevSeq, hk0, ↓reduceIte] at hcG
      obtain ⟨ht0, hr0, hq0, hin, -⟩ := hcG
      have hlc : MultiRelay.recList c.1.1.record = [] := by
        rw [hr0]
        unfold MultiRelay.recList
        rcases m with _ | m
        · rfl
        · simp [List.finRange_succ]
      refine unitaryMat_relay_step_relSw D h hidle hdef hπ hk hrq ⟨k, k.isLt⟩ a c hrecA
        (fun i r hi => by rw [hlc] at hi; simp at hi) hqa hsa hgc.1 hgc.2 ?_
      refine ctrl_relSw D hn hIH k a c (es := []) (Nat.zero_le _) (by rw [hr0]; funext i; simp)
        (fun i hi => absurd hi (Nat.not_lt_zero _)) fun _ => ?_
      rw [(preFun_record_inner (F := F) (b := b) (Q := Q) k c).2.2.2.2 hk0]
      exact hin
    · simp only [prevSeq, hk0, ↓reduceIte] at hcG
      obtain ⟨esc, htc, hrecc, hqc, -, hJc, hinc⟩ := hcG
      have hlc : MultiRelay.recList c.1.1.record = esc := by
        rw [hrecc.2.1, MultiRelay.recList_getElem? esc hrecc.1]
      have hrecC : ∀ i r, (MultiRelay.recList c.1.1.record).getD i none = some r →
          J r = true → r = r₀ := by
        rw [hlc]
        exact getD_of_inBlock hJc (by rw [← hlc]; exact hcb)
      have hkS : (k : ℕ) - 1 < relaySlots n m F := by
        have := k.isLt
        change (k : ℕ) < relaySlots n m F + 0 + 1 at this
        omega
      obtain ⟨hxr, hxw, hxq, hxt, -⟩ := preFun_record_inner (F := F) (b := b) (Q := Q) k c
      refine unitaryMat_relay_step_relSw D h hidle hdef hπ hk hrq ⟨k, k.isLt⟩ a c hrecA hrecC
        hqa hsa hgc.1 hgc.2 ?_
      refine ctrl_relSw D hn hIH k a c hrecc.1 hrecc.2.1 (fun i hi => ?_) ?_
      · rw [hxt hk0 (by rw [htc]; exact hkS), htc]
        exact Nat.lt_succ_of_le (hrecc.2.2 i hi)
      · intro hf
        rcases hinc with h | ⟨hm, hle⟩
        · exact preFun_inner_mem J Gin hI k c (by
            rw [hrecc.2.1, MultiRelay.recList_getElem? esc hrecc.1]) h
        · exfalso
          have h1 := hxt hk0 (by rw [htc]; exact hkS)
          have h2 : F.startAt n b Q esc esc.length = F.startAt n b Q esc m := congrArg _ hm
          omega
  init_supp a c hac := by
    rw [toAdaptive_init_mat] at hac
    change (D.relay F b Q).init a * star ((D.relay F b Q).init c) ≠ 0 at hac
    exact ⟨good₀_of_init hI a (left_ne_zero_of_mul hac),
      good₀_of_init hI c (fun h0 => hac (by rw [h0, star_zero, mul_zero]))⟩
  init_supp' a c hac := by
    rw [toAdaptive_init_mat] at hac
    change (D.relay F b Q).init a * star ((D.relay F b Q).init c) ≠ 0 at hac
    exact ⟨good₀_of_init hI a (left_ne_zero_of_mul hac),
      good₀_of_init hI c (fun h0 => hac (by rw [h0, star_zero, mul_zero]))⟩
  init_eq a c haG hcG ha hc := by
    have ea : AdaptiveIAlg.tripPerm (relSwT F p' b Q J (· = r₀) sw πin) a = a :=
      Prod.ext (relSwT_blank hπ0 a.1 haG.2.1) rfl
    have ec : AdaptiveIAlg.tripPerm (relSwT F p' b Q J (· = r₀) sw πin) c = c :=
      Prod.ext (relSwT_blank hπ0 c.1 hcG.2.1) rfl
    erw [ea, ec]

/-! ### Off the blocks -/

theorem curSw_refl {m' : ℕ} (rec : Fin m' → Option (Option Req)) (t : ℕ) :
    F.curSw J (Equiv.refl Req') n b Q rec t = Equiv.refl _ := by
  unfold MultiRelay.curSw MultiRelay.swAt
  rcases F.curBlk n b Q rec t with _ | ⟨j', sub⟩
  · rfl
  · simp only
    rcases MultiRelay.blkAt b Q (MultiRelay.recList rec) j' with _ | _ | _ <;>
      rcases (MultiRelay.recList rec).getD j' none with _ | r <;> try rfl
    simp only [ite_self]

theorem lastSwO_refl {m' : ℕ} (rec : Fin m' → Option (Option Req)) :
    MultiRelay.lastSwO J (Equiv.refl Resp) b Q rec = Equiv.refl _ := by
  unfold MultiRelay.lastSwO MultiRelay.swOAt
  split_ifs
  · rcases MultiRelay.blkAt b Q (MultiRelay.recList rec) ((MultiRelay.recList rec).length - 1)
      with _ | _ | _ <;>
      rcases (MultiRelay.recList rec).getD ((MultiRelay.recList rec).length - 1) none with _ | r <;>
      try rfl
    simp only [ite_self]
  · rfl

/-- A record whose first request satisfying `J` is absent has none. -/
theorem getD_of_none {es : List (Option Req)} (h0 : MultiRelay.firstJ J es = none) :
    ∀ i r, es.getD i none = some r → J r = true → False := fun i r hi hr => by
  have hi' : es[i]? = some (some r) := by
    rw [List.getD_eq_getElem?_getD] at hi
    rcases h : es[i]? with _ | e
    · rw [h] at hi
      exact absurd hi (by simp)
    · rw [h] at hi
      simp only [Option.getD_some] at hi
      rw [hi]
  exact absurd (MultiRelay.not_J_of_firstJ_none h0 hi') (by simp [hr])

omit [Fintype W] [DecidableEq W] [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp] [Fintype Req']
  [DecidableEq Req'] [Fintype Resp'] [DecidableEq Resp'] [Inhabited X] [Inhabited Req']
  [AddGroup Y] [AddGroup Ys] [Fintype Ys] [DecidableEq Ys] in
/-- Programs equal off `J` are equal at the requests of a list without requests satisfying `J`. -/
theorem prog_eq_of_off (hoff : ∀ r, J r = false → p' r = F.prog r) {es : List (Option Req)}
    (hes : ∀ i r, es.getD i none = some r → J r = true → False) :
    ∀ i r, es.getD i none = some r → p' r = F.prog r :=
  fun i r he => hoff r (Bool.eq_false_iff.2 fun hJ => hes i r he hJ)

/-- `sideSw` of a record without requests satisfying `J`, for programs equal off `J`, is the
identity. -/
theorem sideSw_off (hoff : ∀ r, J r = false → p' r = F.prog r) (rec : Fin m → Option (Option Req))
    (hrec : ∀ i r, (MultiRelay.recList rec).getD i none = some r → J r = true → False)
    (store : Fin (relaySlots n m F) → Option Resp' × (X × Y)) (t : ℕ) :
    sideSw F p' b Q J P rec store t = Equiv.refl _ := by
  have hC : (F.withProg p').consSide n b Q rec store t = F.consSide n b Q rec store t :=
    funext fun i => MultiRelay.consSide_withProg_of_eq n b Q rec store t i fun r he =>
      prog_eq_of_off hoff hrec i r he
  refine Equiv.ext fun v => funext fun i => ?_
  rw [sideSw_apply, hC]
  split_ifs
  · simp
  · rfl

/-- `relSw` with identity permutations, on a record without requests satisfying `J` for programs
equal off `J`, is the identity. -/
theorem relSw_refl (hoff : ∀ r, J r = false → p' r = F.prog r) (x : RR)
    (hx : ∀ i r, (MultiRelay.recList x.1.1.record).getD i none = some r → J r = true → False) :
    relSw F p' b Q J P (Equiv.refl Req') (fun _ => Equiv.refl (W × Req × Option Resp)) x = x := by
  obtain ⟨⟨⟨⟨w, p⟩, rec, store, side, t⟩, q, a⟩, pr⟩ := x
  change (((RelayW.mk (w, p) rec store (sideSw F p' b Q J P rec store t side) t :
      RelayW (DReg W n X Y Req Resp) Req Resp' X Y m (relaySlots n m F) (Fin F.qS → Ys)),
      F.curSw J (Equiv.refl Req') n b Q rec t q, a), pr) = _
  rw [curSw_refl, sideSw_off hoff rec hx]
  rfl

/-- Identity permutations move the response register by the last slot's permutation. -/
theorem respSw_refl : RespSw b Q J (Equiv.refl Resp)
    (fun _ => Equiv.refl (W × Req × Option Resp)) := fun rec w q a => by
  rw [lastSwO_refl]
  simp

/-- **Other programs off `J` give the relay's actions on the records without requests satisfying
`J`.** -/
theorem progSwap_off (hoff : ∀ r, J r = false → p' r = F.prog r) :
    F.ProgSwap p' J (fun _ => False) (Equiv.refl _) (Equiv.refl _) :=
  ⟨hoff, fun _ h => h.elim, fun _ h => h.elim, fun _ h => h.elim, fun _ h => h.elim⟩

/-- `innerMap` of identity permutations and `restSw`, on a record without requests satisfying `J`
for programs equal off `J`, is the identity. -/
theorem innerMap_off (hoff : ∀ r, J r = false → p' r = F.prog r) (x : RR)
    (hx : ∀ i r, (MultiRelay.recList x.1.1.record).getD i none = some r → J r = true → False) :
    innerMap F ((Equiv.refl (W × Req × Option Resp)).prodCongr (Equiv.refl _))
      (restSw F p' b Q J P) x = x := by
  apply (relaySplit W X Y Req Resp Req' Resp' n m (relaySlots n m F) (Fin F.qS → Ys)).injective
  rw [relaySplit_innerMap]
  obtain ⟨⟨⟨⟨w, p⟩, rec, store, side, t⟩, q, a⟩, pr⟩ := x
  change ((w, p), rec, store, sideSw F p' b Q J P rec store t side, t, q, a, pr) = _
  rw [sideSw_off hoff rec hx]
  rfl

/-- **The tear-down, clock and reply with other programs off `J`** are `F`'s on a record without
requests satisfying `J`, before step `k ≠ 0` on a column whose main request register holds the
action's main request and whose side store is read from the record at a clock `t < S`. -/
theorem preFun_withProg_off (hoff : ∀ r, J r = false → p' r = F.prog r) (k : ℕ) (x : RR)
    (hx : MultiRelay.firstJ J (MultiRelay.recList x.1.1.record) = none)
    (hc : k ≠ 0 → x.1.2.1 = askOf (F.actAt n b Q x.1.1.record x.1.1.store x.1.1.side
        x.1.1.time) ∧ x.1.1.side = F.consSide n b Q x.1.1.record x.1.1.store x.1.1.time ∧
      (∃ es, RecAt (n := n) F b Q x.1.1.record es x.1.1.time) ∧
      (x.1.1.time : ℕ) < relaySlots n m F) :
    preFun (F.withProg p') b Q k x = preFun F b Q k x := by
  have hrec := getD_of_none hx
  by_cases hk : k = 0
  · unfold preFun
    simp only [hk, ↓reduceIte]
    rfl
  · have e := preFun_relSw (p' := p') (b := b) (Q := Q) (P := fun _ => False) (sw := Equiv.refl _)
      (πin := fun _ => Equiv.refl (W × Req × Option Resp)) (progSwap_off hoff) rfl rfl
      respSw_refl k x hrec hc (fun h => absurd h hk)
    rw [relSw_refl (P := fun _ => False) hoff x hrec, innerMap_off (P := fun _ => False) hoff _ (by
      rw [(preFun_record_inner (F := F) (b := b) (Q := Q) k x).1]
      exact hrec)] at e
    exact e

/-- **The overlaps into a block of a step of the relayed distinguisher**, read through the record
and set-up undone: a sum over the rows `y` of the controlled step whose record of the starting
slot has the label. -/
theorem sum_label_relay (k : Fin (relaySlots n m F + 1)) (r : Req) (c d : RR) :
    (∑ a : RR, if jLabel F J a.1.1 = some r then
      unitaryMat ((D.relay F b Q).step k) a c * star (unitaryMat ((D.relay F b Q).step k) a d)
      else 0) =
    ∑ y : RR, if jLabel F J (recordFun F b Q D.kind y).1.1 = some r then
      unitaryMat (D.ctrlStep F b Q) y (preFun F b Q k c) *
        star (unitaryMat (D.ctrlStep F b Q) y (preFun F b Q k d)) else 0 := by
  refine Fintype.sum_equiv ((setupPerm F b Q).trans (recordPerm F b Q D.kind)) _ _ fun a => ?_
  have he : ((setupPerm F b Q).trans (recordPerm F b Q D.kind)) a =
      recordFun F b Q D.kind (setupFun F b Q a) := rfl
  rw [he, recordFun_recordFun, D.unitaryMat_relay_step F b Q k a c,
    D.unitaryMat_relay_step F b Q k a d]
  have hl : jLabel F J (setupFun F b Q a).1.1 = jLabel F J a.1.1 := by
    unfold jLabel
    rw [setupFun_record]
  rw [hl]

/-- **The overlaps into a block of a step with other programs off `J`** are `F`'s, from two
columns without requests satisfying `J`. -/
theorem sum_label_relay_off (hoff : ∀ r, J r = false → p' r = F.prog r)
    (k : Fin (relaySlots n m F + 1)) (r : Req) (c d : RR)
    (hc : MultiRelay.firstJ J (MultiRelay.recList c.1.1.record) = none)
    (hd : MultiRelay.firstJ J (MultiRelay.recList d.1.1.record) = none)
    (hgc : (k : ℕ) ≠ 0 → c.1.2.1 = askOf (F.actAt n b Q c.1.1.record c.1.1.store c.1.1.side
        c.1.1.time) ∧ c.1.1.side = F.consSide n b Q c.1.1.record c.1.1.store c.1.1.time ∧
      (∃ es, RecAt (n := n) F b Q c.1.1.record es c.1.1.time) ∧
      (c.1.1.time : ℕ) < relaySlots n m F)
    (hgd : (k : ℕ) ≠ 0 → d.1.2.1 = askOf (F.actAt n b Q d.1.1.record d.1.1.store d.1.1.side
        d.1.1.time) ∧ d.1.1.side = F.consSide n b Q d.1.1.record d.1.1.store d.1.1.time ∧
      (∃ es, RecAt (n := n) F b Q d.1.1.record es d.1.1.time) ∧
      (d.1.1.time : ℕ) < relaySlots n m F) :
    (∑ a : RR, if jLabel F J a.1.1 = some r then
      unitaryMat ((D.relay (F.withProg p') b Q).step k) a c *
        star (unitaryMat ((D.relay (F.withProg p') b Q).step k) a d) else 0) =
    ∑ a : RR, if jLabel F J a.1.1 = some r then
      unitaryMat ((D.relay F b Q).step k) a c * star (unitaryMat ((D.relay F b Q).step k) a d)
      else 0 := by
  rw [sum_label_relay D k r c d]
  have h := sum_label_relay (F := F.withProg p') (b := b) (Q := Q) (J := J) D k r c d
  rw [preFun_withProg_off hoff k c hc hgc, preFun_withProg_off hoff k d hd hgd] at h
  exact h

/-- **The well-formed registers without requests satisfying `J`** are the same for `p'`'s
programs off `J`. -/
theorem goodAt_off (hoff : ∀ r, J r = false → p' r = F.prog r) (k : ℕ) (x : RT)
    (hx : jLabel F J x.1 = none) :
    x ∈ GoodAt (F.withProg p') b Q J Gin k ↔ x ∈ GoodAt F b Q J Gin k := by
  have hp := prog_eq_of_off hoff (getD_of_none hx)
  have hA := MultiRelay.actAt_of_eq (n := n) (b := b) (Q := Q) hp x.1.store x.1.side x.1.time
  have hC : (F.withProg p').consSide n b Q x.1.record x.1.store x.1.time =
      F.consSide n b Q x.1.record x.1.store x.1.time :=
    funext fun i => MultiRelay.consSide_withProg_of_eq n b Q _ _ _ i fun r he => hp i r he
  change (∃ es, (x.1.time : ℕ) = k ∧ RecAt (n := n) F b Q x.1.record es k ∧
    x.2.1 = askOf ((F.withProg p').actAt n b Q x.1.record x.1.store x.1.side x.1.time) ∧
    x.1.side = (F.withProg p').consSide n b Q x.1.record x.1.store x.1.time ∧
    MultiRelay.JTagged J es ∧
    (x.1.inner.1 ∈ Gin es ∨ (es.length = m ∧ F.startAt n b Q es m ≤ k))) ↔ _
  rw [hA, hC]
  rfl

/-- **The `none`-block hypotheses of the relayed distinguisher**: the adversaries of the relayed
distinguishers with `F`'s and with `p'`'s programs, equal off `J`, agree on the rows of label
`none` and have the same overlaps into every block from the columns of label `none`. -/
theorem blockNone_relay (hn : 0 < n) (hI : InnerSupp J Gin D)
    (hoff : ∀ r, J r = false → p' r = F.prog r) (q₀ : ℕ) {O : Type}
    (out out' : RelayW (DReg W n X Y Req Resp) Req Resp' X Y m (relaySlots n m F) (Fin F.qS → Ys) →
        O) :
    ((D.relay F b Q).toAdaptive Nat.one_pos q₀ out).BlockNone
      ((D.relay (F.withProg p') b Q).toAdaptive Nat.one_pos q₀ out').step (jLabel F J)
      (fun k => GoodAt F b Q J Gin k) (fun k => GoodAt (F.withProg p') b Q J Gin k)
      (Good₀ F Gin) (Good₀ (F.withProg p') Gin) where
  none_eq n x hx := goodAt_off hoff n x hx
  none_eq₀ x _ := Iff.rfl
  keepsSet k i a c hc hne := by
    rw [toAdaptive_op] at hne
    change unitaryMat ((D.relay F b Q).stepAt k) a c ≠ 0 at hne
    erw [stepAt_of_lt _ k k.isLt] at hne
    exact relay_step_good J Gin D hn hI ⟨k, k.isLt⟩ a c hc hne
  keepsSet' k i a c hc hne := by
    -- TODO(unbundle-M4): `rw` does not match `toAdaptive_op` against the adversary at
    -- `F.withProg p'`: its implicit shape and instance arguments are spelled through
    -- `F.withProg p'`, the lemma's through the synthesized ones (not isolated); `erw`
    -- bridges the two spellings.
    erw [toAdaptive_op] at hne
    change unitaryMat ((D.relay (F.withProg p') b Q).stepAt k) a c ≠ 0 at hne
    erw [stepAt_of_lt _ k k.isLt] at hne
    exact relay_step_good (F := F.withProg p') J Gin D hn hI ⟨k, k.isLt⟩ a c hc hne
  keeps k i r' a c hcG hc hne := by
    rw [toAdaptive_op] at hne
    change unitaryMat ((D.relay F b Q).stepAt k) a c ≠ 0 at hne
    erw [stepAt_of_lt _ k k.isLt] at hne
    obtain ⟨-, es, hes, ha, -⟩ := relay_step_good_rec J Gin D hn hI ⟨k, k.isLt⟩ a c hcG hne
    change MultiRelay.firstJ J (MultiRelay.recList c.1.1.record) = some r' at hc
    change MultiRelay.firstJ J (MultiRelay.recList a.1.1.record) = some r'
    rw [hes] at hc
    rcases ha with ha | ⟨e, ha, -⟩
    · rw [ha]
      exact hc
    · rw [ha]
      exact MultiRelay.firstJ_append hc e
  keeps' k i r' a c hcG hc hne := by
    -- TODO(unbundle-M4): `rw` does not match `toAdaptive_op` against the adversary at
    -- `F.withProg p'`: its implicit shape and instance arguments are spelled through
    -- `F.withProg p'`, the lemma's through the synthesized ones (not isolated); `erw`
    -- bridges the two spellings.
    erw [toAdaptive_op] at hne
    change unitaryMat ((D.relay (F.withProg p') b Q).stepAt k) a c ≠ 0 at hne
    erw [stepAt_of_lt _ k k.isLt] at hne
    obtain ⟨-, es, hes, ha, -⟩ := relay_step_good_rec (F := F.withProg p') J Gin D hn hI
      ⟨k, k.isLt⟩ a c hcG hne
    change MultiRelay.firstJ J (MultiRelay.recList c.1.1.record) = some r' at hc
    change MultiRelay.firstJ J (MultiRelay.recList a.1.1.record) = some r'
    rw [hes] at hc
    rcases ha with ha | ⟨e, ha, -⟩
    · rw [ha]
      exact hc
    · rw [ha]
      exact MultiRelay.firstJ_append hc e
  row_none_eq k i a c haG hcG ha hc := by
    have e1 := toAdaptive_op_fin (D.relay (F.withProg p') b Q) Nat.one_pos q₀ out' k i
    have e2 := toAdaptive_op_fin (D.relay F b Q) Nat.one_pos q₀ out k i
    obtain ⟨esa, -, -, hqa, hsa, -, -⟩ := haG
    have hs : unitaryMat ((D.relay (F.withProg p') b Q).step ⟨k, k.isLt⟩) a c =
        unitaryMat ((D.relay F b Q).step ⟨k, k.isLt⟩) a c := by
      have hgc := prev_good (Gin := Gin) ⟨k, k.isLt⟩ c hcG
      have := unitaryMat_relay_step_relSw (p' := p') (P := fun _ => False) (sw := Equiv.refl _)
        (πin := fun _ => Equiv.refl (W × Req × Option Resp)) D (progSwap_off (J := J) hoff) rfl
        rfl respSw_refl (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl) ⟨k, k.isLt⟩ a c
        (getD_of_none ha) (getD_of_none hc) hqa hsa hgc.1 hgc.2 (fun _ => by simp)
      rw [relSw_refl (P := fun _ => False) hoff a (getD_of_none ha),
        relSw_refl (P := fun _ => False) hoff c (getD_of_none hc)] at this
      exact this
    exact (congrFun (congrFun e1 a) c).trans (hs.trans (congrFun (congrFun e2 a) c).symm)
  gram_eq k r c d hcG hdG hc hd := by
    have h := sum_label_relay_off (b := b) (Q := Q) (J := J) D hoff ⟨k, k.isLt⟩ r c d hc hd
      (prev_good (Gin := Gin) ⟨k, k.isLt⟩ c hcG).1
      (prev_good (Gin := Gin) ⟨k, k.isLt⟩ d hdG).1
    unfold rowGram
    refine Finset.sum_congr rfl fun i _ => ?_
    have e1 := toAdaptive_op_fin (D.relay (F.withProg p') b Q) Nat.one_pos q₀ out' k i
    have e2 := toAdaptive_op_fin (D.relay F b Q) Nat.one_pos q₀ out k i
    rw [Finset.sum_filter, Finset.sum_filter]
    refine Eq.trans ?_ (h.trans ?_)
    · refine Finset.sum_congr rfl fun a _ => ?_
      exact congrArg (fun M : Matrix _ _ ℂ => if jLabel F J a.1.1 = some r then
        M a c * star (M a d) else 0) e1
    · refine Finset.sum_congr rfl fun a _ => ?_
      exact (congrArg (fun M : Matrix _ _ ℂ => if jLabel F J a.1.1 = some r then
        M a c * star (M a d) else 0) e2).symm
  init_supp a c hac := by
    rw [toAdaptive_init_mat] at hac
    change (D.relay F b Q).init a * star ((D.relay F b Q).init c) ≠ 0 at hac
    exact ⟨good₀_of_init hI a (left_ne_zero_of_mul hac),
      good₀_of_init hI c (fun h0 => hac (by rw [h0, star_zero, mul_zero]))⟩
  init_supp' a c hac := by
    rw [toAdaptive_init_mat] at hac
    change (D.relay F b Q).init a * star ((D.relay F b Q).init c) ≠ 0 at hac
    exact ⟨good₀_of_init hI a (left_ne_zero_of_mul hac),
      good₀_of_init hI c (fun h0 => hac (by rw [h0, star_zero, mul_zero]))⟩

end Distinguisher


end GordieHowe.Quantum
