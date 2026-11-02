-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Pure.MultiRelay

@[expose] public section

/-!
# A relay with other programs

For a relay `F` (`MultiRelay`, `GordieHowe/Model/Quantum/Pure/MultiRelay.lean`) and other programs
`p'` (`MultiRelay.withProg`):

- `MultiRelay.swAt`, `MultiRelay.swOAt`: the permutations of a request's main requests and result
  on the requests of a test `J` (the identity off `J`).
- `SubAct.mapAsk`, `SubAct.mapAsk_refl`, `SubAct.isAsk_mapAsk`, `MultiRelay.curSw`,
  `MultiRelay.lastSwO`: the action of a sub-slot with its main
  request moved, and the permutations of the current and of the last started slot.
- `MultiRelay.curBlk_withProg`, `MultiRelay.startAt_withProg`, `MultiRelay.fillAt_withProg`: the
  schedule is `F`'s.
- `MultiRelay.shapeOf`, `MultiRelay.SameShape`, `MultiRelay.actTag`,
  `MultiRelay.progAct_tag_withProg`, `MultiRelay.next_shape`, `MultiRelay.stAt_shape`,
  `MultiRelay.act_isLeft_shape`, `MultiRelay.isAsk_actAt_shape`: programs of the same shape
  (returned, querying or asking after any answers) give the same states and the same kinds of
  sub-slots.
-/

namespace GordieHowe.Quantum

namespace MultiRelay

variable {X Y Req Resp Req' Resp' Xs Ys : Type} (F : MultiRelay X Y Req Resp Req' Resp' Xs Ys)

/-- **The relay with the programs `p'`**, the budgets and the padding request kept. -/
def withProg (p' : Req → OracleProg ((X ⊕ Xs) ⊕ Req') ((Y ⊕ Ys) ⊕ Option Resp') (Option Resp)) :
    MultiRelay X Y Req Resp Req' Resp' Xs Ys :=
  { F with prog := p' }

variable (p' : Req → OracleProg ((X ⊕ Xs) ⊕ Req') ((Y ⊕ Ys) ⊕ Option Resp') (Option Resp))

theorem len_withProg : (F.withProg p').len = F.len :=
  rfl

variable (J : Req → Bool) (sw : Equiv.Perm Req') (swO : Equiv.Perm Resp)

/-- **The permutation of a request's main requests**: `sw` on `J`, the identity off it. -/
def swAt (r : Req) : Equiv.Perm Req' :=
  if J r then sw else Equiv.refl _

/-- **The permutation of a request's result**: `swO` on `J`, the identity off it. -/
def swOAt (r : Req) : Equiv.Perm Resp :=
  if J r then swO else Equiv.refl _

end MultiRelay

namespace SubAct

variable {X Req' : Type} {n : ℕ}

/-- **The action with its main request moved by `f`.** -/
def mapAsk (f : Req' → Req') : SubAct X Req' n → SubAct X Req' n
  | .pair i => .pair i
  | .query x => .query x
  | .ask r' => .ask (f r')

theorem mapAsk_refl (a : SubAct X Req' n) : a.mapAsk (Equiv.refl Req') = a := by
  cases a <;> rfl

theorem isAsk_mapAsk (f : Req' → Req') (a : SubAct X Req' n) : (a.mapAsk f).isAsk = a.isAsk := by
  cases a <;> rfl

end SubAct

namespace MultiRelay

variable {X Y Req Resp Req' Resp' Xs Ys : Type} (F : MultiRelay X Y Req Resp Req' Resp' Xs Ys)
  (J : Req → Bool) (sw : Equiv.Perm Req') (swO : Equiv.Perm Resp)

/-- **The permutation of the current slot's main requests** at sub-slot `t`: `swAt` of the
current block's request when it is a relayed request, the identity otherwise. -/
def curSw (n b Q : ℕ) {m : ℕ} (rec : Fin m → Option (Option Req)) (t : ℕ) : Equiv.Perm Req' :=
  match F.curBlk n b Q rec t with
  | none => Equiv.refl _
  | some (j, _) =>
    match blkAt b Q (recList rec) j, (recList rec).getD j none with
    | .rel, some r => swAt J sw r
    | _, _ => Equiv.refl _

/-- **The permutation of the last started slot's result**: `swOAt` of its request when it is a
relayed request, the identity otherwise. -/
def lastSwO (b Q : ℕ) {m : ℕ} (rec : Fin m → Option (Option Req)) : Equiv.Perm Resp :=
  if 0 < (recList rec).length then
    match blkAt b Q (recList rec) ((recList rec).length - 1),
      (recList rec).getD ((recList rec).length - 1) none with
    | .rel, some r => swOAt J swO r
    | _, _ => Equiv.refl _
  else Equiv.refl _

variable {F J sw swO} {p' : Req → OracleProg ((X ⊕ Xs) ⊕ Req') ((Y ⊕ Ys) ⊕ Option Resp')
      (Option Resp)}
  {P : Req → Prop}

theorem startAt_withProg (n b Q : ℕ) (es : List (Option Req)) (i : ℕ) :
    (F.withProg p').startAt n b Q es i = F.startAt n b Q es i :=
  rfl

theorem curBlk_withProg (n b Q : ℕ) {m : ℕ} (rec : Fin m → Option (Option Req)) (t : ℕ) :
    (F.withProg p').curBlk n b Q rec t = F.curBlk n b Q rec t :=
  rfl

theorem fillAt_withProg (n b Q : ℕ) {m : ℕ} (rec : Fin m → Option (Option Req)) (t : ℕ) :
    (F.withProg p').fillAt n b Q rec t = F.fillAt n b Q rec t :=
  rfl

variable [Inhabited X] [Zero Y] [Zero Ys] [Inhabited Req']

/-! ### Programs of the same shape -/

/-- **The shape of a program's state**: returned, an oracle query, a main request, or a side
read. -/
def shapeOf {R X' Xs' Req'' : Type} : R ⊕ ((X' ⊕ Xs') ⊕ Req'') → Fin 4
  | .inl _ => 0
  | .inr (.inl (.inl _)) => 1
  | .inr (.inr _) => 2
  | .inr (.inl (.inr _)) => 3

/-- **Programs of the same shape**: after any answers, `p'` and `F`'s programs have both
returned, both query the oracle, both read the side function, or both make a main request. -/
def SameShape (p' : Req → OracleProg ((X ⊕ Xs) ⊕ Req') ((Y ⊕ Ys) ⊕ Option Resp') (Option Resp)) :
    Prop :=
  ∀ r ans, shapeOf ((p' r).after ans) = shapeOf ((F.prog r).after ans)

/-- The tag of an action: none, an oracle query, a main request, or a side read. -/
def actTag {X' Xs' Req'' : Type} : Option ((X' ⊕ Xs') ⊕ Req'') → Fin 4
  | none => 0
  | some (.inl (.inl _)) => 1
  | some (.inr _) => 2
  | some (.inl (.inr _)) => 3

omit [Inhabited X] [Zero Y] [Inhabited Req'] in
theorem progAct_tag_withProg {p' : Req → OracleProg ((X ⊕ Xs) ⊕ Req') ((Y ⊕ Ys) ⊕ Option Resp')
      (Option Resp)}
    (h : F.SameShape p') (r : Req) (st : RelaySt Y Resp' Ys) :
    actTag ((F.withProg p').progAct r st) = actTag (F.progAct r st) := by
  have hs := h r st.ans
  unfold progAct
  simp only [withProg]
  by_cases hl : st.live
  · simp only [hl, ↓reduceIte]
    rcases h1 : (p' r).after st.ans with o | (x | x) | r' <;>
      rcases h2 : (F.prog r).after st.ans with o' | (x' | x') | r'' <;>
      simp only [h1, h2, shapeOf] at hs <;> (try exact absurd hs (by decide)) <;>
      by_cases hq : st.nq < F.qR <;> by_cases hs : st.ns < F.qS <;> by_cases hk : st.na < F.K <;>
      simp [hq, hs, hk, actTag]
  · simp [hl]

omit [Inhabited X] [Zero Y] [Inhabited Req'] in
/-- **The states of a relayed request with programs of the same shape** are `F`'s. -/
theorem next_shape {p' : Req → OracleProg ((X ⊕ Xs) ⊕ Req') ((Y ⊕ Ys) ⊕ Option Resp')
      (Option Resp)}
    (h : F.SameShape p') (r : Req) (st : RelaySt Y Resp' Ys) (a : Option Resp' × (X × Y)) :
    (F.withProg p').next r st a = F.next r st a := by
  have ht := progAct_tag_withProg h r st
  have hl : (((F.withProg p').prog r).after st.ans).isLeft = ((F.prog r).after st.ans).isLeft := by
    have hs := h r st.ans
    change ((p' r).after st.ans).isLeft = _
    rcases h1 : (p' r).after st.ans with o | (x | x) | r' <;>
      rcases h2 : (F.prog r).after st.ans with o' | (x' | x') | r'' <;>
      simp only [h1, h2, shapeOf] at hs <;> first | exact absurd hs (by decide) | rfl
  unfold next
  rcases h1 : (F.withProg p').progAct r st with _ | ((x | x) | r') <;>
    rcases h2 : F.progAct r st with _ | ((x' | x') | r'') <;>
    simp only [h1, h2, actTag] at ht <;> (try exact absurd ht (by decide))
  · simp only
    rw [hl]
    rfl
  · rfl
  · rfl
  · rfl

omit [Inhabited X] [Zero Y] [Inhabited Req'] in
/-- **A side step with programs of the same shape** is `F`'s, for side answers that do not read
the side point. -/
theorem sideStep_shape {p' : Req → OracleProg ((X ⊕ Xs) ⊕ Req') ((Y ⊕ Ys) ⊕ Option Resp')
      (Option Resp)}
    (h : F.SameShape p') {sa : ℕ → Xs → Ys} (hsa : ∀ k x x', sa k x = sa k x') (r : Req)
    (st : RelaySt Y Resp' Ys) : (F.withProg p').sideStep sa r st = F.sideStep sa r st := by
  have ht := progAct_tag_withProg h r st
  unfold sideStep
  rcases h1 : (F.withProg p').progAct r st with _ | ((x | x) | r') <;>
    rcases h2 : F.progAct r st with _ | ((x' | x') | r'') <;>
    simp only [h1, h2, actTag] at ht <;> (try exact absurd ht (by decide)) <;> try rfl
  simp only
  rw [hsa st.ns x x']

omit [Inhabited X] [Zero Y] [Inhabited Req'] in
theorem close_shape {p' : Req → OracleProg ((X ⊕ Xs) ⊕ Req') ((Y ⊕ Ys) ⊕ Option Resp')
      (Option Resp)}
    (h : F.SameShape p') {sa : ℕ → Xs → Ys} (hsa : ∀ k x x', sa k x = sa k x') (r : Req)
    (st : RelaySt Y Resp' Ys) : (F.withProg p').close sa r st = F.close sa r st := by
  unfold close
  rw [show (F.withProg p').sideStep sa r = F.sideStep sa r from
    funext (sideStep_shape h hsa r)]
  rfl

omit [Inhabited X] [Zero Y] [Inhabited Req'] in
theorem stAt_shape {p' : Req → OracleProg ((X ⊕ Xs) ⊕ Req') ((Y ⊕ Ys) ⊕ Option Resp')
      (Option Resp)}
    (h : F.SameShape p') {sa : ℕ → Xs → Ys} (hsa : ∀ k x x', sa k x = sa k x') (r : Req)
    (g : ℕ → Option Resp' × (X × Y)) :
    ∀ i, (F.withProg p').stAt sa r g i = F.stAt sa r g i
  | 0 => rfl
  | i + 1 => by
    rw [stAt, stAt, stAt_shape h hsa r g i, next_shape h, close_shape h hsa]

omit [Zero Y] [Inhabited Req'] in
theorem act_isLeft_shape {p' : Req → OracleProg ((X ⊕ Xs) ⊕ Req') ((Y ⊕ Ys) ⊕ Option Resp')
      (Option Resp)}
    (h : F.SameShape p') (r : Req) (st : RelaySt Y Resp' Ys) :
    ((F.withProg p').act r st).isLeft = (F.act r st).isLeft := by
  have ht := progAct_tag_withProg h r st
  unfold act
  rcases h1 : (F.withProg p').progAct r st with _ | ((x | x) | r') <;>
    rcases h2 : F.progAct r st with _ | ((x' | x') | r'') <;>
    simp only [h1, h2, actTag] at ht <;> (try exact absurd ht (by decide))
  · rfl
  · rfl
  · change (if st.np < F.qP then (Sum.inl (Sum.inr x) : (X ⊕ Xs) ⊕ Req')
        else if st.na < F.K then Sum.inr F.idle else Sum.inl (Sum.inl default)).isLeft =
      (if st.np < F.qP then (Sum.inl (Sum.inr x') : (X ⊕ Xs) ⊕ Req')
        else if st.na < F.K then Sum.inr F.idle else Sum.inl (Sum.inl default)).isLeft
    split_ifs <;> rfl
  · rfl

/-- **The kind of a sub-slot with programs of the same shape** is `F`'s. -/
theorem isAsk_actAt_shape {p' : Req → OracleProg ((X ⊕ Xs) ⊕ Req') ((Y ⊕ Ys) ⊕ Option Resp')
      (Option Resp)}
    (h : F.SameShape p') {n b Q m S : ℕ} (rec : Fin m → Option (Option Req))
    (store : Fin S → Option Resp' × (X × Y)) (side : Fin m → Fin F.qS → Ys) (t : ℕ) :
    ((F.withProg p').actAt n b Q rec store side t).isAsk =
      (F.actAt n b Q rec store side t).isAsk := by
  unfold actAt
  rw [curBlk_withProg]
  rcases F.curBlk n b Q rec t with _ | ⟨j, sub⟩
  · rfl
  · simp only
    rcases MultiRelay.blkAt b Q (recList rec) j with _ | _ | _ <;>
      rcases (recList rec).getD j none with _ | r <;> simp only
    · split_ifs <;> rfl
    · split_ifs <;> rfl
    · rfl
    · rfl
    · rfl
    · rw [show (F.withProg p').vecSa ((F.withProg p').vecAt side j) = F.vecSa (F.vecAt side j)
          from rfl, stAt_shape h (F.vecSa_point _), startAt_withProg]
      have := act_isLeft_shape h r
        (F.stAt (F.vecSa (F.vecAt side j)) r
          (fun k => storeAt store (F.startAt n b Q (recList rec) j + k)) sub)
      rcases h1 : (F.withProg p').act r
          (F.stAt (F.vecSa (F.vecAt side j)) r
            (fun k => storeAt store (F.startAt n b Q (recList rec) j + k)) sub) with
          (x | x) | r' <;>
        rcases h2 : F.act r
          (F.stAt (F.vecSa (F.vecAt side j)) r
            (fun k => storeAt store (F.startAt n b Q (recList rec) j + k)) sub) with
          (x' | x') | r'' <;>
        simp only [h1, h2, Sum.isLeft_inl, Sum.isLeft_inr] at this <;> first
          | exact absurd this (by decide) | rfl

/-! ### The pad sub-slot -/

omit [Inhabited X] [Zero Y] [Zero Ys] [Inhabited Req'] in
/-- **Whether a program begins with a side read is read from its shape.** -/
theorem startsSide_eq_shapeOf {R : Type} (p : OracleProg ((X ⊕ Xs) ⊕ Req') ((Y ⊕ Ys) ⊕ Option Resp')
    R) :
    p.startsSide = decide (shapeOf (p.after []) = 3) := by
  cases p with
  | pure _ => rfl
  | query a k => rcases a with (x | x) | r' <;> rfl

omit [Inhabited X] [Zero Y] [Zero Ys] [Inhabited Req'] in
/-- **The pad decision with programs of the same shape** is `F`'s: a pad sub-slot exactly when
`F`'s program begins with a side read. -/
theorem startsSide_shape {p' : Req → OracleProg ((X ⊕ Xs) ⊕ Req') ((Y ⊕ Ys) ⊕ Option Resp')
      (Option Resp)}
    (h : F.SameShape p') (r : Req) : (p' r).startsSide = (F.prog r).startsSide := by
  rw [startsSide_eq_shapeOf, startsSide_eq_shapeOf, h r []]

omit [Zero Y] [Zero Ys] [Inhabited Req'] in
/-- **The pad's stored pair is never read**: at a side read the state after the sub-slot does not
depend on the sub-slot's stored answer. -/
theorem next_pad (r : Req) (st : RelaySt Y Resp' Ys) {x : Xs}
    (hp : F.progAct r st = some (.inl (.inr x))) (a a' : Option Resp' × (X × Y)) :
    F.next r st a = F.next r st a' := by
  unfold next
  rw [hp]

omit [Inhabited X] [Zero Y] [Zero Ys] [Inhabited Req'] in
/-- **Before the first sub-slot no side answer is read.** -/
theorem stAt_zero (sa : ℕ → Xs → Ys) (r : Req) (g : ℕ → Option Resp' × (X × Y)) :
    F.stAt sa r g 0 = .init :=
  rfl

/-- **The action of a block's first sub-slot does not read the side store**: in particular the
pad point `default` and the pad's stored pair do not depend on it. -/
theorem actAt_side_of_sub_zero {n b Q m S : ℕ} {rec : Fin m → Option (Option Req)} {t j : ℕ}
    (hc : F.curBlk n b Q rec t = some (j, 0)) (store : Fin S → Option Resp' × (X × Y))
    (side side' : Fin m → Fin F.qS → Ys) :
    F.actAt n b Q rec store side t = F.actAt n b Q rec store side' t := by
  unfold actAt
  rw [hc]
  rfl

end MultiRelay

end GordieHowe.Quantum
