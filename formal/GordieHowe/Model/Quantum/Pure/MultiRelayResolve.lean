-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Pure.MultiRelaySwap
public import GordieHowe.Model.Quantum.Pure.MultiRelayRun
public import GordieHowe.Model.Quantum.Pure.MultiRelaySim

@[expose] public section

set_option linter.unusedSectionVars false

/-!
# Relay programs with their side reads resolved

A relay program (`MultiRelay`) reads its side function classically. Resolving its side reads by a
side function `s` (`OracleProg.resolve`) gives a program over oracle queries and main requests
alone. Two relay programs whose resolved forms agree up to permutations of the main requests and
results (`MultiRelay.ProgSwap`) may read the side function at different points: their relayed
requests make the same queries and main requests, moved by the permutations, while their side
answers differ.

- `OracleProg.embedAns`, `OracleProg.plainAns?`, `OracleProg.plainList`: the answers to oracle
  queries and main requests inside the answers of a relay program.
- `OracleProg.resolve`: the program with its side reads answered by `s`.
- `OracleProg.rest`: the program after a list of answers. `OracleProg.Consistent`: answers whose
  side answers are `s` at the side reads and whose other answers answer queries and main requests.
  `OracleProg.after_resolve`: the resolved program after the answers' plain part is the resolved
  rest.
- `OracleProg.SidesLE`: at most `q` side reads on every path.
- `OracleProg.resolve_after_map`, `OracleProg.sidesLE_of_after_map`,
  `OracleProg.startsSide_of_after_map`: programs whose states move along permutations of the
  results and main requests, side reads kept.
- `OracleProg.embedAns_of_plainAns?`, `OracleProg.plainList_append`, `OracleProg.after_eq_rest`,
  `OracleProg.Consistent.append_side`, `OracleProg.Consistent.append_plain`,
  `OracleProg.Consistent.nil`, `OracleProg.rest_append`, `OracleProg.rest_nil`,
  `OracleProg.rest_of_after`, `OracleProg.ofView`, `OracleProg.resolve_after_nil`,
  `OracleProg.after_eq_ofView`, `OracleProg.ofView_map`: the states of a program at answers
  consistent with `s`, read back from its resolved form.
- `MultiRelay.ProgSwap`: other programs whose resolved forms are `F`'s with the main requests
  moved by `sw` and the results by `swO`, on the requests satisfying `P`, and `F`'s off `J`.
  `MultiRelay.ProgSwap.of_sidePoints`: from programs whose states, side reads included, move
  alike. `MultiRelay.ProgSwap.self`, `MultiRelay.sameShape_self`: `F`'s own programs.
- `MultiRelay.stAt_ans_le`, `MultiRelay.sideInv_stAt`, `MultiRelay.ns_stAt_le`,
  `MultiRelay.stAt_vecSa`, `MultiRelay.addsVec_stAt`: the states of a relayed request with its
  side reads answered by the side function, and their side vectors.
- `MultiRelay.Closed`, `MultiRelay.ResInv`, `MultiRelay.progAct_plain`, `MultiRelay.resInv_init`,
  `MultiRelay.resInv_sideStep`, `MultiRelay.resInv_iterate_sideStep`, `MultiRelay.resInv_next`,
  `MultiRelay.closed_close`, `MultiRelay.sideStep_plain`, `MultiRelay.close_plain`: those states
  have answers consistent with the side function within the side budget, and are past their side
  reads after a sub-slot.
- `MultiRelay.StRel`, `MultiRelay.ActRel`, `MultiRelay.after_withProg`,
  `MultiRelay.actRel_of_after`, `MultiRelay.next_rel`, `MultiRelay.close_rel`,
  `MultiRelay.actRel_at`, **`MultiRelay.stAt_withProg`**: with programs `p'` related by
  `ProgSwap`, the states of a relayed request on `P` are alike but for their side answers.
- `MultiRelay.actSub`, `MultiRelay.actSub_act_of_rel`, `MultiRelay.actSub_withProg`,
  `MultiRelay.reply_withProg`, `MultiRelay.actSub_withProg_at`: their sub-slots, the main request
  moved by `sw`, and their replies, moved by `swO`.
- `MultiRelay.progAct_of_eq`, `MultiRelay.sideStep_of_eq`, `MultiRelay.close_of_eq`,
  `MultiRelay.next_of_eq`, `MultiRelay.act_of_eq`, `MultiRelay.stAt_of_eq`,
  `MultiRelay.reply_of_eq`, `MultiRelay.actAt_of_eq`, `MultiRelay.lastReply_of_eq`: programs equal
  at a request, or at the started requests, act alike.
- **`MultiRelay.actAt_withProg`**, **`MultiRelay.lastReply_withProg`**: the action of a sub-slot
  and the reply of the last started slot with `p'`, read from side stores agreeing with the side
  function at the current or the last block, are `F`'s moved by the current or the last slot's
  permutation.
-/

namespace GordieHowe

namespace OracleProg

variable {X Xs Req' Y Ys Resp' R : Type}

/-- **An answer to an oracle query or a main request** as an answer of a relay program. -/
def embedAns : (Y ⊕ Option Resp') → (Y ⊕ Ys) ⊕ Option Resp'
  | .inl y => .inl (.inl y)
  | .inr a => .inr a

/-- **The answer to an oracle query or a main request**, `none` for a side answer. -/
def plainAns? : ((Y ⊕ Ys) ⊕ Option Resp') → Option (Y ⊕ Option Resp')
  | .inl (.inl y) => some (.inl y)
  | .inl (.inr _) => none
  | .inr a => some (.inr a)

theorem embedAns_of_plainAns? {b : (Y ⊕ Ys) ⊕ Option Resp'} {b' : Y ⊕ Option Resp'}
    (h : plainAns? b = some b') : embedAns b' = b := by
  rcases b with (y | y) | a <;> simp only [plainAns?, Option.some.injEq, reduceCtorEq] at h <;>
    subst h <;> rfl

/-- **The answers to oracle queries and main requests**, in order. -/
def plainList (l : List ((Y ⊕ Ys) ⊕ Option Resp')) : List (Y ⊕ Option Resp') :=
  l.filterMap plainAns?

theorem plainList_append (l l' : List ((Y ⊕ Ys) ⊕ Option Resp')) :
    plainList (l ++ l') = plainList l ++ plainList l' :=
  List.filterMap_append

/-- **The program with its side reads answered by `s`**: its oracle queries and main requests,
each side read of `x` answered by `s x`. -/
def resolve (s : Xs → Ys) :
    OracleProg ((X ⊕ Xs) ⊕ Req') ((Y ⊕ Ys) ⊕ Option Resp') R →
      OracleProg (X ⊕ Req') (Y ⊕ Option Resp') R
  | pure r => pure r
  | query (.inl (.inr x)) k => resolve s (k (.inl (.inr (s x))))
  | query (.inl (.inl x)) k => query (.inl x) fun b => resolve s (k (embedAns b))
  | query (.inr r') k => query (.inr r') fun b => resolve s (k (embedAns b))

/-- **The program after the answers `ans`.** -/
def rest {A B : Type} : OracleProg A B R → List B → OracleProg A B R
  | pure r, _ => pure r
  | p, [] => p
  | query _ k, b :: bs => rest (k b) bs

theorem after_eq_rest {A B : Type} : ∀ (p : OracleProg A B R) (ans : List B),
    p.after ans = (p.rest ans).after []
  | pure _, _ => rfl
  | query _ _, [] => rfl
  | query _ k, b :: bs => after_eq_rest (k b) bs

/-- **Answers consistent with the side function `s`**: each side read of `x` answered by `s x`,
each oracle query or main request by an answer to one. -/
def Consistent (s : Xs → Ys) :
    OracleProg ((X ⊕ Xs) ⊕ Req') ((Y ⊕ Ys) ⊕ Option Resp') R → List ((Y ⊕ Ys) ⊕ Option Resp') →
      Prop
  | pure _, _ => True
  | query _ _, [] => True
  | query a k, b :: bs =>
    (match a with
      | .inl (.inr x) => b = .inl (.inr (s x))
      | _ => (plainAns? b).isSome) ∧ Consistent s (k b) bs

/-- **The resolved program after the plain answers** is the resolved program after the answers. -/
theorem after_resolve (s : Xs → Ys) :
    ∀ (p : OracleProg ((X ⊕ Xs) ⊕ Req') ((Y ⊕ Ys) ⊕ Option Resp') R) (ans), Consistent s p ans →
      (resolve s p).after (plainList ans) = (resolve s (p.rest ans)).after []
  | pure _, _, _ => rfl
  | query _ _, [], _ => rfl
  | query a k, b :: bs, h => by
    obtain ⟨hb, hc⟩ := h
    rcases a with (x | x) | r'
    · simp only at hb
      obtain ⟨b', hb'⟩ := Option.isSome_iff_exists.1 hb
      have he := embedAns_of_plainAns? hb'
      have hl : plainList (b :: bs) = b' :: plainList bs := by
        simp [plainList, hb']
      rw [hl]
      show (resolve s (k (embedAns b'))).after (plainList bs) = _
      rw [he]
      exact after_resolve s (k b) bs hc
    · simp only at hb
      subst hb
      have hl : plainList ((.inl (.inr (s x)) : (Y ⊕ Ys) ⊕ Option Resp') :: bs) =
          plainList bs := by
        simp [plainList, List.filterMap_cons, plainAns?]
      rw [hl]
      exact after_resolve s (k _) bs hc
    · simp only at hb
      obtain ⟨b', hb'⟩ := Option.isSome_iff_exists.1 hb
      have he := embedAns_of_plainAns? hb'
      have hl : plainList (b :: bs) = b' :: plainList bs := by
        simp [plainList, hb']
      rw [hl]
      show (resolve s (k (embedAns b'))).after (plainList bs) = _
      rw [he]
      exact after_resolve s (k b) bs hc

/-- An answer appended at a side read of `x` answered by `s x` keeps the answers consistent. -/
theorem Consistent.append_side {s : Xs → Ys} :
    ∀ {p : OracleProg ((X ⊕ Xs) ⊕ Req') ((Y ⊕ Ys) ⊕ Option Resp') R} {ans} {x : Xs},
      Consistent s p ans → p.after ans = .inr (.inl (.inr x)) →
        Consistent s p (ans ++ [.inl (.inr (s x))])
  | pure _, _, _, _, h => by simp [after] at h
  | query a k, [], x, _, h => by
    simp only [after_query_nil, Sum.inr.injEq] at h
    subst h
    exact ⟨rfl, by cases k (.inl (.inr (s x))) <;> trivial⟩
  | query a k, b :: bs, x, hc, h => ⟨hc.1, Consistent.append_side hc.2 h⟩

/-- An answer to an oracle query or a main request appended at one keeps the answers consistent. -/
theorem Consistent.append_plain {s : Xs → Ys} :
    ∀ {p : OracleProg ((X ⊕ Xs) ⊕ Req') ((Y ⊕ Ys) ⊕ Option Resp') R} {ans}
      {a : (X ⊕ Xs) ⊕ Req'} {b : (Y ⊕ Ys) ⊕ Option Resp'},
      Consistent s p ans → p.after ans = .inr a → (∀ x, a ≠ .inl (.inr x)) →
        (plainAns? b).isSome → Consistent s p (ans ++ [b])
  | pure _, _, _, _, _, h, _, _ => by simp [after] at h
  | query a' k, [], a, b, _, h, ha, hb => by
    simp only [after_query_nil, Sum.inr.injEq] at h
    subst h
    refine ⟨?_, by cases k b <;> trivial⟩
    rcases a' with (x | x) | r'
    · exact hb
    · exact absurd rfl (ha x)
    · exact hb
  | query a' k, b' :: bs, a, b, hc, h, ha, hb => ⟨hc.1, Consistent.append_plain hc.2 h ha hb⟩

/-- **At most `q` side reads on every path.** -/
def SidesLE : ℕ → OracleProg ((X ⊕ Xs) ⊕ Req') ((Y ⊕ Ys) ⊕ Option Resp') R → Prop
  | _, pure _ => True
  | q, query (.inl (.inr _)) k => 0 < q ∧ ∀ b, SidesLE (q - 1) (k b)
  | q, query _ k => ∀ b, SidesLE q (k b)

/-- The program after the answers and one more answer. -/
theorem rest_append {A B : Type} : ∀ (p : OracleProg A B R) (ans : List B) (b : B),
    p.rest (ans ++ [b]) = match p.rest ans with
      | pure r => pure r
      | query _ k => k b
  | pure _, _, _ => rfl
  | query _ k, [], b => by
    show (k b).rest [] = k b
    cases k b <;> rfl
  | query _ k, c :: cs, b => rest_append (k c) cs b

/-- The state of a program not at a side read, read back from its view. -/
def ofView : R ⊕ (X ⊕ Req') → R ⊕ ((X ⊕ Xs) ⊕ Req')
  | .inl o => .inl o
  | .inr (.inl x) => .inr (.inl (.inl x))
  | .inr (.inr r') => .inr (.inr r')

/-- **A program not at a side read**: its resolved state is the view of its state. -/
theorem resolve_after_nil (s : Xs → Ys)
    (q : OracleProg ((X ⊕ Xs) ⊕ Req') ((Y ⊕ Ys) ⊕ Option Resp') R)
    (hq : ∀ x, q.after [] ≠ .inr (.inl (.inr x))) :
    q.after [] = ofView ((resolve s q).after []) := by
  cases q with
  | pure o => rfl
  | query a k =>
    rcases a with (x | x) | r'
    · rfl
    · exact absurd rfl (hq x)
    · rfl

/-- **The state of a program at consistent answers, not at a side read**, read back from the
resolved program's state after the answers' plain part. -/
theorem after_eq_ofView (s : Xs → Ys)
    {p : OracleProg ((X ⊕ Xs) ⊕ Req') ((Y ⊕ Ys) ⊕ Option Resp') R}
    {ans : List ((Y ⊕ Ys) ⊕ Option Resp')} (hc : Consistent s p ans)
    (hq : ∀ x, p.after ans ≠ .inr (.inl (.inr x))) :
    p.after ans = ofView ((resolve s p).after (plainList ans)) := by
  rw [after_resolve s p ans hc, after_eq_rest]
  rw [after_eq_rest] at hq
  exact resolve_after_nil s _ hq

/-- `ofView` commutes with moving the result and the main request. -/
theorem ofView_map {R' : Type} (f : R → R') (sw : Req' → Req') (v : R ⊕ (X ⊕ Req')) :
    ofView (Sum.map f (Sum.map id sw) v) =
      Sum.map f (Sum.map id sw) (ofView (Xs := Xs) v) := by
  rcases v with o | x | r' <;> rfl

theorem Consistent.nil (s : Xs → Ys)
    (p : OracleProg ((X ⊕ Xs) ⊕ Req') ((Y ⊕ Ys) ⊕ Option Resp') R) : Consistent s p [] := by
  cases p <;> trivial

theorem rest_nil {A B : Type} (p : OracleProg A B R) : p.rest [] = p := by
  cases p <;> rfl

theorem rest_of_after {A B : Type} {p : OracleProg A B R} {ans : List B} {a : A}
    (h : p.after ans = .inr a) : ∃ k, p.rest ans = query a k := by
  rw [after_eq_rest] at h
  rcases hr : p.rest ans with o | ⟨a', k⟩
  · rw [hr] at h
    cases h
  · rw [hr] at h
    cases h
    exact ⟨k, rfl⟩

section Map

variable {R' : Type} (f : R → R') (sw : Req' → Req')

/-- **Programs whose states move along `f` and `sw`** after any answers have resolved forms whose
states move alike. -/
theorem resolve_after_map (s : Xs → Ys) :
    ∀ (p : OracleProg ((X ⊕ Xs) ⊕ Req') ((Y ⊕ Ys) ⊕ Option Resp') R)
      (p' : OracleProg ((X ⊕ Xs) ⊕ Req') ((Y ⊕ Ys) ⊕ Option Resp') R'),
      (∀ ans, p'.after ans = Sum.map f (Sum.map id sw) (p.after ans)) →
      ∀ ans, (resolve s p').after ans = Sum.map f (Sum.map id sw) ((resolve s p).after ans)
  | pure o, p', h, ans => by
    cases p' with
    | pure o' =>
      have h0 := h []
      simp only [after_pure, Sum.map_inl, Sum.inl.injEq] at h0
      subst h0
      rfl
    | query a k =>
      have h0 := h []
      simp at h0
  | query a k, p', h, ans => by
    cases p' with
    | pure o' =>
      have h0 := h []
      simp at h0
    | query a' k' =>
      have hk : ∀ b ans, (k' b).after ans = Sum.map f (Sum.map id sw) ((k b).after ans) :=
        fun b ans => h (b :: ans)
      have h0 := h []
      rcases a with (x | x) | r' <;>
        simp only [after_query_nil, Sum.map_inr, Sum.map_inl, id, Sum.inr.injEq] at h0 <;>
        subst h0
      · cases ans with
        | nil => rfl
        | cons b bs => exact resolve_after_map s (k (embedAns b)) (k' (embedAns b)) (hk _) bs
      · exact resolve_after_map s (k _) (k' _) (hk _) ans
      · cases ans with
        | nil => rfl
        | cons b bs => exact resolve_after_map s (k (embedAns b)) (k' (embedAns b)) (hk _) bs

/-- **Programs whose states move along `f` and `sw`** make the same side reads. -/
theorem sidesLE_of_after_map :
    ∀ (q : ℕ) (p : OracleProg ((X ⊕ Xs) ⊕ Req') ((Y ⊕ Ys) ⊕ Option Resp') R)
      (p' : OracleProg ((X ⊕ Xs) ⊕ Req') ((Y ⊕ Ys) ⊕ Option Resp') R'),
      (∀ ans, p'.after ans = Sum.map f (Sum.map id sw) (p.after ans)) →
      SidesLE q p → SidesLE q p'
  | q, pure o, p', h, _ => by
    cases p' with
    | pure o' => trivial
    | query a k =>
      have h0 := h []
      simp at h0
  | q, query a k, p', h, hs => by
    cases p' with
    | pure o' => trivial
    | query a' k' =>
      have hk : ∀ b ans, (k' b).after ans = Sum.map f (Sum.map id sw) ((k b).after ans) :=
        fun b ans => h (b :: ans)
      have h0 := h []
      rcases a with (x | x) | r' <;>
        simp only [after_query_nil, Sum.map_inr, Sum.map_inl, id, Sum.inr.injEq] at h0 <;>
        subst h0
      · exact fun b => sidesLE_of_after_map q (k b) (k' b) (hk b) (hs b)
      · exact ⟨hs.1, fun b => sidesLE_of_after_map (q - 1) (k b) (k' b) (hk b) (hs.2 b)⟩
      · exact fun b => sidesLE_of_after_map q (k b) (k' b) (hk b) (hs b)

/-- **Programs whose states move along `f` and `sw`** begin with a side read alike. -/
theorem startsSide_of_after_map {p : OracleProg ((X ⊕ Xs) ⊕ Req') ((Y ⊕ Ys) ⊕ Option Resp') R}
    {p' : OracleProg ((X ⊕ Xs) ⊕ Req') ((Y ⊕ Ys) ⊕ Option Resp') R'}
    (h : ∀ ans, p'.after ans = Sum.map f (Sum.map id sw) (p.after ans)) :
    p'.startsSide = p.startsSide := by
  have h0 := h []
  cases p with
  | pure o =>
    cases p' with
    | pure o' => rfl
    | query a k => simp at h0
  | query a k =>
    cases p' with
    | pure o' => simp at h0
    | query a' k' =>
      rcases a with (x | x) | r' <;>
        simp only [after_query_nil, Sum.map_inr, Sum.map_inl, id, Sum.inr.injEq] at h0 <;>
        subst h0 <;> rfl

end Map

end OracleProg

namespace Quantum

namespace MultiRelay

open OracleProg

variable {X Y Req Resp Req' Resp' Xs Ys : Type} (F : MultiRelay X Y Req Resp Req' Resp' Xs Ys)
  (p' : Req → OracleProg ((X ⊕ Xs) ⊕ Req') ((Y ⊕ Ys) ⊕ Option Resp') (Option Resp))

/-- **Other programs whose resolved forms move the main requests and results of the requests
satisfying `P`**: the programs `p'` are `F`'s on the requests failing `J`; on the requests
satisfying `P`, both programs make at most `qS` side reads on every path and begin with a side read
alike, and the program `p'` with its side reads answered by the side function is `F`'s with the
main request moved by `sw` and the result by `swO`. -/
structure ProgSwap (J : Req → Bool) (P : Req → Prop) (sw : Equiv.Perm Req')
    (swO : Equiv.Perm Resp) : Prop where
  /-- The programs off `J`. -/
  off : ∀ r, J r = false → p' r = F.prog r
  /-- The side reads of `F`'s programs on `P`. -/
  sides : ∀ r, P r → SidesLE F.qS (F.prog r)
  /-- The side reads of the programs `p'` on `P`. -/
  sides' : ∀ r, P r → SidesLE F.qS (p' r)
  /-- The pad sub-slots on `P`. -/
  starts : ∀ r, P r → (p' r).startsSide = (F.prog r).startsSide
  /-- The resolved programs on `P`. -/
  on : ∀ r, P r → ∀ ans, (resolve F.side (p' r)).after ans =
    Sum.map (Option.map swO) (Sum.map id sw) ((resolve F.side (F.prog r)).after ans)

/-- **The programs off `J` ask main requests fixed by `sw`**: on every request failing `J`, the
resolved program of `F` with `sw` applied to its main requests is the resolved program. -/
def OffTagFixed (J : Req → Bool) (sw : Equiv.Perm Req') : Prop :=
  ∀ r, J r = false → ∀ ans, Sum.map id (Sum.map id sw) ((resolve F.side (F.prog r)).after ans) =
    (resolve F.side (F.prog r)).after ans

variable {F p'} in
/-- **Programs whose states move the main requests and results of the requests satisfying `P`**,
making at most `qS` side reads on `P`, at the same side points as `F`'s: their resolved forms move
alike. -/
theorem ProgSwap.of_sidePoints {J : Req → Bool} {P : Req → Prop} {sw : Equiv.Perm Req'}
    {swO : Equiv.Perm Resp} (off : ∀ r, J r = false → p' r = F.prog r)
    (sides : ∀ r, P r → SidesLE F.qS (F.prog r))
    (on : ∀ r, P r → ∀ ans, (p' r).after ans =
      Sum.map (Option.map swO) (Sum.map id sw) ((F.prog r).after ans)) :
    F.ProgSwap p' J P sw swO where
  off := off
  sides := sides
  sides' r hr := sidesLE_of_after_map _ _ F.qS _ _ (on r hr) (sides r hr)
  starts r hr := startsSide_of_after_map _ _ (on r hr)
  on r hr := resolve_after_map _ _ F.side _ _ (on r hr)

variable {F} in
/-- **`F`'s own programs** move nothing, when they make at most `qS` side reads on `P`. -/
theorem ProgSwap.self {J : Req → Bool} {P : Req → Prop}
    (sides : ∀ r, P r → SidesLE F.qS (F.prog r)) :
    F.ProgSwap F.prog J P (Equiv.refl _) (Equiv.refl _) :=
  ProgSwap.of_sidePoints (fun _ _ => rfl) sides fun r _ ans => by
    rcases (F.prog r).after ans with o | (x | x) | r' <;> simp

variable {F} in
/-- **`F`'s own programs have its shape.** -/
theorem sameShape_self : F.SameShape F.prog := fun _ _ => rfl

/-! ### The states of a relayed request on any stored answers -/

section StAt

variable [Inhabited X] [Zero Y] [Zero Ys] [Inhabited Req']

omit [Zero Y] [Inhabited Req'] in
/-- The answers fed after more sub-slots extend the earlier ones. -/
theorem stAt_ans_le (sa : ℕ → Xs → Ys) (r : Req) (g : ℕ → Option Resp' × (X × Y)) {i j : ℕ}
    (hij : i ≤ j) : ∃ l, (F.stAt sa r g j).ans = (F.stAt sa r g i).ans ++ l := by
  induction j, hij using Nat.le_induction with
  | base => exact ⟨[], by simp⟩
  | succ j _ ih =>
    obtain ⟨l₁, h₁⟩ := ih
    obtain ⟨l₂, h₂⟩ := F.close_next_ans sa r (F.stAt sa r g j) (g j)
    exact ⟨l₁ ++ l₂, by rw [stAt, h₂, h₁, List.append_assoc]⟩

omit [Zero Y] [Inhabited Req'] in
/-- **The side answers of a relayed request's states are its side reads.** -/
theorem sideInv_stAt (sa : ℕ → Xs → Ys) (r : Req) (g : ℕ → Option Resp' × (X × Y)) :
    ∀ i, SideInv (F.stAt sa r g i)
  | 0 => rfl
  | i + 1 => F.sideInv_iterate_sideStep _ r _ (F.sideInv_next r _ (sideInv_stAt sa r g i))

omit [Zero Y] [Inhabited Req'] in
theorem ns_stAt_le (sa : ℕ → Xs → Ys) (r : Req) (g : ℕ → Option Resp' × (X × Y)) {i j : ℕ}
    (hij : i ≤ j) : (F.stAt sa r g i).ns ≤ (F.stAt sa r g j).ns := by
  obtain ⟨l, hl⟩ := F.stAt_ans_le sa r g hij
  have h1 := F.sideInv_stAt sa r g i
  have h2 := F.sideInv_stAt sa r g j
  unfold SideInv at h1 h2
  rw [hl, sideVals_append, List.length_append] at h2
  omega

omit [Inhabited Req'] in
/-- **The states of a relayed request, its side reads answered from an agreeing side vector**,
are those with the side reads answered by the side function. -/
theorem stAt_vecSa (r : Req) (g : ℕ → Option Resp' × (X × Y)) {V : Fin F.qS → Ys} :
    ∀ i, F.VecAgrees V (F.stAt F.sideSa r g i) → F.stAt (F.vecSa V) r g i = F.stAt F.sideSa r g i
  | 0, _ => rfl
  | i + 1, hV => by
    have hV' : F.VecAgrees V (F.stAt F.sideSa r g i) :=
      hV.of_prefix (F.sideInv_stAt _ r g i) (F.stAt_ans_le _ r g (Nat.le_succ i))
        (F.ns_stAt_le _ r g (Nat.le_succ i))
    rw [stAt, stAt, stAt_vecSa r g i hV']
    exact F.close_vecSa r (F.sideInv_next r _ (F.sideInv_stAt _ r g i)) hV

end StAt

section Adds

variable [Inhabited X] [Zero Y] [AddGroup Ys] [Inhabited Req']

omit [Inhabited Req'] in
/-- **The side additions after sub-slot `s` rebuild the side vector** of the state after it from
that before it, on any stored answers. -/
theorem addsVec_stAt (r : Req) (g : ℕ → Option Resp' × (X × Y)) (s : ℕ) :
    F.addsVec r g (s + 1) (F.sideVec (F.stAt F.sideSa r g s)) =
      F.sideVec (F.stAt F.sideSa r g (s + 1)) := by
  set u₀ := F.next r (F.stAt F.sideSa r g s) (g s) with hu₀
  have hinv₀ : SideInv u₀ := F.sideInv_next r _ (F.sideInv_stAt _ r g s)
  have hend : F.stAt F.sideSa r g (s + 1) = (F.sideStep F.sideSa r)^[F.qS] u₀ := rfl
  have key : ∀ i ≤ F.qS, (List.range i).foldl (fun v i => F.addVec r g (s + 1) i true v)
      (F.sideVec (F.stAt F.sideSa r g s)) = F.sideVec ((F.sideStep F.sideSa r)^[i] u₀) := by
    intro i
    induction i with
    | zero =>
      intro _
      have ⟨l, hl, hs⟩ := F.next_ans r (F.stAt F.sideSa r g s) (g s)
      funext k
      simp only [List.range_zero, List.foldl_nil, Function.iterate_zero, id, sideVec, hu₀, hl,
        sideVals_append, hs, List.append_nil]
    | succ i ih =>
      intro hi
      rw [List.range_succ, List.foldl_append, ih (by omega)]
      simp only [List.foldl_cons, List.foldl_nil]
      set u := (F.sideStep F.sideSa r)^[i] u₀ with hu
      have hinv : SideInv u := F.sideInv_iterate_sideStep _ r i hinv₀
      have hpre : F.preSt (F.vecSa (F.sideVec u)) r g (s + 1) = u₀ := by
        simp only [preSt]
        obtain ⟨l, hl⟩ := F.iterate_sideStep_ans F.sideSa r i u₀
        obtain ⟨l', hl', -⟩ := F.next_ans r (F.stAt F.sideSa r g s) (g s)
        rw [F.stAt_vecSa r g s]
        refine (F.vecAgrees_sideVec u).of_prefix (F.sideInv_stAt _ r g s)
          ⟨l' ++ l, by rw [hu, hl, hu₀, hl', List.append_assoc]⟩ ?_
        have := F.ns_le_iterate_sideStep F.sideSa r i u₀
        rw [hu₀, F.ns_next] at this
        exact this
      have hpend : F.pendSt (F.vecSa (F.sideVec u)) r g (s + 1) i = u := by
        unfold pendSt
        rw [hpre]
        exact F.iterate_sideStep_vecSa r i hinv₀ (F.vecAgrees_sideVec u)
      rw [Function.iterate_succ_apply']
      unfold addVec
      generalize hP : F.pendSt (F.vecSa (F.sideVec u)) r g (s + 1) i = P
      rw [hpend] at hP
      subst hP
      rcases hp : F.progAct r u with _ | ((x | x) | r')
      · exact (congrArg F.sideVec (F.sideStep_of_not F.sideSa r u fun x h => by
          rw [hp] at h; cases h)).symm
      · exact (congrArg F.sideVec (F.sideStep_of_not F.sideSa r u fun x h => by
          rw [hp] at h; cases h)).symm
      · have hk := F.ns_lt_of_progAct r u hp
        simp only [hk, ↓reduceDIte, ↓reduceIte]
        rw [F.sideVec_sideStep r hinv hp hk]
        congr 1
        have : F.sideVec u ⟨_, hk⟩ = 0 := by
          have h1 : (sideVals u.ans).length = u.ns := hinv
          show (sideVals u.ans).getD u.ns 0 = 0
          exact getD_of_length_le _ _ (by omega)
        rw [this, zero_add]
      · exact (congrArg F.sideVec (F.sideStep_of_not F.sideSa r u fun x h => by
          rw [hp] at h; cases h)).symm
  rw [addsVec_eq, key F.qS le_rfl, hend]

end Adds

/-! ### Resolved states of a relayed request -/

section Res

variable [Inhabited X] [Zero Y] [Zero Ys] [Inhabited Req']

/-- **A state not at a side read.** -/
def Closed (r : Req) (st : RelaySt Y Resp' Ys) : Prop :=
  ∀ x, (F.prog r).after st.ans ≠ .inr (.inl (.inr x))

/-- **A state whose answers are consistent with the side function**, with the side reads made and
those left within the side budget. -/
def ResInv (r : Req) (st : RelaySt Y Resp' Ys) : Prop :=
  Consistent F.side (F.prog r) st.ans ∧ SidesLE (F.qS - st.ns) ((F.prog r).rest st.ans) ∧
    st.ns ≤ F.qS

omit [Inhabited X] [Zero Y] [Zero Ys] [Inhabited Req'] in
theorem progAct_plain {r : Req} {st : RelaySt Y Resp' Ys} {a : (X ⊕ Xs) ⊕ Req'}
    (h : F.progAct r st = some a) :
    st.live = true ∧ (F.prog r).after st.ans = .inr a := by
  unfold progAct at h
  by_cases hl : st.live = true
  · simp only [hl, ↓reduceIte] at h
    refine ⟨hl, ?_⟩
    rcases ha : (F.prog r).after st.ans with o | ((x' | x') | r') <;> simp only [ha] at h
    · simp at h
    · split at h <;> simp_all
    · split at h <;> simp_all
    · split at h <;> simp_all
  · simp [hl] at h

omit [Inhabited X] [Zero Y] [Inhabited Req'] in
theorem resInv_init {r : Req} (h : SidesLE F.qS (F.prog r)) : F.ResInv r .init :=
  ⟨Consistent.nil _ _, by simpa [RelaySt.init, rest_nil] using h, Nat.zero_le _⟩

omit [Inhabited X] [Zero Y] [Inhabited Req'] in
theorem resInv_sideStep {r : Req} {st : RelaySt Y Resp' Ys} (h : F.ResInv r st) :
    F.ResInv r (F.sideStep F.sideSa r st) := by
  unfold sideStep
  rcases hp : F.progAct r st with _ | ((x | x) | r')
  · exact h
  · exact h
  · obtain ⟨-, ha⟩ := F.progAct_plain hp
    obtain ⟨k, hk⟩ := rest_of_after ha
    obtain ⟨hc, hs, hns⟩ := h
    rw [hk] at hs
    obtain ⟨hpos, hs⟩ := hs
    refine ⟨Consistent.append_side hc ha, ?_, by show st.ns + 1 ≤ F.qS; omega⟩
    show SidesLE (F.qS - (st.ns + 1)) ((F.prog r).rest (st.ans ++ [.inl (.inr (F.side x))]))
    rw [rest_append, hk]
    simpa [Nat.sub_add_eq] using hs _
  · exact h

omit [Inhabited X] [Zero Y] [Inhabited Req'] in
theorem resInv_iterate_sideStep {r : Req} :
    ∀ (j : ℕ) {st : RelaySt Y Resp' Ys}, F.ResInv r st →
      F.ResInv r ((F.sideStep F.sideSa r)^[j] st)
  | 0, _, h => h
  | j + 1, _, h => by
    rw [Function.iterate_succ_apply]
    exact resInv_iterate_sideStep j (F.resInv_sideStep h)

omit [Inhabited Req'] in
theorem resInv_next {r : Req} {st : RelaySt Y Resp' Ys} (h : F.ResInv r st)
    (a : Option Resp' × (X × Y)) : F.ResInv r (F.next r st a) := by
  obtain ⟨hc, hs, hns⟩ := h
  unfold next
  rcases hp : F.progAct r st with _ | ((x | x) | r')
  · split_ifs <;> exact ⟨hc, hs, hns⟩
  · obtain ⟨-, ha⟩ := F.progAct_plain hp
    obtain ⟨k, hk⟩ := rest_of_after ha
    refine ⟨Consistent.append_plain hc ha (fun x' e => by cases e) rfl, ?_, hns⟩
    show SidesLE (F.qS - st.ns) ((F.prog r).rest (st.ans ++ [.inl (.inl a.2.2)]))
    rw [rest_append, hk]
    rw [hk] at hs
    exact hs _
  · split_ifs <;> exact ⟨hc, hs, hns⟩
  · obtain ⟨-, ha⟩ := F.progAct_plain hp
    obtain ⟨k, hk⟩ := rest_of_after ha
    refine ⟨Consistent.append_plain hc ha (fun x' e => by cases e) rfl, ?_, hns⟩
    show SidesLE (F.qS - st.ns) ((F.prog r).rest (st.ans ++ [.inr a.1]))
    rw [rest_append, hk]
    rw [hk] at hs
    exact hs _

omit [Inhabited X] [Zero Y] [Inhabited Req'] in
/-- **After the side reads, a live state within the side budget is not at a side read.** -/
theorem closed_close {r : Req} {st : RelaySt Y Resp' Ys} (h : F.ResInv r st)
    (hl : (F.close F.sideSa r st).live = true) : F.Closed r (F.close F.sideSa r st) := by
  intro x hx
  have hinv : F.ResInv r (F.close F.sideSa r st) := F.resInv_iterate_sideStep F.qS h
  have hne := F.progAct_close_ne_side F.sideSa r st x
  obtain ⟨k, hk⟩ := rest_of_after hx
  obtain ⟨-, hs, -⟩ := hinv
  rw [hk] at hs
  obtain ⟨hpos, -⟩ := hs
  apply hne
  simp only [progAct, hl, ↓reduceIte, hx]
  rw [if_pos (by omega)]

end Res

/-! ### Relayed requests with programs whose resolved forms move the main requests -/

section SwapS

variable [Inhabited X] [Zero Y] [Zero Ys] [Inhabited Req']

omit [Inhabited X] [Zero Y] [Zero Ys] [Inhabited Req'] in
/-- A side step keeps the plain answers, the counts but the side reads, and the budget flag. -/
theorem sideStep_plain (sa : ℕ → Xs → Ys) (r : Req) (st : RelaySt Y Resp' Ys) :
    plainList (F.sideStep sa r st).ans = plainList st.ans ∧ (F.sideStep sa r st).na = st.na ∧
      (F.sideStep sa r st).nq = st.nq ∧ (F.sideStep sa r st).np = st.np ∧
      (F.sideStep sa r st).live = st.live := by
  unfold sideStep
  rcases F.progAct r st with _ | ((x | x) | r')
  · exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  · exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  · refine ⟨?_, rfl, rfl, rfl, rfl⟩
    show plainList (st.ans ++ [_]) = _
    rw [plainList_append]
    simp [plainList, plainAns?]
  · exact ⟨rfl, rfl, rfl, rfl, rfl⟩

omit [Inhabited X] [Zero Y] [Zero Ys] [Inhabited Req'] in
theorem close_plain (sa : ℕ → Xs → Ys) (r : Req) :
    ∀ (j : ℕ) (st : RelaySt Y Resp' Ys),
      plainList ((F.sideStep sa r)^[j] st).ans = plainList st.ans ∧
        ((F.sideStep sa r)^[j] st).na = st.na ∧ ((F.sideStep sa r)^[j] st).nq = st.nq ∧
        ((F.sideStep sa r)^[j] st).np = st.np ∧ ((F.sideStep sa r)^[j] st).live = st.live
  | 0, _ => ⟨rfl, rfl, rfl, rfl, rfl⟩
  | j + 1, st => by
    rw [Function.iterate_succ_apply]
    obtain ⟨h1, h2, h3, h4, h5⟩ := close_plain sa r j (F.sideStep sa r st)
    obtain ⟨g1, g2, g3, g4, g5⟩ := F.sideStep_plain sa r st
    exact ⟨h1.trans g1, h2.trans g2, h3.trans g3, h4.trans g4, h5.trans g5⟩

/-- **Two states of a relayed request alike but for their side answers.** -/
def StRel (st st' : RelaySt Y Resp' Ys) : Prop :=
  st.na = st'.na ∧ st.nq = st'.nq ∧ st.np = st'.np ∧ st.live = st'.live ∧
    plainList st.ans = plainList st'.ans

/-- **Actions alike up to the main request moved by `sw` and the side point.** -/
def ActRel (sw : Req' → Req') : Option ((X ⊕ Xs) ⊕ Req') → Option ((X ⊕ Xs) ⊕ Req') → Prop
  | none, none => True
  | some (.inl (.inl x)), some (.inl (.inl x')) => x' = x
  | some (.inl (.inr _)), some (.inl (.inr _)) => True
  | some (.inr r'), some (.inr r'') => r'' = sw r'
  | _, _ => False

variable {F p'} {J : Req → Bool} {P : Req → Prop} {sw : Equiv.Perm Req'} {swO : Equiv.Perm Resp}

omit [Inhabited X] [Zero Y] [Zero Ys] [Inhabited Req'] in
/-- **The state of `p'` at a closed state** is `F`'s with the main request moved by `sw` and the
result by `swO`. -/
theorem after_withProg (h : F.ProgSwap p' J P sw swO) {r : Req} (hr : P r)
    {st st' : RelaySt Y Resp' Ys} (hR : StRel st st') (hi : F.ResInv r st)
    (hi' : (F.withProg p').ResInv r st') (hc : F.Closed r st)
    (hc' : (F.withProg p').Closed r st') :
    (p' r).after st'.ans = Sum.map (Option.map swO) (Sum.map id sw) ((F.prog r).after st.ans) := by
  have e1 := after_eq_ofView F.side hi'.1 hc'
  have e2 := after_eq_ofView F.side hi.1 hc
  change (p' r).after st'.ans = ofView ((resolve F.side (p' r)).after (plainList st'.ans)) at e1
  rw [e1, e2, ← hR.2.2.2.2, h.on r hr, ofView_map]

omit [Inhabited X] [Zero Y] [Zero Ys] [Inhabited Req'] in
theorem actRel_of_after {st st' : RelaySt Y Resp' Ys} {r : Req}
    (hR : StRel st st')
    (ha : (p' r).after st'.ans = Sum.map (Option.map swO) (Sum.map id sw) ((F.prog r).after st.ans))
    (hside : ∀ x, (F.prog r).after st.ans = .inr (.inl (.inr x)) →
      (st.ns < F.qS ↔ st'.ns < F.qS)) :
    ActRel sw (F.progAct r st) ((F.withProg p').progAct r st') := by
  obtain ⟨hna, hnq, hnp, hl, -⟩ := hR
  unfold progAct
  change ActRel sw _ (if st'.live then match (p' r).after st'.ans with
    | .inl _ => none
    | .inr (.inl (.inl x)) => if st'.nq < F.qR then some (.inl (.inl x)) else none
    | .inr (.inl (.inr x)) => if st'.ns < F.qS then some (.inl (.inr x)) else none
    | .inr (.inr r') => if st'.na < F.K then some (.inr r') else none
    else none)
  rw [ha, ← hl, ← hna, ← hnq]
  by_cases hlv : st.live = true
  · simp only [hlv, ↓reduceIte]
    rcases hq : (F.prog r).after st.ans with o | ((x | x) | r') <;>
      simp only [Sum.map_inl, Sum.map_inr, id]
    · trivial
    · split_ifs <;> trivial
    · have := hside x hq
      split_ifs <;> simp_all [ActRel]
    · split_ifs <;> trivial
  · simp only [hlv, Bool.false_eq_true, ↓reduceIte]
    trivial

omit [Zero Y] [Zero Ys] [Inhabited Req'] in
/-- **The states after a sub-slot are alike** when the states and the actions are, the program's
return read alike. -/
theorem next_rel {r : Req} {st st' : RelaySt Y Resp' Ys} (hR : StRel st st')
    (hA : ActRel sw (F.progAct r st) ((F.withProg p').progAct r st'))
    (hL : st.live = true → ((F.prog r).after st.ans).isLeft = ((p' r).after st'.ans).isLeft)
    (a : Option Resp' × (X × Y)) : StRel (F.next r st a) ((F.withProg p').next r st' a) := by
  obtain ⟨hna, hnq, hnp, hl, hpl⟩ := hR
  unfold next
  rcases h1 : F.progAct r st with _ | ((x | x) | r') <;>
    rcases h2 : (F.withProg p').progAct r st' with _ | ((x' | x') | r'') <;>
    simp only [h1, h2, ActRel] at hA <;> simp only
  · change StRel (if st.na < F.K then
        (⟨st.ans, st.na + 1, st.nq, st.ns, st.np, st.live && ((F.prog r).after st.ans).isLeft⟩ :
          RelaySt Y Resp' Ys)
      else ⟨st.ans, st.na, st.nq + 1, st.ns, st.np, st.live && ((F.prog r).after st.ans).isLeft⟩)
      (if st'.na < F.K then
        (⟨st'.ans, st'.na + 1, st'.nq, st'.ns, st'.np,
          st'.live && ((p' r).after st'.ans).isLeft⟩ : RelaySt Y Resp' Ys)
      else ⟨st'.ans, st'.na, st'.nq + 1, st'.ns, st'.np, st'.live && ((p' r).after st'.ans).isLeft⟩)
    have hb : (st.live && ((F.prog r).after st.ans).isLeft) =
        (st'.live && ((p' r).after st'.ans).isLeft) := by
      by_cases hlv : st.live = true
      · rw [hlv, ← hl, hlv, hL hlv]
      · simp only [Bool.not_eq_true] at hlv
        rw [hlv, ← hl, hlv]
        rfl
    split_ifs <;> refine ⟨?_, ?_, ?_, hb, hpl⟩ <;> simp_all
  · subst hA
    refine ⟨hna, by show st.nq + 1 = st'.nq + 1; rw [hnq], hnp, hl, ?_⟩
    show plainList (st.ans ++ [_]) = plainList (st'.ans ++ [_])
    rw [plainList_append, plainList_append, hpl]
  · change StRel (if st.np < F.qP then (⟨st.ans, st.na, st.nq, st.ns, st.np + 1, st.live⟩ :
        RelaySt Y Resp' Ys) else if st.na < F.K then ⟨st.ans, st.na + 1, st.nq, st.ns, st.np, false⟩
        else ⟨st.ans, st.na, st.nq + 1, st.ns, st.np, false⟩)
      (if st'.np < F.qP then (⟨st'.ans, st'.na, st'.nq, st'.ns, st'.np + 1, st'.live⟩ :
        RelaySt Y Resp' Ys) else if st'.na < F.K then ⟨st'.ans, st'.na + 1, st'.nq, st'.ns, st'.np,
        false⟩ else ⟨st'.ans, st'.na, st'.nq + 1, st'.ns, st'.np, false⟩)
    split_ifs <;> refine ⟨?_, ?_, ?_, ?_, hpl⟩ <;> simp_all
  · subst hA
    refine ⟨by show st.na + 1 = st'.na + 1; rw [hna], hnq, hnp, hl, ?_⟩
    show plainList (st.ans ++ [_]) = plainList (st'.ans ++ [_])
    rw [plainList_append, plainList_append, hpl]

omit [Inhabited X] [Zero Y] [Inhabited Req'] in
theorem close_rel {r : Req} {st st' : RelaySt Y Resp' Ys} (hR : StRel st st') :
    StRel (F.close F.sideSa r st) ((F.withProg p').close (F.withProg p').sideSa r st') := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := F.close_plain F.sideSa r F.qS st
  obtain ⟨g1, g2, g3, g4, g5⟩ := (F.withProg p').close_plain (F.withProg p').sideSa r F.qS st'
  obtain ⟨hna, hnq, hnp, hl, hpl⟩ := hR
  exact ⟨h2.trans (hna.trans g2.symm), h3.trans (hnq.trans g3.symm),
    h4.trans (hnp.trans g4.symm), h5.trans (hl.trans g5.symm), h1.trans (hpl.trans g1.symm)⟩

omit [Inhabited Req'] in
/-- **The actions of a relayed request on `P` with the programs `p'` are alike**, and so is its
return, at a state alike but for its side answers (`stAt_withProg`). -/
theorem actRel_at (h : F.ProgSwap p' J P sw swO) {r : Req} (hr : P r)
    (g : ℕ → Option Resp' × (X × Y)) (i : ℕ)
    (hR : StRel (F.stAt F.sideSa r g i) ((F.withProg p').stAt (F.withProg p').sideSa r g i))
    (hi : F.ResInv r (F.stAt F.sideSa r g i))
    (hi' : (F.withProg p').ResInv r ((F.withProg p').stAt (F.withProg p').sideSa r g i))
    (hc : 0 < i → (F.stAt F.sideSa r g i).live = true →
      F.Closed r (F.stAt F.sideSa r g i) ∧
        (F.withProg p').Closed r ((F.withProg p').stAt (F.withProg p').sideSa r g i)) :
    ActRel sw (F.progAct r (F.stAt F.sideSa r g i))
        ((F.withProg p').progAct r ((F.withProg p').stAt (F.withProg p').sideSa r g i)) ∧
      ((F.stAt F.sideSa r g i).live = true →
        ((F.prog r).after (F.stAt F.sideSa r g i).ans).isLeft =
          ((p' r).after ((F.withProg p').stAt (F.withProg p').sideSa r g i).ans).isLeft) := by
  set st := F.stAt F.sideSa r g i with hst
  set st' := (F.withProg p').stAt (F.withProg p').sideSa r g i with hst'
  by_cases hlv : st.live = true
  · by_cases hcl : F.Closed r st ∧ (F.withProg p').Closed r st'
    · have ha := after_withProg h hr hR hi hi' hcl.1 hcl.2
      refine ⟨actRel_of_after hR ha fun x hx => absurd hx (hcl.1 x), fun _ => ?_⟩
      rw [ha]
      rcases (F.prog r).after st.ans <;> rfl
    · -- only before the first sub-slot, at programs beginning with side reads alike
      rcases Nat.eq_zero_or_pos i with hi0 | hi0
      · subst hi0
        have hs := h.starts r hr
        change ¬ ((∀ x, (F.prog r).after [] ≠ .inr (.inl (.inr x))) ∧
          (∀ x, (p' r).after [] ≠ .inr (.inl (.inr x)))) at hcl
        rcases hF : F.prog r with o | ⟨a, k⟩ <;> rcases hP : p' r with o' | ⟨a', k'⟩ <;>
          rw [hF, hP] at hs <;> rw [hF, hP] at hcl
        · (refine absurd ⟨?_, ?_⟩ hcl <;> intro x <;> simp)
        · rcases a' with (x' | x') | r'' <;> simp [OracleProg.startsSide] at hs
          all_goals (refine absurd ⟨?_, ?_⟩ hcl <;> intro x <;> simp)
        · rcases a with (x | x) | r' <;> simp [OracleProg.startsSide] at hs
          all_goals (refine absurd ⟨?_, ?_⟩ hcl <;> intro x <;> simp)
        · rcases a with (x | x) | r' <;> rcases a' with (x' | x') | r'' <;>
            simp [OracleProg.startsSide] at hs
          all_goals try (refine absurd ⟨?_, ?_⟩ hcl <;> intro x <;> simp; done)
          refine ⟨?_, fun _ => ?_⟩
          · unfold progAct
            change ActRel sw (if true = true then match (F.prog r).after [] with
              | .inl _ => none
              | .inr (.inl (.inl x)) => if 0 < F.qR then some (.inl (.inl x)) else none
              | .inr (.inl (.inr x)) => if 0 < F.qS then some (.inl (.inr x)) else none
              | .inr (.inr r') => if 0 < F.K then some (.inr r') else none else none)
              (if true = true then match (p' r).after [] with
              | .inl _ => none
              | .inr (.inl (.inl x)) => if 0 < F.qR then some (.inl (.inl x)) else none
              | .inr (.inl (.inr x)) => if 0 < F.qS then some (.inl (.inr x)) else none
              | .inr (.inr r') => if 0 < F.K then some (.inr r') else none else none)
            rw [hF, hP]
            simp only [↓reduceIte, OracleProg.after_query_nil]
            split_ifs <;> trivial
          · rfl
      · exact absurd (hc hi0 hlv) hcl
  · have hlv' : st.live = false := by simpa using hlv
    have hlv'' : st'.live = false := hR.2.2.2.1 ▸ hlv'
    refine ⟨?_, fun e => absurd e hlv⟩
    simp only [progAct, hlv', hlv'', Bool.false_eq_true, ↓reduceIte]
    trivial

omit [Inhabited Req'] in
/-- **The states of a relayed request on `P` with the programs `p'`**: alike but for their side
answers, each consistent with the side function within the side budget, and not at a side read
after a sub-slot. -/
theorem stAt_withProg (h : F.ProgSwap p' J P sw swO) {r : Req} (hr : P r)
    (g : ℕ → Option Resp' × (X × Y)) : ∀ i,
      StRel (F.stAt F.sideSa r g i) ((F.withProg p').stAt (F.withProg p').sideSa r g i) ∧
      F.ResInv r (F.stAt F.sideSa r g i) ∧
      (F.withProg p').ResInv r ((F.withProg p').stAt (F.withProg p').sideSa r g i) ∧
      (0 < i → (F.stAt F.sideSa r g i).live = true →
        F.Closed r (F.stAt F.sideSa r g i) ∧
          (F.withProg p').Closed r ((F.withProg p').stAt (F.withProg p').sideSa r g i))
  | 0 => ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, F.resInv_init (h.sides r hr),
      (F.withProg p').resInv_init (h.sides' r hr), fun h0 => absurd h0 (lt_irrefl 0)⟩
  | i + 1 => by
    obtain ⟨hR, hi, hi', hc⟩ := stAt_withProg h hr g i
    set st := F.stAt F.sideSa r g i with hst
    set st' := (F.withProg p').stAt (F.withProg p').sideSa r g i with hst'
    have hAL := actRel_at h hr g i hR hi hi' hc
    have hN := next_rel hR hAL.1 hAL.2 (g i)
    have hC := close_rel (F := F) (p' := p') (r := r) hN
    refine ⟨hC, F.resInv_iterate_sideStep F.qS (F.resInv_next hi (g i)),
      (F.withProg p').resInv_iterate_sideStep F.qS ((F.withProg p').resInv_next hi' (g i)),
      fun _ hl => ⟨F.closed_close (F.resInv_next hi (g i)) hl,
        (F.withProg p').closed_close ((F.withProg p').resInv_next hi' (g i)) ?_⟩⟩
    exact hC.2.2.2.1 ▸ hl

/-- **The sub-slot of an action**: an oracle query, a pad sub-slot (a query of `default`) or a main
request. -/
def actSub (n : ℕ) : (X ⊕ Xs) ⊕ Req' → SubAct X Req' n
  | .inl (.inl x) => .query x
  | .inl (.inr _) => .query default
  | .inr r' => .ask r'

omit [Zero Y] [Zero Ys] [Inhabited Req'] in
/-- **The sub-slots of alike states are alike**, the main request moved by `sw`, when `sw` keeps
the padding request. -/
theorem actSub_act_of_rel (n : ℕ) (hidle : sw F.idle = F.idle) {r : Req}
    {st st' : RelaySt Y Resp' Ys} (hR : StRel st st')
    (hA : ActRel sw (F.progAct r st) ((F.withProg p').progAct r st')) :
    actSub n ((F.withProg p').act r st') = (actSub n (F.act r st)).mapAsk sw := by
  obtain ⟨hna, -, hnp, -, -⟩ := hR
  unfold act
  rcases h1 : F.progAct r st with _ | ((x | x) | r') <;>
    rcases h2 : (F.withProg p').progAct r st' with _ | ((x' | x') | r'') <;>
    simp only [h1, h2, ActRel] at hA <;> simp only
  · change actSub n (if st'.na < F.K then .inr F.idle else .inl (.inl default)) =
      (actSub n (if st.na < F.K then .inr F.idle else .inl (.inl default))).mapAsk sw
    rw [← hna]
    split_ifs <;> simp [actSub, SubAct.mapAsk, hidle]
  · subst hA
    rfl
  · change actSub n (if st'.np < F.qP then .inl (.inr x') else if st'.na < F.K then .inr F.idle
        else .inl (.inl default)) = (actSub n (if st.np < F.qP then .inl (.inr x) else
        if st.na < F.K then .inr F.idle else .inl (.inl default))).mapAsk sw
    rw [← hna, ← hnp]
    split_ifs <;> simp [actSub, SubAct.mapAsk, hidle]
  · subst hA
    rfl

omit [Inhabited Req'] in
/-- **The sub-slots of a relayed request on `P` with the programs `p'`** are `F`'s with the main
request moved by `sw`. -/
theorem actSub_withProg (h : F.ProgSwap p' J P sw swO) (hidle : sw F.idle = F.idle) (n : ℕ)
    {r : Req} (hr : P r) (g : ℕ → Option Resp' × (X × Y)) (i : ℕ) :
    actSub n ((F.withProg p').act r ((F.withProg p').stAt (F.withProg p').sideSa r g i)) =
      (actSub n (F.act r (F.stAt F.sideSa r g i))).mapAsk sw := by
  obtain ⟨hR, hi, hi', hc⟩ := stAt_withProg h hr g i
  exact actSub_act_of_rel n hidle hR (actRel_at h hr g i hR hi hi' hc).1

omit [Inhabited Req'] in
/-- **The reply of a relayed request on `P` with the programs `p'`** after at least one sub-slot is
`F`'s moved by `swO`. -/
theorem reply_withProg (h : F.ProgSwap p' J P sw swO) {r : Req} (hr : P r)
    (g : ℕ → Option Resp' × (X × Y)) {i : ℕ} (hi0 : 0 < i) :
    (F.withProg p').reply r ((F.withProg p').stAt (F.withProg p').sideSa r g i) =
      Option.map swO (F.reply r (F.stAt F.sideSa r g i)) := by
  obtain ⟨hR, hi, hi', hc⟩ := stAt_withProg h hr g i
  unfold reply
  rw [← hR.2.2.2.1]
  by_cases hl : (F.stAt F.sideSa r g i).live = true
  · obtain ⟨hcF, hcP⟩ := hc hi0 hl
    have ha := after_withProg h hr hR hi hi' hcF hcP
    simp only [hl, ↓reduceIte]
    change ((p' r).after _).elim id (fun _ => none) = _
    rw [ha]
    rcases (F.prog r).after (F.stAt F.sideSa r g i).ans <;> rfl
  · simp only [hl, Bool.false_eq_true, ↓reduceIte, Option.map_none]

/-! ### The programs off `J` -/

omit [Inhabited X] [Zero Y] [Zero Ys] [Inhabited Req'] in
theorem progAct_of_eq {r : Req} (he : p' r = F.prog r) :
    (F.withProg p').progAct r = F.progAct r := by
  funext st
  unfold progAct
  rw [show (F.withProg p').prog r = F.prog r from he]
  rfl

omit [Inhabited X] [Zero Y] [Zero Ys] [Inhabited Req'] in
theorem sideStep_of_eq {r : Req} (he : p' r = F.prog r) (sa : ℕ → Xs → Ys) :
    (F.withProg p').sideStep sa r = F.sideStep sa r := by
  funext st
  unfold sideStep
  rw [progAct_of_eq he]

omit [Inhabited X] [Zero Y] [Zero Ys] [Inhabited Req'] in
theorem close_of_eq {r : Req} (he : p' r = F.prog r) (sa : ℕ → Xs → Ys) :
    (F.withProg p').close sa r = F.close sa r := by
  funext st
  unfold close
  rw [sideStep_of_eq he]
  rfl

omit [Zero Y] [Zero Ys] [Inhabited Req'] in
theorem next_of_eq {r : Req} (he : p' r = F.prog r) :
    (F.withProg p').next r = F.next r := by
  funext st a
  unfold next
  rw [progAct_of_eq he, show (F.withProg p').prog r = F.prog r from he]
  rfl

omit [Zero Y] [Zero Ys] [Inhabited Req'] in
theorem act_of_eq {r : Req} (he : p' r = F.prog r) :
    (F.withProg p').act r = F.act r := by
  funext st
  unfold act
  rw [progAct_of_eq he]
  rfl

omit [Zero Y] [Zero Ys] [Inhabited Req'] in
theorem stAt_of_eq {r : Req} (he : p' r = F.prog r) (sa : ℕ → Xs → Ys)
    (g : ℕ → Option Resp' × (X × Y)) : ∀ i, (F.withProg p').stAt sa r g i = F.stAt sa r g i
  | 0 => rfl
  | i + 1 => by
    rw [stAt, stAt, stAt_of_eq he sa g i, next_of_eq he, close_of_eq he]

omit [Inhabited X] [Zero Y] [Zero Ys] [Inhabited Req'] in
theorem reply_of_eq {r : Req} (he : p' r = F.prog r) :
    (F.withProg p').reply r = F.reply r := by
  funext st
  unfold reply
  rw [show (F.withProg p').prog r = F.prog r from he]

/-- **The action of a sub-slot with programs equal at the started requests** is `F`'s. -/
theorem actAt_of_eq {n b Q m S : ℕ} {rec : Fin m → Option (Option Req)}
    (hrec : ∀ j r, (recList rec).getD j none = some r → p' r = F.prog r)
    (store : Fin S → Option Resp' × (X × Y)) (side : Fin m → Fin F.qS → Ys) (t : ℕ) :
    (F.withProg p').actAt n b Q rec store side t = F.actAt n b Q rec store side t := by
  unfold actAt
  rw [curBlk_withProg]
  rcases F.curBlk n b Q rec t with _ | ⟨j, sub⟩
  · rfl
  · simp only
    rcases hb : blkAt b Q (recList rec) j with _ | _ | _ <;>
      rcases he : (recList rec).getD j none with _ | r <;> simp only
    all_goals first
      | rfl
      | rw [startAt_withProg, show (F.withProg p').vecSa ((F.withProg p').vecAt side j) =
          F.vecSa (F.vecAt side j) from rfl, stAt_of_eq (hrec j _ he), act_of_eq (hrec j _ he)]

/-- **The reply of the last started slot with programs equal at the started requests** is
`F`'s. -/
theorem lastReply_of_eq {n b Q m S : ℕ} {rec : Fin m → Option (Option Req)}
    (hrec : ∀ j r, (recList rec).getD j none = some r → p' r = F.prog r)
    (store : Fin S → Option Resp' × (X × Y)) (side : Fin m → Fin F.qS → Ys) :
    (F.withProg p').lastReply n b Q rec store side = F.lastReply n b Q rec store side := by
  unfold lastReply
  split_ifs with hl
  · rcases hb : blkAt b Q (recList rec) ((recList rec).length - 1) with _ | _ | _ <;>
      rcases he : (recList rec).getD ((recList rec).length - 1) none with _ | r <;> simp only
    all_goals first
      | rfl
      | (rw [startAt_withProg, show (F.withProg p').vecSa ((F.withProg p').vecAt side _) =
          F.vecSa (F.vecAt side _) from rfl, stAt_of_eq (hrec _ _ he), reply_of_eq (hrec _ _ he)];
         rfl)
  · rfl

/-- **The sub-slot of a relayed request with other programs, read from side stores agreeing with
the side function**: `F`'s with the main request moved by `swAt`. -/
theorem actSub_withProg_at (h : F.ProgSwap p' J P sw swO) (hidle : sw F.idle = F.idle) (n : ℕ)
    {r : Req} (hr : J r = true → P r) (g : ℕ → Option Resp' × (X × Y)) (i : ℕ) :
    actSub n ((F.withProg p').act r ((F.withProg p').stAt (F.withProg p').sideSa r g i)) =
      (actSub n (F.act r (F.stAt F.sideSa r g i))).mapAsk (swAt J sw r) := by
  by_cases hJ : J r = true
  · simp only [swAt, hJ, ↓reduceIte]
    exact actSub_withProg h hidle n (hr hJ) g i
  · have hJ' : J r = false := by simpa using hJ
    simp only [swAt, hJ', Bool.false_eq_true, ↓reduceIte]
    rw [act_of_eq (h.off r hJ'), stAt_of_eq (h.off r hJ'), SubAct.mapAsk_refl]
    rfl

/-- **The action of a sub-slot with other programs whose resolved forms move the main requests**,
read from side stores agreeing at the current block with the side function: `F`'s with its main
request moved by the current slot's permutation, when the current block's request satisfies `P`
if it satisfies `J`. -/
theorem actAt_withProg (h : F.ProgSwap p' J P sw swO) (hidle : sw F.idle = F.idle)
    {n b Q m S : ℕ} {rec : Fin m → Option (Option Req)}
    (store : Fin S → Option Resp' × (X × Y)) (side side' : Fin m → Fin F.qS → Ys) (t : ℕ)
    (hrec : ∀ j sub r, F.curBlk n b Q rec t = some (j, sub) → (recList rec).getD j none = some r →
      J r = true → P r)
    (hside : ∀ j sub r, F.curBlk n b Q rec t = some (j, sub) → blkAt b Q (recList rec) j = .rel →
      (recList rec).getD j none = some r →
      F.stAt (F.vecSa (F.vecAt side j)) r
          (fun k => storeAt store (F.startAt n b Q (recList rec) j + k)) sub =
        F.stAt F.sideSa r (fun k => storeAt store (F.startAt n b Q (recList rec) j + k)) sub ∧
      (F.withProg p').stAt (F.vecSa (F.vecAt side' j)) r
          (fun k => storeAt store (F.startAt n b Q (recList rec) j + k)) sub =
        (F.withProg p').stAt (F.withProg p').sideSa r
          (fun k => storeAt store (F.startAt n b Q (recList rec) j + k)) sub) :
    (F.withProg p').actAt n b Q rec store side' t =
      (F.actAt n b Q rec store side t).mapAsk (curSw F J sw n b Q rec t) := by
  unfold actAt curSw
  rw [curBlk_withProg]
  rcases hcb : F.curBlk n b Q rec t with _ | ⟨j, sub⟩
  · rfl
  · simp only
    rcases hb : blkAt b Q (recList rec) j with _ | _ | _ <;>
      rcases he : (recList rec).getD j none with _ | r <;> simp only
    · split_ifs <;> rfl
    · split_ifs <;> rfl
    · rfl
    · rfl
    · rfl
    · obtain ⟨h1, h2⟩ := hside j sub r hcb hb he
      rw [startAt_withProg]
      change actSub n ((F.withProg p').act r ((F.withProg p').stAt (F.vecSa (F.vecAt side' j)) r
          (fun k => storeAt store (F.startAt n b Q (recList rec) j + k)) sub)) =
        (actSub n (F.act r (F.stAt (F.vecSa (F.vecAt side j)) r
          (fun k => storeAt store (F.startAt n b Q (recList rec) j + k)) sub))).mapAsk _
      rw [h1, h2]
      exact actSub_withProg_at h hidle n (hrec j sub r hcb he) _ sub

/-- **The reply of the last started slot with other programs whose resolved forms move the
results**, read from side stores agreeing at the last block with the side function: `F`'s moved
by the last slot's permutation. -/
theorem lastReply_withProg (h : F.ProgSwap p' J P sw swO) {n b Q m S : ℕ}
    {rec : Fin m → Option (Option Req)}
    (hrec : ∀ j r, (recList rec).getD j none = some r → J r = true → P r)
    (store : Fin S → Option Resp' × (X × Y)) (side side' : Fin m → Fin F.qS → Ys)
    (hside : ∀ r, blkAt b Q (recList rec) ((recList rec).length - 1) = .rel →
      (recList rec).getD ((recList rec).length - 1) none = some r →
      F.stAt (F.vecSa (F.vecAt side ((recList rec).length - 1))) r (fun k => storeAt store
          (F.startAt n b Q (recList rec) ((recList rec).length - 1) + k)) F.len =
        F.stAt F.sideSa r (fun k => storeAt store
          (F.startAt n b Q (recList rec) ((recList rec).length - 1) + k)) F.len ∧
      (F.withProg p').stAt (F.vecSa (F.vecAt side' ((recList rec).length - 1))) r
          (fun k => storeAt store (F.startAt n b Q (recList rec) ((recList rec).length - 1) + k))
          F.len =
        (F.withProg p').stAt (F.withProg p').sideSa r (fun k => storeAt store
          (F.startAt n b Q (recList rec) ((recList rec).length - 1) + k)) F.len) :
    (F.withProg p').lastReply n b Q rec store side' =
      Option.map (Option.map ⇑(lastSwO J swO b Q rec)) (F.lastReply n b Q rec store side) := by
  unfold lastReply lastSwO
  split_ifs with hl
  · rcases hb : blkAt b Q (recList rec) ((recList rec).length - 1) with _ | _ | _ <;>
      rcases he : (recList rec).getD ((recList rec).length - 1) none with _ | r <;> simp only
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · obtain ⟨h1, h2⟩ := hside r hb he
      rw [startAt_withProg]
      change some ((F.withProg p').reply r ((F.withProg p').stAt (F.vecSa (F.vecAt side'
          ((recList rec).length - 1))) r _ F.len)) = some (Option.map _ (F.reply r (F.stAt
          (F.vecSa (F.vecAt side ((recList rec).length - 1))) r _ F.len)))
      rw [h1, h2]
      by_cases hJ : J r = true
      · simp only [swOAt, hJ, ↓reduceIte]
        rw [reply_withProg h (hrec _ r he hJ) _ F.len_pos]
      · have hJ' : J r = false := by simpa using hJ
        simp only [swOAt, hJ', Bool.false_eq_true, ↓reduceIte]
        rw [reply_of_eq (h.off r hJ'), stAt_of_eq (h.off r hJ')]
        simp only [Equiv.coe_refl, Option.map_id, id]
        rfl
  · rfl

end SwapS

end MultiRelay

end Quantum

end GordieHowe
