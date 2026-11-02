-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Pure.MultiRelayRun

@[expose] public section

/-!
# Relay programs without trailing side reads

A relay program makes no trailing side reads when it makes no side read once it has made its `K`
main requests (`OracleProg.NoTrailingSides`). For such programs the relayed request makes no side
read after its last sub-slot (`MultiRelay.progAct_preSt_len_ne_side`), so the side additions at the
step that finalizes a relayed request are the identity (`MultiRelay.addVec_len`).

- `OracleProg.asksAlong`: the main requests a program makes along a list of answers;
  `OracleProg.asksAlong_nil`, `OracleProg.asksAlong_append`.
- `OracleProg.NoTrailingSides`, `MultiRelay.NoTrailingSides`.
- `OracleProg.NoAsks`, `OracleProg.NoSides`, `OracleProg.NoSideAfterAsk` (structural forms):
  `NoSides.after_ne`, `NoSideAfterAsk.noTrailingSides` (no side read after the first main request
  is no trailing side read for `K = 1`), `NoSides.bind`, `NoSides.mapOutput`,
  `NoSideAfterAsk.mapOutput`,
  `NoSides.noSideAfterAsk`, `NoAsks.bind_noSideAfterAsk`, `noAsks_translate`.
- `MultiRelay.progAct_eq_some`: an action of the program is its next query within its budgets.
- `MultiRelay.TrailInv` (the counting invariant of a relayed request), `MultiRelay.trailInv_init`,
  `MultiRelay.trailInv_sideStep`, `MultiRelay.trailInv_iterate_sideStep`,
  `MultiRelay.trailInv_next`, `MultiRelay.trailInv_stAt`.
- `MultiRelay.progAct_preSt_len_ne_side`, `MultiRelay.pendSt_len`, `MultiRelay.addVec_len`.
-/

namespace GordieHowe

namespace OracleProg

variable {α β B R : Type*}

/-- **The main requests a program makes along the answers `ans`**: its queries `inr _` answered
by an entry of `ans`. -/
def asksAlong : OracleProg (α ⊕ β) B R → List B → ℕ
  | pure _, _ => 0
  | query _ _, [] => 0
  | query a k, b :: bs => (if a.isRight then 1 else 0) + (k b).asksAlong bs

@[simp] theorem asksAlong_nil (p : OracleProg (α ⊕ β) B R) : p.asksAlong [] = 0 := by
  cases p <;> rfl

/-- **One more answer**, to the next query `a`, counts `a` if it is a main request. -/
theorem asksAlong_append :
    ∀ (p : OracleProg (α ⊕ β) B R) (ans : List B) (a : α ⊕ β) (b : B), p.after ans = .inr a →
      p.asksAlong (ans ++ [b]) = p.asksAlong ans + (if a.isRight then 1 else 0)
  | pure _, _, _, _, h => by simp at h
  | query a' k, [], a, b, h => by
    simp only [after_query_nil, Sum.inr.injEq] at h
    subst h
    simp [asksAlong]
  | query a' k, c :: cs, a, b, h => by
    simp only [after_query_cons] at h
    simp only [List.cons_append, asksAlong, asksAlong_append (k c) cs a b h]
    omega

/-- **No trailing side reads**: once a program has made `K` main requests, its next query is not
a side read `inl (inr x)`. -/
def NoTrailingSides {X Xs Req' B R : Type*} (K : ℕ) (p : OracleProg ((X ⊕ Xs) ⊕ Req') B R) :
    Prop :=
  ∀ (ans : List B) (x : Xs), K ≤ p.asksAlong ans → p.after ans ≠ .inr (.inl (.inr x))

/-- **A program without main requests**: none of its queries is a main request `inr _`. -/
def NoAsks : OracleProg (α ⊕ β) B R → Prop
  | pure _ => True
  | query a k => a.isRight = false ∧ ∀ b, NoAsks (k b)

/-- **A program without side reads**: none of its queries is a side read `inl (inr x)`. -/
def NoSides {X Xs Req' B R : Type*} : OracleProg ((X ⊕ Xs) ⊕ Req') B R → Prop
  | pure _ => True
  | query a k => (∀ x, a ≠ .inl (.inr x)) ∧ ∀ b, NoSides (k b)

/-- **A program without side reads after its first main request.** -/
def NoSideAfterAsk {X Xs Req' B R : Type*} : OracleProg ((X ⊕ Xs) ⊕ Req') B R → Prop
  | pure _ => True
  | query (.inr _) k => ∀ b, (k b).NoSides
  | query (.inl _) k => ∀ b, NoSideAfterAsk (k b)

section Sides

variable {X Xs Req' S : Type*}

/-- A program without side reads never asks for one. -/
theorem NoSides.after_ne : ∀ {p : OracleProg ((X ⊕ Xs) ⊕ Req') B R}, p.NoSides →
    ∀ (ans : List B) (x : Xs), p.after ans ≠ .inr (.inl (.inr x))
  | pure _, _, _, _ => by simp
  | query a k, h, [], x => by
    simp only [after_query_nil, ne_eq, Sum.inr.injEq]
    exact h.1 x
  | query a k, h, b :: bs, x => by
    rw [after_query_cons]
    exact NoSides.after_ne (h.2 b) bs x

/-- **No side read after the first main request** is no trailing side read for `K = 1`. -/
theorem NoSideAfterAsk.noTrailingSides : ∀ {p : OracleProg ((X ⊕ Xs) ⊕ Req') B R},
    p.NoSideAfterAsk → p.NoTrailingSides 1
  | pure _, _, _, _, _ => by simp
  | query _ _, _, [], _, hK => by simp at hK
  | query (.inr r') k, h, b :: bs, x, _ => by
    rw [after_query_cons]
    exact NoSides.after_ne (h b) bs x
  | query (.inl a) k, h, b :: bs, x, hK => by
    rw [after_query_cons]
    refine NoSideAfterAsk.noTrailingSides (h b) bs x ?_
    simpa [asksAlong] using hK

theorem NoSides.bind : ∀ {p : OracleProg ((X ⊕ Xs) ⊕ Req') B R} {f : R → OracleProg _ B S},
    p.NoSides → (∀ r, (f r).NoSides) → (p.bind f).NoSides
  | pure r, _, _, hf => hf r
  | query _ _, _, h, hf => ⟨h.1, fun b => NoSides.bind (h.2 b) hf⟩

theorem NoSides.mapOutput {p : OracleProg ((X ⊕ Xs) ⊕ Req') B R} (h : p.NoSides) (f : R → S) :
    (p.mapOutput f).NoSides :=
  h.bind fun _ => trivial

theorem NoSideAfterAsk.mapOutput : ∀ {p : OracleProg ((X ⊕ Xs) ⊕ Req') B R},
    p.NoSideAfterAsk → ∀ f : R → S, (p.mapOutput f).NoSideAfterAsk
  | pure _, _, _ => trivial
  | query (.inr _) _, h, f => fun b => (h b).mapOutput f
  | query (.inl _) _, h, f => fun b => NoSideAfterAsk.mapOutput (h b) f

/-- A program without side reads has none after its first main request. -/
theorem NoSides.noSideAfterAsk : ∀ {p : OracleProg ((X ⊕ Xs) ⊕ Req') B R}, p.NoSides →
    p.NoSideAfterAsk
  | pure _, _ => trivial
  | query (.inr _) _, h => h.2
  | query (.inl (.inl _)) _, h => fun b => NoSides.noSideAfterAsk (h.2 b)
  | query (.inl (.inr x)) _, h => absurd rfl (h.1 x)

/-- **A program without main requests followed by programs without side reads after their first
main request** has none after its first main request. -/
theorem NoAsks.bind_noSideAfterAsk : ∀ {p : OracleProg ((X ⊕ Xs) ⊕ Req') B R}
    {f : R → OracleProg _ B S}, p.NoAsks → (∀ r, (f r).NoSideAfterAsk) →
      (p.bind f).NoSideAfterAsk
  | pure r, _, _, hf => hf r
  | query (.inr _) _, _, h, _ => absurd h.1 (by simp)
  | query (.inl _) _, _, h, hf => fun b => NoAsks.bind_noSideAfterAsk (h.2 b) hf

/-- **A translated program whose queries are no main requests has none.** -/
theorem noAsks_translate {A' B' : Type*} (ι : A' → α ⊕ β) (g : A' → B → B')
    (hι : ∀ a, (ι a).isRight = false) : ∀ p : OracleProg A' B' R, (p.translate ι g).NoAsks
  | pure _ => trivial
  | query a k => ⟨hι a, fun b => noAsks_translate ι g hι (k (g a b))⟩

end Sides

end OracleProg

namespace Quantum

namespace MultiRelay

variable {X Y Req Resp Req' Resp' Xs Ys : Type} (F : MultiRelay X Y Req Resp Req' Resp' Xs Ys)

/-- **A relay without trailing side reads**: every program makes no side read once it has made
its `K` main requests. -/
def NoTrailingSides : Prop :=
  ∀ r, (F.prog r).NoTrailingSides F.K

/-- **An action of the program is its next query**, on a state within its budgets. -/
theorem progAct_eq_some (r : Req) (st : RelaySt Y Resp' Ys) {a : (X ⊕ Xs) ⊕ Req'}
    (h : F.progAct r st = some a) : st.live = true ∧ (F.prog r).after st.ans = .inr a := by
  unfold progAct at h
  by_cases hl : st.live
  · refine ⟨hl, ?_⟩
    rcases hq : (F.prog r).after st.ans with _ | ((x | x) | r') <;>
      simp only [hl, hq, ↓reduceIte] at h
    · simp at h
    · split_ifs at h
      · cases h
        rfl
    · split_ifs at h
      · cases h
        rfl
    · split_ifs at h
      · cases h
        rfl
  · simp [hl] at h

/-- **The counting invariant of a relayed request**: at most `K` main requests and `qP` pad
sub-slots; at most `qR` queries while fewer than `K` main requests were made; and, within the
budgets, the program has returned or its main requests are those counted. -/
def TrailInv (r : Req) (st : RelaySt Y Resp' Ys) : Prop :=
  st.na ≤ F.K ∧ st.np ≤ F.qP ∧ (st.na < F.K → st.nq ≤ F.qR) ∧
    (st.live = true → ((F.prog r).after st.ans).isLeft = true ∨
      st.na = (F.prog r).asksAlong st.ans)

theorem trailInv_init (r : Req) : F.TrailInv r (RelaySt.init (Y := Y) (Resp' := Resp')
    (Ys := Ys)) := by
  refine ⟨Nat.zero_le _, Nat.zero_le _, fun _ => Nat.zero_le _, fun _ => Or.inr ?_⟩
  simp [RelaySt.init]

theorem trailInv_sideStep (sa : ℕ → Xs → Ys) (r : Req) {st : RelaySt Y Resp' Ys}
    (h : F.TrailInv r st) : F.TrailInv r (F.sideStep sa r st) := by
  unfold sideStep
  rcases hp : F.progAct r st with _ | ((x | x) | r')
  · exact h
  · exact h
  · obtain ⟨hl, ha⟩ := F.progAct_eq_some r st hp
    obtain ⟨h1, h2, h3, h4⟩ := h
    refine ⟨h1, h2, h3, fun _ => Or.inr ?_⟩
    rcases h4 hl with h5 | h5
    · rw [ha] at h5
      simp at h5
    · simp only
      rw [OracleProg.asksAlong_append _ _ _ _ ha, h5]
      simp
  · exact h

theorem trailInv_iterate_sideStep (sa : ℕ → Xs → Ys) (r : Req) :
    ∀ (j : ℕ) {st : RelaySt Y Resp' Ys}, F.TrailInv r st →
      F.TrailInv r ((F.sideStep sa r)^[j] st)
  | 0, _, h => h
  | j + 1, _, h => by
    rw [Function.iterate_succ_apply]
    exact trailInv_iterate_sideStep sa r j (F.trailInv_sideStep sa r h)

theorem trailInv_next (r : Req) {st : RelaySt Y Resp' Ys} (a : Option Resp' × (X × Y))
    (h : F.TrailInv r st) : F.TrailInv r (F.next r st a) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  unfold next
  rcases hp : F.progAct r st with _ | ((x | x) | r')
  · simp only
    split_ifs with hK
    · refine ⟨?_, ?_, ?_, ?_⟩ <;> dsimp only
      · omega
      · exact h2
      · intro hK'
        exact h3 (by omega)
      · intro hl
        simp only [Bool.and_eq_true] at hl
        exact Or.inl hl.2
    · refine ⟨?_, ?_, ?_, ?_⟩ <;> dsimp only
      · exact h1
      · exact h2
      · intro hK'
        exact absurd hK' hK
      · intro hl
        simp only [Bool.and_eq_true] at hl
        exact Or.inl hl.2
  · obtain ⟨hl, ha⟩ := F.progAct_eq_some r st hp
    have hq := F.nq_lt_of_progAct r st hp
    refine ⟨?_, ?_, ?_, ?_⟩ <;> dsimp only
    · exact h1
    · exact h2
    · intro _
      omega
    · intro _
      right
      rcases h4 hl with h5 | h5
      · rw [ha] at h5
        simp at h5
      · rw [OracleProg.asksAlong_append _ _ _ _ ha, h5]
        simp
  · simp only
    split_ifs with hP hK
    · refine ⟨?_, ?_, ?_, ?_⟩ <;> dsimp only
      · exact h1
      · omega
      · exact h3
      · exact h4
    · refine ⟨?_, ?_, ?_, ?_⟩ <;> dsimp only
      · omega
      · exact h2
      · intro hK'
        exact h3 (by omega)
      · intro hl
        simp at hl
    · refine ⟨?_, ?_, ?_, ?_⟩ <;> dsimp only
      · exact h1
      · exact h2
      · intro hK'
        exact absurd hK' hK
      · intro hl
        simp at hl
  · obtain ⟨hl, ha⟩ := F.progAct_eq_some r st hp
    have hK := F.na_lt_of_progAct r st hp
    refine ⟨?_, ?_, ?_, ?_⟩ <;> dsimp only
    · omega
    · exact h2
    · intro hK'
      exact h3 (by omega)
    · intro _
      right
      rcases h4 hl with h5 | h5
      · rw [ha] at h5
        simp at h5
      · rw [OracleProg.asksAlong_append _ _ _ _ ha, h5]
        simp

theorem trailInv_stAt (sa : ℕ → Xs → Ys) (r : Req) (g : ℕ → Option Resp' × (X × Y)) :
    ∀ i, F.TrailInv r (F.stAt sa r g i)
  | 0 => F.trailInv_init r
  | i + 1 => F.trailInv_iterate_sideStep sa r F.qS (F.trailInv_next r _ (trailInv_stAt sa r g i))

/-- **No side read after the last sub-slot**: without trailing side reads, after the `len`
sub-slots of a relayed request the program's action is not a side read. -/
theorem progAct_preSt_len_ne_side (hT : F.NoTrailingSides) (sa : ℕ → Xs → Ys) (r : Req)
    (g : ℕ → Option Resp' × (X × Y)) (x : Xs) :
    F.progAct r (F.preSt sa r g F.len) ≠ some (.inl (.inr x)) := by
  intro hp
  obtain ⟨i, hi⟩ : ∃ i, F.len = i + 1 := ⟨F.len - 1, by have := F.len_pos; omega⟩
  rw [hi] at hp
  have hinv := F.trailInv_next r (g i) (F.trailInv_stAt sa r g i)
  have hc : (F.next r (F.stAt sa r g i) (g i)).na + (F.next r (F.stAt sa r g i) (g i)).nq +
      (F.next r (F.stAt sa r g i) (g i)).np = F.len := by
    rw [F.counts_next, F.counts_stAt, hi]
  change F.progAct r (F.next r (F.stAt sa r g i) (g i)) = _ at hp
  obtain ⟨hl, ha⟩ := F.progAct_eq_some r _ hp
  obtain ⟨h1, h2, h3, h4⟩ := hinv
  have hK : (F.next r (F.stAt sa r g i) (g i)).na = F.K := by
    by_contra hne
    have := h3 (by omega)
    unfold len at hc
    omega
  rcases h4 hl with h5 | h5
  · rw [ha] at h5
    simp at h5
  · exact hT r _ x (by rw [← h5, hK]) ha

/-- **The side reads after the last sub-slot** are none: the state is the one before them. -/
theorem pendSt_len (hT : F.NoTrailingSides) (sa : ℕ → Xs → Ys) (r : Req)
    (g : ℕ → Option Resp' × (X × Y)) (i : ℕ) :
    F.pendSt sa r g F.len i = F.preSt sa r g F.len :=
  Function.iterate_fixed
    (F.sideStep_of_not sa r _ fun x => F.progAct_preSt_len_ne_side hT sa r g x) i

variable [AddGroup Ys]

/-- **The side additions after the last sub-slot are the identity** without trailing side
reads. -/
theorem addVec_len (hT : F.NoTrailingSides) (r : Req) (g : ℕ → Option Resp' × (X × Y)) (i : ℕ)
    (sgn : Bool) (v : Fin F.qS → Ys) : F.addVec r g F.len i sgn v = v := by
  unfold addVec
  rw [F.pendSt_len hT]
  rcases hp : F.progAct r (F.preSt (F.vecSa v) r g F.len) with _ | ((x | x) | r')
  · rfl
  · rfl
  · exact absurd hp (F.progAct_preSt_len_ne_side hT _ r g x)
  · rfl

end MultiRelay

end Quantum

end GordieHowe
