-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Pure.MultiRelayRun
public import GordieHowe.Model.Quantum.Pure.MultiRelaySim

@[expose] public section

/-!
# The origin of the relay's main requests

Every main request in the logs of the final placement (`Distinguisher.place`) of a basis state `g`
of `D`'s game in the game of the relayed distinguisher (`Distinguisher.relay`) is the idle request
of the relay or a request that the program of one of the first `Q` requests in `g`'s logs can make.

- `OracleProg.AnsFit`, `OracleProg.exists_after_elimSide`: answers fitting a relay program, its
  side reads answered by the side function.
- `MultiRelay.CanAsk F r r'`: the program of `r`, its side reads answered by the side function,
  makes the main request `r'` after some answers; `MultiRelay.canAsk_of_asksIn_elimSide`,
  `MultiRelay.canAsk_of_asksIn`: such a request satisfies every `P` the program's main requests
  satisfy (`MultiRelay.AsksIn`). `MultiRelay.ansFit_runAux`, `MultiRelay.ansFit_stAt`: the relay's
  answers fit its program.
- `MultiRelay.origin_runEntries`, `MultiRelay.origin_sched`, `MultiRelay.origin_subEntriesL`: the
  main requests of a relayed request, of a schedule and of its padded prefix.
- `Distinguisher.origin_place`: the main requests in the logs of the final placement
  (`Distinguisher.place`) of a basis state `g`: each is the idle request or one that the program
  of one of the first `Q` requests in `g`'s logs can make.
- `MultiRelay.length_filterMap_runEntries`: a relayed request makes exactly `K` main requests;
  `MultiRelay.length_mainReqs`: relaying at most `Q` requests `rs` makes `K · |rs|` main requests.
-/

namespace GordieHowe.Quantum

namespace MultiRelay

variable {X Y Req Resp Req' Resp' Xs Ys : Type} (F : MultiRelay X Y Req Resp Req' Resp' Xs Ys)

end MultiRelay

end GordieHowe.Quantum

namespace GordieHowe.OracleProg

variable {X Xs Y Ys Req' Resp' R : Type}

/-- **Answers that fit a relay program** with its side reads answered by `s`: each answer to an
oracle read is an oracle answer, to a side read at `x` the side answer `s x`, to a main request a
main reply. -/
def AnsFit (s : Xs → Ys) :
    OracleProg ((X ⊕ Xs) ⊕ Req') ((Y ⊕ Ys) ⊕ Option Resp') R → List ((Y ⊕ Ys) ⊕ Option Resp') →
      Prop
  | _, [] => True
  | .pure _, _ :: _ => True
  | .query (.inl (.inl _)) k, b :: bs => (∃ y, b = .inl (.inl y)) ∧ AnsFit s (k b) bs
  | .query (.inl (.inr x)) k, b :: bs => b = .inl (.inr (s x)) ∧ AnsFit s (k b) bs
  | .query (.inr _) k, b :: bs => (∃ c, b = .inr c) ∧ AnsFit s (k b) bs

/-- **An answer fitting the next query**: an oracle answer to an oracle read, the side answer to a
side read, a main reply to a main request. -/
def FitsQuery (s : Xs → Ys) : (X ⊕ Xs) ⊕ Req' → (Y ⊕ Ys) ⊕ Option Resp' → Prop
  | .inl (.inl _), b => ∃ y, b = .inl (.inl y)
  | .inl (.inr x), b => b = .inl (.inr (s x))
  | .inr _, b => ∃ c, b = .inr c

/-- No answers fit every program. -/
theorem AnsFit.nil (s : Xs → Ys) (p : OracleProg ((X ⊕ Xs) ⊕ Req') ((Y ⊕ Ys) ⊕ Option Resp') R) :
    AnsFit s p [] := by
  cases p <;> trivial

/-- **Fitting answers extended by an answer fitting the next query fit.** -/
theorem AnsFit.append (s : Xs → Ys) {b : (Y ⊕ Ys) ⊕ Option Resp'} :
    ∀ (p : OracleProg ((X ⊕ Xs) ⊕ Req') ((Y ⊕ Ys) ⊕ Option Resp') R) (ans), AnsFit s p ans →
      (∀ a, p.after ans = .inr a → FitsQuery s a b) → AnsFit s p (ans ++ [b])
  | .pure _, [], _, _ => trivial
  | .pure _, _ :: _, _, _ => trivial
  | .query a k, [], _, hb => by
    have := hb a rfl
    rcases a with (x | x) | r' <;> exact ⟨this, AnsFit.nil s _⟩
  | .query (.inl (.inl _)) k, c :: cs, h, hb => ⟨h.1, AnsFit.append s (k c) cs h.2 hb⟩
  | .query (.inl (.inr _)) k, c :: cs, h, hb => ⟨h.1, AnsFit.append s (k c) cs h.2 hb⟩
  | .query (.inr _) k, c :: cs, h, hb => ⟨h.1, AnsFit.append s (k c) cs h.2 hb⟩

/-- **A main request after fitting answers is one after some answers with the side reads answered
classically.** -/
theorem exists_after_elimSide (s : Xs → Ys) {r' : Req'} :
    ∀ (p : OracleProg ((X ⊕ Xs) ⊕ Req') ((Y ⊕ Ys) ⊕ Option Resp') R) (ans), AnsFit s p ans →
      p.after ans = .inr (.inr r') → ∃ ans', (elimSide s p).after ans' = .inr (.inr r')
  | .pure _, _, _, h => by simp at h
  | .query (.inl (.inl _)) k, [], _, h => by simp at h
  | .query (.inl (.inr _)) k, [], _, h => by simp at h
  | .query (.inr _) k, [], _, h => ⟨[], by simpa [elimSide] using h⟩
  | .query (.inl (.inl x)) k, b :: bs, hf, h => by
    obtain ⟨⟨y, rfl⟩, hf⟩ := hf
    obtain ⟨ans', h'⟩ := exists_after_elimSide s (k _) bs hf h
    exact ⟨.inl y :: ans', h'⟩
  | .query (.inl (.inr x)) k, b :: bs, hf, h => by
    obtain ⟨rfl, hf⟩ := hf
    exact exists_after_elimSide s (k _) bs hf h
  | .query (.inr _) k, b :: bs, hf, h => by
    obtain ⟨⟨c, rfl⟩, hf⟩ := hf
    obtain ⟨ans', h'⟩ := exists_after_elimSide s (k _) bs hf h
    exact ⟨.inr c :: ans', h'⟩

/-- **A main request of the program with its side reads answered classically is one of the
program**, after the answers lifted and the side answers inserted. -/
theorem exists_after_of_elimSide (s : Xs → Ys) {r' : Req'} :
    ∀ (p : OracleProg ((X ⊕ Xs) ⊕ Req') ((Y ⊕ Ys) ⊕ Option Resp') R) (ans),
      (elimSide s p).after ans = .inr (.inr r') → ∃ ans', p.after ans' = .inr (.inr r')
  | .pure _, _, h => by simp [elimSide] at h
  | .query (.inl (.inl _)) k, [], h => by simp [elimSide] at h
  | .query (.inl (.inr x)) k, ans, h => by
    obtain ⟨ans', h'⟩ := exists_after_of_elimSide s (k _) ans h
    exact ⟨_ :: ans', h'⟩
  | .query (.inr _) k, [], h => ⟨[], by simpa [elimSide] using h⟩
  | .query (.inl (.inl x)) k, b :: bs, h => by
    obtain ⟨ans', h'⟩ := exists_after_of_elimSide s (k _) bs h
    exact ⟨_ :: ans', h'⟩
  | .query (.inr _) k, b :: bs, h => by
    obtain ⟨ans', h'⟩ := exists_after_of_elimSide s (k _) bs h
    exact ⟨_ :: ans', h'⟩

end GordieHowe.OracleProg

namespace GordieHowe.Quantum

namespace MultiRelay

variable {X Y Req Resp Req' Resp' Xs Ys : Type} (F : MultiRelay X Y Req Resp Req' Resp' Xs Ys)

/-- **The program of `r` can make the main request `r'`**: after some answers, its side reads
answered by the side function, it asks for `r'`. -/
def CanAsk (r : Req) (r' : Req') : Prop :=
  ∃ ans, (OracleProg.elimSide F.side (F.prog r)).after ans = .inr (.inr r')

/-- **A request the program can make is one after some answers**, its side reads answered
anyhow. -/
theorem CanAsk.exists_after {r : Req} {r' : Req'} (h : F.CanAsk r r') :
    ∃ ans, (F.prog r).after ans = .inr (.inr r') :=
  let ⟨ans, h⟩ := h
  OracleProg.exists_after_of_elimSide F.side _ ans h

/-- **A main request the program of `r` can make satisfies `P`** when every main request of the
program, its side reads answered by the side function, satisfies `P` (`AsksIn`). -/
theorem canAsk_of_asksIn_elimSide {r : Req} {P : Req' → Prop}
    (h : AsksIn Resp' (OracleProg.elimSide F.side (F.prog r)) P) {r' : Req'}
    (hr : F.CanAsk r r') : P r' :=
  let ⟨ans, hans⟩ := hr
  h ans r' hans

/-- **A main request the program of `r` can make satisfies `P`** when every main request of the
program satisfies `P` (`AsksIn`). -/
theorem canAsk_of_asksIn {r : Req} {P : Req' → Prop} (h : AsksIn Resp' (F.prog r) P) {r' : Req'}
    (hr : F.CanAsk r r') : P r' :=
  let ⟨ans, hans⟩ := CanAsk.exists_after F hr
  h ans r' hans

/-- **A main request the relay's step asks for is one the program of `r` can make**, when the
answers fed so far fit the program (`AnsFit`). -/
theorem canAsk_of_progAct {r : Req} {st : RelaySt Y Resp' Ys} {r' : Req'}
    (hfit : OracleProg.AnsFit F.side (F.prog r) st.ans)
    (h : F.progAct r st = some (.inr r')) : F.CanAsk r r' := by
  unfold progAct at h
  by_cases hl : st.live
  · rw [if_pos hl] at h
    rcases hq : (F.prog r).after st.ans with _ | ((x | x) | r'')
    · rw [hq] at h
      simp at h
    · rw [hq] at h
      simp only at h
      split_ifs at h <;> simp at h
    · rw [hq] at h
      simp only at h
      split_ifs at h <;> simp at h
    · rw [hq] at h
      simp only at h
      split_ifs at h with h2
      · cases h
        exact OracleProg.exists_after_elimSide F.side _ _ hfit hq
  · rw [if_neg hl] at h
    simp at h

/-- **The relay's step queries what the program asks next.** -/
theorem after_of_progAct {r : Req} {st : RelaySt Y Resp' Ys} {q : (X ⊕ Xs) ⊕ Req'}
    (h : F.progAct r st = some q) : (F.prog r).after st.ans = .inr q := by
  unfold progAct at h
  by_cases hl : st.live
  · rw [if_pos hl] at h
    rcases hq : (F.prog r).after st.ans with _ | ((x | x) | r'') <;> rw [hq] at h
    · simp at h
    all_goals
      simp only at h
      split_ifs at h
      · cases h
        rfl
  · rw [if_neg hl] at h
    simp at h

/-- **One side read keeps the answers fitting the program**, the side reads answered by the side
function. -/
theorem ansFit_sideStep (r : Req) {st : RelaySt Y Resp' Ys}
    (hf : OracleProg.AnsFit F.side (F.prog r) st.ans) :
    OracleProg.AnsFit F.side (F.prog r) (F.sideStep (fun _ x => F.side x) r st).ans := by
  unfold sideStep
  rcases hp : F.progAct r st with _ | ((x | x) | r')
  · exact hf
  · exact hf
  · refine OracleProg.AnsFit.append _ _ _ hf fun a ha => ?_
    rw [F.after_of_progAct hp] at ha
    cases ha
    rfl
  · exact hf

/-- **A sub-slot keeps the answers fitting the program.** -/
theorem ansFit_next (r : Req) {st : RelaySt Y Resp' Ys} (a : Option Resp' × (X × Y))
    (hf : OracleProg.AnsFit F.side (F.prog r) st.ans) :
    OracleProg.AnsFit F.side (F.prog r) (F.next r st a).ans := by
  unfold next
  rcases hp : F.progAct r st with _ | ((x | x) | r')
  · split_ifs <;> exact hf
  · refine OracleProg.AnsFit.append _ _ _ hf fun a' ha => ?_
    rw [F.after_of_progAct hp] at ha
    cases ha
    exact ⟨_, rfl⟩
  · split_ifs <;> exact hf
  · refine OracleProg.AnsFit.append _ _ _ hf fun a' ha => ?_
    rw [F.after_of_progAct hp] at ha
    cases ha
    exact ⟨_, rfl⟩

variable [Inhabited X] [Zero Y] [Zero Ys] [Inhabited Req']

/-- **The side reads keep the answers fitting the program.** -/
theorem ansFit_iterate (r : Req) :
    ∀ (N : ℕ) (st : RelaySt Y Resp' Ys), OracleProg.AnsFit F.side (F.prog r) st.ans →
      OracleProg.AnsFit F.side (F.prog r) ((F.sideStep F.sideSa r)^[N] st).ans
  | 0, _, h => h
  | N + 1, st, h => by
    rw [Function.iterate_succ_apply]
    exact ansFit_iterate r N _ (F.ansFit_sideStep r h)

/-- **The answers after the stored answers fit the program**, the side reads answered by the side
function. -/
theorem ansFit_stAt (r : Req) (g : ℕ → Option Resp' × (X × Y)) :
    ∀ u, OracleProg.AnsFit F.side (F.prog r) (F.stAt F.sideSa r g u).ans
  | 0 => OracleProg.AnsFit.nil _ _
  | u + 1 => F.ansFit_iterate r _ _ (F.ansFit_next r _ (ansFit_stAt r g u))

/-- **The answers of a relayed request fit its program**, its side reads answered by the side
function. -/
theorem ansFit_runAux (ansM : List Req' → Req' → Option Resp') (H : X → Y) (r : Req)
    (rs : List Req') : ∀ i, OracleProg.AnsFit F.side (F.prog r) (F.runAux ansM H r rs i).1.ans
  | 0 => OracleProg.AnsFit.nil _ _
  | i + 1 => by
    simp only [runAux, close]
    exact F.ansFit_iterate r _ _ (F.ansFit_next r _ (ansFit_runAux ansM H r rs i))


/-- **The main requests of a relayed request** are the idle request or requests its program can
make. -/
theorem origin_runEntries (ansM : List Req' → Req' → Option Resp') (H : X → Y) (r : Req)
    (rs : List Req') {r' : Req'} (hr : r' ∈ (F.runEntries ansM H r rs).filterMap Prod.fst) :
    r' = F.idle ∨ F.CanAsk r r' := by
  have key : ∀ i, ∀ r' ∈ (F.runAux ansM H r rs i).2.filterMap Prod.fst,
      r' = F.idle ∨ F.CanAsk r r' := by
    intro i
    induction i with
    | zero => simp [runAux]
    | succ i ih =>
      intro r' hr'
      simp only [runAux, List.filterMap_append, List.mem_append] at hr'
      rcases hr' with hr' | hr'
      · exact ih r' hr'
      · rcases ha : F.act r (F.runAux ansM H r rs i).1 with (x | x) | r''
        · simp [ha] at hr'
        · simp [ha] at hr'
        · simp only [ha, List.filterMap_cons, List.filterMap_nil, List.mem_singleton] at hr'
          subst hr'
          unfold act at ha
          rcases hp : F.progAct r (F.runAux ansM H r rs i).1 with _ | ((x | x) | r''')
          · rw [hp] at ha
            simp only at ha
            split_ifs at ha
            · cases ha
              exact Or.inl rfl
          · rw [hp] at ha
            simp at ha
          · rw [hp] at ha
            simp only at ha
            split_ifs at ha
            · cases ha
              exact Or.inl rfl
          · rw [hp] at ha
            simp only [Sum.inr.injEq] at ha
            subst ha
            exact Or.inr (F.canAsk_of_progAct (F.ansFit_runAux ansM H r rs i) hp)
  exact key _ r' hr

variable (n b Q : ℕ) (ansM : List Req' → Req' → Option Resp') (H : X → Y)

/-- **The main requests of a schedule** are the idle request or requests the program of one of the
first `Q` requests of the entries can make. -/
theorem origin_sched (es : List (Option Req)) {r' : Req'}
    (hr : r' ∈ (F.sched n b Q ansM H es).out.filterMap Prod.fst) :
    r' = F.idle ∨ ∃ r ∈ (es.filterMap id).take Q, F.CanAsk r r' := by
  induction es using List.reverseRecOn generalizing r' with
  | nil => simp [sched] at hr
  | append_singleton es e ih =>
    have hpre : ∀ r, r ∈ (es.filterMap id).take Q → r ∈ ((es ++ [e]).filterMap id).take Q :=
      fun r h => by
        rw [List.filterMap_append, List.take_append]
        exact List.mem_append_left _ h
    rw [F.sched_append, F.schedStep_out, List.filterMap_append, List.mem_append] at hr
    rcases hr with hr | hr
    · rcases ih hr with h | ⟨r, hr, hc⟩
      · exact Or.inl h
      · exact Or.inr ⟨r, hpre r hr, hc⟩
    · rcases e with _ | r
      · simp only [blockOf] at hr
        split_ifs at hr
        · simp at hr
        · simp [idleEntry] at hr
          exact Or.inl hr
      · simp only [blockOf] at hr
        split_ifs at hr with hq
        · rcases F.origin_runEntries ansM H r _ hr with h | h
          · exact Or.inl h
          · refine Or.inr ⟨r, ?_, h⟩
            have hlen : (es.filterMap id).length < Q := by
              rw [length_filterMap_id]
              rw [(F.sched_qb_rb n b Q ansM H es).2] at hq
              exact hq
            rw [List.filterMap_append, List.take_append]
            refine List.mem_append_right _ ?_
            rw [List.take_of_length_le (by
              change 1 ≤ Q - (List.filterMap id es).length
              omega)]
            exact List.mem_singleton_self r
        · simp [idleEntry] at hr
          exact Or.inl hr

/-- The trailing sub-slots add only idle requests. -/
theorem origin_tailEntries (out : List (Option Req' × (Option Resp' × (X × Y)))) :
    ∀ k, ∀ {r' : Req'}, r' ∈ (F.tailEntries ansM out k).filterMap Prod.fst →
      r' ∈ out.filterMap Prod.fst ∨ r' = F.idle
  | 0, _, hr => Or.inl hr
  | k + 1, r', hr => by
    rw [tailEntries, List.filterMap_append, List.mem_append] at hr
    rcases hr with hr | hr
    · exact origin_tailEntries out k hr
    · simp [idleEntry] at hr
      exact Or.inr hr

/-- **The main requests of the sub-slots before sub-slot `s`** are the idle request or requests
the program of one of the first `Q` requests of the entries can make. -/
theorem origin_subEntriesL (s : ℕ) (es : List (Option Req)) {r' : Req'}
    (hr : r' ∈ (F.subEntriesL n b Q ansM H s es).filterMap Prod.fst) :
    r' = F.idle ∨ ∃ r ∈ (es.filterMap id).take Q, F.CanAsk r r' := by
  have hr' := ((List.take_sublist _ _).filterMap Prod.fst).subset hr
  rcases F.origin_tailEntries ansM _ s hr' with h | h
  · exact F.origin_sched n b Q ansM H es h
  · exact Or.inl h

/-- The main requests made after `i` sub-slots are at most `K`. -/
theorem na_runAux_le (r : Req) (rs : List Req') : ∀ i, (F.runAux ansM H r rs i).1.na ≤ F.K
  | 0 => Nat.zero_le _
  | i + 1 => by
    simp only [runAux]
    rw [F.na_close]
    exact F.na_next_le r _ _ (na_runAux_le r rs i)

/-- After `i` sub-slots, `i` main requests, queries and pad sub-slots were made. -/
theorem counts_runAux (r : Req) (rs : List Req') (i : ℕ) :
    (F.runAux ansM H r rs i).1.na + (F.runAux ansM H r rs i).1.nq +
      (F.runAux ansM H r rs i).1.np = i := by
  rw [← F.stAt_runAux ansM H r rs (le_refl i)]
  exact F.counts_stAt _ r _ i

/-- **A relayed request makes exactly `K` main requests.** -/
theorem length_filterMap_runEntries (r : Req) (rs : List Req') :
    ((F.runEntries ansM H r rs).filterMap Prod.fst).length = F.K := by
  have h1 := F.na_runAux_le ansM H r rs F.len
  have h2 := F.nq_runAux_le ansM H r rs (le_refl F.len)
  have h3 := F.counts_runAux ansM H r rs F.len
  have h4 := F.noneCount_runAux ansM H r rs F.len
  have h5 := F.length_runAux ansM H r rs F.len
  have hlen : ∀ l : List (Option Req' × (Option Resp' × (X × Y))),
      (l.filterMap Prod.fst).length + noneCount l = l.length := by
    intro l
    induction l with
    | nil => rfl
    | cons e l ih => rcases e with ⟨_ | _, _⟩ <;> simp [noneCount] at ih ⊢ <;> omega
  have h6 := hlen (F.runAux ansM H r rs F.len).2
  rw [h4, h5] at h6
  have hL : F.len = F.K + F.qR + F.qP := rfl
  change ((F.runAux ansM H r rs F.len).2.filterMap Prod.fst).length = F.K
  omega

/-- **The main requests of `rs` number `K · |rs|`** when `rs` has at most `Q` requests. -/
theorem length_mainReqs (rs : List Req) (hrs : rs.length ≤ Q) :
    (F.mainReqs Q ansM H rs).length = F.K * rs.length := by
  induction rs using List.reverseRecOn with
  | nil => rfl
  | append_singleton rs r ih =>
    simp only [List.length_append, List.length_singleton] at hrs
    rw [F.mainReqs_append, if_pos (by omega), List.length_append, ih (by omega),
      F.length_filterMap_runEntries, List.length_append, List.length_singleton, Nat.mul_succ]

end MultiRelay

namespace Distinguisher

variable {W X Y Req Resp Req' Resp' Xs Ys : Type} [Fintype W] [DecidableEq W] [Fintype X]
  [DecidableEq X] [Fintype Y] [DecidableEq Y] [Fintype Req] [DecidableEq Req] [Fintype Resp]
  [DecidableEq Resp] [Fintype Req'] [DecidableEq Req'] [Fintype Resp'] [DecidableEq Resp']
  [Inhabited X] [Inhabited Req'] [AddGroup Y] [AddGroup Ys] [Fintype Ys] [DecidableEq Ys] {n m : ℕ}
  (D : Distinguisher W X Y Req Resp n m) (F : MultiRelay X Y Req Resp Req' Resp' Xs Ys) (b Q : ℕ)
      (ansM : List Req' → Req' → Option Resp')
  (H : X → Y)

/-- **The main requests in the logs of the final placement** of a basis state `g` are the idle
request or requests that the program of one of the first `Q` requests in `g`'s logs can make. -/
theorem origin_place (g : GameReg W n X Y Req Resp m) {r' : Req'}
    (hr : r' ∈ requests (splitLogs (D.place F b Q ansM H (relaySlots n m F) m g)).2) :
    r' = F.idle ∨ ∃ r ∈ (requests (splitLogs g).2).take Q, F.CanAsk r r' := by
  have hl : (splitLogs (D.place F b Q ansM H (relaySlots n m F) m g)).2 =
      fun t : Fin (relaySlots n m F) =>
        ((D.subEntries F b Q ansM H (relaySlots n m F) m g.1).getD t blankEntry).1 := by
    simp only [place, Equiv.apply_symm_apply]
  rw [hl, requests, requestsBefore_ofList _ _ rfl _ le_rfl] at hr
  have hr' := ((List.take_sublist _ _).filterMap Prod.fst).subset hr
  rw [subEntries, D.stEntries_self] at hr'
  rw [requests, requestsBefore_eq_logEntries _ m le_rfl]
  exact F.origin_subEntriesL n b Q ansM H _ _ hr'

end Distinguisher

end GordieHowe.Quantum
