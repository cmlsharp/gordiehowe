-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Pure.ClassicalSim

@[expose] public section

/-!
# Deterministic strategies against challengers with deterministic replies

A deterministic classical strategy (`Interaction.DetStrategy`) against a challenger whose replies
are point masses plays one history, `detPlay`. When the replies answer the `k`-th request (moves
`some c`; `none` is a query slot) by `a k c`, the history depends on the answer function only
through its values at the requests the strategy makes, and the `k`-th request depends only on the
answers to the requests before it. So, when no request numbered `Q` or later is answered, the play
with answers given on the fly is the play with the answer vector of length `Q` computed request by
request (`detPlay_ansRep_eq_vecAns`), which turns the play into rounds indexed by the requests.

- `detPlay`, `cont_toStrategy_eq_pure`: the history of a deterministic strategy against point-mass
  replies, and the continuation of the interaction as the point mass at it and the output.
  `exists_detPlay_eq_append`: the play extends the history it starts from.
- `ansRep x a`: the replies answering the `k`-th request `c` by `a k c` and every move with `x` (the
  oracle in force, unchanged). `exists_histReqs_detPlay_eq_append`, `histReqs_append_move`: the
  requests of the play extend those of the starting history, one move at a time.
  `detPlay_ansRep_congr`: plays with answer functions agreeing on the requests made are equal.
  `take_histReqs_detPlay_ansRep`: the first `K + 1` requests depend only on the answers to the
  first `K`.
- `vecAns`, `reqAt`, `ansVec`, `ansVec_apply`: the answers of a vector, the request number `j` of
  the play with the answers of a vector of length `j`, and the vector of answers of `a`, request by
  request. `detPlay_ansRep_eq_vecAns`: the consistency.
-/

namespace GordieHowe.Interaction

open GordieHowe.Quantum

variable {I M R O : Type*}

/-- **The history of a deterministic strategy** with input `i` against the point-mass replies
`rep`, `k` rounds from the history `h`. -/
def detPlay (s : DetStrategy I M R O) (i : I) (rep : Hist M R → M → R) : Hist M R → ℕ → Hist M R
  | h, 0 => h
  | h, k + 1 => detPlay s i rep (h ++ [(s.next i h, rep h (s.next i h))]) k

/-- **A deterministic strategy against point-mass replies** has as continuation the point mass at
its history and its output. -/
theorem cont_toStrategy_eq_pure {Ω : Type*} (s : DetStrategy I M R O) (χ : Challenger Ω I M R)
    (ω : Ω) (rep : Hist M R → M → R) (hrep : ∀ h m, χ.reply ω h m = PMF.pure (rep h m)) :
    ∀ k h, cont s.toStrategy χ ω h k = PMF.pure (detPlay s (χ.input ω) rep h k,
      s.out (χ.input ω) (detPlay s (χ.input ω) rep h k))
  | 0, h => by
    simp only [cont, DetStrategy.toStrategy, PMF.pure_map, detPlay]
  | k + 1, h => by
    simp only [cont, DetStrategy.toStrategy, PMF.pure_bind, hrep]
    exact cont_toStrategy_eq_pure s χ ω rep hrep k _

/-- **The play extends the history it starts from.** -/
theorem exists_detPlay_eq_append (s : DetStrategy I M R O) (i : I) (rep : Hist M R → M → R) :
    ∀ k h, ∃ t, detPlay s i rep h k = h ++ t
  | 0, h => ⟨[], by simp [detPlay]⟩
  | k + 1, h => by
    obtain ⟨t, ht⟩ := exists_detPlay_eq_append s i rep k (h ++ [(s.next i h, rep h (s.next i h))])
    exact ⟨(s.next i h, rep h (s.next i h)) :: t, by rw [detPlay, ht]; simp⟩

/-! ### Answers to numbered requests -/

variable {Req Resp Ix : Type*}

/-- **The replies answering numbered requests**: a query slot gets no response; the `k`-th request
`c` gets `a k c`; both with the oracle `x`. -/
def ansRep (x : Ix) (a : ℕ → Req → Option Resp) (h : Hist (Option Req) (Option Resp × Ix)) :
    Option Req → Option Resp × Ix
  | none => (none, x)
  | some c => (a (Env.histReqs h).length c, x)

variable (s : DetStrategy I (Option Req) (Option Resp × Ix) O) (i : I) (x : Ix)

/-- **The requests of the play extend the requests of the history it starts from.** -/
theorem exists_histReqs_detPlay_eq_append (a : ℕ → Req → Option Resp) (k : ℕ)
    (h : Hist (Option Req) (Option Resp × Ix)) :
    ∃ t, Env.histReqs (detPlay s i (ansRep x a) h k) = Env.histReqs h ++ t := by
  obtain ⟨t, ht⟩ := exists_detPlay_eq_append s i (ansRep x a) k h
  exact ⟨Env.histReqs t, by rw [ht, Env.histReqs, Env.histReqs, Env.histReqs, List.filterMap_append]⟩

/-- **The next request extends the requests by the move**: after the move `e`, the requests of the
history are those before it followed by the request of `e`, if any. -/
theorem histReqs_append_move (h : Hist (Option Req) (Option Resp × Ix)) (e : Option Req)
    (r : Option Resp × Ix) : Env.histReqs (h ++ [(e, r)]) = Env.histReqs h ++ e.toList :=
  Env.histReqs_append_singleton h (e, r)

/-- **Plays with answer functions agreeing on the requests made are equal.** -/
theorem detPlay_ansRep_congr {a a' : ℕ → Req → Option Resp} :
    ∀ k h, (∀ j (hj : j < (Env.histReqs (detPlay s i (ansRep x a) h k)).length),
      a j (Env.histReqs (detPlay s i (ansRep x a) h k))[j] =
        a' j (Env.histReqs (detPlay s i (ansRep x a) h k))[j]) →
      detPlay s i (ansRep x a) h k = detPlay s i (ansRep x a') h k
  | 0, h, _ => rfl
  | k + 1, h, hyp => by
    have hrep : ansRep x a h (s.next i h) = ansRep x a' h (s.next i h) := by
      cases he : s.next i h with
      | none => rfl
      | some c =>
        simp only [ansRep]
        obtain ⟨t, ht⟩ := exists_histReqs_detPlay_eq_append s i x a k
          (h ++ [(s.next i h, ansRep x a h (s.next i h))])
        rw [histReqs_append_move, show (s.next i h).toList = [c] by rw [he]; rfl] at ht
        have hlen : (Env.histReqs h).length <
            (Env.histReqs (detPlay s i (ansRep x a) h (k + 1))).length := by
          rw [detPlay, ht]
          simp
        have hc : (Env.histReqs (detPlay s i (ansRep x a) h (k + 1)))[(Env.histReqs h).length] =
            c := by
          simp only [detPlay, ht]
          rw [List.getElem_append_left (by simp)]
          simp
        have := hyp _ hlen
        rw [hc] at this
        rw [this]
    change detPlay s i (ansRep x a) (h ++ [(s.next i h, ansRep x a h (s.next i h))]) k =
      detPlay s i (ansRep x a') (h ++ [(s.next i h, ansRep x a' h (s.next i h))]) k
    rw [← hrep]
    exact detPlay_ansRep_congr k _ hyp

/-- **The first `K + 1` requests depend only on the answers to the first `K`.** -/
theorem take_histReqs_detPlay_ansRep {a a' : ℕ → Req → Option Resp} (K : ℕ) :
    ∀ k h, (∀ j < K, ∀ (hj : j < (Env.histReqs (detPlay s i (ansRep x a) h k)).length),
      a j (Env.histReqs (detPlay s i (ansRep x a) h k))[j] =
        a' j (Env.histReqs (detPlay s i (ansRep x a) h k))[j]) →
      (Env.histReqs (detPlay s i (ansRep x a) h k)).take (K + 1) =
        (Env.histReqs (detPlay s i (ansRep x a') h k)).take (K + 1)
  | 0, h, _ => rfl
  | k + 1, h, hyp => by
    cases he : s.next i h with
    | none =>
      have hrep : ansRep x a h (s.next i h) = ansRep x a' h (s.next i h) := by
        rw [he]
        rfl
      change (Env.histReqs (detPlay s i (ansRep x a)
          (h ++ [(s.next i h, ansRep x a h (s.next i h))]) k)).take (K + 1) =
        (Env.histReqs (detPlay s i (ansRep x a')
          (h ++ [(s.next i h, ansRep x a' h (s.next i h))]) k)).take (K + 1)
      rw [← hrep]
      exact take_histReqs_detPlay_ansRep K k _ hyp
    | some c =>
      by_cases hK : (Env.histReqs h).length < K
      · have hrep : ansRep x a h (s.next i h) = ansRep x a' h (s.next i h) := by
          simp only [he, ansRep]
          obtain ⟨t, ht⟩ := exists_histReqs_detPlay_eq_append s i x a k
            (h ++ [(s.next i h, ansRep x a h (s.next i h))])
          rw [histReqs_append_move, show (s.next i h).toList = [c] by rw [he]; rfl] at ht
          have hlen : (Env.histReqs h).length <
              (Env.histReqs (detPlay s i (ansRep x a) h (k + 1))).length := by
            rw [detPlay, ht]
            simp
          have hc : (Env.histReqs (detPlay s i (ansRep x a) h (k + 1)))[(Env.histReqs h).length] =
              c := by
            simp only [detPlay, ht]
            rw [List.getElem_append_left (by simp)]
            simp
          have := hyp _ hK hlen
          rw [hc] at this
          rw [this]
        change (Env.histReqs (detPlay s i (ansRep x a)
            (h ++ [(s.next i h, ansRep x a h (s.next i h))]) k)).take (K + 1) =
          (Env.histReqs (detPlay s i (ansRep x a')
            (h ++ [(s.next i h, ansRep x a' h (s.next i h))]) k)).take (K + 1)
        rw [← hrep]
        exact take_histReqs_detPlay_ansRep K k _ hyp
      · have key : ∀ a'' : ℕ → Req → Option Resp,
            (Env.histReqs (detPlay s i (ansRep x a'') h (k + 1))).take (K + 1) =
              (Env.histReqs h ++ [c]).take (K + 1) := fun a'' => by
          obtain ⟨t, ht⟩ := exists_histReqs_detPlay_eq_append s i x a'' k
            (h ++ [(s.next i h, ansRep x a'' h (s.next i h))])
          rw [histReqs_append_move, show (s.next i h).toList = [c] by rw [he]; rfl] at ht
          simp only [detPlay]
          rw [ht, List.take_append_of_le_length (by simp; omega)]
        rw [key a, key a']

/-! ### The answer vector -/

/-- **The answers of a vector** of length `j`: the `k`-th request gets entry `k`, or none past the
vector. -/
def vecAns {j : ℕ} (v : Fin j → Option Resp) : ℕ → Req → Option Resp :=
  fun k _ => if h : k < j then v ⟨k, h⟩ else none

/-- **Request number `j` of the play of `m` rounds** with the answers of the vector `v` of length
`j`, if the strategy makes it. -/
def reqAt (m j : ℕ) (v : Fin j → Option Resp) : Option Req :=
  (Env.histReqs (detPlay s i (ansRep x (vecAns v)) [] m))[j]?

/-- **The answer vector of the answer function `a`**, request by request: entry `j` is the answer
`a j c` to request number `j` of the play with the earlier entries, or none if there is no such
request. -/
def ansVec (m : ℕ) (a : ℕ → Req → Option Resp) : (j : ℕ) → Fin j → Option Resp
  | 0 => Fin.elim0
  | j + 1 => Fin.snoc (α := fun _ => Option Resp) (ansVec m a j)
      ((reqAt s i x m j (ansVec m a j)).elim none (a j))

/-- **Entry `k` of the answer vector** is the answer `a k c` to request number `k` of the play with
the first `k` entries, or none if there is no such request. -/
theorem ansVec_apply (m : ℕ) (a : ℕ → Req → Option Resp) :
    ∀ j (k : Fin j), ansVec s i x m a j k =
      (reqAt s i x m k (ansVec s i x m a k)).elim none (a k)
  | j + 1, k => by
    rw [ansVec]
    by_cases hk : (k : ℕ) < j
    · have : k = Fin.castSucc ⟨k, hk⟩ := rfl
      rw [this, Fin.snoc_castSucc, ansVec_apply m a j ⟨k, hk⟩]
      rfl
    · have hkj : (k : ℕ) = j := by omega
      have : k = Fin.last j := Fin.ext hkj
      subst this
      rw [Fin.snoc_last]
      rfl

/-- **The consistency of the answer vector**: when `a` answers no request numbered `Q` or later,
the play with the answers `a` given on the fly is the play with the answers of the vector of `a`
of length `Q`. -/
theorem detPlay_ansRep_eq_vecAns (m Q : ℕ) (a : ℕ → Req → Option Resp)
    (ha : ∀ k, Q ≤ k → ∀ c, a k c = none) :
    detPlay s i (ansRep x a) [] m = detPlay s i (ansRep x (vecAns (ansVec s i x m a Q))) [] m := by
  set rs := Env.histReqs (detPlay s i (ansRep x a) [] m)
  have key : ∀ k (hk : k < rs.length), a k rs[k] = vecAns (ansVec s i x m a Q) k rs[k] := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hk
      by_cases hQ : k < Q
      · simp only [vecAns, hQ, dite_true]
        rw [ansVec_apply]
        have hreq : reqAt s i x m k (ansVec s i x m a k) = some rs[k] := by
          have htake := take_histReqs_detPlay_ansRep s i x (a := a)
            (a' := vecAns (ansVec s i x m a k)) k m [] fun j hj hjl => by
              rw [ih j hj hjl]
              simp only [vecAns, show j < Q by omega, hj, dite_true]
              rw [ansVec_apply, ansVec_apply]
          have h1 : (rs.take (k + 1))[k]? = some rs[k] := by
            rw [List.getElem?_take_of_lt (by omega)]
            exact List.getElem?_eq_getElem hk
          rw [reqAt, ← List.getElem?_take_of_lt (j := k + 1) (by omega), ← htake]
          exact h1
        rw [hreq]
        rfl
      · rw [ha k (by omega)]
        simp [vecAns, hQ]
  exact detPlay_ansRep_congr s i x m [] key

end GordieHowe.Interaction
