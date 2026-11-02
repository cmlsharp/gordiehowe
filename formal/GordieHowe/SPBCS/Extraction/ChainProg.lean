-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.SPBCS.ComponentModel

@[expose] public section

/-!
# The queries of one chain

`ComponentModel.chainProg`: the key and `xof` queries of a chain whose chain input at the items `l`
is `inputOf l`, as a classical oracle program (`run_chainProg`: the chain `chainWith` and its `xof`
answers; `mem_trace_chainProg_iff`: its queries; `length_trace_chainProg`: two per round). The
compiled verifiers' query programs are built from it.
-/

namespace GordieHowe.SPBCS

open GordieHowe.QROM GordieHowe.IOP

variable {k kN kS L e : ℕ}

namespace ComponentModel

variable {m : ℕ} {P : ProtocolSpec m} [∀ i, Fintype (P.Challenge i)]
  [∀ i, DecidableEq (P.Challenge i)] (C : ComponentModel P k kN L e)
  (wr : (i : P.MessageIdx) → C.MessageWrite i) (salt : FiatShamirSalt kS)
  (inputOf : List (Item k C.W) → Bytes L)

/-- **The key and `xof` queries of a chain** whose chain input at the items `l` is `inputOf l`,
returning the chain and the `xof` answer of each round. The program queries the key and the point
at every round; at a prover round the item is the write. -/
def chainProg : (r : ℕ) → r ≤ m →
    GordieHowe.OracleProg (Query k kN kS L) (Out k e) (List (Item k C.W) × List (Out k e))
  | 0, _ => .pure ([], [])
  | r + 1, hr => (chainProg r (by omega)).bind fun st =>
      .query (.transcript (inputOf st.1)) fun a => .query (.xof a.digest salt) fun s =>
        .pure (st.1 ++ [if hd : P.dir ⟨r, by omega⟩ = .P_to_V then
          .write ⟨⟨⟨r, by omega⟩, hd⟩, wr ⟨⟨r, by omega⟩, hd⟩⟩ else .absorb s.digest], st.2 ++ [s])

variable (h : Query k kN kS L → Out k e)

/-- The key function of chain inputs `inputOf` under `h`. -/
def keyOfInput (l : List (Item k C.W)) : Digest k := (h (.transcript (inputOf l))).digest

/-- The `xof` answers of a chain's rounds. -/
def answersWith (keyOf : List (Item k C.W) → Digest k) : (r : ℕ) → r ≤ m → List (Out k e)
  | 0, _ => []
  | r + 1, hr => answersWith keyOf r (by omega) ++
      [h (.xof (keyOf (C.chainWith wr keyOf salt h r (by omega))) salt)]

theorem length_answersWith (keyOf : List (Item k C.W) → Digest k) :
    ∀ r (hr : r ≤ m), (C.answersWith wr salt h keyOf r hr).length = r
  | 0, _ => rfl
  | r + 1, hr => by simp [answersWith, length_answersWith keyOf r]

theorem answersWith_getElem? (keyOf : List (Item k C.W) → Digest k) :
    ∀ r (hr : r ≤ m) j (hj : j < r), (C.answersWith wr salt h keyOf r hr)[j]? =
      some (h (.xof (keyOf (C.chainWith wr keyOf salt h j (by omega))) salt))
  | 0, _, _, hj => absurd hj (Nat.not_lt_zero _)
  | r + 1, hr, j, hj => by
    rw [answersWith]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj' | rfl
    · rw [List.getElem?_append_left (by rw [length_answersWith]; exact hj'),
        answersWith_getElem? keyOf r (by omega) j hj']
    · rw [List.getElem?_append_right (by rw [length_answersWith]), length_answersWith]
      simp

/-- **The challenge of a chain read from its answers.** -/
theorem chalWith_eq_answers (keyOf : List (Item k C.W) → Digest k) (i : P.ChallengeIdx) :
    C.chalWith wr keyOf salt h i = ((C.answersWith wr salt h keyOf m le_rfl)[i.1.1]?).bind
      fun s => (C.sampler i).sample s.stream := by
  rw [answersWith_getElem? _ _ _ _ _ _ _ i.1.1 i.1.2, Option.bind_some, chalWith]

/-- **The run of the chain program**: the chain for the keys of its inputs, and its answers. -/
theorem run_chainProg : ∀ r (hr : r ≤ m), (C.chainProg wr salt inputOf r hr).run h =
    (C.chainWith wr (C.keyOfInput inputOf h) salt h r hr,
      C.answersWith wr salt h (C.keyOfInput inputOf h) r hr)
  | 0, _ => rfl
  | r + 1, hr => by
    rw [chainProg, GordieHowe.OracleProg.run_bind, run_chainProg r (by omega)]
    simp only [chainWith, answersWith, itemWith, GordieHowe.OracleProg.run_query,
      GordieHowe.OracleProg.run_pure]
    rfl

/-- **The queries of the chain program**: at each round below `r`, the input of the chain so far
and the `xof` point at its key. -/
theorem mem_trace_chainProg : ∀ r (hr : r ≤ m) j (hj : j < r),
    Query.transcript (inputOf (C.chainWith wr (C.keyOfInput inputOf h) salt h j (by omega))) ∈
        (C.chainProg wr salt inputOf r hr).trace h ∧
      Query.xof (C.keyOfInput inputOf h (C.chainWith wr (C.keyOfInput inputOf h) salt h j (by omega)))
        salt ∈ (C.chainProg wr salt inputOf r hr).trace h
  | 0, _, _, hj => absurd hj (Nat.not_lt_zero _)
  | r + 1, hr, j, hj => by
    rw [chainProg, GordieHowe.OracleProg.trace_bind, run_chainProg]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj' | rfl
    · obtain ⟨h1, h2⟩ := mem_trace_chainProg r (by omega) j hj'
      exact ⟨List.mem_append_left _ h1, List.mem_append_left _ h2⟩
    · simp only [GordieHowe.OracleProg.trace_query, GordieHowe.OracleProg.trace_pure]
      exact ⟨List.mem_append_right _ (List.mem_cons_self ..),
        List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))⟩

/-- **Every query of the chain program** is the input of a prefix of the chain or the `xof` point
at its key. -/
theorem mem_trace_chainProg_iff : ∀ r (hr : r ≤ m) {q : Query k kN kS L},
    q ∈ (C.chainProg wr salt inputOf r hr).trace h ↔ ∃ j, ∃ hj : j < r,
      q = .transcript (inputOf (C.chainWith wr (C.keyOfInput inputOf h) salt h j (by omega))) ∨
      q = .xof (C.keyOfInput inputOf h (C.chainWith wr (C.keyOfInput inputOf h) salt h j (by omega)))
        salt
  | 0, _, q => by simp [chainProg]
  | r + 1, hr, q => by
    rw [chainProg, GordieHowe.OracleProg.trace_bind, run_chainProg, List.mem_append,
      mem_trace_chainProg_iff r (by omega)]
    simp only [GordieHowe.OracleProg.trace_query, GordieHowe.OracleProg.trace_pure, List.mem_cons,
      List.not_mem_nil, or_false]
    constructor
    · rintro (⟨j, hj, hq⟩ | hq | hq)
      · exact ⟨j, by omega, hq⟩
      · exact ⟨r, by omega, Or.inl hq⟩
      · exact ⟨r, by omega, Or.inr hq⟩
    · rintro ⟨j, hj, hq⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj' | rfl
      · exact Or.inl ⟨j, hj', hq⟩
      · exact Or.inr hq

theorem length_trace_chainProg : ∀ r (hr : r ≤ m),
    ((C.chainProg wr salt inputOf r hr).trace h).length = 2 * r
  | 0, _ => rfl
  | r + 1, hr => by
    rw [chainProg, GordieHowe.OracleProg.trace_bind, List.length_append,
      length_trace_chainProg r (by omega)]
    simp only [GordieHowe.OracleProg.trace_query, GordieHowe.OracleProg.trace_pure, List.length_cons,
      List.length_nil]
    omega

end ComponentModel

end GordieHowe.SPBCS
