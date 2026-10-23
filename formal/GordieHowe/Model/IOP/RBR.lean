-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import Mathlib.Data.Fintype.Pi
public import Mathlib.Basic.NNReal.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import GordieHowe.Foundations.Probability.Probability

@[expose] public section

/-!
# Round-by-round knowledge soundness, worst case per prefix

A thin framework for public-coin interactive protocols, shaped after ArkLib
(`ArkLib/OracleReduction/Security/RoundByRound.lean`) so a later bridge to its
definitions is direct:

* `ProtocolSpec`, `Transcript`, `ProtocolSpec.concat` follow ArkLib's
  `ProtocolSpec`, `Transcript` (the first `k` messages) and `concat`;
* `Extractor` is ArkLib's one-shot round-by-round extractor (`Extractor.RoundByRoundOneShot`)
  without query logs: it reads the statement and the partial transcript, whose oracle messages it
  sees in full;
* `KnowledgeStateFunction` is ArkLib's `KnowledgeStateFunctionOneShot` with a
  deterministic verifier decision;
* `rbrKnowledgeSoundness` is the worst-case-per-prefix condition of ArkLib's
  `rbrKnowledgeSoundnessWorstCase`, for the one-shot extractor, stated as a
  probability over the uniform fresh challenge (`GordieHowe/Foundations/Probability/Probability.lean`): at
  every prefix, the challenge moves the state from false to true while the
  extractor fails with probability at most `ε i`. The extractor and the state
  function are arguments, not existentially quantified: without a cost bound on
  the extractor the notion is vacuous for relations whose statements have
  witnesses (the docstring of `rbrKnowledgeSoundness`). The proofs use the
  equivalent counting forms `rbrKnowledgeSoundness_iff_count` and
  `knowledgeSoundness_iff_count`.

The verifier's decision is a function of the statement and the full transcript.
How it reads oracle messages (queries, Merkle openings) does not matter for
interactive soundness and is left out.

`knowledgeSoundness_of_rbr`: round-by-round error `ε` gives knowledge soundness with error
`∑ i, ε i` against every prover, at the straight-line extractor `Extractor.straightLine`. ArkLib
states this step (`rbrKnowledgeSoundness_implies_knowledgeSoundness`); this development does not use
ArkLib's statement and proves it here. Deterministic provers suffice: a randomized prover is a
mixture of them (`knowledgeSoundness.randomized`).
-/

namespace GordieHowe

open scoped NNReal

/-- A bound on both halves of a sum-indexed function bounds its reindexing. -/
theorem Sum.elim_comp_le_of {ι ι₁ ι₂ : Type*} (e : ι ≃ ι₁ ⊕ ι₂) (a : ι₁ → ℝ≥0) (b : ι₂ → ℝ≥0)
    {δ : ℝ≥0} (ha : ∀ j, a j ≤ δ) (hb : ∀ j, b j ≤ δ) (i : ι) : (Sum.elim a b ∘ e) i ≤ δ := by
  rw [Function.comp_apply]
  rcases e i with j | j
  exacts [ha j, hb j]

end GordieHowe

namespace GordieHowe.IOP

open scoped NNReal

/-- Who sends a round's message. -/
inductive Direction
  | P_to_V
  | V_to_P
  deriving DecidableEq

/-- A protocol with `n` rounds: each round's direction and message type. -/
structure ProtocolSpec (n : ℕ) where
  dir : Fin n → Direction
  «Type» : Fin n → Type

variable {n : ℕ}

namespace ProtocolSpec

variable (P : ProtocolSpec n)

/-- The verifier's rounds. -/
def ChallengeIdx : Type := {i : Fin n // P.dir i = .V_to_P}

/-- A finite protocol has finitely many verifier moves. -/
instance challengeIdxFintype : Fintype P.ChallengeIdx :=
  inferInstanceAs (Fintype { i : Fin n // P.dir i = .V_to_P })

/-- The verifier's rounds have decidable equality, as indices of `Fin n`. -/
instance challengeIdxDecidableEq : DecidableEq P.ChallengeIdx :=
  inferInstanceAs (DecidableEq { i : Fin n // P.dir i = .V_to_P })

/-- The prover's rounds. -/
def MessageIdx : Type := {i : Fin n // P.dir i = .P_to_V}

/-- A finite protocol has finitely many prover moves. -/
instance messageIdxFintype : Fintype P.MessageIdx :=
  inferInstanceAs (Fintype { i : Fin n // P.dir i = .P_to_V })

/-- The prover's rounds have decidable equality, as indices of `Fin n`. -/
instance messageIdxDecidableEq : DecidableEq P.MessageIdx :=
  inferInstanceAs (DecidableEq { i : Fin n // P.dir i = .P_to_V })

/-- The challenge type of a verifier round. -/
abbrev Challenge (i : P.ChallengeIdx) : Type := P.Type i.1

/-- The first `k` messages. -/
def Transcript (k : Fin (n + 1)) : Type := (i : Fin k) → P.Type (Fin.castLE (by omega) i)

/-- Append round `m`'s message to a transcript of the first `m` rounds. -/
def concat {m : Fin n} (tr : P.Transcript m.castSucc) (msg : P.Type m) :
    P.Transcript m.succ :=
  Fin.snoc (α := fun i : Fin ((m : ℕ) + 1) => P.Type (Fin.castLE (by omega) i)) tr msg

/-- One challenge for every verifier round. -/
abbrev Challenges : Type := (i : P.ChallengeIdx) → P.Challenge i

end ProtocolSpec

variable {P : ProtocolSpec n} {StmtIn WitIn : Type}

/-- The first `m` messages of a transcript of the first `k` rounds, `m ≤ k`. -/
def ProtocolSpec.Transcript.take {k : Fin (n + 1)} (m : Fin (n + 1)) (hm : m ≤ k)
    (tr : P.Transcript k) : P.Transcript m :=
  fun i => tr (Fin.castLE (by omega) i)

/-- Appending a message does not change the first `m` messages, `m` at most the
length before appending. -/
theorem ProtocolSpec.take_concat {j : Fin n} (tr : P.Transcript j.castSucc) (msg : P.Type j)
    (m : Fin (n + 1)) (hm : m ≤ j.castSucc) :
    (P.concat tr msg).take m (hm.trans (Fin.castSucc_le_succ j)) = tr.take m hm := by
  funext i
  have hi : (i : ℕ) < j := by
    have := i.2
    have : m.val ≤ j.val := hm
    omega
  simp only [ProtocolSpec.Transcript.take, ProtocolSpec.concat, Fin.snoc, Fin.val_castLE, hi,
    dite_true]
  rfl

/-- Appending a message does not change the earlier messages. -/
theorem ProtocolSpec.concat_apply_of_lt {m : Fin n} (tr : P.Transcript m.castSucc)
    (msg : P.Type m) (i : ℕ) (hi : i < m) :
    P.concat tr msg ⟨i, by simp only [Fin.val_succ]; omega⟩ = tr ⟨i, hi⟩ := by
  simp only [ProtocolSpec.concat, Fin.snoc, hi, dite_true]
  rfl

/-- The appended message is the last message. -/
theorem ProtocolSpec.concat_apply_last {m : Fin n} (tr : P.Transcript m.castSucc)
    (msg : P.Type m) : P.concat tr msg ⟨m, by simp⟩ = msg := by
  simp only [ProtocolSpec.concat, Fin.snoc, lt_irrefl, dite_false]
  rfl

/-- A deterministic prover strategy: each prover message is a function of the
statement and the transcript so far. -/
def Prover (P : ProtocolSpec n) (StmtIn : Type) : Type :=
  (i : P.MessageIdx) → StmtIn → P.Transcript i.1.castSucc → P.Type i.1

/-- The transcript of the first `k` rounds when the prover answers the
challenges `ch`. -/
def Prover.runTo (prv : Prover P StmtIn) (x : StmtIn) (ch : P.Challenges) :
    (k : ℕ) → (hk : k ≤ n) → P.Transcript ⟨k, by omega⟩
  | 0, _ => fun i => i.elim0
  | k + 1, hk =>
    let m : Fin n := ⟨k, by omega⟩
    let tr : P.Transcript m.castSucc := prv.runTo x ch k (by omega)
    if hdir : P.dir m = .P_to_V then P.concat tr (prv ⟨m, hdir⟩ x tr)
    else P.concat tr (ch ⟨m, by cases h : P.dir m <;> simp_all⟩)

/-- The full transcript. -/
def Prover.run (prv : Prover P StmtIn) (x : StmtIn) (ch : P.Challenges) :
    P.Transcript (Fin.last n) :=
  prv.runTo x ch n le_rfl

/-- After a challenge round the transcript is extended by that round's challenge. -/
theorem Prover.runTo_succ_of_challenge (prv : Prover P StmtIn) (x : StmtIn) (ch : P.Challenges)
    (i : P.ChallengeIdx) :
    prv.runTo x ch (i.1 + 1) i.1.2 = P.concat (prv.runTo x ch i.1 i.1.2.le) (ch i) := by
  have h : ¬ P.dir i.1 = .P_to_V := by simp [i.2]
  rw [Prover.runTo]
  simp only [h, dite_false]
  rfl

/-- After a prover round the transcript is extended by the prover's answer to the
transcript so far. -/
theorem Prover.runTo_succ_of_message (prv : Prover P StmtIn) (x : StmtIn) (ch : P.Challenges)
    (i : P.MessageIdx) :
    prv.runTo x ch (i.1 + 1) i.1.2 =
      P.concat (prv.runTo x ch i.1 i.1.2.le) (prv i x (prv.runTo x ch i.1 i.1.2.le)) := by
  rw [Prover.runTo]
  simp only [i.2, dite_true]
  rfl

/-- **A prover that reads its strategy off the statement**: at the statement `x` it runs the
prover `f x`. An honest prover whose input is decoded from the statement and a witness is of this
form. -/
def Prover.ofStatement (f : StmtIn → Prover P StmtIn) : Prover P StmtIn :=
  fun i x tr => f x i x tr

/-- The runs of `Prover.ofStatement f` on `x` are the runs of `f x`. -/
theorem Prover.runTo_ofStatement (f : StmtIn → Prover P StmtIn) (x : StmtIn) (ch : P.Challenges)
    (k : ℕ) (hk : k ≤ n) : (Prover.ofStatement f).runTo x ch k hk = (f x).runTo x ch k hk := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [Prover.runTo, ih]
    rfl

/-- The run of `Prover.ofStatement f` on `x` is the run of `f x`. -/
theorem Prover.run_ofStatement (f : StmtIn → Prover P StmtIn) (x : StmtIn) (ch : P.Challenges) :
    (Prover.ofStatement f).run x ch = (f x).run x ch :=
  Prover.runTo_ofStatement f x ch n le_rfl

/-- The first `k` rounds depend only on the challenges of rounds before `k`. -/
theorem Prover.runTo_congr (prv : Prover P StmtIn) (x : StmtIn) {ch ch' : P.Challenges} {k : ℕ}
    (hk : k ≤ n) (h : ∀ i : P.ChallengeIdx, i.1 < k → ch i = ch' i) :
    prv.runTo x ch k hk = prv.runTo x ch' k hk := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Prover.runTo, Prover.runTo, ih (by omega) fun i hi => h i (by omega)]
    split
    · rfl
    · congr 1
      exact h _ (by simp)

/-- The first `m` messages of the first `k` rounds are the first `m` rounds. -/
theorem Prover.take_runTo (prv : Prover P StmtIn) (x : StmtIn) (ch : P.Challenges) {k : ℕ}
    (hk : k ≤ n) (m : Fin (n + 1)) (hm : m.1 ≤ k) :
    (prv.runTo x ch k hk).take m hm = prv.runTo x ch m m.is_le := by
  induction k with
  | zero =>
    obtain ⟨m, hm'⟩ := m
    obtain rfl : m = 0 := by simpa using hm
    rfl
  | succ k ih =>
    rcases Nat.lt_or_ge (m : ℕ) (k + 1) with hlt | hge
    · rw [Prover.runTo]
      split
      · exact (P.take_concat _ _ m (by rw [Fin.le_iff_val_le_val]; simp; omega)).trans (ih _ _)
      · exact (P.take_concat _ _ m (by rw [Fin.le_iff_val_le_val]; simp; omega)).trans (ih _ _)
    · obtain ⟨m, hm'⟩ := m
      obtain rfl : m = k + 1 := by simp at hm hge; omega
      rfl

/-- A deterministic verifier decision on the full transcript. -/
def Verifier (P : ProtocolSpec n) (StmtIn : Type) : Type := StmtIn → P.Transcript (Fin.last n) → Bool

/-- **A one-shot round-by-round extractor**: a candidate witness from the statement and any
partial transcript (`extract`, applied through the coercion to a function).

CMS19 Definition 8.5 (p. 40) asks for "a polynomial-time extractor E". Nothing in this
structure bounds the cost of `extract`, and without such a bound knowledge soundness is vacuous
for a relation whose statements have witnesses (`rbrKnowledgeSoundness`). The invariant kept
instead: every extractor is constructed by a named definition (or `abbrev`) whose docstring has a
"Running time" paragraph arguing that it runs in polynomial time, and every theorem names the
extractor it is about. The Lean lint `scripts/CostLint.lean`, run by `scripts/check.sh`,
enforces the docstring for every declaration whose type is an `Extractor`, however the value is
constructed. An unnamed extractor written inline inside a statement is not a declaration and
is not caught, so headlines must name theirs. -/
structure Extractor (P : ProtocolSpec n) (StmtIn WitIn : Type) where
  /-- The candidate witness at a prefix of length `m`. -/
  extract : (m : Fin (n + 1)) → StmtIn → P.Transcript m → WitIn

instance {StmtIn WitIn : Type} :
    CoeFun (Extractor P StmtIn WitIn) fun _ => (m : Fin (n + 1)) → StmtIn → P.Transcript m → WitIn :=
  ⟨Extractor.extract⟩

/-- **A state function, CMS19 Definition 8.3** (pp. 39–40; the same as Chiesa–Yogev 2024
Definition 31.1.1, pp. 382–383): false on the empty transcript, never made true by a prover
message, and true whenever the verifier accepts. The polarity is CMS19's: `true` is their state
`1`, the transcripts that escaped rejection. ArkLib calls this `KnowledgeStateFunctionOneShot`. -/
structure KnowledgeStateFunction (V : Verifier P StmtIn) where
  toFun : (m : Fin (n + 1)) → StmtIn → P.Transcript m → Prop
  toFun_empty : ∀ x tr, ¬ toFun 0 x tr
  toFun_next : ∀ (m : Fin n), P.dir m = .P_to_V →
    ∀ x (tr : P.Transcript m.castSucc) msg, ¬ toFun m.castSucc x tr →
      ¬ toFun m.succ x (P.concat tr msg)
  toFun_full : ∀ x tr, V x tr = true → toFun (Fin.last n) x tr

/-- If the state function is true on the full run, some challenge round moves it
from false to true: prover rounds never do, and it is false on the empty
transcript. -/
theorem KnowledgeStateFunction.exists_flip {V : Verifier P StmtIn} (S : KnowledgeStateFunction V)
    {prv : Prover P StmtIn} {x : StmtIn} {ch : P.Challenges}
    (hS : S.toFun (Fin.last n) x (prv.run x ch)) :
    ∃ i : P.ChallengeIdx, ¬ S.toFun i.1.castSucc x (prv.runTo x ch i.1 i.1.2.le) ∧
      S.toFun i.1.succ x (P.concat (prv.runTo x ch i.1 i.1.2.le) (ch i)) := by
  by_contra hne
  push Not at hne
  have hall : ∀ k (hk : k ≤ n), ¬ S.toFun ⟨k, by omega⟩ x (prv.runTo x ch k hk) := by
    intro k
    induction k with
    | zero =>
      intro hk
      exact S.toFun_empty x _
    | succ k ih =>
      intro hk
      have ih' := ih (by omega)
      cases hd : P.dir ⟨k, hk⟩ with
      | P_to_V =>
        have := S.toFun_next ⟨k, hk⟩ hd x _ (prv ⟨⟨k, hk⟩, hd⟩ x (prv.runTo x ch k (by omega))) ih'
        rwa [← Prover.runTo_succ_of_message prv x ch ⟨⟨k, hk⟩, hd⟩] at this
      | V_to_P =>
        have := hne ⟨⟨k, hk⟩, hd⟩ ih'
        rwa [← Prover.runTo_succ_of_challenge prv x ch ⟨⟨k, hk⟩, hd⟩] at this
  exact hall n le_rfl hS

/-- **Round-by-round knowledge soundness, worst case per prefix**, at the one-shot extractor
`E` and the state function `S`: at every prefix before a challenge round, the probability over
a uniform fresh challenge that the state becomes true from false while `E` fails on the prefix
is at most `ε i`. The challenge types are nonempty, so the uniform distribution exists;
`rbrKnowledgeSoundness_iff_count` is the equivalent counting form.

The extractor is an argument, never existentially quantified. CMS19 Definition 8.5 (p. 40)
asks for "a polynomial-time extractor E and state function state"; without a cost bound on
`E` the notion is vacuous for a relation whose statements have witnesses: at a statement `x`
with a witness `w₀`, the constant extractor returning `w₀` makes the event empty at `x`, so
the condition reduces to soundness at the statements without a witness. The Falcon and ML-DSA
relations are of that kind, since every public key has valid signatures. Every theorem
therefore names its extractor, and the extractor's docstring argues that it runs in polynomial
time (`Extractor`); that argument is not stated in Lean, a deviation from Definition 8.5. The
state function need not be efficient: CMS19 requires only `E` to be. -/
def rbrKnowledgeSoundness [∀ i, Fintype (P.Challenge i)]
    [∀ i, Nonempty (P.Challenge i)] (rel : Set (StmtIn × WitIn))
    (V : Verifier P StmtIn) (E : Extractor P StmtIn WitIn) (S : KnowledgeStateFunction V)
    (ε : P.ChallengeIdx → ℝ≥0) : Prop :=
  ∀ (x : StmtIn) (i : P.ChallengeIdx) (tr : P.Transcript i.1.castSucc),
    Pr[c ← P.Challenge i : (x, E i.1.castSucc x tr) ∉ rel ∧ ¬ S.toFun i.1.castSucc x tr ∧
          S.toFun i.1.succ x (P.concat tr c)] ≤ ε i

/-- **Round-by-round knowledge soundness with errors that depend on the statement** (the paper's
`def:rbr`): `rbrKnowledgeSoundness` with the error `ε x i` at the statement `x` and the challenge
round `i`. At errors that do not depend on the statement it is `rbrKnowledgeSoundness`
(`rbrKnowledgeSoundnessStmt_const`). -/
def rbrKnowledgeSoundnessStmt [∀ i, Fintype (P.Challenge i)]
    [∀ i, Nonempty (P.Challenge i)] (rel : Set (StmtIn × WitIn))
    (V : Verifier P StmtIn) (E : Extractor P StmtIn WitIn) (S : KnowledgeStateFunction V)
    (ε : StmtIn → P.ChallengeIdx → ℝ≥0) : Prop :=
  ∀ (x : StmtIn) (i : P.ChallengeIdx) (tr : P.Transcript i.1.castSucc),
    Pr[c ← P.Challenge i : (x, E i.1.castSucc x tr) ∉ rel ∧ ¬ S.toFun i.1.castSucc x tr ∧
          S.toFun i.1.succ x (P.concat tr c)] ≤ ε x i

/-- At errors that do not depend on the statement, `rbrKnowledgeSoundnessStmt` is
`rbrKnowledgeSoundness`. -/
theorem rbrKnowledgeSoundnessStmt_const [∀ i, Fintype (P.Challenge i)]
    [∀ i, Nonempty (P.Challenge i)] {rel : Set (StmtIn × WitIn)} {V : Verifier P StmtIn}
    {E : Extractor P StmtIn WitIn} {S : KnowledgeStateFunction V} {ε : P.ChallengeIdx → ℝ≥0} :
    rbrKnowledgeSoundnessStmt rel V E S (fun _ => ε) ↔ rbrKnowledgeSoundness rel V E S ε :=
  Iff.rfl

open Classical in
/-- `rbrKnowledgeSoundness` as a count: at most `ε i · |C_i|` fresh
challenges make the state true from false while `E` fails on the prefix. -/
theorem rbrKnowledgeSoundness_iff_count [∀ i, Fintype (P.Challenge i)]
    [∀ i, Nonempty (P.Challenge i)]
    {rel : Set (StmtIn × WitIn)} {V : Verifier P StmtIn} {E : Extractor P StmtIn WitIn}
    {S : KnowledgeStateFunction V} {ε : P.ChallengeIdx → ℝ≥0} :
    rbrKnowledgeSoundness rel V E S ε ↔
      ∀ (x : StmtIn) (i : P.ChallengeIdx) (tr : P.Transcript i.1.castSucc),
        ((Finset.univ.filter fun c : P.Challenge i =>
            (x, E i.1.castSucc x tr) ∉ rel ∧ ¬ S.toFun i.1.castSucc x tr ∧
              S.toFun i.1.succ x (P.concat tr c)).card : ℝ≥0) ≤
          ε i * Fintype.card (P.Challenge i) := by
  exact forall_congr' fun x => forall_congr' fun i => forall_congr' fun tr =>
    (card_le_iff_probUniform_le (P.Challenge i) _ _).symm

open Finset in
/-- A counting bound for product types. If for every tuple `f`, at most `a · |β i|`
values `c` put `Function.update f i c` into `A`, then `A` has at most
`a · |∀ j, β j|` elements. The statement is about Mathlib objects only and is a
candidate for `PQ/ToMathlib`. -/
theorem card_le_of_card_update_le {ι : Type*} [DecidableEq ι] [Fintype ι] {β : ι → Type*}
    [∀ j, Fintype (β j)] [∀ j, DecidableEq (β j)] (i : ι) {A : Finset (∀ j, β j)} {a : ℝ≥0}
    (h : ∀ f, (#{c | Function.update f i c ∈ A} : ℝ≥0) ≤ a * Fintype.card (β i)) :
    (#A : ℝ≥0) ≤ a * Fintype.card (∀ j, β j) := by
  let r : (∀ j, β j) → ∀ j : {j // j ≠ i}, β j := fun f j => f j
  rw [card_eq_sum_card_fiberwise (f := r) (t := univ) (by simp)]
  push_cast
  have hfib : ∀ g, (#{f ∈ A | r f = g} : ℝ≥0) ≤ a * Fintype.card (β i) := by
    intro g
    rcases ({f ∈ A | r f = g} : Finset _).eq_empty_or_nonempty with he | ⟨f₀, hf₀⟩
    · simp [he]
    · rw [mem_filter] at hf₀
      refine le_trans (Nat.cast_le.mpr (card_le_card_of_injOn (fun f => f i) ?_ ?_)) (h f₀)
      · intro f hf
        rw [coe_filter, Set.mem_ofPred_eq] at hf
        simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq]
        convert hf.1 using 1
        funext j
        by_cases hj : j = i
        · subst hj
          simp
        · rw [Function.update_of_ne hj]
          exact congrFun (hf₀.2.trans hf.2.symm) ⟨j, hj⟩
      · intro f hf f' hf' heq
        rw [coe_filter, Set.mem_ofPred_eq] at hf hf'
        funext j
        by_cases hj : j = i
        · subst hj
          exact heq
        · exact congrFun (hf.2.trans hf'.2.symm) ⟨j, hj⟩
  calc ∑ g, (#{f ∈ A | r f = g} : ℝ≥0) ≤ ∑ _g : (∀ j : {j // j ≠ i}, β j), a * Fintype.card (β i) :=
        sum_le_sum fun g _ => hfib g
    _ = a * Fintype.card (∀ j, β j) := by
      rw [sum_const, card_univ, Fintype.card_congr (Equiv.piSplitAt i β), Fintype.card_prod]
      push_cast
      rw [nsmul_eq_mul]
      ring

/-- **Knowledge soundness** with straight-line extractor `E` (read on the full transcript) and
error `δ`: for every statement and deterministic prover, the probability over uniform challenge
tuples that the verifier accepts while `E` fails on the full transcript is at most `δ`. The
challenge types are nonempty, so the uniform distribution exists; `knowledgeSoundness_iff_count`
is the equivalent counting form. As for `rbrKnowledgeSoundness`, the extractor is an argument,
since without a cost bound on it the notion is vacuous for relations whose statements have
witnesses. -/
def knowledgeSoundness [∀ i, Fintype (P.Challenge i)]
    [∀ i, Nonempty (P.Challenge i)] [Fintype P.ChallengeIdx]
    (rel : Set (StmtIn × WitIn)) (V : Verifier P StmtIn) (E : Extractor P StmtIn WitIn)
    (δ : ℝ≥0) : Prop :=
  open Classical in
  ∀ (x : StmtIn) (prv : Prover P StmtIn),
    Pr[ch ← P.Challenges : V x (prv.run x ch) = true ∧
      (x, E (Fin.last n) x (prv.run x ch)) ∉ rel] ≤ δ

open Classical in
/-- `knowledgeSoundness` as a count: at most `δ · |C|` challenge tuples make the
verifier accept while `E` fails. -/
theorem knowledgeSoundness_iff_count [∀ i, Fintype (P.Challenge i)]
    [∀ i, Nonempty (P.Challenge i)] [Fintype P.ChallengeIdx]
    {rel : Set (StmtIn × WitIn)} {V : Verifier P StmtIn} {E : Extractor P StmtIn WitIn}
    {δ : ℝ≥0} :
    knowledgeSoundness rel V E δ ↔
      ∀ (x : StmtIn) (prv : Prover P StmtIn),
        ((Finset.univ.filter fun ch : P.Challenges =>
            V x (prv.run x ch) = true ∧ (x, E (Fin.last n) x (prv.run x ch)) ∉ rel).card : ℝ≥0) ≤
          δ * Fintype.card P.Challenges := by
  exact forall_congr' fun x => forall_congr' fun prv =>
    (card_le_iff_probUniform_le P.Challenges _ _).symm

/-- A larger stated error preserves the same extractor and verifier. -/
theorem knowledgeSoundness.monoError [∀ i, Fintype (P.Challenge i)]
    [∀ i, Nonempty (P.Challenge i)] [Fintype P.ChallengeIdx]
    {rel : Set (StmtIn × WitIn)} {V : Verifier P StmtIn} {E : Extractor P StmtIn WitIn}
    {δ δ' : ℝ≥0} (h : knowledgeSoundness rel V E δ) (hδ : δ ≤ δ') :
    knowledgeSoundness rel V E δ' := by
  rw [knowledgeSoundness_iff_count] at h ⊢
  exact fun x prv => (h x prv).trans (mul_le_mul_of_nonneg_right hδ (by positivity))

open Classical in
/-- **Randomized provers.** A prover drawing a random tape `ρ` from a finite type
`R`, independently of the verifier's challenges, is the deterministic prover
`prv ρ` for each tape. The same extractor then fails on accepting runs for at
most a `δ` fraction of the pairs of tape and challenges: the fraction for the
randomized prover is the average over `ρ` of the deterministic fractions. -/
theorem knowledgeSoundness.randomized [∀ i, Fintype (P.Challenge i)]
    [∀ i, Nonempty (P.Challenge i)] [Fintype P.ChallengeIdx]
    {rel : Set (StmtIn × WitIn)} {V : Verifier P StmtIn} {E : Extractor P StmtIn WitIn}
    {δ : ℝ≥0} (h : knowledgeSoundness rel V E δ) (x : StmtIn) (R : Type) [Fintype R]
    (prv : R → Prover P StmtIn) :
    ((Finset.univ.filter fun rc : R × P.Challenges =>
        V x ((prv rc.1).run x rc.2) = true ∧
          (x, E (Fin.last n) x ((prv rc.1).run x rc.2)) ∉ rel).card : ℝ≥0) ≤
      δ * (Fintype.card R * Fintype.card P.Challenges) := by
  rw [knowledgeSoundness_iff_count] at h
  have hsum : ((Finset.univ.filter fun rc : R × P.Challenges =>
        V x ((prv rc.1).run x rc.2) = true ∧
          (x, E (Fin.last n) x ((prv rc.1).run x rc.2)) ∉ rel).card : ℝ≥0) =
      ∑ ρ : R, ((Finset.univ.filter fun ch : P.Challenges =>
        V x ((prv ρ).run x ch) = true ∧ (x, E (Fin.last n) x ((prv ρ).run x ch)) ∉ rel).card :
          ℝ≥0) := by
    simp only [Finset.card_filter, Nat.cast_sum, Fintype.sum_prod_type]
  rw [hsum]
  calc ∑ ρ : R, ((Finset.univ.filter fun ch : P.Challenges =>
          V x ((prv ρ).run x ch) = true ∧ (x, E (Fin.last n) x ((prv ρ).run x ch)) ∉ rel).card :
            ℝ≥0)
      ≤ ∑ _ρ : R, δ * Fintype.card P.Challenges := Finset.sum_le_sum fun ρ _ => h x (prv ρ)
    _ = δ * (Fintype.card R * Fintype.card P.Challenges) := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring

/-- **The straight-line extractor of a one-shot extractor** `E` for `rel`: on a transcript
prefix `tr` of length `m`, `E` at the shortest prefix of `tr` at which it returns a witness for
`rel`, if there is one, and `E` at `tr` otherwise. `knowledgeSoundness_of_rbr` reads it on the
full transcript.

Running time: at most `m + 1` calls of `E`, one per prefix of `tr` in increasing length
(`Fin.find`), and as many membership tests of `rel` (the instance `DecidablePred (· ∈ rel)`);
polynomial when `E` is and membership in `rel` is decidable in polynomial time (for the
proof-of-possession relations, one run of the signature verifier). The proofs use only that the
result is a witness whenever some prefix gives one (`straightLine_mem`). This running time is argued
here, not proved in Lean. -/
def Extractor.straightLine (rel : Set (StmtIn × WitIn)) [DecidablePred (· ∈ rel)]
    (E : Extractor P StmtIn WitIn) : Extractor P StmtIn WitIn where
  extract m x tr :=
    if hm : ∃ m' : Fin (n + 1), ∃ h : m' ≤ m, (x, E m' x (tr.take m' h)) ∈ rel then
      E (Fin.find _ hm) x (tr.take (Fin.find _ hm) (Fin.find_spec hm).fst)
    else E m x tr

/-- `E.straightLine rel` returns a witness whenever `E` does at some prefix. -/
theorem Extractor.straightLine_mem {rel : Set (StmtIn × WitIn)} [DecidablePred (· ∈ rel)]
    (E : Extractor P StmtIn WitIn) {m m' : Fin (n + 1)} {x : StmtIn} {tr : P.Transcript m}
    (h : m' ≤ m) (hm' : (x, E m' x (tr.take m' h)) ∈ rel) :
    (x, E.straightLine rel m x tr) ∈ rel := by
  have hex : ∃ m' : Fin (n + 1), ∃ h : m' ≤ m, (x, E m' x (tr.take m' h)) ∈ rel := ⟨m', h, hm'⟩
  change (x, (if hm : ∃ m' : Fin (n + 1), ∃ h : m' ≤ m, (x, E m' x (tr.take m' h)) ∈ rel then
      E (Fin.find _ hm) x (tr.take (Fin.find _ hm) (Fin.find_spec hm).fst) else E m x tr)) ∈ rel
  rw [dite_cond_eq_true (eq_true hex)]
  exact (Fin.find_spec hex).snd

open Classical Finset in
/-- `knowledgeSoundness_of_rbr` in counting form, over challenge types that may be
empty: the per-prefix counts of `rbrKnowledgeSoundness_iff_count` give the
count of `knowledgeSoundness_iff_count` with the summed error, at the straight-line
extractor `E.straightLine rel`. -/
theorem knowledgeSoundness_count_of_rbr_count [∀ i, Fintype (P.Challenge i)]
    [Fintype P.ChallengeIdx] {rel : Set (StmtIn × WitIn)} {V : Verifier P StmtIn}
    {ε : P.ChallengeIdx → ℝ≥0} (E : Extractor P StmtIn WitIn) (S : KnowledgeStateFunction V)
    (hE : ∀ (x : StmtIn) (i : P.ChallengeIdx) (tr : P.Transcript i.1.castSucc),
        ((Finset.univ.filter fun c : P.Challenge i =>
            (x, E i.1.castSucc x tr) ∉ rel ∧ ¬ S.toFun i.1.castSucc x tr ∧
              S.toFun i.1.succ x (P.concat tr c)).card : ℝ≥0) ≤
          ε i * Fintype.card (P.Challenge i))
    (x : StmtIn) (prv : Prover P StmtIn) :
    ((Finset.univ.filter fun ch : P.Challenges =>
        V x (prv.run x ch) = true ∧
          (x, E.straightLine rel (Fin.last n) x (prv.run x ch)) ∉ rel).card : ℝ≥0) ≤
      (∑ i, ε i) * Fintype.card P.Challenges := by
  have hE' : ∀ tr, (x, E.straightLine rel (Fin.last n) x tr) ∉ rel →
      ∀ m, (x, E m x (tr.take m (Fin.le_last m))) ∉ rel :=
    fun tr hfail m hm => hfail (E.straightLine_mem (Fin.le_last m) hm)
  let B : P.ChallengeIdx → Finset P.Challenges := fun i =>
    {ch | (x, E i.1.castSucc x (prv.runTo x ch i.1 i.1.2.le)) ∉ rel ∧
      ¬ S.toFun i.1.castSucc x (prv.runTo x ch i.1 i.1.2.le) ∧
      S.toFun i.1.succ x (P.concat (prv.runTo x ch i.1 i.1.2.le) (ch i))}
  have hsub : ({ch | V x (prv.run x ch) = true ∧
      (x, E.straightLine rel (Fin.last n) x (prv.run x ch)) ∉ rel} :
      Finset P.Challenges) ⊆ univ.biUnion B := by
    intro ch hch
    rw [mem_filter] at hch
    obtain ⟨i, hi⟩ := S.exists_flip (S.toFun_full x _ hch.2.1)
    have hfail := hE' _ hch.2.2 i.1.castSucc
    have hpre : (prv.run x ch).take i.1.castSucc (Fin.le_last _) =
        prv.runTo x ch i.1 i.1.2.le :=
      prv.take_runTo x ch le_rfl i.1.castSucc (Fin.le_last _)
    rw [hpre] at hfail
    exact mem_biUnion.mpr ⟨i, mem_univ i, mem_filter.mpr ⟨mem_univ ch, hfail, hi⟩⟩
  have hB : ∀ i, (#(B i) : ℝ≥0) ≤ ε i * Fintype.card P.Challenges := by
    intro i
    refine card_le_of_card_update_le i fun f => le_trans (Nat.cast_le.mpr (card_le_card ?_))
      (hE x i (prv.runTo x f i.1 i.1.2.le))
    intro c hc
    have hpre : prv.runTo x (Function.update f i c) i.1 i.1.2.le = prv.runTo x f i.1 i.1.2.le :=
      prv.runTo_congr x i.1.2.le fun j hj => Function.update_of_ne (by rintro rfl; omega) c f
    simp only [B, mem_filter, mem_univ, true_and, hpre, Function.update_self] at hc
    simpa only [mem_filter, mem_univ, true_and] using hc
  calc (#{ch | V x (prv.run x ch) = true ∧
          (x, E.straightLine rel (Fin.last n) x (prv.run x ch)) ∉ rel} : ℝ≥0)
      ≤ #(univ.biUnion B) := Nat.cast_le.mpr (card_le_card hsub)
    _ ≤ ∑ i, (#(B i) : ℝ≥0) := by exact_mod_cast card_biUnion_le
    _ ≤ ∑ i, ε i * Fintype.card P.Challenges := sum_le_sum fun i _ => hB i
    _ = (∑ i, ε i) * Fintype.card P.Challenges := (sum_mul ..).symm

open Classical in
/-- **Round-by-round knowledge soundness implies knowledge soundness** with the
summed error, at the straight-line extractor `E.straightLine rel`
(`knowledgeSoundness_count_of_rbr_count`). -/
theorem knowledgeSoundness_of_rbr [∀ i, Fintype (P.Challenge i)] [∀ i, Nonempty (P.Challenge i)]
    [Fintype P.ChallengeIdx] {rel : Set (StmtIn × WitIn)} {V : Verifier P StmtIn}
    {E : Extractor P StmtIn WitIn} {S : KnowledgeStateFunction V} {ε : P.ChallengeIdx → ℝ≥0}
    (h : rbrKnowledgeSoundness rel V E S ε) :
    knowledgeSoundness rel V (E.straightLine rel) (∑ i, ε i) :=
  knowledgeSoundness_iff_count.mpr
    (knowledgeSoundness_count_of_rbr_count E S (rbrKnowledgeSoundness_iff_count.mp h))

/-- A pointwise larger round error, at the same extractor and state function. -/
theorem rbrKnowledgeSoundness.monoError [∀ i, Fintype (P.Challenge i)]
    [∀ i, Nonempty (P.Challenge i)]
    {rel : Set (StmtIn × WitIn)} {V : Verifier P StmtIn} {E : Extractor P StmtIn WitIn}
    {S : KnowledgeStateFunction V} {ε δ : P.ChallengeIdx → ℝ≥0}
    (h : rbrKnowledgeSoundness rel V E S ε) (hεδ : ∀ i, ε i ≤ δ i) :
    rbrKnowledgeSoundness rel V E S δ := by
  rw [rbrKnowledgeSoundness_iff_count] at h ⊢
  exact fun x i tr => (h x i tr).trans (mul_le_mul_of_nonneg_right (hεδ i) (by positivity))

/-- A uniform per-round bound: every round's error is at most `δ`. -/
theorem rbrKnowledgeSoundness.monoError_const [∀ i, Fintype (P.Challenge i)]
    [∀ i, Nonempty (P.Challenge i)]
    {rel : Set (StmtIn × WitIn)} {V : Verifier P StmtIn} {E : Extractor P StmtIn WitIn}
    {S : KnowledgeStateFunction V} {ε : P.ChallengeIdx → ℝ≥0} {δ : ℝ≥0}
    (h : rbrKnowledgeSoundness rel V E S ε) (hεδ : ∀ i, ε i ≤ δ) :
    rbrKnowledgeSoundness rel V E S fun _ => δ :=
  h.monoError hεδ

/-! ### Full runs -/

section FullRun

variable {m : ℕ} {Q : ProtocolSpec m} {Stmt : Type}

/-- Round `r` of a full run is the last round of the run up to `r + 1`. -/
theorem Prover.run_apply (prv : Prover Q Stmt) (x : Stmt) (ch : Q.Challenges) (r : Fin m) :
    prv.run x ch r = prv.runTo x ch (r.1 + 1) r.2 ⟨r.1, by simp⟩ := by
  exact congrFun (prv.take_runTo x ch le_rfl r.succ (by simp)) ⟨r.1, by simp⟩

/-- A full run carries the challenge at every challenge round. -/
theorem Prover.run_challenge (prv : Prover Q Stmt) (x : Stmt) (ch : Q.Challenges)
    (i : Q.ChallengeIdx) : prv.run x ch i.1 = ch i := by
  rw [prv.run_apply, prv.runTo_succ_of_challenge]
  exact Q.concat_apply_last _ _

/-- The message of a prover round of a full run depends only on the challenges before it. -/
theorem Prover.run_message_congr (prv : Prover Q Stmt) (x : Stmt) {ch ch' : Q.Challenges}
    (i : Q.MessageIdx) (h : ∀ j : Q.ChallengeIdx, j.1 < i.1 → ch j = ch' j) :
    prv.run x ch i.1 = prv.run x ch' i.1 := by
  rw [prv.run_apply, prv.run_apply, prv.runTo_succ_of_message, prv.runTo_succ_of_message,
    prv.runTo_congr x i.1.2.le fun j hj => h j hj]

end FullRun

section MaxError

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- The largest per-round error `max_i ε i`, over a finite round index. -/
def maxError (ε : ι → ℝ≥0) : ℝ≥0 := Finset.univ.sup ε

theorem le_maxError (ε : ι → ℝ≥0) (i : ι) : ε i ≤ maxError ε :=
  Finset.le_sup (Finset.mem_univ i)

theorem maxError_le_iff {ε : ι → ℝ≥0} {δ : ℝ≥0} : maxError ε ≤ δ ↔ ∀ i, ε i ≤ δ := by
  simp [maxError, Finset.sup_le_iff]

theorem maxError_mono {ε δ : ι → ℝ≥0} (h : ∀ i, ε i ≤ δ i) : maxError ε ≤ maxError δ :=
  maxError_le_iff.mpr fun i => (h i).trans (le_maxError δ i)

/-- The sum of the round errors is at most the number of rounds times the largest. -/
theorem sum_le_card_mul_max (ε : ι → ℝ≥0) : ∑ i, ε i ≤ Fintype.card ι * maxError ε := by
  calc ∑ i, ε i ≤ ∑ _i : ι, maxError ε := Finset.sum_le_sum fun i _ => le_maxError ε i
    _ = Fintype.card ι * maxError ε := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- Reindexing along an equivalence of round indices keeps the maximum. -/
theorem maxError_comp_equiv (ε : κ → ℝ≥0) (e : ι ≃ κ) : maxError (ε ∘ e) = maxError ε :=
  le_antisymm (maxError_le_iff.mpr fun i => le_maxError ε (e i))
    (maxError_le_iff.mpr fun j => by simpa using le_maxError (ε ∘ e) (e.symm j))

/-- The maximum over a sum of round indices is the larger of the two maxima. -/
theorem maxError_sum_elim (ε₁ : ι → ℝ≥0) (ε₂ : κ → ℝ≥0) :
    maxError (Sum.elim ε₁ ε₂) = max (maxError ε₁) (maxError ε₂) := by
  refine le_antisymm (maxError_le_iff.mpr ?_) (max_le (maxError_le_iff.mpr fun i => ?_)
    (maxError_le_iff.mpr fun j => ?_))
  · rintro (i | j)
    · exact (le_maxError ε₁ i).trans (le_max_left _ _)
    · exact (le_maxError ε₂ j).trans (le_max_right _ _)
  · simpa using le_maxError (Sum.elim ε₁ ε₂) (.inl i)
  · simpa using le_maxError (Sum.elim ε₁ ε₂) (.inr j)

end MaxError

/-- Round-by-round knowledge soundness at error `ε` gives it at the constant
error `maxError ε`, at the same extractor and state function. -/
theorem rbrKnowledgeSoundness.toMaxError [∀ i, Fintype (P.Challenge i)]
    [∀ i, Nonempty (P.Challenge i)]
    {rel : Set (StmtIn × WitIn)} {V : Verifier P StmtIn} {E : Extractor P StmtIn WitIn}
    {S : KnowledgeStateFunction V} {ε : P.ChallengeIdx → ℝ≥0}
    (h : rbrKnowledgeSoundness rel V E S ε) : rbrKnowledgeSoundness rel V E S fun _ => maxError ε :=
  h.monoError (le_maxError ε)

end GordieHowe.IOP
