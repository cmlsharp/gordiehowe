-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.SPBCS.FullPast.SimProg
public import GordieHowe.SPBCS.FullPast.Verifier
public import GordieHowe.SPBCS.Extraction.KnowledgeError
public import GordieHowe.Model.QROM.QueryBits
public import GordieHowe.Model.QROM.QueryCount
public import GordieHowe.SPBCS.Merkle.TreeProg
public import GordieHowe.Model.Quantum.Interactive.SimChallenger
public import GordieHowe.Model.Quantum.Interactive.Adaptive
public import GordieHowe.Model.Quantum.Interactive.QueryBounded

@[expose] public section

/-!
# The simulation-sound extractability game of the series–parallel base model

The objects of the weak simulation-sound extractability game (Unruh 2017, ePrint 2017/398,
Definition 14, p. 21, eq. (6), for residual-state tests that make no oracle queries) at the
series–parallel base model (`GordieHowe.SPBCS.FullPast`, `GordieHowe/SPBCS/FullPast/Model.lean`), and the classical
facts about one run. The spBCS compiler's game (`GordieHowe/SPBCS/SimExtractGame.lean`) uses them with the
spBCS verifier.

- `SimExtractionAdversary`: an adaptive interactive adversary with proof queries in `X'`;
  `QBSimExtractionAdversary`: the query-bounded adversaries (`Quantum.QueryBoundedAdversary`),
  with `QBSimExtractionAdversary.toSimExtraction`.
- `Register`, `advOut`, `advWorkspace`, `finalAss`, `queried`, `simQueryInputs`, `assBytes`,
  `finalAnswer`, `padQuery`: the composed registers with the simulation challenger and what is
  read from them.
- `stateAt_of_consistent`, `finalAss_of_consistent`, `queried_of_consistent`, `mem_queried`,
  `simQueryInputs_length_le`, `mem_simQueryInputs`, `finalAnswer_eq`: the facts about one run on
  consistent registers.
- `SimCoinsOf`: the coins of the composite's simulator.
-/

namespace GordieHowe.SPBCS

open GordieHowe.QROM GordieHowe.IOP IOP.SPTerm Quantum GordieHowe.QROM
open scoped NNReal ENNReal

variable {k kN kS L e : ℕ}

namespace Base

variable {ι : Type} {n : ι → ℕ} {P : (j : ι) → ProtocolSpec (n j)}
  [∀ j i, Fintype ((P j).Challenge i)] [∀ j i, DecidableEq ((P j).Challenge i)]
  [∀ j i, Nonempty ((P j).Challenge i)] {t : SPTerm ι} {X : Type}
  (M : Base P t X k kN kS L e) (B : ℕ) [∀ j i, Fintype ((M.comp j).MessageWrite i)]

/-! ### The game objects -/

/-- **An adversary of the simulation-sound extractability game**: auxiliary input, then an
interactive adversary of the model with run-time kinds with proof queries in the finite type `X'`,
replies the simulator's proofs, and output a statement and a proof; at most `t` queries of its own
on every branch. -/
structure SimExtractionAdversary (X' : Type) [Fintype X'] [DecidableEq X'] (tq Q : ℕ) where
  /-- The values of the auxiliary input. -/
  Aux : Type
  /-- The distribution of the auxiliary input, independent of the oracle. -/
  aux : PMF Aux
  /-- The interactive adversary run on each value. -/
  alg : Aux → AdaptiveIAlg (Bits (queryBits k kN kS L)) (XOut k e) X' (M.Response B)
    (Claim X M.NIProof)
  /-- At most `tq` queries of its own on every branch. -/
  queries_le : ∀ a, (alg a).width * ((alg a).budget + (alg a).post) ≤ tq

/-- **The query-bounded adversaries of the simulation-extraction game** of the composite with
proof queries in `X'` (`Quantum.QueryBoundedAdversary`, the paper's `(t, Q)`-adversaries). -/
abbrev QBSimExtractionAdversary (X' : Type) [Fintype X'] [DecidableEq X'] (tq : ℕ) : Type 1 :=
  QueryBoundedAdversary (Bits (queryBits k kN kS L)) (XOut k e) X' (M.Response B)
    (Claim X M.NIProof) tq

variable {M B} in
/-- **A query-bounded adversary as an adversary of the simulation-extraction game** answered on
`Q` proof queries (proof-internal): the same auxiliary input, algorithms and query bound. -/
def QBSimExtractionAdversary.toSimExtraction {X' : Type} [Fintype X'] [DecidableEq X'] {tq : ℕ}
    (Q : ℕ) (𝒜 : M.QBSimExtractionAdversary B X' tq) :
    M.SimExtractionAdversary B X' tq Q where
  Aux := 𝒜.Aux
  aux := 𝒜.aux
  alg := 𝒜.alg
  queries_le := 𝒜.queries_le

variable {X' : Type} [Fintype X'] [DecidableEq X'] {SC : Type} [Fintype SC] [DecidableEq SC]

/-- The composed registers of an adversary with the simulation challenger. -/
abbrev Register (A : KindAlg (Bits (queryBits k kN kS L)) (XOut k e) X' (M.Response B)
      (Claim X M.NIProof))
    (Psim : NARG.Simulator (Bits (queryBits k kN kS L)) (XOut k e) X' (M.Response B) SC) (Q : ℕ) :
    Type :=
  A.CW (simExtChallenger Psim Q)

variable {M B} (A : KindAlg (Bits (queryBits k kN kS L)) (XOut k e) X' (M.Response B)
    (Claim X M.NIProof))
  (Psim : NARG.Simulator (Bits (queryBits k kN kS L)) (XOut k e) X' (M.Response B) SC) (Q : ℕ)

/-- The adversary's output read from the composed registers. -/
def advOut (v : M.Register B A Psim Q) : Claim X M.NIProof := A.out v.adv.workspace

/-- The adversary's workspace read from the composed registers. -/
noncomputable def advWorkspace (v : M.Register B A Psim Q) : A.W := v.adv.workspace

/-- The assignment list in force after the last slot. -/
noncomputable def finalAss (v : M.Register B A Psim Q) :
    List (Assignment (Bits (queryBits k kN kS L)) (XOut k e)) :=
  A.postAss _ v.chal

/-- The statements sent to the simulator. -/
noncomputable def queried (v : M.Register B A Psim Q) : List X' :=
  (A.stateAt (simExtChallenger Psim Q) v.chal A.slots).history.map HistoryEntry.request

variable {V : X → FullTr P t → Bool} (Qs : ∀ x, M.IOPQueries V x)

/-- The query inputs of the simulator's programs for the first `Q` proof queries. -/
noncomputable def simQueryInputs (v : M.Register B A Psim Q) : List (Bits (queryBits k kN kS L)) :=
  (List.finRange A.slots).flatMap fun j =>
    if (v.chal.logs j).isSome ∧ (requestsBefore v.chal.logs j).length < Q then
      List.ofFn fun i : Fin (simExtChallenger Psim Q).q => (v.chal.queries j i).1
    else []

/-- The final assignment list with its answers as bytes. -/
noncomputable def assBytes (v : M.Register B A Psim Q) :
    List (Assignment (Bits (queryBits k kN kS L)) (Out k e)) :=
  (finalAss A Psim Q v).map (Assignment.mapOutput (outEquiv k e))

/-- The answer of the final oracle at `q` from the base oracle's answer `y`. -/
noncomputable def finalAnswer (v : M.Register B A Psim Q) (q : Bits (queryBits k kN kS L))
    (y : Out k e) : Out k e :=
  (lastAssign (assBytes A Psim Q v) q).getD y

/-- The padding query of the expansion. -/
def padQuery : Bits (queryBits k kN kS L) := Query.toBits (.node (fun _ => 0) fun _ => 0)

/-! ### One run -/

section Run

variable {Qs}

omit [∀ j i, Nonempty ((P j).Challenge i)] in
theorem stateAt_of_consistent {H : Bits (queryBits k kN kS L) → XOut k e} {v : M.Register B A Psim Q}
    (hv : A.Consistent (simExtChallenger Psim Q) H v) :
    A.stateAt (simExtChallenger Psim Q) v.chal A.slots =
      ⟨((simExtChallenger Psim Q).stateAfter H v.chal.coins (requestsBefore v.chal.logs A.slots)).hist,
        ((simExtChallenger Psim Q).stateAfter H v.chal.coins
          (requestsBefore v.chal.logs A.slots)).ass⟩ := by
  obtain ⟨d, lg, chal, c⟩ := v
  simp only [KindAlg.Consistent] at hv
  subst hv
  exact A.regState_eq (simExtChallenger Psim Q) H c lg (J := A.slots) A.slots le_rfl

omit [∀ j i, Nonempty ((P j).Challenge i)] in
theorem finalAss_of_consistent {H : Bits (queryBits k kN kS L) → XOut k e} {v : M.Register B A Psim Q}
    (hv : A.Consistent (simExtChallenger Psim Q) H v) :
    finalAss A Psim Q v =
      ((simExtChallenger Psim Q).stateAfter H v.chal.coins (requestsBefore v.chal.logs A.slots)).ass := by
  rw [finalAss, KindAlg.postAss]
  exact congrArg ChallengerRecord.assignments (stateAt_of_consistent A Psim Q hv)

omit [∀ j i, Nonempty ((P j).Challenge i)] in
theorem queried_of_consistent {H : Bits (queryBits k kN kS L) → XOut k e} {v : M.Register B A Psim Q}
    (hv : A.Consistent (simExtChallenger Psim Q) H v) :
    queried A Psim Q v = (requestsBefore v.chal.logs A.slots).take Q := by
  rw [queried, stateAt_of_consistent A Psim Q hv]
  exact (simExtChallenger Psim Q).map_request_hist_stateAfter H v.chal.coins _

omit [∀ j i, Nonempty ((P j).Challenge i)] in
/-- A proof query of a slot numbered below `Q` was sent to the simulator. -/
theorem mem_queried {H : Bits (queryBits k kN kS L) → XOut k e} {v : M.Register B A Psim Q}
    (hv : A.Consistent (simExtChallenger Psim Q) H v) {j : Fin A.slots} {r : X'}
    (hr : v.chal.logs j = some r) (hQ : (requestsBefore v.chal.logs j).length < Q) :
    r ∈ queried A Psim Q v := by
  rw [queried_of_consistent A Psim Q hv]
  obtain ⟨tt, ht⟩ := requestsBefore_prefix v.chal.logs (show (j : ℕ) + 1 ≤ A.slots from j.2)
  rw [requestsBefore_succ_of_some v.chal.logs j hr] at ht
  rw [← ht, List.take_append, List.take_of_length_le (by simp; omega)]
  simp

omit [∀ j i, Nonempty ((P j).Challenge i)] in
theorem simQueryInputs_length_le (v : M.Register B A Psim Q) :
    (simQueryInputs A Psim Q v).length ≤ Q * Psim.q :=
  length_flatMap_logged_le v.chal.logs _ fun _ => List.length_ofFn

omit [∀ j i, Nonempty ((P j).Challenge i)] in
/-- **The queries of the program of a logged proof query numbered below `Q` are among the simulator's
queries read from consistent registers.** -/
theorem mem_simQueryInputs {H : Bits (queryBits k kN kS L) → XOut k e} {v : M.Register B A Psim Q}
    (hv : A.Consistent (simExtChallenger Psim Q) H v) {j : Fin A.slots} {r : X'}
    (hr : v.chal.logs j = some r) (hQ : (requestsBefore v.chal.logs j).length < Q)
    {Tq : Bits (queryBits k kN kS L)}
    (hT : Tq ∈ (Psim.prog r (v.chal.coins ⟨_, hQ⟩)).trace
      ((simExtChallenger Psim Q).oracleAfter H v.chal.coins (requestsBefore v.chal.logs j))) :
    Tq ∈ simQueryInputs A Psim Q v := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hT
  have hq : i < Psim.q := lt_of_lt_of_le hi (Psim.prog_queries _ _ _)
  have hent : (v.chal.queries j ⟨i, hq⟩).1 =
      ((Psim.prog r (v.chal.coins ⟨_, hQ⟩)).trace
        ((simExtChallenger Psim Q).oracleAfter H v.chal.coins (requestsBefore v.chal.logs j)))[i] := by
    have hv' := congrFun (congrFun hv j) ⟨i, hq⟩
    rw [hv']
    simp only [KindAlg.garFill, j.2, if_true, hr, KindAlg.ansEntry]
    have htr : ((simExtChallenger Psim Q).progAfter H v.chal.coins (requestsBefore v.chal.logs j) r).trace
        ((simExtChallenger Psim Q).oracleAfter H v.chal.coins (requestsBefore v.chal.logs j)) =
        (Psim.prog r (v.chal.coins ⟨_, hQ⟩)).trace
          ((simExtChallenger Psim Q).oracleAfter H v.chal.coins (requestsBefore v.chal.logs j)) := by
      erw [progAfter_simExtChallenger Psim Q H v.chal.coins _ r hQ, OracleProg.trace_bind]
      simp
    have hQ' : (requestsBefore v.chal.logs j).length < (simExtChallenger Psim Q).Q := hQ
    rw [if_pos hQ', dif_pos (htr ▸ hi)]
    simp only [htr]
  have hmem : (v.chal.queries j ⟨i, hq⟩).1 ∈ (if (v.chal.logs j).isSome ∧
      (requestsBefore v.chal.logs j).length < Q
      then List.ofFn fun i : Fin (simExtChallenger Psim Q).q => (v.chal.queries j i).1 else []) := by
    rw [if_pos ⟨by simp [hr], hQ⟩]
    exact List.mem_ofFn.2 ⟨⟨i, hq⟩, rfl⟩
  rw [← hent]
  exact List.mem_flatMap.2 ⟨j, List.mem_finRange j, hmem⟩

omit [∀ j i, Nonempty ((P j).Challenge i)] in
/-- **The final answer read from the base oracle's answer is the final oracle's answer.** -/
theorem finalAnswer_eq (H : Bits (queryBits k kN kS L) → XOut k e) (v : M.Register B A Psim Q)
    (q : Query k kN kS L) :
    finalAnswer A Psim Q v (Query.toBits q) (outEquiv k e (H (Query.toBits q))) =
      chainOracle (H.reprogram (finalAss A Psim Q v)) q := by
  rw [finalAnswer, assBytes, lastAssign_map, chainOracle, reprogram_apply_eq_lastAssign]
  cases lastAssign (finalAss A Psim Q v) (Query.toBits q) <;> rfl

end Run

/-! ### The simulator's assignments in a run -/

section SimRun

variable {E : (j : ι) → (M.comp j).Encoder} {VE : M.ViewEncoder E Qs} {Pub : Type}
  {pub : X → Pub} {S : CausalJointSimulator VE.MV Pub} {T : M.Preimages} (fx : X' → X)
  (A' : KindAlg (Bits (queryBits k kN kS L)) (XOut k e) X' (M.Response B) (Claim X M.NIProof))

/-- The coins of the composite's simulator. -/
abbrev SimCoinsOf (VE : M.ViewEncoder E Qs) (S : CausalJointSimulator VE.MV Pub) (T : M.Preimages) :
    Type :=
  SaltedCoins (FiatShamirSalt kS) (M.JointSimCoins VE.toViewRead S T)

/-- The simulator's coins have decidable equality (classically). -/
noncomputable instance (VE : M.ViewEncoder E Qs) (S : CausalJointSimulator VE.MV Pub)
    (T : M.Preimages) : DecidableEq (M.SimCoinsOf Qs VE S T) := Classical.decEq _

end SimRun

end Base
end GordieHowe.SPBCS
