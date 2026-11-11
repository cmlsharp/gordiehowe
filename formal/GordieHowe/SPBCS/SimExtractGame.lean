-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.SPBCS.Knowledge
public import GordieHowe.Headline
public import GordieHowe.SPBCS.SimAssign
public import GordieHowe.SPBCS.SimProg
public import GordieHowe.SPBCS.Extractor
public import GordieHowe.SPBCS.Extraction.KnowledgeError
public import GordieHowe.Model.QROM.QueryBits
public import GordieHowe.Model.QROM.QueryCount
public import GordieHowe.SPBCS.Merkle.TreeProg
public import GordieHowe.Model.Quantum.Interactive.SimChallenger
public import GordieHowe.Model.Quantum.Interactive.Adaptive
public import GordieHowe.Model.Quantum.Interactive.QueryBounded

@[expose] public section

/-!
# The simulation-sound extractability game of the spBCS compiler

The objects of the weak simulation-sound extractability game (Unruh 2017, ePrint 2017/398,
Definition 14, p. 21, eq. (6), for residual-state tests that make no oracle queries) for the
spBCS compiler (`GordieHowe/SPBCS/Basic.lean`), and the classical facts about one run. The registers, the adversary's
output, the assignments in force, the queried statements, the simulator's query inputs and the
final answers are `Register`, `advOut`, `finalAss`, `queried`, `simQueryInputs` and `finalAnswer`
(below).

- `SimAssignsAtKeys`: the property of a counted simulator program that the argument uses (paper
  `def:bcs-base-game`, third condition): at every proof query and coins, it assigns only at the `xof`
  point of the coins' salt at the digest of a queried `transcript` input whose content holds the
  salt and the queried statement. The bits form of `GordieHowe.SPBCS.AssignsAtKeys`
  (`GordieHowe/SPBCS/SimAssign.lean`); `simAssignsAtKeys_of_mapQuery` derives it for a program that maps
  a plain one.
- `Wins`, `extractionProg`, `simExtractionExpansion`, `simExtGame`: with the spBCS verifier
  `Accepts` and its queries `queries`.
- `exists_input_of_xof_mem_queries`: an `xof` query of the verifier is the point at the key of
  one of its chain inputs, at the proof's salt; the chain input encodes the proof's salted
  statement.
- `cover_simExtGame`: a database consistent with a tuple of `simExtGame` extracts
  (`extracts`), is in `bad`, or has a digest collision (paper `lem:sse-cover`). A
  programmed verifier `xof` query would equate the digests of a verifier chain input (encoding the
  adversary's statement) and a simulator chain input (encoding a queried statement), which differ
  by freshness.
-/

/-!
## The registers and the classical facts about one run

The objects of the weak simulation-sound extractability game (Unruh 2017, ePrint 2017/398,
Definition 14, p. 21, eq. (6), for residual-state tests that make no oracle queries) that do not
read the verifier, and the classical facts about one run. The game (below) uses them with the
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

section

variable {ι : Type} {n : ι → ℕ} {P : (j : ι) → ProtocolSpec (n j)}
  [∀ j i, Fintype ((P j).Challenge i)] [∀ j i, DecidableEq ((P j).Challenge i)]
  [∀ j i, Nonempty ((P j).Challenge i)] {t : SPTerm ι} {Mg : Merges t} {X : Type}
  (M : SPBCS Mg P X k kN kS L e) (B : ℕ) [∀ j i, Fintype ((M.comp j).MessageWrite i)]

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
  /-- The shape of the adversary on each value. -/
  sh : Aux → AlgShape (Bits (queryBits k kN kS L)) (XOut k e) X' (M.Response B)
  /-- The interactive adversary run on each value. -/
  alg : (a : Aux) → AdaptiveIAlg (sh a) (Claim X M.NIProof)
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
  sh := 𝒜.sh
  alg := 𝒜.alg
  queries_le := 𝒜.queries_le

variable {X' : Type} [Fintype X'] [DecidableEq X'] {SC : Type} [Fintype SC] [DecidableEq SC]

/-- The composed registers of an adversary with the simulation challenger. -/
abbrev Register {ksA : KindShape (Bits (queryBits k kN kS L)) (XOut k e) X' (M.Response B)} (A : KindAlg ksA (Claim X M.NIProof))
    (Psim : NARG.Simulator (Bits (queryBits k kN kS L)) (XOut k e) X' (M.Response B) SC) (Q : ℕ) :
    Type :=
  A.CW (simExtChallenger Psim Q)

variable {M B} {ksA : KindShape (Bits (queryBits k kN kS L)) (XOut k e) X' (M.Response B)} (A : KindAlg ksA (Claim X M.NIProof))
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
  {ksA' : KindShape (Bits (queryBits k kN kS L)) (XOut k e) X' (M.Response B)} (A' : KindAlg ksA' (Claim X M.NIProof))

/-- The coins of the composite's simulator. -/
abbrev SimCoinsOf (VE : M.ViewEncoder E Qs) (S : CausalJointSimulator VE.MV Pub) (T : M.Preimages) :
    Type :=
  SaltedCoins (FiatShamirSalt kS) (M.JointSimCoins VE.toViewRead S T)

/-- The simulator's coins have decidable equality (classically). -/
noncomputable instance (VE : M.ViewEncoder E Qs) (S : CausalJointSimulator VE.MV Pub)
    (T : M.Preimages) : DecidableEq (M.SimCoinsOf Qs VE S T) := Classical.decEq _

end SimRun

end
end GordieHowe.SPBCS

namespace GordieHowe.SPBCS

open GordieHowe.QROM GordieHowe.IOP IOP.SPTerm Quantum GordieHowe.QROM
open scoped NNReal ENNReal

variable {ι : Type} {t : SPTerm ι} {Mg : Merges t} {k kN kS L e : ℕ} {n : ι → ℕ}
  {P : (j : ι) → ProtocolSpec (n j)} [∀ j i, Fintype ((P j).Challenge i)]
  [∀ j i, DecidableEq ((P j).Challenge i)] [∀ j i, Nonempty ((P j).Challenge i)] {X : Type}

section

variable (M : SPBCS Mg P X k kN kS L e) (B : ℕ) [∀ j i, Fintype ((M.comp j).MessageWrite i)]

/-! ### The simulator property -/

/-- **The counted simulator program assigns only at the keys of its chain inputs** (module
docstring): at every proof query `r` and coins `c`, under every oracle `G`, each assignment programs
the `xof` point at the salt of `c` and the digest of `G` at a queried `transcript` input whose
content holds the salt of `c` and the statement `fx r`. -/
def SimAssignsAtKeys {X' C : Type}
    (Psim : NARG.Simulator (Bits (queryBits k kN kS L)) (XOut k e) X' (M.Response B)
      (SaltedCoins (FiatShamirSalt kS) C)) (fx : X' → X) : Prop :=
  ∀ (r : X') (c : SaltedCoins (FiatShamirSalt kS) C) (G : Bits (queryBits k kN kS L) → XOut k e)
    (qa : Assignment (Bits (queryBits k kN kS L)) (XOut k e)),
    qa ∈ ((Psim.prog r c).run G).assignments →
      ∃ (bT : Bytes L) (cnt : M.MContent), Query.toBits (.transcript bT) ∈ (Psim.prog r c).trace G ∧
        M.senc.decode bT = some cnt ∧ cnt.stmt = ⟨c.salt, fx r⟩ ∧
        qa.input = Query.toBits (.xof (outEquiv k e (G (Query.toBits (.transcript bT)))).digest c.salt)

variable {M B}

/-- **A counted program that maps a plain program assigning at keys assigns at keys**: the
program `(plain r c).bind (pure ∘ map to bits)` read through `Query.toBits` and `outEquiv`, for
plain programs `plain r c` with `M.AssignsAtKeys (plain r c) ⟨c.salt, fx r⟩`. -/
theorem simAssignsAtKeys_of_mapQuery {X' C : Type}
    {Psim : NARG.Simulator (Bits (queryBits k kN kS L)) (XOut k e) X' (M.Response B)
      (SaltedCoins (FiatShamirSalt kS) C)} {fx : X' → X}
    (plain : X' → SaltedCoins (FiatShamirSalt kS) C →
      OracleProg (Query k kN kS L) (Out k e) (NARG.SimOutput (Query k kN kS L) (Out k e) (M.Response B)))
    (hprog : ∀ r c, Psim.prog r c = ((plain r c).bind fun s => .pure ⟨s.proof,
      s.assignments.map fun qa => ⟨Query.toBits qa.input, (outEquiv k e).symm qa.output⟩⟩).mapQuery
        Query.toBits (outEquiv k e))
    (hplain : ∀ r c, M.AssignsAtKeys (plain r c) ⟨c.salt, fx r⟩) : M.SimAssignsAtKeys B Psim fx := by
  intro r c G qa hqa
  rw [hprog, OracleProg.run_mapQuery, OracleProg.run_bind, OracleProg.run_pure] at hqa
  obtain ⟨qa₀, hqa₀, rfl⟩ := List.mem_map.1 hqa
  obtain ⟨bT, cnt, hT, hdec, hst, hin⟩ := hplain r c _ qa₀ hqa₀
  refine ⟨bT, cnt, ?_, hdec, hst, ?_⟩
  · rw [hprog, OracleProg.trace_mapQuery, OracleProg.trace_bind, OracleProg.trace_pure,
      List.append_nil]
    exact List.mem_map_of_mem hT
  · show Query.toBits qa₀.input = _
    rw [hin]
    rfl

/-- **Reading the proof queries through `fx` keeps the property.** -/
theorem SimAssignsAtKeys.comap {C : Type}
    {Sim : NARG.Simulator (Bits (queryBits k kN kS L)) (XOut k e) X (M.Response B)
      (SaltedCoins (FiatShamirSalt kS) C)} (h : M.SimAssignsAtKeys B Sim id) {X' : Type}
    (fx : X' → X) : M.SimAssignsAtKeys B (Sim.comap fx) fx :=
  fun r c G qa hqa => h (fx r) c G qa hqa

/-! ### Verifier queries -/

section Queries

variable (h : Query k kN kS L → Out k e) (x : X) (π : M.NIProof) {V : X → FullTr P t → Bool}
  (Q : M.IOPQueries V x)

omit [∀ j i, Fintype ((M.comp j).MessageWrite i)] in
/-- **An `xof` query of the spBCS verifier is the point at the key of one of its chain
inputs**, at the proof's salt; the chain input is well formed, holds the proof's salted statement
and is a verifier query. -/
theorem exists_input_of_xof_mem_queries {d : Digest k} {s : FiatShamirSalt kS}
    (hq : Query.xof d s ∈ M.queries x π h Q) :
    s = π.salt ∧ ∃ c : M.MContent, c.WF n (fun j => chainWF (P j)) ∧ c.stmt = M.ssOf x π ∧
      d = (h (.transcript (M.senc.encode c))).digest ∧
      Query.transcript (M.senc.encode c) ∈ M.queries x π h Q := by
  have hR : ∀ q, q ∈ (M.roundsProg x π).trace h → q ∈ M.queries x π h Q := fun q hq => by
    rw [queries_eq]
    exact List.mem_append_left _ hq
  rw [queries_eq, List.mem_append] at hq
  rcases hq with hq | hq
  swap
  · obtain ⟨τ, -, hτ⟩ := List.mem_flatMap.1 hq
    exact absurd hτ (M.opening.not_xof_mem_trace h d s)
  obtain ⟨o, ho⟩ := (M.mem_roundsProg_iff x π h).1 hq
  cases o with
  | sink s' => simp [honestTrace] at ho
  | leaf p =>
    simp only [honestTrace, leafProg] at ho
    rw [ComponentModel.mem_trace_chainProg_iff] at ho
    obtain ⟨j, hj, hq' | hq'⟩ := ho
    · cases hq'
    · obtain ⟨rfl, rfl⟩ := Query.xof.inj hq'
      refine ⟨rfl, _, wf_roundContent_chains p ((M.comp p.label).chainWF_chainWith _ _ _ _ j _)
        (by rw [ComponentModel.length_chainWith]; exact hj), rfl, rfl, hR _ ?_⟩
      exact (M.mem_roundsProg_input x π h p j hj).1

end Queries

/-! ### The game objects -/

variable {X' : Type} [Fintype X'] [DecidableEq X'] {SC : Type} [Fintype SC] [DecidableEq SC]

variable {ksA : KindShape (Bits (queryBits k kN kS L)) (XOut k e) X' (M.Response B)} (A : KindAlg ksA (Claim X M.NIProof))
  (Psim : NARG.Simulator (Bits (queryBits k kN kS L)) (XOut k e) X' (M.Response B) SC) (Q : ℕ)
  {V : X → FullTr P t → Bool} (Qs : ∀ x, M.IOPQueries V x)

/-- **The adversary wins the game of simulation soundness**: a statement no proof query was, with a
proof the spBCS verifier accepts under the final oracle. -/
def Wins (fx : X' → X) (H : Bits (queryBits k kN kS L) → XOut k e) (v : M.Register B A Psim Q) :
    Prop :=
  (∀ x' ∈ SPBCS.queried A Psim Q v, fx x' ≠ (SPBCS.advOut A Psim Q v).stmt) ∧
    M.Accepts (chainOracle (H.reprogram (SPBCS.finalAss A Psim Q v)))
      (SPBCS.advOut A Psim Q v).stmt (SPBCS.advOut A Psim Q v).proof
      (Qs (SPBCS.advOut A Psim Q v).stmt)

/-- **The extraction queries**: the spBCS verifier's queries under the final oracle, then the
simulator's query inputs. -/
noncomputable def extractionProg (v : M.Register B A Psim Q) :
    GordieHowe.OracleProg (Bits (queryBits k kN kS L)) (Out k e) (List (Out k e)) :=
  (OracleProg.translate Query.toBits
      (fun q y => SPBCS.finalAnswer A Psim Q v (Query.toBits q) y)
      (M.queryProg (SPBCS.advOut A Psim Q v).stmt (SPBCS.advOut A Psim Q v).proof
        (Qs (SPBCS.advOut A Psim Q v).stmt))).bind fun _ =>
    OracleProg.queryAll (SPBCS.simQueryInputs A Psim Q v)

/-- **The expansion for extraction**: `extractionProg`, padded with `padQuery`. -/
noncomputable def simExtractionExpansion :
    Expansion (Bits (queryBits k kN kS L)) (Out k e) (M.Register B A Psim Q) :=
  OracleProg.toExpansion (extractionProg A Psim Q Qs) (SPBCS.padQuery (kS := kS))

/-- **The base game of the expanded tuples** with `K` queries: a fresh statement; an oracle under
which the spBCS verifier accepts, each of its queries in the tuple with that answer as its
final answer; and each assignment the `xof` point of a salt at the digest of the answer to a
`transcript` query of the tuple whose merge content holds that salt and a queried
statement. -/
def simExtGame (fx : X' → X) (K : ℕ) :
    GordieHowe.QROM.BaseGame (Bits (queryBits k kN kS L)) (Out k e) (M.Register B A Psim Q) K :=
  {o | (∀ x' ∈ SPBCS.queried A Psim Q o.out,
      fx x' ≠ (SPBCS.advOut A Psim Q o.out).stmt) ∧
    (∃ h, M.Accepts h (SPBCS.advOut A Psim Q o.out).stmt
        (SPBCS.advOut A Psim Q o.out).proof (Qs (SPBCS.advOut A Psim Q o.out).stmt) ∧
      ∀ q ∈ M.queries (SPBCS.advOut A Psim Q o.out).stmt
          (SPBCS.advOut A Psim Q o.out).proof h (Qs (SPBCS.advOut A Psim Q o.out).stmt),
        ∃ i, o.queries i = Query.toBits q ∧
          SPBCS.finalAnswer A Psim Q o.out (o.queries i) (o.answers i) = h q) ∧
    ∀ qa ∈ SPBCS.finalAss A Psim Q o.out, ∃ (i : Fin K) (bT : Bytes L)
      (σ : FiatShamirSalt kS) (c : M.MContent) (x' : X'),
      o.queries i = Query.toBits (.transcript bT) ∧ M.senc.decode bT = some c ∧
      c.stmt = ⟨σ, fx x'⟩ ∧ x' ∈ SPBCS.queried A Psim Q o.out ∧
      qa.input = Query.toBits (.xof (o.answers i).digest σ)}

/-! ### One run -/

section Run

variable {Qs}

variable (Qs) in
/-- **The extraction queries**: the spBCS verifier's queries under the final oracle, then the
simulator's queries read from the registers. -/
theorem trace_extProg (H : Bits (queryBits k kN kS L) → XOut k e) (v : M.Register B A Psim Q) :
    (extractionProg A Psim Q Qs v).trace (fun a => outEquiv k e (H a)) =
      (M.queries (SPBCS.advOut A Psim Q v).stmt (SPBCS.advOut A Psim Q v).proof
        (chainOracle (H.reprogram (SPBCS.finalAss A Psim Q v)))
        (Qs (SPBCS.advOut A Psim Q v).stmt)).map Query.toBits ++
      SPBCS.simQueryInputs A Psim Q v := by
  rw [extractionProg, OracleProg.trace_bind, OracleProg.trace_translate,
    OracleProg.trace_queryAll]
  have hf : (fun a => SPBCS.finalAnswer A Psim Q v (Query.toBits a)
      (outEquiv k e (H (Query.toBits a)))) =
      chainOracle (H.reprogram (SPBCS.finalAss A Psim Q v)) :=
    funext (SPBCS.finalAnswer_eq A Psim Q H v)
  rw [hf]
  rfl

variable (fx : X' → X)

/-- A non-`xof` query is never programmed in a tuple of `simExtGame`. -/
theorem lastAssign_eq_none_of_not_xof {K : ℕ}
    {o : GordieHowe.QROM.BaseGame.Tuple (Bits (queryBits k kN kS L)) (Out k e) (M.Register B A Psim Q) K}
    (ho : o ∈ simExtGame A Psim Q Qs fx K) (q : Query k kN kS L) (hq : ∀ d σ, q ≠ .xof d σ) :
    lastAssign (SPBCS.assBytes A Psim Q o.out) (Query.toBits q) = none := by
  rw [SPBCS.assBytes, lastAssign_map, lastAssign_eq_none fun qa hqa heq => ?_]
  · rfl
  obtain ⟨i, bT, σ, c, x', -, -, -, -, h⟩ := ho.2.2 qa hqa
  rw [h] at heq
  exact hq _ _ (Query.toBits.injective heq).symm

/-- **Without digest collisions, every verifier query of a tuple of `simExtGame` is read from
the database with its base answer**: a programmed verifier `xof` query would equate the digest of
a verifier chain input's answer with the digest of a simulator chain input's answer; both inputs
are in the database and hold different statements by freshness. -/
theorem lookup_of_mem_queries_of_no_collision {K : ℕ}
    {o : GordieHowe.QROM.BaseGame.Tuple (Bits (queryBits k kN kS L)) (Out k e) (M.Register B A Psim Q) K}
    (ho : o ∈ simExtGame A Psim Q Qs fx K) {D : GordieHowe.QROM.DB (Bits (queryBits k kN kS L)) (Out k e)}
    (hD : o.InDB D) (hcol : D.restrict Query.toBits ∉ digestCollision)
    {h : Query k kN kS L → Out k e}
    (hcov : ∀ q ∈ M.queries (SPBCS.advOut A Psim Q o.out).stmt
        (SPBCS.advOut A Psim Q o.out).proof h (Qs (SPBCS.advOut A Psim Q o.out).stmt),
      ∃ i, o.queries i = Query.toBits q ∧
        SPBCS.finalAnswer A Psim Q o.out (o.queries i) (o.answers i) = h q) :
    ∀ q ∈ M.queries (SPBCS.advOut A Psim Q o.out).stmt
        (SPBCS.advOut A Psim Q o.out).proof h (Qs (SPBCS.advOut A Psim Q o.out).stmt),
      (D.restrict Query.toBits).lookup q = some (h q) := by
  have hnone := lastAssign_eq_none_of_not_xof A Psim Q fx ho
  obtain ⟨hfresh, -, hstruct⟩ := ho
  set x := (SPBCS.advOut A Psim Q o.out).stmt
  set π := (SPBCS.advOut A Psim Q o.out).proof
  intro q hq
  have hunprogrammed : lastAssign (SPBCS.assBytes A Psim Q o.out) (Query.toBits q) = none := by
    rw [SPBCS.assBytes, lastAssign_map, lastAssign_eq_none fun qa hqa heq => ?_]
    · rfl
    obtain ⟨i, bT, σ, c, x', hi, hdec, hst, hx', hqa⟩ := hstruct qa hqa
    rw [hqa] at heq
    have hqx := Query.toBits.injective heq
    subst hqx
    obtain ⟨-, cV, hwfV, hstV, hd, hT⟩ := exists_input_of_xof_mem_queries h x π (Qs x) hq
    obtain ⟨i', hi'1, hi'2⟩ := hcov _ hT
    rw [SPBCS.finalAnswer, hi'1, hnone _ (fun d σ h => by cases h)] at hi'2
    simp only [Option.getD_none] at hi'2
    apply hcol
    refine ⟨Query.transcript bT, ?_, Query.transcript (M.senc.encode cV), ?_, ?_, ?_⟩
    · rw [GordieHowe.QROM.DB.mem_restrict, GordieHowe.QROM.DB.mem_iff_lookup, ← hi]
      exact ⟨_, hD i⟩
    · rw [GordieHowe.QROM.DB.mem_restrict, GordieHowe.QROM.DB.mem_iff_lookup, ← hi'1]
      exact ⟨_, hD i'⟩
    · intro heq
      obtain rfl := Query.transcript.inj heq
      rw [M.senc.decode_encode _ hwfV] at hdec
      obtain rfl := Option.some_inj.1 hdec
      exact hfresh x' hx' (congrArg SaltedStatement.stmt (hst.symm.trans hstV))
    · rw [GordieHowe.QROM.DB.lookup_restrict, GordieHowe.QROM.DB.lookup_restrict, ← hi, ← hi'1, hD i, hD i']
      simp only [Option.map_some, Option.some_inj]
      rw [hi'2]
      exact hd
  obtain ⟨i, hi1, hi2⟩ := hcov q hq
  rw [GordieHowe.QROM.DB.lookup_restrict, ← hi1, hD i, ← hi2, SPBCS.finalAnswer, hi1, hunprogrammed]
  rfl

variable {Wit : Type} {rel : Set (X × Wit)} {E : CausalExtractor P t X Wit}
  (St : CausalStateFn P t X) {ε : ChIdx P t → ℝ≥0}

/-- **A database consistent with a tuple of `simExtGame` extracts, is in `bad`, or has a digest
collision.** -/
@[headline]
theorem cover_simExtGame [DecidableEq X] (hrbr : CausalRBRKnowledgeSound rel V E St ε)
    {K : ℕ}
    {o : GordieHowe.QROM.BaseGame.Tuple (Bits (queryBits k kN kS L)) (Out k e) (M.Register B A Psim Q) K}
    (ho : o ∈ simExtGame A Psim Q Qs fx K) {D : GordieHowe.QROM.DB (Bits (queryBits k kN kS L)) (Out k e)}
    (hD : o.InDB D) :
    D.restrict Query.toBits ∈ M.extracts rel E (SPBCS.advOut A Psim Q o.out).stmt ∨
      D.restrict Query.toBits ∈ M.bad rel E St ∪ digestCollision := by
  by_cases hcol : D.restrict Query.toBits ∈ digestCollision
  · exact Or.inr (Or.inr hcol)
  obtain ⟨h, hv, hcov⟩ := ho.2.1
  have hQ := lookup_of_mem_queries_of_no_collision A Psim Q fx ho hD hcol hcov
  rcases mem_of_verify rel E St hrbr hv (D := D.restrict Query.toBits) hQ with hc | hE | hb
  · exact Or.inr (Or.inr hc)
  · exact Or.inl hE
  · exact Or.inr (Or.inl hb)

end Run

/-! ### The simulator's assignments in a run -/

section SimRun

variable (fx : X' → X)
  {ksA' : KindShape (Bits (queryBits k kN kS L)) (XOut k e) X' (M.Response B)} (A' : KindAlg ksA' (Claim X M.NIProof))
  {C : Type} [Fintype C] [DecidableEq (SaltedCoins (FiatShamirSalt kS) C)]
  {Psim' : NARG.Simulator (Bits (queryBits k kN kS L)) (XOut k e) X' (M.Response B)
    (SaltedCoins (FiatShamirSalt kS) C)}

omit [∀ j i, Nonempty ((P j).Challenge i)] in
/-- **The structure of the assignments in force**: each was made by the program of a logged
proof query numbered below `Q`, programs the `xof` point of that proof query's salt at the digest of the
oracle in force at a `transcript` input the program queried, whose merge content holds the
salt and the queried statement. -/
theorem ass_structure (hA : M.SimAssignsAtKeys B Psim' fx)
    (H : Bits (queryBits k kN kS L) → XOut k e) (c : Fin Q → SaltedCoins (FiatShamirSalt kS) C)
    (lg : LogReg X' A'.slots) (J : ℕ) {qa : Assignment (Bits (queryBits k kN kS L)) (XOut k e)}
    (hqa : qa ∈ ((simExtChallenger Psim' Q).stateAfter H c (requestsBefore lg J)).ass) :
    ∃ (j : Fin A'.slots) (r : X') (hQ : (requestsBefore lg j).length < Q) (bT : Bytes L)
      (cont : M.MContent), (j : ℕ) < J ∧ lg j = some r ∧
      Query.toBits (.transcript bT) ∈ (Psim'.prog r (c ⟨_, hQ⟩)).trace
        ((simExtChallenger Psim' Q).oracleAfter H c (requestsBefore lg j)) ∧
      M.senc.decode bT = some cont ∧ cont.stmt = ⟨(c ⟨_, hQ⟩).1, fx r⟩ ∧
      qa.input = Query.toBits (.xof (outEquiv k e
        ((simExtChallenger Psim' Q).oracleAfter H c (requestsBefore lg j)
          (Query.toBits (.transcript bT)))).digest (c ⟨_, hQ⟩).1) := by
  obtain ⟨j, r, hj, hr, hQ, hmem⟩ := (simExtChallenger Psim' Q).mem_ass_stateAfter H c lg J qa hqa
  have hQ' : (requestsBefore lg j).length < Q := hQ
  rw [progAfter_simExtChallenger Psim' Q H c _ r hQ', OracleProg.run_bind] at hmem
  obtain ⟨bT, cont, hT, hdec, hst, hqa1⟩ := hA r (c ⟨_, hQ'⟩) _ qa hmem
  exact ⟨j, r, hQ', bT, cont, hj, hr, hT, hdec, hst, hqa1⟩

omit [∀ j i, Nonempty ((P j).Challenge i)] in
/-- **The oracle in force answers `transcript` queries as the base oracle.** -/
theorem oracleAfter_transcript (hA : M.SimAssignsAtKeys B Psim' fx)
    (H : Bits (queryBits k kN kS L) → XOut k e) (c : Fin Q → SaltedCoins (FiatShamirSalt kS) C)
    (lg : LogReg X' A'.slots) (J : ℕ) (bT : Bytes L) :
    (simExtChallenger Psim' Q).oracleAfter H c (requestsBefore lg J)
      (Query.toBits (.transcript bT)) = H (Query.toBits (.transcript bT)) := by
  refine reprogram_apply_of_forall_ne H fun qa hqa heq => ?_
  obtain ⟨j, r, hQ, bT', cont, _, _, _, _, _, h⟩ := ass_structure Q fx A' hA H c lg J hqa
  rw [h] at heq
  cases Query.toBits.injective heq

/-- **A win, expanded by the extraction queries, is in the base game** `simExtGame` with
`kq + Q · q` queries, on registers consistent with the base oracle. Hypotheses: `hk`, a nonzero
digest length; `hkq`, accepting runs make at most `kq` verifier queries; `hA`, the simulator
program assigns only at the keys of its chain inputs. -/
theorem expand_mem_simExtGame {kq : ℕ}
    (hkq : M.QueriesAtMost Qs kq)
    (hA : M.SimAssignsAtKeys B Psim' fx)
    {H : Bits (queryBits k kN kS L) → XOut k e} {v : M.Register B A' Psim' Q}
    (hv : A'.Consistent (simExtChallenger Psim' Q) H v) (hw : Wins A' Psim' Q Qs fx H v) :
    (simExtractionExpansion A' Psim' Q Qs).expand (fun a => outEquiv k e (H a)) v ∈
      simExtGame A' Psim' Q Qs fx (kq + Q * Psim'.q) := by
  set h := chainOracle (H.reprogram (SPBCS.finalAss A' Psim' Q v))
  have htr := trace_extProg A' Psim' Q Qs H v
  have hlen : ((extractionProg A' Psim' Q Qs v).trace (fun a => outEquiv k e (H a))).length ≤
      kq + Q * Psim'.q := by
    rw [htr, List.length_append, List.length_map]
    exact Nat.add_le_add (hkq _ h _ hw.2) (SPBCS.simQueryInputs_length_le A' Psim' Q v)
  have hmem : ∀ y ∈ (extractionProg A' Psim' Q Qs v).trace (fun a => outEquiv k e (H a)),
      ∃ i : Fin (kq + Q * Psim'.q),
        ((simExtractionExpansion A' Psim' Q Qs).expand (fun a => outEquiv k e (H a)) v).queries i = y ∧
        ((simExtractionExpansion A' Psim' Q Qs).expand (fun a => outEquiv k e (H a)) v).answers i =
          outEquiv k e (H y) :=
    fun y hy => OracleProg.mem_expand_toExpansion _ _ _ v hlen hy
  refine ⟨hw.1, ⟨h, hw.2, fun q hq => ?_⟩, fun qa hqa => ?_⟩
  · obtain ⟨i, hi1, hi2⟩ := hmem (Query.toBits q)
      (by rw [htr]; exact List.mem_append_left _ (List.mem_map_of_mem hq))
    refine ⟨i, hi1, ?_⟩
    rw [hi1, hi2]
    exact SPBCS.finalAnswer_eq A' Psim' Q H v q
  · change qa ∈ SPBCS.finalAss A' Psim' Q v at hqa
    rw [SPBCS.finalAss_of_consistent A' Psim' Q hv] at hqa
    obtain ⟨j, r, hQ, bT, cont, -, hr, hT, hdec, hst, hqa1⟩ :=
      ass_structure Q fx A' hA H v.chal.coins v.chal.logs A'.slots hqa
    obtain ⟨i, hi1, hi2⟩ := hmem _ (by
      rw [htr]
      exact List.mem_append_right _ (SPBCS.mem_simQueryInputs A' Psim' Q hv hr hQ hT))
    refine ⟨i, bT, _, cont, r, hi1, hdec, hst, SPBCS.mem_queried A' Psim' Q hv hr hQ, ?_⟩
    rw [hqa1, hi2, oracleAfter_transcript Q fx A' hA H v.chal.coins v.chal.logs j bT]

end SimRun

end

end GordieHowe.SPBCS
