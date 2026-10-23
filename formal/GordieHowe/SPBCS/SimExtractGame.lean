-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.SPBCS.Knowledge
public import GordieHowe.SPBCS.SimAssign
public import GordieHowe.SPBCS.FullPast.SimExtractGame

@[expose] public section

/-!
# The simulation-sound extractability game of the spBCS compiler

The objects of the weak simulation-sound extractability game (Unruh 2017, ePrint 2017/398,
Definition 14, p. 21, eq. (6), for residual-state tests that make no oracle queries) for the
spBCS compiler (`GordieHowe/SPBCS/Basic.lean`), and the classical facts about one run. The registers, the adversary's
output, the assignments in force, the queried statements, the simulator's query inputs and the
final answers are those of the compiler over the term (`GordieHowe.SPBCS.Base.Register`, `advOut`,
`finalAss`, `queried`, `simQueryInputs`, `finalAnswer`); what changes is the verifier.

- `SimAssignsAtKeys`: the property of a counted simulator program that the argument uses (paper
  `def:bcs-base-game`, third condition): at every proof query and coins, it assigns only at the `xof`
  point of the coins' salt at the digest of a queried `transcript` input whose content holds the
  salt and the queried statement. The bits form of `GordieHowe.SPBCS.AssignsAtKeys`
  (`GordieHowe/SPBCS/SimAssign.lean`); `simAssignsAtKeys_of_mapQuery` derives it for a program that maps
  a plain one.
- `Wins`, `extractionProg`, `simExtractionExpansion`, `simExtGame`: as for the compiler over
  the term, with the spBCS verifier `Accepts` and its queries `queries`.
- `exists_input_of_xof_mem_queries`: an `xof` query of the verifier is the point at the key of
  one of its chain inputs, at the proof's salt; the chain input encodes the proof's salted
  statement.
- `cover_simExtGame`: a database consistent with a tuple of `simExtGame` extracts through the
  translation (`extracts`), is in `bad`, or has a digest collision (paper `lem:sse-cover`). A
  programmed verifier `xof` query would equate the digests of a verifier chain input (encoding the
  adversary's statement) and a simulator chain input (encoding a queried statement), which differ
  by freshness.
-/

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

variable (A : KindAlg (Bits (queryBits k kN kS L)) (XOut k e) X' (M.Response B)
    (Claim X M.NIProof))
  (Psim : NARG.Simulator (Bits (queryBits k kN kS L)) (XOut k e) X' (M.Response B) SC) (Q : ℕ)
  {V : X → FullTr P t → Bool} (Qs : ∀ x, M.IOPQueries V x)

/-- **The adversary wins the game of simulation soundness**: a statement no proof query was, with a
proof the spBCS verifier accepts under the final oracle. -/
def Wins (fx : X' → X) (H : Bits (queryBits k kN kS L) → XOut k e) (v : M.Register B A Psim Q) :
    Prop :=
  (∀ x' ∈ Base.queried A Psim Q v, fx x' ≠ (Base.advOut A Psim Q v).stmt) ∧
    M.Accepts (chainOracle (H.reprogram (Base.finalAss A Psim Q v)))
      (Base.advOut A Psim Q v).stmt (Base.advOut A Psim Q v).proof
      (Qs (Base.advOut A Psim Q v).stmt)

/-- **The extraction queries**: the spBCS verifier's queries under the final oracle, then the
simulator's query inputs. -/
noncomputable def extractionProg (v : M.Register B A Psim Q) :
    GordieHowe.OracleProg (Bits (queryBits k kN kS L)) (Out k e) (List (Out k e)) :=
  (OracleProg.translate Query.toBits
      (fun q y => Base.finalAnswer A Psim Q v (Query.toBits q) y)
      (M.queryProg (Base.advOut A Psim Q v).stmt (Base.advOut A Psim Q v).proof
        (Qs (Base.advOut A Psim Q v).stmt))).bind fun _ =>
    OracleProg.queryAll (Base.simQueryInputs A Psim Q v)

/-- **The expansion for extraction**: `extractionProg`, padded with `padQuery`. -/
noncomputable def simExtractionExpansion :
    Expansion (Bits (queryBits k kN kS L)) (Out k e) (M.Register B A Psim Q) :=
  OracleProg.toExpansion (extractionProg A Psim Q Qs) (Base.padQuery (kS := kS))

/-- **The base game of the expanded tuples** with `K` queries: a fresh statement; an oracle under
which the spBCS verifier accepts, each of its queries in the tuple with that answer as its
final answer; and each assignment the `xof` point of a salt at the digest of the answer to a
`transcript` query of the tuple whose merge content holds that salt and a queried
statement. -/
def simExtGame (fx : X' → X) (K : ℕ) :
    GordieHowe.QROM.BaseGame (Bits (queryBits k kN kS L)) (Out k e) (M.Register B A Psim Q) K :=
  {o | (∀ x' ∈ Base.queried A Psim Q o.out,
      fx x' ≠ (Base.advOut A Psim Q o.out).stmt) ∧
    (∃ h, M.Accepts h (Base.advOut A Psim Q o.out).stmt
        (Base.advOut A Psim Q o.out).proof (Qs (Base.advOut A Psim Q o.out).stmt) ∧
      ∀ q ∈ M.queries (Base.advOut A Psim Q o.out).stmt
          (Base.advOut A Psim Q o.out).proof h (Qs (Base.advOut A Psim Q o.out).stmt),
        ∃ i, o.queries i = Query.toBits q ∧
          Base.finalAnswer A Psim Q o.out (o.queries i) (o.answers i) = h q) ∧
    ∀ qa ∈ Base.finalAss A Psim Q o.out, ∃ (i : Fin K) (bT : Bytes L)
      (σ : FiatShamirSalt kS) (c : M.MContent) (x' : X'),
      o.queries i = Query.toBits (.transcript bT) ∧ M.senc.decode bT = some c ∧
      c.stmt = ⟨σ, fx x'⟩ ∧ x' ∈ Base.queried A Psim Q o.out ∧
      qa.input = Query.toBits (.xof (o.answers i).digest σ)}


/-! ### One run -/

section Run

variable {Qs}

variable (Qs) in
/-- **The extraction queries**: the spBCS verifier's queries under the final oracle, then the
simulator's queries read from the registers. -/
theorem trace_extProg (H : Bits (queryBits k kN kS L) → XOut k e) (v : M.Register B A Psim Q) :
    (extractionProg A Psim Q Qs v).trace (fun a => outEquiv k e (H a)) =
      (M.queries (Base.advOut A Psim Q v).stmt (Base.advOut A Psim Q v).proof
        (chainOracle (H.reprogram (Base.finalAss A Psim Q v)))
        (Qs (Base.advOut A Psim Q v).stmt)).map Query.toBits ++
      Base.simQueryInputs A Psim Q v := by
  rw [extractionProg, OracleProg.trace_bind, OracleProg.trace_translate,
    OracleProg.trace_queryAll]
  have hf : (fun a => Base.finalAnswer A Psim Q v (Query.toBits a)
      (outEquiv k e (H (Query.toBits a)))) =
      chainOracle (H.reprogram (Base.finalAss A Psim Q v)) :=
    funext (Base.finalAnswer_eq A Psim Q H v)
  rw [hf]
  rfl

variable (fx : X' → X)

/-- A non-`xof` query is never programmed in a tuple of `simExtGame`. -/
theorem lastAssign_eq_none_of_not_xof {K : ℕ}
    {o : GordieHowe.QROM.BaseGame.Tuple (Bits (queryBits k kN kS L)) (Out k e) (M.Register B A Psim Q) K}
    (ho : o ∈ simExtGame A Psim Q Qs fx K) (q : Query k kN kS L) (hq : ∀ d σ, q ≠ .xof d σ) :
    lastAssign (Base.assBytes A Psim Q o.out) (Query.toBits q) = none := by
  rw [Base.assBytes, lastAssign_map, lastAssign_eq_none fun qa hqa heq => ?_]
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
    (hcov : ∀ q ∈ M.queries (Base.advOut A Psim Q o.out).stmt
        (Base.advOut A Psim Q o.out).proof h (Qs (Base.advOut A Psim Q o.out).stmt),
      ∃ i, o.queries i = Query.toBits q ∧
        Base.finalAnswer A Psim Q o.out (o.queries i) (o.answers i) = h q) :
    ∀ q ∈ M.queries (Base.advOut A Psim Q o.out).stmt
        (Base.advOut A Psim Q o.out).proof h (Qs (Base.advOut A Psim Q o.out).stmt),
      (D.restrict Query.toBits).lookup q = some (h q) := by
  have hnone := lastAssign_eq_none_of_not_xof A Psim Q fx ho
  obtain ⟨hfresh, -, hstruct⟩ := ho
  set x := (Base.advOut A Psim Q o.out).stmt
  set π := (Base.advOut A Psim Q o.out).proof
  intro q hq
  have hunprogrammed : lastAssign (Base.assBytes A Psim Q o.out) (Query.toBits q) = none := by
    rw [Base.assBytes, lastAssign_map, lastAssign_eq_none fun qa hqa heq => ?_]
    · rfl
    obtain ⟨i, bT, σ, c, x', hi, hdec, hst, hx', hqa⟩ := hstruct qa hqa
    rw [hqa] at heq
    have hqx := Query.toBits.injective heq
    subst hqx
    obtain ⟨-, cV, hwfV, hstV, hd, hT⟩ := exists_input_of_xof_mem_queries h x π (Qs x) hq
    obtain ⟨i', hi'1, hi'2⟩ := hcov _ hT
    rw [Base.finalAnswer, hi'1, hnone _ (fun d σ h => by cases h)] at hi'2
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
  rw [GordieHowe.QROM.DB.lookup_restrict, ← hi1, hD i, ← hi2, Base.finalAnswer, hi1, hunprogrammed]
  rfl

variable {Wit : Type} {rel : Set (X × Wit)} {E : CausalExtractor P t X Wit}
  (St : CausalStateFn P t X) {ε : ChIdx P t → ℝ≥0}

/-- **A database consistent with a tuple of `simExtGame` extracts through the translation, is in
`bad`, or has a digest collision.** -/
theorem cover_simExtGame [DecidableEq X] (hrbr : CausalRBRKnowledgeSound rel V E St ε)
    {K : ℕ}
    {o : GordieHowe.QROM.BaseGame.Tuple (Bits (queryBits k kN kS L)) (Out k e) (M.Register B A Psim Q) K}
    (ho : o ∈ simExtGame A Psim Q Qs fx K) {D : GordieHowe.QROM.DB (Bits (queryBits k kN kS L)) (Out k e)}
    (hD : o.InDB D) :
    D.restrict Query.toBits ∈ M.extracts rel E (Base.advOut A Psim Q o.out).stmt ∨
      D.restrict Query.toBits ∈ M.bad rel E St ∪ digestCollision := by
  by_cases hcol : D.restrict Query.toBits ∈ digestCollision
  · exact Or.inr (Or.inr hcol)
  obtain ⟨h, hv, hcov⟩ := ho.2.1
  have hQ := lookup_of_mem_queries_of_no_collision A Psim Q fx ho hD hcol hcov
  rcases mem_of_verify rel E St hrbr hv (D := D.restrict Query.toBits) hQ with hc | hE | hb | hc
  · exact Or.inr (Or.inr hc)
  · exact Or.inl hE
  · exact Or.inr (Or.inl hb)
  · exact absurd hc (trans_notMem_digestCollision hcol)

end Run

/-! ### The simulator's assignments in a run -/

section SimRun

variable (fx : X' → X)
  (A' : KindAlg (Bits (queryBits k kN kS L)) (XOut k e) X' (M.Response B) (Claim X M.NIProof))
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
    (hkq : ∀ x h π, M.Accepts h x π (Qs x) → (M.queries x π h (Qs x)).length ≤ kq)
    (hA : M.SimAssignsAtKeys B Psim' fx)
    {H : Bits (queryBits k kN kS L) → XOut k e} {v : M.Register B A' Psim' Q}
    (hv : A'.Consistent (simExtChallenger Psim' Q) H v) (hw : Wins A' Psim' Q Qs fx H v) :
    (simExtractionExpansion A' Psim' Q Qs).expand (fun a => outEquiv k e (H a)) v ∈
      simExtGame A' Psim' Q Qs fx (kq + Q * Psim'.q) := by
  set h := chainOracle (H.reprogram (Base.finalAss A' Psim' Q v))
  have htr := trace_extProg A' Psim' Q Qs H v
  have hlen : ((extractionProg A' Psim' Q Qs v).trace (fun a => outEquiv k e (H a))).length ≤
      kq + Q * Psim'.q := by
    rw [htr, List.length_append, List.length_map]
    exact Nat.add_le_add (hkq _ h _ hw.2) (Base.simQueryInputs_length_le A' Psim' Q v)
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
    exact Base.finalAnswer_eq A' Psim' Q H v q
  · change qa ∈ Base.finalAss A' Psim' Q v at hqa
    rw [Base.finalAss_of_consistent A' Psim' Q hv] at hqa
    obtain ⟨j, r, hQ, bT, cont, -, hr, hT, hdec, hst, hqa1⟩ :=
      ass_structure Q fx A' hA H v.chal.coins v.chal.logs A'.slots hqa
    obtain ⟨i, hi1, hi2⟩ := hmem _ (by
      rw [htr]
      exact List.mem_append_right _ (Base.mem_simQueryInputs A' Psim' Q hv hr hQ hT))
    refine ⟨i, bT, _, cont, r, hi1, hdec, hst, Base.mem_queried A' Psim' Q hv hr hQ, ?_⟩
    rw [hqa1, hi2, oracleAfter_transcript Q fx A' hA H v.chal.coins v.chal.logs j bT]

end SimRun

end

end GordieHowe.SPBCS
