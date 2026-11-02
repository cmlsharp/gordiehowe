-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.SPBCS.SimExtractGame
public import GordieHowe.SPBCS.KnowledgeROM
public import GordieHowe.Model.ROM.SimExtract

@[expose] public section

/-!
# Simulation-sound extractability of the spBCS compiler in the classical random-oracle model

Weak simulation-sound extractability with straight-line extraction (paper `thm:bcs-se`(2); Unruh
2017, ePrint 2017/398, Definition 14, p. 21, eq. (6), weak variant), against query-bounded
classical adversaries (`ROM.QueryBoundedAdversary`), for the spBCS compiler. The game is the
one of `GordieHowe/SPBCS/SEProg.lean` (the composed run `SEProg.compose` of the adversary's
tree with the simulation oracle, then the verifier's queries under the final oracle) with a
classical simulator program `sp` that assigns only at the keys of its chain inputs
(`GordieHowe.SPBCS.AssignsAtKeys`) and the spBCS verifier.

**The extractor** reads the game's query table: the database extractor `dbExtract` on
`gameLog`. It is straight-line and makes no queries.

**The theorem** (`simulation_sound_extractability_rom_joint`, CY24 Definition 5.1.1 joint form):
`Pr_h[win ∧ the extractor fails] ≤ simExtractionErrorROM kq (max_c ε c) q tq Q`, the classical
spBCS knowledge error `knowledgeErrorROM k (tq + Q q + kq) c nJ κ`, `q` the simulator's
queries per proof query: the paper's `errse^C(t, Q)`. A win whose table the extractor fails on puts the
table in `bad ∪ P_col`: every assignment programs the `xof` point of a recorded simulator chain
input holding a queried statement (`assignInv_compose`), so a programmed verifier `xof` query
would collide two recorded chain inputs whose statements differ by freshness; without it the
verifier's run is read from the table and the spBCS cover applies (`mem_of_verify`).
`GordieHowe.SPBCS.weak_online_simulation_extractability_rom_basic` averages it over the coins of a query-bounded classical
adversary; `GordieHowe.SPBCS.weak_online_simulation_extractability_rom`
(`GordieHowe/SPBCS/SimExtractROMJoint.lean`) derives from it the full `def:bcs-se` in the ROM.
-/

namespace GordieHowe.SPBCS

open GordieHowe.QROM GordieHowe.IOP IOP.SPTerm Quantum GordieHowe.QROM
open scoped NNReal ENNReal BigOperators

variable {ι : Type} {t : SPTerm ι} {Mg : Merges t} {k kN kS L e : ℕ} {n : ι → ℕ}
  {P : (j : ι) → ProtocolSpec (n j)} [∀ j i, Fintype ((P j).Challenge i)]
  [∀ j i, DecidableEq ((P j).Challenge i)] [∀ j i, Nonempty ((P j).Challenge i)] {X : Type}

section

variable (M : SPBCS Mg P X k kN kS L e) (B : ℕ) [∀ j i, Fintype ((M.comp j).MessageWrite i)]

/-! ### The game -/

variable {V : X → FullTr P t → Bool} (Qs : ∀ x, M.IOPQueries V x) {X' : Type} (fx : X' → X)
  {C : Type}
  (sp : X' → SaltedCoins (FiatShamirSalt kS) C →
    OracleProg (Query k kN kS L) (Out k e) (NARG.SimOutput (Query k kN kS L) (Out k e) (M.Response B)))

variable {Q : ℕ} (c : Fin Q → SaltedCoins (FiatShamirSalt kS) C) (𝒜 : M.ROMAdversary B X')

/-- **The game as a classical program**: the composed run, then the spBCS verifier's queries
on the output under the final oracle. -/
noncomputable def romGame : OracleProg (Query k kN kS L) (Out k e)
    (SEProg.Result (Query k kN kS L) (Out k e) X' (Claim X M.NIProof)) :=
  (SEProg.compose (sp) c 𝒜 [] 0 []).bind fun res =>
    (SEProg.inForce res.ass (M.queryProg res.out.stmt res.out.proof (Qs res.out.stmt))).bind
      fun _ => .pure res

/-- The run's result. -/
def romResult (h : Query k kN kS L → Out k e) :
    SEProg.Result (Query k kN kS L) (Out k e) X' (Claim X M.NIProof) :=
  (SEProg.compose (sp) c 𝒜 [] 0 []).run h

/-- **The adversary wins**: a statement none of its proof queries was, with a proof the spBCS
verifier accepts under the final oracle. -/
def WinsROM (h : Query k kN kS L → Out k e) : Prop :=
  (∀ x' ∈ (M.romResult B sp c 𝒜 h).queried,
      fx x' ≠ (M.romResult B sp c 𝒜 h).out.stmt) ∧
    M.Accepts (h.reprogram (M.romResult B sp c 𝒜 h).ass)
      (M.romResult B sp c 𝒜 h).out.stmt
      (M.romResult B sp c 𝒜 h).out.proof
      (Qs (M.romResult B sp c 𝒜 h).out.stmt)

/-- **The game's query table**: the base answers at the game's queries, padded to `K`. -/
noncomputable def gameLog (K : ℕ) (h : Query k kN kS L → Out k e) : DB (Query k kN kS L) (Out k e) :=
  ((SPBCS.baseAlg (k := k) (kN := kN) (kS := kS) (L := L) (e := e)).append
    (OracleProg.toExpansion (fun _ : Unit => M.romGame B Qs sp c 𝒜)
      (.xof (fun _ => 0) fun _ => 0)) K).log h (0 + K)

/-! ### The assignments of a run -/

/-- **The invariant of the assignments in force**: each programs the `xof` point of a salt at the
base digest of a recorded `transcript` input whose merge content holds that salt and a
queried statement. -/
def AssignInv (h : Query k kN kS L → Out k e) (Tr : List (Query k kN kS L)) (qs : List X')
    (ass : List (Assignment (Query k kN kS L) (Out k e))) : Prop :=
  ∀ qa ∈ ass, ∃ (bT : Bytes L) (σ : FiatShamirSalt kS) (cont : M.MContent) (r : X'), r ∈ qs ∧
    Query.transcript bT ∈ Tr ∧ M.senc.decode bT = some cont ∧ cont.stmt = ⟨σ, fx r⟩ ∧
      qa.input = .xof (h (.transcript bT)).digest σ

variable {M B Qs fx sp}

omit [∀ j i, Nonempty ((P j).Challenge i)] [∀ j i, Fintype ((M.comp j).MessageWrite i)] in
theorem AssignInv.mono {h : Query k kN kS L → Out k e} {Tr Tr' : List (Query k kN kS L)}
    {qs qs' : List X'} {ass : List (Assignment (Query k kN kS L) (Out k e))}
    (hi : M.AssignInv fx h Tr qs ass) (hT : Tr ⊆ Tr') (hq : qs ⊆ qs') :
    M.AssignInv fx h Tr' qs' ass := fun qa hqa => by
  obtain ⟨bT, σ, cont, r, hr, hb, hd, hs, he⟩ := hi qa hqa
  exact ⟨bT, σ, cont, r, hq hr, hT hb, hd, hs, he⟩

omit [∀ j i, Nonempty ((P j).Challenge i)] [∀ j i, Fintype ((M.comp j).MessageWrite i)] in
/-- Under the invariant the oracle in force answers `transcript` queries as the base oracle. -/
theorem AssignInv.reprogram_transcript {h : Query k kN kS L → Out k e}
    {Tr : List (Query k kN kS L)} {qs : List X'} {ass : List (Assignment (Query k kN kS L) (Out k e))}
    (hi : M.AssignInv fx h Tr qs ass) (b : Bytes L) :
    h.reprogram ass (.transcript b) = h (.transcript b) :=
  reprogram_apply_of_forall_ne h fun qa hqa heq => by
    obtain ⟨_bT, _σ, _cont, _r, _hr, _hb, _hd, _hs, he⟩ := hi qa hqa
    rw [he] at heq
    cases heq

omit [∀ j i, Nonempty ((P j).Challenge i)] [∀ j i, Fintype ((M.comp j).MessageWrite i)] in
variable (M B fx sp) in
/-- **The assignments of a composed run keep the invariant.** -/
theorem assignInv_compose (hA : ∀ r a, M.AssignsAtKeys (sp r a) ⟨a.salt, fx r⟩) {Q : ℕ} (c : Fin Q → SaltedCoins (FiatShamirSalt kS) C)
    (h : Query k kN kS L → Out k e) : ∀ (p : M.ROMAdversary B X') ass i qs Tr,
    M.AssignInv fx h Tr qs ass →
    M.AssignInv fx h (Tr ++ (SEProg.compose (sp) c p ass i qs).trace h)
      ((SEProg.compose (sp) c p ass i qs).run h).queried
      ((SEProg.compose (sp) c p ass i qs).run h).ass
  | .done o, ass, i, qs, Tr, hi => by
    simpa [SEProg.compose] using hi
  | .query a kk, ass, i, qs, Tr, hi => by
    simp only [SEProg.compose, OracleProg.trace_query, OracleProg.run_query]
    have := assignInv_compose hA c h (kk ((lastAssign ass a).getD (h a))) ass i qs (Tr ++ [a])
      (hi.mono (List.subset_append_left _ _) (List.Subset.refl _))
    simpa [List.append_assoc] using this
  | .request r kk, ass, i, qs, Tr, hi => by
    unfold SEProg.compose
    split_ifs with hiQ
    · rw [OracleProg.trace_bind, OracleProg.run_bind]
      set so := (SEProg.inForce ass (sp r (c ⟨i, hiQ⟩))).run h
      set Tr₁ := Tr ++ (SEProg.inForce ass (sp r (c ⟨i, hiQ⟩))).trace h
      have hnew : M.AssignInv fx h Tr₁ (qs ++ [r]) (ass ++ so.assignments) := by
        intro qa hqa
        rcases List.mem_append.1 hqa with hqa | hqa
        · exact hi.mono (List.subset_append_left _ _) (List.subset_append_left _ _) qa hqa
        · rw [show so = (sp r (c ⟨i, hiQ⟩)).run (h.reprogram ass) from
            SEProg.run_inForce _ _ _] at hqa
          obtain ⟨bT, cont, hT, hdec, hst, hin⟩ := hA r (c ⟨i, hiQ⟩) _ _ hqa
          refine ⟨bT, _, cont, r, List.mem_append_right _ (List.mem_singleton_self _),
            List.mem_append_right _ ?_, hdec, hst, ?_⟩
          · rw [SEProg.trace_inForce]
            exact hT
          · rw [hin, hi.reprogram_transcript]
      have := assignInv_compose hA c h (kk (some so.proof)) (ass ++ so.assignments) (i + 1)
        (qs ++ [r]) Tr₁ hnew
      simpa [Tr₁, List.append_assoc] using this
    · exact assignInv_compose hA c h (kk none) ass i qs Tr hi

/-! ### The game's trace and query table -/

omit [∀ j i, Fintype ((M.comp j).MessageWrite i)] in
theorem trace_romGame {Q : ℕ} (c : Fin Q → SaltedCoins (FiatShamirSalt kS) C) (𝒜 : M.ROMAdversary B X')
    (h : Query k kN kS L → Out k e) :
    (M.romGame B Qs sp c 𝒜).trace h =
      (SEProg.compose (sp) c 𝒜 [] 0 []).trace h ++
        M.queries (M.romResult B sp c 𝒜 h).out.stmt
          (M.romResult B sp c 𝒜 h).out.proof
          (h.reprogram (M.romResult B sp c 𝒜 h).ass)
          (Qs (M.romResult B sp c 𝒜 h).out.stmt) := by
  rw [romGame, OracleProg.trace_bind, OracleProg.trace_bind, SEProg.trace_inForce]
  simp only [OracleProg.trace_pure, List.append_nil]
  rfl

omit [∀ j i, Fintype ((M.comp j).MessageWrite i)] in
/-- **The query table records every query of the game with its base answer**, when the padding
`K` covers the game's queries. -/
theorem lookup_gameLog {Q : ℕ} (c : Fin Q → SaltedCoins (FiatShamirSalt kS) C) (𝒜 : M.ROMAdversary B X')
    {K : ℕ} {h : Query k kN kS L → Out k e}
    (hK : ((M.romGame B Qs sp c 𝒜).trace h).length ≤ K) {q : Query k kN kS L}
    (hq : q ∈ (M.romGame B Qs sp c 𝒜).trace h) :
    (M.gameLog B Qs sp c 𝒜 K h).lookup q = some (h q) := by
  refine ROM.Alg.lookup_log_append_of_mem _ _ K h ?_
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hq
  have := OracleProg.queries_toExpansion h (fun _ : Unit => M.romGame B Qs sp c 𝒜)
    (.xof (fun _ => 0) fun _ => 0) () (⟨j, by omega⟩ : Fin K)
  rw [List.getElem?_eq_getElem hj, Option.getD_some] at this
  rw [← this]
  exact List.getElem_mem _

/-! ### Simulation-sound extractability -/

variable {Wit : Type} {rel : Set (X × Wit)} {E : CausalExtractor P t X Wit}
  {St : CausalStateFn P t X} {ε : ChIdx P t → ℝ≥0}

variable (M) in
/-- **The classical simulation-sound extractability error of the spBCS compiler**: the
classical spBCS knowledge error at `tq + Q q + kq` queries (the adversary's, the simulator's
on `Q` proof queries of `q` queries each, and the verifier's). -/
noncomputable def simExtractionErrorROM (kq : ℕ) (κ : ℝ≥0) (q tq Q : ℕ) : ℝ≥0∞ :=
  knowledgeErrorROM k (tq + Q * q + kq) M.senc.digestsPerInput Mg.nJ κ

omit [∀ j i, Fintype ((M.comp j).MessageWrite i)] in
/-- **A win whose query table the extractor fails on puts the table in `bad ∪ P_col`.** -/
theorem gameLog_mem_bad [DecidableEq X] (hA : ∀ r a, M.AssignsAtKeys (sp r a) ⟨a.salt, fx r⟩)
    (hrbr : CausalRBRKnowledgeSound rel V E St ε) {Q : ℕ} (c : Fin Q → SaltedCoins (FiatShamirSalt kS) C)
    (𝒜 : M.ROMAdversary B X') {K : ℕ} {h : Query k kN kS L → Out k e}
    (hK : ((M.romGame B Qs sp c 𝒜).trace h).length ≤ K)
    (hw : M.WinsROM B Qs fx sp c 𝒜 h)
    (hn : M.gameLog B Qs sp c 𝒜 K h ∉
      M.extracts rel E (M.romResult B sp c 𝒜 h).out.stmt) :
    M.gameLog B Qs sp c 𝒜 K h ∈ M.bad rel E St ∪ digestCollision := by
  set res := M.romResult B sp c 𝒜 h
  set D := M.gameLog B Qs sp c 𝒜 K h
  set x := res.out.stmt
  set π := res.out.proof
  set Of := h.reprogram res.ass
  by_cases hcol : D ∈ digestCollision
  · exact Or.inr hcol
  have htr := trace_romGame (B := B) (Qs := Qs) (sp := sp) c 𝒜 h
  have hinv := M.assignInv_compose B fx sp hA c h 𝒜 [] 0 [] []
    (fun _ h => absurd h (List.not_mem_nil))
  simp only [List.nil_append] at hinv
  have hlookup : ∀ q ∈ (M.romGame B Qs sp c 𝒜).trace h, D.lookup q = some (h q) :=
    fun q hq => lookup_gameLog c 𝒜 hK hq
  have hver : ∀ q ∈ M.queries x π Of (Qs x), q ∈ (M.romGame B Qs sp c 𝒜).trace h :=
    fun q hq => by rw [htr]; exact List.mem_append_right _ hq
  have hcomp : ∀ q ∈ (SEProg.compose (sp) c 𝒜 [] 0 []).trace h,
      q ∈ (M.romGame B Qs sp c 𝒜).trace h :=
    fun q hq => by rw [htr]; exact List.mem_append_left _ hq
  -- no verifier query is programmed
  have hunprog : ∀ q ∈ M.queries x π Of (Qs x), ∀ qa ∈ res.ass, qa.input ≠ q := by
    intro q hq qa hqa heq
    obtain ⟨bT, σ, cont, r, hr, hT, hdec, hst, hin⟩ := hinv qa hqa
    rw [hin] at heq
    subst heq
    obtain ⟨-, cV, hwfV, hstV, hd, hV⟩ := exists_input_of_xof_mem_queries Of x π (Qs x) hq
    have hVO : Of (.transcript (M.senc.encode cV)) = h (.transcript (M.senc.encode cV)) :=
      hinv.reprogram_transcript _
    apply hcol
    refine ⟨Query.transcript bT, ?_, _, DB.mem_iff_lookup.2 ⟨_, hlookup _ (hver _ hV)⟩, ?_, ?_⟩
    · exact DB.mem_iff_lookup.2 ⟨_, hlookup _ (hcomp _ hT)⟩
    · intro he
      obtain rfl := Query.transcript.inj he
      rw [M.senc.decode_encode _ hwfV] at hdec
      obtain rfl := Option.some_inj.1 hdec
      exact hw.1 r hr (congrArg SaltedStatement.stmt (hst.symm.trans hstV))
    · rw [hlookup _ (hcomp _ hT), hlookup _ (hver _ hV)]
      simp only [Option.map_some, Option.some_inj]
      rw [← hVO]
      exact hd
  have hQ : RecordsQueries D Of x π (Qs x) := fun q hq => by
    show D.lookup q = some (Of q)
    rw [hlookup _ (hver _ hq), show Of q = h q from reprogram_apply_of_forall_ne h (hunprog q hq)]
  rcases mem_of_verify rel E St hrbr hw.2 hQ with hc | hE | hb
  · exact Or.inr hc
  · exact absurd hE hn
  · exact Or.inl hb

omit [∀ j i, Fintype ((M.comp j).MessageWrite i)] in
/-- **Simulation-sound extractability of the spBCS compiler in the classical random-oracle
model, joint form** (CY24 Definition 5.1.1 with Unruh 2017 Definition 14, weak variant): for a
composite causally round-by-round knowledge sound at `E` with errors `ε` (`hrbr`), query phases
whose accepting runs make at most `kq` spBCS verifier queries (`hkq`), digests of at least one
byte, every classical adversary tree with at most `tq` queries of its own (`h𝒜`) and all simulator
coins `c`, over a uniform base oracle: the probability that the adversary outputs a statement none
of its proof queries was, with a proof the spBCS verifier accepts under the final oracle, and the
straight-line extractor (`dbExtract` on the game's query table) returns no witness for the
statement, is at most `simExtractionErrorROM kq (max_c ε c) q tq Q`, with
`q` the queries of one run of `Sim`. -/
theorem simulation_sound_extractability_rom_joint [DecidableEq X]
    (hA : ∀ r a, M.AssignsAtKeys (sp r a) ⟨a.salt, fx r⟩) {q : ℕ}
    (hqs : ∀ r a G, ((sp r a).trace G).length ≤ q)
    (hrbr : CausalRBRKnowledgeSound rel V E St ε) {kq : ℕ}
    (hkq : ∀ x h π, M.Accepts h x π (Qs x) → (M.queries x π h (Qs x)).length ≤ kq) {Q tq : ℕ}
    (c : Fin Q → SaltedCoins (FiatShamirSalt kS) C) (𝒜 : M.ROMAdversary B X') (h𝒜 : 𝒜.QueryBound tq) :
    Pr[h ← (Query k kN kS L → Out k e) : M.WinsROM B Qs fx sp c 𝒜 h ∧
        M.gameLog B Qs sp c 𝒜
          (tq + Q * q + kq) h ∉
          M.extracts rel E (M.romResult B sp c 𝒜 h).out.stmt] ≤
      M.simExtractionErrorROM kq (maxError ε)
        q tq Q := by
  set K := tq + Q * q + kq
  have hlen : ∀ h, M.WinsROM B Qs fx sp c 𝒜 h →
      ((M.romGame B Qs sp c 𝒜).trace h).length ≤ K := fun h hw => by
    rw [trace_romGame, List.length_append]
    have h1 := SEProg.length_trace_compose _ c hqs 𝒜 tq h𝒜 [] 0 [] h (Nat.zero_le _)
    have h2 := hkq _ _ _ hw.2
    simp only [Nat.sub_zero] at h1
    omega
  have hle := M.prob_log_bad_union_le rel E St hrbr
    ((SPBCS.baseAlg (k := k) (kN := kN) (kS := kS) (L := L) (e := e)).append
      (OracleProg.toExpansion (fun _ : Unit => M.romGame B Qs sp c 𝒜)
        (.xof (fun _ => 0) fun _ => 0)) K)
  refine le_trans (QROM.probUniform_mono fun h hh => ?_)
    (hle.trans_eq (by rw [Nat.zero_add, simExtractionErrorROM]))
  have := gameLog_mem_bad hA hrbr c 𝒜 (hlen h hh.1) hh.1 hh.2
  simpa [gameLog] using this

/-! ### Query-bounded classical adversaries -/

namespace SimExtractionAdversaryROM

variable {tq Q : ℕ} (𝒜 : M.SimExtractionAdversaryROM B X' (Claim X M.NIProof) tq) (c : Fin Q → SaltedCoins (FiatShamirSalt kS) C)

/-- **The probability that `𝒜` wins while the straight-line extractor `dbExtract` fails**, over
its coins and a uniform base oracle, with simulator coins `c`: it outputs a statement none of its
proof queries was, with a proof the spBCS verifier accepts under the final oracle, and `dbExtract
E` returns no witness for the statement from the game's query table padded to `tq + Q q + kq`. -/
noncomputable def winsNotExtracts [DecidableEq X] (rel : Set (X × Wit))
    (E : CausalExtractor P t X Wit) (kq q : ℕ) : ℝ≥0∞ :=
  ∑' r, 𝒜.coins r * Pr[h ← (Query k kN kS L → Out k e) :
    M.WinsROM B Qs fx sp c (𝒜.prog r) h ∧
    M.gameLog B Qs sp c (𝒜.prog r)
        (tq + Q * q + kq) h ∉
      M.extracts rel E (M.romResult B sp c (𝒜.prog r) h).out.stmt]

end SimExtractionAdversaryROM

end

namespace ROM

open SPBCS

variable {M : SPBCS Mg P X k kN kS L e} {B : ℕ} [∀ j i, Fintype ((M.comp j).MessageWrite i)]
  {V : X → FullTr P t → Bool} {Qs : ∀ x, M.IOPQueries V x} {X' : Type} {fx : X' → X} {C : Type}
  {sp : X' → SaltedCoins (FiatShamirSalt kS) C →
    OracleProg (Query k kN kS L) (Out k e) (NARG.SimOutput (Query k kN kS L) (Out k e) (M.Response B))}
  {Wit : Type} {rel : Set (X × Wit)} {E : CausalExtractor P t X Wit}
  {St : CausalStateFn P t X} {ε : ChIdx P t → ℝ≥0}

omit [∀ j i, Fintype ((M.comp j).MessageWrite i)] in
/-- **Simulation-sound extractability of the spBCS compiler in the classical random-oracle
model, at fixed simulator coins** (the extraction condition of paper `thm:bcs-se`(2), from which
`SPBCS.weak_online_simulation_extractability_rom` derives the full statement; Unruh 2017, ePrint 2017/398, Definition 14, p. 21, weak variant,
with straight-line extraction, against classical adversaries; the event of CY24 Definition 5.1.1,
p. 48, with coins independent of the oracle, CY24 Remark 5.1.4, p. 49): for a composite causally
round-by-round knowledge sound at `E` with errors `ε` (`hrbr`), query phases whose accepting runs
make at most `kq` verifier queries (`hkq`), the simulation oracle running a classical simulator
program `sp` that assigns only at the keys of its chain inputs (`hA`) and makes at most `q`
queries (`hqs`), with coins `c`, on any queried statement and answering the first `Q` proof queries,
and every query-bounded classical adversary (`ROM.QueryBoundedAdversary`): over its coins and a
uniform base oracle, the probability that it outputs a statement none of its proof queries was with a
proof the verifier accepts under the final reprogrammed oracle while the straight-line extractor
`dbExtract` at `E`, reading the query table of the adversary's, the simulator's and the
verifier's queries, returns no witness for the statement is at most
`simExtractionErrorROM kq (maxError ε) q tq Q`. -/
theorem _root_.GordieHowe.SPBCS.weak_online_simulation_extractability_rom_basic [DecidableEq X]
    (hA : ∀ r a, M.AssignsAtKeys (sp r a) ⟨a.salt, fx r⟩) {q : ℕ}
    (hqs : ∀ r a G, ((sp r a).trace G).length ≤ q)
    (hrbr : CausalRBRKnowledgeSound rel V E St ε) {kq : ℕ}
    (hkq : ∀ x h π, M.Accepts h x π (Qs x) → (M.queries x π h (Qs x)).length ≤ kq) {Q tq : ℕ}
    (c : Fin Q → SaltedCoins (FiatShamirSalt kS) C) (𝒜 : M.SimExtractionAdversaryROM B X' (Claim X M.NIProof) tq) :
    SimExtractionAdversaryROM.winsNotExtracts (Qs := Qs) (fx := fx) (sp := sp) 𝒜 c rel E kq q ≤
      M.simExtractionErrorROM kq (maxError ε) q tq Q :=
  𝒜.tsum_le fun r => simulation_sound_extractability_rom_joint hA hqs hrbr hkq c
    _ ((𝒜.alg r).queryBound_toSEProg tq)

end ROM

end GordieHowe.SPBCS
