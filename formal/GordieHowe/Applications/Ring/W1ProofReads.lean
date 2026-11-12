-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Ring.SPBCSSplit
public import GordieHowe.Applications.Ring.MLDSAW1Unforgeability
public import GordieHowe.Applications.Ring.MLDSAW1HiddenPoints
public import GordieHowe.Applications.Ring.MLDSAW1KeyFreeRoute2

@[expose] public section

/-!
# Where the proof system of the ML-DSA ring publishing `w₁` reads the oracle

The spBCS proof system on the second component of a split oracle (`spbcsSplitProofSystem`,
`GordieHowe/Applications/Ring/SPBCSSplit.lean`) reads the base component through the statement
program and the second component only at the encoded spBCS queries `Query.toBits q`.

- `accepted_qVerifier_congr`: the compiled verifier's acceptance is the same at two oracles that
  agree at every point `Query.toBits q`. `run_splitNIProver_congr`, `mem_range_of_mem_trace_splitNIProver`:
  the compiled honest prover's result is the same at two such oracles, and it queries only such
  points.
- `run_prove_spbcsSplit_congr`, `verify_spbcsSplit_congr`: the prover's runs and the verifier agree
  at two oracles whose statement programs give the same value on the base components and whose
  second components agree at every point `Query.toBits q`.
- `run_prove_spbcsSplit_eq_of_agreeOff`, `verify_spbcsSplit_eq_of_agreeOff`: for a set `Bad` of
  points off the range of `Query.toBits` that the statement program never queries, the prover's runs
  and the verifier agree at two oracles agreeing outside `Bad`.
- `mem_trace_hashesProg`, `mem_trace_w1StmtProg`, `isPt_of_mem_trace_w1StmtProg`: the statement
  program `w1StmtProg` queries only the points `O.muPt (pubTr pk, bmsg R m)` of the ring's keys and
  `O.chPt (u, x.pub)`.
- `w1PS_run_prove_eq_of_agreeOffRange`, `w1PS_verify_eq_of_agreeOffRange`, and the same for `w1HPS`:
  the hypotheses `hPSm`, `hPSv` of `insiderForgeProb_le_w1C2` for oracles agreeing off the mask
  points, when the base signer's points and the encoded spBCS queries are not mask points.
- `w1PS_run_prove_eq_of_pub`, `proverReadsPub_w1HPS`: `ProverReadsPub` for `w1HPS`, when message
  points are not commitment-hash points.
-/

namespace GordieHowe.Ring

open Quantum GordieHowe.QROM GordieHowe.SPBCS IOP SPTerm GordieHowe.RingSignature GordieHowe.IOP
open GordieHowe.RingSignature.OracleSplit
open scoped ENNReal

section System

variable {k kN kS L e N : ℕ} {Y Y₁ : Type} [AddGroup Y] [AddGroup Y₁]
  (sp : OracleSplit Y Y₁ (XOut k e)) {TS : Signature.SchemeTypes} {RMsg : Type}
  {B : BaseSigner (Bits (queryBits k kN kS L)) Y N TS RMsg}
  {ι : Type} {τ : SPTerm ι} {Mg : Merges τ} {nr : ι → ℕ}
  {P : (j : ι) → ProtocolSpec (nr j)} [∀ j i, Fintype ((P j).Challenge i)]
  [∀ j i, DecidableEq ((P j).Challenge i)] [∀ j i, Nonempty ((P j).Challenge i)] {X₀ Wit₀ : Type}
  (M : SPBCS Mg P X₀ k kN kS L e) (Λ : SiteLayout Mg) {b : ℕ}
  [∀ j i, Fintype ((M.comp j).MessageWrite i)] (E : (j : ι) → (M.comp j).Encoder)
  {Vr : X₀ → FullTr P τ → Bool} {Qs : ∀ x, M.IOPQueries Vr x}
  (hb : M.FormatBounds Qs b b) {R : Type} [Fintype R] [DecidableEq R] [Nonempty R]
  (honest : Wit₀ → R → CausalProver P τ X₀)
  (stmtProg : RingSignature.RingStmt B → OracleProg (Bits (queryBits k kN kS L)) Y₁ X₀) (qS : ℕ)
  (hS : ∀ x, (stmtProg x).QueriesLE qS) (check : RingSignature.RingStmt B → Bool)
  (input : RingSignature.RingStmt B → RingSignature.RingWit B → Option Wit₀)

omit [∀ j i, Fintype ((M.comp j).MessageWrite i)] in
include hb in
/-- **The compiled verifier reads the oracle only at the encoded queries**: its acceptance is the
same at two oracles agreeing at every point `Query.toBits q`. -/
theorem accepted_qVerifier_congr {h h' : Bits (queryBits k kN kS L) → Out k e}
    (hh : ∀ q : Query k kN kS L, h (Query.toBits q) = h' (Query.toBits q))
    (c : Claim X₀ M.NIProof) :
    (M.qVerifier Qs b b).Accepted h c ↔ (M.qVerifier Qs b b).Accepted h' c := by
  rw [M.accepted_qVerifier_iff hb, M.accepted_qVerifier_iff hb]
  have : h ∘ Query.toBits = h' ∘ Query.toBits := funext hh
  rw [this]

omit [AddGroup Y] [AddGroup Y₁] [∀ j i, Fintype ((M.comp j).MessageWrite i)] [DecidableEq R] in
/-- **The compiled honest prover reads the oracle only at the encoded queries**: its result is the
same at two oracles agreeing at every point `Query.toBits q`. -/
theorem run_splitNIProver_congr (x₀ : X₀) (y : Wit₀)
    (c : SaltedCoins (FiatShamirSalt kS) (M.ProverCoins R))
    {G G' : Bits (queryBits k kN kS L) → XOut k e}
    (hG : ∀ q : Query k kN kS L, G (Query.toBits q) = G' (Query.toBits q)) :
    ((splitNIProver M Λ E hb honest).prog x₀ y c).run G =
      ((splitNIProver M Λ E hb honest).prog x₀ y c).run G' := by
  have hrun : ∀ G : Bits (queryBits k kN kS L) → XOut k e,
      ((splitNIProver M Λ E hb honest).prog x₀ y c).run G =
        (((M.niProver Λ honest E hb).mapOutput some).prog x₀ y c).run
          ((queryEncoding (k := k) (kN := kN) (kS := kS) (L := L) (e := e)).decode G) :=
    fun G => OracleProg.run_mapQuery _ _ _ _
  rw [hrun, hrun]
  congr 1
  funext q
  exact congrArg (queryEncoding (k := k) (kN := kN) (kS := kS) (L := L) (e := e)).answer (hG q)

omit [AddGroup Y] [AddGroup Y₁] [∀ j i, Fintype ((M.comp j).MessageWrite i)] [DecidableEq R] in
/-- **The compiled honest prover queries only encoded queries.** -/
theorem mem_range_of_mem_trace_splitNIProver (x₀ : X₀) (y : Wit₀)
    (c : SaltedCoins (FiatShamirSalt kS) (M.ProverCoins R))
    (G : Bits (queryBits k kN kS L) → XOut k e) {z : Bits (queryBits k kN kS L)}
    (hz : z ∈ ((splitNIProver M Λ E hb honest).prog x₀ y c).trace G) :
    z ∈ Set.range (Query.toBits (k := k) (kN := kN) (kS := kS) (L := L)) := by
  have htr : ((splitNIProver M Λ E hb honest).prog x₀ y c).trace G =
      ((((M.niProver Λ honest E hb).mapOutput some).prog x₀ y c).trace
        ((queryEncoding (k := k) (kN := kN) (kS := kS) (L := L) (e := e)).decode G)).map
          Query.toBits :=
    OracleProg.trace_mapQuery _ _ _ _
  rw [htr] at hz
  obtain ⟨q, -, rfl⟩ := List.mem_map.1 hz
  exact ⟨q, rfl⟩

omit [∀ j i, Fintype ((M.comp j).MessageWrite i)] [DecidableEq R] in
/-- **The prover of the split proof system is the same at two oracles** whose statement programs
give the same value on the base components and whose second components agree at every point
`Query.toBits q`. -/
theorem run_prove_spbcsSplit_congr (x : RingSignature.RingStmt B) (w : RingSignature.RingWit B)
    (c : SaltedCoins (FiatShamirSalt kS) (M.ProverCoins R)) {H H' : Bits (queryBits k kN kS L) → Y}
    (hbase : (stmtProg x).run (base sp H) = (stmtProg x).run (base sp H'))
    (hprf : ∀ q : Query k kN kS L, prf sp H (Query.toBits q) = prf sp H' (Query.toBits q)) :
    ((spbcsSplitProofSystem sp M Λ E hb honest stmtProg qS hS check input).prove x w c).run H =
      ((spbcsSplitProofSystem sp M Λ E hb honest stmtProg qS hS check input).prove x w c).run
        H' := by
  change ((((stmtProg x).mapQuery id fun y => (sp y).1).bind fun x₀ =>
    (input x w).elim (.pure none) fun y =>
      ((splitNIProver M Λ E hb honest).prog x₀ y c).mapQuery id fun y => (sp y).2)).run H =
    ((((stmtProg x).mapQuery id fun y => (sp y).1).bind fun x₀ =>
    (input x w).elim (.pure none) fun y =>
      ((splitNIProver M Λ E hb honest).prog x₀ y c).mapQuery id fun y => (sp y).2)).run H'
  rw [OracleProg.run_bind, OracleProg.run_bind, OracleProg.run_mapQuery, OracleProg.run_mapQuery]
  change ((input x w).elim (.pure none) fun y =>
      ((splitNIProver M Λ E hb honest).prog ((stmtProg x).run (base sp H)) y c).mapQuery id
        fun y => (sp y).2).run H =
    ((input x w).elim (.pure none) fun y =>
      ((splitNIProver M Λ E hb honest).prog ((stmtProg x).run (base sp H')) y c).mapQuery id
        fun y => (sp y).2).run H'
  rw [hbase]
  rcases input x w with _ | y
  · rfl
  · simp only [Option.elim_some, OracleProg.run_mapQuery]
    exact run_splitNIProver_congr M Λ E hb honest _ y c fun q => hprf q

omit [∀ j i, Fintype ((M.comp j).MessageWrite i)] [Fintype R] [DecidableEq R] [Nonempty R] in
/-- **The verifier of the split proof system is the same at two oracles** whose statement programs
give the same value on the base components and whose second components agree at every point
`Query.toBits q`. -/
theorem verify_spbcsSplit_congr (x : RingSignature.RingStmt B) (π : M.Response b)
    {H H' : Bits (queryBits k kN kS L) → Y}
    (hbase : (stmtProg x).run (base sp H) = (stmtProg x).run (base sp H'))
    (hprf : ∀ q : Query k kN kS L, prf sp H (Query.toBits q) = prf sp H' (Query.toBits q)) :
    (spbcsSplitProofSystem sp M Λ E hb honest stmtProg qS hS check input).verify H x π =
      (spbcsSplitProofSystem sp M Λ E hb honest stmtProg qS hS check input).verify H' x π := by
  have hcl : spbcsSplitClaim M stmtProg (base sp H) x π =
      spbcsSplitClaim M stmtProg (base sp H') x π := by
    simp only [spbcsSplitClaim, hbase]
  rw [Bool.eq_iff_iff, verify_spbcsSplitProofSystem_eq_true_iff,
    verify_spbcsSplitProofSystem_eq_true_iff, hcl]
  refine and_congr Iff.rfl (exists_congr fun c => and_congr Iff.rfl ?_)
  exact accepted_qVerifier_congr M hb (fun q => congrArg (outEquiv k e) (hprf q)) c

variable {sp M Λ E hb honest stmtProg qS hS check input} in
/-- The statement program gives the same value at two oracles agreeing outside a set it never
queries. -/
theorem run_base_eq_of_agreeOff {Bad : Set (Bits (queryBits k kN kS L))}
    (hq : ∀ x (ω : Bits (queryBits k kN kS L) → Y₁), ∀ z ∈ (stmtProg x).trace ω, z ∉ Bad)
    (x : RingSignature.RingStmt B) {H H' : Bits (queryBits k kN kS L) → Y}
    (hH : ∀ z ∉ Bad, H z = H' z) :
    (stmtProg x).run (base sp H) = (stmtProg x).run (base sp H') :=
  OracleProg.run_congr (stmtProg x) fun z hz => by
    simp only [base, hH z (hq x _ z hz)]

omit [∀ j i, Fintype ((M.comp j).MessageWrite i)] [DecidableEq R] in
/-- **The prover of the split proof system is the same at two oracles agreeing outside `Bad`**, a
set of points off the encoded queries that the statement program never queries. -/
theorem run_prove_spbcsSplit_eq_of_agreeOff (Bad : Set (Bits (queryBits k kN kS L)))
    (hBad : ∀ q : Query k kN kS L, Query.toBits q ∉ Bad)
    (hq : ∀ x (ω : Bits (queryBits k kN kS L) → Y₁), ∀ z ∈ (stmtProg x).trace ω, z ∉ Bad)
    (x : RingSignature.RingStmt B) (w : RingSignature.RingWit B)
    (c : SaltedCoins (FiatShamirSalt kS) (M.ProverCoins R)) {H H' : Bits (queryBits k kN kS L) → Y}
    (hH : ∀ z ∉ Bad, H z = H' z) :
    ((spbcsSplitProofSystem sp M Λ E hb honest stmtProg qS hS check input).prove x w c).run H =
      ((spbcsSplitProofSystem sp M Λ E hb honest stmtProg qS hS check input).prove x w c).run
        H' :=
  run_prove_spbcsSplit_congr sp M Λ E hb honest stmtProg qS hS check input x w c
    (run_base_eq_of_agreeOff hq x hH) fun q => by simp only [prf, hH _ (hBad q)]

omit [∀ j i, Fintype ((M.comp j).MessageWrite i)] [Fintype R] [DecidableEq R] [Nonempty R] in
/-- **The verifier of the split proof system is the same at two oracles agreeing outside `Bad`**,
a set of points off the encoded queries that the statement program never queries. -/
theorem verify_spbcsSplit_eq_of_agreeOff (Bad : Set (Bits (queryBits k kN kS L)))
    (hBad : ∀ q : Query k kN kS L, Query.toBits q ∉ Bad)
    (hq : ∀ x (ω : Bits (queryBits k kN kS L) → Y₁), ∀ z ∈ (stmtProg x).trace ω, z ∉ Bad)
    (x : RingSignature.RingStmt B) (π : M.Response b) {H H' : Bits (queryBits k kN kS L) → Y}
    (hH : ∀ z ∉ Bad, H z = H' z) :
    (spbcsSplitProofSystem sp M Λ E hb honest stmtProg qS hS check input).verify H x π =
      (spbcsSplitProofSystem sp M Λ E hb honest stmtProg qS hS check input).verify H' x π :=
  verify_spbcsSplit_congr sp M Λ E hb honest stmtProg qS hS check input x π
    (run_base_eq_of_agreeOff hq x hH) fun q => by simp only [prf, hH _ (hBad q)]

end System

end GordieHowe.Ring

namespace GordieHowe.Ring.MLDSAW1

open _root_.MLDSA GordieHowe.MLDSA GordieHowe.RingSignature GordieHowe.RingSignature.OracleSplit
open Quantum GordieHowe.QROM GordieHowe.SPBCS IOP SPTerm GordieHowe.IOP
open scoped ENNReal

/-! ### The points the statement program queries -/

section Stmt

variable {X Y Y₁ Y₂ : Type} [AddGroup Y] [AddGroup Y₁] [AddGroup Y₂] (sp : OracleSplit Y Y₁ Y₂)
  {p : Params} (prims : Primitives p) {Msg : Type} {N reps : ℕ}
  (O : W1Oracles X Y p prims Msg N reps)

/-- **The hash program queries only the message points of its keys and commitment-hash points at
`w₁`.** -/
theorem mem_trace_hashesProg (m : Msg) (w1 : BucketVec p) (ω : X → Y₁) :
    ∀ (l : List (PubKey p prims)) (z : X), z ∈ (hashesProg sp prims O m w1 l).trace ω →
      (∃ pk ∈ l, z = O.muPt (pubTr prims pk, m)) ∨ ∃ u, z = O.chPt (u, w1)
  | [], z, hz => by simp [hashesProg, OracleProg.trace_pure] at hz
  | pk :: l, z, hz => by
    simp only [hashesProg, OracleProg.trace_query, OracleProg.trace_mapOutput, List.mem_cons] at hz
    rcases hz with rfl | rfl | hz
    · exact Or.inl ⟨pk, by simp, rfl⟩
    · exact Or.inr ⟨_, rfl⟩
    · rcases mem_trace_hashesProg m w1 ω l z hz with ⟨pk', hpk', rfl⟩ | h
      · exact Or.inl ⟨pk', by simp [hpk'], rfl⟩
      · exact Or.inr h

variable [NeZero (bucketCount p)] [nttOps : NTTRingOps] [Fintype prims.Power2High]
  [DecidableEq prims.Power2High] [Fintype prims.Hint] [DecidableEq prims.Hint] [Fintype Msg]
  [DecidableEq Msg] (βmin : ℚ≥0) (tol : ℕ)
  (enc : Vector prims.High p.k → BucketVec p) {CL : Type} [Fintype CL] [DecidableEq CL] [Nonempty CL] (L : W1Loop X Y p prims Msg N CL) {RMsg : Type}
  [Fintype RMsg] [DecidableEq RMsg] (bmsg : KeyRing (PubKey p prims) N → RMsg → Msg)

omit [NeZero (bucketCount p)] in
/-- **The statement program queries only the message points of the ring's keys and the
commitment-hash points `O.chPt (u, x.pub)`.** -/
theorem mem_trace_w1StmtProg
    (x : RingSignature.RingStmt (w1BaseSigner prims O βmin tol enc L bmsg)) (ω : X → Y₁) {z : X}
    (hz : z ∈ (w1StmtProg sp prims O bmsg x).trace ω) :
    (∃ pk ∈ (x.ring.1 : List (PubKey p prims)), z = O.muPt (pubTr prims pk, bmsg x.ring x.msg)) ∨
      ∃ u, z = O.chPt (u, x.pub) := by
  rw [w1StmtProg, OracleProg.trace_mapOutput] at hz
  exact mem_trace_hashesProg sp prims O _ _ ω _ z hz

omit [NeZero (bucketCount p)] in
/-- **The statement program queries only points of the base signer's oracles.** -/
theorem isPt_of_mem_trace_w1StmtProg
    (x : RingSignature.RingStmt (w1BaseSigner prims O βmin tol enc L bmsg)) (ω : X → Y₁) {z : X}
    (hz : z ∈ (w1StmtProg sp prims O bmsg x).trace ω) : O.IsPt z := by
  rcases mem_trace_w1StmtProg sp prims O βmin tol enc L bmsg x ω hz with ⟨_, _, rfl⟩ | ⟨_, rfl⟩
  · exact Or.inl ⟨_, rfl⟩
  · exact Or.inr (Or.inl ⟨_, rfl⟩)

end Stmt

/-! ### The proof system of the ring off the mask points and off the other commitment hashes -/

section PS

variable {k kN kS L e : ℕ} {Y Y₁ : Type} [AddGroup Y] [AddGroup Y₁]
  {sp : OracleSplit Y Y₁ (XOut k e)} {p : Params} {prims : Primitives p} {Msg : Type} {N reps : ℕ}
  [NeZero (bucketCount p)] [nttOps : NTTRingOps] [Fintype prims.Power2High]
  [DecidableEq prims.Power2High] [Fintype prims.Hint] [DecidableEq prims.Hint] [Fintype Msg]
  [DecidableEq Msg] {O : W1Oracles (Bits (queryBits k kN kS L)) Y p prims Msg N reps}
  {βmin : ℚ≥0} {tol : ℕ} {enc : Vector prims.High p.k → BucketVec p}
  {CLp : Type} [Fintype CLp] [DecidableEq CLp] [Nonempty CLp] {Lp : W1Loop (Bits (queryBits k kN kS L)) Y p prims Msg N CLp} {RMsg : Type} [Fintype RMsg]
  [DecidableEq RMsg] {bmsg : KeyRing (PubKey p prims) N → RMsg → Msg}
  {ι : Type} {τ : SPTerm ι} {Mg : Merges τ} {nr : ι → ℕ}
  {P : (j : ι) → ProtocolSpec (nr j)} [∀ j i, Fintype ((P j).Challenge i)]
  [∀ j i, DecidableEq ((P j).Challenge i)] [∀ j i, Nonempty ((P j).Challenge i)]
  {M : SPBCS Mg P (W1ExpStmt prims RMsg N) k kN kS L e} {Λ : SiteLayout Mg}
  {b : ℕ} [∀ j i, Fintype ((M.comp j).MessageWrite i)] {E : (j : ι) → (M.comp j).Encoder}
  {Vr : W1ExpStmt prims RMsg N → FullTr P τ → Bool} {Qs : ∀ x, M.IOPQueries Vr x}
  {hb : M.FormatBounds Qs b b} {R : Type} [Fintype R] [DecidableEq R] [Nonempty R]
  {honest : RingSignature.RingWit (w1BaseSigner prims O βmin tol enc Lp bmsg) → R →
    CausalProver P τ (W1ExpStmt prims RMsg N)}
  {T : ℕ} {Mo : MaskOracle (Bits (queryBits k kN kS L)) Y p T Msg}

omit [NeZero (bucketCount p)] in
/-- The statement program never queries a mask point when the base signer's points are not mask
points. -/
theorem w1StmtProg_avoids_mask (hdisjM : ∀ x, O.IsPt x → x ∉ Set.range Mo.pt)
    (x : RingSignature.RingStmt (w1BaseSigner prims O βmin tol enc Lp bmsg))
    (ω : Bits (queryBits k kN kS L) → Y₁) :
    ∀ z ∈ (w1StmtProg sp prims O bmsg x).trace ω, z ∉ Set.range Mo.pt :=
  fun _ hz => hdisjM _ (isPt_of_mem_trace_w1StmtProg sp prims O βmin tol enc Lp bmsg x ω hz)

omit [NeZero (bucketCount p)] [∀ j i, Fintype ((M.comp j).MessageWrite i)] [DecidableEq R] in
/-- **The prover of the ring reads no mask point** (`hPSm` of `insiderForgeProb_le_w1C2`): when the
base signer's points and the encoded spBCS queries are not mask points. -/
theorem w1PS_run_prove_eq_of_agreeOffRange (hdisjM : ∀ x, O.IsPt x → x ∉ Set.range Mo.pt)
    (hdisjQ : ∀ q : Query k kN kS L, Query.toBits q ∉ Set.range Mo.pt) :
    ∀ x w c H H', Quantum.AgreeOffRange Mo.pt H H' →
      ((w1PS sp prims O βmin tol enc Lp bmsg M Λ E hb honest).prove x w c).run H =
        ((w1PS sp prims O βmin tol enc Lp bmsg M Λ E hb honest).prove x w c).run H' :=
  fun x w c _ _ hH => run_prove_spbcsSplit_eq_of_agreeOff sp M Λ E hb honest _ _ _ _ _ _ hdisjQ
    (fun x ω => w1StmtProg_avoids_mask hdisjM x ω) x w c hH

omit [NeZero (bucketCount p)]
  [∀ j i, Fintype ((M.comp j).MessageWrite i)] [Fintype R] [DecidableEq R] [Nonempty R] in
/-- **The verifier of the ring reads no mask point** (`hPSv` of `insiderForgeProb_le_w1C2`): when
the base signer's points and the encoded spBCS queries are not mask points. -/
theorem w1PS_verify_eq_of_agreeOffRange (hdisjM : ∀ x, O.IsPt x → x ∉ Set.range Mo.pt)
    (hdisjQ : ∀ q : Query k kN kS L, Query.toBits q ∉ Set.range Mo.pt) :
    ∀ x π H H', Quantum.AgreeOffRange Mo.pt H H' →
      (w1PS sp prims O βmin tol enc Lp bmsg M Λ E hb honest).verify H x π =
        (w1PS sp prims O βmin tol enc Lp bmsg M Λ E hb honest).verify H' x π :=
  fun x π _ _ hH => verify_spbcsSplit_eq_of_agreeOff sp M Λ E hb honest _ _ _ _ _ _ hdisjQ
    (fun x ω => w1StmtProg_avoids_mask hdisjM x ω) x π hH

omit [NeZero (bucketCount p)] [∀ j i, Fintype ((M.comp j).MessageWrite i)] [DecidableEq R] in
/-- **The prover of the ring reads the base component only at the commitment hashes of the
statement's public value and off the commitment-hash points**: two oracles with the same second
components everywhere, agreeing off the commitment-hash points and at the points `chPt (u, x.pub)`,
give the same proof, when message points are not commitment-hash points. -/
theorem w1PS_run_prove_eq_of_pub (hdisj : ∀ a b, O.muPt a ≠ O.chPt b)
    (x : RingSignature.RingStmt (w1BaseSigner prims O βmin tol enc Lp bmsg))
    (w : RingSignature.RingWitOf (FIPSSignature p prims))
    (c : (w1PS sp prims O βmin tol enc Lp bmsg M Λ E hb honest).Coins)
    (H₁ H₂ : Bits (queryBits k kN kS L) → Y) (h2 : ∀ z, (sp (H₁ z)).2 = (sp (H₂ z)).2)
    (h1 : ∀ z, (z ∉ Set.range O.chPt ∨ ∃ u, z = O.chPt (u, x.pub)) → H₁ z = H₂ z) :
    ((w1PS sp prims O βmin tol enc Lp bmsg M Λ E hb honest).prove x w c).run H₁ =
      ((w1PS sp prims O βmin tol enc Lp bmsg M Λ E hb honest).prove x w c).run H₂ := by
  refine run_prove_spbcsSplit_congr sp M Λ E hb honest _ _ _ _ _ x w c ?_ fun q => h2 _
  refine OracleProg.run_congr _ fun z hz => ?_
  have hz' : z ∉ Set.range O.chPt ∨ ∃ u, z = O.chPt (u, x.pub) := by
    rcases mem_trace_w1StmtProg sp prims O βmin tol enc Lp bmsg x _ hz with ⟨_, _, rfl⟩ | h
    · exact Or.inl fun ⟨b', hb'⟩ => hdisj _ b' hb'.symm
    · exact Or.inr h
  simp only [base, h1 z hz']

end PS

/-! ### The hedged proof system -/

section Hedged

open GordieHowe.QROM GordieHowe.SPBCS IOP SPTerm GordieHowe.IOP

variable {p : Params} {T : ℕ} {Msg : Type} {N reps : ℕ}
  {kh kN kS L e : ℕ} {Y Y₁ : Type} [AddGroup Y] [AddGroup Y₁] [Fintype Y] [DecidableEq Y]
  [Nonempty Y] {sp : OracleSplit Y Y₁ (XOut kh e)} {prims : Primitives p}
  [NeZero (bucketCount p)] [nttOps : NTTRingOps] [Fintype prims.Power2High]
  [DecidableEq prims.Power2High] [Fintype prims.Hint] [DecidableEq prims.Hint]
  [Nonempty (MaskBox p)] [Fintype Msg] [DecidableEq Msg]
  {O : W1Oracles (Bits (queryBits kh kN kS L)) Y p prims Msg N reps}
  {Mo : MaskOracle (Bits (queryBits kh kN kS L)) Y p T Msg} {βmin : ℚ≥0} {tol : ℕ}
  {enc : Vector prims.High p.k → BucketVec p} {k D : ℕ} [NeZero D] {RMsg : Type} [Fintype RMsg]
  [DecidableEq RMsg] {bmsg : KeyRing (PubKey p prims) N → RMsg → Msg}
  {ι : Type} {τ : SPTerm ι} {Mg : Merges τ} {nr : ι → ℕ}
  {P : (j : ι) → ProtocolSpec (nr j)} [∀ j i, Fintype ((P j).Challenge i)]
  [∀ j i, DecidableEq ((P j).Challenge i)] [∀ j i, Nonempty ((P j).Challenge i)]
  {Mc : SPBCS Mg P (W1ExpStmt prims RMsg N)
    kh kN kS L e}
  {Λ : SiteLayout Mg} {b : ℕ} [∀ j i, Fintype ((Mc.comp j).MessageWrite i)]
  {E : (j : ι) → (Mc.comp j).Encoder}
  {Vr : W1ExpStmt prims RMsg N → FullTr P τ → Bool}
  {Qs : ∀ x, Mc.IOPQueries Vr x} {hb : Mc.FormatBounds Qs b b} {R : Type} [Fintype R]
  [DecidableEq R] [Nonempty R]
  {honest : RingSignature.RingWit (freshBase prims O Mo βmin tol enc k D bmsg) → R →
    CausalProver P τ (W1ExpStmt prims RMsg N)}
  {chk : RingSignature.RingStmt (freshBase prims O Mo βmin tol enc k D bmsg) → Bool}

omit [∀ j i, Fintype ((Mc.comp j).MessageWrite i)] [DecidableEq R] in
/-- **The hedged prover reads no mask point** (`hPSm` of `insiderForgeProb_le_w1C2` for `w1HPS`),
for any check. -/
theorem w1HPS_run_prove_eq_of_agreeOffRange (hdisjM : ∀ x, O.IsPt x → x ∉ Set.range Mo.pt)
    (hdisjQ : ∀ q : Query kh kN kS L, Query.toBits q ∉ Set.range Mo.pt) :
    ∀ x w c H H', Quantum.AgreeOffRange Mo.pt H H' →
      ((w1HPS sp prims O Mo βmin tol enc k D bmsg Mc Λ E hb honest chk).prove x w c).run H =
        ((w1HPS sp prims O Mo βmin tol enc k D bmsg Mc Λ E hb honest chk).prove x w c).run H' :=
  fun x w c _ _ hH => run_prove_spbcsSplit_eq_of_agreeOff sp Mc Λ E hb honest
    (w1StmtProg sp prims O bmsg) (2 * N)
    (w1StmtProg_queries sp prims O bmsg) chk
    (fun _ w => some w)
    _ hdisjQ (fun x ω => w1StmtProg_avoids_mask hdisjM x ω) x w c hH

omit [∀ j i, Fintype ((Mc.comp j).MessageWrite i)] [Fintype R] [DecidableEq R] [Nonempty R] in
/-- **The hedged verifier reads no mask point** (`hPSv` of `insiderForgeProb_le_w1C2` for
`w1HPS`), for any check. -/
theorem w1HPS_verify_eq_of_agreeOffRange (hdisjM : ∀ x, O.IsPt x → x ∉ Set.range Mo.pt)
    (hdisjQ : ∀ q : Query kh kN kS L, Query.toBits q ∉ Set.range Mo.pt) :
    ∀ x π H H', Quantum.AgreeOffRange Mo.pt H H' →
      (w1HPS sp prims O Mo βmin tol enc k D bmsg Mc Λ E hb honest chk).verify H x π =
        (w1HPS sp prims O Mo βmin tol enc k D bmsg Mc Λ E hb honest chk).verify H' x π :=
  fun x π _ _ hH => verify_spbcsSplit_eq_of_agreeOff sp Mc Λ E hb honest
    (w1StmtProg sp prims O bmsg) (2 * N)
    (w1StmtProg_queries sp prims O bmsg) chk
    (fun _ w => some w)
    _ hdisjQ (fun x ω => w1StmtProg_avoids_mask hdisjM x ω) x π hH

omit [∀ j i, Fintype ((Mc.comp j).MessageWrite i)] [DecidableEq R] [Fintype Y] [DecidableEq Y]
  [Nonempty Y] in
/-- **`ProverReadsPub` for the hedged proof system**, for any check, when message points are not
commitment-hash points. -/
theorem proverReadsPub_w1HPS (hdisj : ∀ a b, O.muPt a ≠ O.chPt b) :
    ProverReadsPub O (w1HPS sp prims O Mo βmin tol enc k D bmsg Mc Λ E hb honest chk) sp := by
  intro x w c H₁ H₂ h2 h1
  refine run_prove_spbcsSplit_congr sp Mc Λ E hb honest
    (w1StmtProg sp prims O bmsg) (2 * N)
    (w1StmtProg_queries sp prims O bmsg) chk
    (fun _ w => some w)
    _ _ c ?_ fun q => h2 _
  refine OracleProg.run_congr _ fun z hz => ?_
  have hz' : z ∉ Set.range O.chPt ∨ ∃ u, z = O.chPt (u, x.pub) := by
    rcases mem_trace_w1StmtProg sp prims O βmin tol enc _ bmsg _ _ hz with ⟨_, _, rfl⟩ | h
    · exact Or.inl fun ⟨b', hb'⟩ => hdisj _ b' hb'.symm
    · exact Or.inr h
  simp only [base, h1 z hz']

end Hedged

/-- **The spBCS queries are not mask points**: no encoded query `Query.toBits q` of the spBCS
argument with parameters `kh`, `kN`, `kS`, `L` is a point of the mask oracle `MO`. The Prop field is
a hypothesis the user supplies; `w1M_maskQueryFacts` proves it for the concrete mask oracle. -/
structure W1MaskQueryFacts {Y : Type} {p : Params} {T : ℕ} {Msg : Type} (kh kN kS L : ℕ)
    (MO : MaskOracle (Bits (queryBits kh kN kS L)) Y p T Msg) : Prop where
  /-- No encoded query is a mask point. -/
  toBits_notMem : ∀ q : Query kh kN kS L, Query.toBits q ∉ Set.range MO.pt

end GordieHowe.Ring.MLDSAW1
