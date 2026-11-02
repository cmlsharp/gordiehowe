-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Ring.SPBCSComap
public import GordieHowe.Applications.Ring.MLDSAW1Split

@[expose] public section

/-!
# The spBCS proof system on the second component of a split oracle

For a ring signature whose oracle `H : X → Y` splits additively as `sp : Y ≃+ Y₁ × XOut k e`
(`GordieHowe/Applications/Ring/MLDSAW1Split.lean`), the spBCS compilation `M` of an IOP over
program statements `X₀` as a `RingSignature.ProofSystem` over `H`: a ring statement `x` is read as
the program statement `stmtProg x` by a classical program on the base component `base sp H`
(for the ML-DSA ring publishing `w₁`: the members' commitment hashes `c̃_j = H(µ_j, w₁)`, which
the verifier computes outside the circuit), and proved and verified by spBCS on the second
component `prf sp H`. At a fixed base component the program statement is fixed, so the knowledge
bound of spBCS for the program's relation applies at each value of the base component.

- `ProofSystem.CompiledBySplit PS sp V`: a proof system whose verifier is, at each value `ω` of the
  base component, the acceptance of the compiled verifier `V` against the second component on
  claims whose statement is `stmtAt ω x`. `CompiledBySplit.stmt_eq`,
  `CompiledBySplit.accepted_of_verify`.
- `spbcsSplitProofSystem sp M Λ E hb honest stmtProg qS hS check input`: the proof system: the
  prover runs `stmtProg x` on the base component, then the spBCS prover on the program statement
  with the honest input `input x w`, on the second component; the verifier accepts when `x` passes
  `check` and the compiled verifier accepts the claim `(stmtProg x (base), π)` against the second
  component. `verify_spbcsSplitProofSystem_eq_true_iff`, `verify_spbcsSplitProofSystem_none`,
  `run_prove_spbcsSplitProofSystem`.
- `compiledBySplit_spbcsSplitProofSystem`: it is given by `M.qVerifier Qs b b` at the program
  statements `(stmtProg x).run ω`.
- `readsOff_spbcsSplitProofSystem`: its prover reads the second component everywhere and the base
  component only at the queries of `stmtProg` (`ProofSystem.ReadsOff` for every set of points
  `stmtProg` never queries).
-/

namespace GordieHowe.Ring

open Quantum GordieHowe.QROM GordieHowe.SPBCS IOP SPTerm GordieHowe.RingSignature GordieHowe.IOP
open GordieHowe.RingSignature.OracleSplit
open scoped ENNReal

/-! ### Proof systems compiled at each value of the base component -/

/-- **A proof system compiled by `V` at each value of the base component** of the split `sp`: the
program statement `stmtAt ω x` of a ring statement at the base component `ω`, the claims of a
statement and a proof at `ω`, whose statement is `stmtAt ω x` (`stmt_eq`), and on which `V`
accepts against the second component whenever the proof system accepts (`accepted_of_verify`). -/
structure _root_.GordieHowe.RingSignature.ProofSystem.CompiledBySplit {m k e : ℕ}
    {Y Y₁ Stmt Wit Cl X₀ : Type} [AddGroup Y] [AddGroup Y₁] {TPS : PSTypes} (PS : ProofSystem (Bits m) Y Stmt Wit TPS)
    (sp : OracleSplit Y Y₁ (XOut k e))
    (V : NARG.QROM.Verifier m k e Cl X₀) where
  /-- The program statement of a ring statement at a base component. -/
  stmtAt : (Bits m → Y₁) → Stmt → X₀
  /-- The claim of a statement and a proof at a base component. -/
  claim : (Bits m → Y₁) → Stmt → PS.Proof → Option Cl
  /-- The claim's statement is the program statement. -/
  stmt_eq : ∀ ω x π c, c ∈ claim ω x π → V.stmt c = stmtAt ω x
  /-- An accepted proof has a claim that the compiled verifier accepts against the second
  component. -/
  accepted_of_verify : ∀ H x π, PS.verify H x π = true →
    ∃ c ∈ claim (base sp H) x π, V.Accepted (outEquiv k e ∘ prf sp H) c

/-! ### The proof system -/

section System

variable {k kN kS L e N : ℕ} {Y Y₁ : Type} [AddGroup Y] [AddGroup Y₁]
  (sp : OracleSplit Y Y₁ (XOut k e)) {TB : BaseTypes} {B : BaseSigner (Bits (queryBits k kN kS L)) Y N TB}
  {ι : Type} {τ : SPTerm ι} {Mg : Merges τ} {nr : ι → ℕ}
  {P : (j : ι) → ProtocolSpec (nr j)} [∀ j i, Fintype ((P j).Challenge i)]
  [∀ j i, DecidableEq ((P j).Challenge i)] [∀ j i, Nonempty ((P j).Challenge i)] {X₀ Wit₀ : Type}
  (M : SPBCS Mg P X₀ k kN kS L e) (Λ : SiteLayout Mg) {b : ℕ}
  [∀ j i, Fintype ((M.comp j).MessageWrite i)] (E : (j : ι) → (M.comp j).Encoder)
  {Vr : X₀ → FullTr P τ → Bool} {Qs : ∀ x, M.IOPQueries Vr x}
  (hb : M.FormatBounds Qs b b) {R : Type} [Fintype R] [Nonempty R]
  (honest : Wit₀ → R → CausalProver P τ X₀)
  (stmtProg : RingSignature.RingStmt B → OracleProg (Bits (queryBits k kN kS L)) Y₁ X₀) (qS : ℕ)
  (hS : ∀ x, (stmtProg x).QueriesLE qS) (check : RingSignature.RingStmt B → Bool)
  (input : RingSignature.RingStmt B → RingSignature.RingWit B → Option Wit₀)

/-- The compiled honest prover with its proofs in the format `b`, run through `queryEncoding`. -/
noncomputable abbrev splitNIProver :=
  ((M.niProver Λ honest E hb).mapOutput some).encode queryEncoding

/-- **The claim of a ring statement and a proof at a base component** `ω`: `(stmtProg x (ω), π)`
for a proof `π` in the format, none for the missing proof. -/
def spbcsSplitClaim (ω : Bits (queryBits k kN kS L) → Y₁) (x : RingSignature.RingStmt B)
    (π : M.Response b) :
    Option (Claim X₀ M.NIProof) :=
  π.map fun p => ⟨(stmtProg x).run ω, p.1⟩

open Classical in
/-- **The spBCS proof system on the second component of the split `sp`**: the prover runs
`stmtProg x` on the base component and then, at the honest input `input x w` (the missing proof
when there is none), the compiled honest prover on the program statement, on the second
component; the verifier accepts `π` on `x` at `H` exactly when `x` passes `check` and the
compiled verifier `M.qVerifier Qs b b` accepts `spbcsSplitClaim (base sp H) x π` against the
second component `prf sp H`. -/
noncomputable def spbcsSplitProofSystem :
    ProofSystem (Bits (queryBits k kN kS L)) Y (RingSignature.RingStmt B) (RingSignature.RingWit B)
      (spbcsPST M b R) where
  q := qS + (splitNIProver M Λ E hb honest).q
  prove x w c := ((stmtProg x).mapQuery id fun y => (sp y).1).bind fun x₀ =>
    (input x w).elim (.pure none) fun y =>
      ((splitNIProver M Λ E hb honest).prog x₀ y c).mapQuery id fun y => (sp y).2
  prove_queries x w c := by
    refine OracleProg.QueriesLE.bind (fun H => ?_) fun x₀ => ?_
    · rw [OracleProg.length_trace_mapQuery]
      exact hS x _
    · rcases input x w with _ | y
      · exact (OracleProg.QueriesLE.pure _ _).mono (Nat.zero_le _)
      · intro H
        rw [Option.elim_some, OracleProg.length_trace_mapQuery]
        exact (splitNIProver M Λ E hb honest).prog_queries x₀ y c _
  verify H x π := check x && decide (∃ c ∈ spbcsSplitClaim M stmtProg (base sp H) x π,
    (M.qVerifier Qs b b).Accepted (outEquiv k e ∘ prf sp H) c)

/-- **The proof system accepts exactly the checked statements whose claims the compiled verifier
accepts against the second component.** -/
theorem verify_spbcsSplitProofSystem_eq_true_iff (H : Bits (queryBits k kN kS L) → Y)
    (x : RingSignature.RingStmt B) (π : M.Response b) :
    (spbcsSplitProofSystem sp M Λ E hb honest stmtProg qS hS check input).verify H x π = true ↔
      check x = true ∧ ∃ c ∈ spbcsSplitClaim M stmtProg (base sp H) x π,
        (M.qVerifier Qs b b).Accepted (outEquiv k e ∘ prf sp H) c := by
  classical
  change (check x && decide _) = true ↔ _
  rw [Bool.and_eq_true, decide_eq_true_iff]

/-- **The proof system rejects the missing proof.** -/
theorem verify_spbcsSplitProofSystem_none (H : Bits (queryBits k kN kS L) → Y)
    (x : RingSignature.RingStmt B) :
    (spbcsSplitProofSystem sp M Λ E hb honest stmtProg qS hS check input).verify H x
      (none : M.Response b) = false := by
  rw [Bool.eq_false_iff, Ne, verify_spbcsSplitProofSystem_eq_true_iff]
  simp [spbcsSplitClaim]

omit [AddGroup Y] [AddGroup Y₁] [∀ j i, Fintype ((M.comp j).MessageWrite i)] in
/-- **The statement of a claim at a base component is the program statement there.** -/
theorem stmt_of_mem_spbcsSplitClaim {ω : Bits (queryBits k kN kS L) → Y₁}
    {x : RingSignature.RingStmt B} {π : M.Response b} {c : Claim X₀ M.NIProof}
    (hc : c ∈ spbcsSplitClaim M stmtProg ω x π) :
    (M.qVerifier Qs b b).stmt c = (stmtProg x).run ω := by
  cases π with
  | none => simp [spbcsSplitClaim] at hc
  | some p =>
    simp only [spbcsSplitClaim, Option.map_some, Option.mem_def, Option.some.injEq] at hc
    subst hc
    rfl

/-- **An honest proof is the compiled proof of the program statement on the second component**:
at the honest input `y = input x w`, the prover's proof at `H` is the compiled prover's proof of
`(stmtProg x).run (base sp H)` with `y`, against `prf sp H`. -/
theorem run_prove_spbcsSplitProofSystem (H : Bits (queryBits k kN kS L) → Y)
    (x : RingSignature.RingStmt B) (w : RingSignature.RingWit B) {y : Wit₀}
    (hy : input x w = some y)
    (a : SaltedCoins (FiatShamirSalt kS) (M.ProverCoins R)) :
    ((spbcsSplitProofSystem sp M Λ E hb honest stmtProg qS hS check input).prove x w a).run H =
      ((splitNIProver M Λ E hb honest).prog ((stmtProg x).run (base sp H)) y a).run
        (prf sp H) := by
  change ((((stmtProg x).mapQuery id fun y => (sp y).1).bind fun x₀ =>
    (input x w).elim (.pure none) fun y =>
      ((splitNIProver M Λ E hb honest).prog x₀ y a).mapQuery id fun y => (sp y).2)).run H = _
  rw [OracleProg.run_bind, OracleProg.run_mapQuery, hy, Option.elim_some, OracleProg.run_mapQuery]
  rfl

/-- **The proof system is compiled by `M.qVerifier Qs b b` at the program statements**
`(stmtProg x).run ω`. -/
def compiledBySplit_spbcsSplitProofSystem :
    (spbcsSplitProofSystem sp M Λ E hb honest stmtProg qS hS check input).CompiledBySplit sp
      (M.qVerifier Qs b b) where
  stmtAt ω x := (stmtProg x).run ω
  claim ω x π := spbcsSplitClaim M stmtProg ω x π
  stmt_eq _ _ _ _ hc := stmt_of_mem_spbcsSplitClaim M stmtProg hc
  accepted_of_verify H x π h :=
    ((verify_spbcsSplitProofSystem_eq_true_iff sp M Λ E hb honest stmtProg qS hS check input H x
      π).1 h).2

/-- **The prover reads the base component only at the queries of the statement program**: for a
set `S` of points that `stmtProg` never queries, at any oracle, the prover meets
`ProofSystem.ReadsOff sp S`. -/
theorem readsOff_spbcsSplitProofSystem (S : Set (Bits (queryBits k kN kS L)))
    (hq : ∀ x (ω : Bits (queryBits k kN kS L) → Y₁) (z : Bits (queryBits k kN kS L)),
      z ∈ (stmtProg x).trace ω → z ∉ S) :
    (spbcsSplitProofSystem sp M Λ E hb honest stmtProg qS hS check input).ReadsOff sp S := by
  intro x w c H H' hp hS'
  have hprf : prf sp H = prf sp H' := funext hp
  have hbase : (stmtProg x).run (base sp H) = (stmtProg x).run (base sp H') :=
    OracleProg.run_congr (stmtProg x) fun z hz => by
      have hz' := hq x _ z hz
      simp only [base, hS' z hz']
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
    exact congrArg (fun G => ((splitNIProver M Λ E hb honest).prog
      ((stmtProg x).run (base sp H')) y c).run G) hprf

end System

end GordieHowe.Ring
