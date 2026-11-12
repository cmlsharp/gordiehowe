-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Ring.MLDSAW1Unforgeability
public import GordieHowe.Model.RingSignature.VerifiesBy
public import GordieHowe.Model.NARG.VerifierProg

@[expose] public section

/-!
# The verifier of the spBCS proof system on a split oracle as a query-bounded program

The verifier of `spbcsSplitProofSystem` (`GordieHowe/Applications/Ring/SPBCSSplit.lean`) is the
classical oracle program `spbcsSplitVerifyProg`: when the statement passes `check`, the statement
program `stmtProg x` on the base component, then for a proof `some p` the compiled verifier
`M.qVerifier Qs b b` as a program (`NARG.Verifier.prog`) on the claim `(x₀, p.1)` against the
second component read through `outEquiv`. It makes at most `qS + kq` queries.

- `verifiesBy_spbcsSplitProofSystem`: `ProofSystem.VerifiesBy` with this program and bound.
- `MLDSAW1.verifiesBy_w1PS`: the same for the proof system of the ML-DSA ring publishing `w₁`
  (`MLDSAW1.w1PS`), with `qS = 2 N`.
-/

namespace GordieHowe.Ring

open Quantum GordieHowe.QROM GordieHowe.SPBCS IOP SPTerm GordieHowe.RingSignature GordieHowe.IOP
open GordieHowe.RingSignature.OracleSplit
open scoped ENNReal

section System

variable {k kN kS L e N : ℕ} {Y Y₁ : Type} [AddGroup Y] [AddGroup Y₁]
  (sp : OracleSplit Y Y₁ (XOut k e)) {T : Signature.SchemeTypes} {RMsg : Type}
  {B : BaseSigner (Bits (queryBits k kN kS L)) Y N T RMsg}
  {ι : Type} {τ : SPTerm ι} {Mg : Merges τ} {nr : ι → ℕ}
  {P : (j : ι) → ProtocolSpec (nr j)} [∀ j i, Fintype ((P j).Challenge i)]
  [∀ j i, DecidableEq ((P j).Challenge i)] [∀ j i, Nonempty ((P j).Challenge i)] {X₀ Wit₀ : Type}
  (M : SPBCS Mg P X₀ k kN kS L e) (Λ : SiteLayout Mg) {b : ℕ}
  [∀ j i, Fintype ((M.comp j).MessageWrite i)] (E : (j : ι) → (M.comp j).Encoder)
  {Vr : X₀ → FullTr P τ → Bool} (Qs : ∀ x, M.IOPQueries Vr x)
  (hb : M.FormatBounds Qs b b) {R : Type} [Fintype R] [DecidableEq R] [Nonempty R]
  (honest : Wit₀ → R → CausalProver P τ X₀)
  (stmtProg : RingSignature.RingStmt B → OracleProg (Bits (queryBits k kN kS L)) Y₁ X₀) (qS : ℕ)
  (hS : ∀ x, (stmtProg x).QueriesLE qS) (check : RingSignature.RingStmt B → Bool)
  (input : RingSignature.RingStmt B → RingSignature.RingWit B → Option Wit₀)

/-- **The verifier of the spBCS proof system on a split oracle, as a program**: for a statement
passing `check`, the statement program on the base component, then for a proof `some p` the
compiled verifier's program on the claim `(x₀, p.1)` against the second component; `false`
otherwise. -/
noncomputable def spbcsSplitVerifyProg (x : RingSignature.RingStmt B) (π : M.Response b) :
    OracleProg (Bits (queryBits k kN kS L)) Y Bool :=
  if check x then
    ((stmtProg x).mapQuery id fun y => (sp y).1).bind fun x₀ =>
      π.elim (.pure false) fun p =>
        ((M.qVerifier Qs b b).prog ⟨x₀, p.1⟩).mapQuery id fun y => outEquiv k e (sp y).2
  else .pure false

omit [∀ j i, Fintype ((M.comp j).MessageWrite i)] [Fintype R] [DecidableEq R] [Nonempty R] in
/-- **The verifier of `spbcsSplitProofSystem` is the program `spbcsSplitVerifyProg`**, with at
most `qS + kq` queries. -/
theorem verifiesBy_spbcsSplitProofSystem :
    (spbcsSplitProofSystem sp M Λ E hb honest stmtProg qS hS check input).VerifiesBy
      (spbcsSplitVerifyProg sp M Qs stmtProg check) (qS + (M.qVerifier Qs b b).kq) := by
  refine ⟨fun H x (π : M.Response b) => ?_, fun x (π : M.Response b) => ?_⟩
  · classical
    rw [Bool.eq_iff_iff, verify_spbcsSplitProofSystem_eq_true_iff]
    unfold spbcsSplitVerifyProg
    cases hc : check x
    · simp
    · rcases π with _ | p
      · simp [spbcsSplitClaim]
      · simp only [↓reduceIte, OracleProg.run_bind, OracleProg.run_mapQuery, Option.elim_some,
          NARG.Verifier.run_prog_eq, spbcsSplitClaim, Option.map_some, Option.mem_def,
          Option.some.injEq, exists_eq_left', true_and, decide_eq_true_eq]
        exact Iff.rfl
  · unfold spbcsSplitVerifyProg
    split_ifs
    · refine OracleProg.QueriesLE.bind (fun H => ?_) fun x₀ => ?_
      · rw [OracleProg.length_trace_mapQuery]
        exact hS x _
      · rcases π with _ | p
        · exact OracleProg.QueriesLE.pure _ _
        · intro H
          rw [Option.elim_some, OracleProg.length_trace_mapQuery]
          exact NARG.Verifier.prog_queriesLE _ _ _
    · exact OracleProg.QueriesLE.pure _ _

end System

end GordieHowe.Ring

namespace GordieHowe.Ring.MLDSAW1

open _root_.MLDSA GordieHowe.MLDSA GordieHowe.RingSignature GordieHowe.RingSignature.OracleSplit
open Quantum GordieHowe.QROM GordieHowe.SPBCS IOP SPTerm GordieHowe.IOP
open scoped ENNReal

variable {k kN kS L e : ℕ} {Y Y₁ : Type} [AddGroup Y] [AddGroup Y₁]
  (sp : OracleSplit Y Y₁ (XOut k e)) {p : Params} (prims : Primitives p) {Msg : Type} {N reps : ℕ}
  [NeZero (bucketCount p)] [nttOps : NTTRingOps] [Fintype prims.Power2High]
  [DecidableEq prims.Power2High] [Fintype prims.Hint] [DecidableEq prims.Hint] [Fintype Msg]
  [DecidableEq Msg] (O : W1Oracles (Bits (queryBits k kN kS L)) Y p prims Msg N reps)
  (βmin : ℚ≥0) (tol : ℕ) (enc : Vector prims.High p.k → BucketVec p)
  {CLp : Type} [Fintype CLp] [DecidableEq CLp] [Nonempty CLp] (Lp : W1Loop (Bits (queryBits k kN kS L)) Y p prims Msg N CLp) {RMsg : Type} [Fintype RMsg]
  [DecidableEq RMsg] (bmsg : KeyRing (PubKey p prims) N → RMsg → Msg)
  {ι : Type} {τ : SPTerm ι} {Mg : Merges τ} {nr : ι → ℕ}
  {P : (j : ι) → ProtocolSpec (nr j)} [∀ j i, Fintype ((P j).Challenge i)]
  [∀ j i, DecidableEq ((P j).Challenge i)] [∀ j i, Nonempty ((P j).Challenge i)]
  (M : SPBCS Mg P (W1ExpStmt prims RMsg N) k kN kS L e) (Λ : SiteLayout Mg)
  {b : ℕ} [∀ j i, Fintype ((M.comp j).MessageWrite i)] (E : (j : ι) → (M.comp j).Encoder)
  {Vr : W1ExpStmt prims RMsg N → FullTr P τ → Bool} {Qs : ∀ x, M.IOPQueries Vr x}
  (hb : M.FormatBounds Qs b b) {R : Type} [Fintype R] [DecidableEq R] [Nonempty R]
  (honest : RingSignature.RingWit (w1BaseSigner prims O βmin tol enc Lp bmsg) → R →
    CausalProver P τ (W1ExpStmt prims RMsg N))

omit [NeZero (bucketCount p)]
  [∀ j i, Fintype ((M.comp j).MessageWrite i)] [Fintype R] [DecidableEq R] [Nonempty R] in
/-- **The verifier of the proof system of the ML-DSA ring publishing `w₁` is a program** with
at most `2 N + kq` queries: the members' commitment hashes, then the compiled verifier. -/
theorem verifiesBy_w1PS :
    (w1PS sp prims O βmin tol enc Lp bmsg M Λ E hb honest).VerifiesBy
      (spbcsSplitVerifyProg sp M Qs (w1StmtProg sp prims O bmsg) fun _ => true)
      (2 * N + (M.qVerifier Qs b b).kq) :=
  verifiesBy_spbcsSplitProofSystem sp M Λ E Qs hb honest _ _ _ _ _

end GordieHowe.Ring.MLDSAW1
