-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Ring.SPBCSCompleteness

@[expose] public section

/-!
# The spBCS proof system of another relation, read at ring statements

The spBCS compilation `M` of an IOP over statements `X₀` (a program's statements, which do not
depend on the oracle) as a `RingSignature.ProofSystem` for the ring statements of a base signer
`B` over the compiled oracle: a ring statement `x` is proved as the statement `stmt x` with the
honest input `y` of the ring witness `w` when `input x w = some y`, with the missing proof when
`input x w = none`, and verified as `stmt x` after the statement check `check x`. A partial
`input` serves honest inputs that exist only on the ring relation (a subtype of its pairs). With
`stmt = id`, `check = true` and `input x w = some w` it is `spbcsProofSystem`
(`GordieHowe/Applications/Ring/SPBCSRing.lean`), by `spbcsComapProofSystem_id`. The ring signature of a program
(`GordieHowe/Applications/Ring/ProgramBase.lean`) uses this form: the program's IOP, its
transcript and hence the compiled oracle are fixed before the base signer, whose oracle is the
compiled one.

- `spbcsComapProver`, `spbcsComapClaim`, `spbcsComapProofSystem`: the prover, the claim of a ring
  statement and a proof, and the proof system. `prover_spbcsComapProofSystem`,
  `verify_spbcsComapProofSystem_eq_true_iff`, `verify_spbcsComapProofSystem_none`,
  `stmt_of_mem_spbcsComapClaim`, `run_prove_spbcsComapProofSystem`,
  `verify_spbcsComapProofSystem_of_accepts`: as for `spbcsProofSystem`.
- `spbcsComapProofSystem_completeWithin`: adaptive completeness for the ring relation, when every
  pair of the ring relation at every oracle passes the check and maps to a pair of the IOP's
  relation `rel₀` at an honest input (`hrel`), at error
  `εp + overrun + keyCollision (τ.size nr) k + T / 2^(8 kS)`.
- `spbcsComapProofSystem_id`: `spbcsComapProofSystem` at `stmt = id`, the check accepting every
  statement and `input x w = some w` is `spbcsProofSystem`.
-/

namespace GordieHowe.Ring

open Quantum GordieHowe.QROM GordieHowe.SPBCS IOP SPTerm GordieHowe.RingSignature GordieHowe.IOP
open scoped ENNReal

variable {k kN kS L e N : ℕ} {TB : BaseTypes} {B : BaseSigner (Bits (queryBits k kN kS L)) (XOut k e) N TB}
  {ι : Type} {τ : SPTerm ι} {Mg : Merges τ} {nr : ι → ℕ}
  {P : (j : ι) → ProtocolSpec (nr j)} [∀ j i, Fintype ((P j).Challenge i)]
  [∀ j i, DecidableEq ((P j).Challenge i)] [∀ j i, Nonempty ((P j).Challenge i)] {X₀ Wit₀ : Type}
  (M : SPBCS Mg P X₀ k kN kS L e) (Λ : SiteLayout Mg) {b : ℕ}
  [∀ j i, Fintype ((M.comp j).MessageWrite i)] (E : (j : ι) → (M.comp j).Encoder)
  {Vr : X₀ → FullTr P τ → Bool} {Qs : ∀ x, M.IOPQueries Vr x}
  (hb : M.FormatBounds Qs b b) {R : Type} [Fintype R] [Nonempty R]
  (honest : Wit₀ → R → CausalProver P τ X₀) (stmt : RingStmt B → X₀) (check : RingStmt B → Bool)
  (input : RingStmt B → RingWit B → Option Wit₀)

/-- **The compiled honest prover read at ring statements**: on a ring statement `x` and a ring
witness `w` with the honest input `input x w = some y`, the spBCS prover `niProver` (proofs in the
format `b`, run through `queryEncoding`) on the statement `stmt x` with the honest input `y`; the
missing proof `none`, with no query, when `input x w = none`; uniform coins. -/
noncomputable def spbcsComapProver :
    NARG.Prover (Bits (queryBits k kN kS L)) (XOut k e) (RingStmt B) (RingWit B) (M.Response b)
      (SaltedCoins (FiatShamirSalt kS) (M.ProverCoins R)) where
  prog x w c := (input x w).elim (.pure none) fun y =>
    (((M.niProver Λ honest E hb).mapOutput some).encode queryEncoding).prog (stmt x) y c
  coins := PMF.uniformOfFintype _
  q := (((M.niProver Λ honest E hb).mapOutput some).encode queryEncoding).q
  prog_queries x w c := match input x w with
    | none => OracleProg.QueriesLE.pure _ _
    | some _ =>
      (((M.niProver Λ honest E hb).mapOutput some).encode queryEncoding).prog_queries _ _ c

omit [∀ j i, Fintype ((M.comp j).MessageWrite i)] in
/-- **The claim of a ring statement and a proof**: `(stmt x, π)` for a proof `π` in the format,
none for the missing proof. -/
def spbcsComapClaim (x : RingStmt B) (π : M.Response b) : Option (Claim X₀ M.NIProof) :=
  π.map fun p => ⟨stmt x, p.1⟩

open Classical in
/-- **The spBCS proof system read at ring statements**: the prover `spbcsComapProver`, and the
verifier accepting `π` on `x` at the oracle `H` exactly when `x` passes the check and the compiled
verifier `M.qVerifier Qs b b` accepts the claim `spbcsComapClaim M stmt x π` against
`outEquiv k e ∘ H`. -/
noncomputable def spbcsComapProofSystem :
    ProofSystem (Bits (queryBits k kN kS L)) (XOut k e) (RingStmt B) (RingWit B)
      (spbcsPST M b R) :=
  ProofSystem.ofProver (spbcsComapProver M Λ E hb honest stmt input)
    fun H x π => check x &&
      decide (∃ c ∈ spbcsComapClaim M stmt x π, (M.qVerifier Qs b b).Accepted (outEquiv k e ∘ H) c)

/-- **The prover of the proof system is the compiled honest prover read at ring statements.** -/
theorem prover_spbcsComapProofSystem :
    (spbcsComapProofSystem M Λ E hb honest stmt check input).prover =
      spbcsComapProver M Λ E hb honest stmt input := by
  classical
  exact ProofSystem.prover_ofProver _ _ rfl

/-- **The proof system accepts exactly the checked statements whose claims the compiled verifier
accepts.** -/
theorem verify_spbcsComapProofSystem_eq_true_iff (H : Bits (queryBits k kN kS L) → XOut k e)
    (x : RingStmt B) (π : M.Response b) :
    (spbcsComapProofSystem M Λ E hb honest stmt check input).verify H x π = true ↔
      check x = true ∧
        ∃ c ∈ spbcsComapClaim M stmt x π, (M.qVerifier Qs b b).Accepted (outEquiv k e ∘ H) c := by
  classical
  change (check x && decide _) = true ↔ _
  rw [Bool.and_eq_true, decide_eq_true_iff]

/-- **The proof system rejects the missing proof.** -/
theorem verify_spbcsComapProofSystem_none (H : Bits (queryBits k kN kS L) → XOut k e)
    (x : RingStmt B) :
    (spbcsComapProofSystem M Λ E hb honest stmt check input).verify H x (none : M.Response b) =
      false := by
  rw [Bool.eq_false_iff, Ne, verify_spbcsComapProofSystem_eq_true_iff]
  simp [spbcsComapClaim]

omit [∀ j i, Fintype ((M.comp j).MessageWrite i)] in
/-- **The statement of a claim is the program's statement of the ring statement.** -/
theorem stmt_of_mem_spbcsComapClaim {x : RingStmt B} {π : M.Response b}
    {c : Claim X₀ M.NIProof} (hc : c ∈ spbcsComapClaim M stmt x π) :
    (M.qVerifier Qs b b).stmt c = stmt x := by
  cases π with
  | none => simp [spbcsComapClaim] at hc
  | some p =>
    simp only [spbcsComapClaim, Option.map_some, Option.mem_def, Option.some.injEq] at hc
    subst hc
    rfl

/-- **An honest proof is the compiled proof of the causal honest prover** at the honest input
`y = input x w`, on the statement `stmt x`, against `chainOracle H`, for a query phase with view
laws `VE`. -/
theorem run_prove_spbcsComapProofSystem (VE : M.ViewEncoder E Qs)
    (H : Bits (queryBits k kN kS L) → XOut k e) (x : RingStmt B) (w : RingWit B) {y : Wit₀}
    (hy : input x w = some y) (a : SaltedCoins (FiatShamirSalt kS) (M.ProverCoins R)) :
    ∃ p : M.BProof b,
      ((spbcsComapProofSystem M Λ E hb honest stmt check input).prove x w a).run H = some p ∧
        p.1 = prove (honest y a.coins.iop) (stmt x) a.salt E a.coins.merkleSalts
          (chainOracle H) (Qs (stmt x)) := by
  refine ⟨((M.niProver Λ honest E hb).prog (stmt x) y a).run (chainOracle H), ?_, ?_⟩
  · change ((input x w).elim (.pure none) (fun y =>
      (((M.niProver Λ honest E hb).mapOutput some).encode queryEncoding).prog (stmt x) y a)).run H = _
    rw [hy, Option.elim_some]
    have h := NARG.Prover.toFn_encode_prove queryEncoding ((M.niProver Λ honest E hb).mapOutput some)
      H (stmt x) y a
    simp only [NARG.Prover.toFn_prove, decode_queryEncoding] at h
    rw [h]
    exact OracleProg.run_mapOutput _ _ _
  · have h := M.toFn_niProver Λ honest E VE hb (chainOracle H) (stmt x) y a
    simp only [NARG.Prover.toFn_prove] at h
    exact h

/-- **The honest proof of a checked statement at an honest input `y = input x w` is accepted when
the composite verifier accepts it** against `chainOracle H`. -/
theorem verify_spbcsComapProofSystem_of_accepts (VE : M.ViewEncoder E Qs)
    (H : Bits (queryBits k kN kS L) → XOut k e) (x : RingStmt B) (w : RingWit B) {y : Wit₀}
    (hy : input x w = some y) (a : SaltedCoins (FiatShamirSalt kS) (M.ProverCoins R))
    (hx : check x = true)
    (hacc : M.Accepts (chainOracle H) (stmt x)
      (prove (honest y a.coins.iop) (stmt x) a.salt E a.coins.merkleSalts (chainOracle H)
        (Qs (stmt x))) (Qs (stmt x))) :
    (spbcsComapProofSystem M Λ E hb honest stmt check input).verify H x
      (((spbcsComapProofSystem M Λ E hb honest stmt check input).prove x w a).run H) = true := by
  obtain ⟨p, hp, hpv⟩ :=
    run_prove_spbcsComapProofSystem M Λ E hb honest stmt check input VE H x w hy a
  rw [hp, verify_spbcsComapProofSystem_eq_true_iff]
  refine ⟨hx, ⟨stmt x, p.1⟩, rfl, NARG.Verifier.ofOracle_accepted_of ?_⟩
  rw [hpv]
  exact hacc

/-- **The spBCS proof system read at ring statements is adaptively complete for the ring
relation**: if every pair `(x, w)` of the ring relation at every oracle passes the check and has an
honest input `y ∈ input x w` with `(stmt x, y)` in `rel₀` (`hrel`), and the composite verifier rejects the run of the
causal honest prover on a pair of `rel₀` with probability at most `εp` over uniform coins and
challenges (`hε`), then against every program with `T` queries the error is
`εp + overrun + keyCollision (τ.size nr) k + T / 2^(8 kS)`, for a query phase with view laws `VE`. -/
theorem spbcsComapProofSystem_completeWithin (adm : KeyRing B.PK N → Prop)
    (VE : M.ViewEncoder E Qs) {rel₀ : X₀ → Wit₀ → Prop}
    (hrel : ∀ (H : Bits (queryBits k kN kS L) → XOut k e) (p : RingStmt B × RingWit B),
      p ∈ ringRel B adm H → check p.1 = true ∧ ∃ y ∈ input p.1 p.2, rel₀ (stmt p.1) y)
    {εp : ℝ≥0∞}
    (hε : ∀ x w, rel₀ x w → Pr[q ← R × Chs P τ : Vr x ((honest w q.1).run x q.2) ≠ true] ≤ εp) :
    (spbcsComapProofSystem M Λ E hb honest stmt check input).CompleteWithin (ringRel B adm)
      fun T => εp + M.overrun + SPBCS.keyCollision (τ.size nr) k + T / 2 ^ (8 * kS) := by
  classical
  intro T C _ _ G hG
  have hcard : (Fintype.card (FiatShamirSalt kS) : ℝ≥0∞) = 2 ^ (8 * kS) := by
    rw [show Fintype.card (FiatShamirSalt kS) = 2 ^ (8 * kS) from Out.card_digest]
    push_cast
    rfl
  let Bad : M.ProverCoins R → FiatShamirSalt kS → (Bits (queryBits k kN kS L) → XOut k e) →
      Option (RingStmt B × RingWit B) → Prop := fun r σ H o =>
    ∃ p, o = some p ∧ ∃ y ∈ input p.1 p.2, rel₀ (stmt p.1) y ∧
      ¬ M.Accepts (chainOracle H) (stmt p.1)
        (prove (honest y r.iop) (stmt p.1) σ E r.merkleSalts (chainOracle H) (Qs (stmt p.1)))
        (Qs (stmt p.1))
  have hslice : ∀ σ g o, Pr[q ← M.ProverCoins R × (Bits (queryBits k kN kS L) → XOut k e) :
      Bad q.1 σ (replaceSlice M.saltOfBits σ g q.2) o] ≤
        εp + M.overrun + SPBCS.keyCollision (τ.size nr) k := by
    intro σ g o
    rcases o with _ | p
    · rw [QROM.probUniform_eq_zero fun q hq => by obtain ⟨p, hp, -⟩ := hq; exact absurd hp (by simp)]
      exact zero_le
    · rcases hin : input p.1 p.2 with _ | y
      · rw [QROM.probUniform_eq_zero fun q hq => by
          obtain ⟨p', hp', y', hy', -⟩ := hq
          obtain rfl := Option.some.inj hp'
          rw [hin] at hy'
          exact absurd hy' (by simp)]
        exact zero_le
      refine (QROM.probUniform_mono fun q hq => ?_).trans
        (freshSlice_coins_comp_toBits (saltQ := M.querySalt) M.saltOfBits_toBits
          (Bad := fun (c : M.ProverCoins R) σ h (o : ProofQuery X₀ Wit₀) =>
            rel₀ o.stmt o.wit ∧ ¬ M.Accepts h o.stmt
              (prove (honest o.wit c.iop) o.stmt σ E c.merkleSalts h (Qs o.stmt)) (Qs o.stmt))
          (prob_not_accepts_prove_proverCoins_replaceSlice_le M honest E Qs hε) σ g
          ⟨stmt p.1, y⟩)
      obtain ⟨p', hp', y', hy', hr, hna⟩ := hq
      obtain rfl := Option.some.inj hp'
      rw [hin, Option.mem_def, Option.some.injEq] at hy'
      subst hy'
      exact ⟨hr, hna⟩
  let eqv : C × (M.ProverCoins R × (FiatShamirSalt kS × (Bits (queryBits k kN kS L) → XOut k e))) ≃
      (Bits (queryBits k kN kS L) → XOut k e) × C ×
        SaltedCoins (FiatShamirSalt kS) (M.ProverCoins R) :=
    { toFun := fun z => (z.2.2.2, z.1, ⟨z.2.2.1, z.2.1⟩)
      invFun := fun d => (d.2.1, d.2.2.coins, d.2.2.salt, d.1)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  change probUniform _ (fun d : (Bits (queryBits k kN kS L) → XOut k e) × C ×
      SaltedCoins (FiatShamirSalt kS) (M.ProverCoins R) =>
    ∃ p, (G d.2.1).run d.1 = some p ∧ p ∈ ringRel B adm d.1 ∧
      (spbcsComapProofSystem M Λ E hb honest stmt check input).verify d.1 p.1
        (((spbcsComapProofSystem M Λ E hb honest stmt check input).prove p.1 p.2 d.2.2).run d.1) =
          false) ≤ _
  refine (QROM.probUniform_mono (E' := fun d => Bad d.2.2.coins d.2.2.salt d.1 ((G d.2.1).run d.1))
    fun d hd => ?_).trans ?_
  · obtain ⟨p, hp, hrel', hv⟩ := hd
    obtain ⟨hx, y, hy, h₀⟩ := hrel d.1 p hrel'
    refine ⟨p, hp, y, hy, h₀, fun hacc => ?_⟩
    rw [verify_spbcsComapProofSystem_of_accepts M Λ E hb honest stmt check input VE d.1 p.1 p.2
      hy d.2.2 hx hacc] at hv
    exact Bool.noConfusion hv
  · rw [← QROM.probUniform_equiv eqv]
    refine ROM.probUniform_prod_le fun c => ?_
    rw [ROM.probUniform_prod_eq_sum]
    refine ((G c).prob_bad_coins_le M.saltOfBits (hG c) hslice).trans_eq ?_
    rw [hcard]

end GordieHowe.Ring

/-! ### `spbcsProofSystem` as a special case -/

namespace GordieHowe.Ring

open GordieHowe.QROM GordieHowe.SPBCS IOP GordieHowe.RingSignature

variable {k kN kS L e N : ℕ} {TB : BaseTypes} {B : BaseSigner (Bits (queryBits k kN kS L)) (XOut k e) N TB}
  {ι : Type} {τ : SPTerm ι} {Mg : Merges τ} {nr : ι → ℕ}
  {P : (j : ι) → ProtocolSpec (nr j)} [∀ j i, Fintype ((P j).Challenge i)]
  [∀ j i, DecidableEq ((P j).Challenge i)] [∀ j i, Nonempty ((P j).Challenge i)]
  (M : SPBCS Mg P (RingStmt B) k kN kS L e) (Λ : SiteLayout Mg) {b : ℕ}
  [∀ j i, Fintype ((M.comp j).MessageWrite i)] (E : (j : ι) → (M.comp j).Encoder)
  {Vr : RingStmt B → FullTr P τ → Bool} {Qs : ∀ x, M.IOPQueries Vr x}
  (hb : M.FormatBounds Qs b b) {R : Type} [Fintype R] [Nonempty R]
  (honest : RingWit B → R → CausalProver P τ (RingStmt B))

/-- **`spbcsProofSystem` is `spbcsComapProofSystem` at the ring statements themselves**: the
identity statement map, the check accepting every statement and the ring witness as the honest
input. -/
theorem spbcsComapProofSystem_id :
    spbcsComapProofSystem M Λ E hb honest id (fun _ => true) (fun _ w => some w) =
      spbcsProofSystem M Λ E hb honest :=
  rfl

end GordieHowe.Ring
