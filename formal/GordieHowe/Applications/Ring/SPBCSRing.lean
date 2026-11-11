-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.RingSignature.Base
public import GordieHowe.SPBCS.ProverProg
public import GordieHowe.SPBCS.Online
public import GordieHowe.SPBCS.Merkle.LeafHidingAdaptive

@[expose] public section

/-!
# The spBCS proof system of a ring relation

The spBCS compilation `M` of an IOP for the ring relation of a base signer `B`
(`GordieHowe/Model/RingSignature/Base.lean`) as a `RingSignature.ProofSystem` over the quantum
oracle `Bits (queryBits k kN kS L) → XOut k e`, so that `ofBase B (spbcsProofSystem …) adm` is the
ring signature compiled by spBCS. The prover is the compiled honest prover `SPBCS.niProver` run
through `queryEncoding`, its proofs in the format `b` of the format bounds; the verifier is the
acceptance of the compiled verifier `M.qVerifier Qs b b` on the claim of the statement and the
proof, the oracle read through `outEquiv`.

- `spbcsProver M Λ E hb honest`: the prover program `((M.niProver Λ honest E hb).mapOutput some).encode
  queryEncoding`, with uniform coins.
- `spbcsClaim M x π`: the claim `(x, π)` of a statement and a proof in the format (`none` for the
  missing proof).
- `spbcsProofSystem M Λ E hb honest`: the proof system. `prover_spbcsProofSystem`: its prover is
  `spbcsProver`.
  `verify_spbcsProofSystem_eq_true_iff`: it accepts exactly when the compiled
  verifier accepts the claim; `verify_spbcsProofSystem_none`: it rejects the missing proof;
  `stmt_of_mem_spbcsClaim`: the claim's statement is the statement.
- `run_prove_spbcsProofSystem`: a proof of the prover against `H` is the compiled proof `prove` of
  the causal honest prover at the coins, against the oracle `chainOracle H` read off `H`.
  `verify_spbcsProofSystem_of_accepts`: the honest proof is accepted when the composite verifier
  accepts it against `chainOracle H`.
- `verify_ofBase_spbcs`, `run_sign_ofBase_spbcs`: verification and signing of
  `ofBase B (spbcsProofSystem …) adm` in these terms.
-/

namespace GordieHowe.Ring

open Quantum GordieHowe.QROM GordieHowe.SPBCS IOP SPTerm GordieHowe.RingSignature
open scoped ENNReal

section Types

variable {k kN kS L e : ℕ} {ι : Type} {τ : SPTerm ι} {Mg : Merges τ} {nr : ι → ℕ}
  {P : (j : ι) → ProtocolSpec (nr j)} [∀ j i, Fintype ((P j).Challenge i)]
  [∀ j i, DecidableEq ((P j).Challenge i)] [∀ j i, Nonempty ((P j).Challenge i)] {X₀ : Type}

/-- **The types of the spBCS proof systems** of `M` in the format `b` with causal-prover coins `R`:
proofs in the format `b` (or none), and coins the Fiat–Shamir salt with the prover's coins. -/
noncomputable abbrev spbcsPST (M : SPBCS Mg P X₀ k kN kS L e) (b : ℕ) (R : Type) : PSTypes :=
  ⟨M.Response b, SaltedCoins (FiatShamirSalt kS) (M.ProverCoins R)⟩

end Types

variable {k kN kS L e N : ℕ} {TB : BaseTypes} {B : BaseSigner (Bits (queryBits k kN kS L)) (XOut k e) N TB}
  {ι : Type} {τ : SPTerm ι} {Mg : Merges τ} {nr : ι → ℕ}
  {P : (j : ι) → ProtocolSpec (nr j)} [∀ j i, Fintype ((P j).Challenge i)]
  [∀ j i, DecidableEq ((P j).Challenge i)] [∀ j i, Nonempty ((P j).Challenge i)]
  (M : SPBCS Mg P (RingStmt B) k kN kS L e) (Λ : SiteLayout Mg) {b : ℕ}
  [∀ j i, Fintype ((M.comp j).MessageWrite i)] (E : (j : ι) → (M.comp j).Encoder)
  {Vr : RingStmt B → FullTr P τ → Bool} {Qs : ∀ x, M.IOPQueries Vr x}
  (hb : M.FormatBounds Qs b b) {R : Type} [Fintype R] [Nonempty R]
  (honest : RingWit B → R → CausalProver P τ (RingStmt B))

/-- **The compiled honest prover of the ring relation**: the spBCS prover `niProver` at the site
layout `Λ`, its proofs in the format `b` of `hb` (`some`), run through `queryEncoding` against the
quantum oracle. Its coins are the Fiat–Shamir salt, the causal prover's coins and the Merkle salts;
their law is an argument of each statement (`NARG.Prover.uniformLaw` is the uniform one). This is
the prover of the ring layers of `GordieHowe/Applications/Ring/Insider.lean` and
`InsiderStrong.lean`. -/
def spbcsProver :
    NARG.Prover (Bits (queryBits k kN kS L)) (XOut k e) (RingStmt B) (RingWit B) (M.Response b)
      (SaltedCoins (FiatShamirSalt kS) (M.ProverCoins R)) :=
  ((M.niProver Λ honest E hb).mapOutput some).encode queryEncoding

/-- **The claim of a statement and a proof**: `(x, π)` for a proof `π` in the format, none for the
missing proof. -/
def spbcsClaim (x : RingStmt B) (π : M.Response b) : Option (Claim (RingStmt B) M.NIProof) :=
  π.map fun p => ⟨x, p.1⟩

variable [DecidableEq R]

open Classical in
/-- **The spBCS proof system of the ring relation**: proofs in the format `b` (or none), uniform
coins, the prover `spbcsProver`, and the verifier accepting `π` on `x` at the oracle `H` exactly
when the compiled verifier `M.qVerifier Qs b b` accepts the claim `spbcsClaim M x π` against
`outEquiv k e ∘ H` (as the win conditions of `GordieHowe/Applications/Ring/Games.lean` read it). -/
noncomputable def spbcsProofSystem :
    ProofSystem (Bits (queryBits k kN kS L)) (XOut k e) (RingStmt B) (RingWit B)
      (spbcsPST M b R) :=
  ProofSystem.ofProver (spbcsProver M Λ E hb honest)
    fun H x π => decide (∃ c ∈ spbcsClaim M x π, (M.qVerifier Qs b b).Accepted (outEquiv k e ∘ H) c)

omit [∀ j i, Fintype ((M.comp j).MessageWrite i)] [Fintype R] [Nonempty R] [DecidableEq R] in
/-- **The prover of the spBCS proof system is the compiled honest prover** (its coins are
uniform). -/
theorem prover_spbcsProofSystem :
    (spbcsProofSystem M Λ E hb honest).prover = spbcsProver M Λ E hb honest := by
  classical
  exact ProofSystem.prover_ofProver _ _

omit [∀ j i, Fintype ((M.comp j).MessageWrite i)] [Fintype R] [Nonempty R] [DecidableEq R] in
/-- **The spBCS proof system accepts exactly the claims the compiled verifier accepts.** -/
theorem verify_spbcsProofSystem_eq_true_iff (H : Bits (queryBits k kN kS L) → XOut k e)
    (x : RingStmt B) (π : M.Response b) :
    (spbcsProofSystem M Λ E hb honest).verify H x π = true ↔
      ∃ c ∈ spbcsClaim M x π, (M.qVerifier Qs b b).Accepted (outEquiv k e ∘ H) c := by
  classical
  exact decide_eq_true_iff

omit [∀ j i, Fintype ((M.comp j).MessageWrite i)] [Fintype R] [Nonempty R] [DecidableEq R] in
/-- **The spBCS proof system rejects the missing proof.** -/
theorem verify_spbcsProofSystem_none (H : Bits (queryBits k kN kS L) → XOut k e)
    (x : RingStmt B) :
    (spbcsProofSystem M Λ E hb honest).verify H x (none : M.Response b) = false := by
  rw [Bool.eq_false_iff, Ne, verify_spbcsProofSystem_eq_true_iff]
  simp [spbcsClaim]

omit [∀ j i, Fintype ((M.comp j).MessageWrite i)] in
/-- **The statement of a claim is the statement it was formed with.** -/
theorem stmt_of_mem_spbcsClaim {x : RingStmt B} {π : M.Response b}
    {c : Claim (RingStmt B) M.NIProof} (hc : c ∈ spbcsClaim M x π) :
    (M.qVerifier Qs b b).stmt c = x := by
  cases π with
  | none => simp [spbcsClaim] at hc
  | some p =>
    simp only [spbcsClaim, Option.map_some, Option.mem_def, Option.some.injEq] at hc
    subst hc
    rfl

omit [∀ j i, Fintype ((M.comp j).MessageWrite i)] [DecidableEq R] in
/-- **An honest proof is the compiled proof of the causal honest prover**: against the quantum
oracle `H`, the prover of the spBCS proof system outputs a proof in the format whose underlying
proof is `prove` of the causal prover `honest w` at the coins, with the Fiat–Shamir salt and
Merkle salts of the coins, against the oracle `chainOracle H` read off `H`, for a query phase with
view laws `VE`. -/
theorem run_prove_spbcsProofSystem (VE : M.ViewEncoder E Qs)
    (H : Bits (queryBits k kN kS L) → XOut k e) (x : RingStmt B) (w : RingWit B)
    (a : SaltedCoins (FiatShamirSalt kS) (M.ProverCoins R)) :
    ∃ p : M.BProof b, ((spbcsProofSystem M Λ E hb honest).prove x w a).run H = some p ∧
      p.1 = prove (honest w a.coins.iop) x a.salt E a.coins.merkleSalts (chainOracle H) (Qs x) := by
  refine ⟨((M.niProver Λ honest E hb).prog x w a).run (chainOracle H), ?_, ?_⟩
  · change ((((M.niProver Λ honest E hb).mapOutput some).encode queryEncoding).prog x w a).run H = _
    have h := NARG.Prover.toFn_encode_prove queryEncoding ((M.niProver Λ honest E hb).mapOutput some)
      H x w a
    simp only [NARG.Prover.toFn_prove, decode_queryEncoding] at h
    rw [h]
    exact OracleProg.run_mapOutput _ _ _
  · have h := M.toFn_niProver Λ honest E VE hb (chainOracle H) x w a
    simp only [NARG.Prover.toFn_prove] at h
    exact h

omit [∀ j i, Fintype ((M.comp j).MessageWrite i)] [DecidableEq R] in
/-- **The honest proof is accepted when the composite verifier accepts it**: if `M.Accepts`
holds against `chainOracle H` for the compiled proof of the causal honest prover at the coins, the
spBCS proof system accepts the prover's proof at `H`. -/
theorem verify_spbcsProofSystem_of_accepts (VE : M.ViewEncoder E Qs)
    (H : Bits (queryBits k kN kS L) → XOut k e) (x : RingStmt B) (w : RingWit B)
    (a : SaltedCoins (FiatShamirSalt kS) (M.ProverCoins R))
    (hacc : M.Accepts (chainOracle H) x
      (prove (honest w a.coins.iop) x a.salt E a.coins.merkleSalts (chainOracle H) (Qs x)) (Qs x)) :
    (spbcsProofSystem M Λ E hb honest).verify H x
      (((spbcsProofSystem M Λ E hb honest).prove x w a).run H) = true := by
  obtain ⟨p, hp, hpv⟩ := run_prove_spbcsProofSystem M Λ E hb honest VE H x w a
  rw [hp, verify_spbcsProofSystem_eq_true_iff]
  refine ⟨⟨x, p.1⟩, rfl, NARG.Verifier.ofOracle_accepted_of ?_⟩
  rw [hpv]
  exact hacc

/-! ### The ring signature compiled by spBCS -/

variable (adm : KeyRing B.PK N → Prop) [DecidablePred adm]

variable [DecidableEq TB.PK]

omit [∀ j i, Fintype ((M.comp j).MessageWrite i)] [Fintype R] [Nonempty R] [DecidableEq R] in
/-- **Verification of the ring signature compiled by spBCS**: a signature `(y, π)` on `(R, m)`
verifies exactly when the compiled verifier accepts the claim of `(R, m, y)` and `π`. -/
theorem verify_ofBase_spbcs (H : Bits (queryBits k kN kS L) → XOut k e) (Rg : KeyRing B.PK N)
    (m : B.Msg) (s : B.Pub × M.Response b) :
    (ofBase B (spbcsProofSystem M Λ E hb honest) adm).verify H Rg m s = true ↔
      ∃ c ∈ spbcsClaim M ⟨Rg, m, s.1⟩ s.2, (M.qVerifier Qs b b).Accepted (outEquiv k e ∘ H) c :=
  verify_spbcsProofSystem_eq_true_iff M Λ E hb honest H _ s.2

omit [∀ j i, Fintype ((M.comp j).MessageWrite i)] [Fintype R] [Nonempty R] [DecidableEq R] in
/-- **Signing of the ring signature compiled by spBCS**: on a supported ring holding the signer's
key, when the base signer outputs `σ` at its first position `i`, the signature is the public value
`y` of `σ` with the compiled honest prover's proof of `(R, m, y)` with the witness `(i, σ)`. -/
theorem run_sign_ofBase_spbcs {H : Bits (queryBits k kN kS L) → XOut k e} {kp : B.PK × B.SK}
    {Rg : KeyRing B.PK N} (hR : kp.1 ∈ Rg.1) (ha : adm Rg) {m : B.Msg}
    {c : B.Coins × SaltedCoins (FiatShamirSalt kS) (M.ProverCoins R)} {σ : B.BSig}
    (hσ : (B.bsign kp.2 Rg (Rg.1.idxOf kp.1) m c.1).run H = some σ) :
    ((ofBase B (spbcsProofSystem M Λ E hb honest) adm).sign kp Rg m c).run H =
      some ((B.pub kp.1 σ).run H,
        ((spbcsProver M Λ E hb honest).prog ⟨Rg, m, (B.pub kp.1 σ).run H⟩
          ⟨Rg.1.idxOf kp.1, σ⟩ c.2).run H) := by
  erw [sign_ofBase_of_mem B _ adm hR ha]
  exact run_signAt_of_bsign B _ hσ

end GordieHowe.Ring
