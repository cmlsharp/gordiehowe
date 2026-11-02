-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Ring.SPBCSSplit
public import GordieHowe.Model.RingSignature.WithVerify

@[expose] public section

/-!
# The split spBCS proof system with the empty ring rejected

The ring scheme `ofBase B PS adm` of the split spBCS proof system `PS` with the check `check`, and
the scheme of the same proof system with a check `check'` accepting every statement that `check`
accepts and whose ring is nonempty (for example `check x && decide (x.ring.1 ≠ [])`): the two
schemes differ in their verifier only, so their unforgeability games have the same run
(`RingSignature.forgeProb_le_withVerify`). A forgery against the first scheme is a forgery against
the second or a forgery on the empty ring.

- `verify_spbcsSplit_check`: the second scheme accepts what the first accepts on a nonempty ring.
- `insiderForgeProb_le_spbcsSplit_check`: BKM06 Definition 7 for the first scheme is at most that
  for the second, for the adversary relabelled (`UnforgeAdversary.withVerify`), plus the forgery
  probability on the empty ring.
- `keyReuseForgeProb_le_spbcsSplit_check`: the same in the key-reuse game.
-/

namespace GordieHowe.Ring

open Quantum GordieHowe.QROM GordieHowe.SPBCS IOP SPTerm GordieHowe.RingSignature GordieHowe.IOP
open GordieHowe.RingSignature.OracleSplit
open scoped ENNReal

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
  (hS : ∀ x, (stmtProg x).QueriesLE qS) {check : RingSignature.RingStmt B → Bool}
  (check' : RingSignature.RingStmt B → Bool)
  (input : RingSignature.RingStmt B → RingSignature.RingWit B → Option Wit₀)
  {adm : KeyRing B.PK N → Prop} [DecidablePred adm]

/-- **The scheme with the check `check'` accepts what the scheme with `check` accepts on a
nonempty ring**, when `check'` accepts the statements with a nonempty ring that `check` accepts
(`hc`). -/
theorem verify_spbcsSplit_check
    (hc : ∀ x, check x = true → x.ring.1 ≠ [] → check' x = true) :
    ∀ H R m σ,
      (ofBase B (spbcsSplitProofSystem sp M Λ E hb honest stmtProg qS hS check input) adm).verify
          H R m σ = true → ¬ R.1 = [] →
        (ofBase B (spbcsSplitProofSystem sp M Λ E hb honest stmtProg qS hS check' input)
          adm).verify H R m σ = true := by
  intro H R m σ h hR
  have h' := (verify_spbcsSplitProofSystem_eq_true_iff sp M Λ E hb honest stmtProg qS hS check input
    H ⟨R, m, σ.1⟩ σ.2).1 h
  exact (verify_spbcsSplitProofSystem_eq_true_iff sp M Λ E hb honest stmtProg qS hS check' input
    H ⟨R, m, σ.1⟩ σ.2).2 ⟨hc _ h'.1 hR, h'.2⟩

variable [Fintype Y] [DecidableEq Y] [Nonempty Y] {n : ℕ} [NeZero n]
  {V : RingSignature.OracleView (Bits (queryBits k kN kS L)) Y} {t : ℕ}

/-- **BKM06 Definition 7 with the empty ring rejected** (`insiderForgeProb_le_withVerify`): for a
check `check'` accepting the statements with a nonempty ring that `check` accepts (`hc`), the
forgery probability of an adversary against the scheme of the split spBCS proof system with
`check` is at most that of the relabelled adversary against the scheme with `check'`, plus the
probability of a forgery on the empty ring. -/
theorem insiderForgeProb_le_spbcsSplit_check
    (hc : ∀ x, check x = true → x.ring.1 ≠ [] → check' x = true)
    (A : InsiderAdversary
      (ofBase B (spbcsSplitProofSystem sp M Λ E hb honest stmtProg qS hS check input) adm) n V t)
    (Q : ℕ) :
    insiderForgeProb A Q ≤
      insiderForgeProb
          (S := ofBase B (spbcsSplitProofSystem sp M Λ E hb honest stmtProg qS hS check' input) adm)
          (UnforgeAdversary.withVerify
            (S := ofBase B
              (spbcsSplitProofSystem sp M Λ E hb honest stmtProg qS hS check input) adm)
            (ofBase B (spbcsSplitProofSystem sp M Λ E hb honest stmtProg qS hS check' input)
              adm).verify (SideOracle.none _) A) Q +
        forgeProbOn A Q (fun o => o.1.1 = []) :=
  insiderForgeProb_le_withVerify _ (verify_spbcsSplit_check sp M Λ E hb honest stmtProg qS hS
    check' input hc) A Q

/-- **The key-reuse game with the empty ring rejected** (`forgeProb_le_withVerify`): for a check
`check'` accepting the statements with a nonempty ring that `check` accepts (`hc`), the forgery
probability of an adversary of the key-reuse game of the scheme of the split spBCS proof system
with `check` is at most that of the relabelled adversary in the key-reuse game of the scheme with
`check'`, plus the probability of a forgery on the empty ring. -/
theorem keyReuseForgeProb_le_spbcsSplit_check
    (hc : ∀ x, check x = true → x.ring.1 ≠ [] → check' x = true)
    (A : KeyReuseAdversary B (spbcsSplitProofSystem sp M Λ E hb honest stmtProg qS hS check input)
      adm n V t)
    (Q : ℕ) :
    keyReuseForgeProb A Q ≤
      keyReuseForgeProb
          (PS := spbcsSplitProofSystem sp M Λ E hb honest stmtProg qS hS check' input)
          (UnforgeAdversary.withVerify
            (S := ofBase B
              (spbcsSplitProofSystem sp M Λ E hb honest stmtProg qS hS check input) adm)
            (ofBase B (spbcsSplitProofSystem sp M Λ E hb honest stmtProg qS hS check' input)
              adm).verify _ A) Q +
        forgeProbOn A Q (fun o => o.1.1 = []) :=
  forgeProb_le_withVerify _ (verify_spbcsSplit_check sp M Λ E hb honest stmtProg qS hS
    check' input hc) A Q

end GordieHowe.Ring
