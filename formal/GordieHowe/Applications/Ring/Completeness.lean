-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Ring.Scheme
public import GordieHowe.SPBCS.Theorems

@[expose] public section

/-!
# Completeness of the ring signature

An honest ring signature verifies (BKM06 Definition 1, ePrint 2005/304, p. 3, correctness: for
every honestly generated key at a position of the ring, `Vrfy_R(M, Sign(M, R)) = 1`), up to the
base scheme's correctness error and the completeness error of the compiled argument.

- `signStmt`, `signWit`: the statement `(R, m, pub σ)` and the witness `(i, σ)` of the ring
  signature by the key of the coins `kc` at position `i`, `σ` signed with the signing coins `c`.
- `ringRejectProb`: the probability, over the signing coins, the honest prover's coins and the
  oracle, that the compiled verifier rejects the honest ring signature (at fixed Merkle salts and
  Fiat–Shamir salt).
- `ringRejectProb_le`: it is at most `εc + εp + overrun + keyCollision` for a scheme with
  correctness error `εc` (`SigScheme.CorrectWithin`) and the spBCS completeness guarantees with
  error `εp` for the ring relation (`SPBCS.CompletenessGuarantees`, paper `thm:bcs-complete`), on an
  admissible ring holding the signer's key.
-/

namespace GordieHowe.Ring

open IOP GordieHowe.SPBCS GordieHowe.QROM IOP.SPTerm
open scoped ENNReal NNReal

variable {Sch : SigScheme} {RMsg : Type} {N : ℕ} (bind : List Sch.PK → RMsg → Sch.Msg)

/-- **The statement of an honest ring signature**: the ring, the message and the public value of
the base signature of the key of `kc` on `bind R m` with the signing coins `c`. -/
def signStmt (kc : Sch.KeyCoins) (R : RingOf Sch.PK N) (m : RMsg) (c : Sch.SignCoins) :
    RingStmt Sch RMsg N :=
  ⟨R, m, Sch.pub (Sch.signWith (Sch.sk kc) (bind R.1 m) c)⟩

/-- **The witness of an honest ring signature**: the signer's position `i` and the base
signature. -/
def signWit (kc : Sch.KeyCoins) (R : RingOf Sch.PK N) (m : RMsg) (i : ℕ) (c : Sch.SignCoins) :
    RingWit Sch :=
  ⟨i, Sch.signWith (Sch.sk kc) (bind R.1 m) c⟩

variable [Fintype Sch.SignCoins] [Nonempty Sch.SignCoins]

variable {k kN kS L e : ℕ} {ι : Type} {τ : SPTerm ι} {Mg : Merges τ} {nr : ι → ℕ}
  {P : (j : ι) → ProtocolSpec (nr j)} [∀ j i, Fintype ((P j).Challenge i)]
  [∀ j i, DecidableEq ((P j).Challenge i)] [∀ j i, Nonempty ((P j).Challenge i)]
  (M : SPBCS Mg P (RingStmt Sch RMsg N) k kN kS L e) (E : (j : ι) → (M.comp j).Encoder)
  {V : RingStmt Sch RMsg N → FullTr P τ → Bool} (Qs : ∀ x, M.IOPQueries V x) {R : Type}
  [Fintype R] [DecidableEq R] [Nonempty R]
  (honest : RingWit Sch → R → CausalProver P τ (RingStmt Sch RMsg N))

/-- **The probability that an honest ring signature is rejected**: the member with the key of `kc`
at position `i` of the ring `R` signs `m`, its base signature drawn with uniform signing coins and
its proof by the compiled honest prover with uniform coins, at the Merkle salts `ν` and the
Fiat–Shamir salt `σ`, under a uniform oracle; the compiled verifier rejects on the statement
`signStmt`. -/
noncomputable def ringRejectProb (kc : Sch.KeyCoins) (Rg : RingOf Sch.PK N) (m : RMsg) (i : ℕ)
    (ν : M.Pos → MerkleSalt kN) (σ : FiatShamirSalt kS) : ℝ≥0∞ :=
  Pr[q ← (Sch.SignCoins × (R × (Query k kN kS L → Out k e))) :
    ¬ M.Accepts q.2.2 (signStmt bind kc Rg m q.1)
      (prove (honest (signWit bind kc Rg m i q.1) q.2.1) (signStmt bind kc Rg m q.1) σ E ν q.2.2
        (Qs (signStmt bind kc Rg m q.1))) (Qs (signStmt bind kc Rg m q.1))]

omit [DecidableEq R] in
/-- **Completeness of the ring signature** (BKM06 Definition 1, correctness): on an admissible ring
(`hadm`) holding the key of `kc` at position `i` (`hi`, `hR`), the honest ring signature is
rejected with probability at most the base scheme's correctness error `εc` (`hcorr`: the base
signature fails to verify) plus the completeness error of spBCS for the ring relation (`hG`, at
error `εp`, with the overrun and key-collision terms of `SPBCS.CompletenessGuarantees`), at every
Merkle salts and Fiat–Shamir salt. -/
theorem ringRejectProb_le {adm : List Sch.PK → Prop} {εc εp : ℝ≥0∞} (hcorr : Sch.CorrectWithin εc)
    (hG : M.CompletenessGuarantees E Qs honest (ringRel adm bind) εp) {kc : Sch.KeyCoins}
    {Rg : RingOf Sch.PK N} {m : RMsg} {i : ℕ} (hadm : adm Rg.1) (hi : i < Rg.1.length)
    (hR : Rg.1[i] = Sch.pk kc) (ν : M.Pos → MerkleSalt kN) (σ : FiatShamirSalt kS) :
    ringRejectProb bind M E Qs honest kc Rg m i ν σ ≤
      εp + M.overrun + SPBCS.keyCollision (τ.size nr) k + εc := by
  refine (probUniform_prod_le_add _
    (fun c => Sch.verify (Sch.pk kc) (bind Rg.1 m) (Sch.signWith (Sch.sk kc) (bind Rg.1 m) c) ≠ true)
    fun c hc => ?_).trans (add_le_add le_rfl (hcorr kc (bind Rg.1 m)))
  exact hG.completeness _ _ ν σ ⟨hadm, RingRel.of_signWith hi hR (not_not.1 hc)⟩

end GordieHowe.Ring
