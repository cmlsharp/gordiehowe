-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.SPBCS.CompleteAdaptive
public import GordieHowe.SPBCS.Online
public import GordieHowe.SPBCS.ZeroKnowledge
public import GordieHowe.SPBCS.ProverProg

@[expose] public section

/-!
# Completeness of the spBCS compiler as a non-interactive argument

Completeness in the form of Unruh 2017 (ePrint 2017/398), Definition 5, p. 14 (the statement and
witness chosen by an adversary after querying the oracle, then proved by the honest prover with
fresh coins), for the spBCS compiler (`GordieHowe/SPBCS/Basic.lean`), paper `thm:bcs-complete` (2),
stated as the model-level notions `GordieHowe.NARG.ROM.Complete` and `GordieHowe.NARG.QROM.Complete`
(the paper's `def:narg-complete`) at the honest prover `niProver` (run through `queryEncoding` in
the quantum random-oracle model) and the verifiers `toRVerifier`, `toQVerifier`, the claim reading
the prover's proof in the format. The honest prover draws all its coins uniformly after the
adversary: the causal prover's coins, a Merkle salt per position and the Fiat–Shamir salt.

- `prob_not_accepts_prove_proverCoins_replaceSlice_le`: the fresh-slice bound
  `ε + overrun + keyCollision (t.size n) k` at uniform coins and Merkle salts, from the fixed-salt
  bound `prob_not_accepts_prove_replaceSlice_le` at every value of the coins and the salts,
  averaged; the Merkle salts do not enter the bound;
- `complete_rom`: error `ε + overrun + keyCollision (t.size n) k + T / 2^(8kS)` at `T` queries, from
  the generic `GordieHowe.ROM.QueryBoundedAdversary.adaptiveCompleteness_coins`;
- `complete_qrom`: error `ε + overrun + keyCollision (t.size n) k + 2 T / 2^(4kS)`, from
  `GordieHowe.QROM.QueryBoundedAdversary.adaptiveCompleteness_coins`.
-/

namespace GordieHowe.SPBCS

open GordieHowe.QROM GordieHowe.IOP IOP.SPTerm
open GordieHowe.QROM (replaceSlice ProofQuery)
open scoped ENNReal NNReal

variable {ι : Type} {k kN kS L e : ℕ} {t : SPTerm ι} {Mg : Merges t} {n : ι → ℕ}
  {P : (j : ι) → ProtocolSpec (n j)} [∀ j i, Fintype ((P j).Challenge i)]
  [∀ j i, DecidableEq ((P j).Challenge i)] [∀ j i, Nonempty ((P j).Challenge i)] {X : Type}
  (M : SPBCS Mg P X k kN kS L e) {Wit : Type} {R : Type} [Fintype R] [Nonempty R]
  (prv : Wit → R → CausalProver P t X) (E : (j : ι) → (M.comp j).Encoder)
  {V : X → FullTr P t → Bool} (Q : (x : X) → M.IOPQueries V x)

omit [∀ j i, Nonempty ((P j).Challenge i)] in
/-- **An event of the causal prover's coins has the same probability over the honest prover's
coins**: the Merkle salts drawn with them are not read. -/
theorem probUniform_proverCoins_iop {C : Type} [Fintype C] [Nonempty C]
    (p : R → C → Prop) :
    Pr[q ← M.ProverCoins R × C : p q.1.iop q.2] = Pr[q ← R × C : p q.1 q.2] := by
  let eq : (R × C) × (M.Pos → MerkleSalt kN) ≃ M.ProverCoins R × C :=
    { toFun a := (⟨a.1.1, a.2⟩, a.1.2)
      invFun q := ((q.1.iop, q.2), q.1.merkleSalts)
      left_inv _ := rfl
      right_inv _ := rfl }
  rw [← QROM.probUniform_equiv eq (fun q => p q.1.iop q.2)]
  exact QROM.probUniform_prod_fst (fun q : R × C => p q.1 q.2)

omit [∀ j i, Nonempty ((P j).Challenge i)] in
/-- **The coins of the honest spBCS prover are uniform**, as their two parts. -/
theorem uniform_saltedCoins_apply (c : SaltedCoins (FiatShamirSalt kS) (M.ProverCoins R)) :
    PMF.uniformOfFintype (SaltedCoins (FiatShamirSalt kS) (M.ProverCoins R)) c =
      (Fintype.card (M.ProverCoins R) : ℝ≥0∞)⁻¹ *
        (Fintype.card (FiatShamirSalt kS) : ℝ≥0∞)⁻¹ := by
  rw [PMF.uniformOfFintype_apply, Fintype.card_congr (SaltedCoins.equivProd _ _),
    Fintype.card_prod, Nat.cast_mul, mul_comm,
    ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _)) (Or.inl (ENNReal.natCast_ne_top _))]

variable {rel : X → Wit → Prop}

open Classical in
/-- **The fresh-slice bound of the adaptive rejection event at uniform coins and Merkle salts**:
for every salt `σ`, oracle `g` and proof query `o`, the proof query is in `rel` and the compiled
verifier rejects the honest proof of `o.stmt` by `prv o.wit c.iop` with the Merkle salts
`c.merkleSalts` with probability at most `ε + overrun + keyCollision (t.size n) k`, over uniform
coins `c` and a fresh slice of `σ`, when the composite verifier rejects the run of `prv w r` with
probability at most `ε` over uniform coins and challenges for every pair in `rel`
(`prob_not_accepts_prove_replaceSlice_le` at each value of the coins and the salts, averaged; the
event is empty off `rel`). -/
theorem prob_not_accepts_prove_proverCoins_replaceSlice_le {ε : ℝ≥0∞}
    (hε : ∀ x w, rel x w → Pr[q ← R × Chs P t : V x ((prv w q.1).run x q.2) ≠ true] ≤ ε)
    (σ : FiatShamirSalt kS) (g : Query k kN kS L → Out k e) (o : ProofQuery X Wit) :
    Pr[q ← M.ProverCoins R × (Query k kN kS L → Out k e) :
        rel o.stmt o.wit ∧ ¬ M.Accepts (replaceSlice M.querySalt σ g q.2) o.stmt
          (prove (prv o.wit q.1.iop) o.stmt σ E q.1.merkleSalts (replaceSlice M.querySalt σ g q.2)
            (Q o.stmt)) (Q o.stmt)] ≤
      ε + M.overrun + SPBCS.keyCollision (t.size n) k := by
  by_cases ho : rel o.stmt o.wit
  · rw [ROM.probUniform_prod_eq_sum]
    refine (ROM.sum_inv_card_mul_le_add fun c =>
      ((QROM.probUniform_mono fun F hF => hF.2).trans
        (prob_not_accepts_prove_replaceSlice_le (prv o.wit c.iop) o.stmt σ E c.merkleSalts
          (Q o.stmt) g le_rfl)).trans_eq (add_assoc _ _ _)).trans ?_
    rw [← ROM.probUniform_prod_eq_sum
      (fun q : M.ProverCoins R × Chs P t => V o.stmt ((prv o.wit q.1.iop).run o.stmt q.2) ≠ true),
      probUniform_proverCoins_iop M (fun r ch => V o.stmt ((prv o.wit r).run o.stmt ch) ≠ true),
      add_assoc]
    gcongr
    exact hε _ _ ho
  · rw [QROM.probUniform_eq_zero fun q hq => ho hq.1]
    exact zero_le

variable (rel)

open Classical in
/-- **Completeness of the spBCS compiler in the classical random-oracle model**
(`def:narg-complete`, `NARG.ROM.Complete`; paper `thm:bcs-complete` (2); Unruh 2017 Definition 5,
p. 14): if for every pair `(x, w) ∈ rel` the composite verifier rejects the run of the causal
prover `prv w r` with probability at most `ε` over uniform coins `r` and uniform challenges (the
completeness error of `def:iop-complete`), the honest prover `niProver`, with uniform coins,
Merkle salts and Fiat–Shamir salt, is complete for the verifier `toRVerifier` with `kq` queries at
error `ε + overrun + keyCollision (t.size n) k + T / 2^(8kS)` against classical `T`-query
adversaries. -/
theorem complete_rom (Λ : SiteLayout Mg) (VE : M.ViewEncoder E Q) {B : ℕ}
    (hb : M.FormatBounds Q B B) {ε : ℝ≥0∞}
    (hε : ∀ x w, rel x w → Pr[q ← R × Chs P t : V x ((prv w q.1).run x q.2) ≠ true] ≤ ε) (kq : ℕ) :
    NARG.ROM.Complete (M.niProver Λ prv E hb) (M.toRVerifier Q kq) (fun x π => Claim.mk x π.val) rel
      fun T => ε + M.overrun + SPBCS.keyCollision (t.size n) k + T / 2 ^ (8 * kS) := by
  intro T 𝒜
  have hcard : (Fintype.card (FiatShamirSalt kS) : ℝ≥0∞) = 2 ^ (8 * kS) := by
    rw [show Fintype.card (FiatShamirSalt kS) = 2 ^ (8 * kS) from Out.card_digest]
    push_cast
    rfl
  beta_reduce
  rw [← hcard]
  refine le_trans ?_ (𝒜.adaptiveCompleteness_coins M.querySalt (R := M.ProverCoins R)
    (Bad := fun (c : M.ProverCoins R) σ h (o : ProofQuery X Wit) =>
      rel o.stmt o.wit ∧ ¬ M.Accepts h o.stmt
      (prove (prv o.wit c.iop) o.stmt σ E c.merkleSalts h (Q o.stmt)) (Q o.stmt))
    (prob_not_accepts_prove_proverCoins_replaceSlice_le M prv E Q hε))
  unfold NARG.ROM.Adversary.rejectsHonest
  refine ENNReal.tsum_le_tsum fun a => mul_le_mul_of_nonneg_left ?_ zero_le
  rw [tsum_fintype, ← Equiv.sum_comp (SaltedCoins.equivProd _ _).symm, Fintype.sum_prod_type,
    Finset.sum_comm]
  refine Finset.sum_le_sum fun c _ => ?_
  rw [ROM.probUniform_prod_eq_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun σ _ => ?_
  rw [show (M.niProver Λ prv E hb).coins = PMF.uniformOfFintype _ from rfl,
    uniform_saltedCoins_apply, mul_assoc]
  gcongr
  refine QROM.probUniform_mono fun h hh => ?_
  simp only [M.toFn_niProver Λ prv E VE hb] at hh
  change rel (((𝒜.alg a).toAlg T).output h).stmt (((𝒜.alg a).toAlg T).output h).wit ∧
    ¬ M.Accepts h (((𝒜.alg a).toAlg T).output h).stmt
      (prove (prv (((𝒜.alg a).toAlg T).output h).wit c.iop) (((𝒜.alg a).toAlg T).output h).stmt σ
        E c.merkleSalts h (Q (((𝒜.alg a).toAlg T).output h).stmt))
      (Q (((𝒜.alg a).toAlg T).output h).stmt)
  rw [(𝒜.alg a).output_toAlg ((𝒜.alg a).steps_le (𝒜.budget a))]
  exact ⟨hh.1, fun hv => hh.2 (NARG.Verifier.ofOracle_accepted_of hv)⟩

open Classical in
/-- **Completeness of the spBCS compiler in the quantum random-oracle model**
(`def:narg-complete`, `NARG.QROM.Complete`; paper `thm:bcs-complete` (2); Unruh 2017 Definition 5,
p. 14): under the hypothesis of `complete_rom`, the honest prover `niProver` run through `queryEncoding`, with uniform
coins, Merkle salts and Fiat–Shamir salt, is complete for the verifier `toQVerifier` with `kq`
queries at error `ε + overrun + keyCollision (t.size n) k + 2 T / 2^(4kS)` against `T`-query
adversaries of `def:adversary`. -/
theorem complete_qrom (Λ : SiteLayout Mg) (VE : M.ViewEncoder E Q) {B : ℕ}
    (hb : M.FormatBounds Q B B) {ε : ℝ≥0∞}
    (hε : ∀ x w, rel x w → Pr[q ← R × Chs P t : V x ((prv w q.1).run x q.2) ≠ true] ≤ ε) (kq : ℕ) :
    NARG.QROM.Complete queryEncoding (M.niProver Λ prv E hb) (M.toQVerifier Q kq)
      (fun x π => Claim.mk x π.val) rel
      fun T => ε + M.overrun + SPBCS.keyCollision (t.size n) k + 2 * T / 2 ^ (4 * kS) := by
  intro T 𝒜
  have h := QROM.QueryBoundedAdversary.adaptiveCompleteness_coins M.saltOfBits 𝒜 (outEquiv k e)
    (R := M.ProverCoins R)
    (Bad := fun (c : M.ProverCoins R) σ hb (o : ProofQuery X Wit) =>
      rel o.stmt o.wit ∧ ¬ M.Accepts (hb ∘ Query.toBits) o.stmt
      (prove (prv o.wit c.iop) o.stmt σ E c.merkleSalts (hb ∘ Query.toBits) (Q o.stmt))
      (Q o.stmt))
    (freshSlice_coins_comp_toBits M.saltOfBits_toBits
      (Bad := fun (c : M.ProverCoins R) σ h (o : ProofQuery X Wit) =>
        rel o.stmt o.wit ∧ ¬ M.Accepts h o.stmt
        (prove (prv o.wit c.iop) o.stmt σ E c.merkleSalts h (Q o.stmt)) (Q o.stmt))
      (prob_not_accepts_prove_proverCoins_replaceSlice_le M prv E Q hε))
  rw [ofReal_two_mul_div_sqrt_card] at h
  refine le_trans ?_ h
  unfold NARG.QROM.Adversary.rejectsHonest
  refine ENNReal.tsum_le_tsum fun a => mul_le_mul_of_nonneg_left ?_ zero_le
  rw [tsum_fintype, ← Equiv.sum_comp (SaltedCoins.equivProd _ _).symm, Fintype.sum_prod_type,
    Finset.sum_comm]
  refine Finset.sum_le_sum fun c _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun σ _ => ?_
  rw [show (M.niProver Λ prv E hb).coins = PMF.uniformOfFintype _ from rfl,
    uniform_saltedCoins_apply, mul_assoc]
  gcongr with p o
  intro hv
  refine NARG.Verifier.ofOracle_accepted_of ?_
  have hco : chainOracle ((outEquiv k e).symm ∘ p.oracle) = p.oracle ∘ Query.toBits :=
    funext fun q => by simp [chainOracle]
  simp only [NARG.Prover.toFn_encode_prove, M.toFn_niProver Λ prv E VE hb, decode_queryEncoding, hco]
  exact hv

end GordieHowe.SPBCS
