-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.Realizations.Lowering
public import GordieHowe.Foundations.Algebra.IntLift
public import GordieHowe.Applications.Falcon512.Emulated.System.Params
public import GordieHowe.Applications.Falcon512.System.Source
public import GordieHowe.Applications.Falcon512.Circuits.EmulatedAlgebra
public import GordieHowe.Applications.Falcon512.System.Algebra

@[expose] public section

/-!
# Falcon emulated: the algebra constraints of domain A

The emulated algebra of Falcon emulated (`lib/gordiehowe/examples/falcon/falcon_emulated.h`, the gadgets
`crossing`, `signature_relation`, `magnitudes`, `assert_encoding_budget` and `assert_norm` that
`falcon_emulated` declares, lines 643-663, over a field `F` of characteristic `pGold`): the sample
bits `c_A` (`512 × 16` Bit cells, sample `i` bit `b` at `16 i + b`), the private input `s2`, and the
advice values `s1`, `quot`, `mag1`, `mag2`, `high2`, `norm`, with

* `signature.equation` (512 affine rows, `falcon_emulated.h:522-524`):
  `bias + from_digits(c_A, 2) − NegacyclicConv(h)(s2) − s1 − q · quot = 0`, with `h` the decoded
  public key (`key.coefficients`) and `bias = 77315788807`;
* `magnitudes.s1`, `magnitudes.s2` (`falcon_emulated.h:591-592`; `s1`'s a circuit constraint,
  `s2`'s a field batch of domain A):
  `(mag1 − s1)(mag1 − (q − s1)) = 0`, `(mag2 − s2)(mag2 − (q − s2)) = 0`;
* `norm.sum` (circuit, `falcon_emulated.h:622`, on the advice `norm.squares`, here `norm`):
  `norm − Σ mag1² − Σ mag2² = 0`;
* the Boolean check of the Bit cells `c_A` (`x (x − 1) = 0`, in domain A's Boolean batch
  `A.boolean`, the placement rule's field batch);

and Falcon's seven range requests (`s1` has none).

**Soundness** (`algebraSpec_of_congruent`): given the signature relation as a congruence modulo `q`
on the integer readings (`GordieHowe.Falcon512.Emulated.Rows.Congruent`), the two-root magnitude equations, the
norm equation and the range facts, the challenge `c` and the signature polynomial read from `s2`
(`decodeS2`) satisfy Falcon's algebraic verifier and the encoding bounds (`AlgebraSpecAt`). The
proof uses `EmulatedNorm.lifted_of_sumSq` for the norm (the request on `norm` bounds the sum of
squares).

The parts Falcon native also uses are in `GordieHowe/Applications/Falcon512/System/Algebra.lean`.
-/

namespace GordieHowe.Falcon512.Emulated

open GordieHowe.Bits Range Params

variable {F : Type} [Field F]

variable [DecidableEq F]

variable [CharP F pGold] {K : ℕ} {L : RealizedProgram.ProofSystem.PhaseLayout K}

/-- **Soundness of the algebra from the integer signature relation** (the emulated realized
programs and the carrier rings, whose source programs give `signature.equation` as a congruence
modulo `q` on the integer readings), at a challenge given as naturals `c`: `s1` and `s2` are naturals `s1N`, `s2N` at most `q`;
their magnitudes `mag1 < q / 2 + 1` and `mag2N < 2048` are pinned by the two-root equations; the sum
of squares `norm` is below `β² + 1`; the high parts `⌊mag2N / 128⌋` sum to at most `392`; and `s1N + h · s2N ≡ c` coefficientwise modulo `q`
(`Rows.Congruent`). Then Falcon's algebraic verifier and the encoding bounds hold on
the extracted values. -/
theorem algebraSpec_of_congruent {h : _root_.Falcon.Rq falcon512.n}
    {c : Fin falcon512.n → ℕ} {s1 s2 mag1 mag2 : Fin falcon512.n → F}
    {norm : F} {s1N s2N mag2N : Fin falcon512.n → ℕ}
    (hs1N : ∀ i, s1N i ≤ q ∧ (s1N i : F) = s1 i) (hs2N : ∀ i, s2N i ≤ q ∧ (s2N i : F) = s2 i)
    (hmag1 : ∀ i, Range.IsNatBelow mag1Honest (mag1 i))
    (hmag2N : ∀ i, mag2N i < 2048 ∧ (mag2N i : F) = mag2 i)
    (hmagS1 : ∀ i, (mag1 i - s1 i) * (mag1 i - ((q : F) - s1 i)) = 0)
    (hmagS2 : ∀ i, (mag2 i - s2 i) * (mag2 i - ((q : F) - s2 i)) = 0)
    (hnorm : norm - ∑ i, mag1 i * mag1 i - ∑ i, mag2 i * mag2 i = 0)
    (hnormR : Range.IsNatBelow (betaSq + 1) norm)
    (hbudget : ∑ i, mag2N i / 128 ≤ 392)
    (hcong : Rows.Congruent q (_root_.GordieHowe.Falcon512.EmulatedAlgebraCircuit.keyCoeffs h) c s1N
      s2N) :
    AlgebraSpecAt h c s2 := by
  have hqp : q < pGold := by norm_num [pGold]
  have hs2Eq : s2N = s2Nat s2 := by
    funext i
    have hs2Range : Range.IsNatBelow (q + 1) (s2 i) := ⟨s2N i, Nat.lt_succ_of_le (hs2N i).1, (hs2N i).2⟩
    have hchosen := Range.natBelow_spec (T := q + 1) hs2Range
    apply IntLift.natCast_inj_of_lt (K := F) (p := pGold)
      ((hs2N i).1.trans_lt hqp) ((Nat.le_of_lt_succ hchosen.1).trans_lt hqp)
    rw [(hs2N i).2]
    exact hchosen.2.symm
  -- Norm: the coefficients of `s1 ‖ s2` lift with centered norm at most `β²`.
  obtain ⟨vals, hvals⟩ := EmulatedNorm.lifted_of_sumSq (p := pGold) (q := q) (M := mag1Honest)
    (βSq := betaSq) (v := Fin.append (fun j : Fin 512 => s1 j) (fun j : Fin 512 => s2 j))
    (mag := Fin.append (fun j : Fin 512 => mag1 j) (fun j : Fin 512 => mag2 j))
    (by norm_num) (by norm_num [pGold]) (by norm_num [pGold])
    (fun k => Fin.addCases (fun i => by rw [Fin.append_left]; exact hmag1 i)
      (fun i => by
        rw [Fin.append_right]
        exact ⟨mag2N i, lt_of_lt_of_le (hmag2N i).1 (by norm_num), (hmag2N i).2⟩) k)
    (fun k => Fin.addCases (fun i => by rw [Fin.append_left, Fin.append_left]; exact hmagS1 i)
      (fun i => by rw [Fin.append_right, Fin.append_right]; exact hmagS2 i) k)
    (by
      change norm - ∑ i : Fin 512, mag1 i * mag1 i - ∑ i : Fin 512, mag2 i * mag2 i = 0 at hnorm
      rw [Fin.sum_univ_add]
      simp only [Fin.append_left, Fin.append_right]
      convert hnormR using 1
      linear_combination -hnorm)
  have hvalsLow : ∀ i, vals (Fin.castAdd 512 i) = s1N i := by
    intro i
    apply IntLift.natCast_inj_of_lt (K := F) (p := pGold)
      ((hvals.bounded _).trans_lt hqp) ((hs1N i).1.trans_lt hqp)
    rw [hvals.cast_eq, Fin.append_left, (hs1N i).2]
  have hvalsHigh : ∀ i, vals (Fin.natAdd 512 i) = s2N i := by
    intro i
    apply IntLift.natCast_inj_of_lt (K := F) (p := pGold)
      ((hvals.bounded _).trans_lt hqp) ((hs2N i).1.trans_lt hqp)
    rw [hvals.cast_eq, Fin.append_right, (hs2N i).2]
  -- The algebra.
  let s1Poly : _root_.Falcon.Rq falcon512.n :=
    Falcon512.ofCoeff fun i => (s1N i : _root_.Falcon.Coeff)
  have hs1Poly :
      Falcon512.ofCoeff (fun i => (c i : _root_.Falcon.Coeff)) - decodeS2 s2 * h = s1Poly := by
    rw [Falcon512.mul_comm]
    apply LatticeCrypto.PolyBackend.ext_coeff (backend := _root_.Falcon.polyBackend falcon512.n)
    intro i
    change Falcon512.coeff
        (Falcon512.ofCoeff (fun i => (c i : _root_.Falcon.Coeff)) - h * decodeS2 s2) i =
      Falcon512.coeff s1Poly i
    unfold Falcon512.coeff
    rw [LatticeCrypto.NegacyclicRing.coeff_sub (Falcon.coeffRing falcon512.n)]
    change Falcon512.coeff (Falcon512.ofCoeff fun i => (c i : _root_.Falcon.Coeff)) i -
        Falcon512.coeff (h * decodeS2 s2) i = Falcon512.coeff s1Poly i
    rw [Falcon512.coeff_ofCoeff, Falcon512.coeff_mul]
    dsimp only [decodeS2, s1Poly]
    rw [Falcon512.coeff_ofCoeff, Falcon512.coeff_ofCoeff]
    have hkeyCoeff : Falcon512.coeff h =
        fun j => (_root_.GordieHowe.Falcon512.EmulatedAlgebraCircuit.keyCoeffs h j : _root_.Falcon.Coeff) := by
      funext j
      simp [_root_.GordieHowe.Falcon512.EmulatedAlgebraCircuit.keyCoeffs]
    rw [hkeyCoeff, ← hs2Eq]
    exact sub_eq_iff_eq_add.mpr (hcong i)
  have halgebra : Falcon512.algebraOk falcon512 h
      (Falcon512.ofCoeff fun i => (c i : _root_.Falcon.Coeff)) (decodeS2 s2) := by
    unfold Falcon512.algebraOk
    rw [hs1Poly, Falcon512.pairL2NormSq_eq_sum_append]
    have happend : Fin.append (Falcon512.coeff s1Poly) (Falcon512.coeff (decodeS2 s2)) =
        fun i : Fin (512 + 512) => (vals i : _root_.Falcon.Coeff) := by
      funext i
      refine Fin.addCases (fun i => ?_) (fun i => ?_) i
      · rw [Fin.append_left]
        dsimp only [s1Poly]
        rw [Falcon512.coeff_ofCoeff]
        exact congrArg Nat.cast (hvalsLow i).symm
      · rw [Fin.append_right]
        dsimp only [decodeS2]
        rw [Falcon512.coeff_ofCoeff, ← hs2Eq]
        exact congrArg Nat.cast (hvalsHigh i).symm
    rw [happend]
    exact hvals.norm
  -- The encoding bounds.
  have : NeZero q := ⟨by norm_num⟩
  have hcenter : ∀ i : Fin falcon512.n,
      (LatticeCrypto.centeredRepr (Falcon512.coeff (decodeS2 s2) i)).natAbs ≤ mag2N i := by
    intro i
    dsimp only [decodeS2]
    rw [Falcon512.coeff_ofCoeff, ← hs2Eq]
    apply EmulatedNorm.centered_le_of_centering (F := F) (p := pGold) hqp (hs2N i).1
      ((hmag2N i).1.le.trans (by norm_num))
    rw [(hmag2N i).2, (hs2N i).2]
    exact hmagS2 i
  have hencoding : Falcon512.EncodingBounds falcon512 (decodeS2Int s2) := by
    constructor
    · intro i
      dsimp only [decodeS2Int]
      rw [Vector.get_ofFn, Codec.magnitudeBound_eq]
      have := hcenter i
      have := (hmag2N i).1
      omega
    · dsimp only [decodeS2Int]
      simp only [Vector.get_ofFn]
      have hb : falcon512.encodingHighBudget = 392 := by decide
      rw [hb, Codec.lowRadix_eq]
      calc
        _ ≤ ∑ i : Fin falcon512.n, mag2N i / 128 := by
          apply Finset.sum_le_sum
          intro i _
          exact Nat.div_le_div_right (hcenter i)
        _ ≤ _ := hbudget
  exact ⟨halgebra, hencoding⟩

end GordieHowe.Falcon512.Emulated
