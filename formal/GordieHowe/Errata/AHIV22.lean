-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Errata.Basic
public import GordieHowe.Foundations.ReedSolomon.BerlekampWelch
public import GordieHowe.Foundations.ToMathlib.LagrangeEval
public import GordieHowe.Headline
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Tactic.NormNum.Prime

@[expose] public section

/-!
# An erratum against AHIV22: Lemma B.9 and the quadratic term of Appendix C

Ames, Hazay, Ishai and Venkitasubramaniam, "Ligero: lightweight sublinear arguments without a
trusted setup", ePrint 2022/1608, version of 2022-11-17 (= DCC 2023), Appendix B.5 (p. 44) and
Appendix C (pp. 45–47).

Figure 11 (p. 45), Generalized-Test-Quadratic-Constraints-IRS, tests that the oracle rows
`U^x, U^y, U^z ∈ L^m` encode `x, y, z` with `x ⊙ y + a ⊙ z = b`. The oracle also holds "an
additional auxiliary row vector `u′ ∈ F̂^n` that encodes the all 0s message in `RS_{F,n,2k,η}`";
nothing in the test checks that `u′` is a codeword. Lemma B.9 (p. 44) states:

> Let `e` be a positive integer such that `e < d/2`. Let `U^{x*}, U^{y*}, U^{z*}` be badly formed
> oracles and let `U* ∈ F^{3m×n}` be the matrix obtained by vertically juxtaposing the
> corresponding `m × n` matrices. Suppose `d(U*, L^{3m}) ≤ e`, and let `U^x, U^y, U^z`,
> respectively, be the (unique) codewords in `L^m` that are closest to `U^{x*}, U^{y*}, U^{z*}`.
> Suppose `U^x, U^y, U^z` encode `x, y, z` such that `x ⊙ y + a ⊙ z ≠ b`. Then, for any malicious
> `P` strategy, `(U^{x*}, U^{y*}, U^{z*})` is rejected by `V` except with at most
> `1/|F|^σ + ((e + 2k)/n)^t` probability.

Appendix C (p. 47) replaces the quadratic term by `(2k/n)^t + 1/|F|` "assuming that none of the
columns containing errors are chosen", and uses it in the final soundness sum.

This file transcribes Figure 11 at `σ = 1` (`Setup`, `Prover`, `Accepts`, `acceptProb`), states
Lemma B.9 and Appendix C's quadratic term as propositions (`LemmaB9`, `AppCQuadratic`), and proves
both false, as transcribed, at `F_37`, `n = 34`, `k = 4`, `m = ℓ = 1`, `t = 2` (and `t = 1`): a
prover whose oracle rows are exact codewords and whose auxiliary row `u′` is a fixed non-codeword
passes with probability exactly `2060/20757` (`409/1258` at `t = 1`). Everything is decided by the
kernel (`decide +kernel`).

Reading of the paper (each choice is forced by the text or makes the refuted statement weaker):
- `σ = 1`. Figure 11 mixes two readings of `σ`: an extension field `F̂` with `|F̂| = |F|^σ` and
  `σ` repeated polynomials `p_0^1, …, p_0^σ`. At `σ = 1` both give `F̂ = F` and one polynomial.
- The response is `2k − 1` coefficients (step 3: "P sends the `2k − 1` coefficients"), so a
  polynomial of degree at most `2k − 2`. The honest response also contains `r_Blind`, "the
  polynomial of degree `< 2k` corresponding to `u′`" (Fig. 11; section 4.6.3 says degree
  `< 2k − 1`); the soundness statement concerns a malicious prover, which sends any `2k − 1`
  coefficients.
- "For any malicious `P` strategy" covers the choice of `u′` (part of the oracle `P` supplies)
  and of the response as a function of the challenge `r`. `Prover` is a deterministic strategy;
  refuting the bound for one deterministic prover refutes it for the larger class.
- `V` picks `r` uniform in `F^m` (step 2) and `Q` uniform among the `t`-subsets of `[n]`
  (step 4, "a random index set `Q ⊂ [n]` of size `t`"), independently; "rejected except with at
  most `ε` probability" is `Pr[V accepts] ≤ ε`.
- "The (unique) codewords closest to" `U*` is a hypothesis on a codeword triple `V` closest to
  `U*` within `e` columns (`LemmaB9Hyp`). Codewords are given by their polynomials (coefficient
  vectors of length `k`): with `η` distinct and `k ≤ n` (Def. 4.1) a codeword determines its
  polynomial, so this is Definition 4.2's `Decode_ζ`.
- `U^a = Encode_ζ(a)`, `U^b = Encode_ζ(b)` are the evaluations at `η` of the polynomials of
  degree `< ℓ` through `(ζ_c, a_{ic})` (Fig. 11 steps 1 and 3), written in Lagrange form.
- The setting's side conditions (Def. 4.1–4.2 and section 4.7: `η` distinct, `ζ` distinct and
  disjoint from `η`, `ℓ ≤ k ≤ n`) are a hypothesis of both propositions (`Setup.Valid`), so a
  refutation also proves the instance satisfies them.
- Appendix C's term is read as a claim about Figure 11's (masked) test, the test of the final
  ZKIPCP (section 4.7), whose soundness sum it enters. Only oracles that are exact codewords
  are quantified over, so no column contains errors and every reading of "assuming that none of
  the columns containing errors are chosen" applies.
-/

namespace GordieHowe.Errata.AHIV22

open Finset RSCode.BerlekampWelch

variable {F : Type} [Field F] {n m ℓ k : ℕ}

/-- The public parameters of Figure 11 (ePrint 2022/1608, p. 45): the evaluation points
`η = (η_1, …, η_n)` of `L = RS_{F,n,k,η}` (Def. 4.1), the message points `ζ = (ζ_1, …, ζ_ℓ)`
(Def. 4.2), and the public vectors `a, b ∈ F^{mℓ}` of the constraint `x ⊙ y + a ⊙ z = b`, indexed
by row `i ∈ [m]` and message position `c ∈ [ℓ]`. -/
structure Setup (F : Type) (n m ℓ : ℕ) where
  /-- The evaluation points of the code. -/
  η : Fin n → F
  /-- The message points. -/
  ζ : Fin ℓ → F
  /-- The public vector `a`. -/
  a : Fin m → Fin ℓ → F
  /-- The public vector `b`. -/
  b : Fin m → Fin ℓ → F

namespace Setup

/-- The side conditions of the setting: `η` has distinct entries and `k ≤ n` (Def. 4.1, so a
codeword determines its polynomial), `ζ` has distinct entries with `ℓ ≤ k` (Def. 4.2), disjoint
from `η` (section 4.7, p. 25), and `0 < k`. -/
structure Valid (S : Setup F n m ℓ) (k : ℕ) : Prop where
  η_injective : Function.Injective S.η
  ζ_injective : Function.Injective S.ζ
  ζ_ne_η : ∀ c j, S.ζ c ≠ S.η j
  k_pos : 0 < k
  ℓ_le_k : ℓ ≤ k
  k_le_n : k ≤ n

/-- `Encode_ζ(v)` for a public vector `v` (Fig. 11 step 1): row `i` is the evaluation at `η` of
the polynomial of degree `< ℓ` taking the value `v i c` at `ζ_c`, in Lagrange form. -/
def encode (S : Setup F n m ℓ) (v : Fin m → Fin ℓ → F) (i : Fin m) (j : Fin n) : F :=
  ∑ c, v i c * Lagrange.basisEval univ S.ζ c (S.η j)

end Setup

/-- The oracle rows `U^{x*}, U^{y*}, U^{z*} ∈ F^{m×n}` of Figure 11, possibly badly formed. -/
structure Oracle (F : Type) (m n : ℕ) where
  /-- `U^{x*}`. -/
  x : Fin m → Fin n → F
  /-- `U^{y*}`. -/
  y : Fin m → Fin n → F
  /-- `U^{z*}`. -/
  z : Fin m → Fin n → F

variable [DecidableEq F] in
/-- The number of columns `j ∈ [n]` in which the vertical juxtapositions of `U` and `U′` (in
`F^{3m×n}`) differ: the distance of `L^{3m}` as a code over the alphabet `F^{3m}`. -/
def colDist (U U' : Oracle F m n) : ℕ :=
  #{j | ∃ i, U.x i j ≠ U'.x i j ∨ U.y i j ≠ U'.y i j ∨ U.z i j ≠ U'.z i j}

omit [Field F] in
theorem colDist_self [DecidableEq F] (U : Oracle F m n) : colDist U U = 0 := by
  simp [colDist]

/-- A triple of `L^m` codewords, given by the polynomials of their rows: coefficient vectors of
length `k`, so polynomials of degree `< k` (Def. 4.1). -/
structure CodewordPolys (F : Type) (m k : ℕ) where
  /-- The polynomials of the rows of `U^x`. -/
  x : Fin m → Fin k → F
  /-- The polynomials of the rows of `U^y`. -/
  y : Fin m → Fin k → F
  /-- The polynomials of the rows of `U^z`. -/
  z : Fin m → Fin k → F

namespace CodewordPolys

/-- The codewords: each row's polynomial evaluated at `η` (Def. 4.1). -/
def toOracle (V : CodewordPolys F m k) (η : Fin n → F) : Oracle F m n where
  x i j := evalCoeffs (V.x i) (η j)
  y i j := evalCoeffs (V.y i) (η j)
  z i j := evalCoeffs (V.z i) (η j)

/-- The messages `x = Decode_ζ(U^x)`, `y`, `z` the codewords encode (Def. 4.2: the row
polynomials evaluated at `ζ`) violate `x ⊙ y + a ⊙ z = b` at some row `i` and position `c`. -/
def Violates (V : CodewordPolys F m k) (S : Setup F n m ℓ) : Prop :=
  ∃ i c, evalCoeffs (V.x i) (S.ζ c) * evalCoeffs (V.y i) (S.ζ c) +
    S.a i c * evalCoeffs (V.z i) (S.ζ c) ≠ S.b i c

end CodewordPolys

/-- The hypotheses Lemma B.9 puts on the oracle `U`: `V` is a codeword triple closest to `U` in
`L^{3m}`, `d(U, L^{3m}) ≤ e`, and the messages `V` encodes violate the constraint. -/
structure LemmaB9Hyp [DecidableEq F] (S : Setup F n m ℓ) (e : ℕ) (U : Oracle F m n) (V : CodewordPolys F m k) :
    Prop where
  closest : ∀ V' : CodewordPolys F m k, colDist U (V.toOracle S.η) ≤ colDist U (V'.toOracle S.η)
  within : colDist U (V.toOracle S.η) ≤ e
  violates : V.Violates S

/-- A malicious prover strategy in Figure 11 at `σ = 1`: the auxiliary row `u′ ∈ F^n` of the
oracle, and the `2k − 1` coefficients of `p_0` it sends in step 3 as a function of the challenge
`r ∈ F^m`. -/
structure Prover (F : Type) (m n k : ℕ) where
  /-- The auxiliary row `u′`. -/
  aux : Fin n → F
  /-- The coefficients of the response `p_0` to the challenge `r`. -/
  resp : (Fin m → F) → Fin (2 * k - 1) → F

namespace Setup

variable (S : Setup F n m ℓ)

/-- Check 5(a) of Figure 11: `p_0(ζ_c) = 0` for every `c ∈ [ℓ]`. -/
def Vanishes (P : Prover F m n k) (r : Fin m → F) : Prop :=
  ∀ c, evalCoeffs (P.resp r) (S.ζ c) = 0

/-- Check 5(b) of Figure 11 at column `j`:
`p_0(η_j) = u′_j + ∑_i r_i · (U^x_{i,j} · U^y_{i,j} + U^a_{i,j} · U^z_{i,j} − U^b_{i,j})`. -/
def ColumnHolds (U : Oracle F m n) (P : Prover F m n k) (r : Fin m → F) (j : Fin n) : Prop :=
  evalCoeffs (P.resp r) (S.η j) =
    P.aux j + ∑ i, r i * (U.x i j * U.y i j + S.encode S.a i j * U.z i j - S.encode S.b i j)

/-- The verifier of Figure 11 accepts on challenge `r` and opened columns `Q` (step 5). -/
structure Accepts (U : Oracle F m n) (P : Prover F m n k) (r : Fin m → F) (Q : Finset (Fin n)) :
    Prop where
  vanishes : S.Vanishes P r
  columns : ∀ j ∈ Q, S.ColumnHolds U P r j

theorem accepts_iff {U : Oracle F m n} {P : Prover F m n k} {r : Fin m → F} {Q : Finset (Fin n)} :
    S.Accepts U P r Q ↔ S.Vanishes P r ∧ ∀ j ∈ Q, S.ColumnHolds U P r j :=
  ⟨fun h => ⟨h.vanishes, h.columns⟩, fun h => ⟨h.1, h.2⟩⟩

variable [DecidableEq F]

instance (P : Prover F m n k) (r : Fin m → F) : Decidable (S.Vanishes P r) :=
  inferInstanceAs (Decidable (∀ _, _))

instance (U : Oracle F m n) (P : Prover F m n k) (r : Fin m → F) (j : Fin n) :
    Decidable (S.ColumnHolds U P r j) :=
  inferInstanceAs (Decidable (_ = _))

instance (U : Oracle F m n) (P : Prover F m n k) (r : Fin m → F) (Q : Finset (Fin n)) :
    Decidable (S.Accepts U P r Q) :=
  decidable_of_iff _ S.accepts_iff.symm

variable [Fintype F]

/-- The probability that the verifier of Figure 11 accepts the oracle `U` and the prover `P`
with `t` opened columns: `r` uniform in `F^m`, `Q` uniform among the `t`-subsets of `[n]`. -/
def acceptProb (t : ℕ) (U : Oracle F m n) (P : Prover F m n k) : ℚ :=
  queryProb (Fin m → F) n t (S.Accepts U P)

/-- For each challenge passing check 5(a), the accepted opened sets are the `t`-subsets of the
columns passing check 5(b): `C(#agree, t)` of them. -/
def acceptCount (t : ℕ) (U : Oracle F m n) (P : Prover F m n k) : ℕ :=
  ∑ r, if S.Vanishes P r then (#{j | S.ColumnHolds U P r j}).choose t else 0

theorem acceptProb_eq (t : ℕ) (U : Oracle F m n) (P : Prover F m n k) :
    S.acceptProb t U P = S.acceptCount t U P / (Fintype.card F ^ m * n.choose t) := by
  rw [acceptProb, queryProb_eq_sum (S.Vanishes P) (S.ColumnHolds U P) fun _ _ => S.accepts_iff,
    acceptCount]
  simp

end Setup

variable [DecidableEq F] [Fintype F]

/-- **AHIV22 Lemma B.9** (ePrint 2022/1608, version of 2022-11-17, p. 44), at `σ = 1`, as
transcribed here: in the setting of Figure 11, for every positive `e < d/2` (`d = n − k + 1`), every
oracle `U` whose closest codeword triple `V` is within `e` columns and encodes messages violating
`x ⊙ y + a ⊙ z = b`, and every malicious prover (auxiliary row and responses), the verifier accepts
with probability at most `1/|F| + ((e + 2k)/n)^t`. -/
def LemmaB9 (S : Setup F n m ℓ) (k t : ℕ) : Prop :=
  S.Valid k → ∀ e : ℕ, 0 < e → 2 * e < n - k + 1 →
    ∀ (U : Oracle F m n) (V : CodewordPolys F m k), LemmaB9Hyp S e U V →
      ∀ P : Prover F m n k,
        S.acceptProb t U P ≤ 1 / Fintype.card F + ((e + 2 * k : ℚ) / n) ^ t

/-- **AHIV22 Appendix C**, quadratic test (ePrint 2022/1608, p. 47), applied to the masked test of
Figure 11 at `σ = 1`, for oracles that are exact codewords: if the codewords encode messages
violating `x ⊙ y + a ⊙ z = b`, every malicious prover passes with probability at most
`(2k/n)^t + 1/|F|`. -/
def AppCQuadratic (S : Setup F n m ℓ) (k t : ℕ) : Prop :=
  S.Valid k → ∀ V : CodewordPolys F m k, V.Violates S →
    ∀ P : Prover F m n k,
      S.acceptProb t (V.toOracle S.η) P ≤ ((2 * k : ℚ) / n) ^ t + 1 / Fintype.card F

/-! ## The counterexample: `F_37`, `n = 34`, `k = 4`, `m = ℓ = 1` -/

/-- `37` is prime, so `ZMod 37` is a field. -/
instance fact_prime_37 : Fact (Nat.Prime 37) := ⟨by norm_num⟩

/-- The setting of the counterexample: `F = F_37`, `n = 34`, `m = ℓ = 1`,
`η_j = j`, `ζ_1 = 34`, and the constraint `x · y + z = 1`. -/
def ex : Setup (ZMod 37) 34 1 1 where
  η j := j
  ζ _ := 34
  a _ _ := 1
  b _ _ := 1

/-- The zero codewords of `RS_{F_37,34,4,η}`: `x = y = z = 0`, so `x · y + z = 0 ≠ 1`. -/
def exCodewords : CodewordPolys (ZMod 37) 1 4 := ⟨0, 0, 0⟩

/-- The auxiliary row `u′`, a fixed non-codeword. -/
def exAux : Fin 34 → ZMod 37 :=
  ![8, 36, 4, 16, 7, 31, 28, 30, 24, 13, 6, 31, 1, 24, 27, 0, 28, 17, 14, 6, 20, 1, 1, 1, 34, 0,
    24, 13, 27, 1, 33, 14, 28, 31]

/-- The response coefficients for the challenge `r = δ`: `p_0 = g_δ − δ`, where `g_δ` is a
polynomial of degree `≤ 6` with `g_δ(34) = δ` agreeing with `u′` on the most columns. -/
def exResponses : Fin 37 → Fin 7 → ZMod 37 :=
  ![![25, 21, 19, 30, 16, 8, 4],
    ![22, 19, 36, 26, 22, 25, 33],
    ![6, 4, 4, 33, 8, 19, 15],
    ![5, 10, 8, 12, 13, 9, 13],
    ![4, 24, 12, 23, 2, 36, 21],
    ![3, 23, 30, 9, 14, 18, 8],
    ![2, 33, 23, 0, 30, 35, 6],
    ![20, 20, 27, 17, 36, 11, 19],
    ![7, 27, 22, 32, 3, 0, 12],
    ![36, 32, 30, 2, 1, 17, 16],
    ![35, 26, 11, 26, 22, 36, 11],
    ![21, 15, 26, 7, 9, 11, 27],
    ![33, 31, 3, 1, 3, 32, 6],
    ![7, 30, 13, 18, 20, 7, 2],
    ![22, 21, 21, 12, 2, 1, 17],
    ![30, 15, 23, 33, 2, 18, 11],
    ![29, 25, 3, 14, 20, 26, 1],
    ![10, 33, 8, 36, 13, 23, 9],
    ![27, 27, 29, 12, 34, 17, 29],
    ![26, 23, 13, 30, 5, 29, 2],
    ![15, 0, 29, 11, 36, 2, 34],
    ![24, 3, 35, 5, 3, 8, 1],
    ![36, 21, 28, 9, 32, 17, 30],
    ![22, 15, 15, 28, 7, 12, 34],
    ![21, 36, 2, 27, 14, 3, 8],
    ![2, 29, 9, 15, 15, 16, 36],
    ![19, 23, 34, 35, 11, 25, 11],
    ![25, 26, 23, 1, 33, 15, 14],
    ![17, 20, 22, 14, 22, 0, 24],
    ![16, 31, 19, 6, 20, 23, 3],
    ![15, 12, 1, 0, 27, 5, 20],
    ![23, 23, 13, 0, 28, 21, 1],
    ![13, 16, 20, 0, 26, 31, 21],
    ![12, 32, 18, 6, 18, 8, 2],
    ![22, 30, 30, 11, 1, 34, 28],
    ![10, 7, 33, 24, 19, 32, 19],
    ![32, 29, 12, 11, 35, 20, 9]]

/-- The counterexample prover: auxiliary row `exAux`, response `exResponses` at the challenge. -/
def exProver : Prover (ZMod 37) 1 34 4 where
  aux := exAux
  resp r := exResponses ⟨(r 0).val, (r 0).val_lt⟩

theorem ex_valid : ex.Valid 4 where
  η_injective := by decide +kernel
  ζ_injective := Function.injective_of_subsingleton _
  ζ_ne_η := by decide +kernel
  k_pos := by norm_num
  ℓ_le_k := by norm_num
  k_le_n := by norm_num

theorem exCodewords_violates : exCodewords.Violates ex :=
  ⟨0, 0, by decide⟩

theorem exCodewords_lemmaB9Hyp (e : ℕ) :
    LemmaB9Hyp ex e (exCodewords.toOracle ex.η) exCodewords where
  closest _ := by simp [colDist_self]
  within := by simp [colDist_self]
  violates := exCodewords_violates

theorem exProver_acceptCount_two : ex.acceptCount 2 (exCodewords.toOracle ex.η) exProver = 2060 := by
  decide +kernel

theorem exProver_acceptCount_one : ex.acceptCount 1 (exCodewords.toOracle ex.η) exProver = 409 := by
  decide +kernel

/-- With `t = 2` the counterexample prover passes Figure 11 with probability `2060/20757`. -/
theorem exProver_acceptProb_two :
    ex.acceptProb 2 (exCodewords.toOracle ex.η) exProver = 2060 / 20757 := by
  rw [Setup.acceptProb_eq, exProver_acceptCount_two, ZMod.card]
  norm_num [Nat.choose_two_right]

/-- With `t = 1` the counterexample prover passes Figure 11 with probability `409/1258`. -/
theorem exProver_acceptProb_one :
    ex.acceptProb 1 (exCodewords.toOracle ex.η) exProver = 409 / 1258 := by
  rw [Setup.acceptProb_eq, exProver_acceptCount_one, ZMod.card]
  norm_num

/-- **AHIV22 Lemma B.9 is false as transcribed here** (Ames, Hazay, Ishai and Venkitasubramaniam,
ePrint 2022/1608, version of 2022-11-17, Lemma B.9, p. 44). At `F = F_37`, `n = 34`, `k = 4`,
`m = ℓ = 1`, `σ = 1`, `t = 2`, `e = 1`, with exact codewords encoding `x = y = z = 0` against
`x · y + z = 1`, a prover with an arbitrary auxiliary row passes with probability
`2060/20757 ≈ 0.0992`, above the lemma's `1/37 + (9/34)^2 ≈ 0.0971`. -/
@[headline]
theorem lemmaB9_false_two : ¬ LemmaB9 ex 4 2 := by
  intro h
  have hb := h ex_valid 1 (by norm_num) (by norm_num) _ exCodewords (exCodewords_lemmaB9Hyp 1)
    exProver
  rw [exProver_acceptProb_two, ZMod.card] at hb
  norm_num at hb

/-- **AHIV22 Lemma B.9 is false as transcribed here**, `t = 1`
(ePrint 2022/1608, version of 2022-11-17, Lemma B.9, p. 44): the same
instance passes with probability `409/1258 ≈ 0.3251`, above `1/37 + 9/34 ≈ 0.2917`. -/
@[headline]
theorem lemmaB9_false_one : ¬ LemmaB9 ex 4 1 := by
  intro h
  have hb := h ex_valid 1 (by norm_num) (by norm_num) _ exCodewords (exCodewords_lemmaB9Hyp 1)
    exProver
  rw [exProver_acceptProb_one, ZMod.card] at hb
  norm_num at hb

/-- **AHIV22 Appendix C's quadratic term, as transcribed here, fails for the masked test** (Ames,
Hazay, Ishai and Venkitasubramaniam, ePrint 2022/1608, version of 2022-11-17, Appendix C, p. 47). At
the instance of `lemmaB9_false_two` (`t = 2`), the acceptance `2060/20757 ≈ 0.0992` exceeds
`(8/34)^2 + 1/37 ≈ 0.0824`. -/
@[headline]
theorem appCQuadratic_false_two : ¬ AppCQuadratic ex 4 2 := by
  intro h
  have hb := h ex_valid exCodewords exCodewords_violates exProver
  rw [exProver_acceptProb_two, ZMod.card] at hb
  norm_num at hb

/-- **AHIV22 Appendix C's quadratic term, as transcribed here, fails for the masked test**,
`t = 1` (ePrint 2022/1608, version of 2022-11-17, Appendix C, p. 47): the acceptance
`409/1258 ≈ 0.3251` exceeds `8/34 + 1/37 ≈ 0.2623`. -/
@[headline]
theorem appCQuadratic_false_one : ¬ AppCQuadratic ex 4 1 := by
  intro h
  have hb := h ex_valid exCodewords exCodewords_violates exProver
  rw [exProver_acceptProb_one, ZMod.card] at hb
  norm_num at hb

end GordieHowe.Errata.AHIV22
