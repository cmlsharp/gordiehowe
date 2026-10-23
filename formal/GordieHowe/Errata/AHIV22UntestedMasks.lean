-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Errata.Basic
public import GordieHowe.Foundations.ReedSolomon.BerlekampWelch
public import GordieHowe.Foundations.ToMathlib.LagrangeEval
public import GordieHowe.Headline
public import GordieHowe.Foundations.ReedSolomon.InterleavedProximity
public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Data.Matrix.Mul

@[expose] public section

/-!
# AHIV22 Lemma 4.14 with untested constraint masks

Ames, Hazay, Ishai and Venkitasubramaniam, "Ligero: lightweight sublinear arguments without a
trusted setup", ePrint 2022/1608, version of 2022-11-17 (= DCC 2023), section 4.7 (pp. 24–26),
Lemma 4.14 (p. 26) and Theorem 4.7 (p. 27).

Lemma 4.14 states: for a positive integer `e < d/4`, if no `α` has `C(α) = 1`, then "for any
maliciously formed oracle `U*` and any malicious prover strategy, the verifier rejects except with
at most `(d + 2)/|F|^σ + (1 − e/n)^t + 2((e + 2k)/n)^t` probability". Theorem 4.7 repeats the bound
"for every (unbounded) prover strategy `P*` and every `π̃`". The proof is "analogous to" Lemma 4.12,
which combines Lemmas 4.8 and 4.10; those compare the sent polynomial with an honest polynomial
that, in the masked tests, contains the polynomial of the mask row. In section 4.7 the linear test's
mask `u^add_h` and the quadratic test's mask `u′^0_h` are opened at the queried columns but enter no
proximity test, so for a malicious oracle they are arbitrary vectors and the comparison has no
content. `GordieHowe.Errata.AHIV22` shows that the corresponding Lemma B.9 (p. 44) is false as transcribed
there. This file states Lemma 4.14 for the section 4.7 protocol with arbitrary mask rows
(`Lemma414`) and proves it (`lemma414`), with the sharper field term `(e + 1)/|F|^σ`
(`Setup.acceptProb_le_of_not_satisfiable`).

## The protocol (section 4.7)

* **Oracle** (`Oracle`): the rows `U ∈ F^{4m×n}` (blocks `U^w, U^x, U^y, U^z` of `m` rows each,
  `Block`), and for every repetition `h ∈ [σ]` the code test's blinding row `u^0_h`, the linear
  test's mask `u^add_h` and the quadratic test's mask `u′^0_h`, all arbitrary vectors in `F^n`.
* **Challenges** (`Challenge`, step 1): for every `h`, `r_h ∈ F^{4m}`, `r^add_h ∈ F^L` and
  `r^q_h ∈ F^m`, uniform and independent.
* **Responses** (`Response`, step 2): for every `h`, the code test's `v_h`, the linear test's
  `q^add_h` (degree `< k + ℓ − 1`) and the quadratic test's `p_{0,h}` (degree `< 2k − 1`). A
  malicious prover (`Prover`) chooses them as any function of all the challenges.
* **Query and checks** (step 3): `Q` uniform among the `t`-subsets of `[n]`; the verifier accepts
  when, for every `h`, the algebraic checks hold (`ResponseChecks`) and the three column checks
  hold at every `j ∈ Q` (`ColumnChecks`).

`acceptProb` is the exact acceptance probability: a finite sum over the challenges and `Q`.

## Reading of the paper

Each choice is forced by the text, generalizes it, or is noted as a reading.

* **Constraint system.** Section 4.7 takes the linear system `A · (w, x, y, z) = 0` with
  `A = [[I, −P], [0, P_add]]` and the quadratic system `x ⊙ y − z = 0`, built from the circuit
  `C` (section 4.4). We state the lemma for an arbitrary linear system `A ∈ F^{L×4mℓ}`,
  `b ∈ F^L` with any number `L` of rows (Figure 10's general form; section 4.7 has `L = 4mℓ`) and
  an arbitrary quadratic system `x ⊙ y + a ⊙ z = b′` on the blocks `x, y, z` (Figure 11's `a`,
  `b`); section 4.7 is the instance `b = 0`, `a = −1`, `b′ = 0`. The hypothesis "no `α` with
  `C(α) = 1`" is replaced by "no message satisfies the constraints" (`Setup.Satisfiable`), which
  is what the proof of Lemma 4.12 uses ("there exists no `w, x, y, z` that satisfy all the
  following constraints"); that the circuit's unsatisfiability implies it is the arithmetization
  of section 4.4 and is not restated here.
* **Typos read as intended.** The code check is `Σ_{i ∈ [4m]} r_{h,i} · U_{i,j} + u^0_h[j] = v_h[j]`
  (printed `r_h[j]`); `r^add_{h,i}` interpolates `((r^add_h)^T A)_{i,c}` (printed `(r^add_h)^T P`);
  `q^add_h` sums over all `4m` rows, as the column check does (printed `Σ_{i=1}^m`); the quadratic
  mask is a separate row `u′^0_h` (printed `u^0_h` in step 3's list and in Lemma 4.15).
* **The code test checks that `v_h` is a codeword.** Section 4.7 lists only the column checks;
  Figure 9 (step 4, "accepts iff all `w_h ∈ L`", `L` the code) and Figure 2 include the membership
  check, without which the test accepts every oracle. `v_h` is given by the `k` coefficients of
  its polynomial (`Response.code`), which is the membership check for `RS_{F,n,k,η}` (Def. 4.1).
  In this file `L` is the number of linear constraints.
* **Response degrees.** `q^add_h` has `k + ℓ − 1` coefficients and `p_{0,h}` has `2k − 1`
  (section 4.7, step 2; Theorem 4.7's communication count).
* **The code test's blinding row is arbitrary.** For a malicious oracle every row is arbitrary;
  Theorem B.3 and Lemma B.6 state the code test "for arbitrary `u^0_1, …, u^0_σ`".
* **Interpolation.** "The unique polynomial of degree `< ℓ`" through the points `(ζ_c, v_c)` is
  evaluated at `η_j` in Lagrange form (`Setup.interp`), as `GordieHowe.Errata.AHIV22` does for
  `Encode_ζ`; `U^a_{i,j}` and `U^b_{i,j}` (Figure 11) are the same evaluations of `a` and `b′`.
* **Probability.** The challenges are uniform on `Challenge` and, independently, `Q` is uniform
  among the `t`-subsets of `[n]` (step 3, "a random index set `Q ⊂ [n]` of size `t`"); "rejects
  except with at most `ε` probability" is `acceptProb ≤ ε`. The prover is deterministic; a
  randomized prover is a mixture of deterministic ones and the bound is linear in the prover's
  coins. The oracle is quantified before the prover, so the prover may depend on it.
* **`d` and `e`.** `d = n − k + 1` (Def. 4.1, "the `[n, k, n − k + 1]` linear code"), and the
  hypothesis on `e` is Lemma 4.14's `e < d/4`, written `4 * e < n - k + 1`; Theorem 4.7's
  `e < (n − k)/4` implies it.

## Side conditions

`Setup.Valid` holds what the proof uses: `η` injective (Def. 4.1), `ζ` injective and `ℓ ≤ k`
(Def. 4.2). The theorem is stated with fewer hypotheses than Lemma 4.14 and Theorem 4.7 carry,
which only strengthens it:

* `e` positive (Lemma 4.14): not needed; at `e = 0` the term `(1 − e/n)^t` is `1`.
* `ζ` disjoint from `η` (section 4.7), `|F| ≥ ℓ + n` and `k > ℓ + t` (Theorem 4.7): used only
  for zero knowledge (Lemma 4.15).
* `m · ℓ > n_i + s` (Theorem 4.7): concerns the arithmetization of `C`, which is not modelled.

No hypothesis restricts the oracle (any `U`, any masks) or the prover (any function of the
challenges), and no challenge is excluded.

The bound is stated with Lemma 4.14's terms. The proof bounds `C(a, t)/C(n, t)` by `(a/n)^t`
(the paper's step in Lemmas 4.8, 4.10 and Theorem 4.4).

## Proof

The proof gives the sharper bound `(e + 1)/|F|^σ + max((1 − e/n)^t, ((e + 2k)/n)^t)`
(`Setup.acceptProb_le_of_not_satisfiable`); `lemma414` follows since `e + 1 ≤ d + 2`. Write
`D = 2k − 2` and `S(ch)` for the columns at which all `3σ` column checks hold. A challenge outside
a bad set `Bad` with `ResponseChecks` has `|S(ch)| ≤ T`, so `acceptProb ≤ |Bad|/|Challenge| +
C(T, t)/C(n, t)` (`queryProb_le_of_bad`), and `C(T, t)/C(n, t) ≤ (b/n)^t` for `T ≤ b`
(`choose_div_choose_le_pow`). The oracle is fixed, so one of two cases applies.

**Far case** (`Setup.exists_bad_far`): `U` is not `e`-close to `RS_{F,n,k,η}^{4m}`. `Bad` is the
set of challenges whose rows `r_h^T U + u^0_h` are jointly `e`-close to `RS^σ` (one common set of
`e` error columns); outside it at most `n − e` columns pass the code checks. Its density is at
most `(e + 1)/|F|^σ` by `GordieHowe.InterleavedProximity.card_close_mul_le`, Lemma 4.2 proved jointly over
the repetitions. The paper's proof of Lemma B.2 bounds each repetition separately, which gives only
`((e + 1)/|F|)^σ`; the joint statement needs the common error set.

**Close case** (`Setup.exists_bad_close`): `U` agrees outside a set `E` of `≤ e` columns with the
codewords `V` of coefficient vectors `cf`. The decoded message violates the linear system or a
quadratic constraint (`Setup.linear_or_quadratic_of_not_holds`); take that test.
* The code test (`Setup.card_columns_le_or_disjoint`). Let `c_h = v_h − r_h^T V`, a codeword;
  off `E` the code check reads `c_h[j] = u^0_h[j]`. If some `c_h` is not the candidate
  (`CodeCand`: agreement with `u^0_h` off `E` above `(n − |E| + (n − d))/2`, unique by
  `CodeCand.eq`), then `|S(ch)| ≤ ⌊(n − |E| + k − 1)/2⌋ + |E| ≤ n − e`, using `3e ≤ d`. Otherwise
  an error column in `S(ch)` passes the code check against the candidate in every repetition
  (`Setup.CodeBad`), an affine condition on `r_h` with the nonzero coefficients `U[j] − V[j]` in
  each repetition: density `≤ |E|/|F|^σ` (`Setup.card_codeBad_mul_le`).
* The constraint test (`Setup.card_columns_compl_le_of_quad`, `Setup.card_columns_compl_le_of_lin`).
  Off `E` the column check of repetition `h` reads `g_h(η_j) = u_h[j]` for the response minus the
  test's polynomial on `V` (`Setup.quadComb`, `Setup.linComb`, degree `≤ D`). If some `g_h` is not
  the mask candidate (`MaskCand`: agreement above `(n + D)/2`, unique by `MaskCand.eq`), at most
  `(n + D)/2` columns outside `E` pass. Otherwise every repetition's candidate passes the
  algebraic check (`Setup.QuadBad`, `Setup.LinBad`), an affine condition on that test's challenge
  with nonzero linear part (the violated constraint): density `≤ 1/|F|^σ`
  (`Setup.card_quadBad_mul_le`, `Setup.card_linBad_mul_le`).
So outside a set of density `(e + 1)/|F|^σ`, `|S(ch)| ≤ max(n − e, (n + D)/2)`, and
`(n + D)/2 ≤ max(n − e, e + 2k)`.

The counting steps are `GordieHowe.RepetitionCounting`: lines, affine conditions, repetitions
(`card_piFinset_mul_pow_le`), unions over error columns taken after intersecting the repetitions
(`card_biUnion_piFinset_mul_pow_le`), unique candidates, and events reading one challenge
component (`card_filter_fst_mul_le`).

**Against the informal sketch** that Lemma 4.14's printed number survives. Counting the error
columns as free agreement (Lemma 4.8's accounting) gives `(n + D)/2 + e`, which exceeds both
thresholds once `e > (n − 2k + 2)/4`. The sketch's repair, a queried error column failing the code
test "except w.p. `1/|F|` per repetition", needs two corrections, both made here:
* The union over the error columns is taken after intersecting the repetitions: one column passes
  every repetition with probability `1/|F|^σ`, so `e/|F|^σ` in total. A union per repetition gives
  `(e/|F|)^σ`, which exceeds `(d + 2)/|F|^σ` for `σ ≥ 2` and large `e`.
* The sketch's "a code-test response other than the honest one agrees with it on at most `k − 1`
  columns plus the `e` error columns" assumes the blinding row `u^0_h` is a codeword. For an
  arbitrary blinding row the count is `⌊(n − |E| + k − 1)/2⌋ + |E|`, at most `n − e` exactly when
  `3e ≤ d`, which Lemma 4.14's `e < d/4` gives.
-/

namespace GordieHowe.Errata.AHIV22.UntestedMasks

open Finset RSCode.BerlekampWelch

/-- The four blocks of `m` rows of the section 4.7 oracle `U ∈ L^{4m}`: `U^w`, `U^x`, `U^y`,
`U^z`. -/
inductive Block
  /-- The extended witness `w`. -/
  | w
  /-- The left inputs `x` of the multiplication gates. -/
  | x
  /-- The right inputs `y` of the multiplication gates. -/
  | y
  /-- The outputs `z` of the multiplication gates. -/
  | z
  deriving DecidableEq

instance : Fintype Block :=
  ⟨{.w, .x, .y, .z}, fun b => by cases b <;> simp⟩

/-- A row of the oracle: a block and a row of it (`4m` rows). -/
abbrev Row (m : ℕ) := Block × Fin m

/-- A position of the encoded message: a row and a message position `c ∈ [ℓ]` (`4mℓ`
positions). -/
abbrev Cell (m ℓ : ℕ) := Row m × Fin ℓ

/-- An extended message `(w, x, y, z) ∈ F^{4mℓ}`: row `i`'s message is `c ↦ x (i, c)`
(Def. 4.2). -/
abbrev Message (F : Type) (m ℓ : ℕ) := Cell m ℓ → F

variable {F : Type} [Field F] {n m ℓ L σ k : ℕ}

/-- The public parameters of the section 4.7 ZKIPCP (ePrint 2022/1608, p. 24): the evaluation
points `η` of the code `RS_{F,n,k,η}` (Def. 4.1; the paper names it `L`, which here is the
number of linear constraints), the message points `ζ` (Def. 4.2), the linear system `A x = b` of
`L` constraints on the extended message (Figure 10) and the quadratic system
`x ⊙ y + a ⊙ z = b′` on the blocks `x, y, z` (Figure 11). Section 4.7 has `b = 0`, `a = −1`,
`b′ = 0`. -/
structure Setup (F : Type) (n m ℓ L : ℕ) where
  /-- The evaluation points of the code. -/
  η : Fin n → F
  /-- The message points. -/
  ζ : Fin ℓ → F
  /-- The linear constraint matrix `A ∈ F^{L×4mℓ}`. -/
  A : Matrix (Fin L) (Cell m ℓ) F
  /-- The linear constraint vector `b ∈ F^L`. -/
  b : Fin L → F
  /-- The quadratic system's coefficient vector `a ∈ F^{mℓ}`. -/
  quadA : Fin m → Fin ℓ → F
  /-- The quadratic system's constant vector `b′ ∈ F^{mℓ}`. -/
  quadB : Fin m → Fin ℓ → F

namespace Setup

/-- The side conditions the soundness proof uses: `η` has distinct entries (Def. 4.1), `ζ` has
distinct entries and `ℓ ≤ k` (Def. 4.2). -/
structure Valid (S : Setup F n m ℓ L) (k : ℕ) : Prop where
  η_injective : Function.Injective S.η
  ζ_injective : Function.Injective S.ζ
  ℓ_le_k : ℓ ≤ k

/-- The extended message `x` satisfies the constraint system: `A x = b`, and
`x ⊙ y + a ⊙ z = b′` at every row `i ∈ [m]` and position `c ∈ [ℓ]`. -/
structure Holds (S : Setup F n m ℓ L) (x : Message F m ℓ) : Prop where
  linear : S.A.mulVec x = S.b
  quadratic : ∀ i c,
    x ((.x, i), c) * x ((.y, i), c) + S.quadA i c * x ((.z, i), c) = S.quadB i c

/-- Some extended message satisfies the constraint system. -/
def Satisfiable (S : Setup F n m ℓ L) : Prop :=
  ∃ x, S.Holds x

/-- The value at `η_j` of the polynomial of degree `< ℓ` through the points `(ζ_c, v_c)`, in
Lagrange form. -/
def interp (S : Setup F n m ℓ L) (v : Fin ℓ → F) (j : Fin n) : F :=
  ∑ c, v c * Lagrange.basisEval univ S.ζ c (S.η j)

end Setup

/-- A (possibly malicious) section 4.7 oracle: the rows `U ∈ F^{4m×n}` and, for every repetition
`h ∈ [σ]`, the code test's blinding row `u^0_h`, the linear test's mask `u^add_h` and the
quadratic test's mask `u′^0_h`. Every row is an arbitrary vector of `F^n`. -/
structure Oracle (F : Type) (σ m n : ℕ) where
  /-- The rows `U^w, U^x, U^y, U^z`. -/
  U : Row m → Fin n → F
  /-- The code test's blinding rows `u^0_h`. -/
  codeMask : Fin σ → Fin n → F
  /-- The linear test's masks `u^add_h`. -/
  linMask : Fin σ → Fin n → F
  /-- The quadratic test's masks `u′^0_h`. -/
  quadMask : Fin σ → Fin n → F

/-- The verifier's challenges (section 4.7, step 1): for every repetition `h ∈ [σ]`,
`r_h ∈ F^{4m}`, `r^add_h ∈ F^L` (one coefficient per linear constraint) and `r^q_h ∈ F^m`. -/
structure Challenge (F : Type) (σ m ℓ L : ℕ) where
  /-- The code test's combinations `r_h`. -/
  code : Fin σ → Row m → F
  /-- The linear test's combinations `r^add_h`. -/
  lin : Fin σ → Fin L → F
  /-- The quadratic test's combinations `r^q_h`. -/
  quad : Fin σ → Fin m → F

namespace Challenge

/-- `Challenge` as a product of its three components. -/
def equivProd : Challenge F σ m ℓ L ≃
    (Fin σ → Row m → F) × (Fin σ → Fin L → F) × (Fin σ → Fin m → F) where
  toFun ch := (ch.code, ch.lin, ch.quad)
  invFun p := ⟨p.1, p.2.1, p.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance [Fintype F] [DecidableEq F] : Fintype (Challenge F σ m ℓ L) :=
  Fintype.ofEquiv _ equivProd.symm

end Challenge

/-- The prover's responses (section 4.7, step 2), for every repetition `h ∈ [σ]`: the code test's
`v_h ∈ L` as the `k` coefficients of its polynomial, and the coefficients of `q^add_h` (degree
`< k + ℓ − 1`) and of `p_{0,h}` (degree `< 2k − 1`). -/
structure Response (F : Type) (σ k ℓ : ℕ) where
  /-- The coefficients of the polynomial of `v_h`. -/
  code : Fin σ → Fin k → F
  /-- The coefficients of `q^add_h`. -/
  lin : Fin σ → Fin (k + ℓ - 1) → F
  /-- The coefficients of `p_{0,h}`. -/
  quad : Fin σ → Fin (2 * k - 1) → F

/-- A deterministic malicious prover: its responses as a function of all the challenges. -/
structure Prover (F : Type) (σ m ℓ L k : ℕ) where
  /-- The responses to the challenges. -/
  respond : Challenge F σ m ℓ L → Response F σ k ℓ

namespace Setup

variable (S : Setup F n m ℓ L)

/-- The coefficients `(r^add_h)^T A ∈ F^{4mℓ}` of the linear test's combination in repetition
`h`. -/
def linCoeff (ch : Challenge F σ m ℓ L) (h : Fin σ) : Cell m ℓ → F :=
  Matrix.vecMul (ch.lin h) S.A

/-- The linear test's algebraic check in repetition `h`:
`Σ_c q^add_h(ζ_c) = Σ_{i,c} r^add_{h,ic} · b_{ic}` (Figure 10, check 5(a); `= 0` in section 4.7). -/
def LinSum (ch : Challenge F σ m ℓ L) (π : Response F σ k ℓ) (h : Fin σ) : Prop :=
  ∑ c, evalCoeffs (π.lin h) (S.ζ c) = ∑ p, ch.lin h p * S.b p

/-- The quadratic test's algebraic check in repetition `h`: `p_{0,h}(ζ_c) = 0` for every `c`. -/
def QuadVanishes (π : Response F σ k ℓ) (h : Fin σ) : Prop :=
  ∀ c, evalCoeffs (π.quad h) (S.ζ c) = 0

/-- The code test's column check at `j` in repetition `h`:
`Σ_i r_{h,i} · U_{i,j} + u^0_h[j] = v_h[j]`. -/
def CodeColumn (O : Oracle F σ m n) (ch : Challenge F σ m ℓ L) (π : Response F σ k ℓ) (h : Fin σ)
    (j : Fin n) : Prop :=
  ∑ i, ch.code h i * O.U i j + O.codeMask h j = evalCoeffs (π.code h) (S.η j)

/-- The linear test's column check at `j` in repetition `h`:
`u^add_h[j] + Σ_i r^add_{h,i}(η_j) · U_{i,j} = q^add_h(η_j)`, where `r^add_{h,i}` is the
polynomial of degree `< ℓ` with `r^add_{h,i}(ζ_c) = ((r^add_h)^T A)_{ic}`. -/
def LinColumn (O : Oracle F σ m n) (ch : Challenge F σ m ℓ L) (π : Response F σ k ℓ) (h : Fin σ)
    (j : Fin n) : Prop :=
  O.linMask h j + ∑ i, S.interp (fun c => S.linCoeff ch h (i, c)) j * O.U i j =
    evalCoeffs (π.lin h) (S.η j)

/-- The quadratic test's column check at `j` in repetition `h`:
`p_{0,h}(η_j) = u′^0_h[j] + Σ_i r^q_{h,i} · (U^x_{i,j} U^y_{i,j} + U^a_{i,j} U^z_{i,j} − U^b_{i,j})`
with `U^a = Encode_ζ(a)`, `U^b = Encode_ζ(b′)` (Figure 11, check 5(b)). -/
def QuadColumn (O : Oracle F σ m n) (ch : Challenge F σ m ℓ L) (π : Response F σ k ℓ) (h : Fin σ)
    (j : Fin n) : Prop :=
  evalCoeffs (π.quad h) (S.η j) =
    O.quadMask h j + ∑ i, ch.quad h i *
      (O.U (.x, i) j * O.U (.y, i) j + S.interp (S.quadA i) j * O.U (.z, i) j -
        S.interp (S.quadB i) j)

/-- The algebraic checks of every repetition, which read the responses alone. -/
structure ResponseChecks (ch : Challenge F σ m ℓ L) (π : Response F σ k ℓ) : Prop where
  linSum : ∀ h, S.LinSum ch π h
  quadVanishes : ∀ h, S.QuadVanishes π h

/-- The three column checks of every repetition at column `j`. -/
structure ColumnChecks (O : Oracle F σ m n) (ch : Challenge F σ m ℓ L) (π : Response F σ k ℓ)
    (j : Fin n) : Prop where
  code : ∀ h, S.CodeColumn O ch π h j
  lin : ∀ h, S.LinColumn O ch π h j
  quad : ∀ h, S.QuadColumn O ch π h j

/-- The section 4.7 verifier accepts the oracle `O` with challenges `ch`, responses `π` and opened
columns `Q` (step 3). -/
structure Accepts (O : Oracle F σ m n) (ch : Challenge F σ m ℓ L) (π : Response F σ k ℓ)
    (Q : Finset (Fin n)) : Prop where
  response : S.ResponseChecks ch π
  columns : ∀ j ∈ Q, S.ColumnChecks O ch π j

theorem responseChecks_iff {ch : Challenge F σ m ℓ L} {π : Response F σ k ℓ} :
    S.ResponseChecks ch π ↔ (∀ h, S.LinSum ch π h) ∧ ∀ h, S.QuadVanishes π h :=
  ⟨fun h => ⟨h.linSum, h.quadVanishes⟩, fun h => ⟨h.1, h.2⟩⟩

theorem columnChecks_iff {O : Oracle F σ m n} {ch : Challenge F σ m ℓ L} {π : Response F σ k ℓ}
    {j : Fin n} :
    S.ColumnChecks O ch π j ↔
      (∀ h, S.CodeColumn O ch π h j) ∧ (∀ h, S.LinColumn O ch π h j) ∧
        ∀ h, S.QuadColumn O ch π h j :=
  ⟨fun h => ⟨h.code, h.lin, h.quad⟩, fun h => ⟨h.1, h.2.1, h.2.2⟩⟩

theorem accepts_iff {O : Oracle F σ m n} {ch : Challenge F σ m ℓ L} {π : Response F σ k ℓ}
    {Q : Finset (Fin n)} :
    S.Accepts O ch π Q ↔ S.ResponseChecks ch π ∧ ∀ j ∈ Q, S.ColumnChecks O ch π j :=
  ⟨fun h => ⟨h.response, h.columns⟩, fun h => ⟨h.1, h.2⟩⟩

variable [DecidableEq F]

instance (ch : Challenge F σ m ℓ L) (π : Response F σ k ℓ) (h : Fin σ) :
    Decidable (S.LinSum ch π h) :=
  inferInstanceAs (Decidable (_ = _))

instance (π : Response F σ k ℓ) (h : Fin σ) : Decidable (S.QuadVanishes π h) :=
  inferInstanceAs (Decidable (∀ _, _))

instance (O : Oracle F σ m n) (ch : Challenge F σ m ℓ L) (π : Response F σ k ℓ) (h : Fin σ)
    (j : Fin n) : Decidable (S.CodeColumn O ch π h j) :=
  inferInstanceAs (Decidable (_ = _))

instance (O : Oracle F σ m n) (ch : Challenge F σ m ℓ L) (π : Response F σ k ℓ) (h : Fin σ)
    (j : Fin n) : Decidable (S.LinColumn O ch π h j) :=
  inferInstanceAs (Decidable (_ = _))

instance (O : Oracle F σ m n) (ch : Challenge F σ m ℓ L) (π : Response F σ k ℓ) (h : Fin σ)
    (j : Fin n) : Decidable (S.QuadColumn O ch π h j) :=
  inferInstanceAs (Decidable (_ = _))

instance (ch : Challenge F σ m ℓ L) (π : Response F σ k ℓ) : Decidable (S.ResponseChecks ch π) :=
  decidable_of_iff _ S.responseChecks_iff.symm

instance (O : Oracle F σ m n) (ch : Challenge F σ m ℓ L) (π : Response F σ k ℓ) (j : Fin n) :
    Decidable (S.ColumnChecks O ch π j) :=
  decidable_of_iff _ S.columnChecks_iff.symm

instance (O : Oracle F σ m n) (ch : Challenge F σ m ℓ L) (π : Response F σ k ℓ)
    (Q : Finset (Fin n)) : Decidable (S.Accepts O ch π Q) :=
  decidable_of_iff _ S.accepts_iff.symm

variable [Fintype F]

/-- The probability that the section 4.7 verifier accepts the oracle `O` against the prover `P`
with `t` opened columns: the challenges uniform on `Challenge F σ m ℓ L` and, independently, `Q`
uniform among the `t`-subsets of `[n]`. -/
def acceptProb (t : ℕ) (O : Oracle F σ m n) (P : Prover F σ m ℓ L k) : ℚ :=
  queryProb (Challenge F σ m ℓ L) n t fun ch Q => S.Accepts O ch (P.respond ch) Q

/-- For each challenge passing the algebraic checks, the accepted opened sets are the `t`-subsets
of the columns passing all column checks. -/
theorem acceptProb_eq (t : ℕ) (O : Oracle F σ m n) (P : Prover F σ m ℓ L k) :
    S.acceptProb t O P =
      ((∑ ch, if S.ResponseChecks ch (P.respond ch) then
          (#{j | S.ColumnChecks O ch (P.respond ch) j}).choose t else 0 : ℕ) : ℚ) /
        (Fintype.card (Challenge F σ m ℓ L) * n.choose t) :=
  queryProb_eq_sum _ _ fun _ _ => S.accepts_iff

end Setup

/-! ## Proof -/

section Proof

open Polynomial GordieHowe.InterleavedProximity GordieHowe.RepetitionCounting

namespace Challenge

/-- `Challenge` with the linear test's combinations first. -/
def linEquiv : Challenge F σ m ℓ L ≃
    (Fin σ → Fin L → F) × ((Fin σ → Row m → F) × (Fin σ → Fin m → F)) where
  toFun ch := (ch.lin, ch.code, ch.quad)
  invFun p := ⟨p.2.1, p.1, p.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- `Challenge` with the quadratic test's combinations first. -/
def quadEquiv : Challenge F σ m ℓ L ≃
    (Fin σ → Fin m → F) × ((Fin σ → Row m → F) × (Fin σ → Fin L → F)) where
  toFun ch := (ch.quad, ch.code, ch.lin)
  invFun p := ⟨p.2.1, p.2.2, p.1⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : Nonempty (Challenge F σ m ℓ L) :=
  ⟨⟨fun _ _ => 0, fun _ _ => 0, fun _ _ => 0⟩⟩

end Challenge

namespace Setup

variable (S : Setup F n m ℓ L)

/-- The codeword rows whose polynomials have the coefficient vectors `cf`. -/
def rows (cf : Row m → Fin k → F) : Row m → Fin n → F :=
  fun i => rsEval S.η k (cf i)

theorem rows_mem (cf : Row m → Fin k → F) (i : Row m) : S.rows cf i ∈ rsCode S.η k :=
  LinearMap.mem_range_self _ _

/-- The extended message `Decode_ζ` of the rows with coefficient vectors `cf` (Def. 4.2): row
`i`'s polynomial evaluated at `ζ_c`. -/
def decoded (cf : Row m → Fin k → F) : Message F m ℓ :=
  fun q => evalCoeffs (cf q.1) (S.ζ q.2)

/-- The quadratic system's residual `x ⊙ y + a ⊙ z − b′` of the decoded message at row `i` and
position `c`. -/
def quadResidual (cf : Row m → Fin k → F) (i : Fin m) (c : Fin ℓ) : F :=
  S.decoded cf ((.x, i), c) * S.decoded cf ((.y, i), c) + S.quadA i c * S.decoded cf ((.z, i), c) -
    S.quadB i c

/-- A decoded message violating the constraint system violates the linear system or one
quadratic constraint. -/
theorem linear_or_quadratic_of_not_holds {cf : Row m → Fin k → F} (h : ¬ S.Holds (S.decoded cf)) :
    S.A.mulVec (S.decoded cf) ≠ S.b ∨ ∃ i c, S.quadResidual cf i c ≠ 0 := by
  by_contra hc
  simp only [not_or, not_exists, not_not, ne_eq] at hc
  exact h ⟨hc.1, fun i c => sub_eq_zero.mp (hc.2 i c)⟩

/-- The interpolation polynomial of degree `< ℓ` through the points `(ζ_c, v_c)`. -/
noncomputable def interpPoly (v : Fin ℓ → F) : F[X] :=
  Lagrange.interpolate univ S.ζ v

theorem eval_interpPoly_η (v : Fin ℓ → F) (j : Fin n) :
    (S.interpPoly v).eval (S.η j) = S.interp v j := by
  simp [interpPoly, Lagrange.interpolate_apply, eval_finsetSum, Lagrange.eval_basis_eq_basisEval,
    interp]

theorem eval_interpPoly_ζ (hζ : Function.Injective S.ζ) (v : Fin ℓ → F) (c : Fin ℓ) :
    (S.interpPoly v).eval (S.ζ c) = v c :=
  Lagrange.eval_interpolate_at_node (r := v) hζ.injOn (mem_univ c)

theorem natDegree_interpPoly_le (hζ : Function.Injective S.ζ) (v : Fin ℓ → F) :
    (S.interpPoly v).natDegree ≤ ℓ - 1 := by
  have h := Lagrange.degree_interpolate_lt (r := v) hζ.injOn (s := univ)
  rw [card_univ, Fintype.card_fin] at h
  by_cases hp : S.interpPoly v = 0
  · rw [hp, natDegree_zero]
    exact Nat.zero_le _
  · have := (natDegree_lt_iff_degree_lt hp).mpr h
    omega

/-- Row `i` of the quadratic test's polynomial on the rows `cf`:
`p^x_i · p^y_i + p^a_i · p^z_i − p^b_i`. -/
noncomputable def quadPoly (cf : Row m → Fin k → F) (i : Fin m) : F[X] :=
  ofCoeffs (cf (.x, i)) * ofCoeffs (cf (.y, i)) + S.interpPoly (S.quadA i) * ofCoeffs (cf (.z, i)) -
    S.interpPoly (S.quadB i)

/-- The quadratic test's polynomial `P(X) = Σ_i r_i · (p^x_i p^y_i + p^a_i p^z_i − p^b_i)(X)` on
the rows `cf`. -/
noncomputable def quadComb (cf : Row m → Fin k → F) (r : Fin m → F) : F[X] :=
  ∑ i, C (r i) * S.quadPoly cf i

theorem eval_quadComb_η (cf : Row m → Fin k → F) (r : Fin m → F) (j : Fin n) :
    (S.quadComb cf r).eval (S.η j) = ∑ i, r i *
      (S.rows cf (.x, i) j * S.rows cf (.y, i) j + S.interp (S.quadA i) j * S.rows cf (.z, i) j -
        S.interp (S.quadB i) j) := by
  simp [quadComb, quadPoly, eval_finsetSum, eval_ofCoeffs, eval_interpPoly_η, rows]

theorem eval_quadComb_ζ (hζ : Function.Injective S.ζ) (cf : Row m → Fin k → F) (r : Fin m → F)
    (c : Fin ℓ) : (S.quadComb cf r).eval (S.ζ c) = ∑ i, r i * S.quadResidual cf i c := by
  simp [quadComb, quadPoly, eval_finsetSum, eval_ofCoeffs, S.eval_interpPoly_ζ hζ, quadResidual,
    decoded]

theorem natDegree_quadComb_le (hS : S.Valid k) (cf : Row m → Fin k → F) (r : Fin m → F) :
    (S.quadComb cf r).natDegree ≤ 2 * k - 2 := by
  refine natDegree_sum_le_of_forall_le _ _ fun i _ => (natDegree_C_mul_le _ _).trans ?_
  have hx := natDegree_ofCoeffs_le (cf (.x, i))
  have hy := natDegree_ofCoeffs_le (cf (.y, i))
  have hz := natDegree_ofCoeffs_le (cf (.z, i))
  have ha := S.natDegree_interpPoly_le hS.ζ_injective (S.quadA i)
  have hb := S.natDegree_interpPoly_le hS.ζ_injective (S.quadB i)
  have hℓ := hS.ℓ_le_k
  refine (natDegree_sub_le _ _).trans (max_le ((natDegree_add_le _ _).trans (max_le
    (natDegree_mul_le.trans ?_) (natDegree_mul_le.trans ?_))) ?_) <;> omega

/-- The linear test's polynomial `Σ_i r^add_i(X) · p_i(X)` on the rows `cf`, where `r^add_i` is
the polynomial of degree `< ℓ` through `((r^T A)_{i,c})_c`. -/
noncomputable def linComb (cf : Row m → Fin k → F) (r : Fin L → F) : F[X] :=
  ∑ i, S.interpPoly (fun c => Matrix.vecMul r S.A (i, c)) * ofCoeffs (cf i)

theorem eval_linComb_η (cf : Row m → Fin k → F) (r : Fin L → F) (j : Fin n) :
    (S.linComb cf r).eval (S.η j) =
      ∑ i, S.interp (fun c => Matrix.vecMul r S.A (i, c)) j * S.rows cf i j := by
  simp [linComb, eval_finsetSum, eval_ofCoeffs, eval_interpPoly_η, rows]

theorem sum_eval_linComb_ζ (hζ : Function.Injective S.ζ) (cf : Row m → Fin k → F)
    (r : Fin L → F) :
    ∑ c, (S.linComb cf r).eval (S.ζ c) = ∑ p, r p * S.A.mulVec (S.decoded cf) p := by
  simp only [linComb, eval_finsetSum, eval_mul, eval_ofCoeffs, S.eval_interpPoly_ζ hζ]
  rw [Finset.sum_comm]
  change ∑ i : Row m, ∑ c : Fin ℓ, Matrix.vecMul r S.A (i, c) * S.decoded cf (i, c) = _
  rw [← Fintype.sum_prod_type']
  exact (Matrix.dotProduct_mulVec r S.A (S.decoded cf)).symm

theorem natDegree_linComb_le (hS : S.Valid k) (cf : Row m → Fin k → F) (r : Fin L → F) :
    (S.linComb cf r).natDegree ≤ 2 * k - 2 := by
  refine natDegree_sum_le_of_forall_le _ _ fun i _ => natDegree_mul_le.trans ?_
  have h₁ := S.natDegree_interpPoly_le hS.ζ_injective fun c => Matrix.vecMul r S.A (i, c)
  have h₂ := natDegree_ofCoeffs_le (cf i)
  have hℓ := hS.ℓ_le_k
  omega

end Setup

variable [DecidableEq F]

/-- A mask candidate: a polynomial of degree `≤ D` agreeing with the mask `u` at more than
`(n + D)/2` of the points `η`. -/
def MaskCand (η : Fin n → F) (D : ℕ) (u : Fin n → F) (g : F[X]) : Prop :=
  g.natDegree ≤ D ∧ n + D < 2 * #{j | g.eval (η j) = u j}

/-- There is at most one mask candidate: two would agree with each other at more than `D`
points. -/
theorem MaskCand.eq {η : Fin n → F} (hη : Function.Injective η) {D : ℕ} {u : Fin n → F}
    {g g' : F[X]} (hg : MaskCand η D u g) (hg' : MaskCand η D u g') : g = g' := by
  by_contra hne
  have hsub : (univ.filter fun j => g.eval (η j) = u j) ∩
      (univ.filter fun j => g'.eval (η j) = u j) ⊆
        univ.filter fun j => (g - g').eval (η j) = 0 := by
    intro j hj
    simp only [mem_inter, mem_filter, mem_univ, true_and] at hj ⊢
    rw [eval_sub, hj.1, hj.2, sub_self]
  have hz := RSCode.BerlekampWelch.card_filter_eval_eq_zero_le hη (sub_ne_zero.mpr hne)
  have hdeg : (g - g').natDegree ≤ D := (natDegree_sub_le _ _).trans (max_le hg.1 hg'.1)
  have hU := card_union_add_card_inter (univ.filter fun j => g.eval (η j) = u j)
    (univ.filter fun j => g'.eval (η j) = u j)
  have hun : #((univ.filter fun j => g.eval (η j) = u j) ∪
      (univ.filter fun j => g'.eval (η j) = u j)) ≤ n :=
    (card_le_univ _).trans (by simp)
  have := card_le_card hsub
  have h1 := hg.2
  have h2 := hg'.2
  omega

/-- A masked test's bad event: some mask candidate passes the algebraic check `Alg` at the
challenge. If each fixed polynomial passes for at most `|X|/|F|` challenges, so does the event. -/
theorem card_maskBad_mul_le [Fintype F] {X : Type*} [Fintype X] {η : Fin n → F}
    (hη : Function.Injective η) (D : ℕ) (u : Fin n → F) (Alg : F[X] → X → Prop)
    (hAlg : ∀ g, ∀ [DecidablePred (Alg g)], #{x | Alg g x} * Fintype.card F ≤ Fintype.card X)
    [DecidablePred fun x => ∃ g, MaskCand η D u g ∧ Alg g x] :
    #{x | ∃ g, MaskCand η D u g ∧ Alg g x} * Fintype.card F ≤ Fintype.card X :=
  card_filter_exists_mul_le_of_subsingleton _ (fun _ _ hg hg' => hg.eq hη hg') Alg
    fun g _ => hAlg g

/-- A code-test candidate: a codeword agreeing with the blinding row `u` at more than
`(n − |E| + (n − d))/2` of the columns outside `E`. -/
def CodeCand (C : Submodule F (Fin n → F)) (d : ℕ) (E : Finset (Fin n)) (u c : Fin n → F) :
    Prop :=
  c ∈ C ∧ (n - #E) + (n - d) < 2 * #{j | j ∉ E ∧ c j = u j}

/-- There is at most one code-test candidate: two distinct codewords agree on at most `n − d`
columns. -/
theorem CodeCand.eq {C : Submodule F (Fin n → F)} {d : ℕ} (hC : IsMinDist C d)
    {E : Finset (Fin n)} {u c c' : Fin n → F} (hc : CodeCand C d E u c)
    (hc' : CodeCand C d E u c') : c = c' := by
  by_contra hne
  have hagree := hC.card_agree_le hc.1 hc'.1 hne
  have hsub : (univ.filter fun j => j ∉ E ∧ c j = u j) ∩
      (univ.filter fun j => j ∉ E ∧ c' j = u j) ⊆ univ.filter fun j => c j = c' j := by
    intro j hj
    simp only [mem_inter, mem_filter, mem_univ, true_and] at hj ⊢
    rw [hj.1.2, hj.2.2]
  have hun : (univ.filter fun j => j ∉ E ∧ c j = u j) ∪
      (univ.filter fun j => j ∉ E ∧ c' j = u j) ⊆ Eᶜ := by
    intro j hj
    simp only [mem_union, mem_filter, mem_univ, true_and] at hj
    rw [mem_compl]
    rcases hj with h | h
    · exact h.1
    · exact h.1
  have hU := card_union_add_card_inter (univ.filter fun j => j ∉ E ∧ c j = u j)
    (univ.filter fun j => j ∉ E ∧ c' j = u j)
  have hcompl : #Eᶜ = n - #E := by rw [card_compl, Fintype.card_fin]
  have := card_le_card hsub
  have := card_le_card hun
  have h1 := hc.2
  have h2 := hc'.2
  omega

namespace Setup

variable (S : Setup F n m ℓ L)

/-- The code test's bad event in the close case: some error column passes the code check in
every repetition against the repetition's code-test candidate. -/
def CodeBad (O : Oracle F σ m n) (cf : Row m → Fin k → F) (r : Fin σ → Row m → F) : Prop :=
  ∃ j ∈ colErrors O.U (S.rows cf), ∀ h, ∃ c,
    CodeCand (rsCode S.η k) (n - k + 1) (colErrors O.U (S.rows cf)) (O.codeMask h) c ∧
      c j = O.codeMask h j + ∑ i, r h i * (O.U i j - S.rows cf i j)

/-- The quadratic test's bad event in the close case: in every repetition the mask candidate
passes check 5(a) against the challenge. -/
def QuadBad (O : Oracle F σ m n) (cf : Row m → Fin k → F) (r : Fin σ → Fin m → F) : Prop :=
  ∀ h, ∃ g, MaskCand S.η (2 * k - 2) (O.quadMask h) g ∧
    ∀ c, g.eval (S.ζ c) + (S.quadComb cf (r h)).eval (S.ζ c) = 0

/-- The linear test's bad event in the close case: in every repetition the mask candidate passes
the sum check against the challenge. -/
def LinBad (O : Oracle F σ m n) (cf : Row m → Fin k → F) (r : Fin σ → Fin L → F) : Prop :=
  ∀ h, ∃ g, MaskCand S.η (2 * k - 2) (O.linMask h) g ∧
    ∑ c, g.eval (S.ζ c) = ∑ p, r h p * (S.b p - S.A.mulVec (S.decoded cf) p)

variable [Fintype F]

/-- The code test's bad event has density at most `|E|/|F|^σ`: a fixed error column `j` passes
against the (unique) candidate in repetition `h` only on an affine condition on `r_h` with the
nonzero coefficients `χ_j = U[j] − V[j]`. -/
theorem card_codeBad_mul_le (hS : S.Valid k) (O : Oracle F σ m n) (cf : Row m → Fin k → F)
    [DecidablePred (S.CodeBad O cf)] :
    #{r | S.CodeBad O cf r} * Fintype.card F ^ σ ≤
      #(colErrors O.U (S.rows cf)) * Fintype.card (Fin σ → Row m → F) := by
  classical
  set E := colErrors O.U (S.rows cf)
  let B : Fin n → Fin σ → Finset (Row m → F) := fun j h =>
    univ.filter fun x => ∃ c, CodeCand (rsCode S.η k) (n - k + 1) E (O.codeMask h) c ∧
      c j = O.codeMask h j + ∑ i, x i * (O.U i j - S.rows cf i j)
  have hsub : (univ.filter fun r => S.CodeBad O cf r) ⊆
      E.biUnion fun j => Fintype.piFinset (B j) := by
    intro r hr
    obtain ⟨j, hj, hall⟩ := (mem_filter.mp hr).2
    refine mem_biUnion.mpr ⟨j, hj, Fintype.mem_piFinset.mpr fun h => ?_⟩
    simp only [B, mem_filter, mem_univ, true_and]
    exact hall h
  have hB : ∀ j ∈ E, ∀ h, #(B j h) * Fintype.card F ≤ Fintype.card (Row m → F) := by
    intro j hj h
    refine card_filter_exists_mul_le_of_subsingleton _
      (fun _ _ hc hc' => hc.eq (rsCode_isMinDist hS.η_injective k) hc') _ fun c _ => ?_
    intro _
    have hχ : (fun i => O.U i j - S.rows cf i j) ≠ 0 := by
      obtain ⟨i, hi⟩ := mem_colErrors.mp hj
      intro h0
      exact hi (sub_eq_zero.mp (congrFun h0 i))
    have hcount := card_filter_sum_mul_eq_mul_le hχ (c j - O.codeMask h j)
    rw [← Fintype.card_fun] at hcount
    refine le_trans (Nat.mul_le_mul_right _ (card_le_card ?_)) hcount
    intro x hx
    simp only [mem_filter, mem_univ, true_and] at hx ⊢
    rw [hx]
    ring
  calc _ ≤ #(E.biUnion fun j => Fintype.piFinset (B j)) * Fintype.card F ^ σ :=
        Nat.mul_le_mul_right _ (card_le_card hsub)
    _ ≤ #E * Fintype.card (Row m → F) ^ σ := card_biUnion_piFinset_mul_pow_le E B hB
    _ = #E * Fintype.card (Fin σ → Row m → F) := by rw [card_fin_fun (X := Row m → F)]

/-- The quadratic test's bad event has density at most `1/|F|^σ` when the decoded message
violates a quadratic constraint. -/
theorem card_quadBad_mul_le (hS : S.Valid k) (O : Oracle F σ m n) (cf : Row m → Fin k → F)
    {i₀ : Fin m} {c₀ : Fin ℓ} (hres : S.quadResidual cf i₀ c₀ ≠ 0)
    [DecidablePred (S.QuadBad O cf)] :
    #{r | S.QuadBad O cf r} * Fintype.card F ^ σ ≤ 1 * Fintype.card (Fin σ → Fin m → F) := by
  classical
  let B : Fin σ → Finset (Fin m → F) := fun h =>
    univ.filter fun x => ∃ g, MaskCand S.η (2 * k - 2) (O.quadMask h) g ∧
      ∀ c, g.eval (S.ζ c) + (S.quadComb cf x).eval (S.ζ c) = 0
  have hsub : (univ.filter fun r => S.QuadBad O cf r) ⊆ Fintype.piFinset B := by
    intro r hr
    have hr' : S.QuadBad O cf r := (mem_filter.mp hr).2
    refine Fintype.mem_piFinset.mpr fun h => ?_
    simp only [B, mem_filter, mem_univ, true_and]
    exact hr' h
  have hne : (fun i => S.quadResidual cf i c₀) ≠ 0 := fun h0 => hres (congrFun h0 i₀)
  have hB : ∀ h, #(B h) * Fintype.card F ≤ Fintype.card (Fin m → F) := by
    intro h
    refine card_maskBad_mul_le hS.η_injective _ _
      (fun g x => ∀ c, g.eval (S.ζ c) + (S.quadComb cf x).eval (S.ζ c) = 0) fun g => ?_
    intro _
    have hcount := card_filter_sum_mul_eq_mul_le hne (-g.eval (S.ζ c₀))
    rw [← Fintype.card_fun] at hcount
    refine le_trans (Nat.mul_le_mul_right _ (card_le_card ?_)) hcount
    intro x hx
    simp only [mem_filter, mem_univ, true_and] at hx ⊢
    have := hx c₀
    rw [S.eval_quadComb_ζ hS.ζ_injective] at this
    linear_combination this
  calc _ ≤ #(Fintype.piFinset B) * Fintype.card F ^ σ :=
        Nat.mul_le_mul_right _ (card_le_card hsub)
    _ ≤ Fintype.card (Fin m → F) ^ σ := card_piFinset_mul_pow_le B hB
    _ = 1 * Fintype.card (Fin σ → Fin m → F) := by
        rw [one_mul, card_fin_fun (X := Fin m → F)]

/-- The linear test's bad event has density at most `1/|F|^σ` when the decoded message violates
the linear system. -/
theorem card_linBad_mul_le (hS : S.Valid k) (O : Oracle F σ m n) (cf : Row m → Fin k → F)
    (hlin : S.A.mulVec (S.decoded cf) ≠ S.b) [DecidablePred (S.LinBad O cf)] :
    #{r | S.LinBad O cf r} * Fintype.card F ^ σ ≤ 1 * Fintype.card (Fin σ → Fin L → F) := by
  classical
  let B : Fin σ → Finset (Fin L → F) := fun h =>
    univ.filter fun x => ∃ g, MaskCand S.η (2 * k - 2) (O.linMask h) g ∧
      ∑ c, g.eval (S.ζ c) = ∑ p, x p * (S.b p - S.A.mulVec (S.decoded cf) p)
  have hsub : (univ.filter fun r => S.LinBad O cf r) ⊆ Fintype.piFinset B := by
    intro r hr
    have hr' : S.LinBad O cf r := (mem_filter.mp hr).2
    refine Fintype.mem_piFinset.mpr fun h => ?_
    simp only [B, mem_filter, mem_univ, true_and]
    exact hr' h
  have hne : (fun p => S.b p - S.A.mulVec (S.decoded cf) p) ≠ 0 := by
    intro h0
    exact hlin (funext fun p => (sub_eq_zero.mp (congrFun h0 p)).symm)
  have hB : ∀ h, #(B h) * Fintype.card F ≤ Fintype.card (Fin L → F) := by
    intro h
    have key := card_maskBad_mul_le (X := Fin L → F) hS.η_injective (2 * k - 2) (O.linMask h)
      (fun g x => ∑ c, g.eval (S.ζ c) = ∑ p, x p * (S.b p - S.A.mulVec (S.decoded cf) p))
      fun g => by
        intro _
        have hcount := card_filter_sum_mul_eq_mul_le hne (∑ c, g.eval (S.ζ c))
        rw [← Fintype.card_fun] at hcount
        refine le_trans (Nat.mul_le_mul_right _ (card_le_card ?_)) hcount
        intro x hx
        simp only [mem_filter, mem_univ, true_and] at hx ⊢
        exact hx.symm
    refine le_trans (Nat.mul_le_mul_right _ (card_le_card fun x hx => ?_)) key
    simp only [B, mem_filter, mem_univ, true_and] at hx ⊢
    exact hx
  calc _ ≤ #(Fintype.piFinset B) * Fintype.card F ^ σ :=
        Nat.mul_le_mul_right _ (card_le_card hsub)
    _ ≤ Fintype.card (Fin L → F) ^ σ := card_piFinset_mul_pow_le B hB
    _ = 1 * Fintype.card (Fin σ → Fin L → F) := by
        rw [one_mul, card_fin_fun (X := Fin L → F)]

omit [Fintype F] in
/-- **The code test in the close case.** Outside the code test's bad event, either the opened
columns passing all checks number at most `n − e` (some repetition's response is not the
candidate: its agreement off `E` is at most half of `n − |E| + (n − d)`, and `3e ≤ d`), or none
of them is an error column. -/
theorem card_columns_le_or_disjoint {e : ℕ} (he : 4 * e < n - k + 1) {O : Oracle F σ m n}
    {cf : Row m → Fin k → F} (hE : #(colErrors O.U (S.rows cf)) ≤ e)
    {ch : Challenge F σ m ℓ L} {π : Response F σ k ℓ} (hbad : ¬ S.CodeBad O cf ch.code) :
    #{j | S.ColumnChecks O ch π j} ≤ n - e ∨
      ∀ j, S.ColumnChecks O ch π j → j ∉ colErrors O.U (S.rows cf) := by
  set E := colErrors O.U (S.rows cf)
  let cand : Fin σ → Fin n → F := fun h =>
    rsEval S.η k (π.code h) - combo (ch.code h) (S.rows cf)
  have hmem : ∀ h, cand h ∈ rsCode S.η k := fun h =>
    (rsCode S.η k).sub_mem (LinearMap.mem_range_self _ _) (combo_mem _ (S.rows_mem cf))
  have hcol : ∀ h j, S.CodeColumn O ch π h j →
      cand h j = O.codeMask h j + ∑ i, ch.code h i * (O.U i j - S.rows cf i j) := by
    intro h j hj
    simp only [CodeColumn] at hj
    simp only [cand, Pi.sub_apply, rsEval_apply, combo, ← hj, mul_sub, sum_sub_distrib]
    ring
  by_cases hall : ∀ h, CodeCand (rsCode S.η k) (n - k + 1) E (O.codeMask h) (cand h)
  · right
    intro j hj hjE
    exact hbad ⟨j, hjE, fun h => ⟨cand h, hall h, hcol h j (hj.code h)⟩⟩
  · left
    simp only [not_forall] at hall
    obtain ⟨h, hh⟩ := hall
    have hthr : 2 * #{j | j ∉ E ∧ cand h j = O.codeMask h j} ≤ (n - #E) + (n - (n - k + 1)) := by
      by_contra hlt
      exact hh ⟨hmem h, by omega⟩
    have hsub : (univ.filter fun j => S.ColumnChecks O ch π j) ⊆
        (univ.filter fun j => j ∉ E ∧ cand h j = O.codeMask h j) ∪ E := by
      intro j hj
      simp only [mem_filter, mem_univ, true_and, mem_union] at hj ⊢
      by_cases hjE : j ∈ E
      · exact Or.inr hjE
      · refine Or.inl ⟨hjE, ?_⟩
        have hzero : ∀ i, O.U i j - S.rows cf i j = 0 := fun i => by
          by_contra hne
          exact hjE (mem_colErrors.mpr ⟨i, sub_ne_zero.mp hne⟩)
        simpa [hzero] using hcol h j (hj.code h)
    have hA : #{j | j ∉ E ∧ cand h j = O.codeMask h j} ≤ n - #E := by
      have hc : #Eᶜ = n - #E := by rw [card_compl, Fintype.card_fin]
      rw [← hc]
      exact card_le_card fun j hj => mem_compl.mpr (mem_filter.mp hj).2.1
    have hEn : #E ≤ n := (card_le_univ E).trans (by simp)
    have := (card_le_card hsub).trans (card_union_le _ _)
    omega

omit [Fintype F] in
/-- **The quadratic test in the close case.** Outside the quadratic test's bad event, an accepted
challenge has at most `(n + 2k − 2)/2` columns outside `E` passing all checks: in some repetition
`g = p_{0,h} − P_h` is not the mask candidate, and off `E` the quadratic column check is
`g(η_j) = u′^0_h[j]`. -/
theorem card_columns_compl_le_of_quad (hS : S.Valid k) {O : Oracle F σ m n}
    {cf : Row m → Fin k → F} {ch : Challenge F σ m ℓ L} {π : Response F σ k ℓ}
    (hresp : S.ResponseChecks ch π) (hbad : ¬ S.QuadBad O cf ch.quad) :
    #{j | S.ColumnChecks O ch π j ∧ j ∉ colErrors O.U (S.rows cf)} ≤ (n + (2 * k - 2)) / 2 := by
  simp only [QuadBad, not_forall] at hbad
  obtain ⟨h, hh⟩ := hbad
  set g := ofCoeffs (π.quad h) - S.quadComb cf (ch.quad h)
  have hdeg : g.natDegree ≤ 2 * k - 2 :=
    (natDegree_sub_le _ _).trans (max_le ((natDegree_ofCoeffs_le _).trans (by omega))
      (S.natDegree_quadComb_le hS cf _))
  have halg : ∀ c, g.eval (S.ζ c) + (S.quadComb cf (ch.quad h)).eval (S.ζ c) = 0 := by
    intro c
    have hv : evalCoeffs (π.quad h) (S.ζ c) = 0 := hresp.quadVanishes h c
    rw [eval_sub, eval_ofCoeffs, hv]
    ring
  have hnot : ¬ n + (2 * k - 2) < 2 * #{j | g.eval (S.η j) = O.quadMask h j} :=
    fun hlt => hh ⟨g, ⟨hdeg, hlt⟩, halg⟩
  have hsub : (univ.filter fun j => S.ColumnChecks O ch π j ∧ j ∉ colErrors O.U (S.rows cf)) ⊆
      univ.filter fun j => g.eval (S.η j) = O.quadMask h j := by
    intro j hj
    simp only [mem_filter, mem_univ, true_and] at hj ⊢
    obtain ⟨hc, hjE⟩ := hj
    have hrow : ∀ i, O.U i j = S.rows cf i j := fun i => by
      by_contra hne
      exact hjE (mem_colErrors.mpr ⟨i, hne⟩)
    have hq : evalCoeffs (π.quad h) (S.η j) = _ := hc.quad h
    simp only [hrow] at hq
    rw [eval_sub, eval_ofCoeffs, hq, S.eval_quadComb_η]
    ring
  have := card_le_card hsub
  omega

omit [Fintype F] in
/-- **The linear test in the close case**, as `card_columns_compl_le_of_quad`, with
`g = q^add_h − Σ_i r^add_i p_i` of degree `≤ k + ℓ − 2 ≤ 2k − 2`. -/
theorem card_columns_compl_le_of_lin (hS : S.Valid k) {O : Oracle F σ m n}
    {cf : Row m → Fin k → F} {ch : Challenge F σ m ℓ L} {π : Response F σ k ℓ}
    (hresp : S.ResponseChecks ch π) (hbad : ¬ S.LinBad O cf ch.lin) :
    #{j | S.ColumnChecks O ch π j ∧ j ∉ colErrors O.U (S.rows cf)} ≤ (n + (2 * k - 2)) / 2 := by
  simp only [LinBad, not_forall] at hbad
  obtain ⟨h, hh⟩ := hbad
  set g := ofCoeffs (π.lin h) - S.linComb cf (ch.lin h)
  have hℓ := hS.ℓ_le_k
  have hdeg : g.natDegree ≤ 2 * k - 2 :=
    (natDegree_sub_le _ _).trans (max_le ((natDegree_ofCoeffs_le _).trans (by omega))
      (S.natDegree_linComb_le hS cf _))
  have halg : ∑ c, g.eval (S.ζ c) =
      ∑ p, ch.lin h p * (S.b p - S.A.mulVec (S.decoded cf) p) := by
    have hs : ∑ c, evalCoeffs (π.lin h) (S.ζ c) = ∑ p, ch.lin h p * S.b p := hresp.linSum h
    simp only [g, eval_sub, eval_ofCoeffs, sum_sub_distrib, hs,
      S.sum_eval_linComb_ζ hS.ζ_injective, mul_sub]
  have hnot : ¬ n + (2 * k - 2) < 2 * #{j | g.eval (S.η j) = O.linMask h j} :=
    fun hlt => hh ⟨g, ⟨hdeg, hlt⟩, halg⟩
  have hsub : (univ.filter fun j => S.ColumnChecks O ch π j ∧ j ∉ colErrors O.U (S.rows cf)) ⊆
      univ.filter fun j => g.eval (S.η j) = O.linMask h j := by
    intro j hj
    simp only [mem_filter, mem_univ, true_and] at hj ⊢
    obtain ⟨hc, hjE⟩ := hj
    have hrow : ∀ i, O.U i j = S.rows cf i j := fun i => by
      by_contra hne
      exact hjE (mem_colErrors.mpr ⟨i, hne⟩)
    have hq : O.linMask h j + _ = evalCoeffs (π.lin h) (S.η j) := hc.lin h
    simp only [hrow, linCoeff] at hq
    rw [eval_sub, eval_ofCoeffs, ← hq, S.eval_linComb_η]
    ring
  have := card_le_card hsub
  omega

/-- **The far case.** If `U` is not `e`-close to `L^{4m}`, the code test's joint event (the rows
`r_h^T U + u^0_h` jointly `e`-close to `L^σ`) has density at most `(e + 1)/|F|^σ`
(`card_close_mul_le`), and outside it at most `n − e` columns pass all checks. -/
theorem exists_bad_far (hS : S.Valid k) {e : ℕ} (he : 4 * e < n - k + 1) (O : Oracle F σ m n)
    (hfar : ¬ InterleavedProximity.Close (rsCode S.η k) e O.U) (P : Prover F σ m ℓ L k) :
    ∃ Bad : Finset (Challenge F σ m ℓ L),
      #Bad * Fintype.card F ^ σ ≤ (e + 1) * Fintype.card (Challenge F σ m ℓ L) ∧
        ∀ ch ∉ Bad, #{j | S.ColumnChecks O ch (P.respond ch) j} ≤ n - e := by
  classical
  refine ⟨univ.filter fun ch =>
      InterleavedProximity.Close (rsCode S.η k) e fun h => combo (ch.code h) O.U + O.codeMask h, ?_, ?_⟩
  · have h₁ := card_close_mul_le (rsCode_isMinDist hS.η_injective k) he hfar O.codeMask
    rw [← card_fin_fun (X := Row m → F)] at h₁
    exact card_filter_fst_mul_le Challenge.equivProd
      (fun r => InterleavedProximity.Close (rsCode S.η k) e fun h => combo (r h) O.U + O.codeMask h) h₁
  · intro ch hch
    simp only [mem_filter, mem_univ, true_and] at hch
    let v : Fin σ → Fin n → F := fun h => rsEval S.η k ((P.respond ch).code h)
    have hnot : e < #(colErrors (fun h => combo (ch.code h) O.U + O.codeMask h) v) := by
      by_contra hle
      exact hch ⟨v, fun h => LinearMap.mem_range_self _ _, Nat.le_of_not_lt hle⟩
    have hsub : (univ.filter fun j => S.ColumnChecks O ch (P.respond ch) j) ⊆
        (colErrors (fun h => combo (ch.code h) O.U + O.codeMask h) v)ᶜ := by
      intro j hj
      simp only [mem_filter, mem_univ, true_and] at hj
      rw [mem_compl, mem_colErrors]
      simp only [not_exists, not_not]
      intro h
      have hc : _ = evalCoeffs ((P.respond ch).code h) (S.η j) := hj.code h
      simpa [combo, v] using hc
    have := card_le_card hsub
    rw [card_compl, Fintype.card_fin] at this
    omega

/-- **The close case.** If `U` is `e`-close to `L^{4m}` and the constraint system is
unsatisfiable, the code test's and one constraint test's bad events together have density at
most `(e + 1)/|F|^σ`, and outside them an accepted challenge has at most
`max(n − e, (n + 2k − 2)/2)` columns passing all checks. -/
theorem exists_bad_close (hS : S.Valid k) (hunsat : ¬ S.Satisfiable) {e : ℕ}
    (he : 4 * e < n - k + 1)
    (O : Oracle F σ m n) (hclose : InterleavedProximity.Close (rsCode S.η k) e O.U) (P : Prover F σ m ℓ L k) :
    ∃ Bad : Finset (Challenge F σ m ℓ L),
      #Bad * Fintype.card F ^ σ ≤ (e + 1) * Fintype.card (Challenge F σ m ℓ L) ∧
        ∀ ch ∉ Bad, S.ResponseChecks ch (P.respond ch) →
          #{j | S.ColumnChecks O ch (P.respond ch) j} ≤ max (n - e) ((n + (2 * k - 2)) / 2) := by
  classical
  obtain ⟨V, hV, hVe⟩ := hclose
  choose cf hcf using fun i => mem_rsCode.mp (hV i)
  have hrows : S.rows cf = V := funext hcf
  subst hrows
  have hx : ¬ S.Holds (S.decoded cf) := fun h => hunsat ⟨_, h⟩
  have hcode : #(univ.filter fun ch : Challenge F σ m ℓ L => S.CodeBad O cf ch.code) *
      Fintype.card F ^ σ ≤ e * Fintype.card (Challenge F σ m ℓ L) :=
    card_filter_fst_mul_le Challenge.equivProd (S.CodeBad O cf)
      ((S.card_codeBad_mul_le hS O cf).trans (Nat.mul_le_mul_right _ hVe))
  -- Combine the code test's columns bound with a constraint test's.
  have combine : ∀ {ch : Challenge F σ m ℓ L}, ¬ S.CodeBad O cf ch.code →
      #{j | S.ColumnChecks O ch (P.respond ch) j ∧ j ∉ colErrors O.U (S.rows cf)} ≤
        (n + (2 * k - 2)) / 2 →
      #{j | S.ColumnChecks O ch (P.respond ch) j} ≤ max (n - e) ((n + (2 * k - 2)) / 2) := by
    intro ch hcb hrest
    rcases S.card_columns_le_or_disjoint he hVe hcb with h | h
    · exact h.trans (le_max_left _ _)
    · refine le_trans (card_le_card fun j hj => ?_) (hrest.trans (le_max_right _ _))
      simp only [mem_filter, mem_univ, true_and] at hj ⊢
      exact ⟨hj, h j hj⟩
  rcases S.linear_or_quadratic_of_not_holds hx with hlin | ⟨i₀, c₀, hres⟩
  · have hl : #(univ.filter fun ch : Challenge F σ m ℓ L => S.LinBad O cf ch.lin) *
        Fintype.card F ^ σ ≤ 1 * Fintype.card (Challenge F σ m ℓ L) :=
      card_filter_fst_mul_le Challenge.linEquiv (S.LinBad O cf) (S.card_linBad_mul_le hS O cf hlin)
    refine ⟨(univ.filter fun ch => S.CodeBad O cf ch.code) ∪
      univ.filter fun ch => S.LinBad O cf ch.lin, ?_, ?_⟩
    · refine (Nat.mul_le_mul_right _ (card_union_le _ _)).trans ?_
      rw [add_mul, add_mul, one_mul]
      exact Nat.add_le_add hcode (by simpa using hl)
    · intro ch hch hresp
      simp only [mem_union, mem_filter, mem_univ, true_and, not_or] at hch
      exact combine hch.1 (S.card_columns_compl_le_of_lin hS hresp hch.2)
  · have hq : #(univ.filter fun ch : Challenge F σ m ℓ L => S.QuadBad O cf ch.quad) *
        Fintype.card F ^ σ ≤ 1 * Fintype.card (Challenge F σ m ℓ L) :=
      card_filter_fst_mul_le Challenge.quadEquiv (S.QuadBad O cf)
        (S.card_quadBad_mul_le hS O cf hres)
    refine ⟨(univ.filter fun ch => S.CodeBad O cf ch.code) ∪
      univ.filter fun ch => S.QuadBad O cf ch.quad, ?_, ?_⟩
    · refine (Nat.mul_le_mul_right _ (card_union_le _ _)).trans ?_
      rw [add_mul, add_mul, one_mul]
      exact Nat.add_le_add hcode (by simpa using hq)
    · intro ch hch hresp
      simp only [mem_union, mem_filter, mem_univ, true_and, not_or] at hch
      exact combine hch.1 (S.card_columns_compl_le_of_quad hS hresp hch.2)

/-- **AHIV22 Lemma 4.14, sharpened** (ePrint 2022/1608, p. 26), for the section 4.7 ZKIPCP with
arbitrary mask rows: under `S.Valid k`, if no extended message satisfies the constraint system,
then for every `e < d/4` (`d = n − k + 1`), every oracle and every prover, the verifier accepts
with probability at most `(e + 1)/|F|^σ + max((1 − e/n)^t, ((e + 2k)/n)^t)`. -/
@[headline]
theorem acceptProb_le_of_not_satisfiable (hS : S.Valid k) (hunsat : ¬ S.Satisfiable) {e t : ℕ}
    (he : 4 * e < n - k + 1) (O : Oracle F σ m n) (P : Prover F σ m ℓ L k) :
    S.acceptProb t O P ≤ ((e + 1 : ℕ) : ℚ) / Fintype.card F ^ σ +
      max ((1 - (e : ℚ) / n) ^ t) ((((e + 2 * k : ℕ) : ℚ) / n) ^ t) := by
  obtain ⟨Bad, hcount, hT⟩ : ∃ Bad : Finset (Challenge F σ m ℓ L),
      #Bad * Fintype.card F ^ σ ≤ (e + 1) * Fintype.card (Challenge F σ m ℓ L) ∧
        ∀ ch ∉ Bad, S.ResponseChecks ch (P.respond ch) →
          #{j | S.ColumnChecks O ch (P.respond ch) j} ≤ max (n - e) ((n + (2 * k - 2)) / 2) := by
    by_cases hclose : InterleavedProximity.Close (rsCode S.η k) e O.U
    · exact S.exists_bad_close hS hunsat he O hclose P
    · obtain ⟨Bad, h₁, h₂⟩ := S.exists_bad_far hS he O hclose P
      exact ⟨Bad, h₁, fun ch hch _ => (h₂ ch hch).trans (le_max_left _ _)⟩
  set T := min n (max (n - e) ((n + (2 * k - 2)) / 2)) with hTdef
  have hT' : ∀ ch ∉ Bad, S.ResponseChecks ch (P.respond ch) →
      #{j | S.ColumnChecks O ch (P.respond ch) j} ≤ T := fun ch hch hr =>
    le_min ((card_le_univ _).trans (by simp)) (hT ch hch hr)
  have hq : S.acceptProb t O P ≤ (#Bad : ℚ) / Fintype.card (Challenge F σ m ℓ L) +
      (T.choose t : ℚ) / n.choose t :=
    queryProb_le_of_bad (fun ch => S.ResponseChecks ch (P.respond ch))
      (fun ch j => S.ColumnChecks O ch (P.respond ch) j) (fun _ _ => S.accepts_iff) Bad T hT'
  refine hq.trans (add_le_add ?_ ?_)
  · have hCh : (0 : ℚ) < Fintype.card (Challenge F σ m ℓ L) := by
      exact_mod_cast Fintype.card_pos
    have hF : (0 : ℚ) < Fintype.card F ^ σ := by
      have : 0 < Fintype.card F := Fintype.card_pos
      positivity
    rw [div_le_div_iff₀ hCh hF]
    exact_mod_cast hcount
  · have heN : e ≤ n := by omega
    rcases (show T ≤ n - e ∨ T ≤ e + 2 * k by omega) with h | h
    · refine (choose_div_choose_le_pow (min_le_left _ _) h t).trans
        ((pow_le_pow_left₀ (by positivity) ?_ t).trans (le_max_left _ _))
      rcases Nat.eq_zero_or_pos n with hn | hn
      · subst hn
        simp
      · rw [Nat.cast_sub heN, sub_div, div_self (by positivity)]
    · exact (choose_div_choose_le_pow (min_le_left _ _) h t).trans (le_max_right _ _)

end Setup

end Proof

/-- Lemma 4.14's soundness error `(d + 2)/|F|^σ + (1 − e/n)^t + 2((e + 2k)/n)^t` with
`d = n − k + 1`. -/
def soundnessError (F : Type) [Fintype F] (n k σ t e : ℕ) : ℚ :=
  ((n - k + 1 : ℕ) + 2 : ℚ) / Fintype.card F ^ σ + (1 - (e : ℚ) / n) ^ t +
    2 * (((e + 2 * k : ℕ) : ℚ) / n) ^ t

variable [DecidableEq F] [Fintype F]

/-- **AHIV22 Lemma 4.14** (ePrint 2022/1608, p. 26; Theorem 4.7, p. 27), for the section 4.7
ZKIPCP with arbitrary (untested) mask rows: under the side conditions `S.Valid k`, if no extended
message satisfies the constraint system, then for every `e` with `e < d/4` (`d = n − k + 1`),
every oracle `O` (rows and all `3σ` mask rows arbitrary) and every prover `P`, the verifier
accepts with probability at most `(d + 2)/|F|^σ + (1 − e/n)^t + 2((e + 2k)/n)^t`. -/
def Lemma414 (S : Setup F n m ℓ L) (k σ t : ℕ) : Prop :=
  S.Valid k → ¬ S.Satisfiable → ∀ e : ℕ, 4 * e < n - k + 1 →
    ∀ (O : Oracle F σ m n) (P : Prover F σ m ℓ L k),
      S.acceptProb t O P ≤ soundnessError F n k σ t e

/-- **AHIV22 Lemma 4.14 holds with untested masks** (ePrint 2022/1608, p. 26): `Lemma414` holds
for every setup, every `k`, every number of repetitions `σ` and every query count `t`. -/
@[headline]
theorem lemma414 (S : Setup F n m ℓ L) (k σ t : ℕ) : Lemma414 S k σ t := by
  intro hS hunsat e he O P
  refine (S.acceptProb_le_of_not_satisfiable hS hunsat he O P).trans ?_
  have heN : (e : ℚ) / n ≤ 1 := by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · simp [hn]
    · rw [div_le_one (by exact_mod_cast hn)]
      exact_mod_cast (show e ≤ n by omega)
  have ha : 0 ≤ (1 - (e : ℚ) / n) ^ t := pow_nonneg (by linarith) t
  have hb : 0 ≤ (((e + 2 * k : ℕ) : ℚ) / n) ^ t := by positivity
  have hd : ((e + 1 : ℕ) : ℚ) ≤ ((n - k + 1 : ℕ) + 2 : ℚ) := by
    have : e + 1 ≤ n - k + 1 + 2 := by omega
    exact_mod_cast this
  have hF : (0 : ℚ) ≤ Fintype.card F ^ σ := by positivity
  unfold soundnessError
  have hmax : max ((1 - (e : ℚ) / n) ^ t) ((((e + 2 * k : ℕ) : ℚ) / n) ^ t) ≤
      (1 - (e : ℚ) / n) ^ t + 2 * (((e + 2 * k : ℕ) : ℚ) / n) ^ t :=
    max_le (by linarith) (by linarith)
  have hdiv := div_le_div_of_nonneg_right hd hF
  linarith

end GordieHowe.Errata.AHIV22.UntestedMasks
