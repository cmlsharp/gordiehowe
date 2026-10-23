-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Errata.Basic
public import GordieHowe.Foundations.ReedSolomon.BerlekampWelch
public import GordieHowe.ProofSystem.Ligero.Interpolation
public import GordieHowe.Headline
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Tactic.NormNum.Prime

@[expose] public section

/-!
# An erratum against CHVY25: Theorem 4.4

Cascudo, Hazay, Venkitasubramaniam and Yogev, "Independent Security Analysis of Longfellow ZK",
security review of Longfellow ZK, December 2025
(`docs/static/reviews/Longfellow_security_2025_12_15.pdf` in the longfellow-zk repository,
github.com/longfellow-zk/longfellow-zk), Theorem 4.4 (p. 18):

> In the conditions of Theorem 4.3, suppose the matrix `V` promised by the theorem exists. Then,
> except with probability `C(2ρn − 2, t)/C(n, t) + 1/|F|`, if the linear and quadratic tests pass,
> the inputs encoded by `V` satisfy the tested circuit.

Theorem 4.3 (p. 17) fixes "a Reed-Solomon code `L` of length `n`, rate `ρ < 1/2`, and minimum
distance `d` over the field `F`", with "`t` columns of the matrix `U`" queried; the proof of 4.4
(pp. 18–19) uses `k = ρn` for the dimension and compares the sent polynomial with "the `p_V`
constructed honestly from `V`" as two polynomials of degree at most `2k − 2`.

CHVY25 analyse Longfellow's Ligero (section 2.5, pp. 6–8) and do not restate its tests, so this file
transcribes Longfellow's linear test as specified in Longfellow's specification of Ligero
(`docs/specs/ligero.md` in the longfellow-zk repository, "Ligero verification procedure":
`dot_check`, `want_dot == proof_dot`, `quadratic_check`) and implemented in
`lib/ligero/ligero_verifier.h` (`dot_check`; `proof_dot` sums `y_dot[r .. r + w)`, line 177), for a
statement with linear constraints only. The dot-product mask row `IDOT` and the quadratic mask row
`IQD` are not part of the low-degree test (`low_degree_check` combines `ILDT` and the rows from `IW`
on), so a cheating prover may commit arbitrary values there.

The counterexample (`theorem44_false`) is the instance of `scripts/audit_masked_ligero.py`:
`F_101`, `NREQ = t = 1`, `WR = 1`, `BLOCK = k = 2`, `n = 5` opened-candidate columns (nodes
`3, …, 7`), one witness row encoding `W[0] = 0`, the constraint `W[0] = 1`, and the `IDOT` row
`(x − 1)^3` at the opened-candidate columns. The prover passes with probability exactly `211/505` against the bound
`C(2, 1)/C(5, 1) + 1/101 = 207/505` (and `C(2, 1)/C(8, 1) + 1/101` for the full encoded length).
The family of `GordieHowe.Errata.CHVY25FamilyData` refutes the sum of Theorems 4.3 and 4.4, as transcribed
here, for every `k` from 13 to 30. Decided by the kernel (`decide +kernel`).

Reading of the paper and the specification:
- The code length the theorem calls `n` (`len` here) is not pinned down: the verifier samples from
  the `n = NCOL − DBLOCK` committed columns (the Merkle leaves are columns `DBLOCK … NCOL − 1`,
  `ligero.md`, "Ligero commitment"), while CHVY25's section 6 (p. 23) plugs in the full encoded
  lengths `NCOL` of Longfellow's tableaus (`2945`, `4096`). Both readings, as transcribed, are
  refuted (`theorem44_false`, `theorem44_false_ncol`). `k = ρ·len` is `BLOCK`, the dimension of the
  row code, and `t = NREQ`.
- "In the conditions of Theorem 4.3, suppose the matrix `V` … exists": the tested rows are exact
  codewords (`Tableau.rows` gives each row by its `BLOCK` values, extended), so `V = U`, and "the
  inputs encoded by `V`" are the witness values `W[i·WR + c] = row_i(NREQ + c)`. Restricting to
  exact codewords only weakens the stated claim, so refuting it refutes the transcribed theorem.
- "Except with probability `ε`, if the tests pass, the inputs satisfy the circuit": with the
  inputs fixed and violating a constraint, `Pr[linear and quadratic tests pass] ≤ ε`. The event
  includes the quadratic test; with no quadratic constraints it checks the `IQD` row alone
  (`QuadColumn`), and the low-degree test is not part of the event.
- The challenge `alpha_l ∈ F^{NL}` is uniform; the opened set is uniform among the `NREQ`-subsets
  of the `n` columns ("sampled without replacement", `ligero.md`), independent of `alpha_l`.
- The prover's `y_dot` and quadratic response are its `DBLOCK` values at the nodes
  `0 … DBLOCK − 1`, extended by Lagrange interpolation (`extend`), as in the specification; the
  quadratic response's witness positions `NREQ … BLOCK − 1` are set to `0` by the verifier.
-/

namespace GordieHowe.Errata.CHVY25

open Finset RSCode.BerlekampWelch GordieHowe.LigeroInterpolation

variable {F : Type} [Field F] {nreq wr n m nl : ℕ}

/-- `extend(y, D)` at `x` (`ligero.md`): the value at `x` of the polynomial of degree `< D`
taking the value `y i` at the node `i`, for `i < D`. -/
def extendAt (D : ℕ) (y : Fin D → F) (x : F) : F :=
  interpolateEval (fun i : Fin D => (i : F)) y x

/-- A response sent as the values at the nodes `0 … D − 1` of a polynomial of degree `< D`
extends to the polynomial itself. -/
theorem extendAt_eval {D : ℕ} (hv : Function.Injective (fun i : Fin D => (i : F)))
    {p : Polynomial F} (hp : p.degree < D) (x : F) :
    extendAt D (fun i => p.eval (i : F)) x = p.eval x := by
  rw [extendAt, ← eval_interpolate, interpolate_eval_nodes hv hp]

/-- `extendAt_eval` for a polynomial given by its `D` coefficients. -/
theorem extendAt_evalCoeffs {D : ℕ} (hv : Function.Injective (fun i : Fin D => (i : F)))
    (c : Fin D → F) (x : F) :
    extendAt D (fun i => evalCoeffs c i) x = evalCoeffs c x := by
  simpa only [eval_ofCoeffs] using extendAt_eval hv (degree_ofCoeffs_lt c) x

theorem extendAt_zero (D : ℕ) (x : F) : extendAt D 0 x = 0 := by
  simp [extendAt, interpolateEval]

/-- `BLOCK = NREQ + WR`. -/
abbrev block (nreq wr : ℕ) : ℕ := nreq + wr

/-- `DBLOCK = 2·BLOCK − 1`, the number of values of a dot or quadratic response. -/
abbrev dblock (nreq wr : ℕ) : ℕ := 2 * block nreq wr - 1

/-- The node of the opened-candidate column `q`: `DBLOCK + q`. -/
def colNode (nreq wr : ℕ) (q : Fin n) : F := ((dblock nreq wr + q : ℕ) : F)

/-- The index of the witness position `c` among a response's values: `NREQ + c`. -/
def witnessPos (c : Fin wr) : Fin (dblock nreq wr) :=
  ⟨nreq + c, by have := c.isLt; unfold dblock block; omega⟩

/-- The rows of a Longfellow tableau the linear test reads, for a statement with linear
constraints only. Tested rows are exact codewords (Theorem 4.3's `V` exists and equals `U`):
row `i` is given by its `BLOCK` values `[RANDOM[NREQ], W[i·WR .. (i+1)·WR]]` and extended.
The mask rows are given at the `n` opened-candidate columns, arbitrary. -/
structure Tableau (F : Type) (nreq wr n m : ℕ) where
  /-- The `BLOCK` values of the witness row `i`. -/
  rows : Fin m → Fin (block nreq wr) → F
  /-- The `IDOT` row at the opened-candidate columns. -/
  idot : Fin n → F
  /-- The `IQD` row at the opened-candidate columns. -/
  iqd : Fin n → F

/-- A system of linear constraints `A·W = b` on the witness: `A l i c` is the coefficient of
`W[i·WR + c]` in constraint `l`. -/
structure Constraints (F : Type) (wr m nl : ℕ) where
  /-- The coefficients. -/
  A : Fin nl → Fin m → Fin wr → F
  /-- The right-hand sides. -/
  b : Fin nl → F

namespace Tableau

/-- The witness `W[i·WR + c] = row_i(NREQ + c)` encoded by the rows. -/
def witness (T : Tableau F nreq wr n m) (i : Fin m) (c : Fin wr) : F :=
  T.rows i ⟨nreq + c, by have := c.isLt; unfold block; omega⟩

/-- The witness the rows encode satisfies every linear constraint. -/
def Satisfies (T : Tableau F nreq wr n m) (C : Constraints F wr m nl) : Prop :=
  ∀ l, ∑ i, ∑ c, C.A l i c * T.witness i c = C.b l

end Tableau

/-- A malicious prover's messages after the challenge `alpha_l`: the `DBLOCK` values of `y_dot`
and of the quadratic response (`qpr`, whose witness positions the verifier ignores). -/
structure Prover (F : Type) (nreq wr nl : ℕ) where
  /-- `y_dot`, as values at the nodes `0 … DBLOCK − 1`. -/
  dot : (Fin nl → F) → Fin (dblock nreq wr) → F
  /-- The quadratic response, as values at the nodes `0 … DBLOCK − 1`. -/
  qpr : (Fin nl → F) → Fin (dblock nreq wr) → F

/-- `Aext` of row `i` (`inner_product_vector`, `dot_check`): `NREQ` zeros, then the combined
coefficients `∑_l alpha_l · A l i c` of the row's witnesses. -/
def aext (C : Constraints F wr m nl) (α : Fin nl → F) (i : Fin m) (j : Fin (block nreq wr)) : F :=
  if h : nreq ≤ (j : ℕ) then
    ∑ l, α l * C.A l i ⟨j - nreq, by have := j.isLt; unfold block at this; omega⟩
  else 0

/-- `yquad = qpr[0..NREQ] || 0 || qpr[BLOCK..DBLOCK]` (`quadratic_check`). -/
def yquad (y : Fin (dblock nreq wr) → F) (j : Fin (dblock nreq wr)) : F :=
  if nreq ≤ (j : ℕ) ∧ (j : ℕ) < block nreq wr then 0 else y j

variable (T : Tableau F nreq wr n m) (C : Constraints F wr m nl) (P : Prover F nreq wr nl)

/-- `want_dot == proof_dot`: the `y_dot` values at the witness positions sum to
`∑_l alpha_l · b_l`. -/
def DotSum (α : Fin nl → F) : Prop :=
  ∑ c, P.dot α (witnessPos c) = ∑ l, α l * C.b l

/-- `dot_check` at the opened column `q`: the extended `y_dot` equals the `IDOT` entry plus
`∑_i Af_i · row_i` at the column, with `Af_i = extend(Aext_i, BLOCK)`. -/
def DotColumn (α : Fin nl → F) (q : Fin n) : Prop :=
  extendAt (dblock nreq wr) (P.dot α) (colNode nreq wr q) =
    T.idot q + ∑ i, extendAt (block nreq wr) (aext (nreq := nreq) C α i) (colNode nreq wr q) *
      extendAt (block nreq wr) (T.rows i) (colNode nreq wr q)

/-- `quadratic_check` at the opened column `q`, with no quadratic constraints: the extended
`yquad` equals the `IQD` entry. -/
def QuadColumn (α : Fin nl → F) (q : Fin n) : Prop :=
  extendAt (dblock nreq wr) (yquad (P.qpr α)) (colNode nreq wr q) = T.iqd q

/-- The linear and quadratic tests pass on the challenge `alpha_l` and the opened columns `Q`. -/
structure Accepts (α : Fin nl → F) (Q : Finset (Fin n)) : Prop where
  dotSum : DotSum C P α
  columns : ∀ q ∈ Q, DotColumn T C P α q ∧ QuadColumn T P α q

theorem accepts_iff {α : Fin nl → F} {Q : Finset (Fin n)} :
    Accepts T C P α Q ↔ DotSum C P α ∧ ∀ q ∈ Q, DotColumn T C P α q ∧ QuadColumn T P α q :=
  ⟨fun h => ⟨h.dotSum, h.columns⟩, fun h => ⟨h.1, h.2⟩⟩

variable [DecidableEq F]

instance (α : Fin nl → F) : Decidable (DotSum C P α) := inferInstanceAs (Decidable (_ = _))

instance (α : Fin nl → F) (q : Fin n) : Decidable (DotColumn T C P α q) :=
  inferInstanceAs (Decidable (_ = _))

instance (α : Fin nl → F) (q : Fin n) : Decidable (QuadColumn T P α q) :=
  inferInstanceAs (Decidable (_ = _))

instance (α : Fin nl → F) (Q : Finset (Fin n)) : Decidable (Accepts T C P α Q) :=
  decidable_of_iff _ (accepts_iff T C P).symm

variable [Fintype F]

/-- The probability that the linear and quadratic tests pass with `t = NREQ` opened columns:
`alpha_l` uniform in `F^{NL}`, the opened set uniform among the `NREQ`-subsets of the `n`
columns. -/
def acceptProb : ℚ :=
  queryProb (Fin nl → F) n nreq (Accepts T C P)

theorem acceptProb_eq :
    acceptProb T C P =
      ((∑ α, if DotSum C P α then
          (#{q | DotColumn T C P α q ∧ QuadColumn T P α q}).choose nreq else 0 : ℕ) : ℚ) /
        (Fintype.card F ^ nl * n.choose nreq) := by
  rw [acceptProb, queryProb_eq_sum (DotSum C P)
    (fun α q => DotColumn T C P α q ∧ QuadColumn T P α q) fun _ _ => accepts_iff T C P]
  simp

/-- The setting of Theorem 4.3: the nodes `0 … NCOL − 1`, `NCOL = DBLOCK + n`, are distinct
field elements. -/
structure Valid (F : Type) [Field F] (nreq wr n : ℕ) : Prop where
  nodes_injective : Function.Injective (fun i : Fin (dblock nreq wr + n) => (i : F))

/-- **CHVY25 Theorem 4.4** (p. 18), as transcribed here, for Longfellow's linear test (no quadratic
constraints) with `t = NREQ`: for exact-codeword rows whose encoded witness violates a linear
constraint, any `IDOT` and `IQD` rows and any prover, the linear and quadratic tests pass with
probability at most `C(2k − 2, t)/C(len, t) + 1/|F|`, where `k = ρ·len = BLOCK` and `len` is the
code length the theorem calls `n`, of rate below `1/2`. Two readings of `len`: the `n` columns
the verifier samples from, or the full encoded length `NCOL = DBLOCK + n` (CHVY25's section 6,
p. 23, uses Longfellow's encoded lengths `2945` and `4096`). -/
def Theorem44 (F : Type) [Field F] [DecidableEq F] [Fintype F] (nreq wr n m nl len : ℕ) :
    Prop :=
  Valid F nreq wr n → 2 * block nreq wr < len →
    ∀ (C : Constraints F wr m nl) (T : Tableau F nreq wr n m), ¬ T.Satisfies C →
      ∀ P : Prover F nreq wr nl,
        acceptProb T C P ≤
          ((2 * block nreq wr - 2).choose nreq : ℚ) / len.choose nreq + 1 / Fintype.card F

/-- **CHVY25 Theorems 4.3 and 4.4 summed** (pp. 17–18): Theorem 4.4's event bounded by the sum of
the two theorems' bounds, `C(⌈(1 + ρ)len/2⌉, t)/C(len, t) + (len + 1)/|F| +
C(2ρ·len − 2, t)/C(len, t) + 1/|F|`: the query-round terms of CHVY25's eq. (2) (p. 15) plus
`(len + 2)/|F|`. The binomial top `(1 + ρ)len/2 = (len + k)/2` is rounded up, the larger of the
two readings. Implied by `Theorem44` (`theorem44Summed_of_theorem44`), so a refutation also
refutes Theorem 4.4. -/
def Theorem44Summed (F : Type) [Field F] [DecidableEq F] [Fintype F] (nreq wr n m nl len : ℕ) :
    Prop :=
  Valid F nreq wr n → 2 * block nreq wr < len →
    ∀ (C : Constraints F wr m nl) (T : Tableau F nreq wr n m), ¬ T.Satisfies C →
      ∀ P : Prover F nreq wr nl,
        acceptProb T C P ≤
          (((len + block nreq wr + 1) / 2).choose nreq : ℚ) / len.choose nreq +
            (len + 1) / Fintype.card F +
            ((2 * block nreq wr - 2).choose nreq / len.choose nreq + 1 / Fintype.card F)

theorem theorem44Summed_of_theorem44 {len : ℕ} (h : Theorem44 F nreq wr n m nl len) :
    Theorem44Summed F nreq wr n m nl len := by
  intro hv hr C T hT P
  refine (h hv hr C T hT P).trans (le_add_of_nonneg_left ?_)
  exact add_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    (div_nonneg (add_nonneg (Nat.cast_nonneg _) zero_le_one) (Nat.cast_nonneg _))

/-! ## The counterexample: `F_101`, `NREQ = WR = 1`, `n = 5` -/

/-- `101` is prime, so `ZMod 101` is a field. -/
instance fact_prime_101 : Fact (Nat.Prime 101) := ⟨by norm_num⟩

/-- One witness row, all zero. The mask rows: `IDOT` is `(x − 1)^3` at the opened-candidate
nodes `x = 3, …, 7`, `IQD` is zero. -/
def exTableau : Tableau (ZMod 101) 1 1 5 1 where
  rows _ _ := 0
  idot q := (colNode 1 1 q - 1) ^ 3
  iqd _ := 0

/-- The constraint `W[0] = 1`, which the zero witness violates. -/
def exConstraints : Constraints (ZMod 101) 1 1 1 where
  A _ _ _ := 1
  b _ := 1

/-- The coefficients `(c_0, c_1, c_2)` of the response polynomial for `alpha_l = α`: a
polynomial `p` of degree `≤ 2` with `p(1) = α` agreeing with `(x − 1)^3` at the most of the nodes
`3, …, 7` (exhaustive search, `scripts/audit_masked_ligero.py`). -/
def exCoeffs : Fin 101 → Fin 3 → ZMod 101 :=
  ![![11, 85, 5], ![81, 17, 4], ![56, 23, 24], ![25, 78, 1], ![90, 0, 15], ![54, 52, 0],
    ![23, 78, 6], ![94, 100, 15], ![29, 73, 7], ![13, 79, 18], ![57, 52, 2], ![81, 29, 2],
    ![35, 71, 7], ![37, 53, 24], ![46, 50, 19], ![47, 60, 9], ![44, 65, 8], ![81, 37, 0],
    ![47, 64, 8], ![7, 98, 15], ![53, 59, 9], ![10, 6, 5], ![62, 61, 0], ![80, 21, 23],
    ![59, 57, 9], ![21, 89, 16], ![4, 19, 3], ![99, 7, 22], ![58, 43, 28], ![0, 28, 1],
    ![71, 50, 10], ![93, 39, 0], ![74, 49, 10], ![67, 65, 2], ![92, 40, 3], ![67, 46, 23],
    ![83, 43, 11], ![34, 78, 26], ![74, 46, 19], ![37, 87, 16], ![89, 41, 11], ![10, 30, 1],
    ![92, 50, 1], ![42, 86, 16], ![99, 0, 46], ![95, 40, 11], ![65, 56, 26], ![44, 98, 6],
    ![3, 33, 12], ![49, 85, 16], ![6, 32, 12], ![28, 21, 2], ![33, 13, 6], ![25, 28, 0],
    ![10, 32, 12], ![77, 59, 20], ![52, 100, 5], ![40, 95, 23], ![5, 52, 1], ![67, 76, 17],
    ![18, 30, 12], ![40, 20, 1], ![21, 39, 2], ![88, 76, 0], ![33, 17, 14], ![60, 1, 4],
    ![42, 8, 16], ![77, 74, 17], ![15, 33, 20], ![55, 12, 2], ![42, 14, 14], ![52, 19, 0],
    ![38, 21, 13], ![56, 84, 34], ![84, 91, 0], ![42, 20, 13], ![33, 41, 2], ![64, 12, 1],
    ![66, 95, 18], ![91, 72, 17], ![48, 19, 13], ![82, 95, 5], ![33, 49, 0], ![76, 5, 2],
    ![58, 12, 14], ![85, 97, 4], ![100, 80, 7], ![22, 64, 1], ![78, 94, 17], ![88, 99, 3],
    ![66, 10, 14], ![100, 86, 6], ![89, 63, 41], ![50, 39, 4], ![61, 30, 3], ![100, 92, 4],
    ![73, 9, 14], ![57, 39, 1], ![57, 20, 21], ![26, 54, 19], ![78, 8, 14]]

/-- The counterexample prover: `y_dot` is the values at `0, 1, 2` of the polynomial
`exCoeffs α`; the quadratic response is zero. -/
def exProver : Prover (ZMod 101) 1 1 1 where
  dot α i := evalCoeffs (exCoeffs ⟨(α 0).val, (α 0).val_lt⟩) (i : ZMod 101)
  qpr _ _ := 0

theorem ex_valid : Valid (ZMod 101) 1 1 5 where
  nodes_injective := by decide +kernel

theorem exTableau_not_satisfies : ¬ exTableau.Satisfies exConstraints := by
  intro h
  have := h 0
  simp [exTableau, exConstraints, Tableau.witness] at this

theorem ex_dotColumn_iff (α : Fin 1 → ZMod 101) (q : Fin 5) :
    DotColumn exTableau exConstraints exProver α q ↔
      evalCoeffs (exCoeffs ⟨(α 0).val, (α 0).val_lt⟩) (colNode 1 1 q) = exTableau.idot q := by
  have hv : Function.Injective (fun i : Fin (dblock 1 1) => (i : ZMod 101)) := by decide +kernel
  have hrows : ∀ i, exTableau.rows i = 0 := fun _ => rfl
  simp only [DotColumn, hrows, extendAt_zero, mul_zero, Finset.sum_const_zero, add_zero]
  rw [show exProver.dot α = fun i : Fin (dblock 1 1) =>
    evalCoeffs (exCoeffs ⟨(α 0).val, (α 0).val_lt⟩) (i : ZMod 101) from rfl,
    extendAt_evalCoeffs hv]

theorem ex_quadColumn (α : Fin 1 → ZMod 101) (q : Fin 5) :
    QuadColumn exTableau exProver α q := by
  have h0 : yquad (nreq := 1) (wr := 1) (exProver.qpr α) = 0 := by
    funext j
    simp [yquad, exProver]
  rw [QuadColumn, h0, extendAt_zero]
  rfl

theorem exProver_acceptCount :
    (∑ α, if DotSum exConstraints exProver α then
      (#{q | DotColumn exTableau exConstraints exProver α q ∧
        QuadColumn exTableau exProver α q}).choose 1 else 0) = 211 := by
  have hcol : ∀ α : Fin 1 → ZMod 101,
      (#{q | DotColumn exTableau exConstraints exProver α q ∧ QuadColumn exTableau exProver α q}) =
        #{q | evalCoeffs (exCoeffs ⟨(α 0).val, (α 0).val_lt⟩) (colNode 1 1 q) =
          exTableau.idot q} := by
    intro α
    congr 1
    ext q
    simp [ex_dotColumn_iff, ex_quadColumn]
  simp only [hcol]
  decide +kernel

/-- With `t = 1` the counterexample prover passes Longfellow's linear and quadratic tests with
probability `211/505`. -/
theorem exProver_acceptProb : acceptProb exTableau exConstraints exProver = 211 / 505 := by
  rw [acceptProb_eq, exProver_acceptCount, ZMod.card]
  norm_num

/-- **CHVY25 Theorem 4.4 is false as transcribed here** (Cascudo, Hazay, Venkitasubramaniam and
Yogev, security review of Longfellow ZK, version of 2025-12-15, Theorem 4.4, p. 18). For
Longfellow's linear test over `F_101` with `NREQ = t = 1`, `WR = 1`, `BLOCK = k = 2`, `n = 5`
opened-candidate columns, one exact-codeword witness row and the constraint `W[0] = 1` against the
committed witness `W[0] = 0`, a prover whose `IDOT` row is `(x − 1)^3` passes the linear and
quadratic tests with probability `211/505`, above `C(2, 1)/C(5, 1) + 1/101 = 207/505` (code length
read as `n = 5`). -/
@[headline]
theorem theorem44_false : ¬ Theorem44 (ZMod 101) 1 1 5 1 1 5 := by
  intro h
  have hb := h ex_valid (by norm_num) exConstraints exTableau exTableau_not_satisfies exProver
  rw [exProver_acceptProb, ZMod.card] at hb
  norm_num at hb

/-- **CHVY25 Theorem 4.4 is false as transcribed here**, code length read as the full encoded
length `NCOL = 8` (version of 2025-12-15, Theorem 4.4, p. 18): the instance of `theorem44_false`
exceeds `C(2, 1)/C(8, 1) + 1/101`. -/
@[headline]
theorem theorem44_false_ncol : ¬ Theorem44 (ZMod 101) 1 1 5 1 1 8 := by
  intro h
  have hb := h ex_valid (by norm_num) exConstraints exTableau exTableau_not_satisfies exProver
  rw [exProver_acceptProb, ZMod.card] at hb
  norm_num at hb

end GordieHowe.Errata.CHVY25
