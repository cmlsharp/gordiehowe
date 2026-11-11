-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.RealizedProgram.Ops
public import GordieHowe.Language.RealizedProgram.SpectralSound
public import GordieHowe.Language.Library.TableSelect
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Polynomial.Degree.Operations

@[expose] public section

/-!
# GordieHowe frontend: polynomial identities checked at one random point

The native rings (`lib/gordiehowe/examples/rings/falcon_ring.h`, `native_signature_relation`;
`mldsa_ring_native.h`, `evaluation_relation`) check a product of a committed spectrum and a
committed polynomial in `F[X]/(X^n + 1)` at one challenge `r` of the field: with a committed
quotient `Q` the identity holds over `F[X]`, and each side is read at `r`. A coefficient vector
`x` is read as `Σ_t x_t r^t`, and a spectrum `y` (the transform of a polynomial at the roots
`ω_m` of `X^n + 1`) as `Σ_m y_m λ_m(r)` with the weights `λ(r) = n⁻¹ · Ntt_{ψ⁻¹}(1, r, …, r^{n−1})`
in the spectrum's order, the C++'s `signature.lambda`.

The polynomials of `n` coefficients (`Ops.polyOf`, Mathlib's `Polynomial.ofFn`), the product's
split into the negacyclic product and the quotient's high half (`Ops.polyOf_mul_polyOf`,
`Ops.high`), the split's uniqueness (`Ops.polyOf_eq_zero_of_add_mul`: a polynomial of `n`
coefficients plus a multiple of `X^n + 1` is `0` only when both parts are, and then its
coefficients are, `Ops.eq_zero_of_polyOf_eq_zero`) and the interpolation
(`Ops.eval_inverseNttNatural`, `Ops.eval_inverseNtt`: the polynomial whose transform is `y` takes
the value `Σ_m y_m λ_m(r)` at `r`) are with the operators they read, in
`GordieHowe/Language/RealizedProgram/Ops.lean`. This file holds what the frontends
share on top of them:

* **The roots** (`polyOf_eval_root_natural`, `polyOf_eval_root_scheme`, `root_pow_n`): a
  polynomial of `n` coefficients at the root `ω_m = ψ^(2m+1)` (natural order) or
  `ψ^(2·br(m)+1)` (scheme order) is its transform's coordinate `m`, and `ω_m^n = −1`, so
  `X^n + 1` vanishes there.
* **The degrees** (`natDegree_polyOf_mul_le`, `natDegree_quotient_le`): the identity's
  polynomial has degree at most `2n − 2`.
* **The public constants** (`natCast_eq_inv_of_mul_mod`, `decode_eq_inv_of_mul_mod`): `n⁻¹` and
  `ψ⁻¹` are the naturals `a` with `a · b ≡ 1 (mod p)`.
* **The powers of a challenge** (`ChalPowers`, `ChalPowers.powsAt`, `ChalPowers.evalE_range`,
  `ChalPowers.evalE_sq_add_one`): a public expression the symbolic-power matcher
  (`RealizedProgram.powSym`) reads as `r^l` at a challenge `r` of one coordinate and the constant
  `1` holds those powers (`RealizedProgram.powSym_sound`), as the table's `γ` powers do; the
  weights `λ(r)` (`ChalPowers.evalE_lambda_natural`, `ChalPowers.evalE_lambda_scheme`) and the
  zero constant (`evalE_zeroConst`) read from them.

A frontend combines them: where the predicate holds at `r` and `r` is not a root of the nonzero
difference polynomial (a `GordieHowe.ChallengeEvent` of degree at most `2n − 2`, or
`ChallengeEvent.prodNonzero` over several rows), the difference is `0`, and its value at each
`ω_m` is the spectral row the relation reads.
-/

namespace GordieHowe.RealizedProgram.Ops

open Polynomial

variable {K : Type*} [Field K]

/-! ## The roots -/

/-- **A polynomial at the root `ψ^(2m+1)`** is coordinate `m` of its natural-order transform. -/
theorem polyOf_eval_root_natural [DecidableEq K] (n : ℕ) (ψ : K) (x : ℕ → K) {m : ℕ} (hm : m < n) :
    (polyOf n x).eval (ψ ^ (2 * m + 1)) = nttNatural n ψ x m := by
  rw [polyOf_eval, ← Fin.sum_univ_eq_sum_range, nttNatural_apply n ψ x hm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← pow_mul]

/-- **A polynomial at the root `ψ^(2·br(m)+1)`** is coordinate `m` of its scheme-order transform
(`n = 2^k`). -/
theorem polyOf_eval_root_scheme [DecidableEq K] {k n : ℕ} (hn : n = 2 ^ k) (ψ : K) (x : ℕ → K) {m : ℕ}
    (hm : m < n) :
    (polyOf n x).eval (ψ ^ (2 * bitRevNat k m + 1)) = nttScheme n ψ x m := by
  rw [polyOf_eval, ← Fin.sum_univ_eq_sum_range, nttScheme_apply hn ψ x hm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← pow_mul]

/-- **The roots of `X^n + 1`**: where `ψ^n = −1`, every odd power `ψ^(2b+1)` has `n`-th power
`−1`. -/
theorem root_pow_n {n : ℕ} {ψ : K} (hψ : ψ ^ n = -1) (b : ℕ) : (ψ ^ (2 * b + 1)) ^ n = -1 := by
  rw [← pow_mul, Nat.mul_comm, pow_mul, hψ, pow_succ, pow_mul, neg_one_sq, one_pow, one_mul]

/-- **`X^n + 1` vanishes at the roots.** -/
theorem eval_X_pow_add_one_root {n : ℕ} {ψ : K} (hψ : ψ ^ n = -1) (b : ℕ) :
    (X ^ n + 1 : K[X]).eval (ψ ^ (2 * b + 1)) = 0 := by
  rw [eval_add, eval_pow, eval_X, eval_one, root_pow_n hψ b, neg_add_cancel]

/-! ## The degrees -/

/-- **The degree of `X^n + 1`** is `n`. -/
theorem natDegree_X_pow_add_one_le (n : ℕ) : (X ^ n + 1 : K[X]).natDegree ≤ n :=
  (natDegree_add_le _ _).trans (max_le (natDegree_X_pow_le n) (by simp))

/-- **A product of two polynomials of `n ≥ 1` coefficients** has degree at most `2n − 2`
(`Polynomial.ofFn_natDegree_lt`). -/
theorem natDegree_polyOf_mul_le [DecidableEq K] {n : ℕ} (hn : 1 ≤ n) (a b : ℕ → K) :
    (polyOf n a * polyOf n b).natDegree ≤ 2 * n - 2 :=
  (natDegree_mul_le).trans (by
    have := ofFn_natDegree_lt hn (toFin n a)
    have := ofFn_natDegree_lt hn (toFin n b)
    unfold polyOf
    omega)

/-- **The quotient's term** `(X^n + 1) · Q`, `Q` of `n − 1` coefficients, has degree at most
`2n − 2` (`n ≥ 2`). -/
theorem natDegree_quotient_le [DecidableEq K] {n : ℕ} (hn : 2 ≤ n) (q : ℕ → K) :
    ((X ^ n + 1) * polyOf (n - 1) q).natDegree ≤ 2 * n - 2 :=
  (natDegree_mul_le).trans (by
    have := natDegree_X_pow_add_one_le (K := K) n
    have := ofFn_natDegree_lt (n := n - 1) (by omega) (toFin (n - 1) q)
    unfold polyOf
    omega)

/-! ## Vanishing spectra -/

/-- **A polynomial of `n` coefficients whose scheme-order transform vanishes is `0`**
(`n = 2^k` invertible, `ψ` a primitive `2n`-th root; `inverseNtt_nttScheme`). -/
theorem polyOf_eq_zero_of_nttScheme [DecidableEq K] {k n : ℕ} (hn : n = 2 ^ k) {ψ : K}
    (hψ : IsPrimitiveRoot ψ (2 * n)) (hn0 : (n : K) ≠ 0) {x : ℕ → K}
    (h : ∀ m < n, nttScheme n ψ x m = 0) : polyOf n x = 0 := by
  have hx : ∀ t < n, x t = 0 := fun t ht => by
    rw [← inverseNtt_nttScheme hn hψ hn0 x ht]
    unfold inverseNtt
    rw [if_pos ht]
    simp only [mul_eq_zero, inv_eq_zero]
    right
    refine Finset.sum_eq_zero fun m _ => ?_
    rw [h m m.isLt, zero_mul]
  rw [polyOf_congr (b := fun _ => 0) hx]
  exact map_zero (ofFn n)

/-! ## The public constants -/

/-- **An inverse modulo the characteristic**: where `a · b ≡ 1 (mod p)`, `a = b⁻¹` in a field of
characteristic `p`. -/
theorem natCast_eq_inv_of_mul_mod (p : ℕ) [CharP K p] {a b : ℕ} (h : a * b % p = 1) :
    (a : K) = (b : K)⁻¹ := by
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← Nat.cast_mul, ← Nat.mod_add_div (a * b) p, h, Nat.cast_add, Nat.cast_mul,
    CharP.cast_eq_zero K p, zero_mul, add_zero, Nat.cast_one]

end GordieHowe.RealizedProgram.Ops

namespace GordieHowe.RealizedProgram

/-! ## The powers of a challenge -/

/-- **A challenge of one coordinate and the constant `1`** in field `f`: the program facts that
make the symbolic-power matcher's context `⟨onePub one r, none⟩` sound at the challenge's value
(as `TableSelect.pubCtx_one_sound` for the table's `γ`). -/
structure ChalPowers (program : RealizedProgram) (one r chal f : ℕ) : Prop where
  /-- The constant `1`. -/
  consts : program.isConstant one = true ∧ (program.constEntries one).getD 0 0 = 1
  /-- `r` is the challenge `chal`. -/
  kind : (program.value r).kind = .challenge chal
  /-- The challenge is drawn in field `f`. -/
  chalField : program.chalField chal = f
  /-- The values are of field `f`. -/
  fields : program.valueField one = f ∧ program.valueField r = f
  /-- The sizes. -/
  sizes : (program.value one).size = 1 ∧ (program.value r).size = 1
  /-- The program has values. -/
  values_pos : 0 < program.values.length

namespace ChalPowers

variable {program : RealizedProgram} {one r chal f : ℕ} {I : Interp}

/-- **The challenge** read in field `f`. -/
def val (_h : ChalPowers program one r chal f) (e : program.Env I) : (I f).K :=
  castElt (e.chal chal 0)

/-- **The constant `1` and the challenge, one level down.** -/
theorem ctx_sound (h : ChalPowers program one r chal f) (hd : (I f).decode 1 = 1)
    (e : program.Env I) :
    PowCtx.Sound (program.read e program.values.length) f (h.val e) ⟨onePub one r, none⟩ := by
  obtain ⟨n, hn⟩ : ∃ n, program.values.length = n + 1 :=
    ⟨program.values.length - 1, by have := h.values_pos; omega⟩
  refine ⟨fun v l hv => ?_, fun _ _ hk => by cases hk⟩
  simp only [onePub] at hv
  split_ifs at hv with h1 h2 <;> cases hv
  · subst h1
    obtain ⟨c0, e0⟩ := h.consts
    refine ⟨by rw [exprLen_leaf, h.sizes.1]; rfl, fun i hi => ?_⟩
    simp only [List.length_singleton, Nat.lt_one_iff] at hi
    subst hi
    rw [evalE_leaf, hn]
    simp only [read, kind_of_isConstant c0]
    rw [castElt_decode h.fields.1, e0, hd]
    simp
  · subst h2
    refine ⟨by rw [exprLen_leaf, h.sizes.2]; rfl, fun i hi => ?_⟩
    simp only [List.length_singleton, Nat.lt_one_iff] at hi
    subst hi
    rw [evalE_leaf, hn]
    simp only [read, h.kind]
    rw [castElt_castElt_eq, if_pos (h.chalField.trans h.fields.2.symm)]
    simp [val]

/-- **The powers of the challenge**: an expression the matcher reads as the exponents `l` holds
`r^l`, one level down. -/
theorem powsAt (h : ChalPowers program one r chal f) (hd : (I f).decode 1 = 1)
    (ho : program.RefsOrdered) (hne : 0 < program.exprs.length) (e : program.Env I) {n : ℕ}
    {E : Expr} {l : List ℕ} (hp : program.powSym ⟨onePub one r, none⟩ n E = some l) :
    PowsAt (program.read e program.values.length) f (h.val e) E l :=
  powSym_sound ho hne (h.ctx_sound hd e) n E l hp

/-- **The range of powers**: an expression the matcher reads as `0, 1, …, n − 1` holds `r^t` at
`t < n`, one level down. -/
theorem evalE_range (h : ChalPowers program one r chal f) (hd : (I f).decode 1 = 1)
    (ho : program.RefsOrdered) (hne : 0 < program.exprs.length) (e : program.Env I) {m n : ℕ}
    {E : Expr} (hp : program.powSym ⟨onePub one r, none⟩ m E = some (List.range n)) {t : ℕ}
    (ht : t < n) :
    program.evalE (program.read e program.values.length) f E t = h.val e ^ t := by
  rw [(h.powsAt hd ho hne e hp).2 t (by simpa using ht), List.getD_eq_getElem?_getD,
    List.getElem?_range ht, Option.getD_some]

/-- **`r^(2k) + 1`**: the square of an expression the matcher reads as `r^k`, plus the constant
`1`, one level down (the C++'s `r^n + 1`, built from `r^(n/2)`). -/
theorem evalE_sq_add_one (h : ChalPowers program one r chal f) (hd : (I f).decode 1 = 1)
    (ho : program.RefsOrdered) (hne : 0 < program.exprs.length) (e : program.Env I) {m k : ℕ}
    {E : Expr} (hp : program.powSym ⟨onePub one r, none⟩ m E = some [k]) :
    program.evalE (program.read e program.values.length) f (.add (.mul E E) (.leaf one)) 0 =
      h.val e ^ (2 * k) + 1 := by
  rw [evalE_add, evalE_mul, (h.powsAt hd ho hne e hp).2 0 (by simp),
    ((h.ctx_sound hd e).pub one [0] (by simp [onePub])).2 0 (by simp)]
  simp only [List.getD_cons_zero, pow_zero]
  ring

/-- **The interpolation weights in natural order**: `c · Ntt_ψ` of the powers `r^0, …, r^(n−1)`
(`λ(r)` at `c = n⁻¹`, `ψ` the inverse root), one level down. -/
theorem evalE_lambda_natural (h : ChalPowers program one r chal f) (hd : (I f).decode 1 = 1)
    (ho : program.RefsOrdered) (hne : 0 < program.exprs.length) (e : program.Env I) {m n : ℕ}
    {E : Expr} (hp : program.powSym ⟨onePub one r, none⟩ m E = some (List.range n)) (c ψ : ℕ)
    {t : ℕ} (ht : t < n) :
    program.evalE (program.read e program.values.length) f
        (.scale (.const c) (.apply (.ntt n ψ .natural) E)) t =
      (I f).decode c * Ops.nttNatural n ((I f).decode ψ) (fun s => h.val e ^ s) t := by
  rw [evalE_scale_const, evalE_apply]
  simp only [NamedOp.apply, NamedOp.block, NamedOp.rows, NamedOp.cols, Nat.mod_eq_of_lt ht,
    Nat.div_eq_of_lt ht, zero_mul, zero_add]
  rw [NamedOp.nttNatural_congr (fun s hs => h.evalE_range hd ho hne e hp hs)]

/-- **The interpolation weights in scheme order**: `c · Ntt_ψ` of the powers `r^0, …, r^(n−1)` in
scheme order, one level down. -/
theorem evalE_lambda_scheme (h : ChalPowers program one r chal f) (hd : (I f).decode 1 = 1)
    (ho : program.RefsOrdered) (hne : 0 < program.exprs.length) (e : program.Env I) {m n : ℕ}
    {E : Expr} (hp : program.powSym ⟨onePub one r, none⟩ m E = some (List.range n)) (c ψ : ℕ)
    {t : ℕ} (ht : t < n) :
    program.evalE (program.read e program.values.length) f
        (.scale (.const c) (.apply (.ntt n ψ .scheme) E)) t =
      (I f).decode c * Ops.nttScheme n ((I f).decode ψ) (fun s => h.val e ^ s) t := by
  rw [evalE_scale_const, evalE_apply]
  simp only [NamedOp.apply, NamedOp.block, NamedOp.rows, NamedOp.cols, Nat.mod_eq_of_lt ht,
    Nat.div_eq_of_lt ht, zero_mul, zero_add]
  rw [nttScheme_congr (fun s hs => h.evalE_range hd ho hne e hp hs)]

end ChalPowers

/-- **A public inverse**: where `a` and `b` decode to their casts and `a · b ≡ 1 (mod p)`, `a`
decodes to the inverse of `b`'s decoding (`Ops.natCast_eq_inv_of_mul_mod`). -/
theorem decode_eq_inv_of_mul_mod {I : Interp} {f : ℕ} (p : ℕ) [CharP (I f).K p] {a b : ℕ}
    (ha : (I f).decode a = (a : (I f).K)) (hb : (I f).decode b = (b : (I f).K))
    (h : a * b % p = 1) : (I f).decode a = ((I f).decode b)⁻¹ := by
  rw [ha, hb]
  exact Ops.natCast_eq_inv_of_mul_mod p h

/-- **A zero constant of one coordinate** reads `0`. -/
theorem evalE_zeroConst {program : RealizedProgram} {I : Interp} (e : program.Env I) {z f : ℕ}
    (hc : program.isConstant z = true) (hf : program.valueField z = f)
    (he : program.constEntries z = [0]) (hd : (I f).decode 0 = 0) :
    program.evalE (program.reader e) f (.leaf z) 0 = 0 := by
  rw [evalE_leaf_of_isConstant e hc, constRead_of_valueField hf, he]
  simpa using hd

end GordieHowe.RealizedProgram
