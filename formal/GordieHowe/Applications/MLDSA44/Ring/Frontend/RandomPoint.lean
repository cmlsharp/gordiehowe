-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.Library.Eval
public import GordieHowe.Language.Library.EvalPoint
public import GordieHowe.Language.Realizations.RealizeMac

@[expose] public section

/-!
# GordieHowe frontend: the ML-DSA-44 rings' signature relation at a random point

Both ML-DSA-44 ring arms check the signature relation as four polynomial identities over the
field of domain `A`, one per row `i`, each at one challenge `r` (`signature.r`, drawn after the
committed quotients `Q_i` by `X^256 + 1`): the source predicates `signature.relation.0 … 3`
(`rowLhs`),

  `E_i(r) + (r^256 + 1) Q_i(r) + ⟨t̂_i, λ(r)⟩ c(r) − Σ_j ⟨â_ij, λ(r)⟩ z_j(r) = 0`,

coefficient vectors read against the powers `r^t` (`signature.relation.0.public0`), spectra
against the weights `λ(r) = 256⁻¹ · Ntt_{ψ⁻¹}(1, r, …, r^255)` in scheme order
(`signature.lambda`, `Ops.eval_inverseNtt`), `c = support − 2 · sign` read off `challenge.c`, `â`
and `t̂` the committed `member.a_hat` and `member.t1`. The arms differ in the field, the transform
data and the row's first vector `E_i`:

* the native arm (`lib/gordiehowe/examples/rings/mldsa_ring_native.h`, characteristic `q`,
  `ψ = 1753`) reads `E_i = w_i`, the committed `signature.w`;
* the carrier arm (`mldsa_ring_carrier.h`, a Goldilocks extension, `ψ = psi512`) reads
  `E_i = w′_i − q q′_i − q qlo`, its committed integer quotient `q′` at the offset `qlo`.

This file is the layer both share, generic in the program (at the program facts
`MldsaRandomPoint`, each arm's facts extending them), in the field interpretation and in the
transform data (at the field facts `MldsaRandomPointField`):

* **The program facts** (`MldsaRandomPoint`): the value, predicate, challenge and shared-expression
  numbering of the rows, the row's first vector `rowE i` (an expression of `256` coordinates
  headed by `w_i`'s shared expression), the transform data (`ψ`, `256⁻¹`, `ψ⁻¹`, `−1`, `−2` as
  naturals) and the public values' definitions.
* **The rows at `r`** (`rowPoly`, `relEvent`, `evalE_rowLhs`, `rowPoly_eq_zero`, `rowPoly_zero`):
  row `i`'s polynomial `E_i + (X^256 + 1) Q_i + T_i c − Σ_j A_ij z_j` (`T_i`, `A_ij` the inverse
  transforms of the committed spectra), the relation's event (a root of some row's nonzero
  polynomial, `ChallengeEvent.prodNonzero`, degree `4 · 510`), and the row's left side, its value
  at `r` (`holdsAt_row_iff`).
* **The spectral rows** (`row_spectral`): a row whose polynomial is `0`, read at the roots
  `ψ^(2·br(k)+1)` of `X^256 + 1`, is `NTT(E_i)_k = Σ_j â_ijk · NTT(z_j)_k − t̂_ik · NTT(c)_k`.
-/

namespace GordieHowe.MLDSA44.Ring

open GordieHowe.RealizedProgram (Expr IndexMap)

/-! ## The relation rows -/

/-- **Row `i`'s slice** of a `4 × 256` value: coordinates `256 i, …, 256 i + 255`. -/
def rowSlice (i : ℕ) : IndexMap := [(i * 256, 1, 256)]

/-- **Row `i`'s slice of the quotients** (`4 × 255`): coordinates `255 i, …, 255 i + 254`. -/
def qSlice (i : ℕ) : IndexMap := [(i * 255, 1, 255)]

/-- **Block `(i, j)`** of the `4 × 4 × 256` matrix: coordinates `1024 i + 256 j, …`. -/
def aSlice (i j : ℕ) : IndexMap := [(i * 1024 + j * 256, 1, 256)]

/-- **The left side of a row** (`signature.relation.i`, one coordinate):
`Σ_t E_t r^t + (r^256 + 1) Σ_t Q_t r^t + (Σ_k t̂_k λ_k) c(r) − Σ_j (Σ_k â_jk λ_k) z_j(r)`, at the
row's first vector `rE` (`E`), its shared expressions of `Q` (`rq`), `t̂` (`rt`) and `â`
(`ra j`), the shared sums `z_j(r)` (`rz j`) and `c(r)` (`rcr`), the first `255` powers (`rpw1`),
the powers `r^t` (`pw`), `r^256 + 1` (`rn`), the weights `λ` (`lam`) and the field's `−1`
(`mOne`). -/
def rowLhs (rE : Expr) (rq rt : ℕ) (ra rz : Fin 4 → ℕ) (rpw1 rcr pw rn lam mOne : ℕ) : Expr :=
  .add (.add (.add (.add (.add (.add
    (.apply (.sum 256) (.mul rE (.leaf pw)))
    (.mul (.leaf rn) (.apply (.sum 255) (.mul (.ref rq) (.ref rpw1)))))
    (.mul (.apply (.sum 256) (.mul (.ref rt) (.leaf lam))) (.ref rcr)))
    (.scale (.const mOne) (.mul (.apply (.sum 256) (.mul (.ref (ra 0)) (.leaf lam))) (.ref (rz 0)))))
    (.scale (.const mOne) (.mul (.apply (.sum 256) (.mul (.ref (ra 1)) (.leaf lam))) (.ref (rz 1)))))
    (.scale (.const mOne) (.mul (.apply (.sum 256) (.mul (.ref (ra 2)) (.leaf lam))) (.ref (rz 2)))))
    (.scale (.const mOne) (.mul (.apply (.sum 256) (.mul (.ref (ra 3)) (.leaf lam))) (.ref (rz 3))))

/-- **The program facts of an ML-DSA-44 ring's signature relation at a random point**, every
value, predicate, challenge and shared expression named by a field: the committed
`member.a_hat`, `member.t1`, `z`, `challenge.c`, `signature.w` (`w`, the head of each row's first
vector) and the quotients `signature.Q`; the challenge `signature.r` with the constants `1` and
`0`; the public values `r^t`, `λ` and `r^256 + 1`; the four rows `signature.relation.0 … 3`
(predicates `rel0 + i`, source predicates), each row's first vector `rowE i` and the shared
expressions the rows read; the transform data the program's constants hold (`ψ`, `256⁻¹`,
`ψ⁻¹`, `−1`, `−2`, read in a field by `MldsaRandomPointField`). Each arm extends them
(`Native.MldsaRingRelation`, `Carrier.MldsaCarrierRelation`) and each program decides them. -/
class MldsaRandomPoint (program : RealizedProgram) where
  /-- `member.a_hat`. -/
  aHat : ℕ
  /-- `member.t1`. -/
  t1 : ℕ
  /-- `z`. -/
  z : ℕ
  /-- `challenge.c`. -/
  c : ℕ
  /-- `signature.w`. -/
  w : ℕ
  /-- `signature.Q`. -/
  q : ℕ
  /-- `signature.relation.0`; row `i` is predicate `rel0 + i`. -/
  rel0 : ℕ
  /-- `signature.r`. -/
  r : ℕ
  /-- `signature.r`'s challenge. -/
  rChal : ℕ
  /-- The constant `1` (one coordinate). -/
  one : ℕ
  /-- The constant `0` (one coordinate). -/
  zero1 : ℕ
  /-- `r^t`, `t < 256`. -/
  pw : ℕ
  /-- `λ = 256⁻¹ Ntt_{ψ⁻¹}(1, r, …, r^255)` in scheme order. -/
  lam : ℕ
  /-- `r^256 + 1`. -/
  rn : ℕ
  /-- The shared expression of `r^t`. -/
  pwRef : ℕ
  /-- The shared expression of `r^128`. -/
  r128Ref : ℕ
  /-- Row `i`'s first vector `E_i` (`256` coordinates, headed by `w_i`'s shared expression). -/
  rowE : Fin 4 → Expr
  /-- Row `i`'s `w`. -/
  refW : Fin 4 → ℕ
  /-- Row `i`'s `Q`. -/
  refQ : Fin 4 → ℕ
  /-- Row `i`'s `t̂`. -/
  refT : Fin 4 → ℕ
  /-- Block `(i, j)` of `â`. -/
  refA : Fin 4 → Fin 4 → ℕ
  /-- `z_j`. -/
  refZrow : Fin 4 → ℕ
  /-- `z_j(r)`. -/
  refZ : Fin 4 → ℕ
  /-- The first `255` powers. -/
  refPW1 : ℕ
  /-- `c(r)`. -/
  refCR : ℕ
  /-- The challenge's supports. -/
  refSup : ℕ
  /-- The challenge's signs. -/
  refSign : ℕ
  /-- A bound on the shared expressions read. -/
  nRefs : ℕ
  /-- The transform root `ψ`, a primitive `512`-th root of unity (not a program constant). -/
  psi : ℕ
  /-- The constant `256⁻¹`. -/
  nInv : ℕ
  /-- The constant `ψ⁻¹`. -/
  psiInv : ℕ
  /-- The constant `−1`. -/
  mOne : ℕ
  /-- The constant `−2`. -/
  mTwo : ℕ
  /-- Domain `0` has field `0`. -/
  domainField0 : program.domainField 0 = 0
  /-- Shared expressions refer only to earlier ones. -/
  refsOrdered : program.RefsOrdered
  /-- The shared expressions read lie below `nRefs`, which the program has. -/
  refsLt : nRefs ≤ program.exprs.length ∧
    (∀ i, refW i < nRefs ∧ refQ i < nRefs ∧ refT i < nRefs ∧ refZrow i < nRefs ∧ refZ i < nRefs ∧
      ∀ j, refA i j < nRefs) ∧
    refPW1 < nRefs ∧ refCR < nRefs ∧ refSup < nRefs ∧ refSign < nRefs ∧ pwRef < nRefs ∧
    r128Ref < nRefs
  /-- `signature.relation.i` is row `i`. -/
  rows : ∀ i : Fin 4, ∃ t, (program.predicate (rel0 + i)).body =
    .equal 0 (rowLhs (rowE i) (refQ i) (refT i) (refA i) refZ refPW1 refCR pw rn lam mOne)
      (.leaf zero1) t
  /-- The rows are source predicates. -/
  rowSource : ∀ i : Fin 4, rel0 + i < program.predicates.length ∧
    program.inSource (program.predicate (rel0 + i)) = true
  /-- Row `i`'s first vector has the length of `w_i`'s shared expression. -/
  rowELen : ∀ i, program.exprLen (rowE i) = program.exprLen (.ref (refW i))
  /-- Row `i`'s `w`. -/
  exprW : ∀ i : Fin 4, program.expr (refW i) = .reindex (rowSlice i) (.leaf w)
  /-- Row `i`'s `Q`. -/
  exprQ : ∀ i : Fin 4, program.expr (refQ i) = .reindex (qSlice i) (.leaf q)
  /-- Row `i`'s `t̂`. -/
  exprT : ∀ i : Fin 4, program.expr (refT i) = .reindex (rowSlice i) (.leaf t1)
  /-- Block `(i, j)` of `â`. -/
  exprA : ∀ i j : Fin 4, program.expr (refA i j) = .reindex (aSlice i j) (.leaf aHat)
  /-- `z_j`. -/
  exprZrow : ∀ j : Fin 4, program.expr (refZrow j) = .reindex (rowSlice j) (.leaf z)
  /-- `z_j(r)`. -/
  exprZ : ∀ j : Fin 4, program.expr (refZ j) = .apply (.sum 256) (.mul (.ref (refZrow j)) (.leaf pw))
  /-- The first `255` powers. -/
  exprPW1 : program.expr refPW1 = .reindex [(0, 1, 255)] (.leaf pw)
  /-- The challenge's supports. -/
  exprSup : program.expr refSup = .reindex [(0, 2, 256)] (.leaf c)
  /-- The challenge's signs. -/
  exprSign : program.expr refSign = .reindex [(1, 2, 256)] (.leaf c)
  /-- `c(r)`: `Σ_t (support − 2 · sign)_t r^t`. -/
  exprCR : program.expr refCR = .apply (.sum 256)
    (.mul (.add (.ref refSup) (.scale (.const mTwo) (.ref refSign))) (.leaf pw))
  /-- The zero constant of one coordinate, of field `0`. -/
  zeroConst : program.isConstant zero1 = true ∧ program.valueField zero1 = 0 ∧
    program.constEntries zero1 = [0]
  /-- The values the rows read are of field `0`. -/
  rowFields : ∀ v ∈ [w, z, c, q, pw, lam, rn], program.valueField v = 0
  /-- `signature.r` and the constant `1`. -/
  rPow : RealizedProgram.ChalPowers program one r rChal 0
  /-- `signature.r` is one coordinate drawn from the field. -/
  chalR : (program.challenge rChal).size = 1 ∧ (program.challenge rChal).sampler = .full
  /-- `r^t`'s definition. -/
  pwKind : (program.value pw).kind = .pub (.expr (.ref pwRef))
  /-- `λ`'s definition. -/
  lamKind : (program.value lam).kind =
    .pub (.expr (.scale (.const nInv) (.apply (.ntt 256 psiInv .scheme) (.ref pwRef))))
  /-- `r^256 + 1`'s definition. -/
  rnKind : (program.value rn).kind =
    .pub (.expr (.add (.mul (.ref r128Ref) (.ref r128Ref)) (.leaf one)))
  /-- `r^t`, `t < 256`, by the symbolic-power matcher. -/
  powPw : program.powSym ⟨RealizedProgram.onePub one r, none⟩ RealizedProgram.powFuel (.ref pwRef) =
    some (List.range 256)
  /-- `r^128`. -/
  pow128 : program.powSym ⟨RealizedProgram.onePub one r, none⟩ RealizedProgram.powFuel
    (.ref r128Ref) = some [128]

/-- **The left side of row `i`** of a program (`signature.relation.i`). -/
abbrev MldsaRandomPoint.lhs (program : RealizedProgram) [MldsaRandomPoint program] (i : Fin 4) :
    Expr :=
  rowLhs (MldsaRandomPoint.rowE program i) (MldsaRandomPoint.refQ program i)
    (MldsaRandomPoint.refT program i) (MldsaRandomPoint.refA program i)
    (MldsaRandomPoint.refZ program) (MldsaRandomPoint.refPW1 program)
    (MldsaRandomPoint.refCR program) (MldsaRandomPoint.pw program) (MldsaRandomPoint.rn program)
    (MldsaRandomPoint.lam program) (MldsaRandomPoint.mOne program)

/-- **The field facts of the rows** in a field interpretation: `1`, `0`, `−1` and `−2` decode to
themselves, the program's `256⁻¹` and `ψ⁻¹` to the inverses of `256` and of `ψ`, which is a
primitive `512`-th root of unity, and `256 ≠ 0`. Each arm gives them in its fields (native:
characteristic `q`, `ψ = 1753`; carrier: characteristic `p`, `ψ = psi512`). -/
class MldsaRandomPointField (program : RealizedProgram) [MldsaRandomPoint program]
    (F : RealizedProgram.FieldInterp) : Prop where
  /-- `1` decodes to `1`. -/
  decode_one : F.decode 1 = 1
  /-- `0` decodes to `0`. -/
  decode_zero : F.decode 0 = 0
  /-- The constant `−1`. -/
  decode_mOne : F.decode (MldsaRandomPoint.mOne program) = -1
  /-- The constant `−2`. -/
  decode_mTwo : F.decode (MldsaRandomPoint.mTwo program) = -2
  /-- The constant `256⁻¹`. -/
  decode_nInv : F.decode (MldsaRandomPoint.nInv program) = ((256 : ℕ) : F.K)⁻¹
  /-- The constant `ψ⁻¹`. -/
  decode_psiInv : F.decode (MldsaRandomPoint.psiInv program) =
    (F.decode (MldsaRandomPoint.psi program))⁻¹
  /-- `ψ` is a primitive `512`-th root of unity. -/
  psi_isPrimitiveRoot : IsPrimitiveRoot (F.decode (MldsaRandomPoint.psi program)) (2 * 256)
  /-- `256` is invertible. -/
  n_ne_zero : ((256 : ℕ) : F.K) ≠ 0

set_option linter.unusedSectionVars false

/-! ## The rows' polynomials -/

section Rows

variable {program : RealizedProgram} [MldsaRandomPoint program] {I : RealizedProgram.Interp}

/-- **The challenge `r`** (`signature.r`) read in field `0`. -/
def rOf (e : program.Env I) : (I 0).K :=
  RealizedProgram.castElt (e.chal (MldsaRandomPoint.rChal program) 0)

variable (e : program.Env I) (i : Fin 4)

/-- Row `i`'s first vector `E_i` at `t`. -/
def eRow (t : ℕ) : (I 0).K := program.evalE (program.reader e) 0 (MldsaRandomPoint.rowE program i) t
/-- Row `i`'s `w` at `t`. -/
def wRow (t : ℕ) : (I 0).K :=
  program.evalE (program.reader e) 0 (.leaf (MldsaRandomPoint.w program)) ((i : ℕ) * 256 + t)
/-- Row `i`'s `Q` at `t`. -/
def qRow (t : ℕ) : (I 0).K :=
  program.evalE (program.reader e) 0 (.leaf (MldsaRandomPoint.q program)) ((i : ℕ) * 255 + t)
/-- Row `i`'s `t̂` at `k`. -/
def tRow (k : ℕ) : (I 0).K :=
  program.evalE (program.reader e) 0 (.leaf (MldsaRandomPoint.t1 program)) ((i : ℕ) * 256 + k)
/-- Block `(i, j)` of `â` at `k`. -/
def aRow (j : Fin 4) (k : ℕ) : (I 0).K :=
  program.evalE (program.reader e) 0 (.leaf (MldsaRandomPoint.aHat program))
    ((i : ℕ) * 1024 + ((j : ℕ) * 256 + k))
/-- `z_j` at `t`. -/
def zRow (j : Fin 4) (t : ℕ) : (I 0).K :=
  program.evalE (program.reader e) 0 (.leaf (MldsaRandomPoint.z program)) ((j : ℕ) * 256 + t)
/-- The challenge polynomial's coefficient `t`: `support − 2 · sign`. -/
def cRow (t : ℕ) : (I 0).K :=
  program.evalE (program.reader e) 0 (.leaf (MldsaRandomPoint.c program)) (2 * t) -
    2 * program.evalE (program.reader e) 0 (.leaf (MldsaRandomPoint.c program)) (2 * t + 1)

variable {e i}

open Polynomial RealizedProgram.Ops in
/-- **Row `i`'s polynomial** over the field: `E_i + (X^256 + 1) Q_i + T_i c − Σ_j A_ij z_j`,
`T_i` and `A_ij` the polynomials whose scheme-order transforms at `ψ` are the committed `t̂_i` and
`â_ij` (`Ops.inverseNtt`). -/
noncomputable def rowPoly (e : program.Env I) (i : Fin 4) : (I 0).K[X] :=
  polyOf 256 (eRow e i) + (Polynomial.X ^ 256 + 1 : (I 0).K[X]) * polyOf 255 (qRow e i) +
    polyOf 256 (inverseNtt 256 ((I 0).decode (MldsaRandomPoint.psi program)) (tRow e i)) *
      polyOf 256 (cRow e) -
    ∑ j : Fin 4, polyOf 256 (inverseNtt 256 ((I 0).decode (MldsaRandomPoint.psi program))
      (aRow e i j)) * polyOf 256 (zRow e j)

open Polynomial RealizedProgram.Ops in
theorem rowPoly_natDegree (e : program.Env I) (i : Fin 4) : (rowPoly e i).natDegree ≤ 510 := by
  unfold rowPoly
  refine (natDegree_sub_le _ _).trans (max_le ((natDegree_add_le _ _).trans (max_le
    ((natDegree_add_le _ _).trans (max_le ?_ ?_)) ?_)) ?_)
  · exact (Polynomial.ofFn_natDegree_lt (n := 256) (by norm_num) _).le.trans (by norm_num)
  · exact natDegree_quotient_le (n := 256) (by norm_num) _
  · exact natDegree_polyOf_mul_le (n := 256) (by norm_num) _ _
  · exact natDegree_sum_le_of_forall_le _ _ fun j _ =>
      natDegree_polyOf_mul_le (n := 256) (by norm_num) _ _

/-- **The relation's event** (`ChallengeEvent.prodNonzero` of the rows' polynomials, each of
degree at most `510`): `r` is a root of some row's nonzero polynomial, an event of degree at most
`2040 = 4 · 510`. -/
noncomputable def relEvent (e : program.Env I) : ChallengeEvent (I 0).K :=
  ChallengeEvent.prodNonzero (rowPoly e) 510 (rowPoly_natDegree e)

/-- **A row's polynomial is `0`** where it vanishes at `r` and `r` is not in the event. -/
theorem rowPoly_eq_zero {e : program.Env I} (i : Fin 4) (h : (rowPoly e i).eval (rOf e) = 0)
    (hev : ¬ (relEvent e).BadAt (rOf e)) : rowPoly e i = 0 :=
  ChallengeEvent.prodNonzero_eq_zero i h hev

/-- **The relation's event reads the rows' values**: two environments whose rows' first vectors
(below `256`) and committed `â`, `t̂`, `z`, `c`, `Q` read alike have one event. -/
theorem relEvent_congr_of {e e' : program.Env I}
    (hE : ∀ (i : Fin 4), ∀ t < 256, eRow e i t = eRow e' i t)
    (hrd : ∀ v ∈ [MldsaRandomPoint.aHat program, MldsaRandomPoint.t1 program,
      MldsaRandomPoint.z program, MldsaRandomPoint.c program, MldsaRandomPoint.q program], ∀ t,
      program.evalE (program.reader e) 0 (.leaf v) t =
        program.evalE (program.reader e') 0 (.leaf v) t) :
    relEvent e = relEvent e' := by
  have hrow : ∀ i, rowPoly e i = rowPoly e' i := fun i => by
    unfold rowPoly
    rw [RealizedProgram.Ops.polyOf_congr (hE i)]
    unfold qRow tRow aRow zRow cRow
    simp only [hrd (MldsaRandomPoint.aHat program) (by simp),
      hrd (MldsaRandomPoint.t1 program) (by simp), hrd (MldsaRandomPoint.z program) (by simp),
      hrd (MldsaRandomPoint.c program) (by simp), hrd (MldsaRandomPoint.q program) (by simp)]
  exact ChallengeEvent.prodNonzero_congr (funext hrow)

end Rows

/-! ## The rows at `r` -/

section Field

variable {program : RealizedProgram} [MldsaRandomPoint program] {I : RealizedProgram.Interp}
  [MldsaRandomPointField program (I 0)]

/-- `ψ^256 = −1`. -/
theorem psi_pow : ((I 0).decode (MldsaRandomPoint.psi program)) ^ 256 = -1 :=
  DFT.IsPrimitiveRoot.pow_half_eq_neg_one
    (MldsaRandomPointField.psi_isPrimitiveRoot (program := program)) (by decide)

omit [MldsaRandomPointField program (I 0)] in
/-- **A shared expression of the relation** reads its definition. -/
theorem evalE_ref' (rd : program.Valuation I) {r : ℕ} (hr : r < MldsaRandomPoint.nRefs program) :
    program.evalE rd 0 (.ref r) = program.evalE rd 0 (program.expr r) :=
  RealizedProgram.evalE_ref MldsaRandomPoint.refsOrdered rd 0
    (lt_of_lt_of_le hr (MldsaRandomPoint.refsLt (program := program)).1)

theorem exprs_pos : 0 < program.exprs.length :=
  lt_of_le_of_lt (Nat.zero_le _) (lt_of_lt_of_le
    (MldsaRandomPoint.refsLt (program := program)).2.2.1
    (MldsaRandomPoint.refsLt (program := program)).1)

/-- **The powers of `r`**, one level down: `r^t`. -/
theorem evalE_pwRef (e : program.Env I) {t : ℕ} (ht : t < 256) :
    program.evalE (program.read e program.values.length) 0
      (.ref (MldsaRandomPoint.pwRef program)) t = rOf e ^ t :=
  (MldsaRandomPoint.rPow (program := program)).evalE_range (I := I)
    (MldsaRandomPointField.decode_one (program := program)) MldsaRandomPoint.refsOrdered exprs_pos e
    MldsaRandomPoint.powPw ht

/-- **The powers of `r`** (`signature.relation.0.public0`): `r^t`. -/
theorem evalE_pw (e : program.Env I) {t : ℕ} (ht : t < 256) :
    program.evalE (program.reader e) 0 (.leaf (MldsaRandomPoint.pw program)) t = rOf e ^ t := by
  rw [RealizedProgram.evalE_leaf_pubExpr e MldsaRandomPoint.pwKind
    ((MldsaRandomPoint.rowFields (program := program)) _ (by simp)), evalE_pwRef e ht]

/-- **`r^256 + 1`** (`signature.relation.0.public1`). -/
theorem evalE_rn (e : program.Env I) :
    program.evalE (program.reader e) 0 (.leaf (MldsaRandomPoint.rn program)) 0 =
      rOf e ^ 256 + 1 := by
  rw [RealizedProgram.evalE_leaf_pubExpr e MldsaRandomPoint.rnKind
    ((MldsaRandomPoint.rowFields (program := program)) _ (by simp)),
    (MldsaRandomPoint.rPow (program := program)).evalE_sq_add_one (I := I)
      (MldsaRandomPointField.decode_one (program := program)) MldsaRandomPoint.refsOrdered
      exprs_pos e MldsaRandomPoint.pow128]
  rfl

/-- **The interpolation weights** (`signature.lambda`): `256⁻¹ Ntt_{ψ⁻¹}(1, r, …, r^255)` in
scheme order. -/
theorem evalE_lam (e : program.Env I) {t : ℕ} (ht : t < 256) :
    program.evalE (program.reader e) 0 (.leaf (MldsaRandomPoint.lam program)) t =
      ((256 : ℕ) : (I 0).K)⁻¹ * RealizedProgram.Ops.nttScheme 256
        ((I 0).decode (MldsaRandomPoint.psi program))⁻¹ (fun s => rOf e ^ s) t := by
  rw [RealizedProgram.evalE_leaf_pubExpr e MldsaRandomPoint.lamKind
    ((MldsaRandomPoint.rowFields (program := program)) _ (by simp)),
    (MldsaRandomPoint.rPow (program := program)).evalE_lambda_scheme (I := I)
      (MldsaRandomPointField.decode_one (program := program)) MldsaRandomPoint.refsOrdered
      exprs_pos e MldsaRandomPoint.powPw _ _ ht,
    MldsaRandomPointField.decode_nInv, MldsaRandomPointField.decode_psiInv]
  rfl

/-- The zero constant (one coordinate) reads `0` in field `0`. -/
theorem evalE_zero1 (e : program.Env I) :
    program.evalE (program.reader e) 0 (.leaf (MldsaRandomPoint.zero1 program)) 0 = 0 :=
  RealizedProgram.evalE_zeroConst e (MldsaRandomPoint.zeroConst (program := program)).1
    (MldsaRandomPoint.zeroConst (program := program)).2.1
    (MldsaRandomPoint.zeroConst (program := program)).2.2
    (MldsaRandomPointField.decode_zero (program := program))

omit [MldsaRandomPointField program (I 0)] in
theorem evalE_refW (rd : program.Valuation I) (i : Fin 4) {t : ℕ} (ht : t < 256) :
    program.evalE rd 0 (.ref (MldsaRandomPoint.refW program i)) t =
      program.evalE rd 0 (.leaf (MldsaRandomPoint.w program)) ((i : ℕ) * 256 + t) := by
  rw [evalE_ref' rd ((MldsaRandomPoint.refsLt (program := program)).2.1 i).1,
    MldsaRandomPoint.exprW i, RealizedProgram.evalE_reindex, rowSlice,
    RealizedProgram.IndexMap.entry_step_one ht]

omit [MldsaRandomPointField program (I 0)] in
theorem evalE_refQ (rd : program.Valuation I) (i : Fin 4) {t : ℕ} (ht : t < 255) :
    program.evalE rd 0 (.ref (MldsaRandomPoint.refQ program i)) t =
      program.evalE rd 0 (.leaf (MldsaRandomPoint.q program)) ((i : ℕ) * 255 + t) := by
  rw [evalE_ref' rd ((MldsaRandomPoint.refsLt (program := program)).2.1 i).2.1,
    MldsaRandomPoint.exprQ i, RealizedProgram.evalE_reindex, qSlice,
    RealizedProgram.IndexMap.entry_step_one ht]

omit [MldsaRandomPointField program (I 0)] in
theorem evalE_refT (rd : program.Valuation I) (i : Fin 4) {t : ℕ} (ht : t < 256) :
    program.evalE rd 0 (.ref (MldsaRandomPoint.refT program i)) t =
      program.evalE rd 0 (.leaf (MldsaRandomPoint.t1 program)) ((i : ℕ) * 256 + t) := by
  rw [evalE_ref' rd ((MldsaRandomPoint.refsLt (program := program)).2.1 i).2.2.1,
    MldsaRandomPoint.exprT i, RealizedProgram.evalE_reindex, rowSlice,
    RealizedProgram.IndexMap.entry_step_one ht]

omit [MldsaRandomPointField program (I 0)] in
theorem evalE_refA (rd : program.Valuation I) (i j : Fin 4) {t : ℕ} (ht : t < 256) :
    program.evalE rd 0 (.ref (MldsaRandomPoint.refA program i j)) t =
      program.evalE rd 0 (.leaf (MldsaRandomPoint.aHat program))
        ((i : ℕ) * 1024 + ((j : ℕ) * 256 + t)) := by
  rw [evalE_ref' rd (((MldsaRandomPoint.refsLt (program := program)).2.1 i).2.2.2.2.2 j),
    MldsaRandomPoint.exprA i j, RealizedProgram.evalE_reindex, aSlice,
    RealizedProgram.IndexMap.entry_step_one ht, Nat.add_assoc]

theorem evalE_refZ (e : program.Env I) (j : Fin 4) :
    program.evalE (program.reader e) 0 (.ref (MldsaRandomPoint.refZ program j)) 0 =
      ∑ t : Fin 256, zRow e j t * rOf e ^ (t : ℕ) := by
  rw [evalE_ref' _ ((MldsaRandomPoint.refsLt (program := program)).2.1 j).2.2.2.2.1,
    MldsaRandomPoint.exprZ j, RealizedProgram.evalE_apply_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [zero_mul, zero_add, RealizedProgram.evalE_mul,
    evalE_ref' _ ((MldsaRandomPoint.refsLt (program := program)).2.1 j).2.2.2.1,
    MldsaRandomPoint.exprZrow j, RealizedProgram.evalE_reindex, rowSlice,
    RealizedProgram.IndexMap.entry_step_one t.isLt, evalE_pw e t.isLt]
  rfl

theorem evalE_refCR (e : program.Env I) :
    program.evalE (program.reader e) 0 (.ref (MldsaRandomPoint.refCR program)) 0 =
      ∑ t : Fin 256, cRow e t * rOf e ^ (t : ℕ) := by
  rw [evalE_ref' _ (MldsaRandomPoint.refsLt (program := program)).2.2.2.1,
    MldsaRandomPoint.exprCR, RealizedProgram.evalE_apply_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [zero_mul, zero_add, RealizedProgram.evalE_mul, RealizedProgram.evalE_add,
    RealizedProgram.evalE_scale_const, MldsaRandomPointField.decode_mTwo,
    evalE_ref' _ (MldsaRandomPoint.refsLt (program := program)).2.2.2.2.1,
    evalE_ref' _ (MldsaRandomPoint.refsLt (program := program)).2.2.2.2.2.1,
    MldsaRandomPoint.exprSup, MldsaRandomPoint.exprSign, RealizedProgram.evalE_reindex,
    RealizedProgram.evalE_reindex, RealizedProgram.IndexMap.entry_single t.isLt,
    RealizedProgram.IndexMap.entry_single t.isLt, evalE_pw e t.isLt]
  have h1 : (((0 : ℕ) : ℤ) + (2 : ℤ) * ((t : ℕ) : ℤ)).toNat = 2 * t := by omega
  have h2 : (((1 : ℕ) : ℤ) + (2 : ℤ) * ((t : ℕ) : ℤ)).toNat = 2 * t + 1 := by omega
  rw [h1, h2]
  unfold cRow
  ring

theorem evalE_refPW1 (e : program.Env I) {t : ℕ} (ht : t < 255) :
    program.evalE (program.reader e) 0 (.ref (MldsaRandomPoint.refPW1 program)) t = rOf e ^ t := by
  rw [evalE_ref' _ (MldsaRandomPoint.refsLt (program := program)).2.2.1,
    MldsaRandomPoint.exprPW1, RealizedProgram.evalE_reindex,
    RealizedProgram.IndexMap.entry_step_one ht, Nat.zero_add, evalE_pw e (by omega)]

open Polynomial RealizedProgram.Ops in
/-- **Row `i`'s left side** (one coordinate) is row `i`'s polynomial at `r`. -/
theorem evalE_rowLhs (e : program.Env I) (i : Fin 4) :
    program.evalE (program.reader e) 0 (MldsaRandomPoint.lhs program i) 0 =
      (rowPoly e i).eval (rOf e) := by
  have hpw : (256 : ℕ) = 2 ^ 8 := by norm_num
  unfold rowPoly
  rw [eval_sub, eval_add, eval_add, eval_mul, eval_mul, eval_finsetSum, eval_inverseNtt hpw,
    polyOf_eval, polyOf_eval, polyOf_eval, eval_add, eval_pow, eval_X, eval_one,
    ← Fin.sum_univ_eq_sum_range, ← Fin.sum_univ_eq_sum_range, ← Fin.sum_univ_eq_sum_range]
  simp only [eval_mul, eval_inverseNtt hpw, polyOf_eval, ← Fin.sum_univ_eq_sum_range]
  simp only [MldsaRandomPoint.lhs, rowLhs, RealizedProgram.evalE_add,
    RealizedProgram.evalE_scale_const, MldsaRandomPointField.decode_mOne,
    RealizedProgram.evalE_mul, RealizedProgram.evalE_apply_sum, zero_mul, zero_add, evalE_rn,
    evalE_refZ, evalE_refCR]
  have hE : ∀ t : Fin 256,
      program.evalE (program.reader e) 0 (MldsaRandomPoint.rowE program i) t *
      program.evalE (program.reader e) 0 (.leaf (MldsaRandomPoint.pw program)) t =
      eRow e i t * rOf e ^ (t : ℕ) := fun t => by
    rw [evalE_pw e t.isLt]; rfl
  have hQ : ∀ t : Fin 255,
      program.evalE (program.reader e) 0 (.ref (MldsaRandomPoint.refQ program i)) t *
      program.evalE (program.reader e) 0 (.ref (MldsaRandomPoint.refPW1 program)) t =
      qRow e i t * rOf e ^ (t : ℕ) := fun t => by
    rw [evalE_refQ _ i t.isLt, evalE_refPW1 e t.isLt]; rfl
  have hT : ∀ t : Fin 256,
      program.evalE (program.reader e) 0 (.ref (MldsaRandomPoint.refT program i)) t *
      program.evalE (program.reader e) 0 (.leaf (MldsaRandomPoint.lam program)) t =
      tRow e i t * (((256 : ℕ) : (I 0).K)⁻¹ *
        nttScheme 256 ((I 0).decode (MldsaRandomPoint.psi program))⁻¹ (fun s => rOf e ^ s) t) :=
    fun t => by rw [evalE_refT _ i t.isLt, evalE_lam e t.isLt]; rfl
  have hA : ∀ (j : Fin 4) (t : Fin 256),
      program.evalE (program.reader e) 0 (.ref (MldsaRandomPoint.refA program i j)) t *
      program.evalE (program.reader e) 0 (.leaf (MldsaRandomPoint.lam program)) t =
      aRow e i j t * (((256 : ℕ) : (I 0).K)⁻¹ *
        nttScheme 256 ((I 0).decode (MldsaRandomPoint.psi program))⁻¹ (fun s => rOf e ^ s) t) :=
    fun j t => by rw [evalE_refA _ i j t.isLt, evalE_lam e t.isLt]; rfl
  simp only [hE, hQ, hT, hA, Fin.sum_univ_four]
  ring

/-- **Row `i`'s left side has one coordinate.** -/
theorem exprLen_lhs (i : Fin 4) : program.exprLen (MldsaRandomPoint.lhs program i) = 1 := by
  rw [MldsaRandomPoint.lhs, rowLhs, RealizedProgram.exprLen_add, RealizedProgram.exprLen_add,
    RealizedProgram.exprLen_add, RealizedProgram.exprLen_add, RealizedProgram.exprLen_add,
    RealizedProgram.exprLen_add, RealizedProgram.exprLen_apply, RealizedProgram.exprLen_mul,
    MldsaRandomPoint.rowELen i,
    RealizedProgram.exprLen_ref MldsaRandomPoint.refsOrdered (lt_of_lt_of_le
      ((MldsaRandomPoint.refsLt (program := program)).2.1 i).1
      (MldsaRandomPoint.refsLt (program := program)).1),
    MldsaRandomPoint.exprW i, RealizedProgram.exprLen_reindex]
  simp [rowSlice, RealizedProgram.NamedOp.rows, RealizedProgram.NamedOp.cols,
    RealizedProgram.IndexMap.size]

/-- **Row `i` holds exactly where its polynomial vanishes at `r`** (`signature.relation.i`, one
coordinate: its left side is the polynomial at `r`, its right side the zero constant). -/
theorem holdsAt_row_iff (e : program.Env I) (i : Fin 4) :
    program.HoldsAt e (program.predicate (MldsaRandomPoint.rel0 program + i)).body ↔
      (rowPoly e i).eval (rOf e) = 0 := by
  obtain ⟨t, hb⟩ := MldsaRandomPoint.rows (program := program) i
  rw [RealizedProgram.HoldsAt, hb]
  show (∀ k < program.exprLen (MldsaRandomPoint.lhs program i),
      program.evalWith (program.reader e) 0 (MldsaRandomPoint.lhs program i) k =
        program.evalWith (program.reader e) 0 (.leaf (MldsaRandomPoint.zero1 program)) k) ↔ _
  rw [exprLen_lhs]
  constructor
  · intro h
    have hx := h 0 Nat.one_pos
    unfold RealizedProgram.evalWith at hx
    rwa [MldsaRandomPoint.domainField0 (program := program), evalE_zero1, evalE_rowLhs] at hx
  · intro h k hk
    obtain rfl : k = 0 := by omega
    unfold RealizedProgram.evalWith
    rwa [MldsaRandomPoint.domainField0 (program := program), evalE_zero1, evalE_rowLhs]

omit [MldsaRandomPointField program (I 0)] in
/-- **A row holds** where the source program holds (`signature.relation.i`). -/
theorem holds_row {e : program.Env I} (hs : program.SourceSatAt e) (i : Fin 4) :
    program.HoldsAt e (program.predicate (MldsaRandomPoint.rel0 program + i)).body :=
  hs.preds _ (RealizedProgram.predicate_mem (MldsaRandomPoint.rowSource (program := program) i).1)
    (MldsaRandomPoint.rowSource (program := program) i).2

/-- **A row's polynomial is `0`** where the source program holds and `r` is not in the relation's
event: the row's left side, its value at `r`, is `0`. -/
theorem rowPoly_zero {e : program.Env I} (hs : program.SourceSatAt e)
    (hev : ¬ (relEvent e).BadAt (rOf e)) (i : Fin 4) : rowPoly e i = 0 :=
  rowPoly_eq_zero i ((holdsAt_row_iff e i).1 (holds_row hs i)) hev

open Polynomial RealizedProgram.Ops in
/-- **A row whose polynomial is `0`, at the roots**: at the root `ψ^(2·br(k)+1)` of `X^256 + 1`,
`k < 256`, the polynomial reads the transforms,
`NTT(E_i)_k = Σ_j â_ijk · NTT(z_j)_k − t̂_ik · NTT(support − 2 · sign)_k`. -/
theorem row_spectral {e : program.Env I} (i : Fin 4) (hz : rowPoly e i = 0) {k : ℕ}
    (hk : k < 256) :
    nttScheme 256 ((I 0).decode (MldsaRandomPoint.psi program)) (eRow e i) k =
      (∑ j : Fin 4, aRow e i j k *
          nttScheme 256 ((I 0).decode (MldsaRandomPoint.psi program)) (zRow e j) k) -
        tRow e i k * nttScheme 256 ((I 0).decode (MldsaRandomPoint.psi program)) (cRow e) k := by
  have hpw : (256 : ℕ) = 2 ^ 8 := by norm_num
  have hψ := MldsaRandomPointField.psi_isPrimitiveRoot (program := program) (F := I 0)
  have hn := MldsaRandomPointField.n_ne_zero (program := program) (F := I 0)
  have hroot := congrArg (fun P => Polynomial.eval
    (((I 0).decode (MldsaRandomPoint.psi program)) ^ (2 * bitRevNat 8 k + 1)) P) hz
  simp only [Polynomial.eval_zero] at hroot
  rw [rowPoly, eval_sub, eval_add, eval_add, eval_mul, eval_mul,
    eval_X_pow_add_one_root (psi_pow (program := program) (I := I)), zero_mul, add_zero, eval_finsetSum,
    polyOf_eval_root_scheme hpw _ _ hk, polyOf_eval_root_scheme hpw _ _ hk,
    polyOf_eval_root_scheme hpw _ _ hk, nttScheme_inverseNtt hpw hψ hn _ hk] at hroot
  simp only [eval_mul, polyOf_eval_root_scheme hpw _ _ hk,
    nttScheme_inverseNtt hpw hψ hn _ hk] at hroot
  linear_combination hroot

end Field

end GordieHowe.MLDSA44.Ring
