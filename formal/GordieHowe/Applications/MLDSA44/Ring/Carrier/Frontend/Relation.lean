-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA44.Emulated.Rows
public import GordieHowe.Applications.MLDSA44.Frontend.AField
public import GordieHowe.Applications.Spec.Rq
public import GordieHowe.Foundations.Fields.GoldilocksRoot512
public import GordieHowe.Language.Library.Cross
public import GordieHowe.Language.Realizations.RealizeMac
public import GordieHowe.Language.Realizations.RealizeInteger
public import GordieHowe.Language.RealizedProgram.BroadcastForm

@[expose] public section

/-!
# GordieHowe frontend: the signature relation of the ML-DSA-44 ring carriers

The ML-DSA-44 ring carriers (`MLDSA44.Ring.Carrier.ROMParams`, `MLDSA44.Ring.Carrier.QROMParams`,
export `5d775ae1`; `carrier_relation` in `lib/gordiehowe/examples/rings/mldsa_ring_carrier.h`)
check ML-DSA's verification equation `w′ = A z − c · 2^d t1` in domain `A` over a Goldilocks
extension. The selected member's key enters as carrier spectra: `member.a_hat` (value `55`) holds,
at coordinate `(4 i + j) · 256 + m`, coordinate `m` of the scheme-order negacyclic transform at
`ψ = psi512` (`GordieHowe.psi512_isPrimitiveRoot`) of `A_ij`'s coefficients, and `member.t1`
(value `56`) at `256 i + m` that of `2^d t1_i`'s. The relation (`signature.relation`, predicate `3`)
is one `mod_q` of the spectral product form: at row `i`, `w′_i ≡ Σ_j A_ij ⊛ z_j − 2^d t1_i ⊛ c`
with `c = sup − 2 · sgn` read off the challenge bits (value `62`), each product a
`polyBroadcast` of a committed spectrum in scheme order (`ConvForm.ntt`).

This file proves the relation's meaning, generic in the program at the program facts
`MldsaCarrierRelation` (decided per program):

* **The readings** `wVals`, `zVals`, `cBits` of `w′` (value `63`), `z` (value `60`) and the challenge
  bits, and the extracted `wOf`, `zOf`, `cPoly` (the emulated proof of possession's, at the
  ring's values).
* **The spectra** (`SpectraOf pk rd`): the hypothesis that values `55` and `56` hold the scheme-order
  transforms of `Rows.aKeyOf pk` and `Rows.tKeyOf pk`.
* **The integer reading of the relation**: the inverse transform of a committed spectrum is the
  key (`Ops.inverseNtt_nttScheme`), whose coefficients lie below `q`, so each matrix entry of a
  product reads as the key's coefficient (`coefInt_spectrum`), and the sides' integer readings are
  `w′` and the negacyclic sums `Σ_j A_ij ⊛ z_j − t_i ⊛ c` over the integers (`evalIntWith_sigP`,
  `evalIntWith_rowN`). The integer reading is exact over `ℤ`, so no bound on the products is
  needed beyond the entries' (`2 q < p`).
* **The congruence** (`congruent_carrier`): where the source program holds, at a key whose spectra
  values `55` and `56` hold, `Rows.Congruent (Rows.aKeyOf pk) (Rows.tKeyOf pk)` at the readings, and
  so `w′ = computeWApprox(Â, c, z, t1)` (`algebra_carrier`).
-/

namespace GordieHowe.MLDSA44.Ring.Carrier

open RealizedProgram

/-- `q` is prime (`instFactPrimeMlDsaQ`), so the coefficients form a field. -/
def factPrimeModulus : Fact (Nat.Prime _root_.MLDSA.modulus) := instFactPrimeMlDsaQ

attribute [local instance] factPrimeModulus

/-! ## The relation's expressions -/

/-- **Row block `r` of `256` coordinates**: the view `256 r, …, 256 r + 255`. -/
def rowSeg (r : ℕ) : IndexMap := IndexMap.ofSegs [.run (256 * r, 1, 256)]

/-- **The even coordinates** `0, 2, …, 510` (the challenge's support bits). -/
def evenSeg : IndexMap := IndexMap.ofSegs [.run (0, 2, 256)]

/-- **The odd coordinates** `1, 3, …, 511` (the challenge's sign bits). -/
def oddSeg : IndexMap := IndexMap.ofSegs [.run (1, 2, 256)]

/-- **The product `A_ij ⊛ z_j`**: row block `4 i + j` of the broadcast of `member.a_hat`'s `16`
spectra against `z_j`. -/
def aTerm (i j : ℕ) : Expr :=
  .reindex (rowSeg (4 * i + j))
    (.apply (.polyBroadcast 55 16 (.ntt psi512)) (.reindex (rowSeg j) (.leaf 60)))

/-- **The challenge polynomial** `sup − 2 · sgn` (shared expressions `37`, `38`). -/
def cExpr : Expr := .add (.ref 37) (.scale (.const 18446744069414584319) (.ref 38))

/-- **The product `2^d t1_i ⊛ c`**: row block `i` of the broadcast of `member.t1`'s `4` spectra
against the challenge polynomial. -/
def tTerm (i : ℕ) : Expr :=
  .reindex (rowSeg i) (.apply (.polyBroadcast 56 4 (.ntt psi512)) cExpr)

/-- **Row `i` of the relation's right side**: `Σ_j A_ij ⊛ z_j − 2^d t1_i ⊛ c`. -/
def rowN (i : ℕ) : Expr :=
  .add (.add (.add (.add (aTerm i 0) (aTerm i 1)) (aTerm i 2)) (aTerm i 3))
    (.scale (.const 18446744069414584320) (tTerm i))

/-- **The shared expression of row `i` of `w′`** (`36`, `39`, `40`, `41`). -/
def wRef : ℕ → ℕ
  | 0 => 36
  | 1 => 39
  | 2 => 40
  | _ => 41

/-- **Row `i` of the relation's left side**: the shared expression of row `i` of `w′`. -/
def rowP (i : ℕ) : Expr := .ref (wRef i)

/-- **The relation's left side**: the rows of `w′`. -/
def sigP : Expr := .concat (rowP 0) (.concat (rowP 1) (.concat (rowP 2) (rowP 3)))

/-- **The relation's right side**: the rows `Σ_j A_ij ⊛ z_j − 2^d t1_i ⊛ c`. -/
def sigN : Expr := .concat (rowN 0) (.concat (rowN 1) (.concat (rowN 2) (rowN 3)))

/-! ## The program facts -/

/-- **The program facts of an ML-DSA ring carrier's signature relation** (decided per program):
the shared expressions of `w′`'s rows (`36`, `39`, `40`, `41`) and of the challenge's support and
sign (`37`, `38`); `signature.relation` (predicate `3`, a `mod_q` of the spectral product form);
the challenge bits' type check (`10`); the ranges `signature.w` (`14`, `w′` below `2^24`) and
`norm.z` (`15`, `z + 130993` below `261987`), with the offset `norm.z.offset` (value `65`); and the
sizes, fields and kinds of the values read. -/
class MldsaCarrierRelation (program : RealizedProgram) : Prop where
  /-- The shared expressions are ordered. -/
  refsOrdered : program.RefsOrdered
  /-- The shared expressions read exist. -/
  exprsLen : 41 < program.exprs.length
  /-- Row `0` of `w′`. -/
  expr36 : program.expr 36 = .reindex (rowSeg 0) (.leaf 63)
  /-- Row `1` of `w′`. -/
  expr39 : program.expr 39 = .reindex (rowSeg 1) (.leaf 63)
  /-- Row `2` of `w′`. -/
  expr40 : program.expr 40 = .reindex (rowSeg 2) (.leaf 63)
  /-- Row `3` of `w′`. -/
  expr41 : program.expr 41 = .reindex (rowSeg 3) (.leaf 63)
  /-- The challenge's support bits. -/
  expr37 : program.expr 37 = .reindex evenSeg (.leaf 62)
  /-- The challenge's sign bits. -/
  expr38 : program.expr 38 = .reindex oddSeg (.leaf 62)
  /-- `signature.relation`: `q` divides the sides' integer difference. -/
  sig : ∃ real, (program.predicate 3).body = .mod 0 8380417 sigP sigN real ∧
    real.form = .spectralProduct
  /-- `challenge.c.boolean`. -/
  cBool : (program.predicate 10).body.boolCheck? = some ⟨0, 62⟩
  /-- `signature.w`: `w′` below `2^24`. -/
  wRange : ∃ r, (program.predicate 14).body = .mem 0 [.leaf 63] (.range 16777216) r
  /-- `norm.z`: `z + 130993` below `261987`. -/
  zRange : ∃ r, (program.predicate 15).body = .mem 0 [.add (.leaf 60) (.leaf 65)] (.range 261987) r
  /-- The predicates read are source predicates. -/
  inSource : ∀ p ∈ [3, 10, 14, 15],
    p < program.predicates.length ∧ program.inSource (program.predicate p) = true
  /-- `norm.z.offset` is the constant `130993`. -/
  offset : program.isConstant 65 = true ∧ program.valueField 65 = 0 ∧
    program.constEntries 65 = List.replicate 1024 130993
  /-- `member.a_hat`'s size. -/
  size55 : (program.value 55).size = 4096
  /-- `member.t1`'s size. -/
  size56 : (program.value 56).size = 1024
  /-- `z`'s size. -/
  size60 : (program.value 60).size = 1024
  /-- The challenge bits' size. -/
  size62 : (program.value 62).size = 512
  /-- `w′`'s size. -/
  size63 : (program.value 63).size = 1024
  /-- Domain `0` is field `0`. -/
  domainField0 : program.domainField 0 = 0
  /-- `z` lies in field `0`. -/
  field60 : program.valueField 60 = 0
  /-- The challenge bits lie in field `0`. -/
  field62 : program.valueField 62 = 0
  /-- `w′` lies in field `0`. -/
  field63 : program.valueField 63 = 0
  /-- `z` is bound to its digits. -/
  kind60 : (program.value 60).kind.isBound = true
  /-- `w′` is bound to its digits. -/
  kind63 : (program.value 63).kind.isBound = true
  /-- The challenge bits are committed. -/
  kind62 : (program.value 62).kind = .priv

/-! ## The index maps -/

theorem rowSeg_entry (r : ℕ) {k : ℕ} (hk : k < 256) : (rowSeg r).entry k = 256 * r + k :=
  IndexMap.entry_step_one hk

theorem rowSeg_size (r : ℕ) : (rowSeg r).size = 256 := IndexMap.size_single _ _ _

theorem evenSeg_entry {k : ℕ} (hk : k < 256) : evenSeg.entry k = 2 * k := by
  show IndexMap.entry [(0, 2, 256)] k = _
  rw [IndexMap.entry_single hk]
  omega

theorem oddSeg_entry {k : ℕ} (hk : k < 256) : oddSeg.entry k = 2 * k + 1 := by
  show IndexMap.entry [(1, 2, 256)] k = _
  rw [IndexMap.entry_single hk]
  omega

/-! ## The keys as integers -/

/-- **A key polynomial's coefficients as integers**, `0` past the degree. -/
def keyZ (key : Fin 256 → ℕ) (s : ℕ) : ℤ := if hs : s < 256 then (key ⟨s, hs⟩ : ℤ) else 0

/-- **A key polynomial cast into a field**, `0` past the degree. -/
abbrev keyPoly (K : Type*) [Field K] (key : Fin 256 → ℕ) : ℕ → K :=
  Ops.ofFin fun s : Fin 256 => ((key s : ℕ) : K)

section Field

variable {I : RealizedProgram.Interp} [MLDSA44.AField (I 0)]

theorem decode_lt0 {c : ℕ} (hc : c < pGold) : (I 0).decode c = (c : (I 0).K) :=
  MLDSA44.AField.decode_lt c hc

theorem toNat_lt0 {k : ℕ} (hk : k < pGold) : (I 0).toNat (k : (I 0).K) = k :=
  MLDSA44.AField.toNat_natCast k hk

/-- **The integer reading of a small integer's cast** is the integer. -/
theorem coefInt_small {z : ℤ} (hz : 2 * |z| < pGold) : (I 0).coefInt (z : (I 0).K) = z :=
  FieldInterp.coefInt_intCast MLDSA44.AField.char_spec MLDSA44.AField.charP
    (fun _ hk => toNat_lt0 hk) hz

/-- **A small natural's centred reading** is itself. -/
theorem centered_small0 {c : ℕ} (hc : 2 * c < pGold) : (I 0).centered c = c := by
  unfold FieldInterp.centered
  rw [MLDSA44.AField.char_spec, if_pos hc]

/-- **`p − 1`'s centred reading** is `−1`. -/
theorem centered_mOne : (I 0).centered 18446744069414584320 = -1 := by
  unfold FieldInterp.centered
  rw [MLDSA44.AField.char_spec, if_neg (by norm_num [pGold])]
  norm_num [pGold]

/-- **`p − 2`'s centred reading** is `−2`. -/
theorem centered_mTwo : (I 0).centered 18446744069414584319 = -2 := by
  unfold FieldInterp.centered
  rw [MLDSA44.AField.char_spec, if_neg (by norm_num [pGold])]
  norm_num [pGold]

/-- **The polynomial of a key's spectrum is the key**: the inverse transform at `ψ = psi512` of
the scheme-order transform of a key whose coefficients lie below `q`, read in field `f = 0`, has
matrix entries reading (`FieldInterp.coefInt`) as the key's negacyclic coefficients. -/
theorem coefInt_spectrum {f : ℕ} (hf : f = 0) {a : ℕ} {x : ℕ → (I a).K} {key : Fin 256 → ℕ}
    (hkey : ∀ s, key s < Emulated.Rows.q)
    (hx : ∀ m < 256, (castElt (x m) : (I 0).K) =
      Ops.nttScheme 256 (psi512 : (I 0).K) (keyPoly (I 0).K key) m) (k t : ℕ) :
    (I f).coefInt (Ops.negCoef 256
      (NamedOp.formPoly (I := I) f 256 (fun s => castElt (x s)) (.ntt psi512)) k t) =
      Ops.negCoef 256 (keyZ key) k t := by
  subst hf
  refine FieldInterp.coefInt_negCoef MLDSA44.AField.char_spec MLDSA44.AField.charP
    (fun _ hk => toNat_lt0 hk) (by norm_num [pGold]) 256 (fun s hs => ⟨?_, ?_⟩) k t
  · have h := hkey ⟨s, hs⟩
    change key ⟨s, hs⟩ < 8380417 at h
    simp only [keyZ, dif_pos hs]
    rw [abs_of_nonneg (Int.natCast_nonneg _)]
    norm_num [pGold]
    omega
  · show Ops.inverseNtt 256 ((I 0).decode psi512) (fun s => castElt (x s)) s = _
    rw [decode_lt0 (by norm_num [pGold]), Ops.inverseNtt_congr hx,
      Ops.inverseNtt_nttScheme (k := 8) (by norm_num) psi512_isPrimitiveRoot natCast_256_ne_zero _ hs]
    simp only [keyPoly, keyZ, Ops.ofFin_of_lt _ hs, dif_pos hs, Int.cast_natCast]

/-- **A sum against a negacyclic coefficient row, modulo `q`**, is the negacyclic product's
coefficient of the casts. -/
theorem cast_sum_negCoef {n : ℕ} (h x : ℕ → ℤ) {k : ℕ} (hk : k < n) :
    ((∑ k' : Fin n, Ops.negCoef n h k k' * x k' : ℤ) : _root_.MLDSA.Coeff) =
      LatticeCrypto.negacyclicConvCoeff (fun m : Fin n => (h m : _root_.MLDSA.Coeff))
        (fun m => (x m : _root_.MLDSA.Coeff)) ⟨k, hk⟩ := by
  push_cast
  have hmap : ∀ k', ((Ops.negCoef n h k k' : ℤ) : _root_.MLDSA.Coeff) =
      Ops.negCoef n (fun s => (h s : _root_.MLDSA.Coeff)) k k' := fun k' =>
    Ops.negCoef_map (Int.castAddHom _root_.MLDSA.Coeff) n h k k'
  simp only [hmap]
  rw [Fin.sum_univ_eq_sum_range (fun k' => Ops.negCoef n (fun s => (h s : _root_.MLDSA.Coeff)) k k' *
    (x k' : _root_.MLDSA.Coeff)) n, ← Ops.negacyclic_eq_sum_negCoef n _ _ hk, Ops.negacyclic,
    Ops.ofFin_of_lt _ hk]
  rfl

end Field

/-! ## The readings -/

section Readings

variable {program : RealizedProgram} {I : RealizedProgram.Interp}

/-- **`z`** (value `60`, `4 × 256`), in field `0`. -/
def zVals (rd : program.Valuation I) (j : Fin _root_.MLDSA.mldsa44.l)
    (k : Fin _root_.MLDSA.ringDegree) : (I 0).K :=
  program.evalE rd 0 (.leaf 60) ((j : ℕ) * 256 + k)

/-- **`w′`** (value `63`, `signature.w`, `4 × 256`), in field `0`. -/
def wVals (rd : program.Valuation I) (i : Fin _root_.MLDSA.mldsa44.k)
    (k : Fin _root_.MLDSA.ringDegree) : (I 0).K :=
  program.evalE rd 0 (.leaf 63) ((i : ℕ) * 256 + k)

/-- **The challenge bits** (value `62`, `challenge.c`, `256 × 2`: support, sign). -/
def cBits (rd : program.Valuation I) (k : Fin _root_.MLDSA.ringDegree) (s : Fin 2) : (I 0).K :=
  program.evalE rd 0 (.leaf 62) (2 * k + s)

/-- **The extracted `z`**: each coefficient the integer its element is (`FieldInterp.coefInt`),
modulo `q`. -/
def zOf (rd : program.Valuation I) : _root_.MLDSA.RqVec _root_.MLDSA.mldsa44.l :=
  Vector.ofFn fun j => MLDSA44.ofCoeff fun k => ((I 0).coefInt (zVals rd j k) : _root_.MLDSA.Coeff)

/-- **The extracted `w′`**: each coefficient the integer its element is, modulo `q`. -/
def wOf (rd : program.Valuation I) : _root_.MLDSA.RqVec _root_.MLDSA.mldsa44.k :=
  Vector.ofFn fun i => MLDSA44.ofCoeff fun k => ((I 0).coefInt (wVals rd i k) : _root_.MLDSA.Coeff)

/-- **The challenge polynomial**: `support − 2 · sign` of the challenge bits. -/
def cPoly (rd : program.Valuation I) : _root_.MLDSA.Rq :=
  MLDSA44.ofCoeff fun k =>
    Native.Rows.bitCoeff (cBits rd k 0) - 2 * Native.Rows.bitCoeff (cBits rd k 1)

/-- **The committed spectra are the transforms of `pk`'s keys**: `member.a_hat` (value `55`) holds,
at `(4 i + j) · 256 + m`, coordinate `m` of the scheme-order transform at `ψ = psi512` of `A_ij`'s
coefficients (`Rows.aKeyOf pk`, below `q`), and `member.t1` (value `56`) at `256 i + m` that of
`2^d t1_i`'s (`Rows.tKeyOf pk`). -/
structure SpectraOf (pk : Native.Rows.PublicKey) (rd : program.Valuation I) : Prop where
  /-- `member.a_hat` holds the transforms of `A`. -/
  a : ∀ (i j : Fin 4), ∀ m < 256, program.evalE rd 0 (.leaf 55) (((i : ℕ) * 4 + j) * 256 + m) =
    Ops.nttScheme 256 (psi512 : (I 0).K) (keyPoly (I 0).K (Emulated.Rows.aKeyOf pk i j)) m
  /-- `member.t1` holds the transforms of `2^d t1`. -/
  t : ∀ i : Fin 4, ∀ m < 256, program.evalE rd 0 (.leaf 56) ((i : ℕ) * 256 + m) =
    Ops.nttScheme 256 (psi512 : (I 0).K) (keyPoly (I 0).K (Emulated.Rows.tKeyOf pk i)) m

/-- **The naturals of `w′`** (its integer reading). -/
def wv (rd : program.Valuation I) (i : Fin 4) (k : Fin 256) : ℕ :=
  (program.intOf rd 63 ((i : ℕ) * 256 + k)).toNat

/-- **The shifted naturals of `z`** (`z + (γ₁ − β − 1)`). -/
def zv (rd : program.Valuation I) (j : Fin 4) (m : Fin 256) : ℕ :=
  (program.intOf rd 60 ((j : ℕ) * 256 + m) + 130993).toNat

/-- **The challenge polynomial's integers**: `support − 2 · sign` of the bits' integer readings. -/
def cInt (rd : program.Valuation I) (m : ℕ) : ℤ :=
  program.intOf rd 62 (2 * m) - 2 * program.intOf rd 62 (2 * m + 1)

end Readings

/-! ## The integer reading of the relation -/

section Eval

variable {program : RealizedProgram} [MldsaCarrierRelation program] {I : RealizedProgram.Interp}
  [MLDSA44.AField (I 0)]

/-- **A concatenation of four blocks of `256`** reads block `i` at `256 i + k`. -/
theorem evalIntWith_concat4 (rd : program.Valuation I) (f : ℕ → Expr)
    (hf : ∀ r < 4, program.exprLen (f r) = 256) {i k : ℕ} (hi : i < 4) (hk : k < 256) :
    program.evalIntWith rd 0 (.concat (f 0) (.concat (f 1) (.concat (f 2) (f 3)))) (i * 256 + k) =
      program.evalIntWith rd 0 (f i) k := by
  have h0 := hf 0 (by norm_num)
  have h1 := hf 1 (by norm_num)
  have h2 := hf 2 (by norm_num)
  simp only [evalIntWith_concat, h0, h1, h2]
  interval_cases i
  · rw [if_pos (show 0 * 256 + k < 256 by omega), Nat.zero_mul, Nat.zero_add]
  · rw [if_neg (show ¬ 1 * 256 + k < 256 by omega), if_pos (show 1 * 256 + k - 256 < 256 by omega),
      show 1 * 256 + k - 256 = k by omega]
  · rw [if_neg (show ¬ 2 * 256 + k < 256 by omega),
      if_neg (show ¬ 2 * 256 + k - 256 < 256 by omega),
      if_pos (show 2 * 256 + k - 256 - 256 < 256 by omega),
      show 2 * 256 + k - 256 - 256 = k by omega]
  · rw [if_neg (show ¬ 3 * 256 + k < 256 by omega),
      if_neg (show ¬ 3 * 256 + k - 256 < 256 by omega),
      if_neg (show ¬ 3 * 256 + k - 256 - 256 < 256 by omega),
      show 3 * 256 + k - 256 - 256 - 256 = k by omega]

/-- The length of a concatenation of four blocks of `256`. -/
theorem exprLen_concat4 (f : ℕ → Expr) (hf : ∀ r < 4, program.exprLen (f r) = 256) :
    program.exprLen (.concat (f 0) (.concat (f 1) (.concat (f 2) (f 3)))) = 1024 := by
  simp only [exprLen_concat, hf 0 (by norm_num), hf 1 (by norm_num), hf 2 (by norm_num),
    hf 3 (by norm_num)]

theorem wRef_lt {r : ℕ} : wRef r < program.exprs.length := by
  have := MldsaCarrierRelation.exprsLen (program := program)
  unfold wRef
  split <;> omega

theorem expr_wRef {r : ℕ} (hr : r < 4) : program.expr (wRef r) = .reindex (rowSeg r) (.leaf 63) := by
  interval_cases r
  · exact MldsaCarrierRelation.expr36
  · exact MldsaCarrierRelation.expr39
  · exact MldsaCarrierRelation.expr40
  · exact MldsaCarrierRelation.expr41

theorem exprLen_rowP {r : ℕ} (hr : r < 4) : program.exprLen (rowP r) = 256 := by
  rw [rowP, exprLen_ref MldsaCarrierRelation.refsOrdered wRef_lt, expr_wRef hr, exprLen_reindex,
    rowSeg_size]

theorem exprLen_rowN (r : ℕ) : program.exprLen (rowN r) = 256 := by
  rw [rowN, exprLen_add, exprLen_add, exprLen_add, exprLen_add, aTerm, exprLen_reindex, rowSeg_size]

/-- **The relation's left side has `1024` coordinates.** -/
theorem exprLen_sigP : program.exprLen sigP = 1024 :=
  exprLen_concat4 rowP fun _ hr => exprLen_rowP hr

/-- **The relation's left side on the integers** at row `i`, coefficient `k`: `w′`'s integer
reading. -/
theorem evalIntWith_sigP (rd : program.Valuation I) {i k : ℕ} (hi : i < 4) (hk : k < 256) :
    program.evalIntWith rd 0 sigP (i * 256 + k) = program.intOf rd 63 (i * 256 + k) := by
  rw [sigP, evalIntWith_concat4 rd rowP (fun _ hr => exprLen_rowP hr) hi hk, rowP,
    evalIntWith_ref MldsaCarrierRelation.refsOrdered rd 0 wRef_lt, expr_wRef hi,
    evalIntWith_reindex, rowSeg_entry _ hk, evalIntWith_leaf, Nat.mul_comm]

/-- **The product `A_ij ⊛ z_j` on the integers**, at a key whose spectra value `55` holds: the
negacyclic sums of `A_ij`'s coefficients against `z_j`'s integer readings. -/
theorem evalIntWith_aTerm {pk : Native.Rows.PublicKey} {rd : program.Valuation I}
    (hS : SpectraOf pk rd) (i j : Fin 4) {k : ℕ} (hk : k < 256) :
    program.evalIntWith rd 0 (aTerm i j) k =
      ∑ t : Fin 256, Ops.negCoef 256 (keyZ (Emulated.Rows.aKeyOf pk i j)) k t *
        program.intOf rd 60 ((j : ℕ) * 256 + t) := by
  have hr : 4 * (i : ℕ) + j < 16 := by omega
  rw [aTerm, evalIntWith_reindex, rowSeg_entry _ hk, evalIntWith_apply,
    show 256 * (4 * (i : ℕ) + j) + k = (4 * i + j) * 256 + k by ring,
    NamedOp.applyInt_polyBroadcast_block program rd 55 16 256 _ _
      (by rw [MldsaCarrierRelation.size55]) hr hk]
  refine Finset.sum_congr rfl fun t _ => ?_
  congr 1
  · refine coefInt_spectrum (x := fun s => rd 55 ((4 * (i : ℕ) + j) * 256 + s))
      MldsaCarrierRelation.domainField0 (Emulated.Rows.aKeyOf_lt pk i j) (fun m hm => ?_) k t
    have h := hS.a i j m hm
    rw [show ((i : ℕ) * 4 + j) * 256 + m = (4 * i + j) * 256 + m by ring, evalE_leaf] at h
    exact h
  · rw [evalIntWith_reindex, rowSeg_entry _ t.isLt, evalIntWith_leaf, Nat.mul_comm]

/-- **The challenge polynomial on the integers**: `sup − 2 · sgn` of the bits' integer
readings. -/
theorem evalIntWith_cExpr (rd : program.Valuation I) {t : ℕ} (ht : t < 256) :
    program.evalIntWith rd 0 cExpr t = cInt rd t := by
  have ho := MldsaCarrierRelation.refsOrdered (program := program)
  have hl := MldsaCarrierRelation.exprsLen (program := program)
  rw [cExpr, evalIntWith_add, evalIntWith_scale_const, evalIntWith_ref ho rd 0 (by omega),
    evalIntWith_ref ho rd 0 (by omega), MldsaCarrierRelation.expr37, MldsaCarrierRelation.expr38,
    evalIntWith_reindex, evalIntWith_reindex, evenSeg_entry ht, oddSeg_entry ht, evalIntWith_leaf,
    evalIntWith_leaf, MldsaCarrierRelation.domainField0, centered_mTwo, cInt]
  ring

/-- **The product `2^d t1_i ⊛ c` on the integers**, at a key whose spectra value `56` holds: the
negacyclic sums of `2^d t1_i`'s coefficients against the challenge polynomial's integers. -/
theorem evalIntWith_tTerm {pk : Native.Rows.PublicKey} {rd : program.Valuation I}
    (hS : SpectraOf pk rd) (i : Fin 4) {k : ℕ} (hk : k < 256) :
    program.evalIntWith rd 0 (tTerm i) k =
      ∑ t : Fin 256, Ops.negCoef 256 (keyZ (Emulated.Rows.tKeyOf pk i)) k t * cInt rd t := by
  rw [tTerm, evalIntWith_reindex, rowSeg_entry _ hk, evalIntWith_apply,
    show 256 * (i : ℕ) + k = i * 256 + k by ring,
    NamedOp.applyInt_polyBroadcast_block program rd 56 4 256 _ _
      (by rw [MldsaCarrierRelation.size56]) i.isLt hk]
  refine Finset.sum_congr rfl fun t _ => ?_
  congr 1
  · refine coefInt_spectrum (x := fun s => rd 56 ((i : ℕ) * 256 + s))
      MldsaCarrierRelation.domainField0 (fun s => KeyNTT.vals_lt _ s) (fun m hm => ?_) k t
    have h := hS.t i m hm
    rw [evalE_leaf] at h
    exact h
  · exact evalIntWith_cExpr rd t.isLt

/-- **Row `i` of the relation's right side on the integers**: `Σ_j A_ij ⊛ z_j − 2^d t1_i ⊛ c`
over the integers. -/
theorem evalIntWith_rowN {pk : Native.Rows.PublicKey} {rd : program.Valuation I}
    (hS : SpectraOf pk rd) (i : Fin 4) {k : ℕ} (hk : k < 256) :
    program.evalIntWith rd 0 (rowN i) k =
      ∑ j : Fin 4, ∑ t : Fin 256, Ops.negCoef 256 (keyZ (Emulated.Rows.aKeyOf pk i j)) k t *
        program.intOf rd 60 ((j : ℕ) * 256 + t) -
      ∑ t : Fin 256, Ops.negCoef 256 (keyZ (Emulated.Rows.tKeyOf pk i)) k t * cInt rd t := by
  rw [rowN, evalIntWith_add, evalIntWith_add, evalIntWith_add, evalIntWith_add,
    evalIntWith_scale_const, MldsaCarrierRelation.domainField0, centered_mOne, Fin.sum_univ_four,
    ← evalIntWith_aTerm hS i 0 hk, ← evalIntWith_aTerm hS i 1 hk, ← evalIntWith_aTerm hS i 2 hk,
    ← evalIntWith_aTerm hS i 3 hk, ← evalIntWith_tTerm hS i hk]
  have e0 : ((0 : Fin 4) : ℕ) = 0 := rfl
  have e1 : ((1 : Fin 4) : ℕ) = 1 := rfl
  have e2 : ((2 : Fin 4) : ℕ) = 2 := rfl
  have e3 : ((3 : Fin 4) : ℕ) = 3 := rfl
  rw [e0, e1, e2, e3]
  ring

/-- **The relation's right side on the integers** at row `i`, coefficient `k`. -/
theorem evalIntWith_sigN {pk : Native.Rows.PublicKey} {rd : program.Valuation I}
    (hS : SpectraOf pk rd) (i : Fin 4) {k : ℕ} (hk : k < 256) :
    program.evalIntWith rd 0 sigN ((i : ℕ) * 256 + k) =
      ∑ j : Fin 4, ∑ t : Fin 256, Ops.negCoef 256 (keyZ (Emulated.Rows.aKeyOf pk i j)) k t *
        program.intOf rd 60 ((j : ℕ) * 256 + t) -
      ∑ t : Fin 256, Ops.negCoef 256 (keyZ (Emulated.Rows.tKeyOf pk i)) k t * cInt rd t := by
  rw [sigN, evalIntWith_concat4 rd rowN (fun r _ => exprLen_rowN r) i.isLt hk]
  exact evalIntWith_rowN hS i hk

end Eval

/-! ## Soundness of the relation -/

section Sound

variable {program : RealizedProgram} [MldsaCarrierRelation program] {I : RealizedProgram.Interp}
  [MLDSA44.AField (I 0)]

/-- **A predicate the relation reads holds** where the source program holds. -/
theorem holds_rel {e : program.Env I} (hs : program.SourceSatAt e) {p : ℕ}
    (hp : p ∈ [3, 10, 14, 15]) : program.HoldsAt e (program.predicate p).body :=
  hs.preds _ (predicate_mem (MldsaCarrierRelation.inSource p hp).1)
    (MldsaCarrierRelation.inSource p hp).2

/-- **A range membership of one record** gives a natural below the bound. -/
theorem natBelow_of_mem {rd : program.Valuation I} {n : ℕ} {r : Expr} {real : InRealization}
    (h : program.HoldsWith rd (.mem 0 [r] (.range n) real)) {i : ℕ} (hi : i < program.exprLen r) :
    ∃ k < n, program.evalE rd 0 r i = k := by
  have hw : ∃ k < n, program.evalE rd (program.domainField 0) r i = k :=
    h i hi r (List.mem_singleton_self r)
  have h0 := MldsaCarrierRelation.domainField0 (program := program)
  revert hw
  generalize program.domainField 0 = D at h0 ⊢
  subst h0
  exact id

/-- **The integer reading of a bound value of field `0` whose element is a small integer's cast**
is the integer. -/
theorem intOf_of_boundInt {rd : program.Valuation I} {v i : ℕ}
    (hb : (program.value v).kind.isBound = true) (hf : program.valueField v = 0) {z : ℤ}
    (hz : 2 * |z| < pGold) (hv : program.evalE rd 0 (.leaf v) i = (z : (I 0).K)) :
    program.intOf rd v i = z := by
  obtain ⟨x, hx⟩ : ∃ x, (program.value v).kind = .bound x := by
    revert hb
    cases (program.value v).kind <;> simp [Kind.isBound]
  rw [intOf_of_bound _ hx]
  rw [evalE_leaf] at hv
  revert hv
  generalize rd v i = y
  generalize program.valueField v = a at hf y
  subst hf
  rw [castElt_self]
  intro hv
  rw [hv]
  exact coefInt_small hz

/-- **The integer reading of a committed value of field `0`** is its natural reading. -/
theorem intOf_of_priv (rd : program.Valuation I) {v i : ℕ} (hp : (program.value v).kind = .priv)
    (hf : program.valueField v = 0) :
    program.intOf rd v i = ((I 0).toNat (program.evalE rd 0 (.leaf v) i) : ℤ) := by
  unfold intOf
  rw [hp, evalE_leaf]
  simp only
  revert hf
  generalize rd v i = y
  generalize program.valueField v = a at y
  intro hf
  subst hf
  rw [castElt_self]

/-- **`signature.w` bounds `w′`** below `2^24`. -/
theorem w_range {e : program.Env I} (hs : program.SourceSatAt e) {i : ℕ} (hi : i < 1024) :
    ∃ n : ℕ, n < 16777216 ∧ program.evalE (program.reader e) 0 (.leaf 63) i = n := by
  have h := holds_rel hs (p := 14) (by simp)
  obtain ⟨_, hb⟩ := MldsaCarrierRelation.wRange (program := program)
  rw [hb] at h
  obtain ⟨n, hn, hv⟩ := natBelow_of_mem h
    (by rw [exprLen_leaf, MldsaCarrierRelation.size63]; exact hi)
  exact ⟨n, hn, hv⟩

/-- **`norm.z.offset`** reads `130993`. -/
theorem rd_offset (e : program.Env I) {i : ℕ} (hi : i < 1024) :
    program.evalE (program.reader e) 0 (.leaf 65) i = ((130993 : ℕ) : (I 0).K) := by
  obtain ⟨hc, hf, he⟩ := MldsaCarrierRelation.offset (program := program)
  rw [evalE_leaf_of_isConstant e hc, constRead_of_valueField hf, he, List.getD_eq_getElem?_getD,
    List.getElem?_replicate, if_pos hi, Option.getD_some, decode_lt0 (by norm_num [pGold])]

/-- **`norm.z` bounds `z`**: `z` is the cast of an integer in `[−130993, 130993]`. -/
theorem z_range {e : program.Env I} (hs : program.SourceSatAt e) {i : ℕ} (hi : i < 1024) :
    ∃ z : ℤ, -130993 ≤ z ∧ z ≤ 130993 ∧ program.evalE (program.reader e) 0 (.leaf 60) i = z := by
  have h := holds_rel hs (p := 15) (by simp)
  obtain ⟨_, hb⟩ := MldsaCarrierRelation.zRange (program := program)
  rw [hb] at h
  obtain ⟨n, hn, hv⟩ := natBelow_of_mem h
    (by rw [exprLen_add, exprLen_leaf, MldsaCarrierRelation.size60]; exact hi)
  rw [evalE_add, rd_offset e hi] at hv
  refine ⟨(n : ℤ) - 130993, by omega, by omega, ?_⟩
  push_cast
  rw [← hv]
  push_cast
  ring

/-- **`w′`'s integer reading is a natural below `2^24`** and the integer of its element. -/
theorem intOf_w {e : program.Env I} (hs : program.SourceSatAt e) (i : Fin 4) (k : Fin 256) :
    program.intOf (program.reader e) 63 ((i : ℕ) * 256 + k) = wv (program.reader e) i k ∧
      program.intOf (program.reader e) 63 ((i : ℕ) * 256 + k) =
        (I 0).coefInt (wVals (program.reader e) i k) := by
  obtain ⟨n, hn, hv⟩ := w_range hs (show (i : ℕ) * 256 + k < 1024 by omega)
  have hsmall : 2 * |(n : ℤ)| < pGold := by
    rw [abs_of_nonneg (by positivity)]
    norm_num [pGold]
    omega
  have h : program.intOf (program.reader e) 63 ((i : ℕ) * 256 + k) = n :=
    intOf_of_boundInt MldsaCarrierRelation.kind63 MldsaCarrierRelation.field63 hsmall
      (by rw [hv]; simp)
  refine ⟨by rw [wv, h]; simp, ?_⟩
  unfold wVals
  rw [h, hv, show ((n : ℕ) : (I 0).K) = ((n : ℤ) : (I 0).K) from (Int.cast_natCast n).symm,
    coefInt_small hsmall]

/-- **`z`'s integer reading is its shifted natural less the shift** and the integer of its
element. -/
theorem intOf_z {e : program.Env I} (hs : program.SourceSatAt e) (j : Fin 4) (m : Fin 256) :
    program.intOf (program.reader e) 60 ((j : ℕ) * 256 + m) =
        Emulated.Rows.signedZ (zv (program.reader e)) j m ∧
      program.intOf (program.reader e) 60 ((j : ℕ) * 256 + m) =
        (I 0).coefInt (zVals (program.reader e) j m) := by
  obtain ⟨z, hlo, hhi, hv⟩ := z_range hs (show (j : ℕ) * 256 + m < 1024 by omega)
  have hsmall : 2 * |z| < pGold := by
    have ha : |z| ≤ 130993 := abs_le.mpr ⟨hlo, hhi⟩
    have hp : ((pGold : ℕ) : ℤ) = 18446744069414584321 := by norm_num [pGold]
    rw [hp]
    linarith
  have h : program.intOf (program.reader e) 60 ((j : ℕ) * 256 + m) = z :=
    intOf_of_boundInt MldsaCarrierRelation.kind60 MldsaCarrierRelation.field60 hsmall hv
  refine ⟨?_, ?_⟩
  · have hsh : ((mldsa44.normBound - 1 : ℕ) : ℤ) = 130993 := by decide
    simp only [Emulated.Rows.signedZ, Emulated.Rows.shift, zv, h, hsh]
    omega
  · unfold zVals
    rw [h, hv, coefInt_small hsmall]

/-- **The relation's sides differ by a multiple of `q`** where the source program holds
(`signature.relation`, the congruence of the `mod_q`). -/
theorem sig_dvd {e : program.Env I} (hs : program.SourceSatAt e) {i k : ℕ} (hi : i < 4)
    (hk : k < 256) :
    (8380417 : ℤ) ∣ program.evalIntWith (program.reader e) 0 sigP (i * 256 + k) -
      program.evalIntWith (program.reader e) 0 sigN (i * 256 + k) := by
  obtain ⟨real, hb, -⟩ := MldsaCarrierRelation.sig (program := program)
  have h := holds_rel hs (p := 3) (by simp)
  rw [hb] at h
  exact_mod_cast h.1 _ (by rw [exprLen_sigP]; omega)

/-- **The congruence of an ML-DSA ring carrier** (`Rows.Congruent` at the keys of `pk`):
`w′ ≡ Σ_j A_ij z_j − c t_i (mod q)` with `c = support − 2 · sign` and `t_i = 2^d t1_i`, where the
source program holds, at a key whose transforms the committed spectra hold. -/
theorem congruent_carrier {e : program.Env I} (hs : program.SourceSatAt e)
    {pk : Native.Rows.PublicKey} (hS : SpectraOf pk (program.reader e)) :
    Emulated.Rows.Congruent (Emulated.Rows.aKeyOf pk) (Emulated.Rows.tKeyOf pk)
      (zv (program.reader e)) (wv (program.reader e)) (fun m => cInt (program.reader e) m) :=
  fun i k => by
  have hd := sig_dvd hs i.isLt k.isLt
  rw [evalIntWith_sigP _ i.isLt k.isLt, evalIntWith_sigN hS i k.isLt] at hd
  have h0 : ((program.intOf (program.reader e) 63 ((i : ℕ) * 256 + k) -
      (∑ j : Fin 4, ∑ t : Fin 256, Ops.negCoef 256 (keyZ (Emulated.Rows.aKeyOf pk i j)) k t *
        program.intOf (program.reader e) 60 ((j : ℕ) * 256 + t) -
      ∑ t : Fin 256, Ops.negCoef 256 (keyZ (Emulated.Rows.tKeyOf pk i)) k t *
        cInt (program.reader e) t) : ℤ) : _root_.MLDSA.Coeff) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hd
  have hA : ∀ j : Fin 4,
      ((∑ t : Fin 256, Ops.negCoef 256 (keyZ (Emulated.Rows.aKeyOf pk i j)) k t *
        program.intOf (program.reader e) 60 ((j : ℕ) * 256 + t) : ℤ) : _root_.MLDSA.Coeff) =
      LatticeCrypto.negacyclicConvCoeff
        (fun m : Fin 256 => ((Emulated.Rows.aKeyOf pk i j m : ℕ) : _root_.MLDSA.Coeff))
        (fun m => ((Emulated.Rows.signedZ (zv (program.reader e)) j m : ℤ) : _root_.MLDSA.Coeff))
        k := by
    intro j
    refine (cast_sum_negCoef (keyZ (Emulated.Rows.aKeyOf pk i j))
      (fun t => program.intOf (program.reader e) 60 ((j : ℕ) * 256 + t)) k.isLt).trans ?_
    congr 1
    · funext m
      simp only [keyZ, dif_pos (show (m : ℕ) < 256 from m.isLt), Int.cast_natCast]
      rfl
    · funext m
      rw [(intOf_z hs j m).1]
  have hT : ((∑ t : Fin 256, Ops.negCoef 256 (keyZ (Emulated.Rows.tKeyOf pk i)) k t *
        cInt (program.reader e) t : ℤ) : _root_.MLDSA.Coeff) =
      LatticeCrypto.negacyclicConvCoeff
        (fun m : Fin 256 => ((cInt (program.reader e) m : ℤ) : _root_.MLDSA.Coeff))
        (fun m => ((Emulated.Rows.tKeyOf pk i m : ℕ) : _root_.MLDSA.Coeff)) k := by
    refine (cast_sum_negCoef (keyZ (Emulated.Rows.tKeyOf pk i))
      (fun t => cInt (program.reader e) t) k.isLt).trans ?_
    rw [Falcon512.negacyclicConvCoeff_comm]
    congr 1
    funext m
    simp only [keyZ, dif_pos (show (m : ℕ) < 256 from m.isLt), Int.cast_natCast]
    rfl
  have hW : ((program.intOf (program.reader e) 63 ((i : ℕ) * 256 + k) : ℤ) : _root_.MLDSA.Coeff) =
      ((wv (program.reader e) i k : ℕ) : _root_.MLDSA.Coeff) := by
    rw [(intOf_w hs i k).1, Int.cast_natCast]
  rw [Int.cast_sub, Int.cast_sub, Int.cast_sum, hW, hT] at h0
  simp only [hA] at h0
  show ((wv (program.reader e) i k : ℕ) : _root_.MLDSA.Coeff) = _
  exact sub_eq_zero.mp h0

/-- **The challenge bits are Boolean** where the source program holds. -/
theorem cBit_bool {e : program.Env I} (hs : program.SourceSatAt e) {i : ℕ} (hi : i < 512) :
    program.evalE (program.reader e) 0 (.leaf 62) i = 0 ∨
      program.evalE (program.reader e) 0 (.leaf 62) i = 1 := by
  have h := bool_of_boolCheck MldsaCarrierRelation.cBool (holds_rel hs (p := 10) (by simp))
    (i := i) (by rw [MldsaCarrierRelation.size62]; exact hi)
  rw [MldsaCarrierRelation.domainField0] at h
  exact h

/-- **A Boolean element of field `0` as a coefficient** is its integer reading. -/
theorem bitCoeff_eq_toNat {v : (I 0).K} (hv : v = 0 ∨ v = 1) :
    Native.Rows.bitCoeff v = ((I 0).toNat v : _root_.MLDSA.Coeff) := by
  rcases hv with rfl | rfl
  · rw [show (0 : (I 0).K) = ((0 : ℕ) : (I 0).K) from Nat.cast_zero.symm,
      toNat_lt0 (by norm_num [pGold])]
    unfold Native.Rows.bitCoeff
    simp
  · rw [show (1 : (I 0).K) = ((1 : ℕ) : (I 0).K) from Nat.cast_one.symm,
      toNat_lt0 (by norm_num [pGold])]
    unfold Native.Rows.bitCoeff
    simp

/-- **The challenge polynomial's coefficients** are `support − 2 · sign` of the challenge bits'
integer readings. -/
theorem coeff_cPoly {e : program.Env I} (hs : program.SourceSatAt e) :
    MLDSA44.coeff (cPoly (program.reader e)) = fun k : Fin _root_.MLDSA.ringDegree =>
      ((cInt (program.reader e) k : ℤ) : _root_.MLDSA.Coeff) := by
  funext k
  have hk : (k : ℕ) < 256 := k.isLt
  rw [cPoly, MLDSA44.coeff_ofCoeff, cInt,
    intOf_of_priv _ MldsaCarrierRelation.kind62 MldsaCarrierRelation.field62,
    intOf_of_priv _ MldsaCarrierRelation.kind62 MldsaCarrierRelation.field62]
  have h0 : cBits (program.reader e) k 0 = program.evalE (program.reader e) 0 (.leaf 62) (2 * k) :=
    by simp [cBits]
  have h1 : cBits (program.reader e) k 1 =
      program.evalE (program.reader e) 0 (.leaf 62) (2 * k + 1) := by simp [cBits]
  rw [h0, h1, bitCoeff_eq_toNat (cBit_bool hs (by omega)),
    bitCoeff_eq_toNat (cBit_bool hs (by omega))]
  push_cast
  rfl

/-- **The extracted `z` is the shifted naturals' `z`** (`Rows.zVec`). -/
theorem zOf_eq {e : program.Env I} (hs : program.SourceSatAt e) :
    zOf (program.reader e) = Emulated.Rows.zVec (zv (program.reader e)) := by
  apply Vector.ext
  intro j hj
  unfold zOf Emulated.Rows.zVec
  rw [Vector.getElem_ofFn, Vector.getElem_ofFn]
  refine congrArg MLDSA44.ofCoeff (funext fun m => ?_)
  exact congrArg (Int.cast : ℤ → _root_.MLDSA.Coeff)
    ((intOf_z hs ⟨j, hj⟩ m).2.symm.trans (intOf_z hs ⟨j, hj⟩ m).1)

/-- **`w′ = computeWApprox(Â, c, z, t1)`** for an ML-DSA ring carrier, where the source program
holds, at a key whose transforms the committed spectra hold (`congruent_carrier`,
`Rows.Congruent.computeWApprox`): the emulated proof of possession's `algebra` at the ring's
readings. -/
theorem algebra_carrier {e : program.Env I} (hs : program.SourceSatAt e)
    {pk : Native.Rows.PublicKey} (hS : SpectraOf pk (program.reader e)) :
    wOf (program.reader e) = _root_.MLDSA.computeWApprox _root_.MLDSA.mldsa44 Native.Rows.prims
      (nttOps := _root_.MLDSA.Concrete.concreteNTTRingOps) (Native.Rows.aHat pk)
      (cPoly (program.reader e)) (zOf (program.reader e)) pk.t1 := by
  have hcong := congruent_carrier hs hS
  apply Vector.ext
  intro i hi
  have key : (wOf (program.reader e)).get ⟨i, hi⟩ = (_root_.MLDSA.computeWApprox
      _root_.MLDSA.mldsa44 Native.Rows.prims (nttOps := _root_.MLDSA.Concrete.concreteNTTRingOps)
      (Native.Rows.aHat pk) (cPoly (program.reader e)) (zOf (program.reader e)) pk.t1).get
        ⟨i, hi⟩ := by
    rw [← MLDSA44.ofCoeff_coeff (Vector.get (_root_.MLDSA.computeWApprox _root_.MLDSA.mldsa44
      Native.Rows.prims (nttOps := _root_.MLDSA.Concrete.concreteNTTRingOps)
      (Native.Rows.aHat pk) (cPoly (program.reader e)) (zOf (program.reader e)) pk.t1)
        ⟨i, hi⟩)]
    unfold wOf
    rw [Vector.get_ofFn]
    refine congrArg MLDSA44.ofCoeff (funext fun k => ?_)
    rw [MLDSA44.coeff_computeWApprox, coeff_cPoly hs, zOf_eq hs]
    have h := congrArg (Int.cast : ℤ → _root_.MLDSA.Coeff)
      ((intOf_w hs ⟨i, hi⟩ k).2.symm.trans (intOf_w hs ⟨i, hi⟩ k).1)
    rw [Int.cast_natCast] at h
    exact h.trans (hcong.computeWApprox ⟨i, hi⟩ k)
  simpa [Vector.get_eq_getElem] using key

end Sound

end GordieHowe.MLDSA44.Ring.Carrier
