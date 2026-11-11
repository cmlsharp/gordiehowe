-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Falcon512.Frontend.Norm
public import GordieHowe.Applications.Falcon512.Ring.Native.System.Composite
public import GordieHowe.Language.Library.TableSelect
public import GordieHowe.Language.Library.EvalPoint

@[expose] public section

/-!
# GordieHowe frontend: the native Falcon ring, the relation and the extractor

The frontend of the theorem at the realized program for the native Falcon rings (`Falcon512.Ring.Native.ROMParams` and
`Falcon512.Ring.Native.QROMParams`, export `b65a4929`), generic in the program and its interpretation at the
program facts `FalconRingPowers`, `FalconRingSelect`, `FalconRingMember` and `FalconRingBase`
(decided per program):

* **The table's selection** (`FalconRingPowers`, `FalconRingSelect`): `member.signer` is the
  generic selection of a public table's row (`GordieHowe.RealizedProgram.TableSelect`,
  `GordieHowe/Language/Library/TableSelect.lean`) at the record `key.spectrum`, the rows
  `statement.ring` (`64` keys of `512` coefficients) and the row map the natural-order transform of
  length `512` at `ψ`, whose power indices are the identity.
* **The membership** (`evalE_memberLhs`, `member_eq`, `ringEvent`, `ringEvent_bound`,
  `spec_eq_of_not_event`): the committed spectrum's fingerprint `Σ_k spectrum_k γ^k` is the
  signer's key's (`GordieHowe.RealizedProgram.TableSelect.evalE_lhs`); unless `γ` is a root of the
  nonzero difference polynomial (degree at most `511`, probability `511/|F|`, Schwartz–Zippel),
  the spectrum is the transform of the signer's key.
* **The signature equation at a random point** (`FalconRandomPoint`, `FalconRandomPointField`,
  `sigPoly`, `sigEvent`, `evalE_sigLhs`, `holdsAt_sig_iff`, `sig_spectral`, `eOf_eq_negacyclic`),
  shared by the native rings and the carriers (`GordieHowe/Applications/Falcon512/Ring/Carrier/Frontend.lean`):
  the program checks `E = h · s2` in `F[X]/(X^512 + 1)` at one challenge `r` (`signature.r`) with a
  committed high half `Q` by `X^512 + 1`, the key read through the interpolation weights
  `λ(r) = 512⁻¹ Ntt_{ψ⁻¹}(1, r, …, r^511)` (`GordieHowe/Language/Library/EvalPoint.lean`). The
  predicate is the polynomial `E − H · s2 + (X^512 + 1) Q` at `r` (`H` the interpolation of the
  spectrum); unless `r` is a root of it while it is nonzero (degree at most `1022`,
  Schwartz–Zippel), it is `0`, so at the roots of `X^512 + 1` it reads
  `Ntt(E) = spectrum ⊙ Ntt(s2)`, and coefficientwise `E` is the negacyclic product `H · s2`.
  The native rings' first vector is `E = c − s1` (`FalconRingBase`, `eOf_eq`, `sig_eq`).
* **The relation and the extractor** (`rel`, `proj`, `extractor`): the signer's position is below
  `64` and, at its key (`ringKey`) and the statement's challenge (`chalNat`), Falcon's algebraic
  verifier accepts the extracted `s2` and `s2` is encodable; `proj` reads the index bits and the
  centred `s2`. `mem_rel_of_source`: the spectral equation is `c − s1 = h · s2` over the field, its
  projection onto the prime field (`primeProj`) the ring algebra at the signer's key, and
  `GordieHowe.Falcon512.Ring.Native.ringAlgebra_sound` gives the relation, given the norm's advice (`NormSound`,
  discharged per program by the generic norm `FalconNorm`).
* **Round-by-round knowledge soundness of `Π_P₀`** (`rbr_of_norm`): `GordieHowe.RealizedProgram.rbr_of_events` at the
  membership's and the signature equation's events (`nativeEvent`), errors `511/|F|` at
  `member.ring.gamma` and `1022/|F|` at `signature.r` (`nativeEps`).
-/

namespace GordieHowe.Falcon512.Ring

open GordieHowe.Bits IOP
open scoped NNReal ENNReal

/-! ## The table's selection -/

/-- **The Falcon ring's table selection** (`member.signer`, `lib/gordiehowe/lib/table.h`'s
`select_row`; decided per program): the generic `GordieHowe.RealizedProgram.TableSelect`, whose
theorems read the powers, the digests and the multiplexer fold. -/
class FalconRingPowers (program : RealizedProgram) extends RealizedProgram.TableSelect program

/-- **The Falcon ring selection's identifiers** (decided per program): domain `0`, predicate `0`
(`member.signer`), `6` index bits, `64` rows, challenge `0` (`member.ring.gamma`). -/
class FalconRingSelect (program : RealizedProgram) [FalconRingPowers program] : Prop where
  /-- The identifiers. -/
  ids : (RealizedProgram.TableSelect.shape program).dom = 0 ∧
    (RealizedProgram.TableSelect.shape program).pred = 0 ∧
    (RealizedProgram.TableSelect.shape program).bits = 6 ∧
    (RealizedProgram.TableSelect.shape program).rows = 64 ∧
    (RealizedProgram.TableSelect.shape program).chal = 0

/-- **The index bits** (`member.signer.index`). -/
abbrev FalconRingSelect.idx (program : RealizedProgram) [FalconRingPowers program] : ℕ :=
  (RealizedProgram.TableSelect.shape program).idx

/-- **The low bits of an index**: `Σ_{i ≤ t} b_i 2^i`. -/
def lowBits (b : ℕ → ℕ) (t : ℕ) : ℕ := ∑ i ∈ Finset.range (t + 1), b i * 2 ^ i

theorem lowBits_succ (b : ℕ → ℕ) (t : ℕ) :
    lowBits b (t + 1) = lowBits b t + b (t + 1) * 2 ^ (t + 1) := by
  unfold lowBits
  rw [Finset.sum_range_succ]

theorem lowBits_lt {b : ℕ → ℕ} (hb : ∀ i, b i ≤ 1) : ∀ t, lowBits b t < 2 ^ (t + 1)
  | 0 => by simp [lowBits]; have := hb 0; omega
  | t + 1 => by
    rw [lowBits_succ, pow_succ 2 (t + 1)]
    have := lowBits_lt hb t
    have := hb (t + 1)
    nlinarith

/-! ## The membership -/

/-- **The membership's left side** (`member.signer`): `Σ_k spectrum_k γ^k` less the digest the
index bits select, at the spectrum `spec`, the powers `pow`, the index bits `idx` and the constant
`−1` (`mOne`). -/
def memberLhs (spec pow idx mOne : ℕ) : RealizedProgram.Expr :=
  .add (.apply (.sum 512) (.mul (.reindex [(0, 1, 512)] (.reindex [(0, 1, 512)] (.leaf spec)))
    (.reindex [(0, 1, 512)] (.leaf pow))))
    (.scale (.const mOne) (.mux (.reindex [(5, 0, 1)] (.leaf idx)) (.reindex [(1, 0, 1)] (.ref 20))
      (.reindex [(0, 0, 1)] (.ref 20))))

/-- **The signature equation's left side** (`signature.equation`) of a Falcon ring, one
coordinate: `Σ_t E_t r^t − (Σ_m spectrum_m λ_m) (Σ_t s2_t r^t) + (r^512 + 1) Σ_t Q_t r^t`, at the
equation's first vector `E` (the native rings' `c − s1`, the carriers'
`c − s1 − q · equation.q + q · 6291457`), the spectrum `spec`, `s2`, the high half `q`, the powers
`r^t` (`pw`), the weights `λ = 512⁻¹ Ntt_{ψ⁻¹}(1, r, …, r^511)` (`lam`), `r^512 + 1` (`rn`) and the
field's `−1` (`mOne`). -/
def sigLhs (E : RealizedProgram.Expr) (spec s2 q pw lam rn mOne : ℕ) : RealizedProgram.Expr :=
  .add (.add (.apply (.sum 512) (.mul E (.leaf pw)))
      (.scale (.const mOne) (.mul (.apply (.sum 512) (.mul (.leaf spec) (.leaf lam)))
        (.apply (.sum 512) (.mul (.leaf s2) (.leaf pw))))))
    (.mul (.leaf rn) (.apply (.sum 511) (.mul (.leaf q) (.reindex [(0, 1, 511)] (.leaf pw)))))

/-- **The field facts the membership reads** in a field interpretation: the constant `negOne`
decodes to `−1`, `0` and `1` decode to themselves and read back as `0` and `1`. -/
class RingField (FA : RealizedProgram.FieldInterp) (negOne : ℕ) : Prop where
  /-- `negOne` decodes to `−1`. -/
  decode_negOne : FA.decode negOne = -1
  /-- `0` decodes to `0`. -/
  decode_zero : FA.decode 0 = 0
  /-- `1` decodes to `1`. -/
  decode_one : FA.decode 1 = 1
  /-- `0` reads as `0`. -/
  toNat_zero : FA.toNat 0 = 0
  /-- `1` reads as `1`. -/
  toNat_one : FA.toNat 1 = 1

/-- **A ring field is a selection's field** (`GordieHowe.RealizedProgram.SelectField`). -/
instance (FA : RealizedProgram.FieldInterp) (n : ℕ) [RingField FA n] :
    RealizedProgram.SelectField FA n where
  decode_negOne := RingField.decode_negOne
  decode_zero := RingField.decode_zero (negOne := n)
  decode_one := RingField.decode_one (negOne := n)
  toNat_zero := RingField.toNat_zero (negOne := n)
  toNat_one := RingField.toNat_one (negOne := n)

/-- **A native Falcon field** (`F_q^k`): `q − 1 = 12288` is `−1`. -/
instance (FA : RealizedProgram.FieldInterp) [AField FA] : RingField FA 12288 where
  decode_negOne := by
    rw [AField.decode_lt _ (by norm_num)]
    have h0 : ((12289 : ℕ) : FA.K) = 0 := CharP.cast_eq_zero _ 12289
    push_cast at h0 ⊢
    linear_combination h0
  decode_zero := by rw [AField.decode_lt _ (by norm_num), Nat.cast_zero]
  decode_one := by rw [AField.decode_lt _ (by norm_num), Nat.cast_one]
  toNat_zero := AField.toNat_zero
  toNat_one := AField.toNat_one

/-- **The program facts of a Falcon ring's membership** (decided per program; the native rings and
the carrier rings number their values differently): domain `0` of field `0`; the ring
(`statement.ring`, `ring`), the spectrum (`spec`), the powers (`pow`), the zero constant (`zero`),
the transform root (`psi`) and the constant `−1` (`mOne`) of the field; the membership
`member.signer` (predicate `0`) and the index bits' type check (`idxPred`), source predicates; the
table selection's record, rows and row map; the kinds, fields and sizes of the values read; the
challenge `γ`. -/
class FalconRingMember (program : RealizedProgram) [FalconRingPowers program] [FalconRingSelect program]
    where
  /-- `statement.ring`. -/
  ring : ℕ
  /-- `key.spectrum`. -/
  spec : ℕ
  /-- `member.ring.powers`. -/
  pow : ℕ
  /-- The zero constant of one coordinate. -/
  zero : ℕ
  /-- The transform root. -/
  psi : ℕ
  /-- The constant `−1` of the field. -/
  mOne : ℕ
  /-- `member.signer.index.boolean`. -/
  idxPred : ℕ
  /-- `statement.c`. -/
  chal : ℕ
  /-- `s2`. -/
  s2 : ℕ
  /-- Domain `0` has field `0`. -/
  domainField0 : program.domainField 0 = 0
  /-- `member.signer`: `Σ_k spectrum_k γ^k` is the selected digest. -/
  member : ∃ t, (program.predicate 0).body =
    .equal 0 (memberLhs spec pow (FalconRingSelect.idx program) mOne) (.leaf zero) t
  /-- `member.signer.index.boolean`. -/
  idxBool : ∃ t, (program.predicate idxPred).body = .equal 0
    (.mul (.leaf (FalconRingSelect.idx program)) (.leaf (FalconRingSelect.idx program)))
    (.leaf (FalconRingSelect.idx program)) t
  /-- The two predicates are source predicates. -/
  inSource : ∀ p ∈ [0, idxPred],
    p < program.predicates.length ∧ program.inSource (program.predicate p) = true
  /-- The zero constant. -/
  consts : program.isConstant zero = true ∧ (program.constEntries zero).getD 0 0 = 0
  /-- The table selection's identifiers: the record is the spectrum, the rows the ring, the row
  map the natural-order transform of length `512` at `ψ`. -/
  table : (RealizedProgram.TableSelect.shape program).record = .leaf spec ∧
    (RealizedProgram.TableSelect.shape program).parts = [(ring, 512)] ∧
    (RealizedProgram.TableSelect.shape program).map = [⟨true, true, 512, 0, psi⟩] ∧
    (RealizedProgram.TableSelect.shape program).zero = zero ∧
    (RealizedProgram.TableSelect.shape program).mOne = mOne ∧
    (RealizedProgram.TableSelect.shape program).idxPred = idxPred ∧
    (RealizedProgram.TableSelect.shape program).pow = pow
  /-- The ring is an opaque statement value with no arguments. -/
  ringKind : (program.value ring).kind = .pub (.opaque "statement.ring" [])
  /-- The challenge is an opaque statement value with no arguments. -/
  chalKind : (program.value chal).kind = .pub (.opaque "statement.c" [])
  /-- The challenge and the ring are distinct values. -/
  chal_ne_ring : chal ≠ ring
  /-- The values read are of field `0`. -/
  fields : ∀ v ∈ [(RealizedProgram.TableSelect.shape program).one, zero, ring, spec,
    FalconRingSelect.idx program, (RealizedProgram.TableSelect.shape program).gamma, pow,
    (RealizedProgram.TableSelect.shape program).dig, chal, s2],
    program.valueField v = 0
  /-- The sizes of the values read. -/
  sizes : (program.value (FalconRingSelect.idx program)).size = 6 ∧
    (program.value spec).size = 512 ∧ (program.value ring).size = 32768 ∧
    (program.value chal).size = 512 ∧ (program.value s2).size = 512
  /-- Challenge `0` is one full coordinate of field `0`. -/
  chal0 : (program.challenge 0).size = 1 ∧ (program.challenge 0).sampler = .full ∧
    program.chalField 0 = 0
  /-- `member.ring.gamma` is a challenge of the source program (the native rings also draw the
  signature equation's `signature.r`). -/
  isSourceChal_zero : program.IsSourceChal 0
  /-- The program has values. -/
  values_length : 0 < program.values.length
  /-- The spectrum, the index bits and `s2` are committed. -/
  privKinds : (program.value spec).kind = .priv ∧
    (program.value (FalconRingSelect.idx program)).kind = .priv ∧ (program.value s2).kind = .priv

/-- **The program facts of a Falcon ring's signature equation at a random point** (decided per
program; the native rings and the carriers number their values differently, and both extend
them, `FalconRingBase`, `FalconCarrierBase`): the equation's first vector `sigE` (`512`
coordinates, headed by `statement.c`), the high half `signature.Q` (`q`), `signature.r` and its
challenge, the constants `1` and `0`, the public values `r^t` (`pw`), `λ` (`lam`) and `r^512 + 1`
(`rn`), the shared expressions of `r^t` and `r^256`; the predicate `signature.equation`, a source
predicate; the program's `512⁻¹` and `ψ⁻¹` (`nInv`, `psiInv`, read in a field by
`FalconRandomPointField`); the challenge `signature.r`, a source challenge of one full coordinate;
the public values' definitions and the powers the symbolic-power matcher reads; the fields and
kinds of the values read. -/
class FalconRandomPoint (program : RealizedProgram) [FalconRingPowers program]
    [FalconRingSelect program] [FalconRingMember program] where
  /-- The equation's first vector `E`. -/
  sigE : RealizedProgram.Expr
  /-- `signature.Q`, the high half of the product by `X^512 + 1`. -/
  q : ℕ
  /-- `signature.r`. -/
  r : ℕ
  /-- `signature.r`'s challenge. -/
  rChal : ℕ
  /-- The constant `1` (one coordinate). -/
  one : ℕ
  /-- The constant `0` (one coordinate). -/
  zero1 : ℕ
  /-- `r^t`, `t < 512` (`signature.equation.public0`). -/
  pw : ℕ
  /-- `λ = 512⁻¹ Ntt_{ψ⁻¹}(1, r, …, r^511)` (`signature.lambda`). -/
  lam : ℕ
  /-- `r^512 + 1` (`signature.equation.public1`). -/
  rn : ℕ
  /-- The shared expression of `r^t`. -/
  pwRef : ℕ
  /-- The shared expression of `r^256`. -/
  r256Ref : ℕ
  /-- `signature.equation`. -/
  sigPred : ℕ
  /-- The constant `512⁻¹`. -/
  nInv : ℕ
  /-- The constant `ψ⁻¹`. -/
  psiInv : ℕ
  /-- `signature.equation`: the signature equation at `r`. -/
  sig : ∃ t, (program.predicate sigPred).body = .equal 0
    (sigLhs sigE (FalconRingMember.spec program) (FalconRingMember.s2 program) q pw lam rn
      (FalconRingMember.mOne program)) (.leaf zero1) t
  /-- The first vector has the length of `statement.c`. -/
  sigELen : program.exprLen sigE = program.exprLen (.leaf (FalconRingMember.chal program))
  /-- The signature equation is a source predicate. -/
  inSourceSig : sigPred < program.predicates.length ∧
    program.inSource (program.predicate sigPred) = true
  /-- The zero constant. -/
  const0 : program.isConstant zero1 = true ∧ program.constEntries zero1 = [0]
  /-- The values read are of field `0`. -/
  sigFields : ∀ v ∈ [zero1, q, pw, lam, rn], program.valueField v = 0
  /-- `Q` is committed. -/
  qPriv : (program.value q).kind = .priv
  /-- `signature.r` and the constant `1`. -/
  rPow : RealizedProgram.ChalPowers program one r rChal 0
  /-- `signature.r` is one coordinate drawn from the field. -/
  chalR : (program.challenge rChal).size = 1 ∧ (program.challenge rChal).sampler = .full
  /-- The source program's challenges are `member.ring.gamma` (`0`) and `signature.r`. -/
  isSourceChal_iff : ∀ j, program.IsSourceChal j ↔ j = 0 ∨ j = rChal
  /-- The two challenges are distinct. -/
  rChal_ne : rChal ≠ 0
  /-- `r^t`'s definition. -/
  pwKind : (program.value pw).kind = .pub (.expr (.ref pwRef))
  /-- `λ`'s definition. -/
  lamKind : (program.value lam).kind =
    .pub (.expr (.scale (.const nInv) (.apply (.ntt 512 psiInv .natural) (.ref pwRef))))
  /-- `r^512 + 1`'s definition. -/
  rnKind : (program.value rn).kind =
    .pub (.expr (.add (.mul (.ref r256Ref) (.ref r256Ref)) (.leaf one)))
  /-- Shared expressions refer only to earlier ones. -/
  refsOrdered : program.RefsOrdered
  /-- The program has shared expressions. -/
  exprs_pos : 0 < program.exprs.length
  /-- `r^t`, `t < 512`, by the symbolic-power matcher. -/
  powPw : program.powSym ⟨RealizedProgram.onePub one r, none⟩ RealizedProgram.powFuel (.ref pwRef) =
    some (List.range 512)
  /-- `r^256`. -/
  pow256 : program.powSym ⟨RealizedProgram.onePub one r, none⟩ RealizedProgram.powFuel
    (.ref r256Ref) = some [256]

/-- **The signature equation's left side** of a program (`signature.equation`). -/
abbrev FalconRandomPoint.lhs (program : RealizedProgram) [FalconRingPowers program]
    [FalconRingSelect program] [FalconRingMember program] [FalconRandomPoint program] :
    RealizedProgram.Expr :=
  sigLhs (FalconRandomPoint.sigE program) (FalconRingMember.spec program)
    (FalconRingMember.s2 program) (FalconRandomPoint.q program) (FalconRandomPoint.pw program)
    (FalconRandomPoint.lam program) (FalconRandomPoint.rn program) (FalconRingMember.mOne program)

/-- **The field facts of the signature equation at a random point** in a field interpretation:
the membership's (`RingField` at the program's `−1`), the program's `512⁻¹` and `ψ⁻¹` decoding to
the inverses of `512` and of the transform root `ψ`, which is a primitive `1024`-th root of unity,
and `512 ≠ 0`. The native rings (characteristic `q`, `ψ = 10302`) and the carriers
(characteristic `p`, `ψ = psiG`) each give them. -/
class FalconRandomPointField (program : RealizedProgram) [FalconRingPowers program]
    [FalconRingSelect program] [FalconRingMember program] [FalconRandomPoint program]
    (F : RealizedProgram.FieldInterp) : Prop extends RingField F (FalconRingMember.mOne program) where
  /-- The constant `512⁻¹`. -/
  decode_nInv : F.decode (FalconRandomPoint.nInv program) = ((512 : ℕ) : F.K)⁻¹
  /-- The constant `ψ⁻¹`. -/
  decode_psiInv : F.decode (FalconRandomPoint.psiInv program) =
    (F.decode (FalconRingMember.psi program))⁻¹
  /-- `ψ` is a primitive `1024`-th root of unity. -/
  psi_isPrimitiveRoot : IsPrimitiveRoot (F.decode (FalconRingMember.psi program)) (2 * 512)
  /-- `512` is invertible. -/
  n_ne_zero : ((512 : ℕ) : F.K) ≠ 0

/-- **The program facts of a native Falcon ring outside the membership** (decided per program):
the signature equation's at a random point (`FalconRandomPoint`) with the first vector
`E = c − s1` (`sigE_eq`, at `signature.s1`), the native transform data (`consts`, `invConsts`:
`−1 = 12288`, `ψ = 10302`, `512⁻¹ = 12265`, `ψ⁻¹ = 8974` in `F_q`); the field, sizes, types and
kinds of `signature.s1` and the sizes of the equation's values. -/
class FalconRingBase (program : RealizedProgram) [FalconRingPowers program] [FalconRingSelect program]
    [FalconRingMember program] extends FalconRandomPoint program where
  /-- `signature.s1`. -/
  s1 : ℕ
  /-- The transform root and `−1`. -/
  consts : FalconRingMember.mOne program = 12288 ∧ FalconRingMember.psi program = 10302
  /-- `512⁻¹` and `ψ⁻¹`. -/
  invConsts : nInv = 12265 ∧ psiInv = 8974
  /-- The first vector is `c − s1` (`12288 = −1`). -/
  sigE_eq : sigE = .add (.leaf (FalconRingMember.chal program)) (.scale (.const 12288) (.leaf s1))
  /-- `signature.s1` is of field `0`. -/
  s1Field : program.valueField s1 = 0
  /-- The sizes of the values read. -/
  sizes : (program.value s1).size = 512 ∧ (program.value q).size = 511 ∧
    (program.value pw).size = 512 ∧ (program.value lam).size = 512 ∧
    (program.value rn).size = 1 ∧ (program.value zero1).size = 1
  /-- `s2` and `signature.s1` are prime-typed source values. -/
  primeVals : ∀ v ∈ [FalconRingMember.s2 program, s1], v < program.values.length ∧
    program.IsSourceValue v ∧ (program.value v).typeSource = .node ∧
    (program.value v).type = .sub "GF(p^1)"
  /-- `s1` is committed. -/
  s1Priv : (program.value s1).kind = .priv

section Member

variable {program : RealizedProgram} [FalconRingPowers program] [FalconRingSelect program]
  [FalconRingMember program] {I : RealizedProgram.Interp}

set_option hygiene false in
local notation "vIdx" => FalconRingSelect.idx program

/-- The program has a value. -/
theorem values_length_succ : ∃ n, program.values.length = n + 1 :=
  ⟨program.values.length - 1, by
    have := FalconRingMember.values_length (program := program)
    omega⟩

/-- **The challenge** `γ` read in field `0`. -/
def gammaOf (e : program.Env I) : (I 0).K := RealizedProgram.castElt (e.chal 0 0)

/-- **Entry `s` of the ring** (`statement.ring`) of a statement, read in field `0`. -/
def ringEntry (x : program.Valuation I) (s : ℕ) : (I 0).K :=
  RealizedProgram.castElt (x (FalconRingMember.ring program) s)

/-- **The committed spectrum** (`key.spectrum`). -/
def specOf (e : program.Env I) (t : ℕ) : (I 0).K :=
  program.evalE (program.reader e) 0 (.leaf (FalconRingMember.spec program)) t

/-- **A field `equal` of domain `0` holds coordinatewise in field `0`.** -/
theorem holdsAt_equal0 {e : program.Env I} {lhs rhs : RealizedProgram.Expr} {t : RealizedProgram.Target}
    (h : program.HoldsAt e (.equal 0 lhs rhs t)) :
    ∀ i < program.exprLen lhs,
      program.evalE (program.reader e) 0 lhs i = program.evalE (program.reader e) 0 rhs i :=
  (RealizedProgram.holdsWith_equal_iff_of_domainField
    (FalconRingMember.domainField0 (program := program))).1 h

/-- **A membership predicate holds** where the source program holds. -/
theorem holdsAt_src {e : program.Env I} (hs : program.SourceSatAt e) {p : ℕ}
    (hp : p ∈ [0, FalconRingMember.idxPred program]) : program.HoldsAt e (program.predicate p).body :=
  hs.preds _ (RealizedProgram.predicate_mem (FalconRingMember.inSource p hp).1)
    (FalconRingMember.inSource p hp).2

/-- **The membership's predicates hold**: `member.signer` and the index bits' check. -/
def MemberPreds (e : program.Env I) : Prop :=
  ∀ p ∈ [0, FalconRingMember.idxPred program], program.HoldsAt e (program.predicate p).body

/-- **The membership's predicates hold** where the source program holds. -/
theorem memberPreds_of_source {e : program.Env I} (hs : program.SourceSatAt e) : MemberPreds e :=
  fun _ hp => holdsAt_src hs hp

/-- **Entry `i` of the challenge** (`statement.c`) of a statement, read in field `0`. -/
def chalEntry (x : program.Valuation I) (i : ℕ) : (I 0).K :=
  RealizedProgram.castElt (x (FalconRingMember.chal program) i)

/-- **`s2`**. -/
def s2Of (e : program.Env I) (i : ℕ) : (I 0).K :=
  program.evalE (program.reader e) 0 (.leaf (FalconRingMember.s2 program)) i

variable [RingField (I 0) (FalconRingMember.mOne program)]

theorem read_leafRing (e : program.Env I) (s : ℕ) :
    program.evalE (program.read e program.values.length) 0 (.leaf (FalconRingMember.ring program)) s =
      ringEntry e.stmt s := by
  obtain ⟨n, hn⟩ := values_length_succ (program := program)
  rw [RealizedProgram.evalE_leaf, hn]
  simp only [RealizedProgram.read, FalconRingMember.ringKind (program := program), if_true]
  rfl

/-- **The index bits** (`member.signer.index`) as naturals, `0` past the sixth. -/
def bitsOf (e : program.Env I) (i : ℕ) : ℕ :=
  if i < 6 then (I 0).toNat (program.evalE (program.reader e) 0 (.leaf vIdx) i) else 0

/-- **The signer's position**: the index bits read as a natural. -/
def idxOf (e : program.Env I) : ℕ := lowBits (bitsOf e) 5

/-- **The index bits are bits** where the membership's predicates hold
(`member.signer.index.boolean`). -/
theorem bitsOf_spec {e : program.Env I} (hs : MemberPreds e) {i : ℕ} (hi : i < 6) :
    bitsOf e i ≤ 1 ∧ program.evalE (program.reader e) 0 (.leaf vIdx) i = (bitsOf e i : (I 0).K) := by
  obtain ⟨t, hb⟩ := FalconRingMember.idxBool (program := program)
  have h := hs (FalconRingMember.idxPred program) (by simp)
  rw [hb] at h
  have hx := holdsAt_equal0 h i (by
    rw [RealizedProgram.exprLen_mul, RealizedProgram.exprLen_leaf, (FalconRingMember.sizes (program := program)).1]
    exact hi)
  rw [RealizedProgram.evalE_mul] at hx
  unfold bitsOf
  rw [if_pos hi]
  rcases eq_zero_or_one_of_sq_eq_self ((sq _).trans hx) with h0 | h1
  · rw [h0, RingField.toNat_zero (negOne := FalconRingMember.mOne program), Nat.cast_zero]
    exact ⟨by norm_num, rfl⟩
  · rw [h1, RingField.toNat_one (negOne := FalconRingMember.mOne program), Nat.cast_one]
    exact ⟨le_rfl, rfl⟩

theorem bitsOf_le (e : program.Env I) (hs : MemberPreds e) (i : ℕ) : bitsOf e i ≤ 1 := by
  by_cases hi : i < 6
  · exact (bitsOf_spec hs hi).1
  · simp [bitsOf, hi]

/-- **The signer's position is below `64`.** -/
theorem idxOf_lt (e : program.Env I) (hs : MemberPreds e) : idxOf e < 64 :=
  lowBits_lt (bitsOf_le e hs) 5

theorem decode_mOne : (I 0).decode (FalconRingMember.mOne program) = -1 :=
  RingField.decode_negOne

theorem exprLen_memberLhs (spec pow idx mOne : ℕ) : program.exprLen (memberLhs spec pow idx mOne) = 1 := by
  unfold memberLhs
  rw [RealizedProgram.exprLen_add, RealizedProgram.exprLen_apply, RealizedProgram.exprLen_mul, RealizedProgram.exprLen_reindex]
  simp [RealizedProgram.NamedOp.rows, RealizedProgram.NamedOp.cols]

/-- **The table selection's field facts** at the program's constant `−1`. -/
theorem selectField_shape :
    RealizedProgram.SelectField (I 0) (RealizedProgram.TableSelect.shape program).mOne := by
  rw [(FalconRingMember.table (program := program)).2.2.2.2.1]
  infer_instance

/-- **The table selection's domain** has field `0`. -/
theorem domainField_shape :
    program.domainField (RealizedProgram.TableSelect.shape program).dom = 0 := by
  rw [(FalconRingSelect.ids (program := program)).1]
  exact FalconRingMember.domainField0

/-- **The table selection's index bits** are the membership's. -/
theorem bitsOf_shape (e : program.Env I) : RealizedProgram.TableSelect.bitsOf 0 e = bitsOf e := by
  funext i
  unfold RealizedProgram.TableSelect.bitsOf bitsOf
  rw [(FalconRingSelect.ids (program := program)).2.2.1]

/-- **The table selection's index** is the signer's position. -/
theorem idxOf_shape (e : program.Env I) : RealizedProgram.TableSelect.idxOf 0 e = idxOf e := by
  unfold RealizedProgram.TableSelect.idxOf idxOf lowBits RealizedProgram.idxVal
  rw [bitsOf_shape, (FalconRingSelect.ids (program := program)).2.2.1]

/-- **The table selection's challenge** is `member.ring.gamma`. -/
theorem gammaOf_shape (e : program.Env I) : RealizedProgram.TableSelect.gammaOf 0 e = gammaOf e := by
  unfold RealizedProgram.TableSelect.gammaOf gammaOf
  rw [(FalconRingSelect.ids (program := program)).2.2.2.2]

/-- **The table selection's image of the selected row** is the transform of the ring's row at the
signer's position. -/
theorem mapOf_shape (e : program.Env I)
    (hb : ∀ i < 6, bitsOf e i ≤ 1 ∧
      program.evalE (program.reader e) 0 (.leaf vIdx) i = (bitsOf e i : (I 0).K)) {c : ℕ}
    (hc : c < 512) : RealizedProgram.TableSelect.mapOf 0 e c =
      RealizedProgram.Ops.nttNatural 512 ((I 0).decode (FalconRingMember.psi program))
        (fun c => ringEntry e.stmt (idxOf e * 512 + c)) c := by
  have hle : ∀ i, bitsOf e i ≤ 1 := fun i => by
    by_cases hi : i < 6
    · exact (hb i hi).1
    · simp [bitsOf, hi]
  have hidx : idxOf e < 64 := lowBits_lt hle 5
  obtain ⟨-, hparts, hmap, -⟩ := FalconRingMember.table (program := program)
  have hrow : RealizedProgram.TableSelect.rowIdx 0 e = idxOf e := by
    unfold RealizedProgram.TableSelect.rowIdx
    rw [idxOf_shape, (FalconRingSelect.ids (program := program)).2.2.2.1, if_pos hidx]
  unfold RealizedProgram.TableSelect.mapOf
  rw [hmap, hrow]
  simp only [RealizedProgram.rowApply, if_pos hc, RealizedProgram.RowLeaf.apply, if_true]
  refine RealizedProgram.NamedOp.nttNatural_congr (fun i hi => ?_) c
  unfold RealizedProgram.TableSelect.rowAt
  rw [hparts]
  simp only [RealizedProgram.rowOf, if_pos hi]
  rw [← read_leafRing e]
  rfl

/-- **The membership's left side**, at index bits that are bits: the fingerprint
`Σ_k spectrum_k γ^k` of the committed spectrum less the fingerprint of the natural-order transform
of the ring's row at the position the bits name (`idxOf`). -/
theorem evalE_memberLhs (e : program.Env I)
    (hb : ∀ i < 6, bitsOf e i ≤ 1 ∧
      program.evalE (program.reader e) 0 (.leaf vIdx) i = (bitsOf e i : (I 0).K)) :
    program.evalE (program.reader e) 0 (memberLhs (FalconRingMember.spec program)
        (FalconRingMember.pow program) vIdx (FalconRingMember.mOne program)) 0 =
      ∑ t : Fin 512, specOf e t * gammaOf e ^ (t : ℕ) - ∑ m : Fin 512, gammaOf e ^ (m : ℕ) *
        RealizedProgram.Ops.nttNatural 512 ((I 0).decode (FalconRingMember.psi program))
          (fun c => ringEntry e.stmt (idxOf e * 512 + c)) m := by
  haveI := selectField_shape (program := program) (I := I)
  obtain ⟨t, hm⟩ := FalconRingMember.member (program := program)
  obtain ⟨T, F, tg, hbody, hT, hF⟩ :=
    RealizedProgram.TableShape.bodyOk_spec (RealizedProgram.TableSelect.bodyOk (program := program))
  rw [(FalconRingSelect.ids (program := program)).2.1, hm] at hbody
  have hL := (RealizedProgram.PredBody.equal.inj hbody).2.1
  obtain ⟨hrec, -, hmap, -⟩ := FalconRingMember.table (program := program)
  have hb' : ∀ i < (RealizedProgram.TableSelect.shape program).bits,
      RealizedProgram.TableSelect.bitsOf 0 e i ≤ 1 ∧ program.evalE (program.reader e) 0
        (.leaf (RealizedProgram.TableSelect.shape program).idx) i =
          (RealizedProgram.TableSelect.bitsOf 0 e i : (I 0).K) := by
    rw [bitsOf_shape, (FalconRingSelect.ids (program := program)).2.2.1]
    exact hb
  obtain ⟨-, hv⟩ := RealizedProgram.TableSelect.evalE_lhs domainField_shape e hT hF hb'
  have hW : RealizedProgram.TableSelect.W program = 512 := by
    unfold RealizedProgram.TableSelect.W
    rw [hmap]
    rfl
  have hexp : ∀ c < 512, RealizedProgram.cellExp (RealizedProgram.TableSelect.shape program).map c = c :=
    fun c hc => by
      rw [hmap]
      simp [RealizedProgram.cellExp, RealizedProgram.RowLeaf.perm, RealizedProgram.RowLeaf.scheme, hc]
  rw [hL, hv, hW, Finset.sum_range, Finset.sum_range, gammaOf_shape]
  refine congrArg₂ (· - ·) ?_ ?_
  · refine Finset.sum_congr rfl fun c _ => ?_
    rw [hexp c c.isLt]
    unfold RealizedProgram.TableSelect.recOf specOf
    rw [hrec]
  · refine Finset.sum_congr rfl fun c _ => ?_
    rw [hexp c c.isLt, mapOf_shape e hb c.isLt, _root_.mul_comm]

/-- The zero constant reads `0` in field `0`. -/
theorem evalE_zero (e : program.Env I) :
    program.evalE (program.reader e) 0 (.leaf (FalconRingMember.zero program)) 0 = 0 := by
  obtain ⟨c1, e1⟩ := FalconRingMember.consts (program := program)
  rw [RealizedProgram.evalE_leaf_of_isConstant e c1, RealizedProgram.constRead_of_valueField
    ((FalconRingMember.fields (program := program)) _ (by simp)), e1,
    RingField.decode_zero (negOne := FalconRingMember.mOne program)]

/-- **The membership's equation** (`member.signer`): where the membership's predicates hold, the
fingerprint `Σ_k spectrum_k γ^k` of the committed spectrum is the fingerprint of the natural-order
transform of the ring's row at the signer's position (`idxOf`). -/
theorem member_eq {e : program.Env I} (hs : MemberPreds e) :
    ∑ t : Fin 512, specOf e t * gammaOf e ^ (t : ℕ) = ∑ m : Fin 512, gammaOf e ^ (m : ℕ) *
      RealizedProgram.Ops.nttNatural 512 ((I 0).decode (FalconRingMember.psi program))
        (fun c => ringEntry e.stmt (idxOf e * 512 + c)) m := by
  obtain ⟨t, hb⟩ := FalconRingMember.member (program := program)
  have h := hs 0 (by simp)
  rw [hb] at h
  have hx := holdsAt_equal0 h 0 (by rw [exprLen_memberLhs]; norm_num)
  rw [evalE_zero, evalE_memberLhs e fun i hi => bitsOf_spec hs hi] at hx
  exact sub_eq_zero.1 hx

end Member

/-! ## The membership's event -/

section Event

variable {program : RealizedProgram} [FalconRingPowers program] [FalconRingSelect program]
  [FalconRingMember program] {I : RealizedProgram.Interp}

/-- **The transform of the signer's row** of the ring, at frequency `m`. -/
def keySpec (e : program.Env I) (m : ℕ) : (I 0).K :=
  RealizedProgram.Ops.nttNatural 512 ((I 0).decode (FalconRingMember.psi program)) (fun c => ringEntry e.stmt (idxOf e * 512 + c)) m

/-- **The polynomial of `n` coefficients** `Σ_{m < n} a_m X^m`. -/
@[irreducible] noncomputable def coeffPoly {K : Type*} [Field K] (n : ℕ) (a : ℕ → K) : Polynomial K :=
  ∑ m ∈ Finset.range n, Polynomial.C (a m) * Polynomial.X ^ m

theorem coeffPoly_natDegree {K : Type*} [Field K] (n : ℕ) (a : ℕ → K) :
    (coeffPoly n a).natDegree ≤ n - 1 := by
  unfold coeffPoly
  exact Polynomial.natDegree_sum_le_of_forall_le (Finset.range n) _ fun m hm =>
    (Polynomial.natDegree_C_mul_X_pow_le _ _).trans (by
      have := Finset.mem_range.1 hm
      omega)

theorem coeffPoly_eval {K : Type*} [Field K] (n : ℕ) (a : ℕ → K) (x : K) :
    (coeffPoly n a).eval x = ∑ m ∈ Finset.range n, a m * x ^ m := by
  rw [coeffPoly, Polynomial.eval_finset_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]

theorem coeffPoly_coeff {K : Type*} [Field K] {n : ℕ} (a : ℕ → K) {m : ℕ} (hm : m < n) :
    (coeffPoly n a).coeff m = a m := by
  rw [coeffPoly, Polynomial.finset_sum_coeff]
  simp only [Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single m]
  · simp
  · intro b _ hb
    rw [if_neg (Ne.symm hb)]
  · intro h
    exact absurd (Finset.mem_range.2 hm) h

/-- **The fingerprint's polynomial**: `Σ_m (spectrum_m − NTT(h)_m) X^m`, `h` the signer's row. -/
noncomputable def fpPoly (e : program.Env I) : Polynomial (I 0).K :=
  coeffPoly 512 fun m => specOf e m - keySpec e m

/-- **The membership's event**: `γ` is a root of the fingerprint's polynomial, which is nonzero
(degree at most `511`). -/
noncomputable def fpEvent (e : program.Env I) : ChallengeEvent (I 0).K :=
  ⟨fpPoly e, 511, le_trans (coeffPoly_natDegree _ _) (by norm_num)⟩

theorem fpEvent_poly (e : program.Env I) : (fpEvent e).poly = fpPoly e := rfl

/-- **The source program's event** at `member.ring.gamma` (challenge `0`). -/
def ringEvent (j : ℕ) (e : program.Env I) : Prop := j = 0 ∧ (fpEvent e).BadAt (gammaOf e)

theorem specOf_congr {e e' : program.Env I} (ha : e.asg = e'.asg) : specOf e = specOf e' := by
  funext t
  unfold specOf
  rw [RealizedProgram.evalE_leaf, RealizedProgram.evalE_leaf,
    RealizedProgram.reader_of_priv e (FalconRingMember.privKinds (program := program)).1,
    RealizedProgram.reader_of_priv e' (FalconRingMember.privKinds (program := program)).1, ha]

theorem bitsOf_congr {e e' : program.Env I} (ha : e.asg = e'.asg) : bitsOf e = bitsOf e' := by
  funext t
  unfold bitsOf
  rw [RealizedProgram.evalE_leaf, RealizedProgram.evalE_leaf,
    RealizedProgram.reader_of_priv e (FalconRingMember.privKinds (program := program)).2.1,
    RealizedProgram.reader_of_priv e' (FalconRingMember.privKinds (program := program)).2.1, ha]

theorem fpEvent_congr {e e' : program.Env I} (hs : e.stmt = e'.stmt) (ha : e.asg = e'.asg) :
    fpEvent e = fpEvent e' := by
  have h1 := specOf_congr ha
  have h2 : idxOf e = idxOf e' := by unfold idxOf; rw [bitsOf_congr ha]
  have hk : keySpec e = keySpec e' := by
    funext m
    unfold keySpec ringEntry
    rw [h2, hs]
  have hp : fpPoly e = fpPoly e' := by
    unfold fpPoly
    rw [h1, hk]
  simp only [fpEvent, hp]

/-- **The challenge-use rule** (`RealizedProgram.ChallengeUseAt`): the event reads the statement, the
committed assignment and its challenge. -/
theorem ringEvent_use : RealizedProgram.ChallengeUseAt program I ringEvent := by
  intro j e e' h
  unfold ringEvent
  rw [fpEvent_congr h.stmt h.asg]
  by_cases hj0 : j = 0
  · subst hj0
    unfold gammaOf
    rw [h.chal 0 (Or.inr ⟨rfl, le_refl 0⟩)]
  · simp [hj0]

/-- **The event's errors**: `511/|F|` at `member.ring.gamma`, `0` elsewhere. -/
noncomputable def ringEps (I : RealizedProgram.Interp) (j : ℕ) : NNReal :=
  if j = 0 then 511 / Fintype.card (I 0).K else 0

/-- **The event's probability** (`RealizedProgram.rbr_of_events`' `hbound`): at most `511/|F|` at
`member.ring.gamma` (`RealizedProgram.probUniform_badAt_setChal_le`, Schwartz–Zippel). -/
theorem ringEvent_bound : ∀ j, program.IsSourceChal j → ∀ e : program.Env I,
    Pr[c ← program.ChalVal I j : ringEvent j (e.setChal j c)] ≤ (ringEps I j : ENNReal) := by
  intro j _ e
  by_cases hj0 : j = 0
  swap
  · rw [QROM.probUniform_eq_zero fun _ h => hj0 h.1]
    exact zero_le
  subst hj0
  have hset : ∀ c, ringEvent 0 (e.setChal 0 c) ↔
      (fpEvent e).BadAt (RealizedProgram.castElt ((e.setChal 0 c).chal 0 0)) := fun c => by
    simp only [ringEvent, true_and]
    rw [fpEvent_congr (e := e.setChal 0 c) (e' := e) rfl rfl]
    rfl
  simp only [hset]
  obtain ⟨hsz, hsm, hf⟩ := FalconRingMember.chal0 (program := program)
  refine (RealizedProgram.probUniform_badAt_setChal_le hsz hsm hf (fpEvent e) e).trans ?_
  simp [ringEps, fpEvent]

variable [RingField (I 0) (FalconRingMember.mOne program)]

/-- **Without the event, the spectrum is the transform of the signer's row**: the fingerprints
agree (`member_eq`), so `γ` is a root of the fingerprint's polynomial, which is then `0`. -/
theorem spec_eq_of_not_event {e : program.Env I} (hs : MemberPreds e)
    (hev : ¬ ringEvent 0 e) (m : Fin 512) : specOf e m = keySpec e m := by
  have heval : (fpPoly e).eval (gammaOf e) = 0 := by
    rw [fpPoly, coeffPoly_eval, ← Fin.sum_univ_eq_sum_range
      (fun m => (specOf e m - keySpec e m) * gammaOf e ^ m) 512]
    have := member_eq hs
    simp only [sub_mul, Finset.sum_sub_distrib]
    rw [this, sub_eq_zero]
    exact Finset.sum_congr rfl fun m _ => _root_.mul_comm _ _
  have hz : fpPoly e = 0 := by
    by_contra hne
    apply hev
    refine ⟨rfl, ?_, ?_⟩
    · rw [fpEvent_poly]
      exact hne
    · rw [fpEvent_poly]
      exact heval
  have := coeffPoly_coeff (fun m => specOf e m - keySpec e m) m.isLt
  rw [← fpPoly, hz, Polynomial.coeff_zero] at this
  exact sub_eq_zero.1 this.symm

end Event

/-! ## The relation and the extractor -/

section Relation

open Native (CoreWit)

variable {program : RealizedProgram} [FalconRingPowers program] [FalconRingSelect program]
  [FalconRingMember program] {I : RealizedProgram.Interp}

/-- **The challenge's coefficients** of a statement (`statement.c`), read as naturals below `q`. -/
def chalNat (x : program.Valuation I) (i : Fin falcon512.n) : ℕ :=
  (I 0).toNat (chalEntry x i)

/-- **Key `r` of the ring** of a statement (row `r` of `statement.ring`), its coefficients read as
naturals below `q`. -/
def ringKey (x : program.Valuation I) (r : ℕ) : PublicKey :=
  ⟨Falcon512.ofCoeff fun c => ((I 0).toNat (ringEntry x (r * 512 + c)) : _root_.Falcon.Coeff)⟩

/-- **The relation of the theorem at a Falcon ring's realized program** at the statement's ring and
challenge `c`: the signer's position is below `64` and, at its key, Falcon's algebraic verifier
accepts `s2` on `c` (`c − s2·h` and `s2` within the norm bound) and `s2` is encodable. -/
def rel : Set (program.Valuation I × CoreWit) :=
  {p | p.2.idx < 64 ∧
    Falcon512.algebraOk falcon512 (ringKey p.1 p.2.idx).h
      (Falcon512.ofCoeff fun i => (chalNat p.1 i : _root_.Falcon.Coeff)) p.2.s2.toRq ∧
    Falcon512.EncodingBounds falcon512 p.2.s2}

/-- **The witness read off the committed values**: the index bits read as the position, and the
centred `s2` (`Emulated.decodeS2Int`).

Running time: `6` bits and `512` coefficients read, lifted and centred.
This running time is argued here, not proved in Lean. -/
-- spec-side
def proj (_x : program.Valuation I) (a : program.Assignment I) : CoreWit :=
  ⟨lowBits (fun i => if i < 6 then (I 0).toNat (RealizedProgram.castElt (a.val (FalconRingSelect.idx program) i)) else 0) 5,
    Emulated.decodeS2Int fun i => (RealizedProgram.castElt (a.val (FalconRingMember.s2 program) i) : (I 0).K)⟩

/-- **The extractor of `Π_P₀`** (`RealizedProgram.sourceExtractor` at `proj`).

Running time: the source extractor's reading of the committed values, then one call of `proj`
(`6` bits and `512` coefficients read, lifted and centred).
This running time is argued here, not proved in Lean. -/
def extractor :
    Extractor (program.sourceSpec I) (program.Valuation I) CoreWit :=
  program.sourceExtractor I proj

theorem proj_idx (e : program.Env I) : (proj e.stmt e.asg).idx = idxOf e := by
  simp only [proj, idxOf]
  congr 1
  funext i
  simp only [bitsOf, RealizedProgram.evalE_leaf,
    RealizedProgram.reader_of_priv e (FalconRingMember.privKinds (program := program)).2.1]

theorem proj_s2 (e : program.Env I) :
    (proj e.stmt e.asg).s2 = Emulated.decodeS2Int fun i => s2Of e i := by
  simp only [proj, s2Of, RealizedProgram.evalE_leaf,
    RealizedProgram.reader_of_priv e (FalconRingMember.privKinds (program := program)).2.2]
  rfl

end Relation

/-! ## The signature equation at a random point -/

section Signature

variable {program : RealizedProgram} [FalconRingPowers program] [FalconRingSelect program]
  [FalconRingMember program] [FalconRandomPoint program] {I : RealizedProgram.Interp}

open Polynomial RealizedProgram.Ops

/-- **The signature equation's first vector** `E` read in field `0`. -/
def eOf (e : program.Env I) (i : ℕ) : (I 0).K :=
  program.evalE (program.reader e) 0 (FalconRandomPoint.sigE program) i

/-- **`signature.Q`**: the high half of `h · s2` by `X^512 + 1`. -/
def qOf (e : program.Env I) (i : ℕ) : (I 0).K :=
  program.evalE (program.reader e) 0 (.leaf (FalconRandomPoint.q program)) i

/-- **The challenge `r`** (`signature.r`) read in field `0`. -/
def rOf (e : program.Env I) : (I 0).K :=
  RealizedProgram.castElt (e.chal (FalconRandomPoint.rChal program) 0)

/-- **The signature equation's polynomial** over the field: `E − H · s2 + (X^512 + 1) Q`, `H` the
polynomial whose natural-order transform at `ψ` is the committed spectrum
(`Ops.inverseNttNatural`). -/
noncomputable def sigPoly (e : program.Env I) : (I 0).K[X] :=
  polyOf 512 (eOf e) -
    polyOf 512 (inverseNttNatural 512 ((I 0).decode (FalconRingMember.psi program)) (specOf e)) *
      polyOf 512 (s2Of e) +
    (Polynomial.X ^ 512 + 1 : (I 0).K[X]) * polyOf 511 (qOf e)

theorem sigPoly_natDegree (e : program.Env I) : (sigPoly e).natDegree ≤ 1022 := by
  unfold sigPoly
  refine (natDegree_add_le _ _).trans (max_le ((natDegree_sub_le _ _).trans (max_le ?_ ?_)) ?_)
  · exact (Polynomial.ofFn_natDegree_lt (n := 512) (by norm_num) _).le.trans (by norm_num)
  · exact natDegree_polyOf_mul_le (n := 512) (by norm_num) _ _
  · exact natDegree_quotient_le (n := 512) (by norm_num) (qOf e)

/-- **The signature equation's event**: `r` is a root of the signature equation's polynomial, which
is nonzero (degree at most `1022`). -/
noncomputable def sigEvent (e : program.Env I) : ChallengeEvent (I 0).K :=
  ⟨sigPoly e, 1022, sigPoly_natDegree e⟩

theorem sigEvent_poly (e : program.Env I) : (sigEvent e).poly = sigPoly e := rfl

/-- **A committed value reads alike** in two environments of one assignment. -/
theorem leaf_priv_congr {e e' : program.Env I} {v : ℕ} (hk : (program.value v).kind = .priv)
    (ha : e.asg = e'.asg) (t : ℕ) :
    program.evalE (program.reader e) 0 (.leaf v) t = program.evalE (program.reader e') 0 (.leaf v) t := by
  rw [RealizedProgram.evalE_leaf, RealizedProgram.evalE_leaf, RealizedProgram.reader_of_priv e hk,
    RealizedProgram.reader_of_priv e' hk, ha]

/-- **The signature equation's polynomial reads the first vector and the assignment**: two
environments of one assignment whose first vectors read alike below `512` have one polynomial
(`Q`, `s2` committed, the spectrum `specOf_congr`). -/
theorem sigPoly_congr {e e' : program.Env I} (hE : ∀ t < 512, eOf e t = eOf e' t)
    (ha : e.asg = e'.asg) : sigPoly e = sigPoly e' := by
  have h2 : qOf e = qOf e' :=
    funext (leaf_priv_congr (FalconRandomPoint.qPriv (program := program)) ha)
  have h3 : s2Of e = s2Of e' :=
    funext (leaf_priv_congr (FalconRingMember.privKinds (program := program)).2.2 ha)
  unfold sigPoly
  rw [polyOf_congr hE, h2, h3, specOf_congr ha]

theorem sigEvent_congr {e e' : program.Env I} (hE : ∀ t < 512, eOf e t = eOf e' t)
    (ha : e.asg = e'.asg) : sigEvent e = sigEvent e' := by
  rw [sigEvent, sigEvent, ChallengeEvent.mk.injEq]
  exact ⟨sigPoly_congr hE ha, rfl⟩

variable [FalconRandomPointField program (I 0)]

/-- **The powers of `r`**, one level down: `r^t`. -/
theorem evalE_pwRef (e : program.Env I) {t : ℕ} (ht : t < 512) :
    program.evalE (program.read e program.values.length) 0
      (.ref (FalconRandomPoint.pwRef program)) t = rOf e ^ t :=
  (FalconRandomPoint.rPow (program := program)).evalE_range (I := I)
    (RingField.decode_one (negOne := FalconRingMember.mOne program))
    FalconRandomPoint.refsOrdered FalconRandomPoint.exprs_pos e FalconRandomPoint.powPw ht

/-- **The powers of `r`** (`signature.equation.public0`): `r^t`. -/
theorem evalE_pw (e : program.Env I) {t : ℕ} (ht : t < 512) :
    program.evalE (program.reader e) 0 (.leaf (FalconRandomPoint.pw program)) t = rOf e ^ t := by
  rw [RealizedProgram.evalE_leaf_pubExpr e FalconRandomPoint.pwKind
    ((FalconRandomPoint.sigFields (program := program)) _ (by simp)), evalE_pwRef e ht]

/-- **`r^512 + 1`** (`signature.equation.public1`). -/
theorem evalE_rn (e : program.Env I) :
    program.evalE (program.reader e) 0 (.leaf (FalconRandomPoint.rn program)) 0 =
      rOf e ^ 512 + 1 := by
  rw [RealizedProgram.evalE_leaf_pubExpr e FalconRandomPoint.rnKind
    ((FalconRandomPoint.sigFields (program := program)) _ (by simp)),
    (FalconRandomPoint.rPow (program := program)).evalE_sq_add_one (I := I)
      (RingField.decode_one (negOne := FalconRingMember.mOne program))
      FalconRandomPoint.refsOrdered FalconRandomPoint.exprs_pos e FalconRandomPoint.pow256]
  rfl

/-- **The interpolation weights** (`signature.lambda`): `512⁻¹ Ntt_{ψ⁻¹}(1, r, …, r^511)`. -/
theorem evalE_lam (e : program.Env I) {t : ℕ} (ht : t < 512) :
    program.evalE (program.reader e) 0 (.leaf (FalconRandomPoint.lam program)) t =
      ((512 : ℕ) : (I 0).K)⁻¹ *
        nttNatural 512 ((I 0).decode (FalconRingMember.psi program))⁻¹ (fun s => rOf e ^ s) t := by
  rw [RealizedProgram.evalE_leaf_pubExpr e FalconRandomPoint.lamKind
    ((FalconRandomPoint.sigFields (program := program)) _ (by simp)),
    (FalconRandomPoint.rPow (program := program)).evalE_lambda_natural (I := I)
      (RingField.decode_one (negOne := FalconRingMember.mOne program))
      FalconRandomPoint.refsOrdered FalconRandomPoint.exprs_pos e FalconRandomPoint.powPw _ _ ht,
    FalconRandomPointField.decode_nInv, FalconRandomPointField.decode_psiInv]
  rfl

/-- The zero constant (one coordinate) reads `0` in field `0`. -/
theorem evalE_zero1 (e : program.Env I) :
    program.evalE (program.reader e) 0 (.leaf (FalconRandomPoint.zero1 program)) 0 = 0 :=
  RealizedProgram.evalE_zeroConst e (FalconRandomPoint.const0 (program := program)).1
    ((FalconRandomPoint.sigFields (program := program)) _ (by simp))
    (FalconRandomPoint.const0 (program := program)).2
    (RingField.decode_zero (negOne := FalconRingMember.mOne program))

theorem exprLen_sigLhs : program.exprLen (FalconRandomPoint.lhs program) = 1 := by
  rw [FalconRandomPoint.lhs, sigLhs, RealizedProgram.exprLen_add, RealizedProgram.exprLen_add,
    RealizedProgram.exprLen_apply, RealizedProgram.exprLen_mul, FalconRandomPoint.sigELen,
    RealizedProgram.exprLen_leaf, (FalconRingMember.sizes (program := program)).2.2.2.1]
  simp [RealizedProgram.NamedOp.rows, RealizedProgram.NamedOp.cols]

/-- **The signature equation's left side** (`signature.equation`, one coordinate) is the
signature equation's polynomial at `r`. -/
theorem evalE_sigLhs (e : program.Env I) :
    program.evalE (program.reader e) 0 (FalconRandomPoint.lhs program) 0 =
      (sigPoly e).eval (rOf e) := by
  have hA : ∀ t : Fin 512,
      program.evalE (program.reader e) 0 (FalconRandomPoint.sigE program) t *
      program.evalE (program.reader e) 0 (.leaf (FalconRandomPoint.pw program)) t =
      eOf e t * rOf e ^ (t : ℕ) := fun t => by
    rw [evalE_pw e t.isLt]; rfl
  have hB : ∀ t : Fin 512,
      program.evalE (program.reader e) 0 (.leaf (FalconRingMember.spec program)) t *
      program.evalE (program.reader e) 0 (.leaf (FalconRandomPoint.lam program)) t =
      specOf e t * (((512 : ℕ) : (I 0).K)⁻¹ *
        nttNatural 512 ((I 0).decode (FalconRingMember.psi program))⁻¹ (fun s => rOf e ^ s) t) :=
    fun t => by rw [evalE_lam e t.isLt]; rfl
  have hC : ∀ t : Fin 512,
      program.evalE (program.reader e) 0 (.leaf (FalconRingMember.s2 program)) t *
      program.evalE (program.reader e) 0 (.leaf (FalconRandomPoint.pw program)) t =
      s2Of e t * rOf e ^ (t : ℕ) := fun t => by
    rw [evalE_pw e t.isLt]; rfl
  have hQ : ∀ t : Fin 511,
      program.evalE (program.reader e) 0 (.leaf (FalconRandomPoint.q program)) t *
      program.evalE (program.reader e) 0 (.leaf (FalconRandomPoint.pw program))
        (RealizedProgram.IndexMap.entry [(0, 1, 511)] t) = qOf e t * rOf e ^ (t : ℕ) := fun t => by
    rw [RealizedProgram.IndexMap.entry_step_one t.isLt, Nat.zero_add, evalE_pw e (by omega)]; rfl
  unfold sigPoly
  rw [eval_add, eval_sub, eval_mul, eval_mul, eval_inverseNttNatural, polyOf_eval, polyOf_eval,
    polyOf_eval, eval_add, eval_pow, eval_X, eval_one, ← Fin.sum_univ_eq_sum_range,
    ← Fin.sum_univ_eq_sum_range, ← Fin.sum_univ_eq_sum_range]
  simp only [FalconRandomPoint.lhs, sigLhs, RealizedProgram.evalE_add,
    RealizedProgram.evalE_scale_const, RingField.decode_negOne, RealizedProgram.evalE_mul,
    RealizedProgram.evalE_apply_sum, zero_mul, zero_add, RealizedProgram.evalE_reindex, evalE_rn,
    hA, hB, hC, hQ]
  ring

/-- **The signature equation holds exactly where its polynomial vanishes at `r`**
(`signature.equation`, one coordinate: its left side is the polynomial at `r`, its right side the
zero constant). -/
theorem holdsAt_sig_iff (e : program.Env I) :
    program.HoldsAt e (program.predicate (FalconRandomPoint.sigPred program)).body ↔
      (sigPoly e).eval (rOf e) = 0 := by
  obtain ⟨t, hb⟩ := FalconRandomPoint.sig (program := program)
  rw [RealizedProgram.HoldsAt, hb, RealizedProgram.holdsWith_equal_iff_of_domainField
    (FalconRingMember.domainField0 (program := program))]
  show (∀ i < program.exprLen (FalconRandomPoint.lhs program),
      program.evalE (program.reader e) 0 (FalconRandomPoint.lhs program) i =
        program.evalE (program.reader e) 0 (.leaf (FalconRandomPoint.zero1 program)) i) ↔ _
  rw [exprLen_sigLhs]
  constructor
  · intro h
    have hx := h 0 Nat.one_pos
    rwa [evalE_zero1, evalE_sigLhs] at hx
  · intro h i hi
    obtain rfl : i = 0 := by omega
    rwa [evalE_zero1, evalE_sigLhs]

/-- **The signature equation's polynomial vanishes at `r`** where the source program holds. -/
theorem sigPoly_eval {e : program.Env I} (hs : program.SourceSatAt e) :
    (sigPoly e).eval (rOf e) = 0 :=
  (holdsAt_sig_iff e).1 (hs.preds _
    (RealizedProgram.predicate_mem (FalconRandomPoint.inSourceSig (program := program)).1)
    (FalconRandomPoint.inSourceSig (program := program)).2)

/-- **The signature equation's polynomial is `0`** where the source program holds and `r` is not a
root of it while it is nonzero. -/
theorem sigPoly_eq_zero {e : program.Env I} (hs : program.SourceSatAt e)
    (hev : ¬ (sigEvent e).BadAt (rOf e)) : sigPoly e = 0 := by
  by_contra hne
  exact hev ⟨by rw [sigEvent_poly]; exact hne, by rw [sigEvent_poly]; exact sigPoly_eval hs⟩

/-- **The signature equation at the roots** (`signature.equation`): where the source program holds
and `r` is not a root of the signature equation's nonzero polynomial, `Ntt(E)_k = spectrum_k ·
Ntt(s2)_k` at every frequency `k < 512`: the polynomial is `0`, and at the root `ψ^(2k+1)` of
`X^512 + 1` it reads the transforms. -/
theorem sig_spectral {e : program.Env I} (hs : program.SourceSatAt e)
    (hev : ¬ (sigEvent e).BadAt (rOf e)) {k : ℕ} (hk : k < 512) :
    nttNatural 512 ((I 0).decode (FalconRingMember.psi program)) (eOf e) k =
      specOf e k * nttNatural 512 ((I 0).decode (FalconRingMember.psi program)) (s2Of e) k := by
  have hz := sigPoly_eq_zero hs hev
  have hψ := FalconRandomPointField.psi_isPrimitiveRoot (program := program) (F := I 0)
  have hψn : ((I 0).decode (FalconRingMember.psi program)) ^ 512 = -1 :=
    DFT.IsPrimitiveRoot.pow_half_eq_neg_one hψ (by decide)
  have hn0 := FalconRandomPointField.n_ne_zero (program := program) (F := I 0)
  have h := congrArg (fun P => P.eval (((I 0).decode (FalconRingMember.psi program)) ^ (2 * k + 1))) hz
  simp only [eval_zero] at h
  rw [sigPoly, eval_add, eval_sub, eval_mul, eval_mul, eval_X_pow_add_one_root hψn k, zero_mul,
    add_zero, polyOf_eval_root_natural _ _ _ hk, polyOf_eval_root_natural _ _ _ hk,
    polyOf_eval_root_natural _ _ _ hk, nttNatural_inverseNttNatural hψ hn0 _ hk] at h
  exact sub_eq_zero.1 h

/-- **The signature equation's coefficients** where the source program holds and `r` is not a root
of the signature equation's nonzero polynomial: the polynomial is `0`, so (`Ops.polyOf_mul_polyOf`)
`polyOf(E − H · s2 mod X^512 + 1) + (X^512 + 1)(Q − high(H · s2)) = 0`, whose low part
vanishes (`Ops.polyOf_eq_zero_of_add_mul`): `E_t` is the negacyclic product's coefficient `t`. -/
theorem eOf_eq_negacyclic {e : program.Env I} (hs : program.SourceSatAt e)
    (hev : ¬ (sigEvent e).BadAt (rOf e)) {t : ℕ} (ht : t < 512) :
    eOf e t = negacyclic 512
      (inverseNttNatural 512 ((I 0).decode (FalconRingMember.psi program)) (specOf e)) (s2Of e) t := by
  have hz := sigPoly_eq_zero hs hev
  set H := inverseNttNatural 512 ((I 0).decode (FalconRingMember.psi program)) (specOf e)
  have hmul := polyOf_mul_polyOf (K := (I 0).K) (n := 512) (by norm_num) H (s2Of e)
  rw [show (512 : ℕ) - 1 = 511 from rfl] at hmul
  have h0 : polyOf 512 (eOf e - negacyclic 512 H (s2Of e)) +
      (Polynomial.X ^ 512 + 1 : (I 0).K[X]) * (polyOf 511 (qOf e) - polyOf 511 (high 512 H (s2Of e))) =
      0 := by
    rw [polyOf_sub]
    unfold sigPoly at hz
    linear_combination hz + hmul
  have h1 := eq_zero_of_polyOf_eq_zero (polyOf_eq_zero_of_add_mul (n := 512) (by norm_num) h0).1 ht
  rw [Pi.sub_apply] at h1
  exact sub_eq_zero.1 h1

end Signature

/-! ## The native ring's signature equation -/

section NativeSignature

variable {program : RealizedProgram} [FalconRingPowers program] [FalconRingSelect program]
  [FalconRingMember program] [FalconRingBase program] {I : RealizedProgram.Interp}

open Polynomial RealizedProgram.Ops

/-- **`signature.s1`**. -/
def s1Of (e : program.Env I) (i : ℕ) : (I 0).K :=
  program.evalE (program.reader e) 0 (.leaf (FalconRingBase.s1 program)) i

variable [AField (I 0)]

theorem decode_q1 : (I 0).decode 12288 = -1 := RingField.decode_negOne

/-- **A native ring's field facts at its constant `−1`** (`12288`). -/
theorem ringField_base : RingField (I 0) (FalconRingMember.mOne program) := by
  rw [(FalconRingBase.consts (program := program)).1]
  infer_instance

/-- `512⁻¹ = 12265` and `ψ⁻¹ = 8974` in a field of characteristic `q`
(`Ops.natCast_eq_inv_of_mul_mod`, `RealizedProgram.decode_eq_inv_of_mul_mod`). -/
theorem decode_nInv : (I 0).decode 12265 = ((512 : ℕ) : (I 0).K)⁻¹ := by
  rw [AField.decode_lt _ (by norm_num)]
  exact RealizedProgram.Ops.natCast_eq_inv_of_mul_mod 12289 (by norm_num)

theorem decode_psiInv : (I 0).decode 8974 = ((I 0).decode 10302)⁻¹ :=
  RealizedProgram.decode_eq_inv_of_mul_mod 12289 (AField.decode_lt _ (by norm_num))
    (AField.decode_lt _ (by norm_num)) (by norm_num)

/-- `ψ = 10302` decodes to the transform root. -/
theorem decode_psi' : (I 0).decode 10302 = Native.psiF (I 0).K := by
  rw [AField.decode_lt _ (by norm_num)]
  rfl

/-- **The signature equation's field facts** in a native ring's field (`FalconRandomPointField`):
`−1 = 12288`, `512⁻¹ = 12265`, `ψ⁻¹ = 8974` at the primitive `1024`-th root `ψ = 10302`. -/
instance instRandomPointFieldNative : FalconRandomPointField program (I 0) where
  toRingField := ringField_base
  decode_nInv := by rw [(FalconRingBase.invConsts (program := program)).1]; exact decode_nInv
  decode_psiInv := by
    rw [(FalconRingBase.invConsts (program := program)).2,
      (FalconRingBase.consts (program := program)).2]
    exact decode_psiInv
  psi_isPrimitiveRoot := by
    rw [(FalconRingBase.consts (program := program)).2, decode_psi']
    exact Native.isPrimitiveRoot_psiF (I 0).K
  n_ne_zero := Native.natCast_n_ne_zero (I 0).K

/-- **A native ring's first vector** is `c − s1`. -/
theorem eOf_eq (e : program.Env I) (t : ℕ) : eOf e t = chalEntry e.stmt t - s1Of e t := by
  have hc : program.evalE (program.reader e) 0 (.leaf (FalconRingMember.chal program)) t =
      chalEntry e.stmt t := by
    rw [RealizedProgram.evalE_leaf, RealizedProgram.reader_of_opaque_nil e
      (FalconRingMember.chalKind (program := program))]
    rfl
  unfold eOf
  rw [FalconRingBase.sigE_eq, RealizedProgram.evalE_add, RealizedProgram.evalE_scale_const,
    decode_q1, hc]
  unfold s1Of
  ring

omit [AField (I 0)] in
/-- **A native ring's first vector reads the statement and the assignment.** -/
theorem eOf_congr {e e' : program.Env I} (hs : e.stmt = e'.stmt) (ha : e.asg = e'.asg) :
    ∀ t < 512, eOf e t = eOf e' t := fun t _ => by
  unfold eOf
  rw [FalconRingBase.sigE_eq]
  simp only [RealizedProgram.evalE_add, RealizedProgram.evalE_scale_const,
    RealizedProgram.evalE_leaf,
    RealizedProgram.reader_of_opaque_nil e (FalconRingMember.chalKind (program := program)),
    RealizedProgram.reader_of_opaque_nil e' (FalconRingMember.chalKind (program := program)),
    RealizedProgram.reader_of_priv e (FalconRingBase.s1Priv (program := program)),
    RealizedProgram.reader_of_priv e' (FalconRingBase.s1Priv (program := program)), hs, ha]

/-- **The signature equation** (`signature.equation`): where the source program holds and `r` is
not a root of the signature equation's nonzero polynomial, `Ntt(c − s1)_k = spectrum_k ·
Ntt(s2)_k` at every frequency `k < 512` (`sig_spectral` at `E = c − s1`, `ψ = 10302`). -/
theorem sig_eq {e : program.Env I} (hs : program.SourceSatAt e)
    (hev : ¬ (sigEvent e).BadAt (rOf e)) {k : ℕ} (hk : k < 512) :
    nttNatural 512 ((I 0).decode 10302) (fun i => chalEntry e.stmt i - s1Of e i) k =
      specOf e k * nttNatural 512 ((I 0).decode 10302) (s2Of e) k := by
  have h := sig_spectral hs hev hk
  rw [(FalconRingBase.consts (program := program)).2, show eOf e = fun i => chalEntry e.stmt i - s1Of e i
    from funext (eOf_eq e)] at h
  exact h

end NativeSignature

/-! ## The native ring's events -/

section NativeEvent

variable {program : RealizedProgram} [FalconRingPowers program] [FalconRingSelect program]
  [FalconRingMember program] [FalconRingBase program] {I : RealizedProgram.Interp}

variable [AField (I 0)]

/-- **The native ring's events**: the membership's at `member.ring.gamma` (challenge `0`) and the
signature equation's at `signature.r`. -/
def nativeEvent (j : ℕ) (e : program.Env I) : Prop :=
  ringEvent j e ∨ (j = FalconRandomPoint.rChal program ∧ (sigEvent e).BadAt (rOf e))

omit [AField (I 0)] in
/-- **The challenge-use rule** (`RealizedProgram.ChallengeUseAt`): each event reads the statement,
the committed assignment and its challenge. -/
theorem nativeEvent_use : RealizedProgram.ChallengeUseAt program I nativeEvent := by
  intro j e e' h
  unfold nativeEvent
  rw [ringEvent_use j h]
  by_cases hj : j = FalconRandomPoint.rChal program
  · subst hj
    have hr : rOf e = rOf e' := by
      unfold rOf
      rw [h.chal _ (Or.inr ⟨rfl, le_refl _⟩)]
    rw [sigEvent_congr (eOf_congr h.stmt h.asg) h.asg, hr]
  · simp [hj]

/-- **The events' errors**: `511/|F|` at `member.ring.gamma`, `1022/|F|` at `signature.r`, `0`
elsewhere. -/
noncomputable def nativeEps (I : RealizedProgram.Interp) (j : ℕ) : NNReal :=
  if j = 0 then 511 / Fintype.card (I 0).K
  else if j = FalconRandomPoint.rChal program then 1022 / Fintype.card (I 0).K else 0

/-- **The events' probabilities** (`RealizedProgram.rbr_of_events`' `hbound`): the membership's
(`ringEvent_bound`) and the signature equation's, at most `1022/|F|` at `signature.r`
(`RealizedProgram.probUniform_badAt_setChal_le`, Schwartz–Zippel). -/
theorem nativeEvent_bound : ∀ j, program.IsSourceChal j → ∀ e : program.Env I,
    Pr[c ← program.ChalVal I j : nativeEvent j (e.setChal j c)] ≤
      (nativeEps (program := program) I j : ENNReal) := by
  intro j hj e
  have hne := FalconRandomPoint.rChal_ne (program := program)
  rcases (FalconRandomPoint.isSourceChal_iff (program := program) j).1 hj with rfl | rfl
  · have hset : ∀ c, nativeEvent 0 (e.setChal 0 c) ↔ ringEvent 0 (e.setChal 0 c) := fun c => by
      simp [nativeEvent, Ne.symm hne]
    simp only [hset]
    refine (ringEvent_bound 0 hj e).trans ?_
    simp [ringEps, nativeEps]
  · have hset : ∀ c, nativeEvent (FalconRandomPoint.rChal program) (e.setChal _ c) ↔
        (sigEvent e).BadAt (RealizedProgram.castElt
          ((e.setChal (FalconRandomPoint.rChal program) c).chal (FalconRandomPoint.rChal program) 0)) :=
      fun c => by
      simp only [nativeEvent, ringEvent, hne, false_and, true_and, false_or]
      rw [sigEvent_congr (e := e.setChal _ c) (e' := e) (eOf_congr rfl rfl) rfl]
      rfl
    simp only [hset]
    obtain ⟨hsz, hsm⟩ := FalconRandomPoint.chalR (program := program)
    refine (RealizedProgram.probUniform_badAt_setChal_le hsz hsm
      (FalconRandomPoint.rPow (program := program)).chalField (sigEvent e) e).trans ?_
    simp [nativeEps, sigEvent, hne]

end NativeEvent

/-! ## The relation and the extractor -/

/-- **A node element read in an equal field identifier** stays in the node. -/
theorem castElt_mem_node_of_eq {I : RealizedProgram.Interp} {a b : ℕ} (h : a = b) {s : String} {x : (I a).K}
    (hx : x ∈ (I a).node s) : (RealizedProgram.castElt x : (I b).K) ∈ (I b).node s := by
  subst h
  rwa [RealizedProgram.castElt_self]

section Extract

open Native (CoreWit keyRecord psiF RingAlgebra SpectralRows)
open Falcon512.Native (Committed AlgRequests)
open AField (φq φq_apply coord0_φq_mul)

variable {program : RealizedProgram} [FalconRingPowers program] [FalconRingSelect program]
  [FalconRingMember program] [FalconRingBase program] {I : RealizedProgram.Interp} [AField (I 0)]

attribute [local instance] ringField_base

/-- **A prime-typed source value is in the prime subfield** where the source program holds. -/
theorem prime_of_mem {e : program.Env I} (hs : program.SourceSatAt e) {v : ℕ}
    (hv : v ∈ [FalconRingMember.s2 program, FalconRingBase.s1 program])
    {j : ℕ} (hj : j < 512) :
    program.evalE (program.reader e) 0 (.leaf v) j ∈ (I 0).node "GF(p^1)" := by
  obtain ⟨hvl, hsrc, hts, hty⟩ := FalconRingBase.primeVals (program := program) v hv
  have hsz : (program.value v).size = 512 := by
    rcases List.mem_pair.1 hv with rfl | rfl
    · exact (FalconRingMember.sizes (program := program)).2.2.2.2
    · exact (FalconRingBase.sizes (program := program)).1
  have hf : program.valueField v = 0 := by
    rcases List.mem_pair.1 hv with rfl | rfl
    · exact (FalconRingMember.fields (program := program)) _ (by simp)
    · exact FalconRingBase.s1Field (program := program)
  have hmem := hs.types v hvl hsrc hts j (by rw [hsz]; exact hj)
  rw [hty] at hmem
  exact castElt_mem_node_of_eq hf hmem

theorem prime_s2 {e : program.Env I} (hs : program.SourceSatAt e) (j : Fin falcon512.n) :
    s2Of e j ∈ (I 0).node "GF(p^1)" := by
  exact prime_of_mem hs (v := FalconRingMember.s2 program) (by simp) j.isLt

theorem prime_s1 {e : program.Env I} (hs : program.SourceSatAt e) (j : Fin falcon512.n) :
    s1Of e j ∈ (I 0).node "GF(p^1)" := prime_of_mem hs (v := FalconRingBase.s1 program) (by simp) j.isLt

/-- **The coefficients of a ring key** are the ring's entries read as naturals. -/
theorem keyCoeffs_ringKey (x : program.Valuation I) (r : ℕ) (j : Fin falcon512.n) :
    EmulatedAlgebraCircuit.keyCoeffs (ringKey x r).h j = (I 0).toNat (ringEntry x (r * 512 + j)) := by
  simp only [ringKey, EmulatedAlgebraCircuit.keyCoeffs, Falcon512.coeff_ofCoeff, ZMod.val_natCast]
  exact Nat.mod_eq_of_lt (AField.toNat_lt _)

/-- **The norm's obligation** (discharged per program by the generic norm, `FalconNorm`): advice
whose `s1` is `signature.s1`, at which the native norm and the encoding's checks hold on `s1 ‖ s2`
and the range requests hold. -/
def NormAdvice (e : program.Env I) : Prop :=
  ∃ alg : Committed (I 0).K, (∀ i, alg.s1 i = s1Of e i) ∧
    NativeNorm.Holds (Native.normInputs (fun i => s2Of e i) alg) alg.norm ∧
    NativeEncoding.BitsHold alg.norm ∧ AlgRequests alg

/-- **The norm's obligation wherever the source program holds.** -/
def NormSound : Prop := ∀ e : program.Env I, program.SourceSatAt e → NormAdvice e

/-- **The projection onto the prime field**: `x ↦ (toNat x : K)`, additive. -/
def primeProj : (I 0).K →+ (I 0).K :=
  (φq (FA := I 0)).toAddMonoidHom.comp (AField.coord0 (FA := I 0))

theorem primeProj_apply (x : (I 0).K) : primeProj x = (((I 0).toNat x : ℕ) : (I 0).K) := by
  simp only [primeProj, AddMonoidHom.coe_comp, Function.comp_apply, RingHom.toAddMonoidHom_eq_coe,
    AddMonoidHom.coe_coe, φq_apply, AField.toNat_eq]

theorem primeProj_mul_prime (a s : (I 0).K) (hs : (((I 0).toNat s : ℕ) : (I 0).K) = s) :
    primeProj (a * s) = primeProj a * s := by
  have hs' : φq (AField.coord0 s) = s := by
    rw [φq_apply, ← AField.toNat_eq, hs]
  simp only [primeProj, AddMonoidHom.coe_comp, Function.comp_apply, RingHom.toAddMonoidHom_eq_coe,
    AddMonoidHom.coe_coe]
  conv_lhs => rw [← hs', _root_.mul_comm, coord0_φq_mul]
  rw [map_mul, hs', _root_.mul_comm]

/-- **A prime-subfield element's projection** is itself. -/
theorem primeProj_prime {s : (I 0).K} (hs : (((I 0).toNat s : ℕ) : (I 0).K) = s) :
    primeProj s = s := by
  rw [primeProj_apply, hs]

theorem primeProj_negacyclic (h s2 : Fin falcon512.n → (I 0).K)
    (hs : ∀ j, (((I 0).toNat (s2 j) : ℕ) : (I 0).K) = s2 j) (k : Fin falcon512.n) :
    primeProj (LatticeCrypto.negacyclicConvCoeff h s2 k) =
      LatticeCrypto.negacyclicConvCoeff (fun j => primeProj (h j)) s2 k := by
  unfold LatticeCrypto.negacyclicConvCoeff
  rw [map_sum]
  refine Finset.sum_congr rfl fun ij _ => ?_
  split_ifs
  · exact primeProj_mul_prime _ _ (hs _)
  · rw [map_neg, primeProj_mul_prime _ _ (hs _)]
  · exact map_zero _

theorem decode_psi : (I 0).decode 10302 = psiF (I 0).K := by
  rw [AField.decode_lt _ (by norm_num)]
  rfl

theorem nttNatural_eq_negSpectrum (x : ℕ → (I 0).K) (k : Fin falcon512.n) :
    RealizedProgram.Ops.nttNatural 512 ((I 0).decode 10302) x k =
      DFT.negSpectrum (psiF (I 0).K) (fun j : Fin falcon512.n => x j) k := by
  rw [RealizedProgram.Ops.nttNatural_apply 512 _ _ k.isLt, decode_psi, DFT.negSpectrum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Nat.mul_comm]

/-- **The relation from the source program without the event** (`RealizedProgram.rbr_of_events`'
`hsound`), given the norm's obligation: the spectrum is the transform of the signer's row
(`spec_eq_of_not_event`), so the signature equation is `c − s1 = h · s2` over the field; its
projection onto the prime field is the ring's algebra at the signer's key (`RingAlgebra` at
`ringKey`), and `Native.ringAlgebra_sound` gives the relation. -/
theorem mem_rel_of_source (hN : NormSound (program := program) (I := I)) {e : program.Env I}
    (hs : program.SourceSatAt e) (hev : ¬ nativeEvent 0 e)
    (hev1 : ¬ nativeEvent (FalconRandomPoint.rChal program) e) :
    (e.stmt, proj e.stmt e.asg) ∈ rel := by
  obtain ⟨alg, hs1, hnorm, henc, hreq⟩ := hN e hs
  set pk := ringKey e.stmt (idxOf e) with hpk
  have hψ := Native.isPrimitiveRoot_psiF (I 0).K
  have hn0 := Native.natCast_n_ne_zero (I 0).K
  -- the signature equation over the field
  have hsig : (fun i : Fin falcon512.n => chalEntry e.stmt i - s1Of e i) =
      LatticeCrypto.negacyclicConvCoeff (fun j : Fin falcon512.n =>
        ringEntry e.stmt (idxOf e * 512 + j)) (fun i => s2Of e i) := by
    apply DFT.negSpectrum_injective hψ hn0
    rw [DFT.negSpectrum_negacyclicConvCoeff (Native.psiF_pow _)]
    funext k
    have h := sig_eq hs (fun hb => hev1 (Or.inr ⟨rfl, hb⟩)) k.isLt
    rw [spec_eq_of_not_event (memberPreds_of_source hs) (fun hb => hev (Or.inl hb)) k, keySpec, (FalconRingBase.consts (program := program)).2,
      nttNatural_eq_negSpectrum,
      nttNatural_eq_negSpectrum, nttNatural_eq_negSpectrum] at h
    exact h
  -- s1 and s2 are in the prime field
  have hs2p : ∀ j : Fin falcon512.n, (((I 0).toNat (s2Of e j) : ℕ) : (I 0).K) = s2Of e j :=
    fun j => AField.natCast_toNat (prime_s2 hs j)
  have hs1p : ∀ j : Fin falcon512.n, (((I 0).toNat (s1Of e j) : ℕ) : (I 0).K) = s1Of e j :=
    fun j => AField.natCast_toNat (prime_s1 hs j)
  -- its projection onto the prime field
  have hproj : (fun i : Fin falcon512.n => ((chalNat e.stmt i : ℕ) : (I 0).K) - alg.s1 i) =
      LatticeCrypto.negacyclicConvCoeff (fun j : Fin falcon512.n =>
        ((EmulatedAlgebraCircuit.keyCoeffs pk.h j : ℕ) : (I 0).K)) (fun i => s2Of e i) := by
    funext i
    have h := congrArg (fun f => primeProj (f i)) hsig
    simp only at h
    rw [map_sub, primeProj_prime (hs1p i), primeProj_negacyclic _ _ hs2p] at h
    rw [hs1, chalNat, ← primeProj_apply, h]
    congr 1
    funext j
    rw [primeProj_apply, hpk, keyCoeffs_ringKey]
  have halg : RingAlgebra (fun i => (chalNat e.stmt i : (I 0).K)) (keyRecord pk)
      (fun i => s2Of e i) alg := by
    refine ⟨fun k => ?_, hnorm, henc⟩
    have := congrArg (fun f => DFT.negSpectrum (psiF (I 0).K) f k) hproj
    rw [DFT.negSpectrum_negacyclicConvCoeff (Native.psiF_pow _)] at this
    exact this
  have hq : ∀ i, chalNat e.stmt i < 2 ^ falconSampleBits := fun i =>
    (AField.toNat_lt _).trans (by norm_num [falconSampleBits])
  obtain ⟨hok, hbd⟩ := Native.ringAlgebra_sound hq halg hreq
  refine ⟨by rw [proj_idx]; exact idxOf_lt e (memberPreds_of_source hs), ?_, ?_⟩
  · show Falcon512.algebraOk falcon512 (ringKey e.stmt (proj e.stmt e.asg).idx).h _
      (proj e.stmt e.asg).s2.toRq
    rw [proj_idx, proj_s2]
    have h2 := Emulated.decodeS2Int_toRq (fun i : Fin falcon512.n => s2Of e i)
    erw [h2]
    exact hok
  · show Falcon512.EncodingBounds falcon512 (proj e.stmt e.asg).s2
    rw [proj_s2]
    exact hbd

end Extract

/-! ## Round-by-round knowledge soundness of `Π_P₀` -/

section Rbr

variable {program : RealizedProgram} [FalconRingPowers program] [FalconRingSelect program]
  [FalconRingMember program] [FalconRingBase program] {I : RealizedProgram.Interp} [AField (I 0)]

/-- **The relation from the source program without the events** (`RealizedProgram.rbr_of_events`'
`hsound`), given the norm's obligation. -/
theorem sound_of_norm (hN : NormSound (program := program) (I := I)) :
    ∀ e : program.Env I, program.StatementOk I e.stmt → program.SourceSatAt e →
      (∀ j, program.IsSourceChal j → ¬ nativeEvent j e) → (e.stmt, proj e.stmt e.asg) ∈ rel :=
  fun _ _ hs hno =>
    mem_rel_of_source hN hs (hno 0 (FalconRingMember.isSourceChal_zero (program := program)))
      (hno _ ((FalconRandomPoint.isSourceChal_iff (program := program) _).2 (Or.inr rfl)))

/-- **Round-by-round knowledge soundness of `Π_P₀` for a native Falcon ring**
(`RealizedProgram.rbr_of_events`), given the norm's obligation (`NormSound`, discharged per program by the
generic norm): the relation `rel`, the extractor `extractor`, the errors `511/|F|` at
`member.ring.gamma`, `1022/|F|` at `signature.r` and `0` elsewhere (`nativeEps`). -/
theorem rbr_of_norm (hN : NormSound (program := program) (I := I)) :
    RBRKnowledgeSound rel (program.sourceVerifier I) extractor
      (program.eventState I rel proj nativeEvent nativeEvent_use (sound_of_norm hN))
      (program.roundError I (nativeEps (program := program) I)) :=
  program.rbr_of_events I rel proj nativeEvent (nativeEps (program := program) I) nativeEvent_use
    nativeEvent_bound
    (sound_of_norm hN)

end Rbr

end GordieHowe.Falcon512.Ring
