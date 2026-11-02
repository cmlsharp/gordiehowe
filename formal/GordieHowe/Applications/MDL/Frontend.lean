-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.FieldInterps.P256
public import GordieHowe.Applications.Falcon512.Frontend.Fields
public import GordieHowe.Foundations.Fields.P256Curve

@[expose] public section

/-!
# GordieHowe frontend: the opaque functions of the ECDSA mDL

Domain `A` of the ECDSA mDL (`lib/gordiehowe/examples/mdoc/mdoc_signatures.h`) reads two public
values that both parties compute from the statement, as opaque functions of the program
(`Interp.opaqueFn`) over P-256 (`GordieHowe/Foundations/Fields/P256Curve.lean`):

* **`device.e2_point`** (`e2Point`, `ecdsa_verify_private_key`, `computes("p256_g_mult")`): the
  point `[u] G` for the digest `u` of the statement's two 128-bit halves `(lo, hi)`,
  `u = lo + 2^128 hi` (`of_halves`, the low 128 bits of each), in the coordinates of
  `host::public_point` (`lib/gordiehowe/examples/p256/p256_ecdsa_witness.h`): `(0, 1, 0)` for the
  point at infinity, `(x, y, 1)` otherwise. The C++ `host::g_mult` sums the generator's
  fixed-base table entries with longfellow's complete projective formulas
  (`third_party/longfellow/lib/ec/elliptic_curve.h`, Renes–Costello–Batina), so its result is the
  group sum `[u] G`.
* **`issuer.q_table`** (`qTable`, `issuer_verification`, `computes("p256_fixed_base_table")`): the
  fixed-base table of the issuer key `Q` (`host::fb_table`): entry `16 j + k` (`j < 64`, `k < 16`)
  the affine coordinates `(x, y)` of `[(k + 2) 16^j] Q` at coordinates `2 (16 j + k)` and
  `2 (16 j + k) + 1`, then `K_I = K_G + K_Q` (`K_B = −[2M] B`, `M = Σ_{j<64} 16^j`,
  `fbOffset`) in `public_point`'s coordinates at `2048, 2049, 2050`. For a key on the curve every
  table entry is a point other than infinity (`(k + 2) 16^j` and `2M` are not multiples of the
  group order), so the C++ batch normalization returns its affine coordinates. A key off the curve
  (a statement the member check `p256_affine_point` rejects) reads `0` at every coordinate.

`mdocOps` reads these two names and every other name as `targetBitsFn` (`mac.target_bits`). The
coordinates are the values of the elements of `ZMod p`, the C++ encoding of `F_p256`
(`GordieHowe.RealizedProgram.p256`).
-/

namespace GordieHowe.RealizedProgram

open P256

/-- **The coordinates of a point as `host::public_point` writes them**: `(0, 1, 0)` for the point
at infinity, `(x, y, 1)` for the affine point `(x, y)`; coordinate `c` as a natural, `0` past the
third. -/
def p256ProjCoord : P256.Point → ℕ → ℕ
  | .zero, c => if c = 1 then 1 else 0
  | .some x y _, c => if c = 0 then x.val else if c = 1 then y.val else if c = 2 then 1 else 0

/-- **The affine coordinates of a point**: `(x, y)` for the affine point `(x, y)`, `(0, 0)` for the
point at infinity; coordinate `c` as a natural, `0` past the second. -/
def p256AffineCoord : P256.Point → ℕ → ℕ
  | .zero, _ => 0
  | .some x y _, c => if c = 0 then x.val else if c = 1 then y.val else 0

/-- **The fixed-base table's digit sum** `M = Σ_{j<64} 16^j`. -/
def fbDigitSum : ℕ := ∑ j ∈ Finset.range 64, 16 ^ j

/-- **The fixed-base table's offset of a base `B`**: `K_B = −[2M] B` (`host::fb_table`). -/
def fbOffset (B : P256.Point) : P256.Point := -((2 * fbDigitSum) • B)

/-- **Entry `i` of the fixed-base table of a base `B`**: `[(k + 2) 16^j] B` for `i = 16 j + k`,
`k < 16` (`host::fb_table`). -/
def fbEntry (B : P256.Point) (i : ℕ) : P256.Point := ((i % 16 + 2) * 16 ^ (i / 16)) • B

/-- **The opaque function `device.e2_point`**: coordinate `i` of `[u] G` in `public_point`'s
coordinates, `u = lo + 2^128 hi` for the first argument's coordinates `lo` and `hi`, each read
modulo `2^128` (see the module docstring). -/
def e2Point (xs : List (ℕ → ℕ)) (i : ℕ) : ℕ :=
  p256ProjCoord (((xs.headD 0) 0 % 2 ^ 128 + 2 ^ 128 * ((xs.headD 0) 1 % 2 ^ 128)) • gen) i

set_option compiler.extract_closed false in
/-- **The opaque function `issuer.q_table`**: for the first argument's coordinates `(x, y)` a
point `Q` of the curve, coordinate `i < 2048` the affine coordinate `i mod 2` of table entry
`⌊i / 2⌋` (`fbEntry Q`), coordinates `2048, 2049, 2050` the offset `K_G + K_Q` in
`public_point`'s coordinates, `0` past them; `0` everywhere when `(x, y)` is not on the curve (see
the module docstring). -/
def qTable (xs : List (ℕ → ℕ)) (i : ℕ) : ℕ :=
  match ofAffine ((xs.headD 0) 0) ((xs.headD 0) 1) with
  | some Q =>
    if i < 2048 then p256AffineCoord (fbEntry Q (i / 2)) (i % 2)
    else p256ProjCoord (fbOffset gen + fbOffset Q) (i - 2048)
  | none => 0

/-- **The opaque functions of the ECDSA mDL**: `device.e2_point` (`e2Point`), `issuer.q_table`
(`qTable`), every other name as `targetBitsFn` (`mac.target_bits`). -/
def mdocOps (nm : String) (xs : List (ℕ → ℕ)) (i : ℕ) : ℕ :=
  if nm = "device.e2_point" then e2Point xs i
  else if nm = "issuer.q_table" then qTable xs i
  else targetBitsFn nm xs i

/-- **`device.e2_point` is `e2Point`.** -/
theorem mdocOps_e2Point (xs : List (ℕ → ℕ)) (i : ℕ) :
    mdocOps "device.e2_point" xs i = e2Point xs i := by
  simp [mdocOps]

/-- **`issuer.q_table` is `qTable`.** -/
theorem mdocOps_qTable (xs : List (ℕ → ℕ)) (i : ℕ) :
    mdocOps "issuer.q_table" xs i = qTable xs i := by
  simp [mdocOps]

/-- **The names of the ECDSA mDL's point-valued opaque functions.** -/
def mdocPointOps : List String := ["device.e2_point", "issuer.q_table"]

/-- **Every other opaque function of the ECDSA mDL returns a bit** (`targetBitsFn_lt_two`). -/
theorem mdocOps_lt_two_of_not_mem {nm : String} (h : nm ∉ mdocPointOps) (xs : List (ℕ → ℕ))
    (i : ℕ) : mdocOps nm xs i < 2 := by
  simp only [mdocPointOps, List.mem_cons, List.not_mem_nil, or_false, not_or] at h
  simp only [mdocOps, h.1, h.2, ite_false]
  exact targetBitsFn_lt_two nm xs i

/-- **The opaque `Bit` values of the ECDSA mDL return bits** (`Interp.OpaqueBit`): given, decided
per program, that no opaque `Bit` value computed from arguments is point-valued. -/
theorem mdocOps_opaqueBit {I : Interp} (hI : I.opaqueFn = mdocOps) {ir : RealizedProgram}
    (h : ∀ v < ir.values.length, (ir.value v).type = .bit →
      (ir.value v).kind.opaqueArgsName ∉ mdocPointOps) :
    I.OpaqueBit ir := by
  intro v hv name args hk hne hb xs i
  rw [hI]
  refine mdocOps_lt_two_of_not_mem ?_ xs i
  have := h v hv hb
  rw [hk] at this
  cases args with
  | nil => exact absurd rfl hne
  | cons a as => exact this

/-- **`mac.target_bits` of the ECDSA mDL returns the bits of its argument's first coordinate.** -/
theorem mdocOps_target_bits (xs : List (ℕ → ℕ)) (i : ℕ) :
    mdocOps "mac.target_bits" xs i = if ((xs.headD 0) 0).testBit i then 1 else 0 := by
  rw [← targetBitsFn_target]
  simp [mdocOps]

end GordieHowe.RealizedProgram
