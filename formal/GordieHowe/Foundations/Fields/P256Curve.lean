-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import GordieHowe.Foundations.Fields.P256

@[expose] public section

/-!
# The curve P-256

The NIST curve P-256 (SEC 2 v2.0, §2.4.2, `secp256r1`; `third_party/longfellow/lib/ec/p256.h`)
as Mathlib's Weierstrass curve `y² = x³ − 3x + b` over `ZMod p` (`P256.curve`), an elliptic curve
(`P256.curve_Δ_ne_zero`), with its group of points in affine coordinates (Mathlib's
`WeierstrassCurve.Affine.Point`, whose addition is the chord-and-tangent law) and its base point
`G` (`P256.gen`).
-/

namespace GordieHowe.P256

/-- **The coefficient `b` of P-256** (SEC 2 v2.0, §2.4.2). -/
def b : ZMod p := 41058363725152142129326129780047268409114441015993725554835256314039467401291

/-- **P-256** as a Weierstrass curve: `y² = x³ − 3x + b` (`a₁ = a₂ = a₃ = 0`, `a₄ = −3`,
`a₆ = b`). -/
def curve : WeierstrassCurve (ZMod p) where
  a₁ := 0
  a₂ := 0
  a₃ := 0
  a₄ := -3
  a₆ := b

/-- **P-256 is an elliptic curve**: its discriminant `−16 (4 (−3)³ + 27 b²)` is not `0`. -/
theorem curve_Δ_ne_zero : curve.Δ ≠ 0 := by
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈, curve]
  decide +kernel

instance instIsEllipticCurve : curve.IsElliptic := ⟨isUnit_iff_ne_zero.2 curve_Δ_ne_zero⟩

/-- **The points of P-256**, in affine coordinates with the point at infinity. -/
abbrev Point : Type := curve.toAffine.Point

/-- **The point of the affine coordinates `(x, y)`**: the point when `(x, y)` lies on the curve,
none otherwise. -/
def ofAffine (x y : ZMod p) : Option Point :=
  if h : y ^ 2 + curve.a₁ * x * y + curve.a₃ * y = x ^ 3 + curve.a₂ * x ^ 2 + curve.a₄ * x + curve.a₆
  then some (WeierstrassCurve.Affine.Point.mk ((curve.toAffine.equation_iff x y).2 h))
  else none

/-- **The affine coordinates `(x, y)` give a point exactly when they satisfy the curve
equation.** -/
theorem ofAffine_isSome_iff (x y : ZMod p) :
    (ofAffine x y).isSome ↔ curve.toAffine.Equation x y := by
  rw [WeierstrassCurve.Affine.equation_iff, ofAffine]
  split_ifs with h
  · simpa using h
  · simpa using h

/-- The base point's `x`-coordinate (SEC 2 v2.0, §2.4.2). -/
def gx : ZMod p := 48439561293906451759052585252797914202762949526041747995844080717082404635286

/-- The base point's `y`-coordinate (SEC 2 v2.0, §2.4.2). -/
def gy : ZMod p := 36134250956749795798585127919587881956611106672985015071877198253568414405109

/-- The base point lies on the curve. -/
theorem gen_equation : curve.toAffine.Equation gx gy := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp only [curve, gx, gy, b]
  decide +kernel

/-- **The base point `G` of P-256.** -/
def gen : Point := WeierstrassCurve.Affine.Point.mk gen_equation

/-- **The base point is the point of its coordinates.** -/
theorem ofAffine_gx_gy : ofAffine gx gy = some gen := by
  unfold ofAffine
  split_ifs with h
  · rfl
  · exact absurd ((curve.toAffine.equation_iff gx gy).1 gen_equation) h

end GordieHowe.P256
