-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA44.Gadgets.UseHint
public import GordieHowe.Applications.MLDSA44.Gadgets.HintWeight
public import GordieHowe.Applications.MLDSA44.Gadgets.InfinityNorm
public import GordieHowe.Language.Realizations.Range
public import GordieHowe.Foundations.Algebra.IntLift
public import GordieHowe.Language.Realizations.MAC
public import GordieHowe.Applications.MLDSA44.Native.Rows
public import GordieHowe.Applications.Rows.MAC
public import GordieHowe.Foundations.Algebra.CheckOps
public import GordieHowe.Applications.MLDSA44.Circuits.Hash

@[expose] public section

/-!
# ML-DSA-44 native A circuit: indexing, crossing and extraction readings

The data of the A circuit of the flagship native ML-DSA-44 system (`MLDSANativeSystem` in
`lib/gordiehowe/examples/mldsa/mldsa_native.h`), over `Fp24_6 = F_q[x]/(x^6 − 7)`
(`MLDSANativeField6`), characteristic `q = 8380417`, generic in the MAC width `mw`, the taps and
the arm `A : MLDSANativeArm mldsa44 mw taps` (`B₁ = 512`; at `mw = 128`, `52` chunks and
`B₂ = 115`; at `mw = 256`, `26` chunks and `B₂ = 116`).

* `flat`: a two-index family read at a flat index.
* The crossing: `outputBits` (the UseHint output bits of a coefficient among the `w1` bits). The
  challenge's support and sign bits in MAC order and the MAC crossing are `GordieHowe.MLDSA44.HashCircuit.cBits` and
  `GordieHowe.MLDSA44.HashCircuit.crossBits`. The emulated arm (`GordieHowe.MLDSA44.Emulated`) uses these at its own wires.
* Extraction readings: `natRep`, `coeffRep` (the natural below `q` and the coefficient a wire
  denotes, with `natRep_cast`, `embed_coeffRep`, `coeffRep_eq_intCast`), `decodeHint` and
  `w1Coeff`.
-/

namespace GordieHowe.MLDSA44.NativeAlgebraCircuit

open Native.Rows

variable {F : Type*} [Field F] [DecidableEq F] {mw : ℕ} {taps : Finset ℕ}

/-! ### Indexing -/

/-- A two-index family read at the flat index `i·b + k` (`finProdFinEquiv`), the C++ loop
order `i` outer, `k` inner. -/
def flat {α : Type*} {a b : ℕ} (f : Fin a → Fin b → α) (m : Fin (a * b)) : α :=
  f (finProdFinEquiv.symm m).1 (finProdFinEquiv.symm m).2

@[simp] theorem flat_apply {α : Type*} {a b : ℕ} (f : Fin a → Fin b → α) (ik : Fin a × Fin b) :
    flat f (finProdFinEquiv ik) = f ik.1 ik.2 := by
  simp [flat]

/-! ### The crossing

The UseHint output bits and the MAC crossing are read from the committed `w1` bits and the
challenge's support and sign bits. The emulated arm (`Emulated`) commits the same data and
uses these definitions at its own wires. -/

/-- UseHint output bits of coefficient `m = i·N + k`: bits `r1_bits·m + b` of the `w1` bits
(`w1_tilde` in the native arm, `w1b` in the emulated arm). -/
def outputBits (w1 : BitWires F (8 * 768)) (m : Fin (nRows * deg)) :
    BitWires F mldsa44.r1_bits := fun b =>
  w1 ⟨mldsa44.r1_bits * m + b, by
    have hm := m.isLt
    have hb := b.isLt
    change (m : ℕ) < 4 * 256 at hm
    change (b : ℕ) < 6 at hb
    change 6 * (m : ℕ) + b < 8 * 768
    omega⟩

variable {A : NativeArm mldsa44 mw taps}

/-! ### Extraction -/

/-- The natural below `q` a wire is the cast of, or `0`. -/
-- spec-side
def natRep (v : F) : ℕ :=
  Range.natBelow _root_.MLDSA.modulus v

/-- The coefficient a wire denotes. -/
-- spec-side
def coeffRep (v : F) : _root_.MLDSA.Coeff := (natRep v : _root_.MLDSA.Coeff)

/-- A wire that is the cast of an integer is the cast of its extracted natural. -/
theorem natRep_cast [CharP F _root_.MLDSA.modulus] {v : F} {n : ℤ} (hn : (n : F) = v) :
    ((natRep v : ℕ) : F) = v := by
  have hex : Range.IsNatBelow _root_.MLDSA.modulus v :=
    ⟨(n : _root_.MLDSA.Coeff).val, ZMod.val_lt _, by rw [ZMod.natCast_val, ZMod.cast_intCast', hn]⟩
  exact (Range.natBelow_spec hex).2

theorem embed_coeffRep [CharP F _root_.MLDSA.modulus] {v : F} {n : ℤ} (hn : (n : F) = v) :
    embed (coeffRep v) = v := by
  rw [coeffRep, map_natCast]
  exact natRep_cast hn

theorem coeffRep_eq_intCast [CharP F _root_.MLDSA.modulus] {v : F} {n : ℤ} (hn : (n : F) = v) :
    coeffRep v = (n : _root_.MLDSA.Coeff) :=
  embed_injective ((embed_coeffRep hn).trans (by rw [map_intCast, hn]))

/-- The extracted hint bits. -/
-- spec-side
def decodeHint (hint : Fin nRows → Fin deg → F) (i : Fin nRows) (k : Fin deg) : Bool :=
  decide (hint i k = 1)

/-- The UseHint output of coefficient `(i, k)`, read from its `w1` bits. -/
-- spec-side
def w1Coeff (w1 : BitWires F (8 * 768)) (i : Fin nRows) (k : Fin deg) : ℕ :=
  Bits.natOfBits (outputBits w1 (finProdFinEquiv (i, k)))

end GordieHowe.MLDSA44.NativeAlgebraCircuit
