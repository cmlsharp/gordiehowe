-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.Program.FieldPackings
public import GordieHowe.Foundations.Fields.P256

@[expose] public section

/-!
# GordieHowe: the P-256 base field, read in Lean

The field interpretation (`FieldInterp`, `GordieHowe/Language/RealizedProgram/Semantics.lean`) of
`F_p256` (`GordieHowe.RealizedProgram.p256`), the field of domain `A` of `MDL.ECDSA.ROMParams`:
the registry entry `p256Entry`, Mathlib's `ZMod p` for the P-256 prime
(`GordieHowe/Foundations/Fields/P256.lean`); a constant is the cast of its natural (the C++
`Fp256` writes an element as its canonical value), and the integer reading is the value; every node
is the whole field (a prime field has no proper subfield); no bit coordinates.

* Its model at the prime node `F_p256` (`p256_model`: the domain's prime-subfield node is the field
  itself, `primeNodesOf`).
* Its code arithmetic (`p256_codeHom`): the arithmetic modulo `p` (`GKR.Fold.primeArith`), the
  arithmetic the GKR certificates of a degree-1 field read with the fast path `.withPrime p`
  (`lib/gordiehowe/compiler/emit_export.h`, `field_arith`; `p256Code_primeOn`).
* Its packing facts (`p256Packing`): `F_p = F_{p^1}`, no edges (the plan's packing tree of a prime
  field is the root alone), every node of degree `1`, the casts of the naturals below `p` as
  evaluation points (the registry's `points`), the integer skip domains, the nodes `0, 1, 2`.
-/

namespace GordieHowe.RealizedProgram

open Export RelativePacking P256

/-- **The nodes of `F_p256`**: every name the whole field. -/
def p256Node (_ : String) : AddSubgroup (ZMod P256.p) := ⊤

/-- **`F_p256` as a field of the program**: the registry entry `p256Entry`, `ZMod p`, constants as
casts, the integer reading the value, every node the whole field, no bit coordinates. -/
def p256 : FieldInterp where
  spec := p256Entry.spec
  K := ZMod P256.p
  decode c := (c : ZMod P256.p)
  toNat x := x.val
  node := p256Node
  memDec _ x := isTrue (AddSubgroup.mem_top x)
  coord _ _ _ := false

/-- The registry's characteristic of `F_p256` is the P-256 prime. -/
theorem p256_characteristic : p256.spec.characteristic = P256.p := P256.p_eq.symm

/-- **The model of `F_p256`** at its prime node `F_p256`: the registry entry `p256Entry`
(cardinality `p`, `ZMod.card`); the value of an element is below `p` and inverts the cast
(`ZMod.val_lt`, `ZMod.val_natCast`, `ZMod.natCast_zmod_val`). -/
theorem p256_model : p256.Model ["F_p256"] [] where
  entry := ⟨p256Entry, by simp [fieldRegistry], rfl⟩
  ringChar := by
    change _root_.ringChar (ZMod P256.p) = p256.spec.characteristic
    rw [ZMod.ringChar_zmod_n, p256_characteristic]
  card := by
    change Fintype.card (ZMod P256.p) = p256.spec.characteristic ^ 1
    rw [ZMod.card, p256_characteristic, pow_one]
  toNat_lt _ x := by
    change ZMod.val (n := P256.p) x < p256.spec.characteristic
    rw [p256_characteristic]
    exact ZMod.val_lt (n := P256.p) x
  toNat_natCast k hk := by
    change (k : ZMod P256.p).val = k
    rw [p256_characteristic] at hk
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt hk]
  decode_natCast _ _ := rfl
  natCast_toNat _ _ x _ := ZMod.natCast_zmod_val (n := P256.p) x
  rootNode := rfl
  bitNode _ hE := absurd hE List.not_mem_nil
  bitsAdditive := FieldInterp.bitsAdditive_of_noBits fun _ _ _ => rfl

/-- **The code arithmetic of `F_p256` is the arithmetic modulo `p`** (`FieldInterp.codeHom_cast`:
constants decode as casts). -/
theorem p256_codeHom :
    p256.CodeHom (GKR.Fold.primeArith
      115792089210356248762697446949407573530086143415290314195533631308867097853951) :=
  FieldInterp.codeHom_cast p256_model fun _ => rfl

/-- **`F_p256`'s arithmetic is arithmetic modulo `p`**, so its checks take the fast path
`.withPrime p` (`GKR.Fold.primeArith_primeOn`). -/
theorem p256Code_primeOn :
    (GKR.Fold.primeArith
      115792089210356248762697446949407573530086143415290314195533631308867097853951).PrimeOn
      115792089210356248762697446949407573530086143415290314195533631308867097853951 :=
  GKR.Fold.primeArith_primeOn _

/-- `F_p` is `F_{p^1}`: every element is fixed by `x ↦ x^p` (`ZMod.pow_card`). -/
theorem p256_top : fixedField (ZMod P256.p) P256.p 1 = ⊤ := by
  ext x
  simp only [Subfield.mem_top, iff_true]
  rw [mem_fixedField_iff_pow, pow_one]
  exact ZMod.pow_card x

/-- **A node of `F_p256` is `F_{p^1}`**: every node is the whole field. -/
theorem p256_node_eq (s : String) (m : ℕ) (h : (fun _ : String => some 1) s = some m) :
    ((p256Node s : AddSubgroup (ZMod P256.p)) : Set (ZMod P256.p)) =
      fixedField (ZMod P256.p) P256.p m := by
  cases h
  rw [p256Node, p256_top]
  rfl

/-- **The packing facts of `F_p256`** (see the module docstring). -/
def p256Packing : p256.Packing where
  p := P256.p
  expChar := inferInstanceAs (ExpChar (ZMod P256.p) P256.p)
  n := 1
  top_eq := p256_top
  s0 := 1
  decS0 := fun x => decidableMemFixedField (K := ZMod P256.p) x
  edge _ _ _ := none
  nodeDeg _ := some 1
  node_eq := p256_node_eq
  q := P256.p
  points := Ligero.Relative.Shape.natPoints (ZMod P256.p) P256.p
  points_mem _ := natCast_mem (fixedField (ZMod P256.p) P256.p 1) _
  coord_eq _ _ _ _ _ h := absurd h (by simp)
  bitsAdditive := FieldInterp.bitsAdditive_of_noBits fun _ _ _ => rfl
  skip := integerSkip (K := ZMod P256.p) P256.p
  nodes := some (Sumcheck.Nodes.zeroOneTwo (F := ZMod P256.p) P256.p P256.two_lt_p)

instance : p256.Packing := p256Packing

end GordieHowe.RealizedProgram
