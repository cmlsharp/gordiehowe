-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.RealizedProgram

@[expose] public section

/-!
# Value kinds read by `decide`

`RealizedProgram.Kind` has no decidable equality (`Kind.bound` holds an `Expr`, a nested
inductive). A fact `(ir.value v).kind = .bits w sel` or `= .priv` about a generated program is
then a definitional unfolding of the value table, which the elaborator cannot reach at the indices
of a large program. The `Bool` and `Option` readings below have decidable values, so such facts are
decided by the kernel and read back:

* **the bit view of a kind** (`Kind.bits?`: the source and selection of `bits w sel`), with
  `Kind.eq_bits_of_bits?`;
* **a `priv` kind** (`Kind.isPriv`), with `Kind.eq_priv_of_isPriv`;
* **an opaque statement value** (`Kind.opaque?`: the name and arguments of `pub (opaque name args)`),
  with `Kind.eq_opaque_of_opaque?`;
* **a value bound to an expression** (`Kind.isBoundTo`: `bound e` at an expression equal to `e` by
  `Expr.beq`), with `Kind.eq_bound_of_isBoundTo`.
-/

namespace GordieHowe.RealizedProgram

/-- **The source and selection of a bit view** (`Kind.bits w sel`); none for any other kind. -/
def Kind.bits? : Kind → Option (Nat × IndexMap)
  | .bits w sel => some (w, sel)
  | _ => none

/-- **A kind whose bit view is `(w, sel)` is `bits w sel`.** -/
theorem Kind.eq_bits_of_bits? {k : Kind} {w : Nat} {sel : IndexMap}
    (h : k.bits? = some (w, sel)) : k = .bits w sel := by
  cases k <;> simp_all [Kind.bits?]

/-- **A kind that is `priv` by `isPriv` is `priv`.** -/
theorem Kind.eq_priv_of_isPriv {k : Kind} (h : k.isPriv = true) : k = .priv := by
  cases k <;> simp_all [Kind.isPriv]

/-- **The name and arguments of an opaque statement value** (`Kind.pub (.opaque name args)`); none
for any other kind. -/
def Kind.opaque? : Kind → Option (String × List Nat)
  | .pub (.opaque name args) => some (name, args)
  | _ => none

/-- **A kind whose opaque reading is `(name, args)` is `pub (opaque name args)`.** -/
theorem Kind.eq_opaque_of_opaque? {k : Kind} {name : String} {args : List Nat}
    (h : k.opaque? = some (name, args)) : k = .pub (.opaque name args) := by
  rcases k with _ | d | _ | _ | _ | _ | _ | _ | _ <;> simp [Kind.opaque?] at h
  rcases d <;> simp_all

/-- **Whether a kind is `bound e`**: `bound e'` with `e'` equal to `e` by `Expr.beq`. -/
def Kind.isBoundTo (k : Kind) (e : Expr) : Bool :=
  match k with
  | .bound e' => e'.beq e
  | _ => false

/-- **A kind bound to `e` by `isBoundTo` is `bound e`.** -/
theorem Kind.eq_bound_of_isBoundTo {k : Kind} {e : Expr} (h : k.isBoundTo e = true) :
    k = .bound e := by
  cases k <;> simp only [Kind.isBoundTo, Bool.false_eq_true] at h
  rw [Expr.eq_of_beq h]

end GordieHowe.RealizedProgram
