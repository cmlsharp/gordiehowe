-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Card

@[expose] public section

/-!
# Finiteness of bytes and of core vectors

`UInt8` is the `256` values of `Fin 256`, and a core `Vector α n` is a function `Fin n → α`; both
equivalences give `Fintype` instances (computable). Candidates for upstreaming to Mathlib, which has
`Fintype` instances for `List.Vector` but not for core `Vector` or `UInt8`.
-/

/-- **`UInt8` is `Fin 256`** (`UInt8.toFin`, `UInt8.ofFin`). -/
def UInt8.equivFin : UInt8 ≃ Fin 256 where
  toFun := UInt8.toFin
  invFun := UInt8.ofFin
  left_inv _ := rfl
  right_inv _ := rfl

instance instFintypeUInt8_pQ : Fintype UInt8 := Fintype.ofEquiv _ UInt8.equivFin.symm

/-- **A core vector is a function on its indices** (`Vector.get`, `Vector.ofFn`). -/
def Vector.equivFun (α : Type*) (n : ℕ) : Vector α n ≃ (Fin n → α) where
  toFun v := v.get
  invFun f := Vector.ofFn f
  left_inv v := by
    ext i hi
    simp only [Vector.getElem_ofFn]
    rfl
  right_inv f := by
    funext i
    exact Vector.getElem_ofFn i.isLt

instance instFintypeVectorOfDecidableEq_pQ {α : Type*} [Fintype α] [DecidableEq α] (n : ℕ) :
    Fintype (Vector α n) :=
  Fintype.ofEquiv _ (Vector.equivFun α n).symm
