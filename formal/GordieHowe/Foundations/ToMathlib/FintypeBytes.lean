-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Card

@[expose] public section

/-!
# Finiteness of bytes and of core vectors

`UInt8` is the `256` values of `Fin 256`, and a core `Vector α n` is a function `Fin n → α`. The
equivalences count bytes and vectors (`Fintype.card_congr`) against any `Fintype` instance. The
instances themselves are VCVio's (`instFintypeVector`, and `FinEnum.instFintype` with its
`FinEnum UInt8`, in `VCVio/OracleComp/Constructions/SampleableType/Basic.lean`), so that one
instance is in scope everywhere.
-/

/-- **`UInt8` is `Fin 256`** (`UInt8.toFin`, `UInt8.ofFin`). -/
def UInt8.equivFin : UInt8 ≃ Fin 256 where
  toFun := UInt8.toFin
  invFun := UInt8.ofFin
  left_inv _ := rfl
  right_inv _ := rfl

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
