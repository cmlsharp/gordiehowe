-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

import GordieHowe.ProofSystem.GKR.CertificateBridge
import GordieHoweTest.GKRCertificate

/-!
# The bridge from the certificate's layered circuit to the GKR source circuit, on small circuits

For each small circuit of `GordieHoweTest.GKRCertificate` (the C++ test
`lib/circuits/compiler/cert_export_test.cc`), `decide +kernel` decides that every gate has at most
one assertion term (`uniqueAssertsB`) and the circuit's shape (`shapeB`, at the width and layer
count the plan export computes: `⌈log₂⌉` of the larger of the summed layer input widths and the
input count, and the number of layers). Together with the accepted certificate these give, for
every field and every input dimension `d` the inputs fit, that a vector satisfying the GKR source
circuit `toSource` makes every assertion of the DAG hold (`holds`), and the source's shape bound
(`shapeAtMost`). The checks reject a gate with two assertion terms, a layer wider than the width,
more layers than the bound, and a circuit without layers.
-/

namespace GordieHoweTest.GKRBridge

open GordieHowe.GKR.Certificate GordieHowe.GKR.CertificateBridge GordieHowe.RealizedProgram

namespace Add

open GordieHoweTest.GKRCertificate.Add

/-- Every gate has at most one assertion term. -/
theorem unique : uniqueAssertsB cert.width circuit = true := by decide +kernel

/-- The circuit has `1` layer(s) of at most `2 ^ 2` gates. -/
theorem shape : shapeB circuit 2 1 = true := by decide +kernel

/-- A vector satisfying the GKR source circuit makes every assertion of the DAG hold. -/
theorem holds {F : Type} [Field F] [DecidableEq F] {κ : ℕ → F} (hκ : κ 1 = 1) {d : ℕ}
    (hfit : circuit.inputs ≤ 2 ^ d) {v : Fin (2 ^ d) → F} (hv : vecRead v 0 = 1)
    (h : (toSource circuit cert.width κ d).Satisfied v) : dag.Holds cert.width κ (vecRead v) :=
  check_sound accepts hκ hv (toSource_satisfied unique hfit (readsBelow_of_check accepts) h)

/-- The GKR source circuit has at most `2 ^ 2` wires per layer and at most `1` layer(s). -/
theorem shapeAtMost {F : Type} [Field F] [DecidableEq F] {κ : ℕ → F} {d : ℕ} (hd : d ≤ 2) :
    (toSource circuit cert.width κ d).ShapeAtMost 2 1 :=
  toSource_shapeAtMost shape hd

end Add

namespace Mul

open GordieHoweTest.GKRCertificate.Mul

/-- Every gate has at most one assertion term. -/
theorem unique : uniqueAssertsB cert.width circuit = true := by decide +kernel

/-- The circuit has `1` layer(s) of at most `2 ^ 2` gates. -/
theorem shape : shapeB circuit 2 1 = true := by decide +kernel

/-- A vector satisfying the GKR source circuit makes every assertion of the DAG hold. -/
theorem holds {F : Type} [Field F] [DecidableEq F] {κ : ℕ → F} (hκ : κ 1 = 1) {d : ℕ}
    (hfit : circuit.inputs ≤ 2 ^ d) {v : Fin (2 ^ d) → F} (hv : vecRead v 0 = 1)
    (h : (toSource circuit cert.width κ d).Satisfied v) : dag.Holds cert.width κ (vecRead v) :=
  check_sound accepts hκ hv (toSource_satisfied unique hfit (readsBelow_of_check accepts) h)

/-- The GKR source circuit has at most `2 ^ 2` wires per layer and at most `1` layer(s). -/
theorem shapeAtMost {F : Type} [Field F] [DecidableEq F] {κ : ℕ → F} {d : ℕ} (hd : d ≤ 2) :
    (toSource circuit cert.width κ d).ShapeAtMost 2 1 :=
  toSource_shapeAtMost shape hd

end Mul

namespace Scale

open GordieHoweTest.GKRCertificate.Scale

/-- Every gate has at most one assertion term. -/
theorem unique : uniqueAssertsB cert.width circuit = true := by decide +kernel

/-- The circuit has `1` layer(s) of at most `2 ^ 2` gates. -/
theorem shape : shapeB circuit 2 1 = true := by decide +kernel

/-- A vector satisfying the GKR source circuit makes every assertion of the DAG hold. -/
theorem holds {F : Type} [Field F] [DecidableEq F] {κ : ℕ → F} (hκ : κ 1 = 1) {d : ℕ}
    (hfit : circuit.inputs ≤ 2 ^ d) {v : Fin (2 ^ d) → F} (hv : vecRead v 0 = 1)
    (h : (toSource circuit cert.width κ d).Satisfied v) : dag.Holds cert.width κ (vecRead v) :=
  check_sound accepts hκ hv (toSource_satisfied unique hfit (readsBelow_of_check accepts) h)

/-- The GKR source circuit has at most `2 ^ 2` wires per layer and at most `1` layer(s). -/
theorem shapeAtMost {F : Type} [Field F] [DecidableEq F] {κ : ℕ → F} {d : ℕ} (hd : d ≤ 2) :
    (toSource circuit cert.width κ d).ShapeAtMost 2 1 :=
  toSource_shapeAtMost shape hd

end Scale

namespace Copies

open GordieHoweTest.GKRCertificate.Copies

/-- Every gate has at most one assertion term. -/
theorem unique : uniqueAssertsB cert.width circuit = true := by decide +kernel

/-- The circuit has `4` layer(s) of at most `2 ^ 5` gates. -/
theorem shape : shapeB circuit 5 4 = true := by decide +kernel

/-- A vector satisfying the GKR source circuit makes every assertion of the DAG hold. -/
theorem holds {F : Type} [Field F] [DecidableEq F] {κ : ℕ → F} (hκ : κ 1 = 1) {d : ℕ}
    (hfit : circuit.inputs ≤ 2 ^ d) {v : Fin (2 ^ d) → F} (hv : vecRead v 0 = 1)
    (h : (toSource circuit cert.width κ d).Satisfied v) : dag.Holds cert.width κ (vecRead v) :=
  check_sound accepts hκ hv (toSource_satisfied unique hfit (readsBelow_of_check accepts) h)

/-- The GKR source circuit has at most `2 ^ 5` wires per layer and at most `4` layer(s). -/
theorem shapeAtMost {F : Type} [Field F] [DecidableEq F] {κ : ℕ → F} {d : ℕ} (hd : d ≤ 5) :
    (toSource circuit cert.width κ d).ShapeAtMost 5 4 :=
  toSource_shapeAtMost shape hd

end Copies

namespace Cse

open GordieHoweTest.GKRCertificate.Cse

/-- Every gate has at most one assertion term. -/
theorem unique : uniqueAssertsB cert.width circuit = true := by decide +kernel

/-- The circuit has `2` layer(s) of at most `2 ^ 3` gates. -/
theorem shape : shapeB circuit 3 2 = true := by decide +kernel

/-- A vector satisfying the GKR source circuit makes every assertion of the DAG hold. -/
theorem holds {F : Type} [Field F] [DecidableEq F] {κ : ℕ → F} (hκ : κ 1 = 1) {d : ℕ}
    (hfit : circuit.inputs ≤ 2 ^ d) {v : Fin (2 ^ d) → F} (hv : vecRead v 0 = 1)
    (h : (toSource circuit cert.width κ d).Satisfied v) : dag.Holds cert.width κ (vecRead v) :=
  check_sound accepts hκ hv (toSource_satisfied unique hfit (readsBelow_of_check accepts) h)

/-- The GKR source circuit has at most `2 ^ 3` wires per layer and at most `2` layer(s). -/
theorem shapeAtMost {F : Type} [Field F] [DecidableEq F] {κ : ℕ → F} {d : ℕ} (hd : d ≤ 3) :
    (toSource circuit cert.width κ d).ShapeAtMost 3 2 :=
  toSource_shapeAtMost shape hd

end Cse

namespace LastLayer

open GordieHoweTest.GKRCertificate.LastLayer

/-- Every gate has at most one assertion term. -/
theorem unique : uniqueAssertsB cert.width circuit = true := by decide +kernel

/-- The circuit has `1` layer(s) of at most `2 ^ 2` gates. -/
theorem shape : shapeB circuit 2 1 = true := by decide +kernel

/-- A vector satisfying the GKR source circuit makes every assertion of the DAG hold. -/
theorem holds {F : Type} [Field F] [DecidableEq F] {κ : ℕ → F} (hκ : κ 1 = 1) {d : ℕ}
    (hfit : circuit.inputs ≤ 2 ^ d) {v : Fin (2 ^ d) → F} (hv : vecRead v 0 = 1)
    (h : (toSource circuit cert.width κ d).Satisfied v) : dag.Holds cert.width κ (vecRead v) :=
  check_sound accepts hκ hv (toSource_satisfied unique hfit (readsBelow_of_check accepts) h)

/-- The GKR source circuit has at most `2 ^ 2` wires per layer and at most `1` layer(s). -/
theorem shapeAtMost {F : Type} [Field F] [DecidableEq F] {κ : ℕ → F} {d : ℕ} (hd : d ≤ 2) :
    (toSource circuit cert.width κ d).ShapeAtMost 2 1 :=
  toSource_shapeAtMost shape hd

end LastLayer

namespace OutputAnInput

open GordieHoweTest.GKRCertificate.OutputAnInput

/-- Every gate has at most one assertion term. -/
theorem unique : uniqueAssertsB cert.width circuit = true := by decide +kernel

/-- The circuit has `1` layer(s) of at most `2 ^ 2` gates. -/
theorem shape : shapeB circuit 2 1 = true := by decide +kernel

/-- A vector satisfying the GKR source circuit makes every assertion of the DAG hold. -/
theorem holds {F : Type} [Field F] [DecidableEq F] {κ : ℕ → F} (hκ : κ 1 = 1) {d : ℕ}
    (hfit : circuit.inputs ≤ 2 ^ d) {v : Fin (2 ^ d) → F} (hv : vecRead v 0 = 1)
    (h : (toSource circuit cert.width κ d).Satisfied v) : dag.Holds cert.width κ (vecRead v) :=
  check_sound accepts hκ hv (toSource_satisfied unique hfit (readsBelow_of_check accepts) h)

/-- The GKR source circuit has at most `2 ^ 2` wires per layer and at most `1` layer(s). -/
theorem shapeAtMost {F : Type} [Field F] [DecidableEq F] {κ : ℕ → F} {d : ℕ} (hd : d ≤ 2) :
    (toSource circuit cert.width κ d).ShapeAtMost 2 1 :=
  toSource_shapeAtMost shape hd

end OutputAnInput

namespace AliasLinearCopy

open GordieHoweTest.GKRCertificate.AliasLinearCopy

/-- Every gate has at most one assertion term. -/
theorem unique : uniqueAssertsB cert.width circuit = true := by decide +kernel

/-- The circuit has `1` layer(s) of at most `2 ^ 1` gates. -/
theorem shape : shapeB circuit 1 1 = true := by decide +kernel

/-- A vector satisfying the GKR source circuit makes every assertion of the DAG hold. -/
theorem holds {F : Type} [Field F] [DecidableEq F] {κ : ℕ → F} (hκ : κ 1 = 1) {d : ℕ}
    (hfit : circuit.inputs ≤ 2 ^ d) {v : Fin (2 ^ d) → F} (hv : vecRead v 0 = 1)
    (h : (toSource circuit cert.width κ d).Satisfied v) : dag.Holds cert.width κ (vecRead v) :=
  check_sound accepts hκ hv (toSource_satisfied unique hfit (readsBelow_of_check accepts) h)

/-- The GKR source circuit has at most `2 ^ 1` wires per layer and at most `1` layer(s). -/
theorem shapeAtMost {F : Type} [Field F] [DecidableEq F] {κ : ℕ → F} {d : ℕ} (hd : d ≤ 1) :
    (toSource circuit cert.width κ d).ShapeAtMost 1 1 :=
  toSource_shapeAtMost shape hd

end AliasLinearCopy

namespace Assert0

open GordieHoweTest.GKRCertificate.Assert0

/-- Every gate has at most one assertion term. -/
theorem unique : uniqueAssertsB cert.width circuit = true := by decide +kernel

/-- The circuit has `1` layer(s) of at most `2 ^ 2` gates. -/
theorem shape : shapeB circuit 2 1 = true := by decide +kernel

/-- A vector satisfying the GKR source circuit makes every assertion of the DAG hold. -/
theorem holds {F : Type} [Field F] [DecidableEq F] {κ : ℕ → F} (hκ : κ 1 = 1) {d : ℕ}
    (hfit : circuit.inputs ≤ 2 ^ d) {v : Fin (2 ^ d) → F} (hv : vecRead v 0 = 1)
    (h : (toSource circuit cert.width κ d).Satisfied v) : dag.Holds cert.width κ (vecRead v) :=
  check_sound accepts hκ hv (toSource_satisfied unique hfit (readsBelow_of_check accepts) h)

/-- The GKR source circuit has at most `2 ^ 2` wires per layer and at most `1` layer(s). -/
theorem shapeAtMost {F : Type} [Field F] [DecidableEq F] {κ : ℕ → F} {d : ℕ} (hd : d ≤ 2) :
    (toSource circuit cert.width κ d).ShapeAtMost 2 1 :=
  toSource_shapeAtMost shape hd

end Assert0

namespace Canonicalization

open GordieHoweTest.GKRCertificate.Canonicalization

/-- Every gate has at most one assertion term. -/
theorem unique : uniqueAssertsB cert.width circuit = true := by decide +kernel

/-- The circuit has `2` layer(s) of at most `2 ^ 3` gates. -/
theorem shape : shapeB circuit 3 2 = true := by decide +kernel

/-- A vector satisfying the GKR source circuit makes every assertion of the DAG hold. -/
theorem holds {F : Type} [Field F] [DecidableEq F] {κ : ℕ → F} (hκ : κ 1 = 1) {d : ℕ}
    (hfit : circuit.inputs ≤ 2 ^ d) {v : Fin (2 ^ d) → F} (hv : vecRead v 0 = 1)
    (h : (toSource circuit cert.width κ d).Satisfied v) : dag.Holds cert.width κ (vecRead v) :=
  check_sound accepts hκ hv (toSource_satisfied unique hfit (readsBelow_of_check accepts) h)

/-- The GKR source circuit has at most `2 ^ 3` wires per layer and at most `2` layer(s). -/
theorem shapeAtMost {F : Type} [Field F] [DecidableEq F] {κ : ℕ → F} {d : ℕ} (hd : d ≤ 3) :
    (toSource circuit cert.width κ d).ShapeAtMost 3 2 :=
  toSource_shapeAtMost shape hd

end Canonicalization

namespace MatMul

open GordieHoweTest.GKRCertificate.MatMul

/-- Every gate has at most one assertion term. -/
theorem unique : uniqueAssertsB cert.width circuit = true := by decide +kernel

/-- The circuit has `4` layer(s) of at most `2 ^ 6` gates. -/
theorem shape : shapeB circuit 6 4 = true := by decide +kernel

/-- A vector satisfying the GKR source circuit makes every assertion of the DAG hold. -/
theorem holds {F : Type} [Field F] [DecidableEq F] {κ : ℕ → F} (hκ : κ 1 = 1) {d : ℕ}
    (hfit : circuit.inputs ≤ 2 ^ d) {v : Fin (2 ^ d) → F} (hv : vecRead v 0 = 1)
    (h : (toSource circuit cert.width κ d).Satisfied v) : dag.Holds cert.width κ (vecRead v) :=
  check_sound accepts hκ hv (toSource_satisfied unique hfit (readsBelow_of_check accepts) h)

/-- The GKR source circuit has at most `2 ^ 6` wires per layer and at most `4` layer(s). -/
theorem shapeAtMost {F : Type} [Field F] [DecidableEq F] {κ : ℕ → F} {d : ℕ} (hd : d ≤ 6) :
    (toSource circuit cert.width κ d).ShapeAtMost 6 4 :=
  toSource_shapeAtMost shape hd

end MatMul

/-- Accepted: a gate with one assertion term among two terms. -/
example : uniqueAssertsB 4 ⟨4, [[0x311210704]]⟩ = true := by decide +kernel

/-- Rejected: a gate with two assertion terms. -/
example : uniqueAssertsB 4 ⟨4, [[0x311210704], [0x310210704]]⟩ = false := by decide +kernel

/-- Rejected: the matrix product's input layer has more than `2 ^ 3` gates. -/
example : shapeB GordieHoweTest.GKRCertificate.MatMul.circuit 3 4 = false := by decide +kernel

/-- Rejected: the copies circuit has more than three layers. -/
example : shapeB GordieHoweTest.GKRCertificate.Copies.circuit 5 3 = false := by decide +kernel

/-- Rejected: a circuit without layers. -/
example : shapeB ⟨4, []⟩ 4 4 = false := by decide +kernel

end GordieHoweTest.GKRBridge
