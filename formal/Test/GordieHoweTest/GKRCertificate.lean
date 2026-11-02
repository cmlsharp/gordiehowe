-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

import GordieHowe.ProofSystem.GKR.Certificate

/-!
# The GKR compiler certificate checker on small circuits

Generated from the C++ test `lib/circuits/compiler/cert_export_test.cc` (its certificates, kept
with `GH_GKR_CERT_TEST_DIR`); do not edit. For each circuit (hand-built ones, and Longfellow's
`compiler_test.cc` / `canonicalization_test.cc` circuits) the honest certificate is accepted
(`GordieHowe.GKR.Certificate.check` by `decide +kernel`), and each mutation that applies to it is
rejected: a wrong wire-to-node entry, a gate term reading the wrong wire, a wrong constant index, a
dropped copy wire, a missing assertion, an extra assertion.
-/

namespace GordieHoweTest.GKRCertificate

open GordieHowe.GKR.Certificate NTree

namespace Add

/-- The DAG. -/
def dag : Dag := ⟨(node
(leaf 0x3022011016)
(leaf 0x6002)), 4, 8, [7], []⟩

/-- The layered circuit. -/
def circuit : Layered := ⟨4, [[0x302201101606]]⟩

/-- The certificate. -/
def cert : Cert := ⟨4, [(.packed 2 (leaf 0x6))], [(0, 7)], []⟩

/-- The honest certificate is accepted. -/
theorem accepts : check dag circuit cert = true := by decide +kernel

/-- Hence the DAG's assertions and outputs hold where the circuit is satisfied. -/
theorem sound {F : Type*} [CommSemiring F] {κ x : ℕ → F} (hκ : κ 1 = 1) (hx : x 0 = 1)
    (hs : circuit.Satisfied cert.width κ x) : dag.Holds cert.width κ x :=
  check_sound accepts hκ hx hs

/-- Rejected: a wire's table entry (and its gate's node field) names another node. -/
example : check (⟨(node
(leaf 0x3022011016)
(leaf 0x6002)), 4, 8, [7], []⟩ : Dag)
    (⟨4, [[0x302201101706]]⟩ : Layered)
    (⟨4, [(.packed 2 (leaf 0x7))], [(0, 7)], []⟩ : Cert) = false := by
  decide +kernel

/-- Rejected: a gate term reads the wrong wire. -/
example : check (⟨(node
(leaf 0x3022011016)
(leaf 0x6002)), 4, 8, [7], []⟩ : Dag)
    (⟨4, [[0x302201121606]]⟩ : Layered)
    (⟨4, [(.packed 2 (leaf 0x6))], [(0, 7)], []⟩ : Cert) = false := by
  decide +kernel

/-- Rejected: a gate term's constant index differs from its node's. -/
example : check (⟨(node
(leaf 0x3022011016)
(leaf 0x6002)), 4, 8, [7], []⟩ : Dag)
    (⟨4, [[0x302201102606]]⟩ : Layered)
    (⟨4, [(.packed 2 (leaf 0x6))], [(0, 7)], []⟩ : Cert) = false := by
  decide +kernel

/-- Rejected: an asserted node is left out of the DAG's list. -/
example : check (⟨(node
(leaf 0x3022011016)
(leaf 0x6002)), 4, 8, [], []⟩ : Dag)
    (⟨4, [[0x302201101606]]⟩ : Layered)
    (⟨4, [(.packed 2 (leaf 0x6))], [(0, 7)], []⟩ : Cert) = false := by
  decide +kernel

/-- Rejected: a node with no assertion term is listed as asserted. -/
example : check (⟨(node
(leaf 0x3022011016)
(leaf 0x6002)), 4, 8, [6, 7], []⟩ : Dag)
    (⟨4, [[0x302201101606]]⟩ : Layered)
    (⟨4, [(.packed 2 (leaf 0x6))], [(0, 7)], []⟩ : Cert) = false := by
  decide +kernel

end Add

namespace Mul

/-- The DAG. -/
def dag : Dag := ⟨(node
(leaf 0x3022114)
(leaf 0x6002)), 4, 8, [7], []⟩

/-- The layered circuit. -/
def circuit : Layered := ⟨4, [[0x302211604]]⟩

/-- The certificate. -/
def cert : Cert := ⟨4, [(.packed 2 (leaf 0x6))], [(0, 7)], []⟩

/-- The honest certificate is accepted. -/
theorem accepts : check dag circuit cert = true := by decide +kernel

/-- Hence the DAG's assertions and outputs hold where the circuit is satisfied. -/
theorem sound {F : Type*} [CommSemiring F] {κ x : ℕ → F} (hκ : κ 1 = 1) (hx : x 0 = 1)
    (hs : circuit.Satisfied cert.width κ x) : dag.Holds cert.width κ x :=
  check_sound accepts hκ hx hs

/-- Rejected: a wire's table entry (and its gate's node field) names another node. -/
example : check (⟨(node
(leaf 0x3022114)
(leaf 0x6002)), 4, 8, [7], []⟩ : Dag)
    (⟨4, [[0x302211704]]⟩ : Layered)
    (⟨4, [(.packed 2 (leaf 0x7))], [(0, 7)], []⟩ : Cert) = false := by
  decide +kernel

/-- Rejected: a gate term reads the wrong wire. -/
example : check (⟨(node
(leaf 0x3022114)
(leaf 0x6002)), 4, 8, [7], []⟩ : Dag)
    (⟨4, [[0x302201604]]⟩ : Layered)
    (⟨4, [(.packed 2 (leaf 0x6))], [(0, 7)], []⟩ : Cert) = false := by
  decide +kernel

/-- Rejected: a gate term's constant index differs from its node's. -/
example : check (⟨(node
(leaf 0x3022114)
(leaf 0x6002)), 4, 8, [7], []⟩ : Dag)
    (⟨4, [[0x302212604]]⟩ : Layered)
    (⟨4, [(.packed 2 (leaf 0x6))], [(0, 7)], []⟩ : Cert) = false := by
  decide +kernel

/-- Rejected: an asserted node is left out of the DAG's list. -/
example : check (⟨(node
(leaf 0x3022114)
(leaf 0x6002)), 4, 8, [], []⟩ : Dag)
    (⟨4, [[0x302211604]]⟩ : Layered)
    (⟨4, [(.packed 2 (leaf 0x6))], [(0, 7)], []⟩ : Cert) = false := by
  decide +kernel

/-- Rejected: a node with no assertion term is listed as asserted. -/
example : check (⟨(node
(leaf 0x3022114)
(leaf 0x6002)), 4, 8, [6, 7], []⟩ : Dag)
    (⟨4, [[0x302211604]]⟩ : Layered)
    (⟨4, [(.packed 2 (leaf 0x6))], [(0, 7)], []⟩ : Cert) = false := by
  decide +kernel

end Mul

namespace Scale

/-- The DAG. -/
def dag : Dag := ⟨(node
(leaf 0xa02)
(leaf 0x83214)), 3, 7, [6], []⟩

/-- The layered circuit. -/
def circuit : Layered := ⟨3, [[0x20c8544]]⟩

/-- The certificate. -/
def cert : Cert := ⟨3, [(.packed 2 (leaf 0x5))], [(0, 6)], []⟩

/-- The honest certificate is accepted. -/
theorem accepts : check dag circuit cert = true := by decide +kernel

/-- Hence the DAG's assertions and outputs hold where the circuit is satisfied. -/
theorem sound {F : Type*} [CommSemiring F] {κ x : ℕ → F} (hκ : κ 1 = 1) (hx : x 0 = 1)
    (hs : circuit.Satisfied cert.width κ x) : dag.Holds cert.width κ x :=
  check_sound accepts hκ hx hs

/-- Rejected: a wire's table entry (and its gate's node field) names another node. -/
example : check (⟨(node
(leaf 0xa02)
(leaf 0x83214)), 3, 7, [6], []⟩ : Dag)
    (⟨3, [[0x20c8584]]⟩ : Layered)
    (⟨3, [(.packed 2 (leaf 0x6))], [(0, 6)], []⟩ : Cert) = false := by
  decide +kernel

/-- Rejected: a gate term reads the wrong wire. -/
example : check (⟨(node
(leaf 0xa02)
(leaf 0x83214)), 3, 7, [6], []⟩ : Dag)
    (⟨3, [[0x20ca544]]⟩ : Layered)
    (⟨3, [(.packed 2 (leaf 0x5))], [(0, 6)], []⟩ : Cert) = false := by
  decide +kernel

/-- Rejected: a gate term's constant index differs from its node's. -/
example : check (⟨(node
(leaf 0xa02)
(leaf 0x83214)), 3, 7, [6], []⟩ : Dag)
    (⟨3, [[0x20c8744]]⟩ : Layered)
    (⟨3, [(.packed 2 (leaf 0x5))], [(0, 6)], []⟩ : Cert) = false := by
  decide +kernel

/-- Rejected: an asserted node is left out of the DAG's list. -/
example : check (⟨(node
(leaf 0xa02)
(leaf 0x83214)), 3, 7, [], []⟩ : Dag)
    (⟨3, [[0x20c8544]]⟩ : Layered)
    (⟨3, [(.packed 2 (leaf 0x5))], [(0, 6)], []⟩ : Cert) = false := by
  decide +kernel

/-- Rejected: a node with no assertion term is listed as asserted. -/
example : check (⟨(node
(leaf 0xa02)
(leaf 0x83214)), 3, 7, [5, 6], []⟩ : Dag)
    (⟨3, [[0x20c8544]]⟩ : Layered)
    (⟨3, [(.packed 2 (leaf 0x5))], [(0, 6)], []⟩ : Cert) = false := by
  decide +kernel

end Scale

namespace Copies

/-- The DAG. -/
def dag : Dag := ⟨(node
(node
(node
(leaf 0x78002)
(leaf 0x59022))
(leaf 0x48002))
(node
(leaf 0x180210424)
(node
(leaf 0x38c22)
(node
(leaf 0x10422)
(leaf 0x318128044))))), 7, 17, [10, 16], []⟩

/-- The layered circuit. -/
def circuit : Layered := ⟨7, [[0x8003, 0x6008c23, 0x8009043, 0xa009463, 0x4109c82, 0x6008410a4a4], [0x8003, 0x4009023, 0x6009443, 0xa002862, 0x810ac82], [0x8003, 0x4009423, 0x810b042], [0x21042013c04]]⟩

/-- The certificate. -/
def cert : Cert := ⟨5, [(.packed 2 (node
(leaf 0x29060)
(leaf 0x127))), (.packed 2 (node
(leaf 0x51480)
(leaf 0xb))), (.packed 2 (leaf 0x30a0)), (.packed 2 (leaf 0xf))], [(0, 16)], []⟩

/-- The honest certificate is accepted. -/
theorem accepts : check dag circuit cert = true := by decide +kernel

/-- Hence the DAG's assertions and outputs hold where the circuit is satisfied. -/
theorem sound {F : Type*} [CommSemiring F] {κ x : ℕ → F} (hκ : κ 1 = 1) (hx : x 0 = 1)
    (hs : circuit.Satisfied cert.width κ x) : dag.Holds cert.width κ x :=
  check_sound accepts hκ hx hs

/-- Rejected: a wire's table entry (and its gate's node field) names another node. -/
example : check (⟨(node
(node
(node
(leaf 0x78002)
(leaf 0x59022))
(leaf 0x48002))
(node
(leaf 0x180210424)
(node
(leaf 0x38c22)
(node
(leaf 0x10422)
(leaf 0x318128044))))), 7, 17, [10, 16], []⟩ : Dag)
    (⟨7, [[0x8003, 0x6008c23, 0x8009043, 0xa009463, 0x410a082, 0x6008410a4a4], [0x8003, 0x4009023, 0x6009443, 0xa002862, 0x810ac82], [0x8003, 0x4009423, 0x810b042], [0x21042013c04]]⟩ : Layered)
    (⟨5, [(.packed 2 (node
(leaf 0x29060)
(leaf 0x128))), (.packed 2 (node
(leaf 0x51480)
(leaf 0xb))), (.packed 2 (leaf 0x30a0)), (.packed 2 (leaf 0xf))], [(0, 16)], []⟩ : Cert) = false := by
  decide +kernel

/-- Rejected: a gate term reads the wrong wire. -/
example : check (⟨(node
(node
(node
(leaf 0x78002)
(leaf 0x59022))
(leaf 0x48002))
(node
(leaf 0x180210424)
(node
(leaf 0x38c22)
(node
(leaf 0x10422)
(leaf 0x318128044))))), 7, 17, [10, 16], []⟩ : Dag)
    (⟨7, [[0x8003, 0x6008c23, 0x8009043, 0xa009463, 0x4009c82, 0x6008410a4a4], [0x8003, 0x4009023, 0x6009443, 0xa002862, 0x810ac82], [0x8003, 0x4009423, 0x810b042], [0x21042013c04]]⟩ : Layered)
    (⟨5, [(.packed 2 (node
(leaf 0x29060)
(leaf 0x127))), (.packed 2 (node
(leaf 0x51480)
(leaf 0xb))), (.packed 2 (leaf 0x30a0)), (.packed 2 (leaf 0xf))], [(0, 16)], []⟩ : Cert) = false := by
  decide +kernel

/-- Rejected: a gate term's constant index differs from its node's. -/
example : check (⟨(node
(node
(node
(leaf 0x78002)
(leaf 0x59022))
(leaf 0x48002))
(node
(leaf 0x180210424)
(node
(leaf 0x38c22)
(node
(leaf 0x10422)
(leaf 0x318128044))))), 7, 17, [10, 16], []⟩ : Dag)
    (⟨7, [[0x8003, 0x6008c23, 0x8009043, 0xa009463, 0x4111c82, 0x6008410a4a4], [0x8003, 0x4009023, 0x6009443, 0xa002862, 0x810ac82], [0x8003, 0x4009423, 0x810b042], [0x21042013c04]]⟩ : Layered)
    (⟨5, [(.packed 2 (node
(leaf 0x29060)
(leaf 0x127))), (.packed 2 (node
(leaf 0x51480)
(leaf 0xb))), (.packed 2 (leaf 0x30a0)), (.packed 2 (leaf 0xf))], [(0, 16)], []⟩ : Cert) = false := by
  decide +kernel

/-- Rejected: a copy wire is left out. -/
example : check (⟨(node
(node
(node
(leaf 0x78002)
(leaf 0x59022))
(leaf 0x48002))
(node
(leaf 0x180210424)
(node
(leaf 0x38c22)
(node
(leaf 0x10422)
(leaf 0x318128044))))), 7, 17, [10, 16], []⟩ : Dag)
    (⟨7, [[0x6008c03, 0x8009023, 0xa009443, 0x4109c62, 0x6008410a484], [0x8003, 0x4009023, 0x6009443, 0xa002862, 0x810ac82], [0x8003, 0x4009423, 0x810b042], [0x21042013c04]]⟩ : Layered)
    (⟨5, [(.packed 2 (node
(leaf 0x39483)
(leaf 0x9))), (.packed 2 (node
(leaf 0x51480)
(leaf 0xb))), (.packed 2 (leaf 0x30a0)), (.packed 2 (leaf 0xf))], [(0, 16)], []⟩ : Cert) = false := by
  decide +kernel

/-- Rejected: an asserted node is left out of the DAG's list. -/
example : check (⟨(node
(node
(node
(leaf 0x78002)
(leaf 0x59022))
(leaf 0x48002))
(node
(leaf 0x180210424)
(node
(leaf 0x38c22)
(node
(leaf 0x10422)
(leaf 0x318128044))))), 7, 17, [16], []⟩ : Dag)
    (⟨7, [[0x8003, 0x6008c23, 0x8009043, 0xa009463, 0x4109c82, 0x6008410a4a4], [0x8003, 0x4009023, 0x6009443, 0xa002862, 0x810ac82], [0x8003, 0x4009423, 0x810b042], [0x21042013c04]]⟩ : Layered)
    (⟨5, [(.packed 2 (node
(leaf 0x29060)
(leaf 0x127))), (.packed 2 (node
(leaf 0x51480)
(leaf 0xb))), (.packed 2 (leaf 0x30a0)), (.packed 2 (leaf 0xf))], [(0, 16)], []⟩ : Cert) = false := by
  decide +kernel

/-- Rejected: a node with no assertion term is listed as asserted. -/
example : check (⟨(node
(node
(node
(leaf 0x78002)
(leaf 0x59022))
(leaf 0x48002))
(node
(leaf 0x180210424)
(node
(leaf 0x38c22)
(node
(leaf 0x10422)
(leaf 0x318128044))))), 7, 17, [7, 10, 16], []⟩ : Dag)
    (⟨7, [[0x8003, 0x6008c23, 0x8009043, 0xa009463, 0x4109c82, 0x6008410a4a4], [0x8003, 0x4009023, 0x6009443, 0xa002862, 0x810ac82], [0x8003, 0x4009423, 0x810b042], [0x21042013c04]]⟩ : Layered)
    (⟨5, [(.packed 2 (node
(leaf 0x29060)
(leaf 0x127))), (.packed 2 (node
(leaf 0x51480)
(leaf 0xb))), (.packed 2 (leaf 0x30a0)), (.packed 2 (leaf 0xf))], [(0, 16)], []⟩ : Cert) = false := by
  decide +kernel

end Copies

namespace Cse

/-- The DAG. -/
def dag : Dag := ⟨(node
(leaf 0x9002)
(node
(node
(leaf 0x5425314)
(leaf 0x2112))
nil)), 5, 11, [10], []⟩

/-- The layered circuit. -/
def circuit : Layered := ⟨5, [[0x301303, 0x401413, 0x211522], [0x212201904]]⟩

/-- The certificate. -/
def cert : Cert := ⟨4, [(.packed 2 (leaf 0x543)), (.packed 2 (leaf 0x9))], [(0, 10)], []⟩

/-- The honest certificate is accepted. -/
theorem accepts : check dag circuit cert = true := by decide +kernel

/-- Hence the DAG's assertions and outputs hold where the circuit is satisfied. -/
theorem sound {F : Type*} [CommSemiring F] {κ x : ℕ → F} (hκ : κ 1 = 1) (hx : x 0 = 1)
    (hs : circuit.Satisfied cert.width κ x) : dag.Holds cert.width κ x :=
  check_sound accepts hκ hx hs

/-- Rejected: a wire's table entry (and its gate's node field) names another node. -/
example : check (⟨(node
(leaf 0x9002)
(node
(node
(leaf 0x5425314)
(leaf 0x2112))
nil)), 5, 11, [10], []⟩ : Dag)
    (⟨5, [[0x301303, 0x401413, 0x211622], [0x212201904]]⟩ : Layered)
    (⟨4, [(.packed 2 (leaf 0x643)), (.packed 2 (leaf 0x9))], [(0, 10)], []⟩ : Cert) = false := by
  decide +kernel

/-- Rejected: a gate term reads the wrong wire. -/
example : check (⟨(node
(leaf 0x9002)
(node
(node
(leaf 0x5425314)
(leaf 0x2112))
nil)), 5, 11, [10], []⟩ : Dag)
    (⟨5, [[0x301303, 0x401413, 0x201522], [0x212201904]]⟩ : Layered)
    (⟨4, [(.packed 2 (leaf 0x543)), (.packed 2 (leaf 0x9))], [(0, 10)], []⟩ : Cert) = false := by
  decide +kernel

/-- Rejected: a gate term's constant index differs from its node's. -/
example : check (⟨(node
(leaf 0x9002)
(node
(node
(leaf 0x5425314)
(leaf 0x2112))
nil)), 5, 11, [10], []⟩ : Dag)
    (⟨5, [[0x301303, 0x401413, 0x212522], [0x212201904]]⟩ : Layered)
    (⟨4, [(.packed 2 (leaf 0x543)), (.packed 2 (leaf 0x9))], [(0, 10)], []⟩ : Cert) = false := by
  decide +kernel

/-- Rejected: a copy wire is left out. -/
example : check (⟨(node
(leaf 0x9002)
(node
(node
(leaf 0x5425314)
(leaf 0x2112))
nil)), 5, 11, [10], []⟩ : Dag)
    (⟨5, [[0x401403, 0x211512], [0x212201904]]⟩ : Layered)
    (⟨4, [(.packed 2 (leaf 0x54)), (.packed 2 (leaf 0x9))], [(0, 10)], []⟩ : Cert) = false := by
  decide +kernel

/-- Rejected: an asserted node is left out of the DAG's list. -/
example : check (⟨(node
(leaf 0x9002)
(node
(node
(leaf 0x5425314)
(leaf 0x2112))
nil)), 5, 11, [], []⟩ : Dag)
    (⟨5, [[0x301303, 0x401413, 0x211522], [0x212201904]]⟩ : Layered)
    (⟨4, [(.packed 2 (leaf 0x543)), (.packed 2 (leaf 0x9))], [(0, 10)], []⟩ : Cert) = false := by
  decide +kernel

/-- Rejected: a node with no assertion term is listed as asserted. -/
example : check (⟨(node
(leaf 0x9002)
(node
(node
(leaf 0x5425314)
(leaf 0x2112))
nil)), 5, 11, [5, 10], []⟩ : Dag)
    (⟨5, [[0x301303, 0x401413, 0x211522], [0x212201904]]⟩ : Layered)
    (⟨4, [(.packed 2 (leaf 0x543)), (.packed 2 (leaf 0x9))], [(0, 10)], []⟩ : Cert) = false := by
  decide +kernel

end Cse

namespace LastLayer

/-- The DAG. -/
def dag : Dag := ⟨(node
(node
nil
(node
(leaf 0x3211024)
(leaf 0x3022114)))
(node
nil
(node
(leaf 0xa002)
(leaf 0x6002)))), 4, 12, [7, 11], []⟩

/-- The layered circuit. -/
def circuit : Layered := ⟨4, [[0x302211604, 0x321102a14]]⟩

/-- The certificate. -/
def cert : Cert := ⟨4, [(.packed 2 (leaf 0xa6))], [(0, 7), (1, 11)], []⟩

/-- The honest certificate is accepted. -/
theorem accepts : check dag circuit cert = true := by decide +kernel

/-- Hence the DAG's assertions and outputs hold where the circuit is satisfied. -/
theorem sound {F : Type*} [CommSemiring F] {κ x : ℕ → F} (hκ : κ 1 = 1) (hx : x 0 = 1)
    (hs : circuit.Satisfied cert.width κ x) : dag.Holds cert.width κ x :=
  check_sound accepts hκ hx hs

/-- Rejected: a wire's table entry (and its gate's node field) names another node. -/
example : check (⟨(node
(node
nil
(node
(leaf 0x3211024)
(leaf 0x3022114)))
(node
nil
(node
(leaf 0xa002)
(leaf 0x6002)))), 4, 12, [7, 11], []⟩ : Dag)
    (⟨4, [[0x302211704, 0x321102a14]]⟩ : Layered)
    (⟨4, [(.packed 2 (leaf 0xa7))], [(0, 7), (1, 11)], []⟩ : Cert) = false := by
  decide +kernel

/-- Rejected: a gate term reads the wrong wire. -/
example : check (⟨(node
(node
nil
(node
(leaf 0x3211024)
(leaf 0x3022114)))
(node
nil
(node
(leaf 0xa002)
(leaf 0x6002)))), 4, 12, [7, 11], []⟩ : Dag)
    (⟨4, [[0x302201604, 0x321102a14]]⟩ : Layered)
    (⟨4, [(.packed 2 (leaf 0xa6))], [(0, 7), (1, 11)], []⟩ : Cert) = false := by
  decide +kernel

/-- Rejected: a gate term's constant index differs from its node's. -/
example : check (⟨(node
(node
nil
(node
(leaf 0x3211024)
(leaf 0x3022114)))
(node
nil
(node
(leaf 0xa002)
(leaf 0x6002)))), 4, 12, [7, 11], []⟩ : Dag)
    (⟨4, [[0x302212604, 0x321102a14]]⟩ : Layered)
    (⟨4, [(.packed 2 (leaf 0xa6))], [(0, 7), (1, 11)], []⟩ : Cert) = false := by
  decide +kernel

/-- Rejected: an asserted node is left out of the DAG's list. -/
example : check (⟨(node
(node
nil
(node
(leaf 0x3211024)
(leaf 0x3022114)))
(node
nil
(node
(leaf 0xa002)
(leaf 0x6002)))), 4, 12, [11], []⟩ : Dag)
    (⟨4, [[0x302211604, 0x321102a14]]⟩ : Layered)
    (⟨4, [(.packed 2 (leaf 0xa6))], [(0, 7), (1, 11)], []⟩ : Cert) = false := by
  decide +kernel

/-- Rejected: a node with no assertion term is listed as asserted. -/
example : check (⟨(node
(node
nil
(node
(leaf 0x3211024)
(leaf 0x3022114)))
(node
nil
(node
(leaf 0xa002)
(leaf 0x6002)))), 4, 12, [6, 7, 11], []⟩ : Dag)
    (⟨4, [[0x302211604, 0x321102a14]]⟩ : Layered)
    (⟨4, [(.packed 2 (leaf 0xa6))], [(0, 7), (1, 11)], []⟩ : Cert) = false := by
  decide +kernel

end LastLayer

namespace OutputAnInput

/-- The DAG. -/
def dag : Dag := ⟨(leaf 0x68a), 4, 5, [], [1, 4]⟩

/-- The layered circuit. -/
def circuit : Layered := ⟨4, [[0x8243, 0x1a30a]]⟩

/-- The certificate. -/
def cert : Cert := ⟨3, [(.packed 2 (leaf 0x21))], [], [0, 1]⟩

/-- The honest certificate is accepted. -/
theorem accepts : check dag circuit cert = true := by decide +kernel

/-- Hence the DAG's assertions and outputs hold where the circuit is satisfied. -/
theorem sound {F : Type*} [CommSemiring F] {κ x : ℕ → F} (hκ : κ 1 = 1) (hx : x 0 = 1)
    (hs : circuit.Satisfied cert.width κ x) : dag.Holds cert.width κ x :=
  check_sound accepts hκ hx hs

/-- Rejected: a wire's table entry (and its gate's node field) names another node. -/
example : check (⟨(leaf 0x68a), 4, 5, [], [1, 4]⟩ : Dag)
    (⟨4, [[0x8243, 0x1a34a]]⟩ : Layered)
    (⟨3, [(.packed 2 (leaf 0x29))], [], [0, 1]⟩ : Cert) = false := by
  decide +kernel

/-- Rejected: a gate term reads the wrong wire. -/
example : check (⟨(leaf 0x68a), 4, 5, [], [1, 4]⟩ : Dag)
    (⟨4, [[0x8243, 0x1830a]]⟩ : Layered)
    (⟨3, [(.packed 2 (leaf 0x21))], [], [0, 1]⟩ : Cert) = false := by
  decide +kernel

/-- Rejected: a gate term's constant index differs from its node's. -/
example : check (⟨(leaf 0x68a), 4, 5, [], [1, 4]⟩ : Dag)
    (⟨4, [[0x8243, 0x1a50a]]⟩ : Layered)
    (⟨3, [(.packed 2 (leaf 0x21))], [], [0, 1]⟩ : Cert) = false := by
  decide +kernel

/-- Rejected: a copy wire is left out. -/
example : check (⟨(leaf 0x68a), 4, 5, [], [1, 4]⟩ : Dag)
    (⟨4, [[0x1a302]]⟩ : Layered)
    (⟨3, [(.packed 2 (leaf 0x4))], [], [0, 1]⟩ : Cert) = false := by
  decide +kernel

/-- Rejected: a node with no assertion term is listed as asserted. -/
example : check (⟨(leaf 0x68a), 4, 5, [4], [1, 4]⟩ : Dag)
    (⟨4, [[0x8243, 0x1a30a]]⟩ : Layered)
    (⟨3, [(.packed 2 (leaf 0x21))], [], [0, 1]⟩ : Cert) = false := by
  decide +kernel

end OutputAnInput

namespace AliasLinearCopy

/-- The DAG. -/
def dag : Dag := ⟨(leaf 0x46), 2, 3, [], [1, 2]⟩

/-- The layered circuit. -/
def circuit : Layered := ⟨2, [[0x453, 0x466]]⟩

/-- The certificate. -/
def cert : Cert := ⟨2, [(.packed 2 (leaf 0x9))], [], [0, 1]⟩

/-- The honest certificate is accepted. -/
theorem accepts : check dag circuit cert = true := by decide +kernel

/-- Hence the DAG's assertions and outputs hold where the circuit is satisfied. -/
theorem sound {F : Type*} [CommSemiring F] {κ x : ℕ → F} (hκ : κ 1 = 1) (hx : x 0 = 1)
    (hs : circuit.Satisfied cert.width κ x) : dag.Holds cert.width κ x :=
  check_sound accepts hκ hx hs

/-- Rejected: a wire's table entry (and its gate's node field) names another node. -/
example : check (⟨(leaf 0x46), 2, 3, [], [1, 2]⟩ : Dag)
    (⟨2, [[0x453, 0x476]]⟩ : Layered)
    (⟨2, [(.packed 2 (leaf 0xd))], [], [0, 1]⟩ : Cert) = false := by
  decide +kernel

/-- Rejected: a gate term's constant index differs from its node's. -/
example : check (⟨(leaf 0x46), 2, 3, [], [1, 2]⟩ : Dag)
    (⟨2, [[0x453, 0x4a6]]⟩ : Layered)
    (⟨2, [(.packed 2 (leaf 0x9))], [], [0, 1]⟩ : Cert) = false := by
  decide +kernel

/-- Rejected: a copy wire is left out. -/
example : check (⟨(leaf 0x46), 2, 3, [], [1, 2]⟩ : Dag)
    (⟨2, [[0x462]]⟩ : Layered)
    (⟨2, [(.packed 2 (leaf 0x2))], [], [0, 1]⟩ : Cert) = false := by
  decide +kernel

/-- Rejected: a node with no assertion term is listed as asserted. -/
example : check (⟨(leaf 0x46), 2, 3, [2], [1, 2]⟩ : Dag)
    (⟨2, [[0x453, 0x466]]⟩ : Layered)
    (⟨2, [(.packed 2 (leaf 0x9))], [], [0, 1]⟩ : Cert) = false := by
  decide +kernel

end AliasLinearCopy

namespace Assert0

/-- The DAG. -/
def dag : Dag := ⟨(node
(leaf 0x3022011016)
(leaf 0x6002)), 4, 8, [7], []⟩

/-- The layered circuit. -/
def circuit : Layered := ⟨4, [[0x302201101606]]⟩

/-- The certificate. -/
def cert : Cert := ⟨4, [(.packed 2 (leaf 0x6))], [(0, 7)], []⟩

/-- The honest certificate is accepted. -/
theorem accepts : check dag circuit cert = true := by decide +kernel

/-- Hence the DAG's assertions and outputs hold where the circuit is satisfied. -/
theorem sound {F : Type*} [CommSemiring F] {κ x : ℕ → F} (hκ : κ 1 = 1) (hx : x 0 = 1)
    (hs : circuit.Satisfied cert.width κ x) : dag.Holds cert.width κ x :=
  check_sound accepts hκ hx hs

/-- Rejected: a wire's table entry (and its gate's node field) names another node. -/
example : check (⟨(node
(leaf 0x3022011016)
(leaf 0x6002)), 4, 8, [7], []⟩ : Dag)
    (⟨4, [[0x302201101706]]⟩ : Layered)
    (⟨4, [(.packed 2 (leaf 0x7))], [(0, 7)], []⟩ : Cert) = false := by
  decide +kernel

/-- Rejected: a gate term reads the wrong wire. -/
example : check (⟨(node
(leaf 0x3022011016)
(leaf 0x6002)), 4, 8, [7], []⟩ : Dag)
    (⟨4, [[0x302201121606]]⟩ : Layered)
    (⟨4, [(.packed 2 (leaf 0x6))], [(0, 7)], []⟩ : Cert) = false := by
  decide +kernel

/-- Rejected: a gate term's constant index differs from its node's. -/
example : check (⟨(node
(leaf 0x3022011016)
(leaf 0x6002)), 4, 8, [7], []⟩ : Dag)
    (⟨4, [[0x302201102606]]⟩ : Layered)
    (⟨4, [(.packed 2 (leaf 0x6))], [(0, 7)], []⟩ : Cert) = false := by
  decide +kernel

/-- Rejected: an asserted node is left out of the DAG's list. -/
example : check (⟨(node
(leaf 0x3022011016)
(leaf 0x6002)), 4, 8, [], []⟩ : Dag)
    (⟨4, [[0x302201101606]]⟩ : Layered)
    (⟨4, [(.packed 2 (leaf 0x6))], [(0, 7)], []⟩ : Cert) = false := by
  decide +kernel

/-- Rejected: a node with no assertion term is listed as asserted. -/
example : check (⟨(node
(leaf 0x3022011016)
(leaf 0x6002)), 4, 8, [6, 7], []⟩ : Dag)
    (⟨4, [[0x302201101606]]⟩ : Layered)
    (⟨4, [(.packed 2 (leaf 0x6))], [(0, 7)], []⟩ : Cert) = false := by
  decide +kernel

end Assert0

namespace Canonicalization

/-- The DAG. -/
def dag : Dag := ⟨(node
(node
(leaf 0x6512)
(leaf 0x2112))
(leaf 0x4312)), 5, 9, [], [8]⟩

/-- The layered circuit. -/
def circuit : Layered := ⟨5, [[0x211602, 0x431512], [0x11802]]⟩

/-- The certificate. -/
def cert : Cert := ⟨4, [(.packed 2 (leaf 0x56)), (.packed 2 (leaf 0x8))], [], [0]⟩

/-- The honest certificate is accepted. -/
theorem accepts : check dag circuit cert = true := by decide +kernel

/-- Hence the DAG's assertions and outputs hold where the circuit is satisfied. -/
theorem sound {F : Type*} [CommSemiring F] {κ x : ℕ → F} (hκ : κ 1 = 1) (hx : x 0 = 1)
    (hs : circuit.Satisfied cert.width κ x) : dag.Holds cert.width κ x :=
  check_sound accepts hκ hx hs

/-- Rejected: a wire's table entry (and its gate's node field) names another node. -/
example : check (⟨(node
(node
(leaf 0x6512)
(leaf 0x2112))
(leaf 0x4312)), 5, 9, [], [8]⟩ : Dag)
    (⟨5, [[0x211702, 0x431512], [0x11802]]⟩ : Layered)
    (⟨4, [(.packed 2 (leaf 0x57)), (.packed 2 (leaf 0x8))], [], [0]⟩ : Cert) = false := by
  decide +kernel

/-- Rejected: a gate term reads the wrong wire. -/
example : check (⟨(node
(node
(leaf 0x6512)
(leaf 0x2112))
(leaf 0x4312)), 5, 9, [], [8]⟩ : Dag)
    (⟨5, [[0x201602, 0x431512], [0x11802]]⟩ : Layered)
    (⟨4, [(.packed 2 (leaf 0x56)), (.packed 2 (leaf 0x8))], [], [0]⟩ : Cert) = false := by
  decide +kernel

/-- Rejected: a gate term's constant index differs from its node's. -/
example : check (⟨(node
(node
(leaf 0x6512)
(leaf 0x2112))
(leaf 0x4312)), 5, 9, [], [8]⟩ : Dag)
    (⟨5, [[0x212602, 0x431512], [0x11802]]⟩ : Layered)
    (⟨4, [(.packed 2 (leaf 0x56)), (.packed 2 (leaf 0x8))], [], [0]⟩ : Cert) = false := by
  decide +kernel

/-- Rejected: a node with no assertion term is listed as asserted. -/
example : check (⟨(node
(node
(leaf 0x6512)
(leaf 0x2112))
(leaf 0x4312)), 5, 9, [5], [8]⟩ : Dag)
    (⟨5, [[0x211602, 0x431512], [0x11802]]⟩ : Layered)
    (⟨4, [(.packed 2 (leaf 0x56)), (.packed 2 (leaf 0x8))], [], [0]⟩ : Cert) = false := by
  decide +kernel

end Canonicalization

namespace MatMul

/-- The DAG. -/
def dag : Dag := ⟨(node
(node
(node
(node
(leaf 0x14201444044)
(leaf 0x2c201a44044))
(node
(leaf 0x81c1144044)
(leaf 0x20201744044)))
(node
(node
(leaf 0x262018c4044)
(leaf 0xe2012c4044))
(node
(leaf 0x1a2015c4044)
(leaf 0x80c1101044))))
(node
(node
(node
(leaf 0x7181142044)
(leaf 0x20181742044))
(node
(leaf 0x2c181a42044)
(leaf 0x14181442044)))
(node
(node
(leaf 0x1a1815c2044)
(leaf 0x60c1081044))
(node
(leaf 0xe1812c2044)
(leaf 0x261818c2044))))), 9, 57, [], [47, 50, 53, 56]⟩

/-- The layered circuit. -/
def circuit : Layered := ⟨9, [[0x40003, 0x80042043, 0x100044083, 0x1800460c3, 0x200048103, 0x60c108104b144, 0x80c110104e184, 0x71811420511c4, 0x81c1144054204], [0x40003, 0x40042043, 0x80044083, 0xc00460c3, 0x100048103, 0x60c1141057144, 0x80c11c105d184, 0x610114205a1c4, 0x81011c2060204], [0x40042003, 0x80044043, 0xc0046083, 0x1000480c3, 0x70c1141063104, 0x80c1181069144, 0x7101142066184, 0x810118206c1c4], [0x608110006f004, 0x60c1101072044, 0x7081140075084, 0x70c11410780c4]]⟩

/-- The certificate. -/
def cert : Cert := ⟨6, [(.packed 2 (node
(node
(leaf 0x184080)
(leaf 0x14))
(leaf 0x44e2c8))), (.packed 2 (node
(node
(leaf 0x184080)
(leaf 0x20))
(leaf 0x69d5c8))), (.packed 2 (node
(leaf 0x206102)
(leaf 0xb26a63))), (.packed 2 (leaf 0xe35caf))], [], [0, 1, 2, 3]⟩

/-- The honest certificate is accepted. -/
theorem accepts : check dag circuit cert = true := by decide +kernel

/-- Hence the DAG's assertions and outputs hold where the circuit is satisfied. -/
theorem sound {F : Type*} [CommSemiring F] {κ x : ℕ → F} (hκ : κ 1 = 1) (hx : x 0 = 1)
    (hs : circuit.Satisfied cert.width κ x) : dag.Holds cert.width κ x :=
  check_sound accepts hκ hx hs

/-- Rejected: a wire's table entry (and its gate's node field) names another node. -/
example : check (⟨(node
(node
(node
(node
(leaf 0x14201444044)
(leaf 0x2c201a44044))
(node
(leaf 0x81c1144044)
(leaf 0x20201744044)))
(node
(node
(leaf 0x262018c4044)
(leaf 0xe2012c4044))
(node
(leaf 0x1a2015c4044)
(leaf 0x80c1101044))))
(node
(node
(node
(leaf 0x7181142044)
(leaf 0x20181742044))
(node
(leaf 0x2c181a42044)
(leaf 0x14181442044)))
(node
(node
(leaf 0x1a1815c2044)
(leaf 0x60c1081044))
(node
(leaf 0xe1812c2044)
(leaf 0x261818c2044))))), 9, 57, [], [47, 50, 53, 56]⟩ : Dag)
    (⟨9, [[0x40003, 0x80042043, 0x100044083, 0x1800460c3, 0x200048103, 0x60c108104c144, 0x80c110104e184, 0x71811420511c4, 0x81c1144054204], [0x40003, 0x40042043, 0x80044083, 0xc00460c3, 0x100048103, 0x60c1141057144, 0x80c11c105d184, 0x610114205a1c4, 0x81011c2060204], [0x40042003, 0x80044043, 0xc0046083, 0x1000480c3, 0x70c1141063104, 0x80c1181069144, 0x7101142066184, 0x810118206c1c4], [0x608110006f004, 0x60c1101072044, 0x7081140075084, 0x70c11410780c4]]⟩ : Layered)
    (⟨6, [(.packed 2 (node
(node
(leaf 0x184080)
(leaf 0x14))
(leaf 0x44e308))), (.packed 2 (node
(node
(leaf 0x184080)
(leaf 0x20))
(leaf 0x69d5c8))), (.packed 2 (node
(leaf 0x206102)
(leaf 0xb26a63))), (.packed 2 (leaf 0xe35caf))], [], [0, 1, 2, 3]⟩ : Cert) = false := by
  decide +kernel

/-- Rejected: a gate term reads the wrong wire. -/
example : check (⟨(node
(node
(node
(node
(leaf 0x14201444044)
(leaf 0x2c201a44044))
(node
(leaf 0x81c1144044)
(leaf 0x20201744044)))
(node
(node
(leaf 0x262018c4044)
(leaf 0xe2012c4044))
(node
(leaf 0x1a2015c4044)
(leaf 0x80c1101044))))
(node
(node
(node
(leaf 0x7181142044)
(leaf 0x20181742044))
(node
(leaf 0x2c181a42044)
(leaf 0x14181442044)))
(node
(node
(leaf 0x1a1815c2044)
(leaf 0x60c1081044))
(node
(leaf 0xe1812c2044)
(leaf 0x261818c2044))))), 9, 57, [], [47, 50, 53, 56]⟩ : Dag)
    (⟨9, [[0x40003, 0x80042043, 0x100044083, 0x1800460c3, 0x200048103, 0x60c108004b144, 0x80c110104e184, 0x71811420511c4, 0x81c1144054204], [0x40003, 0x40042043, 0x80044083, 0xc00460c3, 0x100048103, 0x60c1141057144, 0x80c11c105d184, 0x610114205a1c4, 0x81011c2060204], [0x40042003, 0x80044043, 0xc0046083, 0x1000480c3, 0x70c1141063104, 0x80c1181069144, 0x7101142066184, 0x810118206c1c4], [0x608110006f004, 0x60c1101072044, 0x7081140075084, 0x70c11410780c4]]⟩ : Layered)
    (⟨6, [(.packed 2 (node
(node
(leaf 0x184080)
(leaf 0x14))
(leaf 0x44e2c8))), (.packed 2 (node
(node
(leaf 0x184080)
(leaf 0x20))
(leaf 0x69d5c8))), (.packed 2 (node
(leaf 0x206102)
(leaf 0xb26a63))), (.packed 2 (leaf 0xe35caf))], [], [0, 1, 2, 3]⟩ : Cert) = false := by
  decide +kernel

/-- Rejected: a gate term's constant index differs from its node's. -/
example : check (⟨(node
(node
(node
(node
(leaf 0x14201444044)
(leaf 0x2c201a44044))
(node
(leaf 0x81c1144044)
(leaf 0x20201744044)))
(node
(node
(leaf 0x262018c4044)
(leaf 0xe2012c4044))
(node
(leaf 0x1a2015c4044)
(leaf 0x80c1101044))))
(node
(node
(node
(leaf 0x7181142044)
(leaf 0x20181742044))
(node
(leaf 0x2c181a42044)
(leaf 0x14181442044)))
(node
(node
(leaf 0x1a1815c2044)
(leaf 0x60c1081044))
(node
(leaf 0xe1812c2044)
(leaf 0x261818c2044))))), 9, 57, [], [47, 50, 53, 56]⟩ : Dag)
    (⟨9, [[0x40003, 0x80042043, 0x100044083, 0x1800460c3, 0x200048103, 0x60c108108b144, 0x80c110104e184, 0x71811420511c4, 0x81c1144054204], [0x40003, 0x40042043, 0x80044083, 0xc00460c3, 0x100048103, 0x60c1141057144, 0x80c11c105d184, 0x610114205a1c4, 0x81011c2060204], [0x40042003, 0x80044043, 0xc0046083, 0x1000480c3, 0x70c1141063104, 0x80c1181069144, 0x7101142066184, 0x810118206c1c4], [0x608110006f004, 0x60c1101072044, 0x7081140075084, 0x70c11410780c4]]⟩ : Layered)
    (⟨6, [(.packed 2 (node
(node
(leaf 0x184080)
(leaf 0x14))
(leaf 0x44e2c8))), (.packed 2 (node
(node
(leaf 0x184080)
(leaf 0x20))
(leaf 0x69d5c8))), (.packed 2 (node
(leaf 0x206102)
(leaf 0xb26a63))), (.packed 2 (leaf 0xe35caf))], [], [0, 1, 2, 3]⟩ : Cert) = false := by
  decide +kernel

/-- Rejected: a copy wire is left out. -/
example : check (⟨(node
(node
(node
(node
(leaf 0x14201444044)
(leaf 0x2c201a44044))
(node
(leaf 0x81c1144044)
(leaf 0x20201744044)))
(node
(node
(leaf 0x262018c4044)
(leaf 0xe2012c4044))
(node
(leaf 0x1a2015c4044)
(leaf 0x80c1101044))))
(node
(node
(node
(leaf 0x7181142044)
(leaf 0x20181742044))
(node
(leaf 0x2c181a42044)
(leaf 0x14181442044)))
(node
(node
(leaf 0x1a1815c2044)
(leaf 0x60c1081044))
(node
(leaf 0xe1812c2044)
(leaf 0x261818c2044))))), 9, 57, [], [47, 50, 53, 56]⟩ : Dag)
    (⟨9, [[0x80042003, 0x100044043, 0x180046083, 0x2000480c3, 0x60c108104b104, 0x80c110104e144, 0x7181142051184, 0x81c11440541c4], [0x40003, 0x40042043, 0x80044083, 0xc00460c3, 0x100048103, 0x60c1141057144, 0x80c11c105d184, 0x610114205a1c4, 0x81011c2060204], [0x40042003, 0x80044043, 0xc0046083, 0x1000480c3, 0x70c1141063104, 0x80c1181069144, 0x7101142066184, 0x810118206c1c4], [0x608110006f004, 0x60c1101072044, 0x7081140075084, 0x70c11410780c4]]⟩ : Layered)
    (⟨6, [(.packed 2 (node
(leaf 0x206102)
(leaf 0x51138b))), (.packed 2 (node
(node
(leaf 0x184080)
(leaf 0x20))
(leaf 0x69d5c8))), (.packed 2 (node
(leaf 0x206102)
(leaf 0xb26a63))), (.packed 2 (leaf 0xe35caf))], [], [0, 1, 2, 3]⟩ : Cert) = false := by
  decide +kernel

/-- Rejected: a node with no assertion term is listed as asserted. -/
example : check (⟨(node
(node
(node
(node
(leaf 0x14201444044)
(leaf 0x2c201a44044))
(node
(leaf 0x81c1144044)
(leaf 0x20201744044)))
(node
(node
(leaf 0x262018c4044)
(leaf 0xe2012c4044))
(node
(leaf 0x1a2015c4044)
(leaf 0x80c1101044))))
(node
(node
(node
(leaf 0x7181142044)
(leaf 0x20181742044))
(node
(leaf 0x2c181a42044)
(leaf 0x14181442044)))
(node
(node
(leaf 0x1a1815c2044)
(leaf 0x60c1081044))
(node
(leaf 0xe1812c2044)
(leaf 0x261818c2044))))), 9, 57, [11], [47, 50, 53, 56]⟩ : Dag)
    (⟨9, [[0x40003, 0x80042043, 0x100044083, 0x1800460c3, 0x200048103, 0x60c108104b144, 0x80c110104e184, 0x71811420511c4, 0x81c1144054204], [0x40003, 0x40042043, 0x80044083, 0xc00460c3, 0x100048103, 0x60c1141057144, 0x80c11c105d184, 0x610114205a1c4, 0x81011c2060204], [0x40042003, 0x80044043, 0xc0046083, 0x1000480c3, 0x70c1141063104, 0x80c1181069144, 0x7101142066184, 0x810118206c1c4], [0x608110006f004, 0x60c1101072044, 0x7081140075084, 0x70c11410780c4]]⟩ : Layered)
    (⟨6, [(.packed 2 (node
(node
(leaf 0x184080)
(leaf 0x14))
(leaf 0x44e2c8))), (.packed 2 (node
(node
(leaf 0x184080)
(leaf 0x20))
(leaf 0x69d5c8))), (.packed 2 (node
(leaf 0x206102)
(leaf 0xb26a63))), (.packed 2 (leaf 0xe35caf))], [], [0, 1, 2, 3]⟩ : Cert) = false := by
  decide +kernel

end MatMul

end GordieHoweTest.GKRCertificate
