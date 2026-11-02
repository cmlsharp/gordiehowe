-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

import GordieHowe.Language.Realizations.Circuit.ProgramCerts
import GordieHowe.Applications.FieldInterps.Odd
import GordieHowe.Generated.RSA2048.Goldilocks2.Msg2KiB.ROMParams.GKR.H.Circuit

/-!
# A program's certificates discharge its trust base: RSA-2048's circuit `H`

RSA-2048's program has two circuits: `H` (circuit `0`, `GF(2^128)`), whose certificate passes
(`GKR.H.cert.circuit_ok`), and `A` (circuit `1`, Goldilocks²). The program's certificates
(`RealizedProgram.ProgramCerts`, built by `ProgramCerts.ofParts`) are `H`'s, with its field's model
and code arithmetic, and any certificate of `A` given as an argument, with the source parts of
both. From them, the certificates' sources enforce the circuits' entries (`CircuitsEnforce`) and
accept the honest inputs (`CircuitsAccept`) at the model facts a proof system supplies. (The
program's generated proof system, `GordieHowe.Generated.RSA2048.Goldilocks2.Msg2KiB.ROMParams.certs`,
is this construction at `A`'s exported certificate.)
-/

namespace GordieHoweTest.ProgramCerts

open GordieHowe GordieHowe.RealizedProgram GordieHowe.GKR.Fold
open GordieHowe.Generated.RSA2048.Goldilocks2.Msg2KiB.ROMParams (GKR.H.cert GKR.H.ar)
open GordieHowe.Generated.RSA2048.Goldilocks2.Msg2KiB.ROMParams.Program (program)

/-- The fields of RSA-2048's program: field `0` is `GF(2^128)`, field `1` Goldilocks²; no opaque
function. -/
def interp : Interp := ⟨fun n => match n with | 0 => gf128 | _ => gold2, fun _ _ _ => 0⟩

theorem circuits_length : program.circuits.length = 2 := rfl

/-- `H` is the program's circuit `0`. -/
theorem cert_c : GKR.H.cert.c = 0 := rfl

/-- **`H`'s certificate passes** (`GKR.H.cert.circuit_ok`). -/
theorem circuitCertB_H : program.circuitCertB 0 GKR.H.ar GKR.H.cert = true := by
  have h := GKR.H.cert.circuit_ok
  rw [cert_c] at h
  exact h

/-- **`H`'s field meets its codes**: `GF(2^128)` with its model and code arithmetic. -/
theorem circuitFieldOk_H : program.CircuitFieldOk interp 0 GKR.H.ar GKR.H.cert.chr :=
  CircuitFieldOk.of_model gf128_model gf128_codeHom rfl

/-- A certificate of circuit `A`: its data and code arithmetic, passing, its field meeting its
codes. -/
structure CertA where
  /-- The certificate data. -/
  cd : CircuitData
  /-- The code arithmetic. -/
  ar : CodeArith
  /-- The certificate passes. -/
  ok : program.circuitCertB 1 ar cd = true
  /-- The field meets its codes. -/
  field : program.CircuitFieldOk interp 1 ar cd.chr

/-- **The source parts**: `H`'s loaded parts, and `A`'s of the certificate `cA`. -/
def parts (cA : CertA) : SourceParts where
  layered | 0 => GKR.H.cert.layered | _ => cA.cd.layered
  width | 0 => GKR.H.cert.width | _ => cA.cd.w
  consts | 0 => GKR.H.cert.consts | _ => cA.cd.consts

/-- **The program's certificates**: `H`'s, and `A`'s certificate `cA`. -/
noncomputable def certs (cA : CertA) : program.ProgramCerts interp (parts cA) :=
  ProgramCerts.ofParts (fun | 0 => GKR.H.cert | _ => cA.cd) (fun | 0 => GKR.H.ar | _ => cA.ar)
    (fun c hc => by
      rw [circuits_length] at hc
      match c, hc with
      | 0, _ => exact circuitCertB_H
      | 1, _ => exact cA.ok)
    (fun c hc => by
      rw [circuits_length] at hc
      match c, hc with
      | 0, _ => exact circuitFieldOk_H
      | 1, _ => exact cA.field)
    (fun c hc => by
      rw [circuits_length] at hc
      match c, hc with
      | 0, _ => rfl
      | 1, _ => rfl)

/-- **The certificates' sources enforce the circuits**, at the model facts. -/
theorem circuitsEnforce (cA : CertA) {primeNodes : ℕ → List String}
    (hM : program.DerivModel interp primeNodes)
    (hbd : ∀ w < program.values.length, program.BoundOk w) (hL : ∀ c, program.InputLayoutOk c)
    (nodes : ∀ c : Fin program.circuits.length, Sumcheck.Nodes (interp (program.circField c)).K) :
    program.CircuitsEnforce interp ((parts cA).src program interp nodes) :=
  (certs cA).circuitsEnforce hM hbd hL nodes

/-- **The certificates' sources accept the honest inputs**, at the model facts. -/
theorem circuitsAccept (cA : CertA) {primeNodes : ℕ → List String}
    (hM : program.DerivModel interp primeNodes)
    (hbd : ∀ w < program.values.length, program.BoundOk w) (hL : ∀ c, program.InputLayoutOk c)
    (hpriv : ∀ c, ∀ b ∈ (program.circuit c).inputs, b.isPublic = false →
      (program.circuit c).publicInputs ≤ b.first)
    (nodes : ∀ c : Fin program.circuits.length, Sumcheck.Nodes (interp (program.circField c)).K) :
    program.CircuitsAccept interp ((parts cA).src program interp nodes) :=
  (certs cA).circuitsAccept hM hbd hL hpriv nodes

end GordieHoweTest.ProgramCerts
