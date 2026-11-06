-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.Program.FieldFJ
public import GordieHowe.Language.Realizations.Circuit.ProgramCerts

public section

/-!
# The field table of a program

The compiler emits, for each program, the count of its domains with each domain's field index
and the count of its circuits with each circuit's domain, as small data of their own
(`Generated/<App>/<Params>/FieldTable.lean`), checked once against the program
(`RealizedProgram.FieldTable`, by `RealizedProgram.fieldTableB` in a certificate module).

A generated object of a domain or a circuit (its packing facts, its codec, its circuit field's
model) is stated at the field index the table gives and carried to the program's index by the
table's equation (`Interp.packingAt`, `FieldCodec.at`, `CircuitFieldOk.of_model_at`), so its
elaboration reduces the small interpretation only, never the program.
-/

namespace GordieHowe.RealizedProgram

variable (ir : RealizedProgram)

/-- **The field table of a program**: `n` domains, domain `d`'s field `df d`, `m` circuits,
circuit `c`'s domain `cd c` (a domain of the table). -/
structure FieldTable (n : ℕ) (df : ℕ → ℕ) (m : ℕ) (cd : ℕ → ℕ) : Prop where
  /-- The program has `n` domains. -/
  domains_length : ir.domains.length = n
  /-- Domain `d`'s field is `df d`. -/
  domainField_eq : ∀ d < n, ir.domainField d = df d
  /-- The program has `m` circuits. -/
  circuits_length : ir.circuits.length = m
  /-- Circuit `c`'s domain is `cd c`. -/
  circuitDomain_eq : ∀ c < m, (ir.circuit c).domain = cd c
  /-- Every circuit's domain is a domain of the table. -/
  circuitDomain_lt : ∀ c < m, cd c < n

/-- **The field table, as a test.** -/
@[expose] def fieldTableB (n : ℕ) (df : ℕ → ℕ) (m : ℕ) (cd : ℕ → ℕ) : Bool :=
  ir.domains.length == n && (List.range n).all (fun d => ir.domainField d == df d) &&
    ir.circuits.length == m && (List.range m).all (fun c => (ir.circuit c).domain == cd c) &&
    (List.range m).all (fun c => decide (cd c < n))

variable {ir} {n : ℕ} {df : ℕ → ℕ} {m : ℕ} {cd : ℕ → ℕ}

/-- **The test gives the field table.** -/
theorem FieldTable.of_fieldTableB (h : ir.fieldTableB n df m cd = true) :
    ir.FieldTable n df m cd := by
  simp only [fieldTableB, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hn, hd⟩, hm⟩, hc⟩, hl⟩ := h
  exact ⟨hn, hd, hm, hc, hl⟩

/-- **Circuit `c`'s field is its table domain's field.** -/
theorem FieldTable.circField_eq (T : ir.FieldTable n df m cd) {c : ℕ} (hc : c < m) :
    ir.circField c = df (cd c) := by
  change ir.domainField (ir.circuit c).domain = _
  rw [T.circuitDomain_eq c hc, T.domainField_eq _ (T.circuitDomain_lt c hc)]

end RealizedProgram

/-- **A field's packing facts at an equal field index.** -/
@[expose] def RealizedProgram.Interp.packingAt (I : RealizedProgram.Interp) {f f' : ℕ} (h : f = f')
    (Pk : (I.field f).Packing) : (I.field f').Packing :=
  h ▸ Pk

/-- **A field's codecs at an equal field index.** -/
@[expose] def RealizedProgram.FieldCodec.at {I : RealizedProgram.Interp} {f f' : ℕ} (h : f = f')
    (c : RealizedProgram.FieldCodec (I f)) : RealizedProgram.FieldCodec (I f') :=
  h ▸ c

namespace RealizedProgram

variable {ir : RealizedProgram} {I : Interp}

/-- **A circuit's field meets its codes, from the model of the field the table gives**
(`CircuitFieldOk.of_model` at `ir.circField c = f`). -/
theorem CircuitFieldOk.of_model_at {c f chr : ℕ} {ar : GKR.Fold.CodeArith}
    {primes bits : List String} (hf : ir.circField c = f) (hM : (I f).Model primes bits)
    (hH : (I f).CodeHom ar) (hchr : chr = (I f).spec.characteristic) :
    ir.CircuitFieldOk I c ar chr := by
  subst hf
  exact .of_model hM hH hchr

end GordieHowe.RealizedProgram
