-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.Realizations.Circuit.RelComplete
public import GordieHowe.ProofSystem.Program.FieldModel

@[expose] public section

/-!
# GordieHowe: a program's GKR certificates discharge its trust base

A program's certificates (`GordieHowe.RealizedProgram.ProgramCerts`): per circuit its certificate
data and code arithmetic, every circuit's certificate passing the relational check
(`GordieHowe.RealizedProgram.circuitCertB`), and every circuit's field meeting its codes
(`GordieHowe.RealizedProgram.CircuitFieldOk`).

* **The sources** (`GordieHowe.RealizedProgram.SourceParts.src`): circuit `c`'s GKR source is the
  bridge's circuit (`GKR.CertificateBridge.toSource`) of the parts of its certificate a source
  reads (`GordieHowe.RealizedProgram.SourceParts`, the certificate data with compiled code) at the
  input dimension `circuitWidth c`, with given sumcheck nodes.
* **Soundness** (`GordieHowe.RealizedProgram.ProgramCerts.circuitsEnforce`): the sources enforce
  the circuits' entries (`CircuitsEnforce`, by `circuitsEnforce_of_certs`).
* **Completeness** (`GordieHowe.RealizedProgram.ProgramCerts.circuitsAccept`): the sources accept
  the honest inputs (`CircuitsAccept`, by `circuitsAccept_of_certs`).
* **The field facts** (`GordieHowe.RealizedProgram.CircuitFieldOk.of_model`): a field with a model
  meets every code arithmetic that is its homomorphism, at its characteristic.

The model facts these read (`DerivModel`, `BoundOk`, `InputLayoutOk`, the private blocks'
positions) come from a proof system and its ready domains
(`GordieHowe/ProofSystem/Program/Certified.lean`).
-/

namespace GordieHowe.RealizedProgram

open GordieHowe.GKR GordieHowe.GKR.Fold

/-- **The parts of a program's certificates its GKR sources read**, per circuit: the layered
circuit, the term width and the constant table (`load_ghc`'s `name.layered`, `name.width`,
`name.consts`, the only certificate data with compiled code). -/
structure SourceParts where
  /-- Each circuit's layered circuit. -/
  layered : ℕ → Certificate.Layered
  /-- Each circuit's term width. -/
  width : ℕ → ℕ
  /-- Each circuit's constant table. -/
  consts : ℕ → Consts

/-- **A program's GKR certificates** with the source parts `parts`: per circuit its certificate
data and code arithmetic, the source parts being the certificate's (by definition, `layered_eq`,
`width_eq`, `consts_eq`), every circuit's certificate passing (`circuitCertB`), and every
circuit's field meeting its codes (`CircuitFieldOk`). Past the circuits, `cd` and `ar` are
unconstrained. -/
structure ProgramCerts (ir : RealizedProgram) (I : Interp) (parts : SourceParts) where
  /-- The certificate data of each circuit. -/
  cd : ℕ → CircuitData
  /-- The code arithmetic of each circuit's field. -/
  ar : ℕ → CodeArith
  /-- Every circuit's certificate passes. -/
  ok : ∀ c < ir.circuits.length, ir.circuitCertB c (ar c) (cd c) = true
  /-- Every circuit's field meets its codes. -/
  field : ∀ c < ir.circuits.length, ir.CircuitFieldOk I c (ar c) (cd c).chr
  /-- The layered circuit is the certificate's. -/
  layered_eq : ∀ c < ir.circuits.length, parts.layered c = (cd c).layered
  /-- The term width is the certificate's. -/
  width_eq : ∀ c < ir.circuits.length, parts.width c = (cd c).w
  /-- The constant table is the certificate's. -/
  consts_eq : ∀ c < ir.circuits.length, parts.consts c = (cd c).consts

variable {ir : RealizedProgram} {I : Interp} {primeNodes : ℕ → List String} {parts : SourceParts}

/-- **A circuit's inputs fit in `2 ^ circuitWidth`.** -/
theorem inputCount_le_pow_circuitWidth (c : ℕ) :
    (ir.circuit c).inputCount ≤ 2 ^ ir.circuitWidth c :=
  (le_max_right _ _).trans (Nat.le_pow_clog (by norm_num) _)

/-- **The GKR sources of a program's source parts**: circuit `c`'s source is the bridge's circuit
of its layered circuit, term width and constants at the input dimension `circuitWidth c`, with the
sumcheck nodes `nodes c`. -/
def SourceParts.src (parts : SourceParts) (ir : RealizedProgram) (I : Interp)
    (nodes : ∀ c : Fin ir.circuits.length, Sumcheck.Nodes (I (ir.circField c)).K) :
    ∀ c : Fin ir.circuits.length, ir.CircuitSource I c := fun c =>
  { d := ir.circuitWidth c
    S := CertificateBridge.toSource (parts.layered c) (parts.width c)
      ((parts.consts c).decode (I (ir.circField c)).decode) (ir.circuitWidth c)
    nodes := nodes c
    hfit := inputCount_le_pow_circuitWidth c }

namespace ProgramCerts

/-- **The sources are the bridge's circuits of the certificates** (`layered_eq`, `width_eq`,
`consts_eq`). -/
theorem src_S (P : ir.ProgramCerts I parts)
    {nodes : ∀ c : Fin ir.circuits.length, Sumcheck.Nodes (I (ir.circField c)).K}
    (c : Fin ir.circuits.length) :
    (parts.src ir I nodes c).S = CertificateBridge.toSource (P.cd c).layered (P.cd c).w
      ((P.cd c).consts.decode (I (ir.circField c)).decode) (parts.src ir I nodes c).d := by
  show CertificateBridge.toSource (parts.layered c) (parts.width c)
    ((parts.consts c).decode (I (ir.circField c)).decode) (ir.circuitWidth c) = _
  rw [P.layered_eq c c.2, P.width_eq c c.2, P.consts_eq c c.2]
  rfl

/-- **Passing certificates enforce their circuits** (`circuitsEnforce_of_certs` at the
certificates' sources), uniformly over programs. -/
theorem circuitsEnforce (P : ir.ProgramCerts I parts) (hM : ir.DerivModel I primeNodes)
    (hbd : ∀ w < ir.values.length, ir.BoundOk w) (hL : ∀ c, ir.InputLayoutOk c)
    (nodes : ∀ c : Fin ir.circuits.length, Sumcheck.Nodes (I (ir.circField c)).K) :
    ir.CircuitsEnforce I (parts.src ir I nodes) :=
  circuitsEnforce_of_certs hM hbd hL P.cd P.ar P.field P.ok (parts.src ir I nodes)
    (fun _ => le_rfl) P.src_S

/-- **Passing certificates accept the honest inputs** (`circuitsAccept_of_certs` at the
certificates' sources), every private block of every circuit lying at private positions. -/
theorem circuitsAccept (P : ir.ProgramCerts I parts) (hM : ir.DerivModel I primeNodes)
    (hbd : ∀ w < ir.values.length, ir.BoundOk w) (hL : ∀ c, ir.InputLayoutOk c)
    (hpriv : ∀ c, ∀ b ∈ (ir.circuit c).inputs, b.isPublic = false →
      (ir.circuit c).publicInputs ≤ b.first)
    (nodes : ∀ c : Fin ir.circuits.length, Sumcheck.Nodes (I (ir.circField c)).K) :
    ir.CircuitsAccept I (parts.src ir I nodes) :=
  ⟨circuitsAccept_of_certs hM hbd hL hpriv P.cd P.ar P.field P.ok (parts.src ir I nodes) P.src_S⟩

end ProgramCerts

/-! ## The certificates from their source parts -/

/-- **Circuit `c`'s source parts**: its layered circuit, term width and constant table. -/
def SourceParts.at (parts : SourceParts) (c : ℕ) : Certificate.Layered × ℕ × Consts :=
  (parts.layered c, parts.width c, parts.consts c)

/-- **The source parts of certificate data**: its layered circuit, term width and constant table
(`load_ghc`'s `name.layered`, `name.w`, `name.consts`). -/
def CircuitData.sourceParts (cd : CircuitData) : Certificate.Layered × ℕ × Consts :=
  (cd.layered, cd.w, cd.consts)

/-- **A program's GKR certificates from their source parts** (`ProgramCerts`): the certificate data
`cd` and code arithmetic `ar` of every circuit, every circuit's certificate passing (`ok`), every
circuit's field meeting its codes (`field`), and the source parts `parts` being the certificates'
(`hparts`, one equation per circuit: `rfl` where `parts` names the certificates' loaded parts).
The source parts are given apart from `cd`: they are the certificate data with compiled code, the
certificate itself has none (`load_ghc`). -/
def ProgramCerts.ofParts (cd : ℕ → CircuitData) (ar : ℕ → CodeArith)
    (ok : ∀ c < ir.circuits.length, ir.circuitCertB c (ar c) (cd c) = true)
    (field : ∀ c < ir.circuits.length, ir.CircuitFieldOk I c (ar c) (cd c).chr)
    (hparts : ∀ c < ir.circuits.length, parts.at c = (cd c).sourceParts) :
    ir.ProgramCerts I parts where
  cd := cd
  ar := ar
  ok := ok
  field := field
  layered_eq c hc := congrArg (fun p => p.1) (hparts c hc)
  width_eq c hc := congrArg (fun p => p.2.1) (hparts c hc)
  consts_eq c hc := congrArg (fun p => p.2.2) (hparts c hc)

/-- **A field with a model meets every code arithmetic that is its homomorphism**, at its
characteristic (`FieldInterp.Model.ringChar`, `FieldInterp.Model.decode_natCast`; a finite field
has positive characteristic). -/
theorem CircuitFieldOk.of_model {c chr : ℕ} {ar : CodeArith} {primes bits : List String}
    (hM : (I (ir.circField c)).Model primes bits) (hH : (I (ir.circField c)).CodeHom ar)
    (hchr : chr = (I (ir.circField c)).spec.characteristic) :
    ir.CircuitFieldOk I c ar chr := by
  subst hchr
  have hch : CharP (I (ir.circField c)).K (I (ir.circField c)).spec.characteristic :=
    hM.ringChar ▸ ringChar.charP _
  exact ⟨hH, hch, Nat.pos_of_ne_zero (CharP.char_ne_zero_of_finite (I (ir.circField c)).K _),
    hM.decode_natCast⟩

end GordieHowe.RealizedProgram
