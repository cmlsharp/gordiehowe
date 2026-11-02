-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.Realizations.Circuit.ProgramCerts
public import GordieHowe.ProofSystem.Program.FieldDomain
public import GordieHowe.ProofSystem.Program.FieldProofSystem

@[expose] public section

/-!
# GordieHowe: the proof system of a program's certificates

The model facts the certificates' composition reads (`ProgramCerts.circuitsEnforce`,
`ProgramCerts.circuitsAccept`), from a program's checks and model and its ready domains, and the
proof system they give.

* **From the checks** (`GordieHowe.RealizedProgram.Checks.derivModel`,
  `GordieHowe.RealizedProgram.Checks.boundOk`): the program's validity, the interpretation's
  registry, lawful readings and MAC model, and the derivations' tables and bound values.
* **From the ready domains** (`GordieHowe.RealizedProgram.inputLayoutOk_of_ready`,
  `GordieHowe.RealizedProgram.privAfterPub_of_ready`): every circuit is laid out as the plan lays
  it out and has its private blocks at private positions (each domain's `ClaimOk.inputs`; the
  default circuit past the circuits).
* **The proof system** (`GordieHowe.RealizedProgram.ProgramCerts.proofSystem`): the generic
  per-field proof system (`ProofSystem.ofFieldProofs`) at the sources of the certificates' source
  parts, at the sumcheck nodes of the ready domains' packings
  (`GordieHowe.RealizedProgram.ProgramCerts.readyNodes`), with `enforce` and `accept` proved from
  the certificates; its code reads only the source parts, which have compiled code.
-/

namespace GordieHowe.RealizedProgram

open GordieHowe.GKR

variable {ir : RealizedProgram} {I : Interp} {P : Export.Plan}

/-! ## From the checks -/

/-- **The model facts of a program's checks and model** (`DerivModel`): the program's validity, the
interpretation's registry, lawful readings and MAC model, and the derivations' tables. -/
theorem Checks.derivModel {orng : List (ℕ × ℕ)} (checks : ir.Checks P orng) (model : I.Model P ir orng) :
    ir.DerivModel I (primeNodesOf P ir) := by
  obtain ⟨_, hv⟩ := checks.realization
  exact ⟨checks.valid.program.wellFormed, model.registered, model.lawful, hv.tables, model.macModel⟩

/-- **Every bound value of a checked program reads committed values and constants**
(`DerivationsValid.bound`). -/
theorem Checks.boundOk {orng : List (ℕ × ℕ)} (checks : ir.Checks P orng) :
    ∀ w < ir.values.length, ir.BoundOk w := by
  obtain ⟨_, hv⟩ := checks.realization
  exact hv.bound

/-! ## From the ready domains -/

/-- **A plain layout's private blocks lie at private positions** (`blockOkT`, `InputsT.pubEnd`). -/
theorem InputsT.privAfterPub {d c : ℕ} (hc : ir.InputsT d c) :
    ∀ b ∈ (ir.circuit c).inputs, b.isPublic = false → (ir.circuit c).publicInputs ≤ b.first := by
  intro b hb hp
  have h := hc.blocks b hb
  have he := hc.pubEnd
  cases b <;> simp_all [blockOkT, InputBlock.isPublic, InputBlock.first, privEnd] <;> omega

/-- The default circuit has no input blocks. -/
theorem default_inputs : (default : Circuit).inputs = [] := rfl

/-- **A circuit index past the program's circuits names the default circuit.** -/
theorem circuit_eq_default {c : ℕ} (hc : ir.circuits.length ≤ c) : ir.circuit c = default := by
  simp only [circuit, List.getD_eq_default _ _ hc]

/-- **A circuit index past the program's circuits is laid out**: the default circuit has no
blocks. -/
theorem inputLayoutOk_of_le {c : ℕ} (hc : ir.circuits.length ≤ c) : ir.InputLayoutOk c := by
  have h := circuit_eq_default (ir := ir) hc
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [h]; rfl
  · rw [h]; decide
  · intro u a n hm; rw [h, default_inputs] at hm; cases hm
  · intro u a n hm; rw [h, default_inputs] at hm; cases hm

/-- **A circuit lies in its domain's circuits.** -/
theorem mem_circs_domain (c : Fin ir.circuits.length) : c ∈ ir.circs (ir.circuit c).domain := by
  simp [circs]

/-- **Every circuit of a program with ready domains is laid out as the plan lays it out**
(`ClaimOk.inputs`, `InputsT.inputLayoutOk`; the default layout past the circuits). -/
theorem inputLayoutOk_of_ready (R : ∀ d : Fin ir.domains.length, ir.FieldReady I d P)
    (hdom : ∀ c < ir.circuits.length, (ir.circuit c).domain < ir.domains.length) (c : ℕ) :
    ir.InputLayoutOk c := by
  by_cases hc : c < ir.circuits.length
  · exact ((R ⟨_, hdom c hc⟩).claimOk.inputs ⟨c, hc⟩ (mem_circs_domain ⟨c, hc⟩)).inputLayoutOk
  · exact inputLayoutOk_of_le (Nat.le_of_not_lt hc)

/-- **Every circuit of a program with ready domains has its private blocks at private
positions** (`ClaimOk.inputs`, `InputsT.privAfterPub`; the default circuit has no blocks). -/
theorem privAfterPub_of_ready (R : ∀ d : Fin ir.domains.length, ir.FieldReady I d P)
    (hdom : ∀ c < ir.circuits.length, (ir.circuit c).domain < ir.domains.length) (c : ℕ) :
    ∀ b ∈ (ir.circuit c).inputs, b.isPublic = false → (ir.circuit c).publicInputs ≤ b.first := by
  by_cases hc : c < ir.circuits.length
  · exact ((R ⟨_, hdom c hc⟩).claimOk.inputs ⟨c, hc⟩ (mem_circs_domain ⟨c, hc⟩)).privAfterPub
  · intro b hb
    rw [circuit_eq_default (Nat.le_of_not_lt hc), default_inputs] at hb
    cases hb

/-! ## The compiled circuits of the certificates -/

namespace ProgramCerts

/-- **The sumcheck nodes of the ready domains' packings** (`FieldInterp.Packing.nodes`, the C++
`Field::poly_evaluation_point`, which the GKR sumcheck and the bit sumcheck share), at each circuit's
domain, every one present (`h`). -/
def readyNodes (R : ∀ d : Fin ir.domains.length, ir.FieldReady I d P)
    (hdom : ∀ c < ir.circuits.length, (ir.circuit c).domain < ir.domains.length)
    (h : ∀ c : Fin ir.circuits.length, (R ⟨_, hdom c c.2⟩).Pk.nodes.isSome = true)
    (c : Fin ir.circuits.length) : Sumcheck.Nodes (I (ir.circField c)).K :=
  (R ⟨_, hdom c c.2⟩).Pk.nodes.get (h c)

/-- **The proof system of a program's certificates**: the generic per-field proof system
(`ProofSystem.ofFieldProofs`) of the checks `checks`, the model `model` and the ready domains `R`, at
the sources of the certificates' source parts `parts` (`SourceParts.src`) with the sumcheck nodes
of the ready domains' packings (`readyNodes`, every one present: `hnodes`); its sources enforce the
circuits' entries and accept the honest inputs by the certificates `hc`
(`ProgramCerts.circuitsEnforce`, `ProgramCerts.circuitsAccept`). Its code reads only `parts`.
`hsel`: the selections' bound, by default from a program without a product form. -/
def proofSystem (parts : SourceParts) (hc : Nonempty (ir.ProgramCerts I parts))
    {orng : List (ℕ × ℕ)} (checks : ir.Checks P orng) (model : I.Model P ir orng)
    (R : ∀ d : Fin ir.domains.length, ir.FieldReady I d P)
    (hdom : ∀ c < ir.circuits.length, (ir.circuit c).domain < ir.domains.length)
    (hnodes : ∀ c : Fin ir.circuits.length, (R ⟨_, hdom c c.2⟩).Pk.nodes.isSome = true)
    (hsel : ir.SelSound I := by exact RealizedProgram.selSound_of_noProduct _ (by decide +kernel)) :
    ir.ProofSystem P I :=
  ProofSystem.ofFieldProofs checks model (parts.src ir I (readyNodes R hdom hnodes))
    (hc.elim fun cs => cs.circuitsEnforce (checks.derivModel model) checks.boundOk
      (inputLayoutOk_of_ready R hdom) _)
    (hc.elim fun cs => cs.circuitsAccept (checks.derivModel model) checks.boundOk
      (inputLayoutOk_of_ready R hdom) (privAfterPub_of_ready R hdom) _)
    R hsel

/-- **A program with no GKR circuit has no circuit index.** -/
theorem not_circuit (h : ir.circuits.length = 0) (c : Fin ir.circuits.length) : False := by
  have := c.2
  omega

/-- **The proof system of a program with no GKR circuit**: the generic per-field proof system
(`ProofSystem.ofFieldProofs`) of the checks `checks`, the model `model` and the ready domains `R`,
with no source, which enforces and accepts vacuously (`h`: the program has no circuit). -/
def proofSystemOfNoCircuits {orng : List (ℕ × ℕ)} (checks : ir.Checks P orng)
    (model : I.Model P ir orng) (R : ∀ d : Fin ir.domains.length, ir.FieldReady I d P)
    (h : ir.circuits.length = 0)
    (hsel : ir.SelSound I := by exact RealizedProgram.selSound_of_noProduct _ (by decide +kernel)) :
    ir.ProofSystem P I :=
  ProofSystem.ofFieldProofs checks model (fun c => (not_circuit h c).elim)
    ⟨fun c => (not_circuit h c).elim, fun c => (not_circuit h c).elim⟩
    ⟨fun c => (not_circuit h c).elim⟩ R hsel

end ProgramCerts

end GordieHowe.RealizedProgram
