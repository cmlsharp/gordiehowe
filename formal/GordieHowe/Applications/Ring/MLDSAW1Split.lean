-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Ring.MLDSAW1Ring
public import GordieHowe.Model.RingSignature.Adversary
public import GordieHowe.Model.RingSignature.BaseCompleteness

@[expose] public section

/-!
# The split of the oracle of the ML-DSA ring publishing `w₁`

The ring signature `w1Concrete` reads one random oracle `X → Y`. Its theorems that treat the base
signer's oracles and the proof system's oracle separately take an additive split
`sp : Y ≃+ Y₁ × Y₂` of the oracle's values as a hypothesis, with predicates saying which component
each part reads: the base signer's decodings read only the first component `Y₁`, the proof system
reads the second component `Y₂` everywhere and the first only outside a set `B` of points. The
split is not a change to the scheme: `w1Concrete` and `w1Scheme44/65/87` keep their arguments.

A uniform oracle `X → Y` read through `sp` is a pair of independent uniform oracles `X → Y₁` and
`X → Y₂` (`map_uniform_split`): one random oracle with independent output components is two
independent random oracles on the same points, the model of two oracles that an implementation
separates by domain separation. The split is additive because
an oracle query adds the oracle's value to the answer register, so a query of `X → Y` is a query
of each component.

- `OracleSplit Y Y₁ Y₂`: additive equivalences `Y ≃+ Y₁ × Y₂`. `OracleSplit.base sp H`,
  `OracleSplit.prf sp H`: the two components of an oracle; `OracleSplit.splitEquiv sp`: oracles as
  pairs of component oracles; `map_uniform_split`.
- `OracleSplit.refl`: the identity split of `Y₁ × Y₂`; `OracleSplit.unit`: the split `Y ≃+ Y × Unit`
  (no proof-system component), under which the predicates below are the statements without a split.
- `W1Oracles.ReadsFst O sp`, `MaskOracle.ReadsFst M sp`: the decodings of the oracles' values read
  only the first component. `W1Oracles.readsFst_unit`, `MaskOracle.readsFst_unit`: every decoding
  does at the split `unit`.
- `ProofSystem.ReadsOff PS sp B`: the honest prover's result is the same at two oracles with the
  same second component everywhere that agree outside `B`. `ProofSystem.ReadsSnd PS sp`: it reads
  only the second component; `ProofSystem.readsOff_univ_iff` (the form at `B = univ`),
  `ProofSystem.ReadsSnd.readsOff` (a prover reading only the second component satisfies every
  `ReadsOff`), `ProofSystem.readsOff_unit_iff` (at the split `unit`: the prover reads only the
  points outside `B`), `ProofSystem.readsOff_acceptAll`.
- `OracleView.ReadsOff V sp B`: the same for the table an adversary receives;
  `OracleView.readsOff_queriesOnly`, `OracleView.readsOff_tableOn_compl` (the table of the points
  outside `B`), `OracleView.readsOff_unit_iff`.
- Constructions meeting the predicates: `W1Oracles.viaBase sp O`, `MaskOracle.viaBase sp M` (the
  oracles of the first component read through `sp`; `readsFst_viaBase`, `muOrc_viaBase`,
  `chOrc_viaBase`, `hOrc_viaBase`, `gOrc_viaBase`), and `ProofSystem.viaPrf sp PS` (a proof system
  of the second component read through `sp`; `readsSnd_viaPrf`, `verify_viaPrf`).
-/

namespace GordieHowe.RingSignature

open scoped ENNReal

/-- **An additive split of the oracle's values** into the base signer's component `Y₁` and the
proof system's component `Y₂`. -/
abbrev OracleSplit (Y Y₁ Y₂ : Type) [AddGroup Y] [AddGroup Y₁] [AddGroup Y₂] : Type :=
  Y ≃+ Y₁ × Y₂

namespace OracleSplit

variable {X Y Y₁ Y₂ : Type} [AddGroup Y] [AddGroup Y₁] [AddGroup Y₂] (sp : OracleSplit Y Y₁ Y₂)

/-- **The base component of an oracle**: its values' first components. -/
def base (H : X → Y) : X → Y₁ := fun x => (sp (H x)).1

/-- **The proof system's component of an oracle**: its values' second components. -/
def prf (H : X → Y) : X → Y₂ := fun x => (sp (H x)).2

/-- **An oracle as the pair of its components.** -/
def splitEquiv : (X → Y) ≃ (X → Y₁) × (X → Y₂) where
  toFun H := (base sp H, prf sp H)
  invFun G x := sp.symm (G.1 x, G.2 x)
  left_inv H := funext fun x => by simp [base, prf]
  right_inv G := by
    ext x <;> simp [base, prf]

@[simp]
theorem splitEquiv_apply (H : X → Y) : splitEquiv sp H = (base sp H, prf sp H) :=
  rfl

/-- Two oracles with the same components are equal. -/
theorem ext_of_base_prf {H H' : X → Y} (h₁ : base sp H = base sp H') (h₂ : prf sp H = prf sp H') :
    H = H' :=
  (splitEquiv sp).injective (Prod.ext h₁ h₂)

/-- **A uniform oracle is a pair of independent uniform component oracles**: the uniform law on
`X → Y` read through `sp` is the uniform law on pairs of oracles `X → Y₁` and `X → Y₂`. -/
theorem map_uniform_split [Fintype X] [DecidableEq X] [Fintype Y] [Fintype Y₁] [Fintype Y₂]
    [Nonempty Y] [Nonempty Y₁] [Nonempty Y₂] :
    (PMF.uniformOfFintype (X → Y)).map (splitEquiv sp) =
      PMF.uniformOfFintype ((X → Y₁) × (X → Y₂)) := by
  ext G
  rw [PMF.map_apply, tsum_eq_single ((splitEquiv sp).symm G)]
  · simp only [Equiv.apply_symm_apply, ite_true, PMF.uniformOfFintype_apply]
    rw [Fintype.card_congr (splitEquiv sp)]
  · intro H hH
    split_ifs with h
    · exact absurd (by rw [h, Equiv.symm_apply_apply]) hH
    · rfl

/-- **The identity split** of a product: the base component first. -/
def refl : OracleSplit (Y₁ × Y₂) Y₁ Y₂ :=
  AddEquiv.refl _

variable (Y) in
/-- **The split with no proof-system component**: `Y ≃+ Y × Unit`. -/
def unit : OracleSplit Y Y Unit :=
  (AddEquiv.prodUnique (M := Y) (N := Unit)).symm

@[simp]
theorem unit_apply (y : Y) : unit Y y = (y, ()) :=
  rfl

/-- At the split `unit`, the base component of an oracle is the oracle. -/
@[simp]
theorem base_unit (H : X → Y) : base (unit Y) H = H :=
  rfl

/-- At the split `unit`, any two oracles have the same proof-system component. -/
theorem prf_unit (H H' : X → Y) : prf (unit Y) H = prf (unit Y) H' :=
  rfl

end OracleSplit

open OracleSplit

variable {X Y Y₁ Y₂ : Type} [AddGroup Y] [AddGroup Y₁] [AddGroup Y₂] (sp : OracleSplit Y Y₁ Y₂)

/-! ### The proof system reads the second component -/

section Prf

variable {Stmt Wit : Type}

/-- **The honest prover reads the second component everywhere and the first only outside `B`**:
its result is the same at two oracles whose second components agree everywhere and which agree
outside `B`. -/
def ProofSystem.ReadsOff {TPS : PSTypes} (PS : ProofSystem X Y Stmt Wit TPS) (B : Set X) : Prop :=
  ∀ x w c (H H' : X → Y), (∀ z, (sp (H z)).2 = (sp (H' z)).2) → (∀ z ∉ B, H z = H' z) →
    (PS.prove x w c).run H = (PS.prove x w c).run H'

/-- **The honest prover reads only the second component**: its result is the same at two oracles
with the same second component. -/
def ProofSystem.ReadsSnd {TPS : PSTypes} (PS : ProofSystem X Y Stmt Wit TPS) : Prop :=
  ∀ x w c (H H' : X → Y), prf sp H = prf sp H' → (PS.prove x w c).run H = (PS.prove x w c).run H'

variable {sp}

/-- **`ReadsOff` at every point is `ReadsSnd`.** -/
theorem ProofSystem.readsOff_univ_iff {TPS : PSTypes} {PS : ProofSystem X Y Stmt Wit TPS} :
    PS.ReadsOff sp Set.univ ↔ PS.ReadsSnd sp := by
  constructor
  · intro h x w c H H' hp
    exact h x w c H H' (fun z => congrFun hp z) fun z hz => absurd (Set.mem_univ z) hz
  · intro h x w c H H' hp _
    exact h x w c H H' (funext hp)

/-- **A prover reading only the second component meets every `ReadsOff`.** -/
theorem ProofSystem.ReadsSnd.readsOff {TPS : PSTypes} {PS : ProofSystem X Y Stmt Wit TPS} (h : PS.ReadsSnd sp)
    (B : Set X) : PS.ReadsOff sp B :=
  fun x w c H H' hp _ => h x w c H H' (funext hp)

/-- **At the split `unit`, `ReadsOff` says the prover reads only the points outside `B`** (the
form of the hypothesis on the prover without a split). -/
theorem ProofSystem.readsOff_unit_iff {TPS : PSTypes} {PS : ProofSystem X Y Stmt Wit TPS} {B : Set X} :
    PS.ReadsOff (OracleSplit.unit Y) B ↔
      ∀ x w c (H H' : X → Y), (∀ z ∉ B, H z = H' z) →
        (PS.prove x w c).run H = (PS.prove x w c).run H' :=
  ⟨fun h x w c H H' hB => h x w c H H' (fun _ => rfl) hB,
    fun h x w c H H' _ hB => h x w c H H' hB⟩

/-- **The accepting proof system reads nothing**: it meets every `ReadsOff`. -/
theorem ProofSystem.readsOff_acceptAll (B : Set X) :
    (ProofSystem.acceptAll X Y Stmt Wit).ReadsOff sp B :=
  fun _ _ _ _ _ _ _ => rfl

variable (sp)

/-- **A proof system of the second component read through the split**: its prover's answers are
the second components of the oracle's values, and its verifier runs at the second component. -/
def ProofSystem.viaPrf {TPS : PSTypes} (PS : ProofSystem X Y₂ Stmt Wit TPS) :
    ProofSystem X Y Stmt Wit TPS where
  q := PS.q
  prove x w c := (PS.prove x w c).mapQuery id fun y => (sp y).2
  prove_queries x w c H := by
    rw [OracleProg.length_trace_mapQuery]
    exact PS.prove_queries x w c _
  verify H x π := PS.verify (prf sp H) x π

/-- The prover of `viaPrf` is the prover of the second component. -/
theorem ProofSystem.run_prove_viaPrf {TPS : PSTypes} (PS : ProofSystem X Y₂ Stmt Wit TPS) (x : Stmt) (w : Wit)
    (c : PS.Coins) (H : X → Y) :
    ((PS.viaPrf sp).prove x w c).run H = (PS.prove x w c).run (prf sp H) :=
  OracleProg.run_mapQuery _ _ H _

/-- The verifier of `viaPrf` is the verifier of the second component. -/
theorem ProofSystem.verify_viaPrf {TPS : PSTypes} (PS : ProofSystem X Y₂ Stmt Wit TPS) (H : X → Y) (x : Stmt)
    (π : PS.Proof) : (PS.viaPrf sp).verify H x π = PS.verify (prf sp H) x π :=
  rfl

/-- **`viaPrf` reads only the second component.** -/
theorem ProofSystem.readsSnd_viaPrf {TPS : PSTypes} (PS : ProofSystem X Y₂ Stmt Wit TPS) : (PS.viaPrf sp).ReadsSnd sp :=
  fun x w c H H' h => (ProofSystem.run_prove_viaPrf sp PS x w c H).trans
    ((congrArg (fun G => (PS.prove x w c).run G) h).trans
      (ProofSystem.run_prove_viaPrf sp PS x w c H').symm)

end Prf

/-! ### The adversary's table reads the second component -/

/-- **The table an adversary receives reads the second component everywhere and the first only
outside `B`**: it is the same at two oracles whose second components agree everywhere and which
agree outside `B`. -/
def OracleView.ReadsOff (V : OracleView X Y) (B : Set X) : Prop :=
  ∀ H H' : X → Y, (∀ z, (sp (H z)).2 = (sp (H' z)).2) → (∀ z ∉ B, H z = H' z) → V.view H = V.view H'

variable {sp}

/-- **The empty table meets every `ReadsOff`.** -/
theorem OracleView.readsOff_queriesOnly (B : Set X) :
    (OracleView.queriesOnly X Y).ReadsOff sp B :=
  fun _ _ _ _ => rfl

/-- **The table of the points outside `B` meets `ReadsOff` at `B`**: two oracles that agree outside
`B` have the same table there. -/
theorem OracleView.readsOff_tableOn_compl (B : Set X) :
    (OracleView.tableOn (Y := Y) (· ∉ B)).ReadsOff sp B :=
  fun _ _ _ hB => funext fun x => hB x.1 x.2

/-- **At the split `unit`, `ReadsOff` says the table reads only the points outside `B`.** -/
theorem OracleView.readsOff_unit_iff {V : OracleView X Y} {B : Set X} :
    V.ReadsOff (OracleSplit.unit Y) B ↔
      ∀ H H' : X → Y, (∀ z ∉ B, H z = H' z) → V.view H = V.view H' :=
  ⟨fun h H H' hB => h H H' (fun _ => rfl) hB, fun h H H' _ hB => h H H' hB⟩

end GordieHowe.RingSignature

namespace GordieHowe.Ring.MLDSAW1

open _root_.MLDSA GordieHowe.MLDSA GordieHowe.RingSignature GordieHowe.RingSignature.OracleSplit

variable {X Y Y₁ Y₂ : Type} [AddGroup Y] [AddGroup Y₁] [AddGroup Y₂] (sp : OracleSplit Y Y₁ Y₂)

/-! ### The base signer's oracles read the first component -/

section Base

variable {p : Params} {prims : Primitives p} {Msg : Type} {N reps T : ℕ}

/-- **The decodings of the oracles of the ring publishing `w₁` read only the first component**:
the message representatives, commitment hashes and check values decoded from two values with the
same first component agree. -/
structure W1Oracles.ReadsFst (O : W1Oracles X Y p prims Msg N reps) : Prop where
  /-- The message representatives read only the first component. -/
  muAns_eq : ∀ y y', (sp y).1 = (sp y').1 → O.muAns y = O.muAns y'
  /-- The commitment hashes read only the first component. -/
  chAns_eq : ∀ y y', (sp y).1 = (sp y').1 → O.chAns y = O.chAns y'
  /-- The check values read only the first component. -/
  gAns_eq : ∀ y y', (sp y).1 = (sp y').1 → O.gAns y = O.gAns y'

/-- **The decodings of the mask oracle read only the first component.** -/
def _root_.GordieHowe.MLDSA.MaskOracle.ReadsFst (M : MaskOracle X Y p T Msg) : Prop :=
  ∀ y y', (sp y).1 = (sp y').1 → M.ans y = M.ans y'

/-- **Every decoding reads only the first component of the split `unit`.** -/
theorem W1Oracles.readsFst_unit (O : W1Oracles X Y p prims Msg N reps) :
    O.ReadsFst (OracleSplit.unit Y) where
  muAns_eq _ _ h := congrArg O.muAns h
  chAns_eq _ _ h := congrArg O.chAns h
  gAns_eq _ _ h := congrArg O.gAns h

/-- **Every mask decoding reads only the first component of the split `unit`.** -/
theorem _root_.GordieHowe.MLDSA.MaskOracle.readsFst_unit (M : MaskOracle X Y p T Msg) :
    M.ReadsFst (OracleSplit.unit Y) :=
  fun _ _ h => congrArg M.ans h

/-- **The oracles of the first component read through the split**: the points of `O`, the values
decoded from the first component. -/
def W1Oracles.viaBase (O : W1Oracles X Y₁ p prims Msg N reps) :
    W1Oracles X Y p prims Msg N reps where
  muPt := O.muPt
  muAns y := O.muAns (sp y).1
  chPt := O.chPt
  chAns y := O.chAns (sp y).1
  gPt := O.gPt
  gAns y := O.gAns (sp y).1

/-- **The mask oracle of the first component read through the split.** -/
def _root_.GordieHowe.MLDSA.MaskOracle.viaBase (M : MaskOracle X Y₁ p T Msg) :
    MaskOracle X Y p T Msg where
  pt := M.pt
  ans y := M.ans (sp y).1

/-- `viaBase` reads only the first component. -/
theorem W1Oracles.readsFst_viaBase (O : W1Oracles X Y₁ p prims Msg N reps) :
    (O.viaBase sp).ReadsFst sp where
  muAns_eq _ _ h := congrArg O.muAns h
  chAns_eq _ _ h := congrArg O.chAns h
  gAns_eq _ _ h := congrArg O.gAns h

/-- The mask oracle `viaBase` reads only the first component. -/
theorem _root_.GordieHowe.MLDSA.MaskOracle.readsFst_viaBase (M : MaskOracle X Y₁ p T Msg) :
    (M.viaBase sp).ReadsFst sp :=
  fun _ _ h => congrArg M.ans h

/-- The message-representative oracle of `viaBase` is that of the base component. -/
theorem W1Oracles.muOrc_viaBase (O : W1Oracles X Y₁ p prims Msg N reps) (H : X → Y) :
    (O.viaBase sp).muOrc H = O.muOrc (base sp H) :=
  rfl

/-- The commitment-hash oracle of `viaBase` is that of the base component. -/
theorem W1Oracles.chOrc_viaBase (O : W1Oracles X Y₁ p prims Msg N reps) (H : X → Y) :
    (O.viaBase sp).chOrc H = O.chOrc (base sp H) :=
  rfl

/-- The commitment hash of `viaBase` is that of the base component. -/
theorem W1Oracles.hOrc_viaBase (O : W1Oracles X Y₁ p prims Msg N reps) (H : X → Y) :
    (O.viaBase sp).hOrc H = O.hOrc (base sp H) :=
  rfl

/-- The check oracle of `viaBase` is that of the base component. -/
theorem W1Oracles.gOrc_viaBase (O : W1Oracles X Y₁ p prims Msg N reps) (H : X → Y) :
    (O.viaBase sp).gOrc H = O.gOrc (base sp H) :=
  rfl

end Base

end GordieHowe.Ring.MLDSAW1
