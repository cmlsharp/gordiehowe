-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.FieldProof.CommitProve
public import GordieHowe.ProofSystem.FieldProof.CircuitShape
public import GordieHowe.Model.IOP.RBRStable
public import GordieHowe.Model.IOP.CommitPhase
public import GordieHowe.Headline

@[expose] public section

/-!
# The proof of one circuit: a masked row reduction and a commit-and-prove system

A **circuit proof** (`GordieHowe.FieldProof`) is one circuit's sub-proof in a multi-circuit protocol: a
masked row reduction (`MaskedRowReduction`, the circuit's GKR or sumcheck run with its messages masked by committed pads)
followed by a commit-and-prove system (`CommitProve`) proving the masked row reduction's deferred rows on the
committed cells. The cells hold the circuit's witness and the pads; `readout` reads the witness the
circuit proves a relation about. This is the construction of Frigo–shelat Protocol 2.5 (p. 9) and
CHVY25 Figure 1 (masked GKR, then Ligero on the deferred checks), generic in the masked row reduction and in
the commit-and-prove system.

`GordieHowe.FieldProof` is the computational part (the two protocols and the readout); the round errors
with the soundness of the two parts are `GordieHowe.FieldProof.Sound`. The protocol, the
verdict (`verdict`, with `toShape` the computational part as a `GordieHowe.FieldProof.Shape`), the honest prover
(`Honest.toShape`) and the simulator (`simulator`) read the computational part only.

**The guarantees of a circuit proof.**
* **Soundness** (`GordieHowe.FieldProof.rbr_knowledge_soundness`, `knowledge_soundness`, `soundness`):
  on the statement of the public input and the commit phase, the proof phase is round-by-round
  knowledge sound for "the commit phase was bad (`Sound.commitBad`) or `holds`" at the extractor
  that reads the witness off the cells extracted from the commit phase
  (`GordieHowe.FieldProof.Shape.extractor`), with round errors `error`: the masked row reduction's reduction on the
  extracted cells, disjoined with the bad commit phase (`ClaimReduction.orConst`), followed by
  the commit-and-prove proof of its rows (`ClaimReduction.append`,
  `ClaimProof.rbrKnowledgeSoundness`). The commit phase's own events are charged by the protocol
  that runs it (`MultiCircuitIOP`).
* **Completeness** (`GordieHowe.FieldProof.completeness`): the honest masked-row-reduction transcript satisfies the
  rows on the committed cells (`MaskedRowReduction.Honest.complete`), and the commit-and-prove system
  accepts its honest proof of them (`CommitProve.Honest.complete`).
* **Zero knowledge** (`GordieHowe.FieldProof.simulator`, `GordieHowe.FieldProof.hvzk`): the masked-row-reduction
  simulator, then the commit-and-prove simulator on the context the simulated transcript fixes.
  The honest masked transcript has the masked-row-reduction simulator's law (`MaskedRowReduction.Honest.identDistrib`), and
  at each value of the pads the commit-and-prove view has the law of its simulator on that
  context (`CommitProve.Honest.hides`), so the pair has the composed simulator's law
  (`IdentDistrib.dependent`). This is CHVY25's proof of Claim 4.1 (simulate the padded messages, then
  simulate the Ligero proof on the public equations) for any masked row reduction and commit-and-prove
  system.

The verdict reads the oracle message at the queried leaves, and the commit rounds and every
proof-phase message in full (`GordieHowe.FieldProof.oracle`, `oracle_msg_queries`).
-/

namespace GordieHowe
open IOP

open ProtocolSpec
open scoped NNReal

/-- **The proof of one circuit** (see the module docstring): a masked row reduction `ip` on the
cells `ι → F`, a commit-and-prove system `cp` for its deferred rows at the context of the public
input and the masked transcript (`MaskedRowReduction.Context`), and the readout of the circuit's witness
from the cells. `sat` is the relation the masked row reduction proves on the cells (`FieldProof.Sound`),
and `readout_sound` states that it gives `holds` on the read witness. `readout` is part of the
extractor of every protocol built on the circuit proof, so an instance must give a computable,
polynomial-time definition. -/
structure FieldProof (Pub Wit : Type) (holds : Pub → Wit → Prop) where
  /-- The field of the cells. -/
  F : Type
  [field : Field F]
  /-- The cell coordinates. -/
  ι : Type
  [fintypeι : Fintype ι]
  /-- The relation the masked row reduction proves on the cells. -/
  sat : Pub → (ι → F) → Prop
  /-- The masked row reduction. -/
  ip : FieldProof.MaskedRowReduction F ι Pub (ι → F) id
  /-- The commit-and-prove system for the masked row reduction's rows. -/
  cp : FieldProof.CommitProve F ι ip.products ip.Context ip.rowsAt
  /-- The circuit's witness read from the cells. -/
  readout : (ι → F) → Wit
  /-- `sat` on extracted cells gives the relation on the read witness. Only extracted cells are
  quantified, since the extraction may confine the cells: Ligero with the prefix-row test confines
  the extracted prefix cells to the subfield (`Ligero.MaskRow.Setup.in_extract_confined`). -/
  readout_sound : ∀ p O r, sat p (cp.extract O r) → holds p (readout (cp.extract O r))

attribute [instance] FieldProof.field FieldProof.fintypeι

namespace FieldProof

variable {Pub Wit : Type} {holds : Pub → Wit → Prop} (C : FieldProof Pub Wit holds)

/-- **The soundness of a circuit proof**: the masked row reduction's round errors with its soundness for
`sat`, and the commit-and-prove system's commit-phase and proof-phase errors with its
soundness. -/
structure Sound where
  /-- The masked row reduction's round errors. -/
  ipε : C.ip.spec.ChallengeIdx → ℝ≥0
  /-- The masked row reduction proves `sat` on the cells. -/
  ipSound : C.ip.Sound C.sat ipε
  /-- The commit-and-prove system's commit-phase errors. -/
  cpεc : C.cp.commitRounds.ChallengeIdx → ℝ≥0
  /-- The commit-and-prove system's proof-phase errors. -/
  cpε : C.cp.spec.ChallengeIdx → ℝ≥0
  /-- The commit-and-prove system proves the rows on the extracted cells, or its commit phase was
  bad. -/
  cpSound : C.cp.Sound cpεc cpε

variable {C} in
/-- **The circuit proof's commit phase was bad** (`CommitProve.CommitBad` at the commit-and-prove
system's events). -/
def Sound.commitBad (S : C.Sound) (O : C.cp.Com) (r : C.cp.Rounds) : Prop :=
  C.cp.CommitBad S.cpSound.commitEvent O r

/-! ### The protocol -/

/-- The number of rounds of the proof phase: the masked row reduction's, then the commit-and-prove
system's. -/
abbrev n : ℕ := C.ip.n + C.cp.n

/-- **The proof phase**: the masked row reduction, then the commit-and-prove proof. -/
abbrev spec : ProtocolSpec C.n := C.ip.spec ++ C.cp.spec

/-- The proof phase draws a challenge: the commit-and-prove system's. -/
instance : Nonempty C.spec.ChallengeIdx := by
  obtain ⟨j⟩ := C.cp.nonemptyIdx
  exact ⟨ChallengeIdx.inr j⟩

/-- **The verdict** on the public input, the commit phase and the proof-phase transcript: the
commit-and-prove verifier at the context of the public input and the masked transcript. -/
def verdict (p : Pub) (O : C.cp.Com) (r : C.cp.Rounds) (tr : C.spec.Transcript (Fin.last C.n)) :
    Bool :=
  C.cp.V ⟨⟨p, tr.left⟩, O, r⟩ tr.right

/-- **The computational part of the circuit proof**: the commit-and-prove system's commit phase,
read by `readout ∘ extract`, the proof phase and the verdict. -/
abbrev toShape : Shape Pub Wit where
  Com := C.cp.Com
  nc := C.cp.nc
  commitRounds := C.cp.commitRounds
  ext O r := C.readout (C.cp.extract O r)
  n := C.n
  spec := C.spec
  V := C.verdict

/-! ### Soundness -/

variable {C}

/-- **The round errors of a circuit proof**: the masked row reduction's, then the commit-and-prove
system's. -/
abbrev Sound.error (S : C.Sound) : C.spec.ChallengeIdx → ℝ≥0 := appendError S.ipε S.cpε

/-- The errors of a circuit proof sum to the masked row reduction's and the commit-and-prove system's. -/
theorem Sound.sum_error (S : C.Sound) : ∑ i, S.error i = ∑ i, S.ipε i + ∑ j, S.cpε j :=
  sum_appendError _ _

/-- A bound on the masked row reduction's and the commit-and-prove system's errors bounds every error of the
circuit proof. -/
theorem Sound.error_le (S : C.Sound) {δ : ℝ≥0} (hip : ∀ j, S.ipε j ≤ δ) (hcp : ∀ j, S.cpε j ≤ δ)
    (i : C.spec.ChallengeIdx) : S.error i ≤ δ :=
  appendError_le hip hcp i

variable (S : C.Sound)

/-- The circuit proof on the cells: the masked row reduction's reduction on the extracted cells, disjoined
with a bad commit phase (`ClaimReduction.orConst`), then the commit-and-prove proof of its rows,
relative to "the commit phase was bad or `sat` on the extracted cells". -/
def Sound.onCells :
    ClaimProof C.spec (Shape.Statement Pub C.cp.Com C.cp.Rounds) S.error :=
  ((S.ipSound.reduction.comap fun s : Shape.Statement Pub C.cp.Com C.cp.Rounds =>
    (⟨s.pub, C.cp.extract s.com s.rounds⟩ : MaskedRowReduction.Instance Pub (C.ι → C.F))).orConst
      fun s => S.commitBad s.com s.rounds).append
    (S.cpSound.claimProof.comap fun c => ⟨⟨c.1.pub, c.2⟩, c.1.com, c.1.rounds⟩)
    fun c tr h => ((S.cpSound.claim_iff _).mp h).imp id fun hr =>
      (S.ipSound.claimOut_iff c.pub (C.cp.extract c.com c.rounds) tr).mpr hr

/-- **The soundness of a circuit proof as that of its computational part**, for "the commit
phase was bad or `holds` on the read witness": the commit-and-prove system's commit-phase events
(`CommitProve.Sound.commitState`), and the masked row reduction's reduction on the extracted cells, then the
commit-and-prove proof of its rows, with the errors `error`; `readout_sound` turns `sat` into
`holds`. -/
def Sound.toShape : C.toShape.Sound holds where
  εc := S.cpεc
  commit := S.cpSound.commitState
  ε := S.error
  proof := S.onCells.weaken
    (fun s => S.commitBad s.com s.rounds ∨ holds s.pub (C.readout (C.cp.extract s.com s.rounds)))
    fun s hs => hs.imp id fun h => C.readout_sound s.pub s.com s.rounds ((S.ipSound.claim_iff _ _).mp h)
  V_eq _ _ := rfl
  claim_imp _ h := h

/-- **Round-by-round knowledge soundness of a circuit proof**: the proof phase of a circuit proof is
round-by-round knowledge sound for "the commit phase was bad (`Sound.commitBad`) or `holds`" at the
statement (the public input and the commit phase), at the named extractor `Shape.extractor`
(the witness read from the cells extracted from the commit phase, `readout ∘ extract`) and the state
function `Sound.stateFn`, with round errors `S.error`: the masked row reduction's reduction errors, then the
commit-and-prove system's errors. -/
theorem rbr_knowledge_soundness :
    rbrKnowledgeSoundness (C.toShape.relation holds S.commitBad) C.toShape.verifier
      C.toShape.extractor S.toShape.stateFn S.error :=
  S.toShape.rbrKnowledgeSoundness

/-- **Knowledge soundness of a circuit proof** at the named extractor `Shape.extractor`, for
"the commit phase was bad or `holds`", with error the masked row reduction's summed errors plus the
commit-and-prove system's. -/
theorem knowledge_soundness :
    knowledgeSoundness (C.toShape.relation holds S.commitBad) C.toShape.verifier
      C.toShape.extractor (∑ j, S.ipε j + ∑ j, S.cpε j) := by
  have h := knowledgeSoundness_of_rbr_of_stable (rbr_knowledge_soundness S)
    Shape.extractor_stable
  rw [← S.sum_error]
  exact h

/-! ### How the verdict reads -/

variable (C) in
/-- **How the circuit proof's verdict reads**: the oracle message at the commit-and-prove
system's queried leaves, under its own challenges; the commit rounds and every proof-phase
message in full. -/
def oracle : C.toShape.Oracle where
  Idx := Fin C.cp.nLeaves
  Ans := C.cp.Leaf
  com := C.cp.comView.comap Challenges.right
  MIdx _ := Unit
  MAns i := C.spec.Type i.1
  msg _ := MessageView.plain _ _
  reads p ch O O' r r' tr tr' htr htr' hview := by
    obtain ⟨hcom, hr, hmsg⟩ := Shape.Reading.view_eq_iff.mp hview
    subst hr
    have e : tr = tr' := Transcript.ext_of_messages htr htr' fun i =>
      MessageView.eq_of_see_plain (hmsg i)
    subst e
    exact C.cp.V_eq_of_see ⟨p, tr.left⟩ (Transcript.right_challenge htr) hcom

variable (C) in
/-- The view of the circuit proof from the commit-and-prove system's view of the oracle message,
the commit rounds and the full proof-phase transcript. -/
def assemble (leaves : Fin C.cp.nLeaves → Option C.cp.Leaf) (r : C.cp.Rounds)
    (tr : C.spec.Transcript (Fin.last C.n)) : C.oracle.View :=
  ⟨leaves, r, fun i _ => some (tr i.1)⟩

/-! ### The honest prover -/

variable (C) in
/-- **The simulator data of a circuit proof**: the masked row reduction's simulator and the
commit-and-prove system's simulator (`FieldProof.simulator` assembles the view from the two). Data
apart from the honest prover (`Honest`). -/
structure Sim where
  /-- The masked row reduction's simulator. -/
  ip : C.ip.Sim
  /-- The commit-and-prove system's simulator. -/
  cp : C.cp.Sim

variable (C) in
/-- **The honest prover of a circuit proof** on honest inputs `In` in the domain `dom`, simulated
by `S`: the masked row reduction's honest prover, the commit-and-prove system's honest prover, and
the committed cells `cells x π`, which hold the honest input and the pads at their coordinates (the layout): they
commit the input and the pads in the masked row reduction's sense (`commits`) and are admissible for the
commit-and-prove system (`admissible`). The cells are a function of the honest input and the
pads only, since they are committed before the public input is fixed. -/
structure Honest (S : C.Sim) (In : Type) (dom : Pub → In → Prop) where
  /-- The masked row reduction's honest prover. -/
  ip : C.ip.Honest In dom S.ip
  /-- The commit-and-prove system's honest prover. -/
  cp : C.cp.Honest S.cp
  /-- The committed cells. -/
  cells : In → ip.Pads → C.ι → C.F
  /-- The cells commit the honest input and the pads. -/
  commits : ∀ p x π, dom p x → ip.Commits p x π (cells x π)
  /-- The cells are admissible for the commit-and-prove system. -/
  admissible : ∀ p x π, dom p x → cp.Admissible (cells x π)

variable {S : C.Sim} {In : Type} {dom : Pub → In → Prop}

/-- **The honest prover's coins**: the masked row reduction's pads and the commit-and-prove system's
blinding. -/
structure Honest.Coins (Hc : C.Honest S In dom) where
  /-- The masked row reduction's pads. -/
  pads : Hc.ip.Pads
  /-- The commit-and-prove system's coins. -/
  blinding : Hc.cp.Coins

/-- The coins as a pair. -/
def Honest.coinsEquiv (Hc : C.Honest S In dom) : Hc.Coins ≃ Hc.ip.Pads × Hc.cp.Coins where
  toFun c := (c.pads, c.blinding)
  invFun c := ⟨c.1, c.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance (Hc : C.Honest S In dom) : Fintype Hc.Coins := Fintype.ofEquiv _ Hc.coinsEquiv.symm
instance (Hc : C.Honest S In dom) : Nonempty Hc.Coins := Hc.coinsEquiv.nonempty

/-- **The honest oracle message**: the commit-and-prove oracle message for the cells. -/
def Honest.commit (Hc : C.Honest S In dom) (x : In) (ρ : Hc.Coins) : C.cp.Com :=
  Hc.cp.commit (Hc.cells x ρ.pads) ρ.blinding

/-- **The honest commit rounds**: the commit-and-prove commit rounds for the cells. -/
def Honest.commitRounds (Hc : C.Honest S In dom) (x : In) (ρ : Hc.Coins) :
    CausalTranscript C.cp.commitRounds :=
  Hc.cp.commitRounds (Hc.cells x ρ.pads) ρ.blinding

/-- The honest commit rounds at the commit-round challenges `chc`. -/
abbrev Honest.rounds (Hc : C.Honest S In dom) (x : In) (ρ : Hc.Coins)
    (chc : C.cp.commitRounds.Challenges) : C.cp.Rounds :=
  (Hc.commitRounds x ρ).transcript chc

/-- **The honest proof**: the masked row reduction's honest transcript, then the honest commit-and-prove
proof at the context it fixes and the commit rounds. -/
def Honest.prove (Hc : C.Honest S In dom) (p : Pub) (x : In) (ρ : Hc.Coins) (r : C.cp.Rounds) :
    CausalTranscript C.spec :=
  (Hc.ip.prover p x ρ.pads).append fun tr =>
    Hc.cp.prove ⟨p, tr⟩ (Hc.cells x ρ.pads) ρ.blinding r

/-- The honest circuit proof as an honest prover of its computational part. -/
def Honest.toShape (Hc : C.Honest S In dom) : C.toShape.Honest In where
  Coins := Hc.Coins
  commit := Hc.commit
  commitRounds := Hc.commitRounds
  prove := Hc.prove

/-- **Completeness of a circuit proof**: on the domain, the verdict accepts the honest proof at
every challenge of the commit rounds and of the proof phase. -/
theorem completeness (Hc : C.Honest S In dom) {p : Pub} {x : In} (hx : dom p x)
    (ρ : Hc.Coins) (chc : C.cp.commitRounds.Challenges) (ch : C.spec.Challenges) :
    C.verdict p (Hc.commit x ρ) (Hc.rounds x ρ chc)
      ((Hc.prove p x ρ (Hc.rounds x ρ chc)).transcript ch) = true := by
  have e₁ := CausalTranscript.append_left (Hc.ip.prover p x ρ.pads)
    (fun tr => Hc.cp.prove ⟨p, tr⟩ (Hc.cells x ρ.pads) ρ.blinding (Hc.rounds x ρ chc)) ch
  have e₂ := CausalTranscript.append_right (Hc.ip.prover p x ρ.pads)
    (fun tr => Hc.cp.prove ⟨p, tr⟩ (Hc.cells x ρ.pads) ρ.blinding (Hc.rounds x ρ chc)) ch
  have h := Hc.cp.complete ⟨p, (Hc.ip.prover p x ρ.pads).transcript ch.left⟩ _
    ⟨Hc.admissible p x ρ.pads hx,
      Hc.ip.complete p x hx ρ.pads _ (Hc.commits p x ρ.pads hx) ch.left⟩ ρ.blinding chc ch.right
  exact (congrArg₂ (fun a b => C.cp.V ⟨⟨p, a⟩, Hc.cp.commit (Hc.cells x ρ.pads) ρ.blinding,
    Hc.rounds x ρ chc⟩ b) e₁ e₂).trans h

/-! ### The simulator -/

/-- **The simulator's coins**: the masked-row-reduction simulator's and the commit-and-prove
simulator's. -/
structure Sim.SimCoins (S : C.Sim) where
  /-- The masked-row-reduction simulator's coins. -/
  ip : S.ip.SimCoins
  /-- The commit-and-prove simulator's coins. -/
  cp : S.cp.SimCoins

/-- The simulator's coins as a pair. -/
def Sim.simCoinsEquiv (S : C.Sim) : S.SimCoins ≃ S.ip.SimCoins × S.cp.SimCoins where
  toFun c := (c.ip, c.cp)
  invFun c := ⟨c.1, c.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance (S : C.Sim) : Fintype S.SimCoins := Fintype.ofEquiv _ S.simCoinsEquiv.symm
instance (S : C.Sim) : Nonempty S.SimCoins := S.simCoinsEquiv.nonempty

/-- **The simulator of a circuit proof**: the masked-row-reduction simulator on the public input and the
masked row reduction's challenges, then the commit-and-prove simulator at the context of the public input
and the simulated transcript, at its own challenges (of the commit rounds and of its proof
phase); the view is assembled from the two.

Running time: one run of each of the two simulators (their docstrings) and the assembly, linear
in the transcript length. This running time is argued here, not proved in Lean. -/
def simulator (S : C.Sim) : Shape.Simulator C.oracle where
  Coins := S.SimCoins
  sim p chc ch s :=
    let trIP := S.ip.sim p ch.left s.ip
    let v := S.cp.sim ⟨p, trIP⟩ chc ch.right s.cp
    C.assemble v.leaves v.rounds (Transcript.join trIP v.transcript)

/-- **Zero knowledge of a circuit proof**: the simulator of a circuit proof is perfect on the
domain: the masked-row-reduction simulation (`MaskedRowReduction.Honest.identDistrib`) and, at each value of the pads,
the commit-and-prove simulation at the context the honest masked transcript fixes
(`CommitProve.Honest.hides`, whose hypotheses are the layout facts and the masked row reduction's
completeness), composed by `IdentDistrib.dependent`. -/
theorem hvzk (Hc : C.Honest S In dom) : (simulator S).Perfect Hc.toShape dom := by
  intro p x hx chc ch
  have key := (IdentDistrib.dependent
    (f₁ := fun π => (Hc.ip.prover p x π).transcript ch.left) (g₁ := S.ip.sim p ch.left)
    (f₂ := fun π r => C.cp.view ch.right (Hc.cp.commit (Hc.cells x π) r)
      ((Hc.cp.commitRounds (Hc.cells x π) r).transcript chc)
      ((Hc.cp.prove ⟨p, (Hc.ip.prover p x π).transcript ch.left⟩ (Hc.cells x π) r
        ((Hc.cp.commitRounds (Hc.cells x π) r).transcript chc)).transcript ch.right))
    (g₂ := fun v => S.cp.sim ⟨p, v⟩ chc ch.right)
    (Hc.ip.identDistrib p x hx ch.left) fun π =>
      Hc.cp.hides ⟨p, (Hc.ip.prover p x π).transcript ch.left⟩ _
        ⟨Hc.admissible p x π hx, Hc.ip.complete p x hx π _ (Hc.commits p x π hx) ch.left⟩
        chc ch.right).comp
    fun v => C.assemble v.2.leaves v.2.rounds (Transcript.join v.1 v.2.transcript)
  refine IdentDistrib.trans (IdentDistrib.of_equiv Hc.coinsEquiv fun ρ => ?_)
    (key.trans (IdentDistrib.of_equiv S.simCoinsEquiv.symm fun _ => rfl))
  exact congrArg (Shape.Reading.View.mk _ _) (funext fun i => MessageView.see_plain _ _)

end FieldProof

end GordieHowe
