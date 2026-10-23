-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.IOP.RBR
public import GordieHowe.Foundations.Probability.IdentDistrib
public import GordieHowe.Foundations.ToMathlib.PMFTVJoint

@[expose] public section

/-!
# Honest-verifier zero-knowledge in the interactive oracle model

Two forms.
- `IOP.HVZK` is CY24 Definition 23.1.8 (p. 260): a simulator (`IOP.JointSimulator`) outputs,
  from the statement and its own coins, the challenges together with a view, and for every pair in
  the relation the honest verifier's view (CY24 Definition 23.1.7: uniform challenges and the
  answers to the verifier's queries, `honestView`) and the simulator's output are `ε`-close in
  statistical distance. Through `GordieHowe.IOP.CausalHVZK.ofIOP` it is the hypothesis of the BCS zero-knowledge
  theorem (`SPBCS.everlastingZeroKnowledge`).
- `IOP.HVZKOffExceptions` (exception form) follows CHVY25 Definition 2.5 (honest-verifier
  zero-knowledge IOP), which is perfect zero knowledge, relaxed by an exception event: for each
  challenge vector outside an event of probability at most `δ` the laws are equal, with
  distributions as `PMF`s of uniform coins (`IdentDistrib`) and the exception probability as
  `Pr[ch ← P.Challenges : bad x w ch]`. It is stated at a simulator that receives the challenges
  (`IOP.Simulator`); it is what the instances' proofs produce, and it implies `HVZK` at error `δ` at
  the simulator that draws uniform challenges and runs it at them (`Simulator.joint`,
  `HVZKOffExceptions.hvzk`).

**What the verifier sees.** Every prover message is a function table
`read m : ι → A` that the verifier reads at a set of positions determined by
the challenges (`MessageView`). `read` must be injective, so the table is the
whole message. A message the verifier reads in full is `MessageView.plain`: one
position, always queried. The view of a transcript is fixed by these choices:
each message's entries at its queried positions (`MessageView.see`). `IOP`
pairs a verifier with the views of its messages and requires that the
verifier's decision depends only on the view: the verifier is an IOP
verifier.

**The honest prover's randomness.** An honest prover is a deterministic
prover for each value of its random coins `ρ : R`, a finite type holding every
pad and blinding value it draws.

**Zero-knowledge.** For every statement–witness pair in the relation and every
challenge vector outside an exception set `bad`, the view under uniform
coins has the same distribution as the simulator's output on the statement,
the challenges and uniform simulator coins. Equal distributions for each fixed
good challenge vector give joint distributions with the challenges whose
statistical distance is at most `δ`, the probability of a bad challenge vector,
since the honest verifier draws them uniformly and independently of the
prover. With `bad` empty the simulation is perfect. The exception set exists
for events where the honest prover fails on a challenge (the completeness
events), which may depend on the witness.

The simulator (`IOP.Simulator`) is a function of the statement, the challenges
and its own coins only, and `IOP.HVZKOffExceptions` is stated at a named simulator and a named
exception event. Lean has no cost model; each simulator's docstring states its running time. The
commitment compilation (Merkle hiding, random-oracle programming) belongs to the
non-interactive layer.
-/

namespace PMF

/-- **Total variation distance is invariant under an equivalence**: data processing in both
directions (`PMF.tvDist_map_le`). About Mathlib objects only; a candidate for
`GordieHowe/Foundations/ToMathlib/PMFTV.lean`. -/
theorem tvDist_map_equiv {α β : Type*} (e : α ≃ β) (p q : PMF α) :
    tvDist (p.map e) (q.map e) = tvDist p q := by
  refine le_antisymm (tvDist_map_le p q e) ?_
  have h := tvDist_map_le (p.map e) (q.map e) e.symm
  simp only [PMF.map_comp, Equiv.symm_comp_self, PMF.map_id] at h
  exact h

end PMF

namespace GordieHowe.IOP

open ProtocolSpec
open scoped NNReal BigOperators

variable {n : ℕ}

/-- How the verifier reads a prover message of type `M`: as the table
`read m : ι → A`, at the positions `queries ch`. The positions have decidable equality, so that
what the verifier sees (`see`) is computable. -/
structure MessageView (M Ch ι A : Type) where
  read : M → ι → A
  read_injective : Function.Injective read
  queries : Ch → Finset ι
  [decEq : DecidableEq ι]

namespace MessageView

variable {M Ch Ch' ι A M₁ M₂ ι₁ ι₂ A₁ A₂ : Type}

/-- A message read in full: one position, always queried. -/
def plain (M Ch : Type) : MessageView M Ch Unit M where
  read m _ := m
  read_injective _ _ h := congrFun h ()
  queries _ := Finset.univ

/-- What the verifier sees of message `m` under the challenges `ch`. -/
def see (O : MessageView M Ch ι A) (ch : Ch) (m : M) : ι → Option A :=
  letI := O.decEq
  fun j => if j ∈ O.queries ch then some (O.read m j) else none

/-- The same table, with its queries read through a map of the challenges. -/
def comap (O : MessageView M Ch ι A) (f : Ch' → Ch) : MessageView M Ch' ι A where
  read := O.read
  read_injective := O.read_injective
  queries := O.queries ∘ f
  decEq := O.decEq

@[simp] theorem see_comap (O : MessageView M Ch ι A) (f : Ch' → Ch) (ch : Ch') (m : M) :
    (O.comap f).see ch m = O.see (f ch) m := rfl

@[simp] theorem see_plain (ch : Ch) (m : M) : (plain M Ch).see ch m = fun _ => some m := by
  funext _
  simp [see, plain]

/-- A message read in full is determined by what the verifier sees of it. -/
theorem eq_of_see_plain {ch : Ch} {m m' : M} (h : (plain M Ch).see ch m = (plain M Ch).see ch m') :
    m = m' := by
  rw [see_plain, see_plain] at h
  exact Option.some_injective _ (congrFun h ())

/-- A message view whose view determines the message. -/
def SeeInjective (O : MessageView M Ch ι A) : Prop :=
  ∀ ch (m m' : M), O.see ch m = O.see ch m' → m = m'

/-- At a queried position the verifier sees the table's entry. -/
theorem see_of_mem (O : MessageView M Ch ι A) {ch : Ch} {j : ι} (h : j ∈ O.queries ch) (m : M) :
    O.see ch m j = some (O.read m j) := by
  simp only [see, h, ↓reduceIte]

/-- A message read in full is determined by its view. -/
theorem seeInjective_plain : (plain M Ch).SeeInjective := fun _ _ _ h => eq_of_see_plain h

/-- **An explicit read-off of a message from what the verifier sees of it**: a function of the
challenges and the seen entries returning the message on every view of a message (`dec_see`).
It is data, so a simulator can run it; the views that read a message in full have one
(`Decoder.plain`). -/
structure Decoder (O : MessageView M Ch ι A) where
  dec : Ch → (ι → Option A) → Option M
  dec_see : ∀ ch m, dec ch (O.see ch m) = some m

/-- A message read in full is read off its one entry. -/
def Decoder.plain : (MessageView.plain M Ch).Decoder where
  dec _ v := v ()
  dec_see ch m := by rw [see_plain]

/-- A decoder read through a map of the challenges. -/
def Decoder.comap {O : MessageView M Ch ι A} (D : O.Decoder) (f : Ch' → Ch) : (O.comap f).Decoder where
  dec ch v := D.dec (f ch) v
  dec_see ch m := D.dec_see (f ch) m

/-- A view with a decoder determines the message. -/
theorem Decoder.seeInjective {O : MessageView M Ch ι A} (D : O.Decoder) : O.SeeInjective :=
  fun ch m m' h => Option.some_injective _ ((D.dec_see ch m).symm.trans (h ▸ D.dec_see ch m'))

/-- Two tables read as one table on the pair of messages, each at its own
queries. -/
def prod (O₁ : MessageView M₁ Ch ι₁ A₁) (O₂ : MessageView M₂ Ch ι₂ A₂) :
    MessageView (M₁ × M₂) Ch (ι₁ ⊕ ι₂) (A₁ ⊕ A₂) where
  read m := Sum.elim (fun j => .inl (O₁.read m.1 j)) (fun j => .inr (O₂.read m.2 j))
  read_injective _ _ h := Prod.ext
    (O₁.read_injective (funext fun j => Sum.inl_injective (congrFun h (.inl j))))
    (O₂.read_injective (funext fun j => Sum.inr_injective (congrFun h (.inr j))))
  queries ch := (O₁.queries ch).disjSum (O₂.queries ch)
  decEq := letI := O₁.decEq; letI := O₂.decEq; inferInstance

/-- What the verifier sees of a pair is what it sees of each part. -/
theorem see_prod (O₁ : MessageView M₁ Ch ι₁ A₁) (O₂ : MessageView M₂ Ch ι₂ A₂) (ch : Ch)
    (m : M₁ × M₂) :
    (O₁.prod O₂).see ch m =
      Sum.elim (fun j => (O₁.see ch m.1 j).map .inl) (fun j => (O₂.see ch m.2 j).map .inr) := by
  funext j
  rcases j with j | j
  · by_cases h : j ∈ O₁.queries ch <;> simp [see, prod, h]
  · by_cases h : j ∈ O₂.queries ch <;> simp [see, prod, h]

end MessageView

/-- The challenges of a full transcript. -/
def ProtocolSpec.Transcript.challenges {P : ProtocolSpec n} (tr : P.Transcript (Fin.last n)) :
    P.Challenges :=
  fun i => tr i.1

@[simp] theorem ProtocolSpec.Transcript.challenges_apply {P : ProtocolSpec n}
    (tr : P.Transcript (Fin.last n)) (i : P.ChallengeIdx) : tr.challenges i = tr i.1 := rfl

/-- **What the verifier sees of a full transcript** when it reads the prover messages through the
message views `msg`: the transcript's challenges and, of each prover message, its entries at the
positions queried under those challenges. -/
structure TranscriptView {P : ProtocolSpec n} {Idx Ans : P.MessageIdx → Type}
    (msg : ∀ i : P.MessageIdx, MessageView (P.Type i.1) P.Challenges (Idx i) (Ans i)) where
  /-- The challenges. -/
  challenges : P.Challenges
  /-- The seen entries of every prover message. -/
  entries : ∀ i : P.MessageIdx, Idx i → Option (Ans i)

namespace TranscriptView

variable {P : ProtocolSpec n} {Idx Ans : P.MessageIdx → Type}
  {msg : ∀ i : P.MessageIdx, MessageView (P.Type i.1) P.Challenges (Idx i) (Ans i)}

/-- The view of the full transcript `tr` through the message views `msg`. -/
def of (msg : ∀ i : P.MessageIdx, MessageView (P.Type i.1) P.Challenges (Idx i) (Ans i))
    (tr : P.Transcript (Fin.last n)) : TranscriptView msg :=
  ⟨tr.challenges, fun i => (msg i).see tr.challenges (tr i.1)⟩

/-- Two full transcripts have the same view exactly when they have the same challenges and the
verifier sees the same of every prover message under them. -/
theorem of_eq_iff {tr tr' : P.Transcript (Fin.last n)} :
    of msg tr = of msg tr' ↔ tr.challenges = tr'.challenges ∧
      ∀ i : P.MessageIdx, (msg i).see tr.challenges (tr i.1) = (msg i).see tr.challenges (tr' i.1) := by
  constructor
  · intro h
    have hc : tr.challenges = tr'.challenges := congrArg TranscriptView.challenges h
    refine ⟨hc, fun i => ?_⟩
    have he := congrFun (congrArg TranscriptView.entries h) i
    simp only [of] at he
    rw [he, hc]
  · rintro ⟨hc, he⟩
    simp only [of, ← hc]
    exact congrArg _ (funext he)

/-- Two full transcripts with the challenges `ch` on which the verifier sees the same of every
prover message under `ch` have the same view. -/
theorem of_eq_of_see {ch : P.Challenges} {tr tr' : P.Transcript (Fin.last n)}
    (htr : ∀ i : P.ChallengeIdx, tr i.1 = ch i) (htr' : ∀ i : P.ChallengeIdx, tr' i.1 = ch i)
    (h : ∀ i : P.MessageIdx, (msg i).see ch (tr i.1) = (msg i).see ch (tr' i.1)) :
    of msg tr = of msg tr' := by
  have hc : tr.challenges = ch := funext htr
  have hc' : tr'.challenges = ch := funext htr'
  exact of_eq_iff.mpr ⟨hc.trans hc'.symm, fun i => hc ▸ h i⟩

/-- **Query locality from the views at fixed challenges**: a decision on which any two full
transcripts with the challenges `ch` and the same seen entries under `ch` agree is a function of
the view of the transcript. -/
theorem reads_of {Stmt : Type} {V : Verifier P Stmt}
    (h : ∀ x (ch : P.Challenges) (tr tr' : P.Transcript (Fin.last n)),
      (∀ i : P.ChallengeIdx, tr i.1 = ch i) → (∀ i : P.ChallengeIdx, tr' i.1 = ch i) →
      (∀ i : P.MessageIdx, (msg i).see ch (tr i.1) = (msg i).see ch (tr' i.1)) → V x tr = V x tr')
    (x : Stmt) (tr tr' : P.Transcript (Fin.last n)) (hv : of msg tr = of msg tr') :
    V x tr = V x tr' := by
  obtain ⟨hc, he⟩ := of_eq_iff.mp hv
  exact h x tr.challenges tr tr' (fun _ => rfl) (fun i => (congrFun hc i).symm) he

end TranscriptView

/-- A verifier together with how it reads each prover message, such that its decision depends only
on what it reads. `reads` only requires the view to suffice for the decision, so a view could report
less than the verifier receives and make `HVZK` weaker. Each concrete IOP carries the obligation
that its views are what the C++ verifier reads; for the BCS transformation the compiled proof's
revealed data is a function of the view (`SPBCS.Base.Reveal.write_congr`,
`SPBCS.Base.Reveal.col_congr`). -/
structure IOP (P : ProtocolSpec n) (Stmt : Type) where
  V : Verifier P Stmt
  /-- The positions of each prover message. -/
  Idx : P.MessageIdx → Type
  /-- The entry type of each prover message. -/
  Ans : P.MessageIdx → Type
  msg : ∀ i : P.MessageIdx, MessageView (P.Type i.1) P.Challenges (Idx i) (Ans i)
  /-- **Query locality**: the decision is a function of the verifier's view of the transcript. -/
  reads : ∀ x (tr tr' : P.Transcript (Fin.last n)),
    TranscriptView.of msg tr = TranscriptView.of msg tr' → V x tr = V x tr'

namespace IOP

variable {P : ProtocolSpec n} {Stmt Wit : Type}

/-- The verifier's view: what it sees of every prover message. -/
def View (I : IOP P Stmt) : Type := ∀ i : P.MessageIdx, I.Idx i → Option (I.Ans i)

/-- The view of a transcript under the challenges `ch`. -/
def view (I : IOP P Stmt) (ch : P.Challenges) (tr : P.Transcript (Fin.last n)) :
    I.View :=
  fun i => (I.msg i).see ch (tr i.1)

/-- Two full transcripts with the challenges `ch` and the same view under `ch` get the same
decision (`reads`). -/
theorem V_eq_of_view (I : IOP P Stmt) (x : Stmt) {ch : P.Challenges}
    {tr tr' : P.Transcript (Fin.last n)} (htr : ∀ i : P.ChallengeIdx, tr i.1 = ch i)
    (htr' : ∀ i : P.ChallengeIdx, tr' i.1 = ch i) (h : I.view ch tr = I.view ch tr') :
    I.V x tr = I.V x tr' :=
  I.reads x tr tr' (TranscriptView.of_eq_of_see htr htr' fun i => congrFun h i)

/-- **An honest-verifier simulator** for the IOP `I`: from the statement, the challenges and
its own uniform coins, a view of `I`. It reads no witness. What it must achieve is
`IOP.HVZKOffExceptions`; it gives the joint simulator `Simulator.joint` of `IOP.HVZK`.

Zero-knowledge needs an efficient simulator: an unrestricted one can recover a witness by brute
force and run the honest prover, which reduces the notion to witness indistinguishability. Lean
has no cost model, so every simulator is a named definition whose docstring has a "Running time"
paragraph: what it computes and why it is polynomial in the relevant sizes. The Lean lint
`scripts/CostLint.lean`, run by `scripts/check.sh`, enforces the docstring for every
declaration whose type is a `Simulator`, however the value is constructed. A simulator written
inline inside a statement is not a declaration and is not caught, so headlines must name
theirs. -/
structure Simulator (I : IOP P Stmt) where
  /-- The simulator's coins. -/
  Coins : Type
  [fintype : Fintype Coins]
  [nonempty : Nonempty Coins]
  /-- The simulated view on the statement, the challenges and the coins. -/
  sim : Stmt → P.Challenges → Coins → I.View

attribute [instance] Simulator.fintype Simulator.nonempty

open Classical in
/-- **Honest-verifier zero-knowledge** of `honest` on `rel` at the simulator `S`, with
statistical error `δ` and exception event `bad` (CHVY25 Definition 2.5, perfect zero knowledge,
with the statistical error of CY24 Definition 23.1.8, p. 260): the exception event has
probability at most `δ` under uniform challenges for each pair in the relation (`bad_le`), and
for each pair in the relation and each challenge vector outside it the real view under uniform
prover coins and the simulated view under uniform simulator coins have the same distribution
(`simulates`). Perfect when `bad` is empty. The exception event may depend on the witness; it
holds the challenges on which the honest prover fails (the completeness events). -/
structure HVZKOffExceptions [∀ i, Fintype (P.Challenge i)] [∀ i, Nonempty (P.Challenge i)]
    (I : IOP P Stmt)
    (rel : Set (Stmt × Wit)) {R : Type} [Fintype R] [Nonempty R] (honest : Wit → R → Prover P Stmt)
    (S : I.Simulator) (δ : ℝ≥0) (bad : Stmt → Wit → P.Challenges → Prop) : Prop where
  /-- The exception event has probability at most `δ` on the relation. -/
  bad_le : ∀ x w, (x, w) ∈ rel → Pr[ch ← P.Challenges : bad x w ch] ≤ δ
  /-- Outside the exception event the honest view has the simulator's law. -/
  simulates : ∀ x w, (x, w) ∈ rel → ∀ ch, ¬ bad x w ch →
    (fun ρ => I.view ch ((honest w ρ).run x ch)) =ᵈ S.sim x ch

variable [∀ i, Fintype (P.Challenge i)] [∀ i, Nonempty (P.Challenge i)] {I : IOP P Stmt}
  {rel : Set (Stmt × Wit)} {R : Type} [Fintype R] [Nonempty R] {honest : Wit → R → Prover P Stmt}
  {S : I.Simulator} {δ : ℝ≥0} {bad : Stmt → Wit → P.Challenges → Prop}

/-- **Honest-verifier zero knowledge transfers to a decoded honest input**: if `honest` on
inputs `In` is zero knowledge for `relI` at `S`, and `dec` decodes an input of `relI` from every
pair of `rel`, then the prover that decodes its input from the statement and the witness
(`Prover.ofStatement`) is zero knowledge for `rel` at `S` with the same error, at the exception
event read at the decoded input. -/
theorem HVZKOffExceptions.decode {In : Type} {relI : Set (Stmt × In)}
    {honest : In → R → Prover P Stmt}
    {bad : Stmt → In → P.Challenges → Prop} (h : I.HVZKOffExceptions relI honest S δ bad)
    (dec : Stmt → Wit → In) (hdec : ∀ x w, (x, w) ∈ rel → (x, dec x w) ∈ relI) :
    I.HVZKOffExceptions rel (fun w ρ => Prover.ofStatement fun x => honest (dec x w) ρ) S δ
      (fun x w => bad x (dec x w)) where
  bad_le x w hw := h.bad_le x _ (hdec x w hw)
  simulates x w hw ch hch := by
    simp only [Prover.run_ofStatement]
    exact h.simulates x _ (hdec x w hw) ch hch

/-- **Honest-verifier zero knowledge through a map of views**: if the view of `J` is the image of
the view of `I` under `f`, and the simulator `S'` of `J` has the law of `S` read through `f`, then
`S'` simulates `J` with the same error and exception event. -/
theorem HVZKOffExceptions.map {J : IOP P Stmt} {S' : J.Simulator}
    (h : I.HVZKOffExceptions rel honest S δ bad)
    (f : P.Challenges → I.View → J.View) (hf : ∀ ch tr, J.view ch tr = f ch (I.view ch tr))
    (hS : ∀ x ch, (fun s => f ch (S.sim x ch s)) =ᵈ (S'.sim x ch)) :
    J.HVZKOffExceptions rel honest S' δ bad where
  bad_le := h.bad_le
  simulates x w hw ch hch :=
    (IdentDistrib.of_equiv (Equiv.refl _) fun _ => hf ch _).trans
      (((h.simulates x w hw ch hch).comp (f ch)).trans (hS x ch))

/-- A larger error bounds the same exception event. -/
theorem HVZKOffExceptions.mono {δ' : ℝ≥0} (h : I.HVZKOffExceptions rel honest S δ bad)
    (hδ : δ ≤ δ') :
    I.HVZKOffExceptions rel honest S δ' bad where
  bad_le x w hw := (h.bad_le x w hw).trans (by exact_mod_cast hδ)
  simulates := h.simulates

/-- **The verifier's view with its challenges as a pair**: the challenges and the seen entries. -/
def viewEquiv (I : IOP P Stmt) : TranscriptView I.msg ≃ P.Challenges × I.View where
  toFun v := (v.challenges, v.entries)
  invFun c := ⟨c.1, c.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- **The honest verifier's view** on `x` with the witness `w` (CY24 Definition 23.1.7, p. 260,
for a public-coin IOP): uniform challenges `ch` together with what the verifier sees under `ch`
of the run of `honest w ρ` at uniform prover coins `ρ`. The prover's coins are not part of the
view. -/
noncomputable def honestView (I : IOP P Stmt) (honest : Wit → R → Prover P Stmt) (x : Stmt)
    (w : Wit) : PMF (TranscriptView I.msg) :=
  (PMF.uniformOfFintype P.Challenges).bind fun ch =>
    (PMF.uniformOfFintype R).map fun ρ => ⟨ch, I.view ch ((honest w ρ).run x ch)⟩

/-- **An honest-verifier simulator in the form of CY24 Definition 23.1.8** (p. 260): from the
statement and its own uniform coins, a view of `I` together with challenges (`TranscriptView`),
drawn jointly. It reads no witness and receives no challenges. What it must achieve is `IOP.HVZK`.
As for `IOP.Simulator`, every value of this type is a named definition whose docstring has a
"Running time" paragraph (`scripts/CostLint.lean`). -/
structure JointSimulator (I : IOP P Stmt) where
  /-- The simulator's coins. -/
  Coins : Type
  [fintype : Fintype Coins]
  [nonempty : Nonempty Coins]
  /-- The simulated challenges and view on the statement and the coins. -/
  sim : Stmt → Coins → TranscriptView I.msg

attribute [instance] JointSimulator.fintype JointSimulator.nonempty

/-- **The law of the simulated view** on `x`: the simulator at uniform coins. -/
noncomputable def JointSimulator.law (S : I.JointSimulator) (x : Stmt) :
    PMF (TranscriptView I.msg) :=
  (PMF.uniformOfFintype S.Coins).map (S.sim x)

/-- **Honest-verifier zero knowledge** of `honest` on `rel` at the simulator `S` with error `ε`
(CY24 Definition 23.1.8, p. 260: for every instance-witness pair in the relation, the verifier's
view in the honest interaction and the simulator's output on the instance are `ε`-close in
statistical distance): for every pair `(x, w)` in `rel`, the honest
verifier's view `honestView` (uniform challenges and what the verifier sees of the honest
prover's messages under them) and the law of the simulator's output `S.law x` (challenges and a
view, drawn jointly) are at total variation distance at most `ε`. -/
def HVZK (I : IOP P Stmt) (rel : Set (Stmt × Wit)) (honest : Wit → R → Prover P Stmt)
    (S : I.JointSimulator) (ε : ℝ≥0) : Prop :=
  ∀ x w, (x, w) ∈ rel → PMF.tvDist (I.honestView honest x w) (S.law x) ≤ ε

/-- The honest view read as a pair: a uniform challenge vector, then the law of what the verifier
sees under it. -/
theorem map_viewEquiv_honestView (x : Stmt) (w : Wit) :
    (I.honestView honest x w).map I.viewEquiv =
      (PMF.uniformOfFintype P.Challenges).bind fun ch =>
        ((PMF.uniformOfFintype R).map fun ρ => I.view ch ((honest w ρ).run x ch)).map
          (Prod.mk ch) := by
  simp only [honestView, PMF.map_bind, PMF.map_comp]
  rfl

/-- **The honest views of two witnesses are at the average distance of what the verifier sees**:
both views have uniform challenges, so their distance is the average over the challenges of the
distance between the two laws of what the verifier sees
(`PMF.tvDist_uniformOfFintype_bind_map_prodMk`). -/
theorem tvDist_honestView (x : Stmt) (w w' : Wit) :
    PMF.tvDist (I.honestView honest x w) (I.honestView honest x w') =
      𝔼 ch : P.Challenges, PMF.tvDist
        ((PMF.uniformOfFintype R).map fun ρ => I.view ch ((honest w ρ).run x ch))
        ((PMF.uniformOfFintype R).map fun ρ => I.view ch ((honest w' ρ).run x ch)) := by
  rw [← PMF.tvDist_map_equiv I.viewEquiv, map_viewEquiv_honestView, map_viewEquiv_honestView,
    PMF.tvDist_uniformOfFintype_bind_map_prodMk]

/-- **Two witnesses of one statement have close views** under honest-verifier zero knowledge at
error `ε`: the two honest views are within `ε` of the same simulated law, so their distance, the
average over uniform challenges of the distance between the two laws of what the verifier sees
(`tvDist_honestView`), is at most `2ε`. -/
theorem HVZK.expect_tvDist_le {S : I.JointSimulator} {ε : ℝ≥0}
    (h : I.HVZK rel honest S ε) {x : Stmt} {w w' : Wit} (hw : (x, w) ∈ rel)
    (hw' : (x, w') ∈ rel) :
    𝔼 ch : P.Challenges, PMF.tvDist
        ((PMF.uniformOfFintype R).map fun ρ => I.view ch ((honest w ρ).run x ch))
        ((PMF.uniformOfFintype R).map fun ρ => I.view ch ((honest w' ρ).run x ch)) ≤ 2 * ε := by
  rw [← tvDist_honestView]
  calc PMF.tvDist (I.honestView honest x w) (I.honestView honest x w')
      ≤ PMF.tvDist (I.honestView honest x w) (S.law x) +
          PMF.tvDist (S.law x) (I.honestView honest x w') := PMF.tvDist_triangle _ _ _
    _ ≤ ε + ε := add_le_add (h x w hw) ((PMF.tvDist_comm _ _).trans_le (h x w' hw'))
    _ = 2 * ε := (two_mul _).symm

/-- **A simulator receiving the challenges, as a joint simulator**: it draws uniform challenges
and runs `S` at them.

Running time: drawing one challenge vector plus the running time of `S` (its own Running time
paragraph). This running time is argued here, not proved in Lean. -/
def Simulator.joint (S : I.Simulator) : I.JointSimulator where
  Coins := P.Challenges × S.Coins
  sim x c := ⟨c.1, S.sim x c.1 c.2⟩

/-- The law of `S.joint` read as a pair: a uniform challenge vector, then the law of `S` at it. -/
theorem map_viewEquiv_joint_law (S : I.Simulator) (x : Stmt) :
    (S.joint.law x).map I.viewEquiv =
      (PMF.uniformOfFintype P.Challenges).bind fun ch =>
        ((PMF.uniformOfFintype S.Coins).map (S.sim x ch)).map (Prod.mk ch) := by
  change ((PMF.uniformOfFintype (P.Challenges × S.Coins)).map fun c =>
    (⟨c.1, S.sim x c.1 c.2⟩ : TranscriptView I.msg)).map I.viewEquiv = _
  simp only [PMF.uniformOfFintype_prod_eq_bind, PMF.map_bind, PMF.map_comp]
  rfl

/-- **HVZK at a simulator that receives the challenges, as an average over the challenges**: the
distance between the honest view and the law of `S.joint` is the average over uniform challenges
of the distance between the laws of what the verifier sees
(`PMF.tvDist_uniformOfFintype_bind_map_prodMk`). -/
theorem tvDist_honestView_joint (S : I.Simulator) (x : Stmt) (w : Wit) :
    PMF.tvDist (I.honestView honest x w) (S.joint.law x) =
      𝔼 ch : P.Challenges, PMF.tvDist
        ((PMF.uniformOfFintype R).map fun ρ => I.view ch ((honest w ρ).run x ch))
        ((PMF.uniformOfFintype S.Coins).map (S.sim x ch)) := by
  rw [← PMF.tvDist_map_equiv I.viewEquiv, map_viewEquiv_honestView, map_viewEquiv_joint_law,
    PMF.tvDist_uniformOfFintype_bind_map_prodMk]

/-- **The exception form gives honest-verifier zero knowledge** (CY24 Definition 23.1.8) at the
same error, at the simulator that draws uniform challenges first: outside the exception event the
two laws of what the verifier sees are equal, so the average distance over the challenges
(`tvDist_honestView_joint`) is at most the probability of the event, at most `δ`. -/
theorem HVZKOffExceptions.hvzk (h : I.HVZKOffExceptions rel honest S δ bad) :
    I.HVZK rel honest S.joint δ := by
  classical
  intro x w hw
  rw [tvDist_honestView_joint]
  calc 𝔼 ch : P.Challenges, PMF.tvDist
        ((PMF.uniformOfFintype R).map fun ρ => I.view ch ((honest w ρ).run x ch))
        ((PMF.uniformOfFintype S.Coins).map (S.sim x ch))
      ≤ 𝔼 ch : P.Challenges, (if bad x w ch then (1 : ℝ) else 0) :=
        Finset.expect_le_expect fun ch _ => by
          split_ifs with hb
          · exact PMF.tvDist_le_one _ _
          · have hs := h.simulates x w hw ch hb
            simp only [IdentDistrib] at hs
            rw [hs, PMF.tvDist_self]
    _ = (Pr[ch ← P.Challenges : bad x w ch]).toReal := (toReal_probUniform _).symm
    _ ≤ δ := ENNReal.toReal_le_of_le_ofReal δ.2
        ((h.bad_le x w hw).trans_eq ENNReal.ofReal_coe_nnreal.symm)

end IOP

/-- **A simulator of a protocol's transcript**: coins drawn uniformly from a finite type, and the
transcript simulated from a public input in `Pub` and the challenges only. It is the data of the
honest-verifier simulators that output a transcript (masked row reductions, application phases).
The honest provers it simulates are separate structures that refer to it and state that their
transcripts have its law. -/
structure TranscriptSim (Pub : Type) (P : ProtocolSpec n) where
  /-- The simulator's coins. -/
  SimCoins : Type
  [simFintype : Fintype SimCoins]
  [simNonempty : Nonempty SimCoins]
  /-- The simulated transcript, on the public input and the challenges only. -/
  sim : Pub → P.Challenges → SimCoins → P.Transcript (Fin.last n)

attribute [instance] TranscriptSim.simFintype TranscriptSim.simNonempty

end GordieHowe.IOP
