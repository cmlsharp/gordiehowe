-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.RingSwitching.TreeDomain
public import GordieHowe.ProofSystem.FieldProof.Fork
public import GordieHowe.ProofSystem.FieldProof.ClaimFix

@[expose] public section

/-!
# A domain over a packing tree, forked

The series–parallel form of a tree domain (`GordieHowe.RingSwitching.TreeFieldProof`, `lib/gordiehowe/transcript_fork.h`): the masked
reductions of its batches and of its GKR run as branches (`TreeFork.branch`), each on the domain's public
input; the join part is a tree domain (`TreeFork.join`) on the public input together with the
branches' full transcripts, whose masked reduction holds the branches' claims and rows at those
transcripts (in the instances `MaskedReduction.fixAt` of the domain's masked reduction) with the domain's fixed
rows. Its packing stages and its Ligero proof are the domain's.

* `TreeFork`: the branches and the join domain.
* `TreeFork.Sound`: each branch's soundness for its relation `sat b` at the join's logical
  assignment, the join's masked reduction sound for "every branch's output and the fixed rows", and the
  readout with its soundness on cells whose prefix lies in `S0`.
* `TreeFork.Sound.toShape` (`TreeFork.shapeOf`): the forked circuit proof (`GordieHowe.FieldProof.BranchShape`): the join's
  commit phase (Ligero with the prefix-row test, confined), the branches, the join's proof phase
  (stages, then Ligero) and its verdict at the public input with the branches' transcripts.
* `TreeFork.Sound.toFork`: its forked soundness (`GordieHowe.FieldProof.BranchShape.Sound`): each branch's reduction on
  the extracted cells, disjoined with a bad commit phase (`ClaimReduction.orConst`); the join's
  claim-proving phase (the tree domain's, `GordieHowe.FieldProof.Sound.toShape`); the fixed rows on the
  extracted cells.
-/

namespace GordieHowe

namespace FieldProof

open IOP IOP.ProtocolSpec

variable {Pub Wit In : Type} {holds : Pub → Wit → Prop} {C : FieldProof Pub Wit holds}
  {dom : Pub → In → Prop} {SC : C.Sim}

/-- **Zero knowledge of a circuit proof, with the proof-phase transcript**: on the domain, the
oracle message's queried leaves, the commit rounds and the whole proof-phase transcript of the
honest prover have the law of the masked-row-reduction simulator's transcript joined with the commit-and-prove
simulator's view (the form of `hvzk` before the view is read off). -/
theorem hvzk_transcript (Hc : C.Honest SC In dom) {p : Pub} {x : In} (hx : dom p x)
    (chc : C.cp.commitRounds.Challenges) (ch : C.spec.Challenges) :
    (fun ρ : Hc.Coins => (C.cp.comView.see ch.right (Hc.commit x ρ), Hc.rounds x ρ chc,
      (Hc.prove p x ρ (Hc.rounds x ρ chc)).transcript ch)) =ᵈ
    fun s : SC.SimCoins => ((SC.cp.sim ⟨p, SC.ip.sim p ch.left s.ip⟩ chc ch.right s.cp).leaves,
      (SC.cp.sim ⟨p, SC.ip.sim p ch.left s.ip⟩ chc ch.right s.cp).rounds,
      Transcript.join (SC.ip.sim p ch.left s.ip)
        (SC.cp.sim ⟨p, SC.ip.sim p ch.left s.ip⟩ chc ch.right s.cp).transcript) := by
  have key := (IdentDistrib.dependent
    (f₁ := fun π => (Hc.ip.prover p x π).transcript ch.left) (g₁ := SC.ip.sim p ch.left)
    (f₂ := fun π r => C.cp.view ch.right (Hc.cp.commit (Hc.cells x π) r)
      ((Hc.cp.commitRounds (Hc.cells x π) r).transcript chc)
      ((Hc.cp.prove ⟨p, (Hc.ip.prover p x π).transcript ch.left⟩ (Hc.cells x π) r
        ((Hc.cp.commitRounds (Hc.cells x π) r).transcript chc)).transcript ch.right))
    (g₂ := fun v => SC.cp.sim ⟨p, v⟩ chc ch.right)
    (Hc.ip.identDistrib p x hx ch.left) fun π =>
      Hc.cp.hides ⟨p, (Hc.ip.prover p x π).transcript ch.left⟩ _
        ⟨Hc.admissible p x π hx, Hc.ip.complete p x hx π _ (Hc.commits p x π hx) ch.left⟩
        chc ch.right).comp
    fun v => (v.2.leaves, v.2.rounds, Transcript.join v.1 v.2.transcript)
  exact IdentDistrib.trans (IdentDistrib.of_equiv Hc.coinsEquiv fun ρ => rfl)
    (key.trans (IdentDistrib.of_equiv SC.simCoinsEquiv.symm fun _ => rfl))

end FieldProof

end GordieHowe

namespace GordieHowe

open IOP IOP.ProtocolSpec PackingStage RelativePacking
open scoped NNReal

/-- **A tree domain, forked** (module docstring): `nb ≥ 1` branch masked reductions on the domain's public
input and the join domain on the public input with the branches' full transcripts. -/
structure TreeFork (K : Type) [Field K] [Fintype K] [DecidableEq K] (p : ℕ) [ExpChar K p]
    (ι : Type) [Fintype ι] (V Pub : Type) (nc : ℕ) where
  /-- The number of branches. -/
  nb : ℕ
  /-- There is a branch. -/
  nb_pos : 0 < nb
  /-- The number of claims each branch leaves. -/
  ncb : Fin nb → ℕ
  /-- The branches' masked reductions. -/
  branch : (b : Fin nb) → FieldProof.MaskedReduction K ι Pub (ι → K) id V (ncb b)
  /-- The join domain, on the public input with the branches' full transcripts. -/
  join : RingSwitching.TreeFieldProof K p ι V (Pub × ((b : Fin nb) → (branch b).spec.Transcript (Fin.last (branch b).n)))
    nc

namespace TreeFork

variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {p : ℕ} [ExpChar K p] {ι : Type}
  [Fintype ι] [DecidableEq ι] {V Pub Wit : Type} {nc : ℕ} (T : TreeFork K p ι V Pub nc)

/-- The public input of the join: the domain's public input and the branches' full transcripts. -/
abbrev JoinPub : Type := Pub × ((b : Fin T.nb) → (T.branch b).spec.Transcript (Fin.last (T.branch b).n))

/-- The logical assignment of the join's coordinates read from the cells. -/
abbrev view : (ι → K) → V → K := T.join.path.level.view

/-- **The join's relation on the cells**: every branch's output at its transcript and the fixed
rows `fixed`. -/
def JoinSat (fixed : Pub → (ι → K) → Prop) (p' : T.JoinPub) (x : ι → K) : Prop :=
  (∀ b, (T.branch b).OutHolds T.view p'.1 (p'.2 b) x) ∧ fixed p'.1 x

/-- **The join's relation** at the fixed rows `fixed`, as a tree domain's: the join's relation on
the cells with the prefix in `S0`, the cells read as themselves. -/
def joinRelOf (fixed : Pub → (ι → K) → Prop) :
    T.join.Relation fun p' x => T.join.cp.PrefixIn x ∧ T.JoinSat fixed p' x where
  sat := T.JoinSat fixed
  readout := id
  readout_sound _ _ hx h := ⟨hx, h⟩

/-- **The forked circuit proof of a forked tree domain** (module docstring) at the fixed rows
`fixed`, with the witness read by `readout`. -/
abbrev shapeOf (fixed : Pub → (ι → K) → Prop) (readout : (ι → K) → Wit) : FieldProof.BranchShape Pub Wit where
  Com := (T.join.proof (T.joinRelOf fixed)).cp.Com
  nc := (T.join.proof (T.joinRelOf fixed)).cp.nc
  commitRounds := (T.join.proof (T.joinRelOf fixed)).cp.commitRounds
  ext O r := readout ((T.join.proof (T.joinRelOf fixed)).cp.extract O r)
  nb := T.nb
  nb_pos := T.nb_pos
  bn b := (T.branch b).n
  branch b := (T.branch b).spec
  jn := (T.join.proof (T.joinRelOf fixed)).n
  join := (T.join.proof (T.joinRelOf fixed)).spec
  V p O r trs tr := (T.join.proof (T.joinRelOf fixed)).verdict (p, trs) O r tr

/-- **How a forked tree domain's verdict reads its oracle message** at the fixed rows `fixed`: the
join's Ligero commitment, at the columns its proof phase queries (`CommitProve.reads`). -/
def oracleOf (fixed : Pub → (ι → K) → Prop) (readout : (ι → K) → Wit) :
    (T.shapeOf fixed readout).Oracle where
  nLeaves := (T.join.proof (T.joinRelOf fixed)).cp.nLeaves
  Leaf := (T.join.proof (T.joinRelOf fixed)).cp.Leaf
  leaf := (T.join.proof (T.joinRelOf fixed)).cp.leaf
  leaf_injective := (T.join.proof (T.joinRelOf fixed)).cp.leaf_injective
  ofLeaves := (T.join.proof (T.joinRelOf fixed)).cp.ofLeaves
  leaf_ofLeaves := (T.join.proof (T.joinRelOf fixed)).cp.leaf_ofLeaves
  leafDefault := (T.join.proof (T.joinRelOf fixed)).cp.leafDefault
  queries ch := (T.join.proof (T.joinRelOf fixed)).cp.queries ch.right
  reads p O O' r trs ch tr htr hs :=
    (T.join.proof (T.joinRelOf fixed)).cp.reads ⟨(p, trs), tr.left⟩ ch.right O O' r tr.right
      (Transcript.right_challenge htr) hs

/-- **Soundness of a forked tree domain** relative to `holds` (module docstring). -/
structure Sound (holds : Pub → Wit → Prop) where
  /-- Each branch's relation on the cells. -/
  sat : Fin T.nb → Pub → (ι → K) → Prop
  /-- Each branch's round errors. -/
  εb : (b : Fin T.nb) → (T.branch b).spec.ChallengeIdx → ℝ≥0
  /-- Each branch is sound for its relation at the join's logical assignment. -/
  branchSound : ∀ b, (T.branch b).Sound T.view (sat b) (εb b)
  /-- The fixed rows: the claims no branch proves. -/
  fixed : Pub → (ι → K) → Prop
  /-- The join's masked reduction's round errors. -/
  εj : T.join.maskedReduction.spec.ChallengeIdx → ℝ≥0
  /-- The join's masked reduction is sound for every branch's output and the fixed rows. -/
  joinSound : T.join.maskedReduction.Sound T.view (T.JoinSat fixed) εj
  /-- The witness read from the cells. It becomes part of the named extractor, so each instance
  must give a computable, polynomial-time readout. -/
  readout : (ι → K) → Wit
  /-- The branches' relations and the fixed rows give `holds` on the read witness, on cells whose
  prefix lies in `S0`. -/
  readout_sound : ∀ p x, T.join.cp.PrefixIn x → (∀ b, sat b p x) → fixed p x → holds p (readout x)

variable {T} {holds : Pub → Wit → Prop} (S : T.Sound holds)

/-- **The join's relation** as a tree domain's (`joinRelOf` at the fixed rows). -/
abbrev Sound.joinRel :
    T.join.Relation fun p' x => T.join.cp.PrefixIn x ∧ T.JoinSat S.fixed p' x :=
  T.joinRelOf S.fixed

/-- The join's circuit proof. -/
abbrev Sound.joinProof := T.join.proof S.joinRel

/-- The join's circuit proof's soundness. -/
noncomputable abbrev Sound.joinCS : S.joinProof.Sound := T.join.sound S.joinRel S.joinSound

/-- **The forked circuit proof of a forked tree domain** (module docstring), with the witness
read by `S.readout` (`shapeOf`). -/
abbrev Sound.toShape : FieldProof.BranchShape Pub Wit := T.shapeOf S.fixed S.readout

/-- **The forked soundness of a forked tree domain** (module docstring). -/
noncomputable def Sound.toFork : S.toShape.Sound holds where
  εc := S.joinCS.cpεc
  commit := S.joinCS.cpSound.commitState
  εb := S.εb
  red b := ((S.branchSound b).reduction.comap fun s : S.toShape.Stmt =>
      (⟨s.pub, S.joinProof.cp.extract s.com s.rounds⟩ : FieldProof.MaskedRowReduction.Instance Pub (ι → K))).orConst
    fun s => S.joinCS.commitBad s.com s.rounds
  εj := S.joinCS.error
  proof := S.joinCS.toShape.proof.comap fun s =>
    ⟨(s.stmt.pub, s.trs), s.stmt.com, s.stmt.rounds⟩
  V_eq _ _ := rfl
  fixed s := S.joinCS.commitBad s.com s.rounds ∨ S.fixed s.pub (S.joinProof.cp.extract s.com s.rounds)
  join_claim s h := by
    rcases h with hb | ⟨-, hout, hfix⟩
    · exact ⟨fun _ => .inl hb, .inl hb⟩
    · exact ⟨fun b => .inr (((S.branchSound b).claimOut_iff _ _ _).mpr (hout b)), .inr hfix⟩
  claim_imp s hb hf := by
    by_cases hbad : S.joinCS.commitBad s.com s.rounds
    · exact .inl hbad
    · refine .inr (S.readout_sound s.pub _ (T.join.cp.in_extract_confined _ s.com s.rounds)
        (fun b => ((S.branchSound b).claim_iff _ _).mp ((hb b).resolve_left hbad))
        (hf.resolve_left hbad))

/-- **How a forked tree domain's verdict reads its oracle message** (`oracleOf`). -/
abbrev Sound.oracle : S.toShape.Oracle := T.oracleOf S.fixed S.readout

/-! ### The honest prover -/

variable (T) in
/-- **The honest input of the join**: the domain's honest input and every branch's pads. -/
abbrev JoinIn {In : Type} {dom : Pub → In → Prop} {SB : ∀ b, (T.branch b).Sim}
    (Hb : ∀ b, (T.branch b).Honest T.view In dom (SB b)) :
    Type :=
  In × ((b : Fin T.nb) → (Hb b).Pads)

variable (T) in
/-- **The join's honest domain**: the domain's honest domain, and the branches' transcripts are the
honest branches' at the pads, at some challenges. -/
def JoinDom {In : Type} {dom : Pub → In → Prop} {SB : ∀ b, (T.branch b).Sim}
    (Hb : ∀ b, (T.branch b).Honest T.view In dom (SB b))
    (p' : T.JoinPub) (x : T.JoinIn Hb) : Prop :=
  dom p'.1 x.1 ∧ ∃ chs : (b : Fin T.nb) → (T.branch b).spec.Challenges,
    ∀ b, p'.2 b = ((Hb b).prover p'.1 x.1 (x.2 b)).transcript (chs b)

variable (T) in
/-- **The simulator data of a forked tree domain**: every branch's masked-reduction simulator and the
join domain's simulator data. -/
structure SimData where
  /-- Each branch's masked-reduction simulator. -/
  branch : ∀ b, (T.branch b).Sim
  /-- The join domain's simulator data. -/
  join : T.join.SimData

/-- **The honest data of a forked tree domain** on honest inputs `In` in the domain `dom`, simulated
by `SD`: every branch's honest masked reduction, and the join domain's honest data on the honest
input with the branches' pads, on the honest branches' transcripts (`JoinDom`). -/
structure Sound.HonestData (SD : T.SimData) (In : Type) (dom : Pub → In → Prop) where
  /-- Each branch's honest masked reduction. -/
  branch : ∀ b, (T.branch b).Honest T.view In dom (SD.branch b)
  /-- The join domain's honest data. -/
  join : T.join.HonestData S.joinRel SD.join (T.JoinIn branch) (T.JoinDom branch)

variable {S} {SD : T.SimData} {In : Type} {dom : Pub → In → Prop} (Hd : S.HonestData SD In dom)

/-- The join's honest circuit proof. -/
noncomputable abbrev Sound.HonestData.joinHonest :
    S.joinProof.Honest (T.join.sim S.joinRel SD.join) (T.JoinIn Hd.branch) (T.JoinDom Hd.branch) :=
  T.join.honest Hd.join

/-- **The honest forked prover of a forked tree domain**: every branch's honest masked reduction on its own
pads, and the join domain's honest prover on the public input with the branches' transcripts, its
committed cells holding the honest input and all pads. -/
noncomputable def Sound.HonestData.toShape : S.toShape.Honest In where
  Coins := ((b : Fin T.nb) → (Hd.branch b).Pads) × Hd.joinHonest.Coins
  commit x ρ := Hd.joinHonest.commit (x, ρ.1) ρ.2
  commitRounds x ρ := Hd.joinHonest.commitRounds (x, ρ.1) ρ.2
  branch b p x ρ _ := (Hd.branch b).prover p x (ρ.1 b)
  join p x ρ r trs := Hd.joinHonest.prove (p, trs) (x, ρ.1) ρ.2 r

/-- **Completeness of a forked tree domain**: on the domain, the verdict accepts the honest forked
proof at every challenge (`FieldProof.completeness` of the join on the honest branches'
transcripts). -/
theorem Sound.HonestData.accepts : Hd.toShape.Accepts dom := fun p x hx ρ chc chb chj =>
  FieldProof.completeness Hd.joinHonest (p := (p, fun b => ((Hd.branch b).prover p x (ρ.1 b)).transcript (chb b)))
    (x := (x, ρ.1)) ⟨hx, chb, fun _ => rfl⟩ ρ.2 chc chj

variable (T) in
/-- **The simulator of a forked tree domain** at the fixed rows `fixed`, the readout `readout` and
the simulator data `SD`: every branch's masked-reduction simulator, then the join's
masked-row-reduction simulator and Ligero's on the public input with the simulated branches'
transcripts (`TreeFieldProof.sim` at `joinRelOf fixed`). It reads no soundness data.

Running time: one run of each branch's simulator, of the join's masked-row-reduction simulator and of Ligero's
simulator (their docstrings), and the assembly, linear in the transcript lengths.
This running time is argued here, not proved in Lean. -/
def simulatorOf (fixed : Pub → (ι → K) → Prop) (readout : (ι → K) → Wit)
    (SD : T.SimData) : (T.shapeOf fixed readout).Simulator (T.oracleOf fixed readout) where
  Coins := ((b : Fin T.nb) → (SD.branch b).SimCoins) × (T.join.sim (T.joinRelOf fixed) SD.join).SimCoins
  sim p chc chb chj s :=
    let trs : T.JoinPub := (p, fun b => (SD.branch b).sim p (chb b) (s.1 b))
    let trIP := (T.join.sim (T.joinRelOf fixed) SD.join).ip.sim trs chj.left s.2.ip
    let v := (T.join.sim (T.joinRelOf fixed) SD.join).cp.sim ⟨trs, trIP⟩ chc chj.right s.2.cp
    ⟨v.leaves, v.rounds, trs.2, Transcript.join trIP v.transcript⟩

/-- **Zero knowledge of a forked tree domain**: the simulator is perfect on the domain: the
branches' masked-reduction simulations (`MaskedReduction.Honest.identDistrib`, independent pads), then, at each
value of the branches' pads, the join's simulation on the branches' transcripts
(`FieldProof.hvzk_transcript`), composed by `IdentDistrib.dependent`. -/
theorem Sound.HonestData.perfect : (T.simulatorOf S.fixed S.readout SD).Perfect Hd.toShape dom := by
  intro p x hx chc chb chj
  have key := (IdentDistrib.dependent
    (f₁ := fun πs : (b : Fin T.nb) → (Hd.branch b).Pads =>
      fun b => ((Hd.branch b).prover p x (πs b)).transcript (chb b))
    (g₁ := fun ss : (b : Fin T.nb) → (SD.branch b).SimCoins => fun b => (SD.branch b).sim p (chb b) (ss b))
    (f₂ := fun πs (cc : Hd.joinHonest.Coins) =>
      (S.joinProof.cp.comView.see chj.right (Hd.joinHonest.commit (x, πs) cc),
        Hd.joinHonest.rounds (x, πs) cc chc,
        (Hd.joinHonest.prove (p, fun b => ((Hd.branch b).prover p x (πs b)).transcript (chb b))
          (x, πs) cc (Hd.joinHonest.rounds (x, πs) cc chc)).transcript chj))
    (g₂ := fun trs (s : (T.join.sim S.joinRel SD.join).SimCoins) =>
      (((T.join.sim S.joinRel SD.join).cp.sim ⟨(p, trs), (T.join.sim S.joinRel SD.join).ip.sim (p, trs) chj.left s.ip⟩ chc chj.right
          s.cp).leaves,
        ((T.join.sim S.joinRel SD.join).cp.sim ⟨(p, trs), (T.join.sim S.joinRel SD.join).ip.sim (p, trs) chj.left s.ip⟩ chc chj.right
          s.cp).rounds,
        Transcript.join ((T.join.sim S.joinRel SD.join).ip.sim (p, trs) chj.left s.ip)
          ((T.join.sim S.joinRel SD.join).cp.sim ⟨(p, trs), (T.join.sim S.joinRel SD.join).ip.sim (p, trs) chj.left s.ip⟩ chc chj.right
            s.cp).transcript))
    (IdentDistrib.pi fun b => (Hd.branch b).identDistrib p x (chb b)) fun πs =>
      FieldProof.hvzk_transcript Hd.joinHonest (p := (p, _)) (x := (x, πs))
        ⟨hx, chb, fun _ => rfl⟩ chc chj).comp
    fun v => (⟨v.2.1, v.2.2.1, v.1, v.2.2.2⟩ : S.oracle.View)
  exact IdentDistrib.trans (IdentDistrib.of_equiv (Equiv.refl _) fun _ => rfl)
    (key.trans (IdentDistrib.of_equiv (Equiv.refl _) fun _ => rfl))

end TreeFork

end GordieHowe
