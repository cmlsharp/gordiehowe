-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.IOP.SPIOP
public import GordieHowe.SPBCS.Bytes
public import GordieHowe.SPBCS.Basic
public import GordieHowe.SPBCS.FullPast.Extract
public import GordieHowe.SPBCS.FullPast.Online
public import GordieHowe.SPBCS.FullPast.ZeroKnowledge
public import GordieHowe.SPBCS.Merkle.Multiproof

@[expose] public section

/-!
# The setting of the spBCS compiler

The data that fixes the compiled spBCS argument (`GordieHowe.SPBCS`, `GordieHowe/SPBCS/Basic.lean`)
of a composite IOP with oracles (`GordieHowe.IOP.SPIOP`, `GordieHowe/Model/IOP/SPIOP.lean`) over a series–parallel term
`t` with merges `Mg`.

* `Setting I Mg kMin`: digests of `k ≥ kMin` bytes, Merkle salts of `kN` bytes, Fiat–Shamir
  salts of `kS` bytes, inputs of `L` bytes, XOF answers of `k + e` bytes, the label and statement
  codec of the writes before round 0, a site layout of the merges (`SiteLayout`), the write codec
  of each prover message of each component, the leaf codecs, the samplers, and the length budgets
  of both chain-input encodings (`fits` for the chain inputs with merges, `fitsC` for full causal
  pasts).
* `GordieHowe.SPBCS.Setting.model`: the spBCS compiler data (`GordieHowe.SPBCS`): each component's chain data
  (`compModel`), the byte encoding of full causal pasts (`CausalEncoding.bytes`, read only by the
  extractor) and of the chain inputs with merges (`MergeBytes.bytes` at the layout).
* The query phase `queries` (decided by `I.V` through query locality), the honest encoding
  `encoder`, the view laws `viewEncoder` (the composite verifier's view `GordieHowe.IOP.SPIOP.views`), and the
  format bounds `formatBounds` of the query phases.
-/

namespace GordieHowe.SPBCS

open IOP IOP.ProtocolSpec GordieHowe.QROM IOP.SPTerm
open scoped NNReal ENNReal

variable {ι : Type} {n : ι → ℕ} {P : (j : ι) → ProtocolSpec (n j)}
  [∀ j i, Fintype ((P j).Challenge i)] [∀ j i, DecidableEq ((P j).Challenge i)] {X : Type}
  {t : SPTerm ι}

/-- **The setting of the spBCS compiler** of `I` over the merges `Mg` with digests of at
least `kMin` bytes (module docstring). The label, the statement codec, the site layout, the codecs
and the samplers are instance data (their correspondence to an implementation is the instance's
obligation); `kMin_le_k`, `nTrees_le`, `leaf_fit`, `fits` and `fitsC` are conditions on the
parameters. -/
structure Setting (I : SPIOP P t X) (Mg : Merges t) (kMin : ℕ) where
  /-- The digest length in bytes. -/
  k : ℕ
  /-- The Merkle salt length in bytes. -/
  kN : ℕ
  /-- The Fiat–Shamir salt length in bytes. -/
  kS : ℕ
  /-- The byte length of a chain input. -/
  L : ℕ
  /-- The XOF answer has `k + e` bytes. -/
  e : ℕ
  /-- Digests have at least `kMin` bytes. -/
  kMin_le_k : kMin ≤ k
  /-- The label write, the first write of every chain input. -/
  label : List Byte
  /-- The codec of the statement writes. -/
  stmt : Codec X
  /-- The order and the codes of the sites in a chain input. -/
  layout : SiteLayout Mg
  /-- The write of each prover message of each component. -/
  write : ∀ j i, WriteCodec (CompWrite I k j i)
  /-- The byte codec of each tree's leaves. -/
  leaf : ∀ j i t, Codec ((I.comp j).Leaf i t)
  /-- A serialized leaf fits in a leaf input. -/
  leaf_fit : ∀ j i t c, ((leaf j i t).ser c).length ≤ L
  /-- The largest number of roots of a write (at least one). -/
  nd : ℕ
  /-- There is room for one root. -/
  one_le_nd : 1 ≤ nd
  /-- A write carries at most `nd` roots. -/
  nTrees_le : ∀ j i, (I.comp j).nTrees i ≤ nd
  /-- The bound on the bytes of one write. -/
  B : ℕ
  /-- Every write has at most `B` bytes. -/
  write_B_le : ∀ j i, (write j i).B ≤ B
  /-- Every chain input with merges fits in `L` bytes. -/
  fits : ∀ x (o : Mg.Obs),
    ((TranscriptEncoding.saltedCodec (kS := kS) label stmt).ser x).length +
      (MergeBytes.label layout o).length + (∑ q : t.Leaf, n q.label) * max B (9 + k) +
      Mg.nJ * k ≤ L
  /-- Every chain input of the full causal past fits in `L` bytes. -/
  fitsC : ∀ x (p : t.Leaf),
    ((TranscriptEncoding.saltedCodec (kS := kS) label stmt).ser x).length + p.pathLabel.length +
      (∑ q : t.Leaf, n q.label) * max B (9 + k) ≤ L
  /-- The challenge sampler of each challenge round of each component. -/
  sampler : ∀ j i, Sampler k e ((P j).Challenge i)

namespace Setting

variable {I : SPIOP P t X} {Mg : Merges t} {kMin : ℕ} (F : Setting I Mg kMin)

/-- **Message `i` of component `j` read from its write and the Merkle views of its trees**: the
non-oracle part of the write, each leaf through its codec (the default leaf where it is missing
or does not parse).

Running time: one parse per leaf of the message, each of at most `L` bytes.
This running time is argued here, not proved in Lean. -/
def msg (j : ι) (i : (P j).MessageIdx) (w : CompWrite I F.k j i)
    (vw : (t : Fin ((I.comp j).nTrees i)) → MerkleView F.k F.kN F.L ((I.comp j).nLeaves i t)) :
    (P j).Type i.1 :=
  ((I.comp j).parts i).symm
    ⟨w.nonOracle, fun t l => (F.leaf j i t).decodeLeaf ((I.comp j).leafDefault i t) ((vw t).leaves l)⟩

/-- **The chain data of component `j`**: its `ComponentModel`, without the chain-input encoding. -/
def compModel (j : ι) : ComponentModel (P j) F.k F.kN F.L F.e where
  MessageWrite := CompWrite I F.k j
  nTrees := (I.comp j).nTrees
  nLeaves := (I.comp j).nLeaves
  rootOf _ w t := w.roots t
  msg := F.msg j
  sampler := F.sampler j

/-- The codec of the writes before round 0: the label, the salt write, the statement writes. -/
abbrev preCodec : Codec (SaltedStatement F.kS X) :=
  TranscriptEncoding.saltedCodec (kS := F.kS) F.label F.stmt

/-- The write codecs as codecs of the components' writes. -/
abbrev writeC (j : ι) (i : (P j).MessageIdx) : WriteCodec ((F.compModel j).MessageWrite i) :=
  F.write j i

/-- A write carries at most `nd` roots. -/
theorem card_roots_le (j : ι) (w : (F.compModel j).W) : ((F.compModel j).roots w).card ≤ F.nd :=
  Finset.card_image_le.trans (by
    rw [Finset.card_univ, Fintype.card_fin]
    exact F.nTrees_le j w.1)

/-- **The encoding of full causal pasts** (`CausalEncoding.bytes`), read only by the extractor. -/
def causalEnc : CausalEncoding F.k F.L t n (SaltedStatement F.kS X) (fun j => (F.compModel j).W)
    (fun j => (F.compModel j).roots) (fun j => chainWF (P j)) :=
  CausalEncoding.bytes F.writeC F.preCodec (fun j => (F.compModel j).roots) F.B F.card_roots_le
    F.one_le_nd F.write_B_le F.fitsC

/-- **The byte encoding of the chain inputs with merges** (`MergeBytes.bytes` at the layout). -/
def mergeEnc : MergeEncoding F.k F.L Mg n (SaltedStatement F.kS X) (fun j => (F.compModel j).W)
    (fun j => (F.compModel j).roots) (fun j => chainWF (P j)) :=
  MergeBytes.bytes F.writeC F.preCodec F.layout (fun j => (F.compModel j).roots) F.B
    F.card_roots_le F.one_le_nd F.write_B_le F.fits

/-- **The digests of an encoded causal past are those of its content.** -/
theorem causalEnc_digestsOf_encode (ss : SaltedStatement F.kS X)
    (ch : CausalChain t F.k fun j => (F.compModel j).W)
    (hwf : ch.WF n fun j => chainWF (P j)) :
    F.causalEnc.digestsOf (F.causalEnc.encode ss ch) ⊆ ch.digests fun j => (F.compModel j).roots := by
  intro u hu
  have hd := F.causalEnc.decode_encode ss ch hwf
  unfold causalEnc at hu hd
  simp only [CausalEncoding.bytes] at hu hd
  rw [hd] at hu
  simp only at hu
  by_cases hs : ch.size ≤ ∑ q : t.Leaf, n q.label
  · rwa [if_pos hs] at hu
  · rw [if_neg hs] at hu
    exact absurd hu (Finset.notMem_empty u)

/-- **The spBCS compiler data of the setting** (module docstring), with the trees opened by
compressed multiproofs (`Multiproof.opening`), as the C++ does. -/
def model : SPBCS Mg P X F.k F.kN F.kS F.L F.e where
  comp := F.compModel
  enc := F.causalEnc
  opening := Multiproof.opening
  senc := F.mergeEnc
  enc_digests_subset := F.causalEnc_digestsOf_encode

/-- **The quantum adversaries against the argument of the setting**: the `t`-query adversaries of
`def:adversary` without proof queries with output in `O` (`GordieHowe.NARG.QROM.Adversary`) at the
setting's oracle `{0,1}^m → Out k e`. -/
abbrev QROMAdversary (O : Type) (t : ℕ) : Type 1 :=
  NARG.QROM.Adversary (queryBits F.k F.kN F.kS F.L) F.k F.e O t

/-- **The classical adversaries against the argument of the setting**: the classical `t`-query
adversaries without proof queries with output in `O` (`GordieHowe.NARG.ROM.Adversary`) at the
setting's oracle `Query → Out k e`. -/
abbrev ROMAdversary (O : Type) (t : ℕ) : Type 1 :=
  NARG.ROM.Adversary (Query F.k F.kN F.kS F.L) (Out F.k F.e) O t

/-- **The digests of one chain input with merges**: `nd` per item. -/
theorem digestsPerInput_eq : F.model.senc.digestsPerInput = (∑ q : t.Leaf, n q.label) * F.nd :=
  rfl

/-- A write has finitely many values (its codec is injective into bounded byte strings,
`WriteCodec.finite`). -/
noncomputable instance fintypeMessageWrite (j : ι) (i : (P j).MessageIdx) :
    Fintype ((F.model.comp j).MessageWrite i) :=
  @Fintype.ofFinite (CompWrite I F.k j i) (F.write j i).finite

/-! ### The query phase -/

/-- A query position of `I` as a position of the compiler data. -/
def toPos (q : I.Pos) : F.model.Pos := ⟨q.leaf, q.pos⟩

theorem toPos_injective : Function.Injective F.toPos := by
  rintro ⟨p, q⟩ ⟨p', q'⟩ h
  cases h
  rfl

/-- The Merkle views of every tree holding the leaves `lf`. -/
def viewsOf (lf : F.model.Pos → Option (MerkleLeaf F.kN F.L)) : F.model.Views :=
  fun p i t => ⟨fun _ => none, fun l => lf ⟨p, ⟨i, t, l⟩⟩⟩

/-- **The composite transcript read from the chains**, the challenges `ch` and the leaves `lf`:
each prover message of each leaf from the chain's write of its round and the views holding `lf`,
each challenge from `ch`; `none` if a chain lacks the write of a prover round. -/
def trOf (chs : (p : t.Leaf) → F.model.Items p) (ch : Chs P t)
    (lf : F.model.Pos → Option (MerkleLeaf F.kN F.L)) : Option (FullTr P t) :=
  if h : ∀ (p : t.Leaf) (i : (P p.label).MessageIdx),
      ((chs p)[i.1.1]?.bind ((F.model.comp p.label).writeAt i)).isSome then
    some fun p r =>
      if hd : (P p.label).dir r = .P_to_V then
        F.msg p.label ⟨r, hd⟩ (((chs p)[r.1]?.bind ((F.model.comp p.label).writeAt ⟨r, hd⟩)).get
          (h p ⟨r, hd⟩)) (F.viewsOf lf p ⟨r, hd⟩)
      else ch ⟨p, ⟨r, by
        cases h' : (P p.label).dir r with
        | P_to_V => exact absurd h' hd
        | V_to_P => rfl⟩⟩
  else none

variable {F}

theorem challenge_of_trOf {chs : (p : t.Leaf) → F.model.Items p} {ch : Chs P t}
    {lf : F.model.Pos → Option (MerkleLeaf F.kN F.L)} {f : FullTr P t}
    (h1 : F.trOf chs ch lf = some f) (c : ChIdx P t) : f.challenges c = ch c := by
  unfold trOf at h1
  split_ifs at h1 with hall
  obtain rfl := Option.some_inj.1 h1
  have hd : ¬ (P c.leaf.label).dir c.idx.1 = .P_to_V := by
    rw [c.idx.2]
    decide
  change (if hd : (P c.leaf.label).dir c.idx.1 = .P_to_V then _ else _) = _
  rw [dif_neg hd]
  rfl

theorem message_of_trOf {chs : (p : t.Leaf) → F.model.Items p} {ch : Chs P t}
    {lf : F.model.Pos → Option (MerkleLeaf F.kN F.L)} {f : FullTr P t}
    (h1 : F.trOf chs ch lf = some f) (p : t.Leaf) (i : (P p.label).MessageIdx) :
    ∃ w : CompWrite I F.k p.label i, (chs p)[i.1.1]? = some (.write ⟨i, w⟩) ∧
      f p i.1 = F.msg p.label i w (F.viewsOf lf p i) := by
  unfold trOf at h1
  split_ifs at h1 with hall
  obtain rfl := Option.some_inj.1 h1
  obtain ⟨w, hw⟩ := Option.isSome_iff_exists.1 (hall p i)
  obtain ⟨it, hit, hw'⟩ := Option.bind_eq_some_iff.1 hw
  refine ⟨w, hit.trans (congrArg some ((F.model.comp p.label).eq_write_of_writeAt hw')), ?_⟩
  change (if hd : (P p.label).dir i.1 = .P_to_V then _ else _) = _
  rw [dif_pos i.2]
  exact congrArg (fun w => F.msg p.label i w (F.viewsOf lf p i)) (Option.eq_some_iff_get_eq.1 hw).2

theorem trOf_isSome {chs : (p : t.Leaf) → F.model.Items p} (ch : Chs P t)
    (lf : F.model.Pos → Option (MerkleLeaf F.kN F.L)) (hall : F.model.WritesAll chs) :
    ∃ f, F.trOf chs ch lf = some f := by
  classical
  have hsome : ∀ (p : t.Leaf) (i : (P p.label).MessageIdx),
      ((chs p)[i.1.1]?.bind ((F.model.comp p.label).writeAt i)).isSome := fun p i => by
    obtain ⟨w, hw⟩ := hall p i
    rw [hw, Option.bind_some, (F.model.comp p.label).writeAt_write]
    rfl
  unfold trOf
  rw [dif_pos hsome]
  exact ⟨_, rfl⟩

variable (F)

/-- **The decision of the query phase** at the statement `x`: `I.V` on the composite transcript
read from the chains, the challenges and the answers at the query positions; `false` if a chain
lacks a write. -/
def verdict (x : X) (chs : (p : t.Leaf) → F.model.Items p) (ch : Chs P t)
    (ans : List (MerkleLeaf F.kN F.L)) : Bool :=
  match F.trOf chs ch (lookupAns ((I.pos ch).map F.toPos) ans) with
  | some f => I.V x f
  | none => false

variable {F}

/-- **The verdict on a transcript of the chains' messages** at views holding the answers at the
query positions is the verdict on the transcript read with the answers alone: query locality
(`SPIOP.reads`). -/
theorem V_eq_of_trOf (x : X) {chs : (p : t.Leaf) → F.model.Items p} {ch : Chs P t}
    {vw : F.model.Views} {f : FullTr P t} {ans : List (MerkleLeaf F.kN F.L)}
    (hmsg : F.model.MessagesFrom chs vw f) (hch : Base.ChallengesAre f ch)
    (hans : F.model.OpenedAs vw ((I.pos ch).map F.toPos) ans) {f₁ : FullTr P t}
    (h1 : F.trOf chs ch (lookupAns ((I.pos ch).map F.toPos) ans) = some f₁) :
    I.V x f = I.V x f₁ := by
  refine I.reads x f f₁ (fun c => (congrFun hch c).trans (challenge_of_trOf h1 c).symm)
    (fun p i => ?_) (fun q hq => ?_)
  · obtain ⟨w, hw, h1i⟩ := message_of_trOf h1 p i
    rw [hmsg p i w hw, h1i]
    change (((I.comp p.label).parts i) (F.msg p.label i w (vw p i))).nonOracle =
      (((I.comp p.label).parts i) (F.msg p.label i w _)).nonOracle
    simp only [msg, Equiv.apply_symm_apply]
  · rw [hch] at hq
    obtain ⟨w, hw, h1i⟩ := message_of_trOf h1 q.leaf q.pos.msg
    rw [hmsg q.leaf q.pos.msg w hw, h1i]
    change (((I.comp q.leaf.label).parts q.pos.msg)
        (F.msg q.leaf.label q.pos.msg w (vw q.leaf q.pos.msg))).leaves q.pos.tree q.pos.leaf =
      (((I.comp q.leaf.label).parts q.pos.msg) (F.msg q.leaf.label q.pos.msg w _)).leaves
        q.pos.tree q.pos.leaf
    simp only [msg, Equiv.apply_symm_apply]
    exact congrArg ((F.leaf q.leaf.label q.pos.msg q.pos.tree).decodeLeaf
        ((I.comp q.leaf.label).leafDefault q.pos.msg q.pos.tree))
      (lookupAns_of_forall₂ hans (F.toPos q) (List.mem_map_of_mem hq)).symm

variable (F)

/-- **The query phase of the spBCS compiler** at the statement `x`: open the query
positions of `I` and decide by `verdict`; its laws follow from query locality (`V_eq_of_trOf`). -/
def queries (x : X) : F.model.IOPQueries I.V x where
  pos _ ch := (I.pos ch).map F.toPos
  verdict := F.verdict x
  pos_nodup _ ch := (I.pos_nodup ch).map F.toPos_injective
  verdict_of_accept chs ch vw f ans hall hmsg hch hans hV := by
    obtain ⟨f₁, h1⟩ := trOf_isSome ch (lookupAns ((I.pos ch).map F.toPos) ans) hall
    unfold verdict
    rw [h1]
    exact (V_eq_of_trOf x hmsg hch hans h1).symm.trans hV
  accept_of_verdict chs ch vw f ans hmsg hch hans hdec := by
    unfold verdict at hdec
    cases h1 : F.trOf chs ch (lookupAns ((I.pos ch).map F.toPos) ans) with
    | none => rw [h1] at hdec; simp at hdec
    | some f₁ =>
      rw [h1] at hdec
      rw [V_eq_of_trOf x hmsg hch hans h1]
      exact hdec

/-- **The format bounds of the query phases** (`Base.FormatBounds`): at most `NQ` query
positions of `I` and at most `N` leaves per tree. -/
theorem formatBounds {NQ N : ℕ} (hpos : ∀ ch, (I.pos ch).length ≤ NQ)
    (hN : ∀ (p : t.Leaf) i τ, (I.comp p.label).nLeaves i τ ≤ N) :
    F.model.FormatBounds F.queries NQ N where
  pos_le _ _ ch := (List.length_map _).trans_le (hpos ch)
  nLeaves_le := hN

/-! ### The honest encoding and the view laws -/

/-- **The honest encoding of component `j`'s messages** (`ComponentModel.Encoder`): the write of
message `i` is its non-oracle part with the given roots, the column bytes of a leaf its
serialization. -/
def encoder (j : ι) : (F.model.comp j).Encoder where
  cols i m t l := Bytes.ofList ((F.leaf j i t).ser ((((I.comp j).parts i) m).leaves t l))
  write i m rts := ⟨(((I.comp j).parts i) m).nonOracle, rts⟩
  rootOf_write _ _ _ _ := rfl
  msg_write i m rts vw hvw := by
    change F.msg j i _ vw = m
    refine ((I.comp j).parts i).injective ?_
    simp only [msg, Equiv.apply_symm_apply]
    refine MessageParts.ext rfl (funext fun t => funext fun l => ?_)
    obtain ⟨ν, hν⟩ := hvw t l
    exact (congrArg ((F.leaf j i t).decodeLeaf ((I.comp j).leafDefault i t)) hν).trans
      (Codec.decodeLeaf_ser (F.leaf_fit j i t) ν _)

/-- The non-oracle part read off an entry of a message's view. -/
def nonOracleOfEntry {p : t.Leaf} {i : (P p.label).MessageIdx} :
    Option (CausalIOPViews.Ans I p i) → Option ((I.comp p.label).NonOracle i)
  | some (.nonOracle a) => some a
  | _ => none

open Classical in
/-- **The writes read off a view**, as functions of the roots: each message's non-oracle part from
its view at the non-oracle index, with the given roots; `none` if some message's view has no
non-oracle part.

Running time: one lookup per prover message of each leaf. This running time is argued here, not
proved in Lean. -/
def writesOfView (o : CausalView I.views) : Option F.model.RootWriteFn :=
  if h : ∀ (p : t.Leaf) (i : (P p.label).MessageIdx),
      (nonOracleOfEntry (o.entries p i .nonOracle)).isSome then
    some fun p i rts => ⟨(nonOracleOfEntry (o.entries p i .nonOracle)).get (h p i), rts⟩
  else none

/-- **The column bytes of a position of `I` read off a view**: the serialization of the leaf seen
at the position, the empty string if none is seen.

Running time: one lookup and one serialization of at most `L` bytes.
This running time is argued here, not proved in Lean. -/
def colOfViewAt (o : CausalView I.views) (q : I.Pos) : Bytes F.L :=
  match o.entries q.leaf q.pos.msg (.leaf q.pos.tree q.pos.leaf) with
  | some (.leaf τ l) =>
    if h : τ = q.pos.tree then Bytes.ofList ((F.leaf q.leaf.label q.pos.msg q.pos.tree).ser (h ▸ l))
    else ⟨0, Fin.elim0⟩
  | _ => ⟨0, Fin.elim0⟩

/-- **The column bytes of a position read off a view** (`colOfViewAt`).

Running time: one lookup and one serialization of at most `L` bytes.
This running time is argued here, not proved in Lean. -/
def colOfView (o : CausalView I.views) (q : F.model.Pos) : Bytes F.L :=
  F.colOfViewAt o ⟨q.leaf, q.pos⟩

/-- **What the compiled proof reveals of a composite transcript**: the composite verifier's view,
from which the writes (`writesOfView`) and the opened columns (`colOfView`) are read off. -/
@[reducible] def reveal : Base.Reveal (M := F.model.toBase) F.encoder F.queries where
  MV := I.views
  writesOf _ _ o := F.writesOfView o
  colOf _ _ o q := F.colOfView o q
  writesOf_obs x ρ f := by
    have hv : ∀ (p : t.Leaf) (i : (P p.label).MessageIdx),
        nonOracleOfEntry ((I.views.view f).entries p i .nonOracle) =
          some (((I.comp p.label).parts i) (f p i.1)).nonOracle := fun p i => by
      change nonOracleOfEntry ((I.views.msg p i).see f.challenges (f p i.1) .nonOracle) = _
      rw [MessageView.see_of_mem (I.views.msg p i) (j := .nonOracle)
        (CausalIOPViews.nonOracle_mem_queries I p i _)]
      rfl
    have hs : ∀ (p : t.Leaf) (i : (P p.label).MessageIdx),
        (nonOracleOfEntry ((I.views.view f).entries p i .nonOracle)).isSome :=
      fun p i => by rw [hv p i]; rfl
    unfold writesOfView
    rw [dif_pos hs]
    congr 1
    funext p i rts
    exact Write.ext (Option.some_injective _ ((Option.some_get _).trans (hv p i))) rfl
  colOf_obs x chs ρ f hf q hq := by
    obtain ⟨q', hq', rfl⟩ := List.mem_map.1 hq
    rw [← hf] at hq'
    change F.colOfViewAt _ q' = _
    unfold colOfViewAt
    rw [show (I.views.view f).entries q'.leaf q'.pos.msg (.leaf q'.pos.tree q'.pos.leaf) =
        some (CausalIOPViews.read I q'.leaf q'.pos.msg (f q'.leaf q'.pos.msg.1)
          (.leaf q'.pos.tree q'.pos.leaf)) from
      MessageView.see_of_mem (I.views.msg q'.leaf q'.pos.msg)
        (CausalIOPViews.leaf_mem_queries I hq') _]
    simp only [CausalIOPViews.read]
    exact dif_pos trivial

/-- **The view laws of the setting** (`Base.ViewEncoder`): `reveal`, and the opened
positions `I.pos` at the challenges on every chain. -/
@[reducible] def viewEncoder : Base.ViewEncoder (M := F.model.toBase) F.encoder F.queries where
  toReveal := F.reveal
  posC _ ch := (I.pos ch).map F.toPos
  pos_eq _ _ _ _ := rfl

end Setting

end GordieHowe.SPBCS
