-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.Library.Select
public import GordieHowe.Language.Library.Sponge
public import GordieHowe.Applications.Falcon512.Frontend.Fields
public import GordieHowe.Applications.Falcon512.Native.System.Application
public import GordieHowe.Applications.Falcon512.Spec.KeyNTT

@[expose] public section

/-!
# GordieHowe frontend: native Falcon, the relation and the extractor

The frontend of the theorem at the realized program for the native Falcon proofs of possession
(`Falcon512.Native.ROMParams` and `Falcon512.Native.QROMParams`, export `c825eb05`), generic in the program `program` and in the fields of
its domains (`falconInterpOf FH FA`, `GordieHowe/Applications/Falcon512/Frontend/Fields.lean`): the program
facts it reads are the fields of `FalconHBase` (decided per program), `FalconHConsts` (the
selection's labels in `FH`, read by the hash's padding) and `FalconSelField` (the selection's field:
`FH`'s data and the labels there). The parts here do not read the Keccak trace's shape or domain
`A`'s layout:

* **The selection** (`selShape`, `firstAccepted_or_badAt`, `selectEvent`): the source program's
  first-`512` selection of the `639` samples below `61445` (`h2p.select.*`), at the selection field
  of `FH` (`GordieHowe.Falcon512.HField.sel`), its event at `h2p.select.delta` of probability `639/2^bits`.
* **The crossing** (`natOfBits_raw_eq`): `mac.equal` makes sample `j` of `select.raw` and of `c_A`
  the same natural.
* **The statement** (`keyOf`, `stmtOf`): the statement value `statement.hhat` (value `544`, `512`
  coordinates of `F_q`) is the key's transform `key_hat`; `keyOf` decodes it as the verifier's
  preprocessing does (`GordieHowe.Falcon512.KeyNTT.falconDecode`: every entry below `q`, then the C++ inverse
  transform), `stmtOf` writes a key's `keyHat` (`keyOf_stmtOf`).
* **The relation** (`rel`): the Falcon-512 proof-of-possession relation at the decoded key; a
  statement that passes the program's member check (`falcon_key_canonical`) decodes to a key
  (`exists_keyOf_of_statementOk`), and the source verifier rejects the others.
* **The extractor** (`proj`, `extractor`): `GordieHowe.Falcon512.Native.extract` of the source assignment read off
  the committed values (`srcOf`).
* **The hash** (`FalconHashView`): one SHAKE256 call (`SpongeView`) whose input is the nonce and
  the message bytes at the length the in-message flags encode (`lenOf`, `messageBytes`) and whose
  output, two bytes per sample, is the stream the selection reads. Its instance is
  `falconHashView` (`GordieHowe/Applications/Falcon512/Native/ROMParams/Frontend/Hash.lean`).
* **The composition so far** (`mem_rel_of_source`): at a statement that passes the member checks,
  where the source program holds and the selection's event did not occur, the relation holds at
  `proj`, given the hash view and, at the key, some algebra advice satisfying Falcon native's
  algebra constraints (`AlgebraAt`, domain `A`'s obligation).
* **Round-by-round knowledge soundness of `Π_P₀`** (`rbr_of_views`): `GordieHowe.RealizedProgram.rbr_of_events` at the
  selection's event (`selectEvent`, `639/2^bits` at `h2p.select.delta`), the two obligations as
  hypotheses. Domain `A`'s (`AlgebraSound`) is proved in
  `GordieHowe/Applications/Falcon512/Native/ROMParams/Frontend/Algebra.lean` (`algebraSound`), the hash
  view in `GordieHowe/Applications/Falcon512/Native/ROMParams/Frontend/Hash.lean` (`falconHashView`).
-/

namespace GordieHowe.Falcon512.Native.ROMParams

open GordieHowe.Bits IOP
open Emulated (PublicKey bytesOf)
open scoped NNReal ENNReal

/-! ## The program facts -/

/-- **The selection of a native Falcon program** (`h2p.select.*`, domain `H`): the counter `count`
(value `541`), the completion flags `full` (`542`), the challenge value `δ` (`543`), the selected
words' bits `select.raw` (`540`), the shared expressions `489` (the stream: the masked sum of the
views of the squeezed state `h2p.shake.state` and the output blocks `h2p.shake.out.p1`–`p9`), `490`
(the comparisons) and `491` (the acceptance bits), and the constants `1` (`26`), `0` (`0`), the
zeros (`35`, `37`), the ones (`33`), `g` (`34`), `g^512` (`36`), `e_u` (`38`), `g^j` (`39`) and the
bits of `61445` (`32`). -/
abbrev selShape : RealizedProgram.SelectShape :=
  ⟨0, 541, 542, 543, 540, 489, 490, 491, 26, 0, 35, 37, 33, 34, 36, 38, 39, 32⟩

/-- **The program facts the native Falcon frontend reads outside the Keccak trace and domain `A`**,
each decided per program: the selection's predicates `246`–`249` and its shape, the constants'
entries, `δ` the source program's one challenge; `mac.equal` and `crossing.c_A.boolean`; the
statement's member check of `hhat` (value `544`) and the values the extractor reads. -/
class FalconHBase (program : RealizedProgram) : Prop where
  /-- The selection's predicates are `h2p.select.start`, `.step`, `.done` and `.route`, source
  predicates. -/
  selectPreds : program.predByName "h2p.select.start" = some 246 ∧
    program.predByName "h2p.select.step" = some 247 ∧
    program.predByName "h2p.select.done" = some 248 ∧
    program.predByName "h2p.select.route" = some 249 ∧
    (∀ p ∈ [246, 247, 248, 249], program.inSource (program.predicate p) = true)
  /-- The selection has the first-`n` shape at `(S, n, w) = (639, 512, 16)`. -/
  selectShape_eq : program.selectShape? 639 512 16 246 247 248 249 = some selShape
  /-- The program's shared expressions read only earlier entries. -/
  refsOrdered : program.RefsOrdered
  /-- Domain `H` has field `0`. -/
  domainField0 : program.domainField 0 = 0
  /-- The selection's constants are values of domain `H`. -/
  selConstField : ∀ v ∈ [26, 0, 35, 37, 33, 34, 36, 38, 39, 32], program.valueField v = 0
  /-- The entries of the selection's constants other than the labels. -/
  const_entries :
    (program.constEntries 39).getD 0 0 = 1 ∧ (program.constEntries 26).getD 0 0 = 1 ∧
      (program.constEntries 0).getD 0 0 = 0 ∧
      (∀ i < 638, (program.constEntries 35).getD i 0 = 0) ∧
      (∀ t < 127, (program.constEntries 37).getD t 0 = 0) ∧
      (∀ t < 127, (program.constEntries 33).getD t 0 = 1) ∧
      (program.constEntries 34).getD 0 0 = (program.constEntries 39).getD 1 0 ∧
      (∀ u < 16, (program.constEntries 38).getD u 0 = (program.constEntries 39).getD u 0) ∧
      (∀ u < 16, (program.constEntries 32).getD u 0 = 61445 / 2 ^ u % 2)
  /-- `δ` is challenge `0`. -/
  deltaKind : (program.value 543).kind = .challenge 0
  /-- `δ`'s field is its challenge's. -/
  deltaField : program.chalField 0 = program.valueField 543
  /-- The selection's committed values read nothing from the run. -/
  selReads_nil : ∀ v ∈ 541 :: 542 :: 540 :: program.exprNodes (.ref 489),
    program.nodeReads program.fuel v = []
  /-- Challenge `0` is full, of one coordinate, in field `0`. -/
  chal0 : (program.challenge 0).size = 1 ∧ (program.challenge 0).sampler = .full ∧
    program.chalField 0 = 0
  /-- The source program's one challenge is `h2p.select.delta`. -/
  isSourceChal_iff : ∀ j, program.IsSourceChal j ↔ j = 0

/-- **The program facts the Falcon frontend reads about domain `A`**, each decided per program, at
the identifiers `cA` of the sample bits `crossing.c_A` and `s2` of the signature polynomial: domain
`A` has field `1`; `mac.equal` and `crossing.c_A.boolean`; the statement's member check of `hhat`
(value `544`) and the values the extractor reads. The native programs have `(cA, s2) = (545, 546)`,
the emulated ones `(546, 547)`. -/
class FalconACore (program : RealizedProgram) where
  /-- The identifier of `crossing.c_A`. -/
  cA : ℕ
  /-- The identifier of `s2`. -/
  s2 : ℕ
  /-- Domain `A` has field `1`. -/
  domainField1 : program.domainField 1 = 1
  /-- `mac.equal` is `cross(H, select.raw, A, c_A)` of width `1`, a source predicate. -/
  macEqual : ∃ p, program.predByName "mac.equal" = some p ∧
    (program.predicate p).body.crossLeaves? = some ⟨0, 540, 1, cA⟩ ∧
    program.inSource (program.predicate p) = true
  /-- `crossing.c_A.boolean` is `c_A · c_A = c_A` in `A`, a source predicate. -/
  cABoolean : ∃ p, program.predByName "crossing.c_A.boolean" = some p ∧
    (program.predicate p).body.boolCheck? = some ⟨1, cA⟩ ∧
    program.inSource (program.predicate p) = true
  /-- `select.raw` is a bit view; it and `c_A` have `8192` coordinates. -/
  raw_facts : program.isBitView 540 = true ∧ (program.value 540).size = 8192 ∧
    (program.value (cA)).size = 8192
  /-- The member check `falcon_key_canonical [12289]` of `hhat`. -/
  hhatCheck : RealizedProgram.MemberCheck.mk "hhat" 0 1024 "falcon_key_canonical" [12289] ∈
    program.statement.checks
  /-- `hhat` is value `544`. -/
  hhatValue : program.memberValue? "hhat" = some 544
  /-- `hhat` has `512` coordinates. -/
  hhatSize : (program.value 544).size = 512
  /-- `hhat` is a value of field `1`. -/
  hhatField : program.valueField 544 = 1
  /-- The values the extractor reads read nothing from the run. -/
  srcReads_nil : ∀ v ∈ [45, 46, 47, 540, cA, s2], program.nodeReads program.fuel v = []

/-- **The selection's labels in domain `H`'s field** (decided in the field `FH`): entry `j < 512` of
the constant `39` is `g^j`, the constant `36` is `g^512`. -/
class FalconHConsts (program : RealizedProgram) (FH : RealizedProgram.FieldInterp) [HField FH] : Prop where
  /-- Entry `j` of the constant `39` is `g^j`. -/
  gpow : ∀ j < 512, FH.decode ((program.constEntries 39).getD j 0) =
    (HField.sel (FH := FH)).g ^ j
  /-- The constant `36` is `g^512`. -/
  gN : FH.decode ((program.constEntries 36).getD 0 0) = (HField.sel (FH := FH)).g ^ 512

variable {program : RealizedProgram} {FH FA : RealizedProgram.FieldInterp}

set_option hygiene false in
local notation "interp" => RealizedProgram.falconInterpOf FH FA

/-! ## The selection -/

/-- **Facts about field `0`'s interpretation transfer** to a field identifier equal to `0`. -/
theorem fieldAt_transfer (P : RealizedProgram.FieldInterp → Prop) {f : ℕ} (hf : f = 0) (h : P FH) :
    P (interp f) := by
  subst hf
  exact h

variable (program FH FA) in
/-- **The selection's field interpretation**: the field of the selection's domain. -/
abbrev SelField : RealizedProgram.FieldInterp := (RealizedProgram.falconInterpOf FH FA).field (RealizedProgram.SelectShape.field program selShape)

/-- **The selection's field data** (each program instantiates it, the selection's field being `FH`):
domain `H`'s field data at the selection's field (`inst`), of `FH`'s bit length, and the selection's
labels there: entry `j < 512` of the constant `39` is `g^j`, the constant `36` is `g^512`. -/
class FalconSelField (program : RealizedProgram) (FH FA : RealizedProgram.FieldInterp) [HField FH] where
  /-- Domain `H`'s field data at the selection's field. -/
  inst : HField (SelField program FH FA)
  /-- The selection's field has `FH`'s bit length. -/
  bits_eq : inst.bits = HField.bits FH
  /-- Entry `j` of the constant `39` is `g^j`. -/
  gpow : ∀ j < 512, (SelField program FH FA).decode ((program.constEntries 39).getD j 0) =
    inst.sel.g ^ j
  /-- The constant `36` is `g^512`. -/
  gN : (SelField program FH FA).decode ((program.constEntries 36).getD 0 0) = inst.sel.g ^ 512

attribute [instance] FalconSelField.inst

variable [HField FH] [FalconHBase program]

/-- The selection's field identifier is `0`. -/
theorem selField : RealizedProgram.SelectShape.field program selShape = 0 := FalconHBase.domainField0

/-- **The selection field** of the selection's field (`HField.sel`: `GF(2^16)`, `X`, `g` the
subfield's generator, `e_u = g^u`). -/
def selF [FalconSelField program FH FA] : SelectionField (interp (RealizedProgram.SelectShape.field program selShape)).K 639 16 :=
  HField.sel (FH := SelField program FH FA)

instance [FalconSelField program FH FA] : CharP (interp (RealizedProgram.SelectShape.field program selShape)).K 2 :=
  HField.charTwo (FH := SelField program FH FA)

/-- A constant of the selection, read in the selection's field, is its entry decoded. -/
theorem constRead_sel {v : ℕ} (hv : v ∈ [26, 0, 35, 37, 33, 34, 36, 38, 39, 32]) (i : ℕ) :
    program.constRead interp (RealizedProgram.SelectShape.field program selShape) v i =
      (interp (RealizedProgram.SelectShape.field program selShape)).decode ((program.constEntries v).getD i 0) :=
  RealizedProgram.constRead_of_valueField ((FalconHBase.selConstField v hv).trans selField.symm) i

/-- **The selection's constants** (`SelectShape.Consts`) for the selection field `selF`, `n = 512`
and the bound `61445`: decided entries (`FalconHBase.const_entries`) and the labels
(`FalconSelField`); `X` is the decoding of `2`. -/
theorem selConsts [FalconSelField program FH FA] : selShape.Consts program interp selF 512 61445 where
  one := by
    rw [constRead_sel (by simp), FalconHBase.const_entries.2.1]
    exact HField.decode_one (FH := SelField program FH FA)
  zero := by
    rw [constRead_sel (by simp), FalconHBase.const_entries.2.2.1]
    exact HField.decode_zero (FH := SelField program FH FA)
  zerosStep i hi := by
    rw [constRead_sel (by simp), FalconHBase.const_entries.2.2.2.1 i hi]
    exact HField.decode_zero (FH := SelField program FH FA)
  zerosDone t ht := by
    rw [constRead_sel (by simp), FalconHBase.const_entries.2.2.2.2.1 t ht]
    exact HField.decode_zero (FH := SelField program FH FA)
  ones t ht := by
    rw [constRead_sel (by simp), FalconHBase.const_entries.2.2.2.2.2.1 t ht]
    exact HField.decode_one (FH := SelField program FH FA)
  g := by
    rw [constRead_sel (by simp), FalconHBase.const_entries.2.2.2.2.2.2.1]
    exact (FalconSelField.gpow 1 (by omega)).trans (pow_one _)
  gN := by
    rw [constRead_sel (by simp)]
    exact FalconSelField.gN
  basis u := by
    rw [constRead_sel (by simp), FalconHBase.const_entries.2.2.2.2.2.2.2.1 u u.isLt]
    exact (FalconSelField.gpow u (by have := u.isLt; omega)).trans
      (HField.e_eq (FH := SelField program FH FA) u).symm
  gpow j hj := by
    rw [constRead_sel (by simp)]
    exact FalconSelField.gpow j hj
  cutoff u hu := by
    rw [constRead_sel (by simp), FalconHBase.const_entries.2.2.2.2.2.2.2.2 u hu]
    exact HField.decode_lt_two (FH := SelField program FH FA) (Nat.mod_lt _ (by norm_num))
  two := HField.decode_two (FH := SelField program FH FA)

/-! ### Soundness and the event at `h2p.select.delta` -/

/-- **The selection's shape** (`FalconHBase.selectShape_eq`). -/
theorem selectMatches : program.SelectMatches 639 512 16 246 247 248 249 selShape :=
  RealizedProgram.selectMatches_of_selectShape? FalconHBase.selectShape_eq

/-- **The stream's samples** (`h2p.select`'s view of `shake.out`, `16` bits each). -/
abbrev selSample (e : program.Env interp) :
    Fin 639 → BitWires (interp (RealizedProgram.SelectShape.field program selShape)).K 16 :=
  selShape.sample program (program.reader e)

/-- **The selected words** (`select.raw`, `16` bits each). -/
abbrev selWord (e : program.Env interp) :
    Fin 512 → BitWires (interp (RealizedProgram.SelectShape.field program selShape)).K 16 :=
  selShape.word program (program.reader e)

/-- **The route** (`count`, and `full` from sample `512` on). -/
abbrev selRoute (e : program.Env interp) :
    Fin 639 → Route (interp (RealizedProgram.SelectShape.field program selShape)).K :=
  selShape.route program (program.reader e) 512

/-- **The selection's event** at the committed values: `SelectFirstN.badEvent` of the samples, the
selected words and the route (degree `639`). -/
noncomputable def selBad [FalconSelField program FH FA] (e : program.Env interp) :
    ChallengeEvent (interp (RealizedProgram.SelectShape.field program selShape)).K :=
  SelectFirstN.badEvent selF 61445 (selSample e) (selWord e) (selRoute e) (by decide)

/-- **The selection's event has degree `639`.** -/
theorem selBad_deg [FalconSelField program FH FA] (e : program.Env interp) : (selBad e).deg = 639 := rfl

/-- **The selection's soundness** where the source program holds: the selected words are the
first `512` samples below `61445` (`firstAccepted`), or `δ` is a root of the selection's event. -/
theorem firstAccepted_or_badAt [FalconSelField program FH FA] {e : program.Env interp}
    (hs : program.SourceSatAt e) :
    firstAccepted (fun v => decide (v < 61445)) (fun i => Bits.natOfBits (selSample e i)) 512 =
        some (fun j => Bits.natOfBits (selWord e j)) ∨
      (selBad e).BadAt (selShape.deltaAt program (program.reader e)) := by
  obtain ⟨h1, h2, h3, h4, hsrc⟩ := FalconHBase.selectPreds (program := program)
  exact selectMatches.firstAccepted_or_badAt FalconHBase.refsOrdered selConsts (by norm_num)
    (by decide) (by decide) hs (hs.holdsAt_of_predByName h1 (hsrc 246 (by simp)))
    (hs.holdsAt_of_predByName h2 (hsrc 247 (by simp)))
    (hs.holdsAt_of_predByName h3 (hsrc 248 (by simp)))
    (hs.holdsAt_of_predByName h4 (hsrc 249 (by simp)))

/-- **`δ` is challenge `0`** (`h2p.select.delta`), read in the selection's field. -/
theorem selDelta_eq (e : program.Env interp) :
    selShape.deltaAt program (program.reader e) = RealizedProgram.castElt (e.chal 0 0) := by
  unfold RealizedProgram.SelectShape.deltaAt
  rw [RealizedProgram.evalE_leaf]
  exact RealizedProgram.castElt_reader_of_challenge e FalconHBase.deltaKind FalconHBase.deltaField 0

/-- **The selection's event is fixed by the statement and the committed assignment.** -/
theorem selBad_congr [FalconSelField program FH FA] {e e' : program.Env interp} (hs : e.stmt = e'.stmt) (ha : e.asg = e'.asg) :
    selBad e = selBad e' := by
  obtain ⟨h1, h2, h3⟩ :=
    RealizedProgram.selectReadings_congr (s := selShape) (S := 639) (n := 512) (w := 16)
    (rd := program.reader e) (rd' := program.reader e') fun v hv =>
      RealizedProgram.reader_eq_of_nodeReads_nil (FalconHBase.selReads_nil v hv) hs ha
  unfold selBad selSample selWord selRoute
  simp only [h1, h2, h3]

/-- **The event at challenge `0`** (`h2p.select.delta`, the source program's one challenge): `δ`
is a root of the selection's event. No event at any other challenge. -/
def selectEvent [FalconSelField program FH FA] (j : ℕ) (e : program.Env interp) : Prop :=
  j = 0 ∧ (selBad e).BadAt (RealizedProgram.castElt (e.chal 0 0))

/-- **The challenge-use rule** (`RealizedProgram.ChallengeUseAt`): the selection's event reads the committed
assignment and challenge `0`. -/
theorem selectEvent_use [FalconSelField program FH FA] : RealizedProgram.ChallengeUseAt program interp selectEvent := by
  intro j e e' h
  unfold selectEvent
  by_cases hj : j = 0
  · subst hj
    rw [selBad_congr h.stmt h.asg, h.chal 0 (Or.inr ⟨rfl, le_refl 0⟩)]
  · simp [hj]

/-- **The selection field has `2^bits` elements.** -/
theorem card_sel [FalconSelField program FH FA] :
    Fintype.card (interp (RealizedProgram.SelectShape.field program selShape)).K =
      2 ^ HField.bits FH := by
  rw [← FalconSelField.bits_eq (program := program) (FA := FA)]
  exact HField.card (FH := SelField program FH FA)

/-- **The event's probability** over `h2p.select.delta`, uniform in `FH`: at most `639/2^bits`
(`RealizedProgram.probUniform_badAt_setChal_le`, Schwartz–Zippel). -/
theorem selectEvent_prob [FalconSelField program FH FA] (e : program.Env interp) :
    Pr[c ← program.ChalVal interp 0 : selectEvent 0 (e.setChal 0 c)] ≤
      ((639 / 2 ^ HField.bits FH : ℝ≥0) : ℝ≥0∞) := by
  have hset : ∀ c, selectEvent 0 (e.setChal 0 c) ↔
      (selBad e).BadAt (RealizedProgram.castElt ((e.setChal 0 c).chal 0 0)) := fun c => by
    simp only [selectEvent, true_and]
    rw [selBad_congr (e := e.setChal 0 c) (e' := e) rfl rfl]
  simp only [hset]
  obtain ⟨hsz, hsm, hf⟩ := FalconHBase.chal0 (program := program)
  refine (RealizedProgram.probUniform_badAt_setChal_le (j := 0) hsz hsm (hf.trans selField.symm)
    (selBad e) e).trans ?_
  rw [selBad_deg, card_sel]
  norm_num

/-- **The round errors of `Π_P₀`'s challenges**: `639/2^bits` at `h2p.select.delta`, `0`
elsewhere. -/
noncomputable def selectEps (j : ℕ) : ℝ≥0 := if j = 0 then 639 / 2 ^ HField.bits FH else 0

/-- **The events' probabilities** (`RealizedProgram.rbr_of_events`' `hbound`): at the source program's
challenge `h2p.select.delta`, at most `639/2^bits` (`selectEvent_prob`). -/
theorem selectEvent_bound [FalconSelField program FH FA] : ∀ j, program.IsSourceChal j → ∀ e : program.Env interp,
    Pr[c ← program.ChalVal interp j : selectEvent j (e.setChal j c)] ≤ selectEps (FH := FH) j := by
  intro j hj e
  obtain rfl := (FalconHBase.isSourceChal_iff j).1 hj
  simpa [selectEps] using selectEvent_prob e

/-- **The natural of bits read in an equal field identifier** is the natural of the bits. -/
theorem natOfBits_castElt {I : RealizedProgram.Interp} {a b m : ℕ} (h : a = b) (w : BitWires (I a).K m) :
    Bits.natOfBits (fun i => (RealizedProgram.castElt (w i) : (I b).K)) = Bits.natOfBits w := by
  subst h
  simp only [RealizedProgram.castElt_self]

/-- **The stream's samples read in domain `H`'s field `0`** (`selSample`, the selection's field
identifier being `0`). -/
def selSample0 (e : program.Env interp) (i : Fin falcon512.S) :
    BitWires (interp 0).K falconSampleBits :=
  fun b => RealizedProgram.castElt (selSample e i b)

theorem natOfBits_selSample0 (e : program.Env interp) (i : Fin falcon512.S) :
    Bits.natOfBits (selSample0 e i) = Bits.natOfBits (selSample e i) :=
  natOfBits_castElt selField _

/-- **An equation read in a domain of field `f`** is the equation read in field `f`. -/
theorem evalWith_eq_iff_of_domainField {I : RealizedProgram.Interp} {rd : program.Valuation I} {d f : ℕ}
    (h : program.domainField d = f) {a b : RealizedProgram.Expr} {i j : ℕ} :
    program.evalWith rd d a i = program.evalWith rd d b j ↔
      program.evalE rd f a i = program.evalE rd f b j := by
  unfold RealizedProgram.evalWith
  rw [h]

/-- **A field `equal` of domain `H` holds coordinatewise in field `0`.** -/
theorem holdsAt_equal0 {e : program.Env interp} {lhs rhs : RealizedProgram.Expr} {t : RealizedProgram.Target}
    (h : program.HoldsAt e (.equal 0 lhs rhs t)) :
    ∀ i < program.exprLen lhs,
      program.evalE (program.reader e) 0 lhs i = program.evalE (program.reader e) 0 rhs i :=
  fun i hi => (evalWith_eq_iff_of_domainField FalconHBase.domainField0).1 (h i hi)

/-- **A field `equal` of domain `H` holds when it holds coordinatewise in field `0`.** -/
theorem holdsWith_equal0_of {rd : program.Valuation interp} {lhs rhs : RealizedProgram.Expr} {t : RealizedProgram.Target}
    (h : ∀ i < program.exprLen lhs, program.evalE rd 0 lhs i = program.evalE rd 0 rhs i) :
    program.HoldsWith rd (.equal 0 lhs rhs t) :=
  fun i hi => (evalWith_eq_iff_of_domainField FalconHBase.domainField0).2 (h i hi)

/-- **The natural of a word read at a field identifier equal to `f`** is the natural read at `f`. -/
theorem natOfBits_wordAt_congr {I : RealizedProgram.Interp} {rd : program.Valuation I} {f f' : ℕ} (h : f = f')
    (v w j : ℕ) :
    Bits.natOfBits (program.wordAt rd f v w j) = Bits.natOfBits (program.wordAt rd f' v w j) := by
  subst h
  rfl

/-- **The selected samples** (`h2p.select.raw`, value `540`, domain `H`): sample `j` is word `j` of
`16` bits, read in `FH`. -/
def rawBits (e : program.Env interp) (j : Fin falcon512.n) :
    BitWires (interp 0).K falconSampleBits :=
  program.wordAt (program.reader e) 0 540 16 j

/-! ## The message and the hash -/

/-- **The nonce bits** (value `45`, `40 × 8` bits of domain `H`), read in `FH`. -/
def nonceBits (rd : program.Valuation interp) :
    BitWires (interp 0).K (8 * falcon512.saltBytes) :=
  fun k => program.evalE rd 0 (.leaf 45) k

/-- **The message's length** read off the in-message flags (value `47`, `136` bits of domain `H`,
`f_i = [i < 40 + L]`): the number of flags set, less the nonce's `40` bytes, at most the
relation's maximum `32`. Where the source program holds, the flags are the prefix of length
`40 + L` (`h2p.shake.padding.monotone`, `min`, `max`).

Running time: `136` readings of a committed value and a count.
This running time is argued here, not proved in Lean. -/
def lenOf (rd : program.Valuation interp) : ℕ :=
  min 32 ((Finset.univ.filter fun i : Fin 136 => program.evalE rd 0 (.leaf 47) i = 1).card - 40)

theorem lenOf_le (rd : program.Valuation interp) : lenOf rd ≤ 32 := min_le_left _ _

/-- **The message bits** at a length `L`: the first `8 L` bits of the message's part of the hash
buffer (value `46`, `96 × 8` bits of domain `H`: the message, its padding at the private length,
zeros), read in `FH`. -/
def messageBits (rd : program.Valuation interp) (L : ℕ) :
    BitWires (interp 0).K (8 * L) :=
  fun k => program.evalE rd 0 (.leaf 46) k

/-- **The message bytes**: the message bits at the length the flags encode (`lenOf`), as bytes. -/
def messageBytes (rd : program.Valuation interp) : List ℕ :=
  bytesOf (messageBits rd (lenOf rd))

/-- **The message bytes depend only on the message and its flags** (values `46` and `47`). -/
theorem messageBytes_congr {rd rd' : program.Valuation interp} (h46 : rd 46 = rd' 46)
    (h47 : rd 47 = rd' 47) : messageBytes rd = messageBytes rd' := by
  have hL : lenOf rd = lenOf rd' := by
    unfold lenOf
    rw [Finset.filter_congr (q := fun i : Fin 136 => program.evalE rd' 0 (.leaf 47) i = 1)
      fun i _ => by simp only [RealizedProgram.evalE_leaf, h47]]
  have hm : ∀ L, messageBits rd L = messageBits rd' L := fun L => funext fun k => by
    simp only [messageBits, RealizedProgram.evalE_leaf, h46]
  unfold messageBytes
  rw [hm, hL]

/-- **The hash of a native Falcon program as the frontend reads it**: one SHAKE256 call of domain `H`
squeezing `2 · 639` bytes (`SpongeView`), whose input bytes are the nonce's then the message's, at
the length the in-message flags encode (`input_bytes`, `messageBytes`), and whose output, two bytes
per sample (`HashCircuit.sampleAt`: byte `2i + 1` as bits `0 … 7`, byte `2i` as bits `8 … 15`), is
the stream the selection reads (`samples`), where the source program holds. The instance reads the
Keccak trace (`falconHashView`, `GordieHowe/Applications/Falcon512/Native/ROMParams/Frontend/Hash.lean`). -/
structure FalconHashView where
  /-- The SHAKE256 call. -/
  sponge : RealizedProgram.SpongeView program interp 0 (2 * falcon512.S)
  /-- The input bytes are the nonce's then the message's. -/
  input_bytes : ∀ e, program.SourceSatAt e → Shake256.inputBytes (sponge.input e) =
    bytesOf (nonceBits (program.reader e)) ++ messageBytes (program.reader e)
  /-- The selection's samples are the output, two bytes per sample. -/
  samples : ∀ e, program.SourceSatAt e → ∀ i,
    Bits.natOfBits (selSample e i) = Bits.natOfBits (HashCircuit.sampleAt (sponge.out e) i)

/-- **The selection's samples are Falcon's candidate stream** of the nonce and message bytes, where
the source program holds (`FalconHashView`, `HashCircuit.sampleAt_decode`). -/
theorem natOfBits_selSample (hv : FalconHashView (program := program) (FH := FH) (FA := FA))
    {e : program.Env interp}
    (hs : program.SourceSatAt e) (i : Fin falcon512.S) :
    Bits.natOfBits (selSample e i) = Falcon512.streamCandidates falcon512 shake256
      (bytesOf (nonceBits (program.reader e))) (messageBytes (program.reader e)) i := by
  rw [hv.samples e hs i, HashCircuit.sampleAt_decode, Falcon512.streamCandidates,
    ← hv.input_bytes e hs, ← Shake256.SpongeSpec.xof_shake256]
  exact congrFun (congrArg samples16 (funext (hv.sponge.sound e hs))) i

variable [AReading FA] [FalconACore program]

/-- **A field `equal` of domain `A` holds when it holds coordinatewise in field `1`.** -/
theorem holdsWith_equal1_of {rd : program.Valuation interp} {lhs rhs : RealizedProgram.Expr} {t : RealizedProgram.Target}
    (h : ∀ i < program.exprLen lhs, program.evalE rd 1 lhs i = program.evalE rd 1 rhs i) :
    program.HoldsWith rd (.equal 1 lhs rhs t) :=
  fun i hi => (evalWith_eq_iff_of_domainField FalconACore.domainField1).2 (h i hi)

/-! ## The crossing -/

/-- **The sample bits in `A`** (`crossing.c_A`, value `cA`): sample `j` is word `j` of `16` bits,
read in `FA`. -/
def cABits (e : program.Env interp) (j : Fin falcon512.n) :
    BitWires (interp 1).K falconSampleBits :=
  program.wordAt (program.reader e) 1 (FalconACore.cA program) 16 j

/-- **The selected samples are the samples `c_A` reads**: where the source program holds, sample `j` of `select.raw` and of
`c_A` denote the same natural. `mac.equal` gives the agreement
(`RealizedProgram.natOfBits_wordAt_eq_of_cross`): `select.raw` is a bit view and `crossing.c_A.boolean`
makes `c_A` Boolean. -/
theorem natOfBits_raw_eq {e : program.Env interp} (h : program.SourceSatAt e)
    (j : Fin falcon512.n) : Bits.natOfBits (rawBits e j) = Emulated.cNat (cABits e) j := by
  obtain ⟨hraw, hsize, hsizeA⟩ := FalconACore.raw_facts (program := program)
  obtain ⟨pm, hpm, hcl, hsrcm⟩ := FalconACore.macEqual (program := program)
  obtain ⟨pb, hpb, hbc, hsrcb⟩ := FalconACore.cABoolean (program := program)
  have hcross := h.holdsAt_of_predByName hpm hsrcm
  have hbool := h.holdsAt_of_predByName hpb hsrcb
  have hj : (j : ℕ) * 16 + 16 ≤ (program.value 540).size := by
    rw [hsize]
    have := j.isLt
    change (j : ℕ) < 512 at this
    omega
  have hd0 := FalconHBase.domainField0 (program := program)
  have hd1 := FalconACore.domainField1 (program := program)
  have key := RealizedProgram.natOfBits_wordAt_eq_of_cross (s := ⟨0, 540, 1, (FalconACore.cA program)⟩) hcl hcross
    (by change (interp (program.domainField 0)).toNat 0 = 0; rw [hd0]; exact HField.toNat_zero)
    (by change (interp (program.domainField 0)).toNat 1 = 1; rw [hd0]; exact HField.toNat_one)
    (by change (interp (program.domainField 1)).toNat 0 = 0; rw [hd1]; exact AReading.toNat_zero)
    (by change (interp (program.domainField 1)).toNat 1 = 1; rw [hd1]; exact AReading.toNat_one)
    (fun i _ => RealizedProgram.evalE_leaf_bool_of_isBitView e hraw _ i)
    (fun i hi => RealizedProgram.bool_of_boolCheck hbc hbool
      (by change i < (program.value (FalconACore.cA program)).size; rw [hsizeA]; rw [hsize] at hi; exact hi))
    hj
  change Bits.natOfBits (program.wordAt (program.reader e) (program.domainField 0) 540 16 j) =
    Bits.natOfBits (program.wordAt (program.reader e) (program.domainField 1) (FalconACore.cA program) 16 j) at key
  rw [hd0, hd1] at key
  exact key

/-! ## The statement -/

/-- **The key of a statement**: the statement value `statement.hhat` (value `544`) read as naturals
(`FieldInterp.toNat`) and decoded as the verifier's preprocessing decodes `key_hat`
(`FalconKeyNTT.falconDecode 512 12289`: every entry below `q`, then the C++ inverse transform); none
when an entry is not below `q`. -/
-- spec-side
def keyOf (x : program.Valuation interp) : Option PublicKey :=
  (KeyNTT.falconDecode 512 12289
      fun i => (interp (program.valueField 544)).toNat (x 544 i)).map
    fun c => ⟨Falcon512.ofCoeff fun i => (c i : _root_.Falcon.Coeff)⟩

/-- **The statement of a key**: `statement.hhat` holds the key's transform `keyHat` (the forward
C++ transform of its coefficients), every other statement coordinate `0`. -/
def stmtOf (pk : PublicKey) : program.Valuation interp := fun v i =>
  if h : v = 544 ∧ i < 512 then
    RealizedProgram.castElt (a := 1) ((KeyNTT.keyHat pk ⟨i, h.2⟩ : ℕ) : (interp 1).K)
  else 0

/-- `statement.hhat` of a key's statement holds the key's transform. -/
theorem stmtOf_hhat (pk : PublicKey) (i : Fin 512) :
    (stmtOf pk : program.Valuation interp) 544 i = RealizedProgram.castElt (a := 1) ((KeyNTT.keyHat pk i : ℕ) : (interp 1).K) := by
  unfold stmtOf
  rw [dif_pos (show 544 = 544 ∧ (i : ℕ) < 512 from ⟨rfl, i.isLt⟩)]

/-- **The key of a key's statement is the key.** -/
theorem keyOf_stmtOf (pk : PublicKey) : keyOf (stmtOf pk : program.Valuation interp) = some pk := by
  have hread : (fun i : Fin 512 => (interp (program.valueField 544)).toNat
      ((stmtOf pk : program.Valuation interp) 544 i)) =
      KeyNTT.keyHat pk := funext fun i => by
    rw [stmtOf_hhat, RealizedProgram.toNat_castElt FalconACore.hhatField.symm]
    exact AReading.toNat_natCast (KeyNTT.keyHat_lt pk i)
  unfold keyOf
  rw [hread, KeyNTT.falconDecode_keyHat, Option.map_some]
  simp only [ZMod.natCast_zmod_val, Falcon512.ofCoeff_coeff]

/-- **A statement that decodes to a key holds the key's transform**: its `statement.hhat` read as
naturals is `keyHat pk` (`KeyNTT.falconDecode_512_eq_some_iff`). -/
theorem toNat_hhat_of_keyOf {x : program.Valuation interp} {pk : PublicKey}
    (h : keyOf x = some pk) (s : Fin 512) :
    (interp (program.valueField 544)).toNat (x 544 s) = KeyNTT.keyHat pk s := by
  unfold keyOf at h
  obtain ⟨c, hc, hpk⟩ := Option.map_eq_some_iff.1 h
  obtain ⟨hlt, hntt⟩ := (KeyNTT.falconDecode_512_eq_some_iff _ c).1 hc
  have hcoeff : (fun i : Fin 512 => (Falcon512.coeff pk.h i).val) = c := by
    rw [← hpk]
    funext i
    simp only [Falcon512.coeff_ofCoeff]
    exact ZMod.val_natCast_of_lt (hlt i)
  unfold KeyNTT.keyHat
  rw [hcoeff, hntt]

/-! ## The relation -/

/-- **A statement that passes the member checks decodes to a key**: the check
`falcon_key_canonical [12289]` of `hhat` (value `544`, `RealizedProgram.StatementOk`) bounds every entry
below `q`, where `KeyNTT.falconDecode` succeeds. -/
theorem exists_keyOf_of_statementOk {x : program.Valuation interp}
    (hx : program.StatementOk interp x) : ∃ pk, keyOf x = some pk := by
  have hm := FalconACore.hhatCheck (program := program)
  have hv := FalconACore.hhatValue (program := program)
  have hsize := FalconACore.hhatSize (program := program)
  have hlt : ∀ i : Fin 512, (interp (program.valueField 544)).toNat (x 544 i) < 12289 :=
    fun i => hx.toNat_lt hm hv (by decide) (by rw [hsize]; exact i.isLt)
  unfold keyOf
  rw [KeyNTT.falconDecode, if_pos hlt]
  exact ⟨_, rfl⟩

/-- **The witness of the native Falcon proofs of possession**: a message of some length `L ≤ 32` (the relation's
maximum, `private_message.h`) and a Falcon-512 signature (`PoP.Falcon512.Witness L`). -/
abbrev VarWitness : Type := Σ L : Fin 33, Falcon512.PoP.Witness L

instance : Inhabited VarWitness := ⟨⟨0, default⟩⟩

/-- **The relation of the native Falcon theorem at the realized program**: the statement decodes to a key
(`keyOf`), and at that key the Falcon-512 proof-of-possession relation holds for the witness's
message, of its length `L ≤ 32` (`PoP.Falcon512.rel L`). A statement that passes the program's
member checks decodes to a key (`exists_keyOf_of_statementOk`); the source protocol's verifier
rejects every other statement (`RealizedProgram.sourceVerifier`, `RealizedProgram.StatementOk`). -/
def rel : Set (program.Valuation interp × VarWitness) :=
  {p | ∃ pk, keyOf p.1 = some pk ∧ (pk, p.2.2) ∈ Falcon512.PoP.rel p.2.1}

/-! ## The extractor -/

/-- **The signature polynomial** (`s2`, value `s2` of domain `A`), read in `FA`. -/
def s2Vals (rd : program.Valuation interp) (i : Fin falcon512.n) : (interp 1).K :=
  program.evalE rd 1 (.leaf (FalconACore.s2 program)) i

/-- **The environment of a statement and a committed assignment** with every challenge and late
value `0`: what the extractor reads the committed values from (they read nothing from the run). -/
def commitEnv (x : program.Valuation interp) (a : program.Assignment interp) :
    program.Env interp :=
  ⟨x, a, fun _ _ => 0, fun _ _ => 0⟩

/-- **The source assignment read off the committed values** (`Native.Source`): the nonce and
the message bits at the flags' length (`lenOf`), the selected samples `select.raw`, the sample bits
`c_A`, `s2`. The Keccak trace and the algebra advice are not read by the extraction
(`Native.extract`) and are left `0`; the composition takes the advice from domain `A`
(`AlgebraAt`).

Running time: `136 + 8 · 72 + 2 · 8192 + 512` readings of committed values (the flags, then bit
views of committed words read one coordinate each).
This running time is argued here, not proved in Lean. -/
def srcOf (x : program.Valuation interp) (a : program.Assignment interp) :
    Native.Source (interp 0).K (interp 1).K (lenOf (program.reader (commitEnv x a))) where
  nonce := nonceBits (program.reader (commitEnv x a))
  message := messageBits (program.reader (commitEnv x a)) _
  states := fun _ => 0
  raw := rawBits (commitEnv x a)
  cA := cABits (commitEnv x a)
  s2 := s2Vals (program.reader (commitEnv x a))
  alg := ⟨fun _ => 0, ⟨fun _ => ⟨0, 0, 0⟩, fun _ => ⟨0, 0⟩, 0, 0⟩, 0⟩

/-- **The witness extracted from a statement and a committed assignment**: the length the flags
encode (`lenOf`) and Falcon native's extraction (`Native.extract`: the message bytes, and the
signature encoded from the nonce bytes and the centred `s2`) of the source assignment read off the
committed values (`srcOf`).

Running time: `srcOf`'s readings, then `Native.extract` (`msgLen + 40` bytes from their bits,
`512` coefficients of `s2` lifted and centred, the vendored `compress`), polynomial in the program's
size. This running time is argued here, not proved in Lean. -/
-- spec-side
def proj (x : program.Valuation interp) (a : program.Assignment interp) :
    VarWitness :=
  ⟨⟨lenOf (program.reader (commitEnv x a)), Nat.lt_succ_of_le (lenOf_le _)⟩,
    Native.extract (srcOf x a)⟩

/-- **The extractor of `Π_P₀`** for the native Falcon programs (`RealizedProgram.sourceExtractor` at `proj`).

Running time: one read of the transcript's first round and one call of `proj` (polynomial,
`proj`'s paragraph). This running time is argued here, not proved in Lean. -/
def extractor :
    Extractor (program.sourceSpec interp) (program.Valuation interp) VarWitness :=
  program.sourceExtractor interp proj

/-! ## The composition so far -/

/-- **The algebra holds at the key** (domain `A`'s obligation): Falcon's algebraic verifier and the
encoding bounds on the samples the program's `c_A` reads and the signature polynomial extracted from
its `s2` (`Emulated.AlgebraSpec`). Each frontend of domain `A` derives it from the program's
predicates: the native programs through Falcon native's algebra constraints
(`Native.algebra_sound`), the emulated ones from the integer relations of domain `A`. -/
def AlgebraAt (pk : PublicKey) (e : program.Env interp) : Prop :=
  Emulated.AlgebraSpec pk.h (cABits e) (s2Vals (program.reader e))

/-- **Domain `A`'s obligation** (`AlgebraAt` wherever the source program holds): at every
environment where the source program holds and every key its statement decodes to, the algebra holds
at the key. -/
def AlgebraSound : Prop :=
  ∀ e : program.Env interp, program.SourceSatAt e → ∀ pk, keyOf e.stmt = some pk → AlgebraAt pk e

/-- **The committed values read alike** in an environment and in the environment of its statement
and committed assignment (`commitEnv`). -/
theorem reader_commitEnv (e : program.Env interp) {v : ℕ} (hv : v ∈ [45, 46, 47, 540, FalconACore.cA program, FalconACore.s2 program]) :
    program.reader (commitEnv e.stmt e.asg) v = program.reader e v :=
  RealizedProgram.reader_eq_of_nodeReads_nil (FalconACore.srcReads_nil v hv) rfl rfl

/-- **The source assignment's nonce bits** are the environment's. -/
theorem srcOf_nonce (e : program.Env interp) :
    (srcOf e.stmt e.asg).nonce = nonceBits (program.reader e) := by
  funext k
  simp only [srcOf, nonceBits, RealizedProgram.evalE_leaf]
  rw [reader_commitEnv e (by simp)]

/-- **The source assignment's message bytes** are the environment's. -/
theorem srcOf_message (e : program.Env interp) :
    bytesOf (srcOf e.stmt e.asg).message = messageBytes (program.reader e) :=
  messageBytes_congr (reader_commitEnv e (by simp)) (reader_commitEnv e (by simp))

/-- **The source assignment's selected samples** are the environment's. -/
theorem srcOf_raw (e : program.Env interp) : (srcOf e.stmt e.asg).raw = rawBits e := by
  funext j b
  simp only [srcOf, rawBits, RealizedProgram.wordAt, RealizedProgram.evalE_leaf]
  rw [reader_commitEnv e (by simp)]

/-- **The source assignment's sample bits in `A`** are the environment's. -/
theorem srcOf_cA (e : program.Env interp) : (srcOf e.stmt e.asg).cA = cABits e := by
  funext j b
  simp only [srcOf, cABits, RealizedProgram.wordAt, RealizedProgram.evalE_leaf]
  rw [reader_commitEnv e (by simp)]

/-- **The source assignment's `s2`** is the environment's. -/
theorem srcOf_s2 (e : program.Env interp) :
    (srcOf e.stmt e.asg).s2 = s2Vals (program.reader e) := by
  funext i
  simp only [srcOf, s2Vals, RealizedProgram.evalE_leaf]
  rw [reader_commitEnv e (by simp)]

/-- **The frontend's composition, the Keccak trace and domain `A` left open**: at a statement that
passes the member checks, where the source program holds and the selection's event did not occur at
`δ`, the relation holds at the statement and the extracted witness, given the hash view
(`FalconHashView`, domain `H`'s instance) and the algebra at the decoded key (`AlgebraAt`, domain
`A`'s obligation). The proof is `Native.extract_mem_rel_of_spec` at the selection's samples:
they are Falcon's candidate stream (`natOfBits_selSample`), the selected samples are their first
accepted ones (`firstAccepted_or_badAt`), and `select.raw` and `c_A` denote the same samples
(`natOfBits_raw_eq`). -/
theorem mem_rel_of_source [FalconSelField program FH FA]
    (hv : FalconHashView (program := program) (FH := FH) (FA := FA)) {e : program.Env interp}
    (hok : program.StatementOk interp e.stmt) (hs : program.SourceSatAt e)
    (hev : ¬ selectEvent 0 e) (hA : ∀ pk, keyOf e.stmt = some pk → AlgebraAt pk e) :
    (e.stmt, proj e.stmt e.asg) ∈ rel := by
  obtain ⟨pk, hpk⟩ := exists_keyOf_of_statementOk hok
  refine ⟨pk, hpk, ?_⟩
  have hfirst := (firstAccepted_or_badAt hs).resolve_right fun hbad =>
    hev ⟨rfl, by rw [← selDelta_eq]; exact hbad⟩
  change (pk, (proj e.stmt e.asg).2) ∈
    Falcon512.PoP.rel (lenOf (program.reader (commitEnv e.stmt e.asg)))
  refine Native.extract_mem_rel_of_spec (stream := selSample0 e) ?_ ?_ ?_ ?_
  · intro i
    change _ = Falcon512.streamCandidates falcon512 shake256 (bytesOf (srcOf e.stmt e.asg).nonce)
      (bytesOf (srcOf e.stmt e.asg).message) i
    rw [srcOf_nonce, srcOf_message, natOfBits_selSample0]
    exact natOfBits_selSample hv hs i
  · change _ = some fun j => Bits.natOfBits ((srcOf e.stmt e.asg).raw j)
    rw [srcOf_raw, funext (natOfBits_selSample0 e)]
    have hw : (fun j : Fin 512 => Bits.natOfBits (selWord e j)) =
        fun j => Bits.natOfBits (rawBits e j) :=
      funext fun j => natOfBits_wordAt_congr selField 540 16 j
    rw [hw] at hfirst
    exact hfirst
  · intro j
    change Bits.natOfBits ((srcOf e.stmt e.asg).raw j) =
      Emulated.cNat (srcOf e.stmt e.asg).cA j
    rw [srcOf_raw, srcOf_cA]
    exact natOfBits_raw_eq hs j
  · rw [srcOf_cA, srcOf_s2]
    exact hA pk hpk

/-! ## Round-by-round knowledge soundness of `Π_P₀`, the open obligations as hypotheses -/

/-- **The relation from the source program without an event** (`RealizedProgram.rbr_of_events`' `hsound`),
at a statement that passes the member checks, given the hash view and the algebra wherever the
source program holds. -/
theorem sound_of_views [FalconSelField program FH FA]
    (hv : FalconHashView (program := program) (FH := FH) (FA := FA))
    (hA : AlgebraSound (program := program) (FH := FH) (FA := FA)) :
    ∀ e : program.Env interp, program.StatementOk interp e.stmt → program.SourceSatAt e →
      (∀ j, program.IsSourceChal j → ¬ selectEvent j e) → (e.stmt, proj e.stmt e.asg) ∈ rel :=
  fun e hok hs hno =>
    mem_rel_of_source hv hok hs (hno 0 ((FalconHBase.isSourceChal_iff 0).2 rfl)) (hA e hs)

/-- **Round-by-round knowledge soundness of `Π_P₀` for the native Falcon programs**, the proof
system headline's hypothesis (`RealizedProgram.rbr_of_events`), given the two obligations the frontend leaves open:
the hash view (`FalconHashView`, the Keccak trace's instance) and the algebra at the decoded key
wherever the source program holds (`AlgebraSound`, domain `A`). The errors are `639/2^bits` at
`h2p.select.delta` and `0` elsewhere (`selectEps`); the extractor is `extractor`. -/
theorem rbr_of_views [FalconSelField program FH FA]
    (hv : FalconHashView (program := program) (FH := FH) (FA := FA))
    (hA : AlgebraSound (program := program) (FH := FH) (FA := FA)) :
    rbrKnowledgeSoundness rel (program.sourceVerifier interp) extractor
      (program.eventState interp rel proj selectEvent selectEvent_use (sound_of_views hv hA))
      (program.roundError interp (selectEps (FH := FH))) :=
  program.rbr_of_events interp rel proj selectEvent (selectEps (FH := FH)) selectEvent_use
    selectEvent_bound (sound_of_views hv hA)

end GordieHowe.Falcon512.Native.ROMParams
