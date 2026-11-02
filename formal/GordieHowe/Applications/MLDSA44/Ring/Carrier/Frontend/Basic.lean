-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA44.Ring.Carrier.Frontend.Select
public import GordieHowe.Applications.MLDSA44.Ring.Carrier.Frontend.Cross
public import GordieHowe.Applications.MLDSA44.Ring.Native.Frontend.Basic

@[expose] public section

/-!
# GordieHowe frontend: the ML-DSA-44 ring carriers, the relation and the extractor

The frontend of the theorem at the realized programs of the ML-DSA-44 ring carriers
(`lib/gordiehowe/examples/rings/mldsa_ring_carrier.h`), generic in the program through the classes
`CarrierHEmbed`, `CarrierAEmbed`, `MldsaCarrierRelation`, `Native.MldsaRingStmt`, `TableSelect`,
`MldsaCarrierFront` and the emulated proof of possession's `Emulated.MldsaEAlgebra` (decided per
carrier). It has the native rings' shape
(`GordieHowe/Applications/MLDSA44/Ring/Native/Frontend/Basic.lean`):

* **The relation** (`rel`): at every ring statement of every message length that passes the
  check (`ringOk`: `64` keys, each with `ExpandA` within the byte budget) and whose carrier rows the
  statement holds (`RowsOf`), the ring relation (`ringRel64`) holds at the witness's position and
  signature (the native rings' witness, `Native.RingW.toWit`). `ringRel_of_rel`: at the program's
  statement of a checked ring statement (`stmtOf`) the relation is the ring relation.
* **The extractor** (`proj`, `extractor`): the position the index bits name
  (`TableSelect.idxOf`) and the signature `(c̃', z, h)` (`sigAt`: H's `h2c.c_tilde.out` read as the
  native program's, A's `z` and hint read as the emulated program's).
* **The events** (`ringEvent`, `ringEps`, `ringEvent_use`, `ringEvent_bound`): the selection's at
  `member.table.gamma` (challenge `0`, `TableSelect.SelBad`, error `5143/|F|`) and the native
  frontend's SampleInBall events (`MLDSA44.SampleView`) at the carrier's challenges `1`,
  `2` (the native challenges `0`, `1` renamed), their probability bounds transported through the
  renaming (`RealizedProgram.probUniform_pullEnv_setChal`).
* **The composition** (`mem_rel_of_source`, `sound_of_views`, `rbr_of_views`), given the native
  frontend's hash view of domain `H`'s core (`MLDSA44.HashViewCore`) and SampleInBall's
  view (`MLDSA44.SampleView`) of the native program: without an event the committed
  spectra are the selected key's transforms and the committed `μ` its `μ` (`spectraOf_row`,
  `muA_eq`), the relation gives `w′ = computeWApprox(Â, c, z, t1)` (`algebra_carrier`), the
  crossing makes H's `μ` the selected key's (`ringCross`) and A's challenge SampleInBall's
  (`cPoly_eq`), domain `H`'s core makes `c̃'` the commitment hash
  (`MLDSA44.cTildeOf_eq_hashCommitment`), domain `A`'s gadgets UseHint, the norm and the
  hint weight (`Emulated.useHint_eq`, `norm_lt`, `hintWeight_le`); so FIPS 204 verification
  accepts (`MLDSA44.verifies_of_parts`, `MLDSA44.verify_of_verifies`).
-/

namespace GordieHowe.MLDSA44.Ring.Carrier

open GordieHowe.Bits GordieHowe.Ring RealizedProgram IOP
open GordieHowe.MLDSA44.Ring.Native (MldsaRingStmt RingW muOf muBitNat)
open scoped NNReal ENNReal

set_option linter.unusedSectionVars false

variable {program : RealizedProgram} [CarrierHEmbed program] [CarrierAEmbed program]
  [MldsaCarrierRelation program] [MldsaRingStmt program] [TableSelect program]
  [MldsaCarrierFront program] {F0 FH : RealizedProgram.FieldInterp}

set_option hygiene false in
local notation "interp" => RealizedProgram.mldsaInterpOf F0 FH

set_option hygiene false in
local notation "nat" => CarrierHEmbed.nat program

set_option hygiene false in
local notation "emu" => CarrierAEmbed.emu program

/-! ## The relation -/

/-- **The relation of the theorem at an ML-DSA-44 ring carrier's realized program**: at every ring
statement `x` of every message length that passes the check (`ringOk`) and whose carrier rows the
statement holds (`RowsOf`: row `j` of `ring.keys` the carrier row of `x`'s key at position `j`,
row `j` of `ring.mu` its `μ` limbs), the ring relation holds at the witness's position and
signature (`ringRel64`: FIPS 204 verification on `x`'s message representative under the key at the
position). -/
def rel : Set (program.Valuation interp × RingW) :=
  {p | ∀ (len : ℕ) (x : RStmt len), ringOk x = true → RowsOf x p.1 →
    (x, p.2.toWit len) ∈ ringRel64 len}

/-- **The relation at the program's statement of a checked ring statement is the ring relation.** -/
theorem ringRel_of_rel {len : ℕ} {x : RStmt len} (hok : ringOk x = true) {w : RingW}
    (h : (stmtOf (program := program) (I := interp) x, w) ∈ rel) :
    (x, w.toWit len) ∈ ringRel64 len :=
  h len x hok (rowsOf_stmtOf x)

/-! ## The extractor -/

/-- **The signature read off the carrier's valuations read as the proofs of possession's**:
`(c̃', z, h)`, `c̃'` the bytes of H's `h2c.c_tilde.out` (the native program's), `z` and the hint
read from domain `A` (the emulated program's, `MLDSA44.PoP.Native.decodeH`). -/
def sigAt (nrd : (nat).Valuation interp) (ard : (emu).Valuation interp) : Sig :=
  ⟨MLDSA44.cTildeOf nrd, Emulated.zOf ard,
    MLDSA44.PoP.Native.decodeH (Emulated.hVals ard)⟩

/-- **The signature depends only on `c̃'`, `z` and `h`** (native value `457`, emulated values `58`,
`59`). -/
theorem sigAt_congr {nrd nrd' : (nat).Valuation interp} {ard ard' : (emu).Valuation interp}
    (h457 : nrd 457 = nrd' 457) (h58 : ard 58 = ard' 58) (h59 : ard 59 = ard' 59) :
    sigAt nrd ard = sigAt nrd' ard' := by
  unfold sigAt MLDSA44.cTildeOf MLDSA44.cTildeBits
    Emulated.zOf Emulated.zVals Emulated.hVals
  simp only [RealizedProgram.evalE_leaf, h457, h58, h59]

/-- **The environment of a statement and a committed assignment** with every challenge and late
value `0`: what the extractor reads the committed values from. -/
def commitEnv (x : program.Valuation interp) (a : program.Assignment interp) :
    program.Env interp :=
  ⟨x, a, fun _ _ => 0, fun _ _ => 0⟩

/-- **The witness extracted from a statement and a committed assignment**: the position the index
bits name (`TableSelect.idxOf`) and the signature (`sigAt`) read in the environment of the
statement and the committed assignment (`commitEnv`) read as the native and the emulated
programs'.

Running time: `6` index bits, `256` bits of `c̃'`, `2 · 1024` readings of `z` and `h` in domain
`A`, `1024` centred readings of domain `A`'s field, polynomial in the program's size. This running
time is argued here, not proved in Lean. -/
-- spec-side
def proj (x : program.Valuation interp) (a : program.Assignment interp) : RingW :=
  ⟨TableSelect.idxOf 0 (commitEnv x a),
    sigAt ((nat).reader (pullH (commitEnv x a))) ((emu).reader (pullA (commitEnv x a)))⟩

/-- **The extractor of `Π_P₀`** for an ML-DSA-44 ring carrier
(`RealizedProgram.sourceExtractor` at `proj`).

Running time: one read of the transcript's first round and one call of `proj` (polynomial,
`proj`'s paragraph). This running time is argued here, not proved in Lean. -/
def extractor : Extractor (program.sourceSpec interp) (program.Valuation interp) RingW :=
  program.sourceExtractor interp proj

/-- **The extracted position** is the environment's. -/
theorem proj_idx (e : program.Env interp) :
    (proj e.stmt e.asg).idx = TableSelect.idxOf 0 e := by
  unfold proj TableSelect.idxOf
  rw [TableSelect.bitsOf_congr (e := commitEnv e.stmt e.asg) (e' := e) rfl]

/-- The carrier values the extractor reads read alike in an environment and in the environment of
its statement and committed assignment. -/
theorem reader_commitEnv (e : program.Env interp) {v : ℕ} (hv : v ∈ [410, 60, 61]) :
    program.reader (commitEnv e.stmt e.asg) v = program.reader e v :=
  RealizedProgram.reader_eq_of_nodeReads_nil (MldsaCarrierFront.projReads v hv) rfl rfl

/-- **The extracted signature** is the environment's. -/
theorem proj_sig (e : program.Env interp) :
    (proj e.stmt e.asg).sig = sigAt ((nat).reader (pullH e)) ((emu).reader (pullA e)) := by
  refine sigAt_congr ?_ ?_ ?_ <;> funext i
  · rw [readerH_pull _ (by decide), readerH_pull _ (by decide), σH_val457,
      reader_commitEnv e (by simp)]
  · rw [readerA_pull _ (by decide), readerA_pull _ (by decide), σA_vals.1,
      reader_commitEnv e (by simp)]
  · rw [readerA_pull _ (by decide), readerA_pull _ (by decide), σA_vals.2.1,
      reader_commitEnv e (by simp)]

/-! ## The events -/

variable [MLDSA44.AField F0] [MLDSA44.HField FH]
variable (sv : MLDSA44.SampleView nat F0 FH)

/-- **The source program's events**: the selection's at `member.table.gamma` (challenge `0`) and
the native SampleInBall events at the carrier's challenge `j + 1`, read in the environment read as
the native program's. -/
def ringEvent (j : ℕ) (e : program.Env interp) : Prop :=
  TableSelect.SelBad 0 j e ∨ ∃ j', j = j' + 1 ∧ sv.event j' (pullH e)

/-- **The events' errors**: `5143/|F|` at `member.table.gamma`, the native error of challenge
`j` at the carrier's challenge `j + 1`. -/
noncomputable def ringEps (j : ℕ) : ℝ≥0 :=
  if j = 0 then ((5143 : ℕ) : ℝ≥0) / Fintype.card (interp 0).K else sv.eps (j - 1)

/-- **The challenge-use rule** (`RealizedProgram.ChallengeUseAt`): the selection's
(`TableSelect.selBad_use`), and the native one's through the renaming (`eqUpToH_pull`). -/
theorem ringEvent_use : RealizedProgram.ChallengeUseAt program interp (ringEvent sv) := by
  intro j e e' h
  unfold ringEvent
  refine or_congr (TableSelect.selBad_use (f := 0) j h) ⟨?_, ?_⟩ <;> rintro ⟨j', rfl, hj'⟩ <;>
    refine ⟨j', rfl, ?_⟩
  · exact (sv.use j' (eqUpToH_pull (j := j') h)).1 hj'
  · exact (sv.use j' (eqUpToH_pull (j := j') h)).2 hj'

/-- The table's width is `5144`. -/
theorem W_eq : TableSelect.W program = 5144 := by
  unfold TableSelect.W
  rw [MldsaCarrierFront.shape.2.2.2.2.2.2.1, carrierMap_width]

/-- **The events' probabilities** (`RealizedProgram.rbr_of_events`' `hbound`): at most
`5143/|F|` at `member.table.gamma` (`TableSelect.selBad_bound`, Schwartz–Zippel) and the native
error at the carrier's challenge `j + 1` (`SampleView.bound`, through
`RealizedProgram.probUniform_pullEnv_setChal`). -/
theorem ringEvent_bound : ∀ j, program.IsSourceChal j → ∀ e : program.Env interp,
    Pr[c ← program.ChalVal interp j : ringEvent sv j (e.setChal j c)] ≤ (ringEps sv j : ℝ≥0∞) := by
  intro j hj e
  have hchal := (MldsaCarrierFront.shape (program := program)).2.1
  rcases j with _ | j
  · have hset : ∀ c, ringEvent sv 0 (e.setChal 0 c) ↔ TableSelect.SelBad 0 0 (e.setChal 0 c) :=
      fun c => by
        unfold ringEvent
        refine ⟨fun h => h.resolve_right ?_, .inl⟩
        rintro ⟨j', hj', -⟩
        omega
    simp only [hset]
    have h := TableSelect.selBad_bound (f := 0) domainField_shape e
    rw [hchal] at h
    unfold ringEps
    rw [if_pos rfl]
    rw [W_eq] at h
    exact h
  · have hnat := (MldsaCarrierFront.chalIff j).1 hj
    have hset : ∀ c, ringEvent sv (j + 1) (e.setChal (j + 1) c) ↔
        sv.event j (pullH (e.setChal (j + 1) c)) := fun c => by
      unfold ringEvent TableSelect.SelBad
      rw [hchal]
      constructor
      · rintro (⟨h, -⟩ | ⟨j', hj', h⟩)
        · omega
        · obtain rfl : j' = j := by omega
          exact h
      · exact fun h => .inr ⟨j, rfl, h⟩
    simp only [hset]
    unfold ringEps
    rw [if_neg (Nat.succ_ne_zero j), Nat.add_sub_cancel]
    obtain ⟨hsz', hsm', hsz, hsm, hf⟩ := MldsaCarrierFront.chalShape j hnat
    refine le_of_eq_of_le ?_ (sv.bound j hnat (pullH e))
    exact RealizedProgram.probUniform_pullEnv_setChal (σ := σH) (V := hV) hsz' hsm' hsz hsm hf
      (fun j' h => Nat.succ_injective h) (sv.event j) e

/-! ## The composition -/

/-- **H's `μ` bits are the selected key's `μ`** where the source program holds and the selection's
event did not occur, at a statement holding a ring's carrier rows (`muA_eq`, through the
crossing). -/
theorem muH_eq {e : program.Env interp} (hs : program.SourceSatAt e)
    (hno : ¬ TableSelect.SelBad 0 0 e) {len : ℕ} {x : RStmt len} (hrows : RowsOf x e.stmt)
    (hcr : RingCrossAt (program.reader e)) {t : ℕ} (ht : t < 512) :
    program.evalE (program.reader e) 1 (.leaf 71) t =
      if muBitNat (muOf (x.keyAt (TableSelect.idxOf 0 e)) x.msg) t = 1 then 1 else 0 := by
  have h := hcr.mu t ht
  rw [muA_eq hs hno hrows ht] at h
  split_ifs at h ⊢ with hb
  · have h1 : (interp 0).toNat ((1 : ℕ) : (interp 0).K) = 1 :=
      MLDSA44.AField.toNat_natCast (F0 := F0) 1 (by norm_num [pGold])
    rw [show (1 : (interp 0).K) = ((1 : ℕ) : (interp 0).K) from Nat.cast_one.symm, h1] at h
    have := MLDSA44.HField.eq_of_toNat_lt_two (FH := FH) h.symm (by norm_num)
    simpa using this
  · have h0 : (interp 0).toNat ((0 : ℕ) : (interp 0).K) = 0 :=
      MLDSA44.AField.toNat_natCast (F0 := F0) 0 (by norm_num [pGold])
    rw [show (0 : (interp 0).K) = ((0 : ℕ) : (interp 0).K) from Nat.cast_zero.symm, h0] at h
    have := MLDSA44.HField.eq_of_toNat_lt_two (FH := FH) h.symm (by norm_num)
    simpa using this

/-- **The native `μ` bytes are the selected key's `μ`** in the environment read as the native
program's. -/
theorem inputBytes_mu {e : program.Env interp} (hs : program.SourceSatAt e)
    (hno : ¬ TableSelect.SelBad 0 0 e) {len : ℕ} {x : RStmt len} (hrows : RowsOf x e.stmt)
    (hcr : RingCrossAt (program.reader e)) :
    Shake256.inputBytes (Falcon512.HashCircuit.byteWires
        (MLDSA44.muBits ((nat).reader (pullH e)))) =
      (muOf (x.keyAt (TableSelect.idxOf 0 e)) x.msg).toList.map UInt8.toNat := by
  set mu := muOf (x.keyAt (TableSelect.idxOf 0 e)) x.msg
  have hbits : MLDSA44.muBits ((nat).reader (pullH e)) =
      Falcon512.HashCircuit.wiresOfByteVec fun i => (mu.get i).toNat := by
    funext t
    rw [muBits_pull, muH_eq hs hno hrows hcr t.isLt]
    unfold Falcon512.HashCircuit.wiresOfByteVec Bits.constBit muBitNat
    rw [dif_pos t.isLt]
  rw [hbits, Shake256.inputBytes]
  apply List.ext_getElem (by simp)
  intro j h₁ h₂
  simp only [List.getElem_ofFn, List.getElem_map, Vector.getElem_toList]
  rw [Falcon512.HashCircuit.natOfBits_byteWires_wiresOfByteVec (fun i => UInt8.toNat_lt _)]
  simp only [Vector.get_eq_getElem]

variable [Emulated.MldsaEAlgebra emu]
  [MLDSA44.MldsaHHash (Emulated.MldsaEmbed.nat emu)]
  [MLDSA44.MldsaHSample (Emulated.MldsaEmbed.nat emu)]
  [MLDSA44.MldsaHConsts (Emulated.MldsaEmbed.nat emu) FH]

/-- **The frontend's composition, the views as hypotheses**: where the source program holds and
no event occurred, the relation holds at the statement and the extracted witness, given the
native frontend's hash view of domain `H`'s core and SampleInBall's view. At a checked ring
statement whose carrier rows the statement holds: the committed spectra are the selected key's
transforms and the committed `μ` its `μ`, so the relation gives `w′ = computeWApprox(Â, c, z, t1)`
at the key; SampleInBall's stream is `SHAKE256(c̃')` and its fixed-stream `SampleInBall` H's
decoded challenge, which the crossing makes A's challenge polynomial; `c̃'` is the commitment hash
of the key's `μ` and A's `w1`; UseHint, the norm and the hint weight hold; so FIPS 204 verification
accepts. -/
theorem mem_rel_of_source (hv : MLDSA44.HashViewCore nat F0 FH)
    {e : program.Env interp} (hs : program.SourceSatAt e)
    (hno : ∀ j, program.IsSourceChal j → ¬ ringEvent sv j e) :
    (e.stmt, proj e.stmt e.asg) ∈ rel := by
  intro len x hok hrows
  have hAF : MLDSA44.AField (interp 0) := inferInstanceAs (MLDSA44.AField F0)
  have hsel : ¬ TableSelect.SelBad 0 0 e := fun h => hno 0 MldsaCarrierFront.chal0 (.inl h)
  have hnoN : ∀ j, (nat).IsSourceChal j → ¬ sv.event j (pullH e) := fun j hj h =>
    hno (j + 1) ((MldsaCarrierFront.chalIff j).2 hj) (.inr ⟨j, rfl, h⟩)
  have hcore := hSatCore hs
  have hA := eaSat hs
  have hsam := sv.sound (pullH e) hcore hnoN
  have hcr := ringCross hs (fun k hk => by
      have := hsam.sup_lt ⟨k, hk⟩
      rwa [supH_pull e ⟨k, hk⟩] at this) (fun k hk => by
      have := hsam.sgn_lt ⟨k, hk⟩
      rwa [sgnH_pull e ⟨k, hk⟩] at this)
  have hadm := ringOk_iff.1 hok
  have hidx := idxOf_lt64 hs
  have hlt : TableSelect.idxOf 0 e < x.ring.1.length := by rw [hadm.1]; exact hidx
  have hkey : x.keyAt (TableSelect.idxOf 0 e) = x.ring.1[TableSelect.idxOf 0 e]'hlt :=
    RingStmt.keyAt_eq hlt
  have hexp := hadm.2 _ (List.getElem_mem hlt)
  have hS := spectraOf_row hs hsel hrows (by rw [hkey]; exact hexp)
  have hmu := inputBytes_mu hs hsel hrows hcr
  rw [hkey] at hS hmu
  set pk := x.ring.1[TableSelect.idxOf 0 e]'hlt
  set rd := program.reader e
  set nrd := (nat).reader (pullH e)
  set ard := (emu).reader (pullA e)
  have hW : wOf rd = _root_.MLDSA.computeWApprox _root_.MLDSA.mldsa44 MLDSA44.Native.Rows.prims
      (nttOps := _root_.MLDSA.Concrete.concreteNTTRingOps) (MLDSA44.Native.Rows.aHat pk)
      (cPoly rd) (zOf rd) pk.t1 :=
    algebra_carrier hs hS
  have hb : AllBool (Emulated.w1ABits ard) := fun t => Emulated.w1Bool hA t.isLt
  have hw1 : Shake256.inputBytes (Falcon512.HashCircuit.byteWires
      (MLDSA44.w1HBits nrd)) =
      (_root_.MLDSA.Concrete.w1Encode _root_.MLDSA.mldsa44
        (MLDSA44.PoP.Native.decodeW1 (Emulated.w1ABits ard))).map UInt8.toNat := by
    have hlen :=
      MLDSA44.w1Encode_length_mldsa44 (MLDSA44.PoP.Native.decodeW1 (Emulated.w1ABits ard))
    apply List.ext_getElem (by rw [Shake256.inputBytes, List.length_ofFn, List.length_map, hlen])
    intro j h₁ h₂
    simp only [Shake256.inputBytes, List.getElem_ofFn, List.getElem_map]
    rw [MLDSA44.HashCircuit.natOfBits_byteWires_w1Encode (w1HBits_eq hcr hb),
      List.getD_eq_getElem]
  have hcommit := MLDSA44.cTildeOf_eq_hashCommitment hv hcore hmu hw1
  have hcb : ∀ k s, cBits rd k s = 0 ∨ cBits rd k s = 1 := fun k s => by
    have hk' : (k : ℕ) < 256 := k.isLt
    have hs' : (s : ℕ) < 2 := s.isLt
    exact cBit_bool hs (by omega)
  have hver : MLDSA44.Verifies pk x.msg.toList (sigAt nrd ard) := by
    refine MLDSA44.verifies_of_parts (C := 264) (c := MLDSA44.chalH nrd)
      (W := Emulated.wOf ard) (by decide) hexp ?_ ?_ ?_ hcommit (Emulated.norm_lt hA) ?_
    · rw [← MLDSA44.sibStream_eq_core hv hcore]
      exact hsam.challenge
    · rw [← cPoly_eq hcr hcb, zOf_pullA, wOf_pullA, hW]
    · exact MLDSA44.PoP.Compose.useHintVec_eq_of_get (fun i k => (MLDSA44.coeff_apply _ k).symm)
        fun i k => by
          rw [MLDSA44.coeff_apply, MLDSA44.PoP.Native.decodeW1_get]
          erw [MLDSA44.PoP.Native.decodeH_get, Emulated.useHint_eq hA i k]
          rfl
    · have hwt := MLDSA44.hintWeightVec_ofFn fun i k =>
        MLDSA44.NativeAlgebraCircuit.decodeHint (Emulated.hVals ard) i k
      exact hwt.trans_le (Emulated.hintWeight_le hA)
  change ringAdm x.ring.1 ∧ RingRel bindSelf x ⟨(proj e.stmt e.asg).idx, (proj e.stmt e.asg).sig⟩
  rw [proj_idx, proj_sig]
  exact ⟨hadm, ⟨hlt, rfl, MLDSA44.verify_of_verifies hver⟩⟩

/-- **The relation from the source program without an event** (`RealizedProgram.rbr_of_events`'
`hsound`), given the views. -/
theorem sound_of_views (hv : MLDSA44.HashViewCore nat F0 FH) :
    ∀ e : program.Env interp, program.StatementOk interp e.stmt → program.SourceSatAt e →
      (∀ j, program.IsSourceChal j → ¬ ringEvent sv j e) → (e.stmt, proj e.stmt e.asg) ∈ rel :=
  fun _ _ hs hno => mem_rel_of_source sv hv hs hno

/-- **Round-by-round knowledge soundness of `Π_P₀` for an ML-DSA-44 ring carrier**
(`RealizedProgram.rbr_of_events`), given the native frontend's hash view of domain `H`'s core
(`HashViewCore`, the Keccak trace's instance) and SampleInBall's view (`SampleView`) of the
native program: the relation `rel`, the extractor `extractor`, the errors `5143/|F|` at
`member.table.gamma` and SampleInBall's at the carrier's challenges `1`, `2` (`ringEps`). -/
theorem rbr_of_views (hv : MLDSA44.HashViewCore nat F0 FH) :
    rbrKnowledgeSoundness rel (program.sourceVerifier interp) extractor
      (program.eventState interp rel proj (ringEvent sv) (ringEvent_use sv) (sound_of_views sv hv))
      (program.roundError interp (ringEps sv)) :=
  program.rbr_of_events interp rel proj (ringEvent sv) (ringEps sv) (ringEvent_use sv)
    (ringEvent_bound sv) (sound_of_views sv hv)

end GordieHowe.MLDSA44.Ring.Carrier
