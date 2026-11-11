-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweCerts.Applications.MLDSA44.Ring.Native.Frontend.Select
public import GordieHoweCerts.Applications.MLDSA44.Ring.Native.Frontend.Cross
public import GordieHowe.Applications.MLDSA44.Ring.Native.Frontend.Verify
public import GordieHowe.Language.RealizedProgram.EmbedChal

@[expose] public section

/-!
# GordieHowe frontend: the native ML-DSA-44 ring programs, the relation and the extractor

The frontend of the theorem at the realized programs of the native ML-DSA-44 rings
(`lib/gordiehowe/examples/rings/mldsa_ring_native.h`), generic in the program through the classes
`MldsaRingEmbed`, `MldsaRingRelation`, `MldsaRingStmt`, `TableSelect`, `MldsaRingFront` and the
native proof of possession's `MldsaAAlgebra` (decided per program):

* **The relation** (`rel`): at every ring statement of every message length that passes the
  check (`ringOk`: `64` keys, each with `ExpandA` within the byte budget) and whose rows the
  statement holds (`RowsOf`), the ring relation (`ringRel64`) holds at the witness's position and
  signature (`RingW.toWit`). `ringRel_of_rel`: at the program's statement of a checked ring
  statement (`stmtOf`) the relation is the ring relation.
* **The extractor** (`proj`, `extractor`): the position the index bits name
  (`TableSelect.idxOf`) and the signature `(c̃', z, h)` read in the environment read as the native
  program's (`sigAt`: H's `h2c.c_tilde.out`, A's `z` and hint).
* **The events** (`ringEvent`, `ringEps`, `ringEvent_use`, `ringEvent_bound`): the selection's at
  `member.table.gamma` (challenge `0`, `TableSelect.SelBad`, error `5143/|F|`) and the native
  frontend's SampleInBall events (`MLDSA44.SampleView`) at the ring's challenges `1`, `2`
  (the native challenges `0`, `1` renamed), their probability bounds transported through the
  renaming (`RealizedProgram.probUniform_pullEnv_setChal`).
* **The composition** (`mem_rel_of_source`, `sound_of_views`, `rbr_of_views`), given the native
  frontend's hash view of domain `H`'s core (`MLDSA44.HashViewCore`) and SampleInBall's
  view (`MLDSA44.SampleView`) of the native program: without an event the record is the
  selected key's row and `μ` (`aHatVals_eq`, `t1HatVals_eq`, `muA_eq`), the algebra gives
  `w' = computeWApprox(Â, c, z, t1)` (`algebra_eq_of_cast`), the crossing makes H's `μ` the
  selected key's (`ringCross`) and A's challenge SampleInBall's (`crossAt_pull`,
  `MLDSA44.cPolyA_eq`), domain `H`'s core makes `c̃'` the commitment hash
  (`MLDSA44.cTildeOf_eq_hashCommitment`), domain `A`'s gadgets UseHint, the norm and the
  hint weight (`Native.useHint_eq`, `norm_lt`, `hintWeight_le`); so FIPS 204
  verification accepts (`MLDSA44.verifies_of_parts`, `MLDSA44.verify_of_verifies`).
-/

namespace GordieHowe.MLDSA44.Ring.Native

open GordieHowe.Bits GordieHowe.Ring RealizedProgram IOP
open scoped NNReal ENNReal

/-- **The witness of the native ML-DSA-44 ring programs**: the signer's position and the
signature `(c̃, z, h)`. -/
structure RingW where
  /-- The signer's position. -/
  idx : ℕ
  /-- The signature. -/
  sig : Sig

/-- **A witness**: position `0` and the zero signature (the IOP's witness maps need an
inhabited witness type). -/
instance : Inhabited RingW := ⟨⟨0, ⟨Vector.replicate _ 0, 0, Vector.replicate _ default⟩⟩⟩

/-- **The ring witness of a witness** at `msgLen`-byte message representatives. -/
def RingW.toWit (msgLen : ℕ) (w : RingW) : RingWit (scheme msgLen) := ⟨w.idx, w.sig⟩

set_option linter.unusedSectionVars false

variable {program : RealizedProgram} [MldsaRingEmbed program] [MldsaRingRelation program]
  [MldsaRingStmt program] [TableSelect program] [MldsaRingFront program]
  [MLDSA44.Native.MldsaAAlgebra (MldsaRingEmbed.nat program)]
  {F0 FH : RealizedProgram.FieldInterp} [QField F0] [HField FH]

set_option hygiene false in
local notation "interp" => RealizedProgram.mldsaInterpOf F0 FH

set_option hygiene false in
local notation "nat" => MldsaRingEmbed.nat program

set_option hygiene false in
local notation "σ" => MldsaRingEmbed.σ program

set_option hygiene false in
local notation "ringV" => MldsaRingEmbed.V program

set_option hygiene false in
local notation "ringR" => MldsaRingEmbed.R program

set_option hygiene false in
local notation "predMap" => MldsaRingEmbed.pred program

/-! ## The relation -/

/-- **The relation of the theorem at a native ML-DSA-44 ring program's realized program**: at
every ring statement `x` of every message length that passes the check (`ringOk`) and whose rows
the statement holds (`RowsOf`: row `j` of `ring.keys` the row of `x`'s key at position `j`, row
`j` of `ring.mu` its `μ` limbs), the ring relation holds at the witness's position and signature
(`ringRel64`: FIPS 204 verification on `x`'s message representative under the key at the
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

/-- **The signature read off a valuation of the native program**: `(c̃', z, h)`, `c̃'` the bytes
of H's `h2c.c_tilde.out`, `z` and the hint read from domain `A`
(`MLDSA44.PoP.Native.decodeH`). -/
def sigAt (rd : (nat).Valuation interp) : Sig :=
  ⟨MLDSA44.cTildeOf rd, MLDSA44.zOf rd,
    MLDSA44.PoP.Native.decodeH (MLDSA44.hVals rd)⟩

/-- **The signature depends only on `c̃'`, `z` and `h`** (native values `457`, `57`, `58`). -/
theorem sigAt_congr {rd rd' : (nat).Valuation interp} (h457 : rd 457 = rd' 457)
    (h57 : rd 57 = rd' 57) (h58 : rd 58 = rd' 58) : sigAt rd = sigAt rd' := by
  unfold sigAt MLDSA44.cTildeOf MLDSA44.cTildeBits
    MLDSA44.zOf MLDSA44.zVals MLDSA44.hVals
  simp only [RealizedProgram.evalE_leaf, h457, h57, h58]

/-- **The environment of a statement and a committed assignment** with every challenge and late
value `0`: what the extractor reads the committed values from. -/
def commitEnv (x : program.Valuation interp) (a : program.Assignment interp) :
    program.Env interp :=
  ⟨x, a, fun _ _ => 0, fun _ _ => 0⟩

/-- **The witness extracted from a statement and a committed assignment**: the position the index
bits name (`TableSelect.idxOf`) and the signature (`sigAt`) read in the environment of the
statement and the committed assignment (`commitEnv`) read as the native program's.

Running time: `6` index bits, `256` bits of `c̃'`, `2 · 1024` readings of `z` and `h` in domain
`A`, `1024` coefficients lifted below `q` (`NativeAlgebraCircuit.coeffRep`), polynomial in the
program's size. This running time is argued here, not proved in Lean. -/
-- spec-side
def proj (x : program.Valuation interp) (a : program.Assignment interp) : RingW :=
  ⟨TableSelect.idxOf 0 (commitEnv x a), sigAt ((nat).reader (pull (commitEnv x a)))⟩

/-- **The extractor of `Π_P₀`** for a native ML-DSA-44 ring program
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

/-- The values the extractor reads, renamed, read alike in an environment and in the environment
of its statement and committed assignment. -/
theorem reader_pull_commitEnv (e : program.Env interp) {v : ℕ} (hv : v ∈ [457, 57, 58]) :
    (nat).reader (pull (commitEnv e.stmt e.asg)) v = (nat).reader (pull e) v := by
  have hvV : v ∈ ringV :=
    MldsaRingEmbed.readV v ((by decide : ∀ v ∈ [457, 57, 58], v ∈ readVals) v hv)
  funext i
  rw [reader_pull _ hvV, reader_pull _ hvV,
    RealizedProgram.reader_eq_of_nodeReads_nil (MldsaRingFront.projReads _ (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv ⊢
      rcases hv with rfl | rfl | rfl <;> simp)) (e := commitEnv e.stmt e.asg) (e' := e) rfl rfl]

/-- **The extracted signature** is the environment's. -/
theorem proj_sig (e : program.Env interp) :
    (proj e.stmt e.asg).sig = sigAt ((nat).reader (pull e)) :=
  sigAt_congr (reader_pull_commitEnv e (by simp)) (reader_pull_commitEnv e (by simp))
    (reader_pull_commitEnv e (by simp))

/-! ## The events -/

variable (sv : MLDSA44.SampleView nat F0 FH)

/-- **The source program's events**: the selection's at `member.table.gamma` (challenge `0`), the
signature relation's at `signature.r` (`relEvent`: some row's nonzero polynomial vanishes at `r`)
and the native SampleInBall events at the ring's challenge `j + sibOff`, read in the environment
read as the native program's. -/
def ringEvent (j : ℕ) (e : program.Env interp) : Prop :=
  TableSelect.SelBad 0 j e ∨ (j = MldsaRandomPoint.rChal program ∧ (relEvent e).BadAt (rOf e)) ∨
    ∃ j', j = j' + MldsaRingFront.sibOff program ∧ sv.event j' (pull e)

/-- **The events' errors**: `5143/|F_q^m|` at `member.table.gamma`, `2040/|F_q^m|` at
`signature.r`, the native error of challenge `j` at the ring's challenge `j + sibOff`. -/
noncomputable def ringEps (j : ℕ) : ℝ≥0 :=
  if j = 0 then ((5143 : ℕ) : ℝ≥0) / Fintype.card (interp 0).K
  else if j = MldsaRandomPoint.rChal program then ((2040 : ℕ) : ℝ≥0) / Fintype.card (interp 0).K
  else sv.eps (j - MldsaRingFront.sibOff program)

omit [QField F0] in
theorem relEvent_congr {e e' : program.Env interp} (hs : e.stmt = e'.stmt) (ha : e.asg = e'.asg) :
    relEvent e = relEvent e' := by
  have hrd : ∀ v ∈ [MldsaRandomPoint.w program, MldsaRandomPoint.q program,
      MldsaRandomPoint.t1 program, MldsaRandomPoint.aHat program, MldsaRandomPoint.z program,
      MldsaRandomPoint.c program], ∀ t,
      program.evalE (program.reader e) 0 (.leaf v) t =
        program.evalE (program.reader e') 0 (.leaf v) t := fun v hv t => by
    rw [RealizedProgram.evalE_leaf, RealizedProgram.evalE_leaf,
      RealizedProgram.reader_eq_of_nodeReads_nil (MldsaRingFront.relReads v hv) hs ha]
  refine relEvent_congr_of (fun i t ht => ?_) (fun v hv => hrd v ?_)
  · rw [eRow_eq e i ht, eRow_eq e' i ht]
    exact hrd _ (by simp) _
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hv ⊢
    tauto

/-- **The challenge-use rule** (`RealizedProgram.ChallengeUseAt`): the selection's
(`TableSelect.selBad_use`), the relation's (its polynomial reads the committed values, its
challenge `r`), and the native one's through the renaming (`eqUpTo_pull`). -/
theorem ringEvent_use : RealizedProgram.ChallengeUseAt program interp (ringEvent sv) := by
  intro j e e' h
  unfold ringEvent
  refine or_congr (TableSelect.selBad_use (f := 0) j h) (or_congr ?_ ⟨?_, ?_⟩)
  · constructor <;> rintro ⟨rfl, hb⟩ <;> refine ⟨rfl, ?_⟩
    · have hr : rOf e = rOf e' := by unfold rOf; rw [h.chal _ (Or.inr ⟨rfl, le_refl _⟩)]
      rwa [← relEvent_congr h.stmt h.asg, ← hr]
    · have hr : rOf e = rOf e' := by unfold rOf; rw [h.chal _ (Or.inr ⟨rfl, le_refl _⟩)]
      rwa [relEvent_congr h.stmt h.asg, hr]
  all_goals rintro ⟨j', rfl, hj'⟩; refine ⟨j', rfl, ?_⟩
  · have h' : RealizedProgram.Env.EqUpTo ((σ).chal j') e e' := by
      rw [MldsaRingFront.chalSucc]; exact h
    exact (sv.use j' (eqUpTo_pull h')).1 hj'
  · have h' : RealizedProgram.Env.EqUpTo ((σ).chal j') e e' := by
      rw [MldsaRingFront.chalSucc]; exact h
    exact (sv.use j' (eqUpTo_pull h')).2 hj'

/-- The table's width is `5144`. -/
theorem W_eq : TableSelect.W program = 5144 := by
  unfold TableSelect.W
  rw [MldsaRingFront.shape.2.2.2.2.2.2.1, nativeMap_facts.1]

omit [QField F0] in
/-- **The events' probabilities** (`RealizedProgram.rbr_of_events`' `hbound`): at most
`5143/|F_q^m|` at `member.table.gamma` (`TableSelect.selBad_bound`, Schwartz–Zippel), `2040/|F_q^m|`
at `signature.r` (`RealizedProgram.probUniform_badAt_setChal_le`) and the native error at the
ring's challenge `j + sibOff` (`SampleView.bound`, through
`RealizedProgram.probUniform_pullEnv_setChal`). -/
theorem ringEvent_bound : ∀ j, program.IsSourceChal j → ∀ e : program.Env interp,
    Pr[c ← program.ChalVal interp j : ringEvent sv j (e.setChal j c)] ≤ (ringEps sv j : ℝ≥0∞) := by
  intro j hj e
  have hchal := (MldsaRingFront.shape (program := program)).2.1
  obtain ⟨-, hr0, hrlt⟩ := MldsaRingFront.chalR (program := program)
  rcases MldsaRingFront.chalCases j hj with rfl | rfl | ⟨j, rfl⟩
  · have hset : ∀ c, ringEvent sv 0 (e.setChal 0 c) ↔ TableSelect.SelBad 0 0 (e.setChal 0 c) :=
      fun c => by
        unfold ringEvent
        refine ⟨fun h => ?_, .inl⟩
        rcases h with h | ⟨h, -⟩ | ⟨j', hj', -⟩
        · exact h
        · omega
        · omega
    simp only [hset]
    have h := TableSelect.selBad_bound (f := 0) domainField_shape e
    rw [hchal] at h
    unfold ringEps
    rw [if_pos rfl]
    rw [W_eq] at h
    exact h
  · have hset : ∀ c, ringEvent sv (MldsaRandomPoint.rChal program)
        (e.setChal (MldsaRandomPoint.rChal program) c) ↔
        (relEvent e).BadAt (RealizedProgram.castElt
          ((e.setChal (MldsaRandomPoint.rChal program) c).chal (MldsaRandomPoint.rChal program) 0)) :=
      fun c => by
        unfold ringEvent TableSelect.SelBad
        rw [hchal, relEvent_congr (e := e.setChal _ c) (e' := e) rfl rfl]
        constructor
        · rintro (⟨h, -⟩ | ⟨-, h⟩ | ⟨j', hj', -⟩)
          · omega
          · exact h
          · omega
        · exact fun h => .inr (.inl ⟨rfl, h⟩)
    simp only [hset]
    unfold ringEps
    rw [if_neg hr0, if_pos rfl]
    obtain ⟨hsz, hsm⟩ := MldsaRandomPoint.chalR (program := program)
    refine (RealizedProgram.probUniform_badAt_setChal_le hsz hsm
      (MldsaRandomPoint.rPow (program := program)).chalField (relEvent e) e).trans ?_
    simp [relEvent, ChallengeEvent.prodNonzero]
  · have hnat := (MldsaRingFront.chalIff j).1 hj
    have hset : ∀ c, ringEvent sv (j + MldsaRingFront.sibOff program)
        (e.setChal (j + MldsaRingFront.sibOff program) c) ↔
        sv.event j (pull (e.setChal (j + MldsaRingFront.sibOff program) c)) := fun c => by
      unfold ringEvent TableSelect.SelBad
      rw [hchal]
      constructor
      · rintro (⟨h, -⟩ | ⟨h, -⟩ | ⟨j', hj', h⟩)
        · omega
        · omega
        · obtain rfl : j' = j := by omega
          exact h
      · exact fun h => .inr (.inr ⟨j, rfl, h⟩)
    simp only [hset]
    unfold ringEps
    rw [if_neg (by omega), if_neg (by omega), Nat.add_sub_cancel]
    obtain ⟨hsz', hsm', hsz, hsm, hf⟩ := MldsaRingFront.chalShape j hnat
    rw [← MldsaRingFront.chalSucc (program := program) j] at hsz' hsm' hf ⊢
    rw [RealizedProgram.probUniform_pullEnv_setChal hsz' hsm' hsz hsm hf
      (fun j' h => by rw [MldsaRingFront.chalSucc, MldsaRingFront.chalSucc] at h; omega)]
    exact sv.bound j hnat (pull e)

/-! ## The composition -/

/-- **H's `μ` bits are the selected key's `μ`** where the source program holds and the selection's
event did not occur, at a statement holding a ring's rows (`muA_eq`, through the crossing). -/
theorem muH_eq {e : program.Env interp} (hs : program.SourceSatAt e)
    (hno : ¬ TableSelect.SelBad 0 0 e) {len : ℕ} {x : RStmt len} (hrows : RowsOf x e.stmt)
    (hcr : RingCrossAt (program.reader e)) {t : ℕ} (ht : t < 512) :
    program.evalE (program.reader e) 1 (.leaf (MldsaRingFront.muH program)) t =
      if muBitNat (muOf (x.keyAt (TableSelect.idxOf 0 e)) x.msg) t = 1 then 1 else 0 := by
  have h := hcr.mu t ht
  rw [muA_eq hs hno hrows ht] at h
  split_ifs at h ⊢ with hb
  · have h1 : (interp 0).toNat ((1 : ℕ) : (interp 0).K) = 1 :=
      QField.toNat_natCast (F0 := F0) (by norm_num)
    rw [show (1 : (interp 0).K) = ((1 : ℕ) : (interp 0).K) from Nat.cast_one.symm, h1] at h
    have := HField.eq_of_toNat_lt_two (FH := FH) h.symm (by norm_num)
    simpa using this
  · have h0 : (interp 0).toNat ((0 : ℕ) : (interp 0).K) = 0 :=
      QField.toNat_natCast (F0 := F0) (by norm_num)
    rw [show (0 : (interp 0).K) = ((0 : ℕ) : (interp 0).K) from Nat.cast_zero.symm, h0] at h
    have := HField.eq_of_toNat_lt_two (FH := FH) h.symm (by norm_num)
    simpa using this

/-- **The native `μ` bytes are the selected key's `μ`** in the environment read as the native
program's. -/
theorem inputBytes_mu {e : program.Env interp} (hs : program.SourceSatAt e)
    (hno : ¬ TableSelect.SelBad 0 0 e) {len : ℕ} {x : RStmt len} (hrows : RowsOf x e.stmt)
    (hcr : RingCrossAt (program.reader e)) :
    Shake256.inputBytes (Falcon512.HashCircuit.byteWires
        (MLDSA44.muBits ((nat).reader (pull e)))) =
      (muOf (x.keyAt (TableSelect.idxOf 0 e)) x.msg).toList.map UInt8.toNat := by
  set mu := muOf (x.keyAt (TableSelect.idxOf 0 e)) x.msg
  have hbits : MLDSA44.muBits ((nat).reader (pull e)) =
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

/-- **The frontend's composition, the views as hypotheses**: where the source program holds and
no event occurred, the relation holds at the statement and the extracted witness, given the
native frontend's hash view of domain `H`'s core and SampleInBall's view. At a checked ring
statement whose rows the statement holds: the record is the selected key's row and `μ`, so the
algebra gives `w' = computeWApprox(Â, c, z, t1)` at the key; SampleInBall's stream is
`SHAKE256(c̃')` and its fixed-stream `SampleInBall` H's decoded challenge, which the crossing makes
A's challenge polynomial; `c̃'` is the commitment hash of the key's `μ` and A's `w1`; UseHint, the
norm and the hint weight hold; so FIPS 204 verification accepts. -/
theorem mem_rel_of_source (hv : MLDSA44.HashViewCore nat F0 FH)
    {e : program.Env interp} (hs : program.SourceSatAt e)
    (hno : ∀ j, program.IsSourceChal j → ¬ ringEvent sv j e) :
    (e.stmt, proj e.stmt e.asg) ∈ rel := by
  intro len x hok hrows
  have hsel : ¬ TableSelect.SelBad 0 0 e := fun h => hno 0 MldsaRingFront.chal0 (.inl h)
  have hrel : ¬ (relEvent e).BadAt (rOf e) := fun h =>
    hno _ (MldsaRingFront.chalR (program := program)).1 (.inr (.inl ⟨rfl, h⟩))
  have hnoN : ∀ j, (nat).IsSourceChal j → ¬ sv.event j (pull e) := fun j hj h =>
    hno (j + MldsaRingFront.sibOff program) ((MldsaRingFront.chalIff j).2 hj)
      (.inr (.inr ⟨j, rfl, h⟩))
  have hcore := hSatCore hs
  have hA := aSatNat hs
  have hsam := sv.sound (pull e) hcore hnoN
  have hcr := ringCross hs (fun k hk => by
      have := hsam.sup_lt ⟨k, hk⟩
      rwa [supH_pull e ⟨k, hk⟩] at this) (fun k hk => by
      have := hsam.sgn_lt ⟨k, hk⟩
      rwa [sgnH_pull e ⟨k, hk⟩] at this)
  have hcrN := crossAt_pull hcr
  have hadm := ringOk_iff.1 hok
  have hidx := idxOf_lt64 hs
  have hlt : TableSelect.idxOf 0 e < x.ring.1.length := by rw [hadm.1]; exact hidx
  have hkey : x.keyAt (TableSelect.idxOf 0 e) = x.ring.1[TableSelect.idxOf 0 e]'hlt :=
    RingStmt.keyAt_eq hlt
  have hexp := hadm.2 _ (List.getElem_mem hlt)
  set pk := x.ring.1[TableSelect.idxOf 0 e]'hlt
  set rd := program.reader e
  set nrd := (nat).reader (pull e)
  have hW : wOf rd = _root_.MLDSA.computeWApprox _root_.MLDSA.mldsa44 Native.Rows.prims
      (nttOps := _root_.MLDSA.Concrete.concreteNTTRingOps) (Native.Rows.aHat pk) (cPoly rd)
      (zOf rd) pk.t1 :=
    algebra_eq_of_cast hs hrel (fun i j k => by
        rw [aHatVals_eq hs hsel hrows, hkey]
        unfold aHatNat Native.Rows.aHat
        rw [MLDSA44.expandABounded_eq_expandAFull hexp])
      (fun i k => by rw [t1HatVals_eq hs hsel hrows, hkey]; rfl)
  have hmu := inputBytes_mu hs hsel hrows hcr
  rw [hkey] at hmu
  have hb : AllBool (MLDSA44.w1ABits nrd) := fun t =>
    MLDSA44.Native.w1Bool hA t.isLt
  have hw1 : Shake256.inputBytes (Falcon512.HashCircuit.byteWires
      (MLDSA44.w1HBits nrd)) =
      (_root_.MLDSA.Concrete.w1Encode _root_.MLDSA.mldsa44
        (MLDSA44.PoP.Native.decodeW1 (MLDSA44.w1ABits nrd))).map UInt8.toNat := by
    have hlen := MLDSA44.w1Encode_length_mldsa44
      (MLDSA44.PoP.Native.decodeW1 (MLDSA44.w1ABits nrd))
    apply List.ext_getElem (by rw [Shake256.inputBytes, List.length_ofFn, List.length_map, hlen])
    intro j h₁ h₂
    simp only [Shake256.inputBytes, List.getElem_ofFn, List.getElem_map]
    rw [MLDSA44.HashCircuit.natOfBits_byteWires_w1Encode
      (MLDSA44.w1HBits_eq hcrN hb), List.getD_eq_getElem]
  have hcommit := MLDSA44.cTildeOf_eq_hashCommitment hv hcore hmu hw1
  have hcb : ∀ k s, MLDSA44.cABits nrd k s = 0 ∨
      MLDSA44.cABits nrd k s = 1 := fun k s => by
    have hk' : (k : ℕ) < 256 := k.isLt
    have hs' : (s : ℕ) < 2 := s.isLt
    exact MLDSA44.Native.cBool hA (by omega)
  have hver : MLDSA44.Verifies pk x.msg.toList (sigAt nrd) := by
    refine MLDSA44.verifies_of_parts (C := 264) (c := MLDSA44.chalH nrd)
      (W := MLDSA44.wOf nrd) (by decide) hexp ?_ ?_ ?_ hcommit
      (MLDSA44.Native.norm_lt hA) ?_
    · rw [← MLDSA44.sibStream_eq_core hv hcore]
      exact hsam.challenge
    · rw [← MLDSA44.cPolyA_eq hcrN hcb, cPolyA_pull, zOf_pull, wOf_pull, hW]
    · exact MLDSA44.PoP.Compose.useHintVec_eq_of_get (fun i k => (MLDSA44.coeff_apply _ k).symm)
        fun i k => by
          rw [MLDSA44.coeff_apply, MLDSA44.PoP.Native.decodeW1_get]
          erw [MLDSA44.PoP.Native.decodeH_get, MLDSA44.Native.useHint_eq hA i k]
          rfl
    · have hwt := MLDSA44.hintWeightVec_ofFn fun i k =>
        NativeAlgebraCircuit.decodeHint (MLDSA44.hVals nrd) i k
      exact hwt.trans_le (MLDSA44.Native.hintWeight_le hA)
  change ringAdm x.ring.1 ∧ RingRel bindSelf x ⟨(proj e.stmt e.asg).idx, (proj e.stmt e.asg).sig⟩
  rw [proj_idx, proj_sig]
  exact ⟨hadm, ⟨hlt, rfl, MLDSA44.verify_of_verifies hver⟩⟩

/-- **The relation from the source program without an event** (`RealizedProgram.rbr_of_events`'
`hsound`), given the views. -/
theorem sound_of_views (hv : MLDSA44.HashViewCore nat F0 FH) :
    ∀ e : program.Env interp, program.StatementOk interp e.stmt → program.SourceSatAt e →
      (∀ j, program.IsSourceChal j → ¬ ringEvent sv j e) → (e.stmt, proj e.stmt e.asg) ∈ rel :=
  fun _ _ hs hno => mem_rel_of_source sv hv hs hno

/-- **Round-by-round knowledge soundness of `Π_P₀` for a native ML-DSA-44 ring program**
(`RealizedProgram.rbr_of_events`), given the native frontend's hash view of domain `H`'s core
(`HashViewCore`, the Keccak trace's instance) and SampleInBall's view (`SampleView`) of the
native program: the relation `rel`, the extractor `extractor`, the errors `5143/|F_q^m|` at
`member.table.gamma`, `2040/|F_q^m|` at `signature.r` and SampleInBall's at the ring's challenges
`j + sibOff` (`ringEps`). -/
theorem rbr_of_views (hv : MLDSA44.HashViewCore nat F0 FH) :
    RBRKnowledgeSound rel (program.sourceVerifier interp) extractor
      (program.eventState interp rel proj (ringEvent sv) (ringEvent_use sv) (sound_of_views sv hv))
      (program.roundError interp (ringEps sv)) :=
  program.rbr_of_events interp rel proj (ringEvent sv) (ringEps sv) (ringEvent_use sv)
    (ringEvent_bound sv) (sound_of_views sv hv)

end GordieHowe.MLDSA44.Ring.Native
