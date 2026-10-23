-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA44.Emulated.Frontend.Embed
public import GordieHowe.Applications.MLDSA44.Native.ROMParams.Frontend.Sample
public import GordieHowe.Applications.MLDSA44.Native.ROMParams.Frontend.Hash
public import GordieHowe.Applications.MLDSA44.Emulated.Rows

@[expose] public section

/-!
# GordieHowe frontend: an emulated ML-DSA program, the relation and the composition

The frontend of the theorem at the realized program, for the emulated ML-DSA-44 proof of possession
at the ROM parameters
(`GordieHowe.Generated.MLDSA44.Emulated.ROMParams.Program.program`, export `c825eb05`). Domain `H` is the
native program's up to a renaming (`GordieHowe/Applications/MLDSA44/Emulated/ROMParams/Frontend/Embed.lean`), so the hash view and
SampleInBall's view are the native frontend's, read in the environment read as the native
program's (`pull`, `nat.reader (pull e)`); domain `A` is Goldilocks², in which every ML-DSA value is an integer:

* **The statement** (`KeyOf`): `key.a` (value `57`, `4 × 4 × 256` coordinates) holds `A = ExpandA(ρ)`
  in coefficient form (`GordieHowe.MLDSA44.Emulated.Rows.aKeyOf`, the C++ `fill_public_key`), `key.t1` (value
  `58`) the coefficients of `t1`, each coordinate the cast of the coefficient; `tr` (value `68`) the
  bits of `tr = H(pk)`.
* **The relation** (`rel`): as the native one, at every key whose preprocessing the statement holds
  and whose `ExpandA` finishes within the byte budget.
* **The extractor** (`proj`, `extractor`): the message bytes and `c̃'` read off domain `H` (the
  native readings `lenOf`, `messageBytes`, `cTildeOf` at `nat.reader (pull e)`), `z` and `h` read from domain `A`,
  `z` as the integer its element is (`FieldInterp.coefInt`, `sigOf`).
* **The obligations** the composition leaves (`CrossSound`, `AlgebraSound`) and the composition
  (`mem_rel_of_source`, `rbr_of_views`), with the native hash view (`GordieHowe.MLDSA44.Native.ROMParams.hashView`)
  and SampleInBall's view read through the renaming (`sampleEvent`, `sampleEvent_use`,
  `sampleEvent_bound`).
-/

namespace GordieHowe.MLDSA44.Emulated

open GordieHowe.Bits IOP
open Native.ROMParams (MldsaHHash MldsaHSample MldsaHConsts)
open scoped NNReal ENNReal

/-- **The program facts of an emulated program and its native program the emulated frontend's
composition reads** (`MldsaEmbed` and): the challenges' phases, the source challenges, the
challenges' fields, the kinds of `z` and `h`, the fields of `tr`, and the native values the
extractor reads reading nothing from the run. Each pair of programs instantiates it by `decide`. -/
class MldsaEMain (program : RealizedProgram) extends MldsaEmbed program where
  /-- The emulated program's challenges have the native one's phases. -/
  chal_phase : ∀ j, (program.challenge j).phase = (nat.challenge j).phase
  /-- **The source program's challenges are `h2c.sample.select.delta` and `h2c.sample.mem.delta`.** -/
  isSourceChal_iff : ∀ {j : ℕ}, program.IsSourceChal j ↔ j = 0 ∨ j = 1
  /-- The challenges are one coordinate of `GF(2^128)`, drawn whole, in both programs. -/
  chalFacts : (program.challenge 0).size = 1 ∧ (program.challenge 0).sampler = .full ∧ program.chalField 0 = 1 ∧ (program.challenge 1).size = 1 ∧ (program.challenge 1).sampler = .full ∧ program.chalField 1 = 1 ∧ nat.chalField 0 = 1 ∧ nat.chalField 1 = 1
  /-- The values the extractor reads read nothing from the run, in both programs. -/
  kinds59_60 : (program.value 59).kind.isBound = true ∧ (program.value 60).kind.isPriv = true
  /-- `tr` lies in domain `H`'s field in both programs. -/
  trFields : nat.valueField 67 = 1 ∧ program.valueField 68 = 1
  /-- The native values the extractor reads read nothing from the run. -/
  projReadsN : ∀ v ∈ [68, 69, 458], nat.nodeReads nat.fuel v = []

set_option linter.unusedSectionVars false

variable {program : RealizedProgram} [MldsaEMain program] {F0 FH : RealizedProgram.FieldInterp} [AField F0]
  [HField FH]

set_option hygiene false in
local notation "nat" => MldsaEmbed.nat program

variable [MldsaHHash nat] [MldsaHSample nat] [MldsaHConsts nat FH]

set_option hygiene false in
local notation "interp" => RealizedProgram.mldsaInterpOf F0 FH

/-! ## The statement -/

/-- **The statement's `tr` bits** (value `68`, `512` bits of domain `H`). -/
def trBits (x : program.Valuation interp) : BitWires (interp 1).K (8 * 64) :=
  fun k => program.evalE x 1 (.leaf 68) k

/-- **The statement holds a key's preprocessing**: `key.a` holds `A = ExpandA(ρ)` in coefficient
form (`Rows.aKeyOf`), its coordinate `(4 i + j) · 256 + k` the cast of `A_ij`'s
coefficient `k` below `q` (the operand layout of `polyMatVec`, the C++ `fill_public_key`'s
`of_scalar`); `key.t1` holds the coefficients of `t1`, coordinate `256 i + k` the cast of `t1_i`'s
coefficient `k`; and `tr` the bits of `tr = H(pk)`. -/
structure KeyOf (pk : MLDSA44.PublicKey44) (x : program.Valuation interp) : Prop where
  /-- `key.a` holds `A`. -/
  a : ∀ (i j : Fin 4) (k : Fin 256), program.evalE x 0 (.leaf 57) (((i : ℕ) * 4 + j) * 256 + k) =
    ((Rows.aKeyOf pk i j k : ℕ) : (interp 0).K)
  /-- `key.t1` holds `t1`. -/
  t1 : ∀ (i : Fin 4) (k : Fin 256), program.evalE x 0 (.leaf 58) ((i : ℕ) * 256 + k) =
    ((((pk.t1.get i).get k).val : ℕ) : (interp 0).K)
  /-- `tr` holds the bits of `H(pk)`. -/
  tr : trBits x = Falcon512.HashCircuit.wiresOfByteVec fun i => (MLDSA44.PoP.Compose.trOf pk i).toNat

/-! ## The relation -/

/-- **The relation of the theorem at an emulated ML-DSA realized program**: at every encoded key whose
decoded key's `ExpandA` finishes within the byte budget (`MLDSA44.ExpandAWithin`) and whose
preprocessing the statement
holds (`KeyOf`), the ML-DSA-44 proof-of-possession relation for messages of at most `32` bytes holds
for the witness (`PoP.MLDSA44.relUpTo 32`). -/
def rel : Set (program.Valuation interp × Native.ROMParams.VarWitness) :=
  {p | ∀ s : MLDSA44.PoP.Statement 0,
    MLDSA44.ExpandAWithin _root_.MLDSA.mldsa44 (MLDSA44.pkDecode44 s.key).rho →
    KeyOf (MLDSA44.pkDecode44 s.key) p.1 → (s, p.2) ∈ MLDSA44.PoP.relUpTo 32}

/-! ## The readings -/

/-- **`z`** (value `59` of domain `A`, `4 × 256`), in domain `A`'s field. -/
def zVals (rd : program.Valuation interp) (j : Fin _root_.MLDSA.mldsa44.l)
    (k : Fin _root_.MLDSA.ringDegree) : (interp 0).K :=
  program.evalE rd 0 (.leaf 59) ((j : ℕ) * 256 + k)

/-- **The hint `h`** (value `60` of domain `A`, `4 × 256`). -/
def hVals (rd : program.Valuation interp) (i : Fin Native.Rows.nRows)
    (k : Fin Native.Rows.deg) : (interp 0).K :=
  program.evalE rd 0 (.leaf 60) ((i : ℕ) * 256 + k)

/-- **`w'`** (value `62` of domain `A`, `4 × 256`). -/
def wVals (rd : program.Valuation interp) (i : Fin _root_.MLDSA.mldsa44.k)
    (k : Fin _root_.MLDSA.ringDegree) : (interp 0).K :=
  program.evalE rd 0 (.leaf 62) ((i : ℕ) * 256 + k)

/-- **The extracted `z`**: each coefficient the integer its element is
(`FieldInterp.coefInt`, in `(−p/2, p/2)`), modulo `q`. -/
def zOf (rd : program.Valuation interp) : _root_.MLDSA.RqVec _root_.MLDSA.mldsa44.l :=
  Vector.ofFn fun j => MLDSA44.ofCoeff fun k => ((interp 0).coefInt (zVals rd j k) : _root_.MLDSA.Coeff)

/-- **The extracted `w'`**: each coefficient the integer its element is, modulo `q`. -/
def wOf (rd : program.Valuation interp) : _root_.MLDSA.RqVec _root_.MLDSA.mldsa44.k :=
  Vector.ofFn fun i => MLDSA44.ofCoeff fun k => ((interp 0).coefInt (wVals rd i k) : _root_.MLDSA.Coeff)

/-- **The extracted signature**: `sigEncode(c̃', z, h)` with `c̃'` read off domain `H`
(`Native.ROMParams.cTildeOf` at `(nat).reader (pull e)`), `z` and the hint read from domain `A`. -/
def sigOf (e : program.Env interp) : ByteArray :=
  _root_.MLDSA.Concrete.sigEncode _root_.MLDSA.mldsa44 (Native.ROMParams.cTildeOf ((nat).reader (pull e)))
    (zOf (program.reader e)) (MLDSA44.PoP.Native.decodeH (hVals (program.reader e)))

/-- **A's `w1` bits** (value `64`, `hint.w1`, `4 × 256 × 6` bits of domain `A`). -/
def w1ABits (rd : program.Valuation interp) : BitWires (interp 0).K (8 * 768) :=
  fun t => program.evalE rd 0 (.leaf 64) t

/-- **A's challenge bits** (value `61`, `challenge.c`, `256 × 2` bits of domain `A`). -/
def cABits (rd : program.Valuation interp) (k : Fin _root_.MLDSA.ringDegree)
    (s : Fin 2) : (interp 0).K :=
  program.evalE rd 0 (.leaf 61) (2 * k + s)

/-- **A's challenge polynomial**: `support − 2 · sign` of its challenge bits. -/
def cPolyA (rd : program.Valuation interp) : _root_.MLDSA.Rq :=
  MLDSA44.ofCoeff fun k =>
    Native.Rows.bitCoeff (cABits rd k 0) - 2 * Native.Rows.bitCoeff (cABits rd k 1)

/-! ## The extractor -/

/-- **The environment of a statement and a committed assignment** with every challenge and late
value `0`. -/
def commitEnv (x : program.Valuation interp) (a : program.Assignment interp) :
    program.Env interp :=
  ⟨x, a, fun _ _ => 0, fun _ _ => 0⟩

/-- **The witness extracted from a statement and a committed assignment**: the length the flags
encode, the message bytes at it and `sigEncode(c̃', z, h)`, read in the environment of the
statement and the committed assignment.

Running time: `136` flag readings, `8 · 32` message bits and `256` bits of `c̃'` (domain `H`'s
values, each one value of the emulated program), `2 · 1024` readings of `z` and `h`, `1024`
centred readings of domain `A`'s field, and the vendored `sigEncode`, polynomial in the program's size.
This running time is argued here, not proved in Lean. -/
-- spec-side
def proj (x : program.Valuation interp) (a : program.Assignment interp) :
    Native.ROMParams.VarWitness :=
  ⟨⟨Native.ROMParams.lenOf ((nat).reader (pull (commitEnv x a))),
      Nat.lt_succ_of_le (Native.ROMParams.lenOf_le _)⟩,
    ⟨Native.ROMParams.messageBytes ((nat).reader (pull (commitEnv x a))), sigOf (commitEnv x a)⟩⟩

/-- **The extractor of `Π_P₀`** for an emulated ML-DSA program (`RealizedProgram.sourceExtractor` at `proj`).

Running time: one read of the transcript's first round and one call of `proj` (polynomial,
`proj`'s paragraph). This running time is argued here, not proved in Lean. -/
def extractor :
    Extractor (program.sourceSpec interp) (program.Valuation interp) Native.ROMParams.VarWitness :=
  program.sourceExtractor interp proj

/-! ## The obligations -/

/-- **The crossing at an environment** (`mac.equal`): A's `hint.w1` bits and challenge bits read as
naturals are H's `w1` bits and H's decoded support and sign (read through the renaming). -/
structure CrossAt (e : program.Env interp) : Prop where
  /-- The `w1` bits agree. -/
  w1 : ∀ t, (interp 0).toNat (w1ABits (program.reader e) t) =
    (interp 1).toNat (Native.ROMParams.w1HBits ((nat).reader (pull e)) t)
  /-- The supports agree. -/
  sup : ∀ k, (interp 0).toNat (cABits (program.reader e) k 0) = Native.ROMParams.supH ((nat).reader (pull e)) k
  /-- The signs agree. -/
  sgn : ∀ k, (interp 0).toNat (cABits (program.reader e) k 1) = Native.ROMParams.sgnH ((nat).reader (pull e)) k

/-- **The crossing wherever the source program holds and H's decoded support and sign are
bits.** -/
def CrossSound : Prop :=
  ∀ e : program.Env interp, program.SourceSatAt e → (∀ k, Native.ROMParams.supH ((nat).reader (pull e)) k < 2) →
    (∀ k, Native.ROMParams.sgnH ((nat).reader (pull e)) k < 2) → CrossAt e

/-- **The algebra holds at a key** (domain `A`'s obligation), on the readings of domain `A`. -/
structure AlgebraAt (pk : MLDSA44.PublicKey44) (rd : program.Valuation interp) : Prop where
  /-- The challenge bits are Boolean. -/
  cBool : ∀ k s, cABits rd k s = 0 ∨ cABits rd k s = 1
  /-- The `w1` bits are Boolean. -/
  w1Bool : AllBool (w1ABits rd)
  /-- `w' = computeWApprox(Â, c, z, t1)`. -/
  algebra : wOf rd = _root_.MLDSA.computeWApprox _root_.MLDSA.mldsa44 Native.Rows.prims
    (nttOps := _root_.MLDSA.Concrete.concreteNTTRingOps) (Native.Rows.aHat pk) (cPolyA rd)
    (zOf rd) pk.t1
  /-- `w1 = UseHint(h, w')`. -/
  useHint : ∀ i k, NativeAlgebraCircuit.w1Coeff (w1ABits rd) i k =
    _root_.MLDSA.Concrete.useHintCoeff (NativeAlgebraCircuit.decodeHint (hVals rd) i k)
      (MLDSA44.coeff ((wOf rd).get i) k) mldsa44.γ₂
  /-- `‖z‖∞ < γ₁ − β`. -/
  norm : ∀ j k,
    (LatticeCrypto.centeredRepr (MLDSA44.coeff ((zOf rd).get j) k)).natAbs < mldsa44.normBound
  /-- The hint weight is at most `ω`. -/
  hintWeight : (Finset.univ.filter fun ik : Fin Native.Rows.nRows × Fin Native.Rows.deg =>
    NativeAlgebraCircuit.decodeHint (hVals rd) ik.1 ik.2 = true).card ≤ mldsa44.ω

/-- **Domain `A`'s obligation**: at every environment where the source program holds and every key
whose preprocessing the statement holds, the algebra holds at the key. -/
def AlgebraSound : Prop :=
  ∀ e : program.Env interp, program.SourceSatAt e → ∀ pk, KeyOf pk e.stmt →
    AlgebraAt pk (program.reader e)

/-! ## SampleInBall's view through the renaming -/

/-- **SampleInBall's events**: the native frontend's (`Native.ROMParams.sampleEvent`) in the
environment read as the native program's. -/
def sampleEvent (j : ℕ) (e : program.Env interp) : Prop :=
  Native.ROMParams.sampleEvent j (pull e)

/-- The emulated program's challenges have the native one's phases. -/
theorem chal_phase : ∀ j, (program.challenge j).phase = ((nat).challenge j).phase :=
  MldsaEMain.chal_phase

/-- **The challenge-use rule** (`RealizedProgram.ChallengeUseAt`), through the native one. -/
theorem sampleEvent_use : RealizedProgram.ChallengeUseAt program interp sampleEvent :=
  fun _ _ _ h => Native.ROMParams.sampleEvent_use _
    (RealizedProgram.eqUpTo_pullEnv MldsaEmbed.embedding (chal_phase (program := program)) h)

/-- **The source program's challenges are `h2c.sample.select.delta` and `h2c.sample.mem.delta`.** -/
theorem isSourceChal_iff : ∀ {j : ℕ}, program.IsSourceChal j ↔ j = 0 ∨ j = 1 :=
  MldsaEMain.isSourceChal_iff

/-- The challenges are one coordinate of `GF(2^128)`, drawn whole, in both programs. -/
theorem chalFacts : (program.challenge 0).size = 1 ∧ (program.challenge 0).sampler = .full ∧ program.chalField 0 = 1 ∧ (program.challenge 1).size = 1 ∧ (program.challenge 1).sampler = .full ∧ program.chalField 1 = 1 ∧ (nat).chalField 0 = 1 ∧ (nat).chalField 1 = 1 :=
  MldsaEMain.chalFacts

/-- **A challenge of the environment read as the native program's** is the emulated challenge. -/
theorem pull_chal (e : program.Env interp) {j : ℕ} (hj : j = 0 ∨ j = 1) :
    (RealizedProgram.castElt ((pull e).chal j 0) : (interp 1).K) = RealizedProgram.castElt (e.chal j 0) := by
  have hf : program.chalField j = (nat).chalField j := by
    rcases hj with rfl | rfl
    · rw [(chalFacts (program := program)).2.2.1, (chalFacts (program := program)).2.2.2.2.2.2.1]
    · rw [(chalFacts (program := program)).2.2.2.2.2.1, (chalFacts (program := program)).2.2.2.2.2.2.2]
  exact RealizedProgram.castElt_castElt_of_src hf _

/-- **The events' probabilities**: at most `264/2^128` and `295/2^128`
(`RealizedProgram.probUniform_badAt_setChal_le`). -/
theorem sampleEvent_bound : ∀ j, program.IsSourceChal j → ∀ e : program.Env interp,
    Pr[c ← program.ChalVal interp j : sampleEvent j (e.setChal j c)] ≤
      Native.ROMParams.sampleEpsOf (HField.bits FH) j := by
  intro j hj e
  have hst : ∀ c, (pull (e.setChal j c)).stmt = (pull e).stmt ∧
      (pull (e.setChal j c)).asg = (pull e).asg := fun c => ⟨rfl, rfl⟩
  rcases (isSourceChal_iff (program := program)).1 hj with rfl | rfl
  · have hset : ∀ c, sampleEvent 0 (e.setChal 0 c) ↔
        (Native.ROMParams.selBadE (pull e)).BadAt (RealizedProgram.castElt ((e.setChal 0 c).chal 0 0)) := fun c => by
      simp only [sampleEvent, Native.ROMParams.sampleEvent, true_and, zero_ne_one, false_and,
        or_false]
      rw [Native.ROMParams.selBadE_congr (hst c).1 (hst c).2, pull_chal _ (.inl rfl)]
    simp only [hset]
    refine (RealizedProgram.probUniform_badAt_setChal_le (j := 0) (chalFacts (program := program)).1 (chalFacts (program := program)).2.1
      (chalFacts (program := program)).2.2.1 (Native.ROMParams.selBadE (pull e)) e).trans ?_
    have hdeg : (Native.ROMParams.selBadE (pull e)).deg = 264 := rfl
    have hcard : Fintype.card (interp 1).K = 2 ^ HField.bits FH := HField.card
    rw [hdeg, hcard]
    simp only [Native.ROMParams.sampleEpsOf]
    norm_num
  · have hset : ∀ c, sampleEvent 1 (e.setChal 1 c) ↔
        (Native.ROMParams.memBadE (pull e)).BadAt (RealizedProgram.castElt ((e.setChal 1 c).chal 1 0)) := fun c => by
      simp only [sampleEvent, Native.ROMParams.sampleEvent, one_ne_zero, false_and, false_or,
        true_and]
      rw [Native.ROMParams.memBadE_congr (hst c).1 (hst c).2, pull_chal _ (.inr rfl)]
    simp only [hset]
    refine (RealizedProgram.probUniform_badAt_setChal_le (j := 1) (chalFacts (program := program)).2.2.2.1 (chalFacts (program := program)).2.2.2.2.1
      (chalFacts (program := program)).2.2.2.2.2.1 (Native.ROMParams.memBadE (pull e)) e).trans ?_
    have hdeg : (Native.ROMParams.memBadE (pull e)).deg = 295 :=
      (Native.ROMParams.samM nat F0 FH).bad_deg _
    have hcard : Fintype.card (interp 1).K = 2 ^ HField.bits FH := HField.card
    rw [hdeg, hcard]
    simp only [Native.ROMParams.sampleEpsOf, if_neg one_ne_zero]
    norm_num

/-! ## The composition's parts -/

/-- **`tr` read through the renaming** is the statement's `tr`. -/
theorem trBits_pull (e : program.Env interp) :
    Native.ROMParams.trBits (pull e).stmt = trBits e.stmt := by
  funext k
  simp only [Native.ROMParams.trBits, trBits, RealizedProgram.evalE_leaf, pull, RealizedProgram.pullEnv,
    if_pos (show (67 : ℕ) ∈ hV by decide)]
  have h1 : (nat).valueField 67 = 1 := (MldsaEMain.trFields (program := program)).1
  have h2 : program.valueField 68 = 1 := (MldsaEMain.trFields (program := program)).2
  exact RealizedProgram.castElt_castElt_of_src (h2.trans h1.symm) _

/-- A Boolean element of domain `A`'s field is read as `0` or `1`. -/
theorem toNat_bool {v : (interp 0).K} (hv : v = 0 ∨ v = 1) : (interp 0).toNat v = if v = 1 then 1 else 0 := by
  rcases hv with rfl | rfl
  · rw [if_neg (zero_ne_one), show (0 : (interp 0).K) = ((0 : ℕ) : (interp 0).K) from
      Nat.cast_zero.symm]
    exact AField.toNat_natCast 0 (by norm_num [pGold])
  · rw [if_pos rfl, show (1 : (interp 0).K) = ((1 : ℕ) : (interp 0).K) from Nat.cast_one.symm]
    exact AField.toNat_natCast 1 (by norm_num [pGold])

/-- **A Boolean element of domain `A`'s field as a coefficient** is its integer reading. -/
theorem bitCoeff_eq_toNat {v : (interp 0).K} (hv : v = 0 ∨ v = 1) :
    Native.Rows.bitCoeff v = ((interp 0).toNat v : _root_.MLDSA.Coeff) := by
  rw [toNat_bool hv]
  unfold Native.Rows.bitCoeff
  split_ifs <;> simp

/-- **A's challenge polynomial is H's decoded challenge**, given the crossing and the Booleanity
of A's challenge bits. -/
theorem cPolyA_eq {e : program.Env interp} (hx : CrossAt e)
    (hb : ∀ k s, cABits (program.reader e) k s = 0 ∨ cABits (program.reader e) k s = 1) :
    cPolyA (program.reader e) =
      MLDSA44.ofCoeff fun k => (Native.ROMParams.chalH ((nat).reader (pull e)) k : _root_.MLDSA.Coeff) := by
  unfold cPolyA
  refine congrArg MLDSA44.ofCoeff (funext fun k => ?_)
  rw [bitCoeff_eq_toNat (hb k 0), bitCoeff_eq_toNat (hb k 1), hx.sup k, hx.sgn k]
  change _ = (((Native.ROMParams.supH ((nat).reader (pull e)) k : ℤ) -
    2 * (Native.ROMParams.sgnH ((nat).reader (pull e)) k : ℤ) : ℤ) : _root_.MLDSA.Coeff)
  push_cast
  ring

/-- **H's `w1` bits are the bits of A's UseHint outputs**, given the crossing and the Booleanity of
A's `w1` bits. -/
theorem w1HBits_eq {e : program.Env interp} (hx : CrossAt e) (hb : AllBool (w1ABits (program.reader e)))
    (i : Fin _root_.MLDSA.mldsa44.k) (c : Fin _root_.MLDSA.ringDegree) (b : Fin 6) :
    Native.ROMParams.w1HBits ((nat).reader (pull e))
        ⟨((i : ℕ) * _root_.MLDSA.ringDegree + c) * 6 + b, HashCircuit.w1Bit_lt i c b⟩ =
      Bits.constBit (((MLDSA44.PoP.Native.decodeW1 (w1ABits (program.reader e))).get i).get c).val
        b := by
  have hidx : (⟨((i : ℕ) * _root_.MLDSA.ringDegree + c) * 6 + b, HashCircuit.w1Bit_lt i c b⟩ :
      Fin (8 * 768)) = ⟨mldsa44.r1_bits * (finProdFinEquiv (i, c) : Fin (4 * 256)) + b, by
        have := HashCircuit.w1Bit_lt i c b
        simp only [finProdFinEquiv_apply_val]
        change 6 * ((c : ℕ) + 256 * i) + b < 8 * 768
        change ((i : ℕ) * 256 + c) * 6 + b < 8 * 768 at this
        omega⟩ := Fin.ext (by
    simp only [finProdFinEquiv_apply_val]
    change ((i : ℕ) * 256 + c) * 6 + b = 6 * ((c : ℕ) + 256 * i) + b
    ring)
  set rd := program.reader e
  have hbits : AllBool (NativeAlgebraCircuit.outputBits (w1ABits rd) (finProdFinEquiv (i, c))) :=
    fun _ => hb _
  rw [MLDSA44.PoP.Native.decodeW1_get, ZMod.val_natCast,
    Nat.mod_eq_of_lt ((MLDSA44.PoP.Native.w1Coeff_lt (w1ABits rd) i c).trans (by decide)),
    NativeAlgebraCircuit.w1Coeff, SelectFirstTau.constBit_eq_ite_testBit]
  have hiff := Native.bit_eq_testBit hbits b
  rw [hidx]
  set t : Fin (8 * 768) := ⟨mldsa44.r1_bits * (finProdFinEquiv (i, c) : Fin (4 * 256)) + b, _⟩
  have hA : w1ABits rd t = 1 ↔ (natOfBits (NativeAlgebraCircuit.outputBits (w1ABits rd)
      (finProdFinEquiv (i, c)))).testBit b := hiff
  have hlt : (interp 0).toNat (w1ABits rd t) < 2 := by
    rw [toNat_bool (hb t)]
    split_ifs <;> omega
  have hH := HField.eq_of_toNat_lt_two (hx.w1 t).symm hlt
  change Native.ROMParams.w1HBits ((nat).reader (pull e)) t = _ at hH
  rw [hH]
  have hone : w1ABits rd t = 1 ↔ (interp 0).toNat (w1ABits rd t) = 1 := by
    rw [toNat_bool (hb t)]
    split_ifs with h <;> simp [h]
  by_cases ht : (natOfBits (NativeAlgebraCircuit.outputBits (w1ABits rd) (finProdFinEquiv (i, c)))).testBit b
  · rw [if_pos (hone.1 (hA.2 ht)), if_pos ht]
  · rw [if_neg fun h => ht (hA.1 (hone.2 h)), if_neg ht]

/-- **`c̃'` is the commitment hash** `H(μ ‖ w1Encode(w1), 32)` with `μ = H(tr ‖ frame([], M), 64)`
and `w1` A's UseHint outputs, where the source program holds, at a key whose preprocessing the
statement holds (FIPS 204 Algorithm 8, line 12). -/
theorem cTilde_eq_hashCommitment {e : program.Env interp} (hs : program.SourceSatAt e)
    {pk : MLDSA44.PublicKey44} (hk : KeyOf pk e.stmt) (hx : CrossAt e)
    (hb : AllBool (w1ABits (program.reader e))) :
    _root_.MLDSA.Concrete.hashCommitment _root_.MLDSA.mldsa44
        (_root_.MLDSA.Concrete.hashMessage (Native.Rows.prims.hashPublicKey pk.rho pk.t1)
          (MLDSA44.frame [] (List.ofFn (Native.ROMParams.messageBytes ((nat).reader (pull e))))))
        (_root_.MLDSA.Concrete.w1Encode _root_.MLDSA.mldsa44
          (MLDSA44.PoP.Native.decodeW1 (w1ABits (program.reader e)))) =
      Native.ROMParams.cTildeOf ((nat).reader (pull e)) := by
  have hH := hSat hs
  have htr : Native.ROMParams.trBits (pull e).stmt =
      Falcon512.HashCircuit.wiresOfByteVec fun i => (MLDSA44.PoP.Compose.trOf pk i).toNat := by
    rw [trBits_pull, hk.tr]
  set rd := program.reader e
  have hv := Native.ROMParams.hashView (program := nat) (F0 := F0) (FH := FH)
  have hw1 : Shake256.inputBytes (Falcon512.HashCircuit.byteWires
      (Native.ROMParams.w1HBits ((nat).reader (pull e)))) =
      (_root_.MLDSA.Concrete.w1Encode _root_.MLDSA.mldsa44
        (MLDSA44.PoP.Native.decodeW1 (w1ABits rd))).map UInt8.toNat := by
    have hlen := MLDSA44.w1Encode_length_mldsa44 (MLDSA44.PoP.Native.decodeW1 (w1ABits rd))
    apply List.ext_getElem (by rw [Shake256.inputBytes, List.length_ofFn, List.length_map, hlen])
    intro j h₁ h₂
    simp only [Shake256.inputBytes, List.getElem_ofFn, List.getElem_map]
    rw [HashCircuit.natOfBits_byteWires_w1Encode (w1HBits_eq hx hb), List.getD_eq_getElem]
  apply Vector.ext
  intro i hi
  apply UInt8.toNat_inj.mp
  have hl := MLDSA44.hashCommitment_get
    (_root_.MLDSA.Concrete.hashMessage (Native.Rows.prims.hashPublicKey pk.rho pk.t1)
      (MLDSA44.frame [] (List.ofFn (Native.ROMParams.messageBytes ((nat).reader (pull e))))))
    (_root_.MLDSA.Concrete.w1Encode _root_.MLDSA.mldsa44
      (MLDSA44.PoP.Native.decodeW1 (w1ABits rd))) ⟨i, hi⟩
  change UInt8.toNat (Vector.get _ ⟨i, hi⟩) = UInt8.toNat (Vector.get _ ⟨i, hi⟩)
  refine hl.trans ?_
  rw [← Native.ROMParams.muBytes_eq hv hH htr, ← hw1, ← Shake256.SpongeSpec.xof_shake256,
    ← hv.cTilde_input _ hH, ← hv.cTilde.sound _ hH ⟨i, hi⟩, hv.cTilde_out _ hH ⟨i, hi⟩]
  simp only [Native.ROMParams.cTildeOf, Vector.get_ofFn]
  rw [Native.toNat_toUInt8_natOfBits]
  rfl

/-! ## The extractor's readings -/

/-- The values the extractor reads read nothing from the run, in both programs. -/
theorem kinds59_60 : (program.value 59).kind.isBound = true ∧ (program.value 60).kind.isPriv = true :=
  MldsaEMain.kinds59_60

/-- **A bound or private value reads the committed assignment.** -/
theorem reader_of_asg (e : program.Env interp) {v : ℕ}
    (h : (program.value v).kind.isBound = true ∨ (program.value v).kind.isPriv = true) :
    program.reader e v = e.asg.val v := by
  funext i
  rw [RealizedProgram.reader, RealizedProgram.fuel, RealizedProgram.read.eq_2]
  cases hk : (program.value v).kind <;> simp_all [RealizedProgram.Kind.isBound, RealizedProgram.Kind.isPriv]

/-- The native values the extractor reads read nothing from the run. -/
theorem projReadsN_nil : ∀ v ∈ [68, 69, 458], (nat).nodeReads (nat).fuel v = [] :=
  MldsaEMain.projReadsN (program := program)

/-- The environment of the statement and the committed assignment, read as the native program's,
has the environment's statement and committed assignment. -/
theorem pull_commitEnv {e : program.Env interp} :
    (pull (commitEnv e.stmt e.asg)).stmt = (pull e).stmt ∧
      (pull (commitEnv e.stmt e.asg)).asg = (pull e).asg := by
  constructor <;> simp only [pull, RealizedProgram.pullEnv, commitEnv]

/-- **The extracted message** is the environment's message bytes. -/
theorem ofFn_proj_message (e : program.Env interp) :
    List.ofFn (proj e.stmt e.asg).2.message =
      List.ofFn (Native.ROMParams.messageBytes ((nat).reader (pull e))) := by
  have h : ∀ v ∈ [68, 69, 458], (nat).reader (pull (commitEnv e.stmt e.asg)) v = (nat).reader (pull e) v := fun v hv =>
    RealizedProgram.reader_eq_of_nodeReads_nil (projReadsN_nil v hv) pull_commitEnv.1 pull_commitEnv.2
  have h68 := h 68 (List.mem_cons_self ..)
  have h69 := h 69 (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  exact Native.ROMParams.ofFn_messageBytes_congr h68 h69

/-- **The extracted signature** is the environment's `sigEncode(c̃', z, h)`. -/
theorem proj_signature (e : program.Env interp) :
    (proj e.stmt e.asg).2.signature = sigOf e := by
  have hN : (nat).reader (pull (commitEnv e.stmt e.asg)) 458 = (nat).reader (pull e) 458 :=
    RealizedProgram.reader_eq_of_nodeReads_nil (projReadsN_nil 458 (by simp)) pull_commitEnv.1
      pull_commitEnv.2
  have h59 : program.reader (commitEnv e.stmt e.asg) 59 = program.reader e 59 := by
    rw [reader_of_asg _ (.inl (kinds59_60 (program := program)).1), reader_of_asg _ (.inl (kinds59_60 (program := program)).1)]
    simp only [commitEnv]
  have h60 : program.reader (commitEnv e.stmt e.asg) 60 = program.reader e 60 := by
    rw [reader_of_asg _ (.inr (kinds59_60 (program := program)).2), reader_of_asg _ (.inr (kinds59_60 (program := program)).2)]
    simp only [commitEnv]
  change sigOf (commitEnv e.stmt e.asg) = sigOf e
  unfold sigOf Native.ROMParams.cTildeOf Native.ROMParams.cTildeBits zOf zVals hVals
  simp only [RealizedProgram.evalE_leaf, hN, h59, h60]

/-! ## The composition -/

/-- **The frontend's composition, the obligations as hypotheses**: where the source program holds
and no SampleInBall event occurred, the relation holds at the statement and the extracted witness,
given the crossing and the algebra (the hash view and SampleInBall's view are the native ones read
through the renaming). -/
theorem mem_rel_of_source (hx : CrossSound (program := program) (F0 := F0) (FH := FH)) (hA : AlgebraSound (program := program) (F0 := F0) (FH := FH)) {e : program.Env interp}
    (hs : program.SourceSatAt e) (hno : ∀ j, program.IsSourceChal j → ¬ sampleEvent j e) :
    (e.stmt, proj e.stmt e.asg) ∈ rel := by
  intro s hexp hkey
  have hH := hSat hs
  have halg := hA e hs _ hkey
  have hnoN : ∀ j, (nat).IsSourceChal j → ¬ Native.ROMParams.sampleEvent j (pull e) := by
    intro j hj
    rcases Native.ROMParams.isSourceChal_iff.1 hj with rfl | rfl
    · exact hno 0 ((isSourceChal_iff (program := program)).2 (.inl rfl))
    · exact hno 1 ((isSourceChal_iff (program := program)).2 (.inr rfl))
  have hsam := Native.ROMParams.sampledAt hH hnoN
  have hcr := hx e hs hsam.sup_lt hsam.sgn_lt
  change MLDSA44.VerifiesBytes _ (List.ofFn s.ctx) (List.ofFn (proj e.stmt e.asg).2.message)
    (proj e.stmt e.asg).2.signature
  rw [ofFn_proj_message, proj_signature, List.ofFn_zero, sigOf]
  refine MLDSA44.verifiesBytes_of_parts (C := 264) (c := Native.ROMParams.chalH ((nat).reader (pull e)))
    (W := wOf (program.reader e)) (by decide) hexp ?_ ?_ ?_
    (cTilde_eq_hashCommitment hs hkey hcr halg.w1Bool) halg.norm ?_
  · rw [← Native.ROMParams.sibStream_eq (Native.ROMParams.hashView) hH]
    exact hsam.challenge
  · rw [← cPolyA_eq hcr halg.cBool, ← halg.algebra]
  · exact MLDSA44.PoP.Compose.useHintVec_eq_of_get (fun i k => (MLDSA44.coeff_apply _ k).symm)
      fun i k => by
        rw [MLDSA44.coeff_apply, MLDSA44.PoP.Native.decodeW1_get]
        erw [MLDSA44.PoP.Native.decodeH_get, halg.useHint i k]
        rfl
  · have hwt := MLDSA44.hintWeightVec_ofFn fun i k =>
      NativeAlgebraCircuit.decodeHint (hVals (program.reader e)) i k
    exact hwt.trans_le halg.hintWeight

/-- **The relation from the source program without an event** (`RealizedProgram.rbr_of_events`'
`hsound`). -/
theorem sound_of_views (hx : CrossSound (program := program) (F0 := F0) (FH := FH)) (hA : AlgebraSound (program := program) (F0 := F0) (FH := FH)) :
    ∀ e : program.Env interp, program.StatementOk interp e.stmt → program.SourceSatAt e →
      (∀ j, program.IsSourceChal j → ¬ sampleEvent j e) → (e.stmt, proj e.stmt e.asg) ∈ rel :=
  fun _ _ hs hno => mem_rel_of_source hx hA hs hno

/-- **Round-by-round knowledge soundness of `Π_P₀` for an emulated ML-DSA program**, the proof system
headline's hypothesis (`RealizedProgram.rbr_of_events`), given the crossing and the algebra: SampleInBall's
events at `h2c.sample.select.delta` and `h2c.sample.mem.delta` with errors `264/2^bits` and
`295/2^bits`. -/
theorem rbr_of_views (hx : CrossSound (program := program) (F0 := F0) (FH := FH)) (hA : AlgebraSound (program := program) (F0 := F0) (FH := FH)) :
    rbrKnowledgeSoundness rel (program.sourceVerifier interp) extractor
      (program.eventState interp rel proj sampleEvent sampleEvent_use (sound_of_views hx hA))
      (program.roundError interp (Native.ROMParams.sampleEpsOf (HField.bits FH))) :=
  program.rbr_of_events interp rel proj sampleEvent (Native.ROMParams.sampleEpsOf (HField.bits FH)) sampleEvent_use
    sampleEvent_bound (sound_of_views hx hA)

end GordieHowe.MLDSA44.Emulated
