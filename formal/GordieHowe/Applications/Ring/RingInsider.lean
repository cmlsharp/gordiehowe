-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Ring.RingInsiderRelays
public import GordieHowe.Model.Quantum.Interactive.ReqBridgeLogs
public import GordieHowe.Applications.Ring.RingUnforgeability
public import GordieHowe.Applications.Ring.SPBCSComap
public import GordieHowe.Model.RingSignature.Transcript
public import GordieHowe.Applications.Ring.InsiderTools
public import GordieHowe.SPBCS.KnowledgeTheorems

@[expose] public section

/-!
# Unforgeability of `ofBase` at every base message, by zero knowledge and simulation extraction

BKM06 Definition 7 (`insiderForgeProb`, `GordieHowe/Model/RingSignature/Unforgeability.lean`) for
the ring signature `ofBase B (spbcsComapProofSystem …) adm` compiled by spBCS at a program's
statements, at every base message (converted signatures included), for base signers whose public
value and refusals are functions of the signing coins. At fixed keys and auxiliary value, the
game's ring signatures are
replaced by checked ones (`Q · εc`), absorbed into proof queries of the real zero-knowledge
challenger, simulated (`zkError`), unchecked (`Q · εc`), and absorbed into the
simulation-extraction game, whose fresh accepted statements are extracted (`simExtractionError`);
an extracted witness decodes to a forgery of MU-EUF-CMA^corr without signing requests. Forgeries on
the empty ring are bounded by the knowledge error.

- `Quantum.AdaptiveIAlg.toTPKindAlg_mapOut`, `composeBothOut_mapOut_tp` (for `AdaptiveIAlg.mapOut`,
  `GordieHowe/Model/RingSignature/Transcript.lean`);
  `Quantum.KindAlg.toOuterMeasure_outLaw_composeBothOut_readout`;
  `QROM.outWith_realChallenger_assignments`, `QROM.simChallenger_congr`.
- `FreshAt` (freshness at a request list), `Fresh.freshAt`; `Output`; `relZ`.
- `ZKRingHyps B adm stmt check input fw enc relH rel wit`: the hypotheses on the program's
  statements, with a partial encoding `enc` (`stmt` injective; a ring witness has an encoding, its
  honest input is the decoded encoding and a witness of `relH`; no statement of the empty ring has
  a witness of `relH`; a witness of `rel` at a checked statement gives a ring witness).
  `zkRingHyps_id`: they hold for the identity reading (satisfiability). `ZKRingHypsAt`: the
  hypotheses of the zero-knowledge step with a total encoding; `ZKRingHyps.at` gives them for the
  encoding read with a default (`encWith`); `ZKRingHyps.not_mem_ringRel`: without an encoding type
  the ring relation is empty.
- `encProver`; `Wins`, `forgeryTest` (with `forgeryTest_queriesLE`, `run_forgeryTest`),
  `zkAbsorbed`, `zkTest`, `distinguisher`: the zero-knowledge distinguisher.
- `prove_eq_of_hyps`, `game_le_sum_real`, `acceptProb_distinguisher`, `acceptProb_real_le`,
  `sum_sim_eq_checked`: the game to the real challenger, zero knowledge, and back to the checked
  simulated game.
- `claimOfOut`, `seAlg`, `seAdversary`, `okAt`, `inertOnNil`, `relayed_ne_of_fresh`,
  `sim_le_sum_winTestProb`, `simAssignsAtKeys_inertOnNil`: the simulation-extraction adversary and
  the hop to its game. `seAlg` reads the corrupted users' key coins from a table of outer replies
  (`AdaptiveIAlg.absorbTab` with `seTwo`); `outLaw_seRelay_absorbTab`: against every challenger it
  has the law of the adversary absorbed through `seRelay` at the key coins; `winTestProb_mapOut`.
- `corruptHist` (the corruption-only history of MU-EUF-CMA^corr), `outStmt`, `forgerWins`,
  `extractFreshTestProb_le`: an extracted witness is a forgery of the multi-user game.
- `seSim`, `game_le_sum_winTestProb_at` (a total encoding), `game_le_sum_winTestProb` (a partial
  encoding; without an encoding type, through the refusing game of `checked_eq_refuse` and
  `simChecked_eq_refuse`), `zkForgerSuccess`, `keys_le`, `forgeProb_le_wins_add`, `zkForgerTerm`.
- `insiderForgeProb_le_zk` (the program form; its form by MU-EUF-CMA^corr,
  `insiderForgeProb_le_zk_muEufProb`, is the headline).

## The base term

`zkForgerTerm` (`zkForgerSuccess`) is the success probability of a forger of another form than the
adversaries of `Signature.MUAdversary`: it runs the
adversary against simulated ring signatures, simulates the oracle with a compressed oracle and
extracts from its database, reading the users' keys only as public keys and the key coins of the
users the adversary corrupts. Its winning condition is that of MU-EUF-CMA^corr with the ring-aware
signing oracle (`Signature.Forges`) at the history of its corruptions, with no signing request. The
theorems here do not bound it by `Signature.muEufProb` of a `GameAdversary`.

## Hypotheses beyond the earlier route

The base signer reads no oracle (`BaseSigner.OracleFree`) and decides its refusals from public
data and coins (`BaseSigner.RefusalOfCoins`); the base message, the public values and the
signatures are inhabited types (`Nonempty B.Msg`, `Nonempty B.Pub`, `Nonempty B.BSig`).
-/

namespace GordieHowe

open Quantum
open scoped ENNReal

namespace Quantum.AdaptiveIAlg

variable {X Y Req Resp O O' : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp]

variable [Nonempty X] [AddGroup Y] [Nonempty Y]

/-- **The trace-preserving form of an adversary with its output read through a map** is that of
the adversary with the output replaced. -/
theorem toTPKindAlg_mapOut {O' : Type} {shA : AlgShape X Y Req Resp} (A : AdaptiveIAlg shA O) (f : O → O') :
    (A.mapOut f).toTPKindAlg = { A.toTPKindAlg with out := fun w => f (A.out w.1) } :=
  rfl

/-- **The composition of the trace-preserving form does not read the output map.** -/
theorem composeBothOut_mapOut_tp {O' : Type} {shA : AlgShape X Y Req Resp} (A : AdaptiveIAlg shA O) (f : O → O')
    (C : Challenger X Y Req Resp) :
    (A.mapOut f).toTPKindAlg.composeBothOut C id = A.toTPKindAlg.composeBothOut C id := by
  have h := congr_arg_heq (fun K : KindAlg _ O' => K.composeBothOut C id)
    (toTPKindAlg_mapOut A f)
  exact eq_of_heq (h.trans (heq_of_eq rfl))

end Quantum.AdaptiveIAlg

namespace Quantum.KindAlg

variable {X Y Req Resp O O' : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp] [Nonempty X] [AddGroup Y]
  [Nonempty Y]

/-- **A readout of the composed registers moves into the event**: the composition read through `f`
has, on the event of its readout, the probability of the composition read as its registers on the
event of `f` of them. -/
theorem toOuterMeasure_outLaw_composeBothOut_readout {ksK : KindShape X Y Req Resp} (K : KindAlg ksK O)
    (C : Challenger X Y Req Resp) (f : K.CW C → O') (H : X → Y) (P : O' → Prop) :
    ((K.composeBothOut C f).outLaw H).toOuterMeasure {o | ∃ y ∈ o, P y} =
      ((K.composeBothOut C id).outLaw H).toOuterMeasure {o | ∃ v ∈ o, P (f v)} := by
  have hmap : (K.composeBothOut C f).outLaw H =
      ((K.composeBothOut C id).outLaw H).map (Option.map f) := by
    simp only [Alg.outLaw]
    rw [PMF.map_comp, Option.map_comp_map]
    rfl
  rw [hmap, PMF.toOuterMeasure_map_apply]
  congr 1
  ext o
  cases o <;> simp

end Quantum.KindAlg

namespace QROM

variable {X Y Stmt Wit Proof Coins : Type} [Fintype Coins] [DecidableEq Coins]

/-- **The real challenger assigns nothing.** -/
theorem outWith_realChallenger_assignments (rel : Stmt → Wit → Prop) [DecidableRel rel]
    (Pv : NARG.Prover X Y Stmt Wit Proof Coins) (μ : PMF Coins) (Q : ℕ) (ω : Fin Q → Coins)
    (hist : List (Quantum.HistoryEntry (ProofQuery Stmt Wit) Proof)) (req : ProofQuery Stmt Wit)
    (ans : List Y) : ((realChallenger rel Pv μ Q).outWith ω hist req ans).assignments = [] := by
  unfold Quantum.Challenger.outWith Quantum.Challenger.outWithOf
  simp only [realChallenger]
  split_ifs
  · rw [Quantum.OracleProgAns.result_bind_pure (fun π => (⟨some π, []⟩ : Quantum.Reply X Y Proof))]
    cases OracleProgAns.result _ ans <;> rfl
  · rfl
  · rfl


/-- **The simulated challenger depends on the relation only through its pairs**, not on the
decision procedure nor on the instances of the simulator's coins. -/
theorem simChallenger_congr {SC : Type} (i₁ i₂ : Fintype SC) (d₁ d₂ : DecidableEq SC)
    (rel rel' : Stmt → Wit → Prop) (r₁ : DecidableRel rel) (r₂ : DecidableRel rel')
    (h : ∀ x w, rel x w ↔ rel' x w) (Sim : NARG.Simulator X Y Stmt Proof SC) (Q : ℕ) :
    @simChallenger X Y Stmt Wit Proof SC rel r₁ i₁ d₁ Sim Q =
      @simChallenger X Y Stmt Wit Proof SC rel' r₂ i₂ d₂ Sim Q := by
  obtain rfl : rel = rel' := funext fun x => funext fun w => propext (h x w)
  obtain rfl : i₁ = i₂ := Subsingleton.elim _ _
  obtain rfl : d₁ = d₂ := Subsingleton.elim _ _
  obtain rfl : r₁ = r₂ := Subsingleton.elim _ _
  rfl

end QROM

/-! ### Freshness at a list of requests -/

namespace RingSignature.Insider

variable {X Y : Type} {N n : ℕ} {TS : Signature.SchemeTypes} {RMsg : Type}
  {B : BaseSigner X Y N TS RMsg}
  {TPS : PSTypes} [Fintype TPS.Proof] [DecidableEq TPS.Proof] [Fintype TPS.Coins] [DecidableEq TPS.Coins] [Nonempty TPS.Coins] {PS : ProofSystem X Y (RingStmt B) (RingWit B) TPS} {adm : KeyRing B.PK N → Prop} [DecidablePred adm]

variable [DecidableEq TS.PK]

/-- **The freshness of BKM06 Definition 7 at the users' key coins `keys` and the requests `rs`**:
every key of the ring is the key of a user without a corruption request, and no ring-signing request
was for the ring and the message. -/
structure FreshAt (keys : Fin n → B.KeyCoins) (rs : List (Req B PS adm n))
    (R : KeyRing (ofBase B PS adm).PK N) (m : (ofBase B PS adm).Msg) : Prop where
  /-- Every key of the ring is the key of an uncorrupted user. -/
  honest_ring : ∀ pk ∈ R.1, ∃ i, B.pk (keys i) = pk ∧ UnforgeRequest.corrupt i ∉ rs
  /-- No ring signature on the ring and the message was requested. -/
  not_sign : ∀ s, UnforgeRequest.sign s R m ∉ rs

omit [Fintype TPS.Proof] [DecidableEq TPS.Proof] [Fintype TPS.Coins] [DecidableEq TPS.Coins]
  [Nonempty TPS.Coins] in
/-- **Freshness for a history is freshness at its requests.** -/
theorem Fresh.freshAt {keys : Fin n → B.KeyCoins}
    {hist : UnforgeHist (S := ofBase B PS adm) n (SideOracle.none _)}
    {R : KeyRing (ofBase B PS adm).PK N} {m : (ofBase B PS adm).Msg} (h : Fresh keys hist R m) :
    FreshAt keys (hist.map HistoryEntry.request) R m where
  honest_ring pk hpk := by
    obtain ⟨i, hi, hc⟩ := h.honest_ring pk hpk
    refine ⟨i, hi, fun hm => hc ?_⟩
    obtain ⟨x, hx, hr⟩ := List.mem_map.1 hm
    exact ⟨x, hx, hr⟩
  not_sign s hm := by
    obtain ⟨x, hx, hr⟩ := List.mem_map.1 hm
    exact h.not_signQueried ⟨x, hx, s, hr⟩


variable (PS adm) in
/-- The output of an adversary of the insider game of `ofBase B PS adm`. -/
abbrev Output : Type :=
  KeyRing (ofBase B PS adm).PK N × (ofBase B PS adm).Msg × (ofBase B PS adm).Sig

variable (B PS adm) in
/-- **The relation of the relayed proof queries** for statements read at `stmt` (a program's
statements) and witnesses decoded by `fw`: `relH` on the statement of the relayed ring statement and
the decoded witness. -/
abbrev relZ {X₀ Wit₀ W' : Type} (stmt : RingStmt B → X₀) (fw : W' → Wit₀)
    (relH : Set (X₀ × Wit₀)) : RelayStmt B PS adm n → W' → Prop :=
  fun x w => (stmt x.1, fw w) ∈ relH

variable (B adm) in
/-- **The hypotheses on a proof system read at a program's statements** (`Ring.spbcsComapProofSystem`
with the statement map `stmt`, the check `check` and the honest inputs `input`), for the
zero-knowledge route, with the relayed witnesses encoded in `W'` by the partial encoding `enc` and
decoded by `fw`, the relation `relH` of zero knowledge and the relation `rel` of knowledge soundness
with the ring witness `wit` of its witnesses: `stmt` is injective; a ring witness has an encoding,
its honest input is the decoded encoding, and that is a witness of `relH`; no statement of the empty
ring has a witness of `relH`; a witness of `rel` at a checked statement gives a ring witness. The
ring relation is read at the zero oracle (the same at every oracle for an oracle-free base signer,
`BaseSigner.OracleFree.ringRel_eq`). -/
structure ZKRingHyps [AddGroup Y] {X₀ Wit₀ W' WitK : Type} (stmt : RingStmt B → X₀)
    (check : RingStmt B → Bool) (input : RingStmt B → RingWit B → Option Wit₀) (fw : W' → Wit₀)
    (enc : RingStmt B → RelayWit B → Option W') (relH : Set (X₀ × Wit₀)) (rel : Set (X₀ × WitK))
    (wit : RingStmt B → WitK → RingWit B) : Prop where
  /-- The statement map is injective. -/
  stmt_injective : Function.Injective stmt
  /-- A ring witness has an encoding; its honest input is the decoded encoding, a witness of
  `relH`. -/
  enc_some : ∀ x (w : RelayWit B), (x, w.toWit) ∈ ringRel B adm 0 →
    ∃ y, enc x w = some y ∧ input x w.toWit = some (fw y) ∧ (stmt x, fw y) ∈ relH
  /-- No statement of the empty ring has a witness of `relH`. -/
  not_mem_relH_nil : ∀ x : RingStmt B, x.ring.1 = [] → ∀ y, (stmt x, y) ∉ relH
  /-- A witness of `rel` at a checked statement gives a ring witness. -/
  sound : ∀ x w, check x = true → (stmt x, w) ∈ rel → (x, wit x w) ∈ ringRel B adm 0

variable (B adm) in
/-- **The hypotheses of the zero-knowledge step with a total encoding** `enc` (`ZKRingHyps` with
`enc` defined everywhere): `stmt` is injective; a ring witness's honest input is its encoding, and
it is a witness of `relH`; no statement of the empty ring has a witness of `relH`. -/
structure ZKRingHypsAt [AddGroup Y] {X₀ Wit₀ W' : Type} (stmt : RingStmt B → X₀)
    (input : RingStmt B → RingWit B → Option Wit₀) (fw : W' → Wit₀)
    (enc : RingStmt B → RelayWit B → W') (relH : Set (X₀ × Wit₀)) : Prop where
  /-- The statement map is injective. -/
  stmt_injective : Function.Injective stmt
  /-- A ring witness's honest input is its encoding. -/
  input_eq : ∀ x (w : RelayWit B), (x, w.toWit) ∈ ringRel B adm 0 →
    input x w.toWit = some (fw (enc x w))
  /-- A ring witness's encoding is a witness of `relH`. -/
  mem_relH : ∀ x (w : RelayWit B), (x, w.toWit) ∈ ringRel B adm 0 → (stmt x, fw (enc x w)) ∈ relH
  /-- No statement of the empty ring has a witness of `relH`. -/
  not_mem_relH_nil : ∀ x : RingStmt B, x.ring.1 = [] → ∀ y, (stmt x, y) ∉ relH

/-- **A partial encoding read with a default**: `enc x w`, or `d` where `enc` has no value. -/
def encWith {W' : Type} (enc : RingStmt B → RelayWit B → Option W') (d : W') :
    RingStmt B → RelayWit B → W' :=
  fun x w => (enc x w).getD d

omit [DecidableEq TS.PK] in
/-- **The hypotheses with a partial encoding give those with the encoding read with any default**
(`encWith`). -/
theorem ZKRingHyps.at [AddGroup Y] {X₀ Wit₀ W' WitK : Type} {stmt : RingStmt B → X₀}
    {check : RingStmt B → Bool} {input : RingStmt B → RingWit B → Option Wit₀} {fw : W' → Wit₀}
    {enc : RingStmt B → RelayWit B → Option W'} {relH : Set (X₀ × Wit₀)} {rel : Set (X₀ × WitK)}
    {wit : RingStmt B → WitK → RingWit B} (hz : ZKRingHyps B adm stmt check input fw enc relH rel wit)
    (d : W') : ZKRingHypsAt B adm stmt input fw (encWith enc d) relH where
  stmt_injective := hz.stmt_injective
  input_eq x w h := by
    obtain ⟨y, hy, hi, -⟩ := hz.enc_some x w h
    simp only [encWith, hy, Option.getD_some, hi]
  mem_relH x w h := by
    obtain ⟨y, hy, -, hr⟩ := hz.enc_some x w h
    simpa only [encWith, hy, Option.getD_some] using hr
  not_mem_relH_nil := hz.not_mem_relH_nil

omit [DecidableEq TS.PK] in
/-- **Without an encoding type, the ring relation is empty** (`ZKRingHyps.enc_some`). -/
theorem ZKRingHyps.not_mem_ringRel [AddGroup Y] {X₀ Wit₀ W' WitK : Type} {stmt : RingStmt B → X₀}
    {check : RingStmt B → Bool} {input : RingStmt B → RingWit B → Option Wit₀} {fw : W' → Wit₀}
    {enc : RingStmt B → RelayWit B → Option W'} {relH : Set (X₀ × Wit₀)} {rel : Set (X₀ × WitK)}
    {wit : RingStmt B → WitK → RingWit B} (hz : ZKRingHyps B adm stmt check input fw enc relH rel wit)
    (hW : IsEmpty W') (x : RingStmt B) (w : RelayWit B) : (x, w.toWit) ∉ ringRel B adm 0 := fun h =>
  hW.false (hz.enc_some x w h).choose

omit [DecidableEq TS.PK] in
variable (B adm) in
/-- **The hypotheses of the zero-knowledge route hold for the identity reading of ring
statements** (`spbcsProofSystem`, `Ring.spbcsComapProofSystem` at `stmt = id`, no check and the
witness as its own honest input), with the relayed witnesses as themselves, both relations the ring
relation and its witnesses as their own ring witnesses: `ZKRingHyps` is satisfiable. -/
theorem zkRingHyps_id [AddGroup Y] :
    ZKRingHyps B adm id (fun _ => true) (fun _ w => some w) RelayWit.toWit (fun _ w => some w)
      (ringRel B adm 0) (ringRel B adm 0) (fun _ w => w) where
  stmt_injective := Function.injective_id
  enc_some _ w h := ⟨w, rfl, rfl, h⟩
  not_mem_relH_nil x hx y h := by
    have hl : y.idx < x.ring.1.length := RingRel.idx_lt h
    rw [hx] at hl
    exact Nat.not_lt_zero _ hl
  sound _ _ _ h := h

end RingSignature.Insider

/-! ### The forgery test and the distinguisher of zero knowledge -/

namespace RingSignature.Insider

open GordieHowe.QROM GordieHowe.SPBCS IOP SPTerm

section SPBCS

variable {k kN kS L e N n t : ℕ} {TS : Signature.SchemeTypes} {RMsg : Type} [DecidableEq TS.PK]
  {B : BaseSigner (Bits (queryBits k kN kS L)) (XOut k e) N TS RMsg}
  {ι : Type} {τ : SPTerm ι} {Mg : Merges τ} {nr : ι → ℕ}
  {P : (j : ι) → ProtocolSpec (nr j)} [∀ j i, Fintype ((P j).Challenge i)]
  [∀ j i, DecidableEq ((P j).Challenge i)] [∀ j i, Nonempty ((P j).Challenge i)]
  {X₀ Wit₀ : Type} (M : SPBCS Mg P X₀ k kN kS L e) (Λ : SiteLayout Mg) {b : ℕ}
  [∀ j i, Fintype ((M.comp j).MessageWrite i)] (E : (j : ι) → (M.comp j).Encoder)
  {Vr : X₀ → FullTr P τ → Bool} {Qs : ∀ x, M.IOPQueries Vr x}
  (hb : M.FormatBounds Qs b b) {R : Type} [Fintype R] [DecidableEq R] [Nonempty R]
  (honest : Wit₀ → R → CausalProver P τ X₀) (stmt : RingStmt B → X₀) (check : RingStmt B → Bool)
  (input : RingStmt B → RingWit B → Option Wit₀)
  (adm : KeyRing B.PK N → Prop) [DecidablePred adm] {W' : Type} [Fintype W'] [DecidableEq W']
  [Nonempty W'] (fw : W' → Wit₀) (enc : RingStmt B → RelayWit B → W')
  {relH : Set (X₀ × Wit₀)} {WitK : Type} {rel : Set (X₀ × WitK)} {wit : RingStmt B → WitK → RingWit B}

local notation "𝒫" => Ring.spbcsComapProofSystem M Λ E hb honest stmt check input

/-- **The compiled honest prover at the program's statements**: the spBCS prover `niProver` with
proofs in the format `b`, run through `queryEncoding`. -/
abbrev encProver :
    NARG.Prover (Bits (queryBits k kN kS L)) (XOut k e) X₀ Wit₀ (M.Response b)
      (SaltedCoins (FiatShamirSalt kS) (M.ProverCoins R)) :=
  ((M.niProver Λ honest E hb).mapOutput some).encode queryEncoding

local notation "𝒫z" => encProver M Λ E hb honest

variable {M Λ E hb honest stmt check input adm fw enc}

/-- **The adversary wins with a nonempty ring** at the key coins `keys`, the output `o`, the
requests `rs` and the oracle `G` (read as bytes): the forgery's statement passes the check, the
compiled verifier accepts its claim, it is fresh at the first `Q` requests, and its ring is
nonempty. -/
def Wins (keys : Fin n → B.KeyCoins) (Q : ℕ) (o : Output 𝒫 adm)
    (rs : List (Req B 𝒫 adm n)) (G : Bits (queryBits k kN kS L) → Out k e) : Prop :=
  check ⟨o.1, o.2.1, o.2.2.1⟩ = true ∧
    (∃ c ∈ Ring.spbcsComapClaim M stmt (⟨o.1, o.2.1, o.2.2.1⟩ : RingStmt B) o.2.2.2,
      (M.qVerifier Qs b b).Accepted G c) ∧
    FreshAt keys (rs.take Q) o.1 o.2.1 ∧ o.1.1 ≠ []

open Classical in
/-- **The test of a forgery** at the key coins `keys`: the compiled verifier's program on the claim
of the forgery (its `kq` queries, answers read through `outEquiv`), then whether its statement passes
the check and it is fresh at the first `Q` requests with a nonempty ring; `false` without a proof.

Running time: the verifier's `kq` queries and decision, and a scan of the ring and of the requests.
This running time is argued here, not proved in Lean. -/
noncomputable def forgeryTest (keys : Fin n → B.KeyCoins) (Q : ℕ) (o : Output 𝒫 adm)
    (rs : List (Req B 𝒫 adm n)) : OracleProg (Bits (queryBits k kN kS L)) (XOut k e) Bool :=
  match Ring.spbcsComapClaim M stmt (⟨o.1, o.2.1, o.2.2.1⟩ : RingStmt B) o.2.2.2 with
  | none => .pure false
  | some c => (((M.qVerifier Qs b b).prog c).mapQuery id (outEquiv k e)).bind fun r =>
      .pure (r && decide (check ⟨o.1, o.2.1, o.2.2.1⟩ = true ∧ FreshAt keys (rs.take Q) o.1 o.2.1 ∧
        o.1.1 ≠ []))

omit [∀ j i, Fintype ((M.comp j).MessageWrite i)] [Fintype R] [DecidableEq R] [Nonempty R] in
/-- The test makes at most the verifier's `kq` queries. -/
theorem forgeryTest_queriesLE (keys : Fin n → B.KeyCoins) (Q : ℕ) (o : Output 𝒫 adm)
    (rs : List (Req B 𝒫 adm n)) :
    (forgeryTest keys Q o rs).QueriesLE (M.qVerifier Qs b b).kq := by
  intro G
  unfold forgeryTest
  split
  · simp
  · simp only [OracleProg.trace_bind, OracleProg.trace_pure, List.append_nil,
      OracleProg.length_trace_mapQuery]
    exact NARG.Verifier.prog_queriesLE _ _ _

omit [∀ j i, Fintype ((M.comp j).MessageWrite i)] [Fintype R] [DecidableEq R] [Nonempty R] in
/-- **The test accepts exactly on a win.** -/
theorem run_forgeryTest (keys : Fin n → B.KeyCoins) (Q : ℕ) (o : Output 𝒫 adm)
    (rs : List (Req B 𝒫 adm n)) (G : Bits (queryBits k kN kS L) → XOut k e) :
    (forgeryTest keys Q o rs).run G = true ↔ Wins keys Q o rs (outEquiv k e ∘ G) := by
  classical
  unfold forgeryTest Wins
  split
  · next h => simp [h]
  · next c h =>
    rw [OracleProg.run_bind, OracleProg.run_mapQuery]
    simp only [OracleProg.run_pure, Bool.and_eq_true, decide_eq_true_eq, NARG.Verifier.run_prog, h,
      Option.mem_def, Option.some.injEq, exists_eq_left']
    tauto

variable [Nonempty TS.KeyCoins]

variable [Fintype TS.PK] [Fintype RMsg] [DecidableEq RMsg] [Fintype TS.BSig]
  [DecidableEq TS.BSig] [Fintype TS.Pub] [DecidableEq TS.Pub] [Fintype TS.KeyCoins]
  [DecidableEq TS.KeyCoins] [Fintype TS.Coins] [DecidableEq TS.Coins] [Nonempty TS.Coins]

variable (A : InsiderAdversary (ofBase B (Ring.spbcsComapProofSystem M Λ E hb honest stmt check input) adm) n
    (OracleView.queriesOnly (Bits (queryBits k kN kS L)) (XOut k e)) t)

variable [Nonempty B.Msg] [Nonempty B.Pub] [Nonempty B.BSig]

/-- A relayed proof query, the blank main request of the absorbed adversaries. -/
noncomputable instance instInhabitedProofQuery [NeZero n] :
    Inhabited (ProofQuery (RelayStmt B 𝒫 adm n) W') :=
  ⟨⟨(dummyStmt B, .corrupt 0), Classical.arbitrary _⟩⟩

/-- A relayed statement, the blank main request of the absorbed adversaries. -/
noncomputable instance instInhabitedRelayStmt [NeZero n] : Inhabited (RelayStmt B 𝒫 adm n) :=
  ⟨(dummyStmt B, .corrupt 0)⟩

/-- **The adversary with its requests absorbed into proof queries** (`zkRelay`) at the key coins
`keys`, the auxiliary value `a` and the signing coins `ds`. -/
noncomputable abbrev zkAbsorbed [NeZero n] (enc : RingStmt B → RelayWit B → W')
    (refuses : KeyRing B.PK N → ℕ → B.Msg → B.Coins → Prop) (pubOf : B.Coins → B.Pub)
    (keys : Fin n → B.KeyCoins) (Q : ℕ) (a : (A.at keys).Aux)
    (ds : Fin Q → B.Coins) :
    AdaptiveIAlg (((A.at keys).sh a).absorbS (Req' := ProofQuery (RelayStmt B 𝒫 adm n) W')
      (Resp' := (𝒫).Proof)) (Output 𝒫 adm) :=
  AdaptiveIAlg.absorb (Req' := ProofQuery (RelayStmt B 𝒫 adm n) W') (Resp' := (𝒫).Proof)
    ((A.at keys).alg a) (zkRelay B enc keys refuses pubOf ds)

/-- **The forgery test on an absorbed workspace**: `forgeryTest` at its output and its logged
requests. -/
noncomputable abbrev zkTest [NeZero n] (enc : RingStmt B → RelayWit B → W')
    (refuses : KeyRing B.PK N → ℕ → B.Msg → B.Coins → Prop) (pubOf : B.Coins → B.Pub)
    (keys : Fin n → B.KeyCoins) (Q : ℕ) (a : (A.at keys).Aux)
    (ds : Fin Q → B.Coins) (w : (zkAbsorbed A enc refuses pubOf keys Q a ds).W) :
    OracleProg (Bits (queryBits k kN kS L)) (XOut k e) Bool :=
  forgeryTest keys Q (((A.at keys).alg a).out w.work) (Quantum.requests w.logs)

/-- **The distinguisher of zero knowledge** at the key coins `keys`, the auxiliary value `a` and the
signing coins `ds`: the adversary with its requests absorbed (`zkAbsorbed`: proof queries with the
signers' witnesses), followed by the forgery test (`zkTest`).

Running time: that of the adversary, plus the relay of each request (at most one base signature)
and `forgeryTest`. This running time is argued here, not proved in Lean. -/
noncomputable def distinguisher [NeZero n] (enc : RingStmt B → RelayWit B → W')
    (refuses : KeyRing B.PK N → ℕ → B.Msg → B.Coins → Prop) (pubOf : B.Coins → B.Pub)
    (keys : Fin n → B.KeyCoins) (Q : ℕ)
    (a : (A.at keys).Aux) (ds : Fin Q → B.Coins) :
    QueryBoundedAdversary (Bits (queryBits k kN kS L)) (XOut k e)
      (ProofQuery (RelayStmt B 𝒫 adm n) W') (𝒫).Proof Bool
      (((A.at keys).alg a).width * (((A.at keys).alg a).budget + ((A.at keys).alg a).post) +
        ((A.at keys).alg a).width * (M.qVerifier Qs b b).kq) where
  Aux := Unit
  aux := PMF.pure ()
  sh _ := (((A.at keys).sh a).absorbS (Req' := ProofQuery (RelayStmt B 𝒫 adm n) W')
    (Resp' := (𝒫).Proof)).thenProgS (M.qVerifier Qs b b).kq
  alg _ := (zkAbsorbed A enc refuses pubOf keys Q a ds).thenProg (zkTest A enc refuses pubOf keys Q a ds)
    (M.qVerifier Qs b b).kq fun _ => forgeryTest_queriesLE keys Q _ _
  tracePreserving _ := AdaptiveIAlg.thenProg_tracePreserving (zkAbsorbed A enc refuses pubOf keys Q a ds)
    (zkTest A enc refuses pubOf keys Q a ds) (M.qVerifier Qs b b).kq
    (fun _ => forgeryTest_queriesLE keys Q _ _)
    (AdaptiveIAlg.absorb_tracePreserving ((A.at keys).alg a) (zkRelay B enc keys refuses pubOf ds)
      ((A.at keys).tracePreserving a))
  withinBudget _ := AdaptiveIAlg.withinBudget_thenProg (zkAbsorbed A enc refuses pubOf keys Q a ds)
    (zkTest A enc refuses pubOf keys Q a ds) (M.qVerifier Qs b b).kq
    (fun _ => forgeryTest_queriesLE keys Q _ _)
    (AdaptiveIAlg.absorb_withinBudget ((A.at keys).alg a) (zkRelay B enc keys refuses pubOf ds)
      (zkRelay_route_injective B enc keys refuses pubOf ds) ((A.at keys).withinBudget a))
  queries_le _ := (AdaptiveIAlg.thenProg_queries (zkAbsorbed A enc refuses pubOf keys Q a ds)
    (zkTest A enc refuses pubOf keys Q a ds) (M.qVerifier Qs b b).kq
    (fun _ => forgeryTest_queriesLE keys Q _ _)).le

/-! ### Real to simulated ring signatures -/

variable {refuses : KeyRing B.PK N → ℕ → B.Msg → B.Coins → Prop} {pubOf : B.Coins → B.Pub}

omit [Nonempty W'] [∀ j i, Fintype ((M.comp j).MessageWrite i)] [Fintype R] [DecidableEq R]
  [Nonempty R] [Fintype TS.PK] [DecidableEq TS.PK] [Fintype RMsg] [DecidableEq RMsg]
  [Fintype TS.Pub] [DecidableEq TS.Pub] [Fintype TS.KeyCoins] [DecidableEq TS.KeyCoins]
  [Nonempty TS.KeyCoins] [Fintype TS.BSig] [DecidableEq TS.BSig] [Fintype TS.Coins]
  [DecidableEq TS.Coins] [Nonempty TS.Coins] in
/-- **On a ring witness the ring prover is the compiled prover at the encoded honest input.** -/
theorem prove_eq_of_hyps (hz : ZKRingHypsAt B adm stmt input fw enc relH)
    (x : RingStmt B) (w : RelayWit B) (c : (𝒫).Coins) (h : (x, w.toWit) ∈ ringRel B adm 0) :
    (𝒫z).prog (stmt x) (fw (enc x w)) c = (𝒫).prove x w.toWit c := by
  change _ = (input x w.toWit).elim (.pure none) (fun y => (𝒫z).prog (stmt x) y c)
  rw [hz.input_eq x w h]
  rfl

open Classical in
omit [Fintype TS.BSig] [DecidableEq TS.BSig] [Nonempty TS.KeyCoins] in
/-- **The insider game at fixed keys is at most the average, over the signing coins, of the
distinguisher against the real challenger of the compiled prover at the program's statements, plus
`Q · εc`**, at each auxiliary value and each oracle, for an oracle-free base signer (`hB`) with
correctness error `εc` (`hcorr`), public values `pubOf` of the coins (`hpub`) and refusing whenever
`refuses` predicts it (`hsound`), under the hypotheses `hz` on the program's statements and inputs: the
game's replies are replaced by the checked
ones (`game_le_checked`), and the checked game relays the real challenger (`relays_real`,
`AdaptiveIAlg.outLaw_absorb`), the forgery test reading the win off the absorbed workspace. -/
theorem game_le_sum_real [NeZero n] (hB : B.OracleFree) (hpub : B.PubOfCoins pubOf)
    (hsound : B.RefusalSound refuses) (hz : ZKRingHypsAt B adm stmt input fw enc relH)
    {εc : ℝ≥0∞} (hcorr : B.CorrectWithin εc)
    (keys : Fin n → B.KeyCoins) (Q : ℕ) (a : (A.at keys).Aux)
    (H : Bits (queryBits k kN kS L) → XOut k e) :
    ((((A.at keys).alg a).toKindAlg.composeBothOut
        (unforgeChallenger (ofBase B 𝒫 adm) n (SideOracle.none _) keys Q) id).outLaw H).toOuterMeasure
        {o | ∃ v ∈ o, Wins keys Q (((A.at keys).alg a).out v.adv.workspace.1)
          (Quantum.requests v.chal.logs) (outEquiv k e ∘ H)} ≤
      ∑ ds, PMF.uniformOfFintype (Fin Q → B.Coins) ds *
        (((distinguisher A enc refuses pubOf keys Q a ds).alg ()).compose
          (realChallenger (relZ B 𝒫 adm stmt fw relH) ((𝒫z).comap (stmt ∘ Prod.fst) fw) (PMF.uniformOfFintype _) Q)).outLaw H
          (some true) + Q * εc := by
  rw [toOuterMeasure_outLaw_unforge_eq_split (ofBase B 𝒫 adm) n (SideOracle.none _)
    ((A.at keys).alg a).toKindAlg keys Q H fun adv lg =>
      Wins keys Q (((A.at keys).alg a).out adv.workspace.1) (Quantum.requests lg) (outEquiv k e ∘ H)]
  refine (game_le_checked hcorr ((A.at keys).alg a).toKindAlg keys Q H fun adv lg =>
      Wins keys Q (((A.at keys).alg a).out adv.workspace.1) (Quantum.requests lg)
        (outEquiv k e ∘ H)).trans (add_le_add (le_of_eq ?_) le_rfl)
  have h := ((A.at keys).alg a).outLaw_absorb (σ := PMF.uniformOfFintype (Fin Q → B.Coins))
    (F' := fun ds => zkRelay B enc keys refuses pubOf ds) (C := (checkedSplit 𝒫 adm keys Q).toChallenger)
    (C' := realChallenger (relZ B 𝒫 adm stmt fw relH) ((𝒫z).comap (stmt ∘ Prod.fst) fw) (PMF.uniformOfFintype _) Q)
    (e := coinSplit Q B.Coins (𝒫).Coins) (fun s c' => coins_checkedSplit (PS := 𝒫) (adm := adm) keys Q s c')
    (fun H s c' => (relays_real (PS := 𝒫) (adm := adm) hB hpub hsound stmt fw enc hz.mem_relH hz.not_mem_relH_nil (𝒫z)
      (fun x w c h => prove_eq_of_hyps hz x w c h) keys s c').relays H _)
    (fun s c => zkRelay_route_injective B enc keys refuses pubOf s c) H
    (fun adv lg _ _ _ =>
      Wins keys Q (((A.at keys).alg a).out adv.workspace.1) (Quantum.requests lg) (outEquiv k e ∘ H))
  refine h.trans (Finset.sum_congr rfl fun ds _ => ?_)
  congr 1
  change _ = (((zkAbsorbed A enc refuses pubOf keys Q a ds).thenProg (zkTest A enc refuses pubOf keys Q a ds)
    (M.qVerifier Qs b b).kq fun _ => forgeryTest_queriesLE keys Q _ _).compose _).outLaw H (some true)
  rw [AdaptiveIAlg.outLaw_thenProg]
  have hnil := KindAlg.postAss_eq_nil (zkAbsorbed A enc refuses pubOf keys Q a ds).toKindAlg
    (realChallenger (relZ B 𝒫 adm stmt fw relH) ((𝒫z).comap (stmt ∘ Prod.fst) fw) (PMF.uniformOfFintype _) Q)
    (QROM.outWith_realChallenger_assignments _ _ _ Q)
  congr 2
  ext o
  simp only [hnil, run_forgeryTest]
  constructor
  · rintro ⟨v, rfl, hv⟩
    exact ⟨v, rfl, hv⟩
  · rintro ⟨v, rfl, hv⟩
    exact ⟨v, rfl, hv⟩

omit [Fintype R] [DecidableEq R] [Nonempty R] [Fintype TS.BSig] [DecidableEq TS.BSig]
  [Fintype TS.Coins] [DecidableEq TS.Coins] [Nonempty TS.Coins] [Nonempty TS.KeyCoins] in
/-- **The acceptance probability of a distinguisher** is the oracle average of its output law at
`true`. -/
theorem acceptProb_distinguisher [NeZero n] (keys : Fin n → B.KeyCoins) (Q : ℕ) (a : (A.at keys).Aux)
    (ds : Fin Q → B.Coins)
    (C : Challenger (Bits (queryBits k kN kS L)) (XOut k e)
      (ProofQuery (RelayStmt B 𝒫 adm n) W') (𝒫).Proof) :
    (distinguisher A enc refuses pubOf keys Q a ds).acceptProb C =
      ∑' H, PMF.uniformOfFintype (Bits (queryBits k kN kS L) → XOut k e) H *
        (((distinguisher A enc refuses pubOf keys Q a ds).alg ()).compose C).outLaw H (some true) := by
  simp only [QueryBoundedAdversary.acceptProb, distinguisher]
  rw [tsum_eq_single () fun u hu => absurd (Subsingleton.elim u ()) hu]
  erw [PMF.pure_apply_self, one_mul]
  rw [Alg.realLaw, PMF.toOuterMeasure_bind_apply]
  refine tsum_congr fun H => ?_
  congr 1
  rw [PMF.toOuterMeasure_map_apply]
  have : (fun o => (⟨o, Equiv.refl _ ∘ H⟩ :
      Outcome (Option Bool) (Bits (queryBits k kN kS L)) (XOut k e))) ⁻¹'
      {p | p.out = some true} = {some true} := by
    ext o
    simp
  rw [this, PMF.toOuterMeasure_apply_singleton]

omit [Fintype R] [DecidableEq R] [Nonempty R] [Fintype TS.BSig] [DecidableEq TS.BSig]
  [Fintype TS.Coins] [DecidableEq TS.Coins] [Nonempty TS.Coins] [Nonempty TS.KeyCoins] in
/-- The acceptance probability of a distinguisher is at most `1`. -/
theorem acceptProb_distinguisher_le_one [NeZero n] (keys : Fin n → B.KeyCoins) (Q : ℕ)
    (a : (A.at keys).Aux) (ds : Fin Q → B.Coins)
    (C : Challenger (Bits (queryBits k kN kS L)) (XOut k e)
      (ProofQuery (RelayStmt B 𝒫 adm n) W') (𝒫).Proof) :
    (distinguisher A enc refuses pubOf keys Q a ds).acceptProb C ≤ 1 := by
  rw [acceptProb_distinguisher]
  calc _ ≤ ∑' H, PMF.uniformOfFintype (Bits (queryBits k kN kS L) → XOut k e) H * 1 :=
        ENNReal.tsum_le_tsum fun H => mul_le_mul_of_nonneg_left (PMF.coe_le_one _ _) zero_le
    _ = 1 := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

open Classical in
omit [Fintype TS.BSig] [DecidableEq TS.BSig] [Fintype TS.Coins] [DecidableEq TS.Coins]
  [Nonempty TS.Coins] [Nonempty TS.KeyCoins] in
/-- **Zero knowledge at one key, one auxiliary value and one draw of signing coins**: the
distinguisher accepts against the real challenger with probability at most its acceptance against
the simulated challenger of the spBCS joint simulator plus `zkError δ t Q`
(`SPBCS.everlastingZeroKnowledge_qrom` at the statements `stmt` of the relayed ring statements and
the decoded witnesses `fw`), for a composite that is honest-verifier zero knowledge for `relH`
(`hvzk`). -/
theorem acceptProb_real_le [NeZero n] (VE : M.ViewEncoder E Qs) {Pub : Type}
    (pub : X₀ → Pub) (Sim : CausalJointSimulator VE.MV Pub) (T : M.Preimages) {δ : NNReal}
    (hvzk : CausalHVZK VE.MV relH honest pub Sim δ) (keys : Fin n → B.KeyCoins) (Q : ℕ)
    (a : (A.at keys).Aux) (ds : Fin Q → B.Coins) :
    (distinguisher A enc refuses pubOf keys Q a ds).acceptProb
        (realChallenger (relZ B 𝒫 adm stmt fw relH) ((𝒫z).comap (stmt ∘ Prod.fst) fw) (PMF.uniformOfFintype _) Q) ≤
      (distinguisher A enc refuses pubOf keys Q a ds).acceptProb
          (simChallenger (relZ B 𝒫 adm stmt fw relH)
            ((M.niJointSimulatorProg Λ VE.toViewRead b pub Sim T).comap (stmt ∘ Prod.fst)) Q) +
        ENNReal.ofReal (M.zkError δ t Q) := by
  have hzk := M.everlastingZeroKnowledge_qrom Λ honest E VE hb T
    (stmt ∘ Prod.fst : RelayStmt B 𝒫 adm n → X₀) fw hvzk
  unfold NARG.QROM.EverlastingZeroKnowledge at hzk
  rw [NARG.Prover.mapOutput_comap, NARG.Prover.encode_comap, NARG.Simulator.encode_comap,
    M.encode_niSimulator Λ E VE hb] at hzk
  have hD : (distinguisher A enc refuses pubOf keys Q a ds).QueriesBeforeLastProofQuery t := fun _ =>
    ⟨((A.at keys).alg a).budget,
      (Nat.mul_le_mul_left _ (Nat.le_add_right _ _)).trans ((A.at keys).queries_le a),
      AdaptiveIAlg.requestsAfterAtMost_thenProg (zkAbsorbed A enc refuses pubOf keys Q a ds)
        (zkTest A enc refuses pubOf keys Q a ds) _ fun _ => forgeryTest_queriesLE keys Q _ _⟩
  have key : ∀ x y : ℝ≥0∞, x ≤ 1 → y ≤ 1 →
      GordieHowe.advantage x.toReal y.toReal ≤ M.zkError δ t Q →
      x ≤ y + ENNReal.ofReal (M.zkError δ t Q) := fun x y hx hy h => by
    have h' : |x.toReal - y.toReal| ≤ M.zkError δ t Q := h
    have hz : 0 ≤ M.zkError δ t Q := (abs_nonneg _).trans h'
    have hr : x.toReal ≤ y.toReal + M.zkError δ t Q := by
      linarith [le_abs_self (x.toReal - y.toReal)]
    rw [← ENNReal.ofReal_toReal (ne_top_of_le_ne_top ENNReal.one_ne_top hx),
      ← ENNReal.ofReal_toReal (ne_top_of_le_ne_top ENNReal.one_ne_top hy),
      ← ENNReal.ofReal_add ENNReal.toReal_nonneg hz]
    exact ENNReal.ofReal_le_ofReal hr
  have h := hzk t Q _ (distinguisher A enc refuses pubOf keys Q a ds) hD
  convert key _ _ (acceptProb_distinguisher_le_one A (enc := enc) keys Q a ds _)
    (acceptProb_distinguisher_le_one A (enc := enc) keys Q a ds _) h using 3
  · exact funext fun _ => funext fun _ => propext Iff.rfl
  · exact QROM.simChallenger_congr _ _ _ _ _ _ _ _ (fun _ _ => Iff.rfl) _ Q

open Classical in
omit [Fintype R] [DecidableEq R] [Nonempty R] [Fintype TS.BSig] [DecidableEq TS.BSig]
  [Nonempty TS.KeyCoins] in
/-- **The side-coin average of the distinguisher against the simulated challenger is the checked
simulated game** (`simSplit` with the test `drawOkR`) at each key, auxiliary value and oracle, the
forgery read under the final oracle, for an oracle-free base signer (`hB`) whose public values are
`pubOf` of the coins (`hpub`). -/
theorem sum_sim_eq_checked [NeZero n] (hB : B.OracleFree) (hpub : B.PubOfCoins pubOf)
    (hz : ZKRingHypsAt B adm stmt input fw enc relH)
    {SC : Type} [Fintype SC] [DecidableEq SC]
    (Sim : NARG.Simulator (Bits (queryBits k kN kS L)) (XOut k e) X₀ (𝒫).Proof SC)
    (keys : Fin n → B.KeyCoins) (Q : ℕ) (a : (A.at keys).Aux)
    (H : Bits (queryBits k kN kS L) → XOut k e) :
    ∑ ds, PMF.uniformOfFintype (Fin Q → B.Coins) ds *
        (((distinguisher A enc refuses pubOf keys Q a ds).alg ()).compose
          (simChallenger (relZ B 𝒫 adm stmt fw relH) (Sim.comap (stmt ∘ Prod.fst)) Q)).outLaw H
          (some true) =
      ((((A.at keys).alg a).toKindAlg.composeBothOut
          (simSplit 𝒫 adm keys refuses pubOf (Sim.comap stmt) Q (drawOkR B keys)).toChallenger
            id).outLaw H).toOuterMeasure
        {o | ∃ v ∈ o, Wins keys Q (((A.at keys).alg a).out v.adv.workspace.1)
          (Quantum.requests v.chal.logs) (outEquiv k e ∘ H.reprogram (((A.at keys).alg a).toKindAlg.postAss
            (simSplit 𝒫 adm keys refuses pubOf (Sim.comap stmt) Q (drawOkR B keys)).toChallenger
              v.chal))} := by
  have h := ((A.at keys).alg a).outLaw_absorb (σ := PMF.uniformOfFintype (Fin Q → B.Coins))
    (F' := fun ds => zkRelay B enc keys refuses pubOf ds)
    (C := (simSplit 𝒫 adm keys refuses pubOf (Sim.comap stmt) Q (drawOkR B keys)).toChallenger)
    (C' := simChallenger (relZ B 𝒫 adm stmt fw relH) (Sim.comap (stmt ∘ Prod.fst)) Q)
    (e := coinSplit Q B.Coins SC) (fun s c' => coins_simSplit keys (Sim.comap stmt) Q _ s c')
    (fun H s c' => (relays_sim_zk (PS := 𝒫) (adm := adm) hB hpub stmt fw enc hz.mem_relH
      hz.not_mem_relH_nil keys Sim s c').relays H _)
    (fun s c => zkRelay_route_injective B enc keys refuses pubOf s c) H
    (fun adv lg _ _ G =>
      Wins keys Q (((A.at keys).alg a).out adv.workspace.1) (Quantum.requests lg) (outEquiv k e ∘ G))
  refine (Eq.trans (Finset.sum_congr rfl fun ds _ => ?_) h.symm)
  congr 1
  change ((((zkAbsorbed A enc refuses pubOf keys Q a ds).thenProg (zkTest A enc refuses pubOf keys Q a ds)
    (M.qVerifier Qs b b).kq fun _ => forgeryTest_queriesLE keys Q _ _).compose _).outLaw H
      (some true)) = _
  rw [AdaptiveIAlg.outLaw_thenProg]
  congr 2
  ext o
  simp only [run_forgeryTest]
  constructor
  · rintro ⟨v, rfl, hv⟩
    exact ⟨v, rfl, hv⟩
  · rintro ⟨v, rfl, hv⟩
    exact ⟨v, rfl, hv⟩

/-! ### Simulation extraction -/

variable [Nonempty M.NIProof]

/-- **The claim of an output** `(R, m, (y, π))`: the claim of the statement `stmt (R, m, y)` with the
proof of `π`, a claim with the same statement and an arbitrary proof when `π` has none. -/
noncomputable def claimOfOut (o : Output 𝒫 adm) : Claim X₀ M.NIProof :=
  (Ring.spbcsComapClaim M stmt (⟨o.1, o.2.1, o.2.2.1⟩ : RingStmt B) o.2.2.2).getD
    ⟨stmt ⟨o.1, o.2.1, o.2.2.1⟩, Classical.arbitrary _⟩

omit [Nonempty B.Msg] [Nonempty B.Pub] [Nonempty B.BSig]
  [∀ j i, Fintype ((M.comp j).MessageWrite i)] [Fintype R] [DecidableEq R] [Nonempty R]
  [Fintype TS.PK] [Fintype RMsg] [DecidableEq RMsg] [Fintype TS.Pub] [DecidableEq TS.Pub]
  [Fintype TS.KeyCoins] [DecidableEq TS.KeyCoins] [Nonempty TS.KeyCoins] [Fintype TS.Coins]
  [DecidableEq TS.Coins] [Nonempty TS.Coins] [Fintype TS.BSig] [DecidableEq TS.BSig] in
/-- The statement of the claim of an output is the output's statement. -/
theorem claimOfOut_stmt (o : Output 𝒫 adm) :
    (claimOfOut o).stmt = stmt (⟨o.1, o.2.1, o.2.2.1⟩ : RingStmt B) := by
  unfold claimOfOut
  cases h : Ring.spbcsComapClaim M stmt (⟨o.1, o.2.1, o.2.2.1⟩ : RingStmt B) o.2.2.2 with
  | none => rfl
  | some c =>
    exact Ring.stmt_of_mem_spbcsComapClaim (Qs := Qs) (b := b) M stmt (Option.mem_def.2 h)

/-- **The adversary of the simulation-extraction game** at the key coins `keys`, the auxiliary
value `a` and the signing coins `ds`: the adversary with its requests absorbed into statements
(`seTwo`: the public keys, the refusals and public values of the coins, no secret key), the
corrupted users' key coins read from a table of outer replies (`AdaptiveIAlg.absorbTab`, a
classical register written once at initialization), its output read as a claim (`claimOfOut`).
Against every challenger it has the law of the adversary absorbed through `seRelay` at the key
coins (`seTwo_atC`, `AdaptiveIAlg.toOuterMeasure_outLaw_absorbTab_const`). -/
noncomputable abbrev seAlg [NeZero n] (refuses : KeyRing B.PK N → ℕ → B.Msg → B.Coins → Prop)
    (pubOf : B.Coins → B.Pub) (keys : Fin n → B.KeyCoins) (Q : ℕ) (a : (A.at keys).Aux)
    (ds : Fin Q → B.Coins) :=
  (AdaptiveIAlg.absorbTab (Req₁ := RelayStmt B 𝒫 adm n) (Resp₁ := (𝒫).Proof) ((A.at keys).alg a)
    (seTwo B (fun i => B.pk (keys i)) refuses pubOf ds) (fun _ => keyReply B keys)).mapOut
    claimOfOut

/-- **The query-bounded adversary of the simulation-extraction game** at the key coins `keys` and
the signing coins `ds`: `seAlg` on each auxiliary value. -/
noncomputable def seAdversary [NeZero n] (refuses : KeyRing B.PK N → ℕ → B.Msg → B.Coins → Prop)
    (pubOf : B.Coins → B.Pub) (keys : Fin n → B.KeyCoins) (Q : ℕ) (ds : Fin Q → B.Coins) :
    M.QBSimExtractionAdversary b (RelayStmt B 𝒫 adm n) t where
  Aux := (A.at keys).Aux
  aux := (A.at keys).aux
  sh a := ((A.at keys).sh a).absorbTabS (Signature.MURequest (Signature.SignOracle.ring B) n)
    (Signature.MUResponse B.core)
  alg a := seAlg A refuses pubOf keys Q a ds
  tracePreserving a := AdaptiveIAlg.mapOut_tracePreserving
    (AdaptiveIAlg.absorbTab_tracePreserving _ _ ((A.at keys).tracePreserving a) _) _
  withinBudget a := AdaptiveIAlg.mapOut_withinBudget
    (AdaptiveIAlg.absorbTab_withinBudget ((A.at keys).alg a)
      (seTwo B (fun i => B.pk (keys i)) refuses pubOf ds) (b := fun _ => keyReply B keys)
      (fun lg j _ q _ _ => AdaptiveIAlg.tabAt_outerCount_const _ _ _ lg j q)
      (fun _ _ _ h => congrArg Prod.snd h) ((A.at keys).withinBudget a)) _
  queries_le a := (A.at keys).queries_le a


/-- **The test of the simulation-extraction game** at the key coins `keys`: the forgery carries a
proof, its statement passes the check, and every key of its ring is the key of a user without a
corruption request among the first `Q` logged requests. -/
def okAt [NeZero n] (refuses : KeyRing B.PK N → ℕ → B.Msg → B.Coins → Prop)
    (pubOf : B.Coins → B.Pub) (keys : Fin n → B.KeyCoins) (Q : ℕ) (a : (A.at keys).Aux)
    (ds : Fin Q → B.Coins) (w : (seAlg A refuses pubOf keys Q a ds).W) : Prop :=
  (Ring.spbcsComapClaim M stmt (⟨(((A.at keys).alg a).out w.1.work).1, (((A.at keys).alg a).out w.1.work).2.1,
      (((A.at keys).alg a).out w.1.work).2.2.1⟩ : RingStmt B)
      (((A.at keys).alg a).out w.1.work).2.2.2).isSome ∧
    check ⟨(((A.at keys).alg a).out w.1.work).1, (((A.at keys).alg a).out w.1.work).2.1,
      (((A.at keys).alg a).out w.1.work).2.2.1⟩ = true ∧
    ∀ pk ∈ (((A.at keys).alg a).out w.1.work).1.1, ∃ i, B.pk (keys i) = pk ∧
      UnforgeRequest.corrupt i ∉ (Quantum.requests w.1.logs).take Q

omit [Nonempty M.NIProof] [Nonempty B.BSig] [∀ j i, Fintype ((M.comp j).MessageWrite i)] [Fintype R]
  [DecidableEq R] [Nonempty R] [Fintype TS.PK] [Fintype RMsg] [DecidableEq RMsg]
  [Fintype TS.BSig] [DecidableEq TS.BSig] [Fintype TS.Pub] [DecidableEq TS.Pub] [Fintype TS.Coins]
  [DecidableEq TS.Coins] [Nonempty TS.Coins] [Fintype TS.KeyCoins] [DecidableEq TS.KeyCoins]
  [Nonempty TS.KeyCoins] in
/-- **The relayed statements of the first `Q` requests differ from a fresh statement with a
nonempty ring**: each is `dummyStmt`, with the empty ring, or the statement of a ring-signing
request among the first `Q`, which freshness separates from it. -/
theorem relayed_ne_of_fresh (pkOf : Fin n → B.PK) (kcOf : Fin n → B.KeyCoins) {Q : ℕ}
    (ds : Fin Q → B.Coins) {keys : Fin n → B.KeyCoins} {rs : List (Req B 𝒫 adm n)}
    {R : KeyRing (ofBase B 𝒫 adm).PK N} {m : (ofBase B 𝒫 adm).Msg} {y : B.Pub}
    (hf : FreshAt keys (rs.take Q) R m) (hR : R.1 ≠ []) :
    ∀ x' ∈ ((seRelay B pkOf kcOf refuses pubOf ds).relayList rs).take Q,
      x'.1 ≠ (⟨R, m, y⟩ : RingStmt B) := by
  intro x' hx' heq
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx'
  simp only [List.length_take, SideRelay.length_relayList] at hj
  have hjQ : j < Q := by omega
  have hjl : j < rs.length := by omega
  simp only [List.getElem_take, SideRelay.relayList, List.getElem_mapIdx, seRelay] at heq
  have hmem : rs[j] ∈ rs.take Q :=
    List.mem_iff_getElem.2 ⟨j, by simp only [List.length_take]; omega, by simp⟩
  by_cases hs : ∃ h : j < Q, signerIn B pkOf refuses (ds ⟨j, h⟩) rs[j]
  · obtain ⟨hjQ', hsg⟩ := hs
    generalize rs[j] = r at heq hmem hsg
    cases r with
    | corrupt i => exact hsg.elim
    | sideSign i bm => exact bm.elim
    | sign s R' m' =>
      rw [stmtAt_sign hjQ' hsg] at heq
      have h1 : R' = R := congrArg RingStmtOf.ring heq
      have h2 : m' = m := congrArg RingStmtOf.msg heq
      subst h1 h2
      exact hf.not_sign s hmem
  · rw [stmtAt_of_not hs] at heq
    exact hR (congrArg (fun x : RingStmt B => x.ring.1) heq).symm

omit [Nonempty B.Msg] [Nonempty B.Pub] [Nonempty B.BSig]
  [∀ j i, Fintype ((M.comp j).MessageWrite i)] [Fintype R] [DecidableEq R] [Nonempty R]
  [Fintype TS.PK] [Fintype RMsg] [DecidableEq RMsg] [Fintype TS.BSig] [DecidableEq TS.BSig]
  [Fintype TS.Pub] [DecidableEq TS.Pub] [Fintype TS.KeyCoins] [DecidableEq TS.KeyCoins]
  [Nonempty TS.KeyCoins] [Fintype TS.Coins] [DecidableEq TS.Coins] [Nonempty TS.Coins] in
/-- The claim of an output with a proof is its claim. -/
theorem claimOfOut_eq {o : Output 𝒫 adm} {c : Claim X₀ M.NIProof}
    (hc : c ∈ Ring.spbcsComapClaim M stmt (⟨o.1, o.2.1, o.2.2.1⟩ : RingStmt B) o.2.2.2) :
    claimOfOut o = c := by
  unfold claimOfOut
  rw [Option.mem_def.1 hc, Option.getD_some]

omit [Nonempty M.NIProof] [Nonempty B.Msg] [Nonempty B.Pub] [Nonempty B.BSig]
  [∀ j i, Fintype ((M.comp j).MessageWrite i)] in
include hb in
/-- **The compiled verifier at its query budget accepts only claims that the spBCS verifier
accepts** under the oracle read through `outEquiv` and `Query.toBits` (`chainOracle`), for format
bounds `b`. -/
theorem accepts_of_accepted {G : Bits (queryBits k kN kS L) → XOut k e}
    {c : Claim X₀ M.NIProof} (h : (M.qVerifier Qs b b).Accepted (outEquiv k e ∘ G) c) :
    M.Accepts (chainOracle G) c.stmt c.proof (Qs c.stmt) := by
  refine (NARG.Verifier.ofOracle_accepted_iff (fun h₁ h₂ c hag hv => ?_)).1 h
  refine M.accepts_of_agree Qs (fun _ _ _ hv => queries_length_le_of_formatBounds hb hv)
    (fun i => ?_) hv
  have := hag i
  rwa [QROM.Expansion.queries_map] at this

/-- **The simulator answering `p₀` on the statements of the empty ring**: on a statement that the
test `EmptyRingTest.isNil` of `stmt` accepts (the statement `stmt x` of a ring statement `x` with
the empty ring) it returns `p₀` without queries or assignments; on every other statement it runs
`Sim`.

Running time: that of `Sim`, and one run of the test `EmptyRingTest.isNil`. This running time is
argued here, not proved in Lean. -/
def inertOnNil (ert : EmptyRingTest stmt) {SC : Type}
    (Sim : NARG.Simulator (Bits (queryBits k kN kS L)) (XOut k e) X₀ (𝒫).Proof SC) (p₀ : (𝒫).Proof) :
    NARG.Simulator (Bits (queryBits k kN kS L)) (XOut k e) X₀ (𝒫).Proof SC where
  prog x c := if ert.isNil x then .pure ⟨p₀, []⟩ else Sim.prog x c
  coins_nonempty := Sim.coins_nonempty
  q := Sim.q
  prog_queries x c H := by
    split_ifs
    · simp
    · exact Sim.prog_queries x c H

omit [Nonempty M.NIProof] [Nonempty B.Msg] [Nonempty B.Pub] [Nonempty B.BSig] [Nonempty W']
  [Fintype TS.PK] [DecidableEq TS.PK] [Fintype RMsg] [DecidableEq RMsg] [Fintype TS.BSig]
  [DecidableEq TS.BSig] [Fintype TS.Pub] [DecidableEq TS.Pub] [Fintype TS.KeyCoins]
  [DecidableEq TS.KeyCoins] [Nonempty TS.KeyCoins] [Fintype TS.Coins] [DecidableEq TS.Coins]
  [Nonempty TS.Coins] in
omit [∀ j i, Fintype ((M.comp j).MessageWrite i)] [Fintype R] [DecidableEq R] [Nonempty R] in
/-- The simulator answering `p₀` on the statements of the empty ring, read at ring statements,
answers `p₀` on the empty ring. -/
theorem prog_inertOnNil_nil (ert : EmptyRingTest stmt) {SC : Type}
    (Sim : NARG.Simulator (Bits (queryBits k kN kS L)) (XOut k e) X₀ (𝒫).Proof SC) (p₀ : (𝒫).Proof)
    (x : RingStmt B) (hx : x.ring.1 = []) (c : SC) :
    ((inertOnNil (ert := ert) (M := M) (Λ := Λ) (E := E) (hb := hb) (honest := honest) (check :=
        check)
      (input := input) Sim p₀).comap stmt).prog x c = .pure ⟨p₀, []⟩ := by
  simp only [NARG.Simulator.comap, inertOnNil]
  rw [if_pos ((ert.isNil_stmt_iff x).2 hx)]

omit [Nonempty M.NIProof] [Nonempty B.Msg] [Nonempty B.Pub] [Nonempty B.BSig] [Nonempty W']
  [Fintype TS.PK] [DecidableEq TS.PK] [Fintype RMsg] [DecidableEq RMsg] [Fintype TS.BSig]
  [DecidableEq TS.BSig] [Fintype TS.Pub] [DecidableEq TS.Pub] [Fintype TS.KeyCoins]
  [DecidableEq TS.KeyCoins] [Nonempty TS.KeyCoins] [Fintype TS.Coins] [DecidableEq TS.Coins]
  [Nonempty TS.Coins] in
omit [∀ j i, Fintype ((M.comp j).MessageWrite i)] [Fintype R] [DecidableEq R] [Nonempty R] in
/-- The simulator answering `p₀` on the statements of the empty ring, read at ring statements, runs
as the simulator on the other ring statements. -/
theorem prog_inertOnNil_ne (ert : EmptyRingTest stmt) {SC : Type}
    (Sim : NARG.Simulator (Bits (queryBits k kN kS L)) (XOut k e) X₀ (𝒫).Proof SC) (p₀ : (𝒫).Proof)
    (x : RingStmt B) (hx : x.ring.1 ≠ []) :
    ((inertOnNil (ert := ert) (M := M) (Λ := Λ) (E := E) (hb := hb) (honest := honest) (check :=
        check)
      (input := input) Sim p₀).comap stmt).prog x = (Sim.comap stmt).prog x := by
  funext c
  simp only [NARG.Simulator.comap, inertOnNil]
  rw [if_neg fun h => hx ((ert.isNil_stmt_iff x).1 h)]

omit [Nonempty B.BSig] [Fintype R] [DecidableEq R] [Nonempty R] [Fintype TS.BSig]
  [DecidableEq TS.BSig] [Fintype TS.KeyCoins] [DecidableEq TS.KeyCoins] [Nonempty TS.KeyCoins]
  [Fintype TS.Coins] [DecidableEq TS.Coins] [Nonempty TS.Coins] in
/-- **The simulation-extraction game of an adversary with its output read as a claim**, through
the composition of the adversary before the readout (which does not read the output). -/
theorem winTestProb_mapOut [NeZero n]
    {shX : AlgShape (Bits (queryBits k kN kS L)) (XOut k e) (RelayStmt B 𝒫 adm n) (M.Response b)} (X : AdaptiveIAlg shX (Output 𝒫 adm)) {SC : Type} [Fintype SC] [DecidableEq SC]
    (Psim : NARG.Simulator (Bits (queryBits k kN kS L)) (XOut k e) (RelayStmt B 𝒫 adm n)
      (M.Response b) SC) (Q : ℕ) (fx : RelayStmt B 𝒫 adm n → X₀)
    (ok : (X.mapOut claimOfOut).W → Prop) :
    winTestProb Qs (X.mapOut claimOfOut) Psim Q fx ok =
      ((X.toKindAlg.composeBothOut (simExtChallenger Psim Q) id).realLaw (outEquiv k e)).toOuterMeasure
        {p | ∃ v, p.out = some v ∧
          SPBCS.Wins (X.mapOut claimOfOut).toTPKindAlg Psim Q Qs fx ((outEquiv k e).symm ∘ p.oracle) v ∧
          ok (SPBCS.advWorkspace (X.mapOut claimOfOut).toTPKindAlg Psim Q v).1} :=
  rfl

omit [Fintype R] [DecidableEq R] [Nonempty R] [Nonempty TS.KeyCoins] [Fintype TS.Coins]
  [DecidableEq TS.Coins] [Nonempty TS.Coins] in
/-- **The adversary absorbed through `seRelay` at the key coins has the law of the adversary
absorbed with the key coins as a table of outer replies** (`seAlg`'s absorption), against every
challenger and on every event of the composed registers named without the relay. -/
theorem outLaw_seRelay_absorbTab [NeZero n] (refuses : KeyRing B.PK N → ℕ → B.Msg → B.Coins → Prop)
    (pubOf : B.Coins → B.Pub) (keys : Fin n → B.KeyCoins) {Q : ℕ} (a : (A.at keys).Aux)
    (s : Fin Q → B.Coins)
    (C' : Challenger (Bits (queryBits k kN kS L)) (XOut k e) (RelayStmt B 𝒫 adm n) (𝒫).Proof)
    (H : Bits (queryBits k kN kS L) → XOut k e) (P : ((A.at keys).alg a).AbsCW C' → Prop) :
    (((((A.at keys).alg a).absorb (seRelay B (fun i => B.pk (keys i)) keys refuses pubOf s)).toKindAlg.composeBothOut
        C' id).outLaw H).toOuterMeasure {o | ∃ v ∈ o, P v} =
      (((((A.at keys).alg a).absorbTab (seTwo B (fun i => B.pk (keys i)) refuses pubOf s)
          (fun _ => keyReply B keys)).toKindAlg.composeBothOut C' id).outLaw H).toOuterMeasure
        {o | ∃ v ∈ o, P ((((A.at keys).alg a).absorb
          (seTwo B (fun i => B.pk (keys i)) refuses pubOf s).base).forgetCWTo
          (fun _ => keyReply B keys) (((A.at keys).alg a).stepTab
            (seTwo B (fun i => B.pk (keys i)) refuses pubOf s)) C'
          (((A.at keys).alg a).absorb ((seTwo B (fun i => B.pk (keys i)) refuses pubOf s).atC
            fun _ => keyReply B keys)).step v)} := by
  rw [← seTwo_atC B (fun i => B.pk (keys i)) keys refuses pubOf s]
  exact (AdaptiveIAlg.toOuterMeasure_outLaw_absorbTab' _ _
    (fun lg j _ q _ _ => AdaptiveIAlg.tabAt_outerCount_const _ _ _ lg j q) C' H P).symm

omit [Fintype R] [DecidableEq R] [Nonempty R] [Nonempty TS.KeyCoins] in
/-- **The simulated game is at most the side-coin average of the simulation-extraction game with
the test `okAt`**: absorbed through the statements' relay (`seRelay`, `relays_sim_se`), a forgery
on a nonempty ring that is fresh at the first `Q` requests is a fresh statement of the
simulation-extraction game (`relayed_ne_of_fresh`, and `stmt` injective), accepted under the final
oracle, whose statement passes the check and whose ring holds only uncorrupted honest keys. -/
theorem sim_le_sum_winTestProb [NeZero n] (ert : EmptyRingTest stmt) (hinj : Function.Injective
    stmt)
    {SC : Type} [Fintype SC] [DecidableEq SC]
    (Sim : NARG.Simulator (Bits (queryBits k kN kS L)) (XOut k e) X₀ (𝒫).Proof SC)
    (keys : Fin n → B.KeyCoins) (Q : ℕ) (a : (A.at keys).Aux) :
    ∑' H, PMF.uniformOfFintype (Bits (queryBits k kN kS L) → XOut k e) H *
        ((((A.at keys).alg a).toKindAlg.composeBothOut
          (simSplit 𝒫 adm keys refuses pubOf (Sim.comap stmt) Q fun _ _ => True).toChallenger
            id).outLaw H).toOuterMeasure
        {o | ∃ v ∈ o, Wins keys Q (((A.at keys).alg a).out v.adv.workspace.1)
          (Quantum.requests v.chal.logs) (outEquiv k e ∘ H.reprogram
            (((A.at keys).alg a).toKindAlg.postAss
              (simSplit 𝒫 adm keys refuses pubOf (Sim.comap stmt) Q fun _ _ => True).toChallenger
                v.chal))} ≤
      ∑ ds, PMF.uniformOfFintype (Fin Q → B.Coins) ds *
        winTestProb Qs (seAlg A refuses pubOf keys Q a ds)
          ((inertOnNil (ert := ert) (M := M) (Λ := Λ) (E := E) (hb := hb) (honest := honest) (check
              := check)
            (input := input) Sim none).comap (stmt ∘ Prod.fst)) Q
          (stmt ∘ Prod.fst) (okAt A refuses pubOf keys Q a ds) := by
  have hstep := fun H => AdaptiveIAlg.outLaw_absorb (A := (A.at keys).alg a)
    (C := (simSplit 𝒫 adm keys refuses pubOf (Sim.comap stmt) Q fun _ _ => True).toChallenger)
    (C' := simExtChallenger ((inertOnNil (ert := ert) (M := M) (Λ := Λ) (E := E) (hb := hb) (honest
        := honest)
      (check := check) (input := input) Sim none).comap (stmt ∘ Prod.fst)) Q)
    (PMF.uniformOfFintype (Fin Q → B.Coins))
    (fun ds => seRelay B (fun i => B.pk (keys i)) keys refuses pubOf ds)
    (coinSplit Q B.Coins SC) (fun s c' => coins_simSplit keys (Sim.comap stmt) Q _ s c')
    (fun H s c' => (relays_sim_se keys (Sim.comap stmt) ((inertOnNil (ert := ert) (M := M) (Λ := Λ)
        (E := E)
      (hb := hb) (honest := honest) (check := check) (input := input) Sim none).comap
        stmt) none (fun x hx c => prog_inertOnNil_nil (ert := ert) Sim none x hx c)
      (fun x hx => prog_inertOnNil_ne (ert := ert) Sim none x hx) s c').relays H _)
    (fun s c => seRelay_route_injective B _ keys refuses pubOf s c) H
    (fun adv lg mlg _ G =>
      Wins keys Q (((A.at keys).alg a).out adv.workspace.1) (Quantum.requests lg)
        (outEquiv k e ∘ G) ∧
      ∀ x' ∈ (Quantum.requests mlg).take Q, x'.1 ≠ (⟨(((A.at keys).alg a).out adv.workspace.1).1,
        (((A.at keys).alg a).out adv.workspace.1).2.1,
        (((A.at keys).alg a).out adv.workspace.1).2.2.1⟩ : RingStmt B))
  refine (tsum_congr fun H => congrArg (_ * ·) (Eq.trans ?_ (hstep H))).trans_le ?_
  · congr 1
    ext o
    refine exists_congr fun v => and_congr_right fun _ => ⟨fun h => ⟨h, ?_⟩, And.left⟩
    rw [SideRelay.requests_logs]
    exact relayed_ne_of_fresh _ _ _ h.2.2.1 h.2.2.2
  rw [ENNReal.tsum_mul_sum_comm]
  refine Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left ?_ zero_le
  refine le_of_eq_of_le (tsum_congr fun H => congrArg (_ * ·)
    (outLaw_seRelay_absorbTab A refuses pubOf keys a s _ H _)) ?_
  unfold seAlg
  erw [winTestProb_mapOut]
  refine le_of_le_of_eq ?_ (Alg.toOuterMeasure_realLaw_eq_tsum _ (outEquiv k e)
    fun v G => SPBCS.Wins (seAlg A refuses pubOf keys Q a s).toTPKindAlg
      ((inertOnNil (ert := ert) (M := M) (Λ := Λ) (E := E) (hb := hb) (honest := honest) (check :=
          check)
        (input := input) Sim none).comap (stmt ∘ Prod.fst)) Q Qs (stmt ∘ Prod.fst)
        ((outEquiv k e).symm ∘ G) v ∧
      okAt A refuses pubOf keys Q a s (SPBCS.advWorkspace (seAlg A refuses pubOf keys Q a s).toTPKindAlg
        ((inertOnNil (ert := ert) (M := M) (Λ := Λ) (E := E) (hb := hb) (honest := honest) (check :=
            check)
          (input := input) Sim none).comap (stmt ∘ Prod.fst)) Q v).1).symm
  refine ENNReal.tsum_le_tsum fun H =>
    mul_le_mul_of_nonneg_left (MeasureTheory.measure_mono ?_) zero_le
  rintro o ⟨v, hv, hw, hf⟩
  refine ⟨v, hv, ?_⟩
  have hH : (outEquiv k e).symm ∘ (outEquiv k e) ∘ H = H := by
    funext x
    simp
  rw [hH]
  obtain ⟨hck, ⟨c, hc, hacc⟩, hfr, -⟩ := hw
  have hco := claimOfOut_eq hc
  refine ⟨⟨fun x' hx' => ?_, ?_⟩, ?_, hck, fun pk hpk => hfr.honest_ring pk hpk⟩
  · have hq := KindAlg.map_request_history_stateAt (seAlg A refuses pubOf keys Q a s).toTPKindAlg
      (simExtChallenger ((inertOnNil (ert := ert) (M := M) (Λ := Λ) (E := E) (hb := hb) (honest :=
          honest)
        (check := check) (input := input) Sim none).comap (stmt ∘ Prod.fst)) Q) v.chal
      (seAlg A refuses pubOf keys Q a s).toTPKindAlg.slots
    unfold SPBCS.queried at hx'
    -- TODO(unbundle-M4): `rw [hq] at hx'` misses (the implicit shape arguments differ
    -- syntactically); transported along `hq` instead
    replace hx' := (congrArg (x' ∈ ·) hq).mp hx'
    have := hf x' hx'
    change stmt x'.1 ≠ (claimOfOut _).stmt
    rw [claimOfOut_stmt]
    exact fun h => this (hinj h)
  · have h := accepts_of_accepted (hb := hb) hacc
    rw [← hco] at h
    exact h
  · exact Option.isSome_iff_exists.2 ⟨c, Option.mem_def.1 hc⟩

omit [Nonempty M.NIProof] [Nonempty B.Msg] [Nonempty B.Pub] [Nonempty B.BSig] [Nonempty W']
  [Fintype R] [DecidableEq R] [Nonempty R] [Fintype TS.PK] [DecidableEq TS.PK] [Fintype RMsg]
  [DecidableEq RMsg] [Fintype TS.BSig] [DecidableEq TS.BSig] [Fintype TS.Pub] [DecidableEq TS.Pub]
  [Fintype TS.KeyCoins] [DecidableEq TS.KeyCoins] [Nonempty TS.KeyCoins] [Fintype TS.Coins]
  [DecidableEq TS.Coins] [Nonempty TS.Coins] in
/-- **The simulator answering `none` on the statements of the empty ring assigns only at the keys
of its chain inputs** when the spBCS simulator does (`simAssignsAtKeys_niJointSimulatorProg`, digests
of at least one byte). -/
theorem simAssignsAtKeys_inertOnNil (ert : EmptyRingTest stmt) (hk : 0 < k)
    (VE : M.ViewEncoder E Qs) {Pub : Type}
    (pub : X₀ → Pub) (Sim : CausalJointSimulator VE.MV Pub) (T : M.Preimages) :
    M.SimAssignsAtKeys b (inertOnNil (ert := ert) (M := M) (Λ := Λ) (E := E) (hb := hb) (honest :=
        honest)
      (stmt := stmt) (check := check) (input := input)
      (M.niJointSimulatorProg Λ VE.toViewRead b pub Sim T) none) id := by
  intro r c G qa hqa
  have hS := simAssignsAtKeys_niJointSimulatorProg hk Λ VE b pub Sim T r c G qa
  simp only [inertOnNil] at hqa ⊢
  split_ifs at hqa ⊢ with h
  · exact nomatch hqa
  · exact hS hqa

end SPBCS

/-! ### The multi-user history of a forger without signing requests -/

section History

variable {X Y : Type} {N n : ℕ} {TS : Signature.SchemeTypes} {RMsg : Type}
  {B : BaseSigner X Y N TS RMsg}
  {TPS : PSTypes} [Fintype TPS.Proof] [DecidableEq TPS.Proof] [Fintype TPS.Coins] [DecidableEq TPS.Coins] [Nonempty TPS.Coins] {PS : ProofSystem X Y (RingStmt B) (RingWit B) TPS} {adm : KeyRing B.PK N → Prop} [DecidablePred adm]

variable [DecidableEq TS.PK]

/-- **The relayed history of a forger without signing requests**: the corruptions among the
requests `rs`, as corruptions of the multi-user game (MU-EUF-CMA^corr with the ring-aware signing
oracle), with no signing request. -/
def corruptHist (rs : List (Req B PS adm n)) :
    Signature.MUHist (Signature.SignOracle.ring B) n :=
  rs.filterMap fun
    | .corrupt i => some ⟨.corrupt i, none⟩
    | _ => none

omit [Fintype TPS.Proof] [DecidableEq TPS.Proof] [Fintype TPS.Coins] [DecidableEq TPS.Coins]
  [Nonempty TPS.Coins] in
/-- A user is corrupted in the relayed history exactly when the requests corrupt it. -/
theorem corrupted_corruptHist {rs : List (Req B PS adm n)} {i : Fin n} :
    Signature.Corrupted (corruptHist rs) i ↔ UnforgeRequest.corrupt i ∈ rs := by
  constructor
  · rintro ⟨x, hx, hr⟩
    obtain ⟨r, hr', hx'⟩ := List.mem_filterMap.1 hx
    cases r with
    | corrupt j =>
      simp only [Option.some.injEq] at hx'
      subst hx'
      simp only [Signature.MURequest.corrupt.injEq] at hr
      exact hr ▸ hr'
    | sign s R m => simp at hx'
    | sideSign j bm => exact bm.elim
  · intro h
    exact ⟨⟨.corrupt i, none⟩, List.mem_filterMap.2 ⟨_, h, rfl⟩, rfl⟩

omit [Fintype TPS.Proof] [DecidableEq TPS.Proof] [Fintype TPS.Coins] [DecidableEq TPS.Coins]
  [Nonempty TPS.Coins] in
/-- No user is asked to sign in the relayed history. -/
theorem not_signed_corruptHist (rs : List (Req B PS adm n)) (i : Fin n) (bm : B.BMsg) :
    ¬ Signature.Signed (corruptHist rs) i bm := by
  rintro ⟨x, hx, sm, hr, -⟩
  obtain ⟨r, -, hx'⟩ := List.mem_filterMap.1 hx
  cases r with
  | corrupt j =>
    simp only [Option.some.injEq] at hx'
    subst hx'
    exact absurd hr (by simp)
  | sign s R m => simp at hx'
  | sideSign j bm => exact bm.elim

end History

section SPBCS'

variable {k kN kS L e N n t : ℕ} {TS : Signature.SchemeTypes} {RMsg : Type} [DecidableEq TS.PK]
  {B : BaseSigner (Bits (queryBits k kN kS L)) (XOut k e) N TS RMsg}
  {ι : Type} {τ : SPTerm ι} {Mg : Merges τ} {nr : ι → ℕ}
  {P : (j : ι) → ProtocolSpec (nr j)} [∀ j i, Fintype ((P j).Challenge i)]
  [∀ j i, DecidableEq ((P j).Challenge i)] [∀ j i, Nonempty ((P j).Challenge i)]
  {X₀ Wit₀ : Type} {M : SPBCS Mg P X₀ k kN kS L e} {Λ : SiteLayout Mg} {b : ℕ}
  [∀ j i, Fintype ((M.comp j).MessageWrite i)] {E : (j : ι) → (M.comp j).Encoder}
  {Vr : X₀ → FullTr P τ → Bool} {Qs : ∀ x, M.IOPQueries Vr x}
  {hb : M.FormatBounds Qs b b} {R : Type} [Fintype R] [DecidableEq R] [Nonempty R]
  {honest : Wit₀ → R → CausalProver P τ X₀} {stmt : RingStmt B → X₀} {check : RingStmt B → Bool}
  {input : RingStmt B → RingWit B → Option Wit₀}
  {adm : KeyRing B.PK N → Prop} [DecidablePred adm] {W' : Type} [Fintype W'] [DecidableEq W']
  {fw : W' → Wit₀} {enc : RingStmt B → RelayWit B → Option W'}
  {relH : Set (X₀ × Wit₀)} {WitK : Type} {rel : Set (X₀ × WitK)} {wit : RingStmt B → WitK → RingWit B}

local notation "𝒫" => Ring.spbcsComapProofSystem M Λ E hb honest stmt check input

local notation "𝒫z" => encProver M Λ E hb honest

variable [Fintype TS.PK] [Fintype RMsg] [DecidableEq RMsg] [Fintype TS.BSig]
  [DecidableEq TS.BSig] [Fintype TS.Pub] [DecidableEq TS.Pub] [Fintype TS.KeyCoins]
  [DecidableEq TS.KeyCoins] [Nonempty TS.KeyCoins] [Fintype TS.Coins] [DecidableEq TS.Coins]
  [Nonempty TS.Coins]

variable (A : InsiderAdversary (ofBase B (Ring.spbcsComapProofSystem M Λ E hb honest stmt check input) adm) n
    (OracleView.queriesOnly (Bits (queryBits k kN kS L)) (XOut k e)) t)
  [Nonempty B.Msg] [Nonempty B.Pub] [Nonempty B.BSig] [Nonempty M.NIProof]

/-- The ring statement of an output. -/
abbrev outStmt (o : Output 𝒫 adm) : RingStmt B := ⟨o.1, o.2.1, o.2.2.1⟩

variable [DecidableEq X₀] (ert : EmptyRingTest stmt)

/-- **The forger's win in one extraction run** of the simulation-extraction adversary at the key
coins `keys` and the signing coins `ds`, on the measured registers `c` and database `D`: some
witness the database extractor `Ext` returns for the statement `stmt x` of the forgery's ring
statement `x` gives a ring witness (`wit`) that decodes (`decodeWit`) to a candidate `(pk, bm, σ)`
that is a forgery of MU-EUF-CMA^corr with the ring-aware signing oracle (`Signature.Forges`) at
every oracle, for the history of the corruptions among the first `Q` logged requests (`corruptHist`;
no signing request). -/
def forgerWins [NeZero n] (wit : RingStmt B → WitK → RingWit B)
    (refuses : KeyRing B.PK N → ℕ → B.Msg → B.Coins → Prop)
    (pubOf : B.Coins → B.Pub) (keys : Fin n → B.KeyCoins) (Q : ℕ) (a : (A.at keys).Aux)
    (ds : Fin Q → B.Coins) {SC : Type} [Fintype SC] [DecidableEq SC]
    (Psim : NARG.Simulator (Bits (queryBits k kN kS L)) (XOut k e) (RelayStmt B 𝒫 adm n)
      (M.Response b) SC)
    (Ext : CausalExtractor P τ X₀ WitK)
    (c : SPBCS.Reg (seAlg A refuses pubOf keys Q a ds) Psim Q)
    (D : DB (Bits (queryBits k kN kS L)) (Out k e)) : Prop :=
  ∃ w ∈ M.dbExtractBits Ext (stmt (outStmt (((A.at keys).alg a).out
      (SPBCS.advWorkspace (seAlg A refuses pubOf keys Q a ds).toTPKindAlg Psim Q c).1.1.work))) D,
    ∃ f ∈ decodeWit (outStmt (((A.at keys).alg a).out
        (SPBCS.advWorkspace (seAlg A refuses pubOf keys Q a ds).toTPKindAlg Psim Q c).1.1.work))
      (wit (outStmt (((A.at keys).alg a).out
        (SPBCS.advWorkspace (seAlg A refuses pubOf keys Q a ds).toTPKindAlg Psim Q c).1.1.work)) w),
      ∀ H, Signature.Forges keys H f (corruptHist ((Quantum.requests
        (SPBCS.advWorkspace (seAlg A refuses pubOf keys Q a ds).toTPKindAlg Psim Q c).1.1.logs).take Q))

omit [Nonempty B.BSig] ert [Fintype R] [DecidableEq R] [Nonempty R] in
omit [Nonempty TS.KeyCoins] [Fintype TS.Coins] [DecidableEq TS.Coins] [Nonempty TS.Coins] in
/-- **A fresh extracted witness passing the test decodes to a forgery of the multi-user game**, for
an oracle-free base signer (`hB`): the extracted witness of `rel` at the checked statement gives a
witness of the ring relation at the zero oracle (`hz.sound`), hence at every oracle, and the test
makes the decoded key that of an uncorrupted user. -/
theorem extractFreshTestProb_le [NeZero n] (hB : B.OracleFree)
    (hz : ZKRingHyps B adm stmt check input fw enc relH rel wit)
    (refuses : KeyRing B.PK N → ℕ → B.Msg → B.Coins → Prop) (pubOf : B.Coins → B.Pub)
    (keys : Fin n → B.KeyCoins) (Q kq : ℕ) (a : (A.at keys).Aux) (ds : Fin Q → B.Coins)
    {SC : Type} [Fintype SC] [DecidableEq SC]
    (Psim : NARG.Simulator (Bits (queryBits k kN kS L)) (XOut k e) (RelayStmt B 𝒫 adm n)
      (M.Response b) SC)
    (Ext : CausalExtractor P τ X₀ WitK) :
    extractFreshTestProb Qs (seAlg A refuses pubOf keys Q a ds) Psim Q kq (stmt ∘ Prod.fst)
        rel Ext (okAt A refuses pubOf keys Q a ds) ≤
      simProb (outEquiv k e) (extAdv Qs (seAlg A refuses pubOf keys Q a ds) Psim Q kq)
        (forgerWins A wit refuses pubOf keys Q a ds Psim Ext) := by
  refine simProb_mono _ _ fun c D ⟨hx, _, hok⟩ => ?_
  obtain ⟨w, hw, hrel⟩ := (extractsAt_dbExtractBits_iff M rel Ext).2 hx
  -- TODO(unbundle-M4): `rw [hst]` misses the claim's statement in `hw`/`hrel` (their implicit
  -- shape arguments differ syntactically), so both are restated at `hst`'s right side.
  obtain ⟨S, hS⟩ : ∃ S, stmt (outStmt (((A.at keys).alg a).out
      (SPBCS.advWorkspace (seAlg A refuses pubOf keys Q a ds).toTPKindAlg Psim Q c).1.1.work)) = S :=
    ⟨_, rfl⟩
  have hst : (SPBCS.advOut (seAlg A refuses pubOf keys Q a ds).toTPKindAlg Psim Q c).stmt = S :=
    (claimOfOut_stmt _).trans hS
  replace hw : w ∈ M.dbExtractBits Ext S D := hst ▸ hw
  replace hrel : rel (S, w) := hst ▸ hrel
  subst hS
  have hR : RingRel B adm 0 _ _ := hz.sound _ w hok.2.1 hrel
  refine ⟨w, hw, _, (by simp only [decodeWit]; rw [dif_pos (by exact hR.idx_lt)]; rfl), fun H => ⟨?_, ?_⟩⟩
  · rw [← hB.bverify_eq 0 H]
    exact hR.verify_eq
  · obtain ⟨i, hi, hc⟩ := hok.2.2 _ (List.getElem_mem hR.idx_lt)
    exact ⟨i, hi, fun h => hc (corrupted_corruptHist.1 h), not_signed_corruptHist _ i _⟩

/-! ### The chain at fixed keys -/

/-- The spBCS joint simulator with the statements of the empty ring answered by `none`, the
simulator of the simulation-extraction game.

Running time: that of `inertOnNil` at the joint simulator `niJointSimulatorProg` (its paragraph).
This running time is argued here, not proved in Lean. -/
abbrev seSim (VE : M.ViewEncoder E Qs) {Pub : Type} (pub : X₀ → Pub)
    (Sim : CausalJointSimulator VE.MV Pub) (T : M.Preimages) :
    NARG.Simulator (Bits (queryBits k kN kS L)) (XOut k e) X₀ (M.Response b)
      (SaltedCoins (FiatShamirSalt kS) (M.JointSimCoins VE.toViewRead Sim T)) :=
  inertOnNil (ert := ert) (M := M) (Λ := Λ) (E := E) (hb := hb) (honest := honest) (stmt := stmt)
    (check := check) (input := input) (M.niJointSimulatorProg Λ VE.toViewRead b pub Sim T) none

omit [Nonempty M.NIProof] [DecidableEq X₀] in
open Classical in
omit [Nonempty TS.KeyCoins] in
/-- **The chain at one key and one auxiliary value, with a total encoding**: the insider game with a nonempty ring,
averaged over the oracle, is at most the average over the signing coins of the simulation-extraction
game with the test `okAt`, plus `zkError δ t Q`, `2 Q εc` and `Q` times the unpredicted refusal rate
(`refusalGap`). -/
theorem game_le_sum_winTestProb_at [NeZero n] [Nonempty M.NIProof] [Nonempty W']
    (hB : B.OracleFree)
    {refuses : KeyRing B.PK N → ℕ → B.Msg → B.Coins → Prop} {pubOf : B.Coins → B.Pub}
    (hpub : B.PubOfCoins pubOf) (hsound : B.RefusalSound refuses) {εc : ℝ≥0∞}
    (hcorr : B.CorrectWithin εc) (enc : RingStmt B → RelayWit B → W')
    (hz : ZKRingHypsAt B adm stmt input fw enc relH)
    (VE : M.ViewEncoder E Qs) {Pub : Type} (pub : X₀ → Pub)
    (Sim : CausalJointSimulator VE.MV Pub) (T : M.Preimages) {δ : NNReal}
    (hvzk : CausalHVZK VE.MV relH honest pub Sim δ) (keys : Fin n → B.KeyCoins)
    (Q : ℕ) (a : (A.at keys).Aux) :
    ∑' H, PMF.uniformOfFintype (Bits (queryBits k kN kS L) → XOut k e) H *
        ((((A.at keys).alg a).toKindAlg.composeBothOut
          (unforgeChallenger (ofBase B 𝒫 adm) n (SideOracle.none _) keys Q) id).outLaw
          H).toOuterMeasure
        {o | ∃ v ∈ o, Wins keys Q (((A.at keys).alg a).out v.adv.workspace.1)
          (Quantum.requests v.chal.logs) (outEquiv k e ∘ H)} ≤
      ∑ ds, PMF.uniformOfFintype (Fin Q → B.Coins) ds *
          winTestProb Qs (seAlg A refuses pubOf keys Q a ds)
            ((seSim (ert := ert) (Λ := Λ) (hb := hb) (honest := honest) (stmt := stmt) (check :=
                check)
              (input := input) VE pub Sim T).comap (stmt ∘ Prod.fst))
            Q (stmt ∘ Prod.fst) (okAt A refuses pubOf keys Q a ds) +
        ENNReal.ofReal (M.zkError δ t Q) + 2 * Q * εc + Q * refusalGap adm keys refuses := by
  set Simj := M.niJointSimulatorProg Λ VE.toViewRead b pub Sim T
  have hσ : ∑ ds : Fin Q → B.Coins, PMF.uniformOfFintype (Fin Q → B.Coins) ds = 1 := by
    have h1 := (PMF.uniformOfFintype (Fin Q → B.Coins)).tsum_coe
    rwa [tsum_fintype] at h1
  have hreal := PMF.tsum_pmf_mul_le_add
    (PMF.uniformOfFintype (Bits (queryBits k kN kS L) → XOut k e)) _ _ _ fun H =>
    game_le_sum_real A hB hpub hsound hz hcorr keys Q a H
  have hzk : ∑' H, PMF.uniformOfFintype (Bits (queryBits k kN kS L) → XOut k e) H *
      ∑ ds, PMF.uniformOfFintype (Fin Q → B.Coins) ds *
        (((distinguisher A enc refuses pubOf keys Q a ds).alg ()).compose
          (realChallenger (relZ B 𝒫 adm stmt fw relH) ((𝒫z).comap (stmt ∘ Prod.fst) fw) (PMF.uniformOfFintype _) Q)).outLaw H
          (some true) ≤
      ∑' H, PMF.uniformOfFintype (Bits (queryBits k kN kS L) → XOut k e) H *
        ∑ ds, PMF.uniformOfFintype (Fin Q → B.Coins) ds *
          (((distinguisher A enc refuses pubOf keys Q a ds).alg ()).compose
            (simChallenger (relZ B 𝒫 adm stmt fw relH) (Simj.comap (stmt ∘ Prod.fst)) Q)).outLaw H (some true) +
        ENNReal.ofReal (M.zkError δ t Q) := by
    rw [ENNReal.tsum_mul_sum_comm, ENNReal.tsum_mul_sum_comm]
    simp_rw [← acceptProb_distinguisher]
    calc _ ≤ ∑ ds, PMF.uniformOfFintype (Fin Q → B.Coins) ds *
          ((distinguisher A enc refuses pubOf keys Q a ds).acceptProb
            (simChallenger (relZ B 𝒫 adm stmt fw relH) (Simj.comap (stmt ∘ Prod.fst)) Q) +
            ENNReal.ofReal (M.zkError δ t Q)) :=
          Finset.sum_le_sum fun ds _ => mul_le_mul_of_nonneg_left
            (acceptProb_real_le A VE pub Sim T hvzk keys Q a ds) zero_le
      _ = _ := by simp_rw [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hσ, one_mul]
  have hsim : ∑' H, PMF.uniformOfFintype (Bits (queryBits k kN kS L) → XOut k e) H *
      ∑ ds, PMF.uniformOfFintype (Fin Q → B.Coins) ds *
        (((distinguisher A enc refuses pubOf keys Q a ds).alg ()).compose
          (simChallenger (relZ B 𝒫 adm stmt fw relH) (Simj.comap (stmt ∘ Prod.fst)) Q)).outLaw H (some true) ≤
      ∑ ds, PMF.uniformOfFintype (Fin Q → B.Coins) ds *
          winTestProb Qs (seAlg A refuses pubOf keys Q a ds)
            ((seSim (ert := ert) (Λ := Λ) (hb := hb) (honest := honest) (stmt := stmt) (check :=
                check)
              (input := input) VE pub Sim T).comap (stmt ∘ Prod.fst))
            Q (stmt ∘ Prod.fst) (okAt A refuses pubOf keys Q a ds) +
          Q * (εc + refusalGap adm keys refuses) := by
    refine (le_of_eq (tsum_congr fun H => congrArg (_ * ·)
      (sum_sim_eq_checked A hB hpub hz Simj keys Q a H))).trans ?_
    refine (PMF.tsum_pmf_mul_le_add
      (PMF.uniformOfFintype (Bits (queryBits k kN kS L) → XOut k e)) _ _ _ fun H =>
      simChecked_le hcorr ((A.at keys).alg a).toKindAlg keys (Simj.comap stmt) Q H fun adv lg G =>
        Wins keys Q (((A.at keys).alg a).out adv.workspace.1) (Quantum.requests lg)
          (outEquiv k e ∘ G)).trans (add_le_add ?_ le_rfl)
    exact sim_le_sum_winTestProb (ert := ert) A hz.stmt_injective Simj keys Q a
  calc _ ≤ _ := hreal
    _ ≤ _ := add_le_add (hzk.trans (add_le_add hsim le_rfl)) le_rfl
    _ = _ := by ring

omit [Nonempty M.NIProof] [DecidableEq X₀] in
omit [Nonempty TS.KeyCoins] in
/-- **The chain at one key and one auxiliary value**: the insider game with a nonempty ring,
averaged over the oracle, is at most the average over the signing coins of the simulation-extraction
game with the test `okAt`, plus `zkError δ t Q`, `2 Q εc` and `Q · refusalGap`. Without an encoding
type the ring relation is empty, and the bound holds without the zero-knowledge step (`checked_eq_refuse`,
`simChecked_eq_refuse`). -/
theorem game_le_sum_winTestProb [NeZero n] [Nonempty M.NIProof] (hB : B.OracleFree)
    {refuses : KeyRing B.PK N → ℕ → B.Msg → B.Coins → Prop} {pubOf : B.Coins → B.Pub}
    (hpub : B.PubOfCoins pubOf) (hsound : B.RefusalSound refuses) {εc : ℝ≥0∞}
    (hcorr : B.CorrectWithin εc) (hz : ZKRingHyps B adm stmt check input fw enc relH rel wit)
    (VE : M.ViewEncoder E Qs) {Pub : Type} (pub : X₀ → Pub)
    (Sim : CausalJointSimulator VE.MV Pub) (T : M.Preimages) {δ : NNReal}
    (hvzk : CausalHVZK VE.MV relH honest pub Sim δ) (keys : Fin n → B.KeyCoins)
    (Q : ℕ) (a : (A.at keys).Aux) :
    ∑' H, PMF.uniformOfFintype (Bits (queryBits k kN kS L) → XOut k e) H *
        ((((A.at keys).alg a).toKindAlg.composeBothOut
          (unforgeChallenger (ofBase B 𝒫 adm) n (SideOracle.none _) keys Q) id).outLaw
          H).toOuterMeasure
        {o | ∃ v ∈ o, Wins keys Q (((A.at keys).alg a).out v.adv.workspace.1)
          (Quantum.requests v.chal.logs) (outEquiv k e ∘ H)} ≤
      ∑ ds, PMF.uniformOfFintype (Fin Q → B.Coins) ds *
          winTestProb Qs (seAlg A refuses pubOf keys Q a ds)
            ((seSim (ert := ert) (Λ := Λ) (hb := hb) (honest := honest) (stmt := stmt) (check :=
                check)
              (input := input) VE pub Sim T).comap (stmt ∘ Prod.fst))
            Q (stmt ∘ Prod.fst) (okAt A refuses pubOf keys Q a ds) +
        ENNReal.ofReal (M.zkError δ t Q) + 2 * Q * εc + Q * refusalGap adm keys refuses := by
  classical
  by_cases hW : Nonempty W'
  · exact game_le_sum_winTestProb_at (ert := ert) A hB hpub hsound hcorr _ (hz.at
      (Classical.arbitrary W')) VE
      pub Sim T hvzk keys Q a
  have hempty := hz.not_mem_ringRel (not_nonempty_iff.1 hW)
  set Simj := M.niJointSimulatorProg Λ VE.toViewRead b pub Sim T
  set K := ((A.at keys).alg a).toKindAlg
  have hstep : ∀ H : Bits (queryBits k kN kS L) → XOut k e,
      ((K.composeBothOut (unforgeChallenger (ofBase B 𝒫 adm) n (SideOracle.none _) keys Q)
        id).outLaw H).toOuterMeasure
        {o | ∃ v ∈ o, Wins keys Q (((A.at keys).alg a).out v.adv.workspace.1)
          (Quantum.requests v.chal.logs) (outEquiv k e ∘ H)} ≤
      ((K.composeBothOut
          (simSplit 𝒫 adm keys refuses pubOf (Simj.comap stmt) Q fun _ _ => True).toChallenger
            id).outLaw H).toOuterMeasure
        {o | ∃ v ∈ o, Wins keys Q (((A.at keys).alg a).out v.adv.workspace.1)
          (Quantum.requests v.chal.logs) (outEquiv k e ∘ H.reprogram (K.postAss
            (simSplit 𝒫 adm keys refuses pubOf (Simj.comap stmt) Q fun _ _ => True).toChallenger
              v.chal))} + (Q * (εc + refusalGap adm keys refuses) + Q * εc) := by
    intro H
    rw [toOuterMeasure_outLaw_unforge_eq_split (ofBase B 𝒫 adm) n (SideOracle.none _) K keys Q H
      fun adv lg => Wins keys Q (((A.at keys).alg a).out adv.workspace.1) (Quantum.requests lg)
        (outEquiv k e ∘ H), ← add_assoc]
    refine (game_le_checked hcorr K keys Q H fun adv lg =>
      Wins keys Q (((A.at keys).alg a).out adv.workspace.1) (Quantum.requests lg)
        (outEquiv k e ∘ H)).trans (add_le_add ?_ le_rfl)
    rw [checked_eq_refuse hB hpub hsound hempty K keys Q H fun adv lg =>
        Wins keys Q (((A.at keys).alg a).out adv.workspace.1) (Quantum.requests lg)
          (outEquiv k e ∘ H),
      ← simChecked_eq_refuse hB hpub hempty K keys (Simj.comap stmt) Q H fun adv lg G =>
        Wins keys Q (((A.at keys).alg a).out adv.workspace.1) (Quantum.requests lg)
          (outEquiv k e ∘ G)]
    exact simChecked_le hcorr K keys (Simj.comap stmt) Q H fun adv lg G =>
      Wins keys Q (((A.at keys).alg a).out adv.workspace.1) (Quantum.requests lg)
        (outEquiv k e ∘ G)
  refine (PMF.tsum_pmf_mul_le_add _ _ _ _ hstep).trans ?_
  refine (add_le_add (sim_le_sum_winTestProb (ert := ert) A hz.stmt_injective Simj keys Q a)
      le_rfl).trans ?_
  have h2 : (Q : ℝ≥0∞) * (εc + refusalGap adm keys refuses) + Q * εc =
      2 * Q * εc + Q * refusalGap adm keys refuses := by ring
  rw [h2, ← add_assoc]
  exact add_le_add (add_le_add (le_add_of_nonneg_right zero_le) le_rfl) le_rfl

/-- **The success probability of the extraction forger without signing requests** (the forger of
the zero-knowledge route): averaged over the
users' key coins, the forger's own signing coins `ds` and the adversary's auxiliary input, the
probability that the extraction run of the simulation-extraction adversary (`seAlg`: the adversary
with ring signatures simulated by the spBCS joint simulator on the statements with the public values
`pubOf` of `ds` and the refusals `refuses`, corruptions answered with the users' key coins, public
keys from the start input; no secret key read, no signing request) yields a forgery of
MU-EUF-CMA^corr with the ring-aware signing oracle at every oracle, for the history of its
corruptions (`forgerWins`). This forger is not an adversary of `Signature.MUAdversary`: it simulates
the oracle with a compressed oracle and extracts from its database. -/
noncomputable def zkForgerSuccess [NeZero n] (wit : RingStmt B → WitK → RingWit B)
    (refuses : KeyRing B.PK N → ℕ → B.Msg → B.Coins → Prop) (pubOf : B.Coins → B.Pub)
    (VE : M.ViewEncoder E Qs) {Pub : Type} (pub : X₀ → Pub)
    (Sim : CausalJointSimulator VE.MV Pub) (T : M.Preimages)
    (Ext : CausalExtractor P τ X₀ WitK) (Q : ℕ) : ℝ≥0∞ :=
  ∑' keys, PMF.uniformOfFintype (Fin n → B.KeyCoins) keys *
    ∑ ds, PMF.uniformOfFintype (Fin Q → B.Coins) ds * ∑' a, (A.at keys).aux a *
      simProb (outEquiv k e) (extAdv Qs (seAlg A refuses pubOf keys Q a ds)
          ((seSim (ert := ert) (Λ := Λ) (hb := hb) (honest := honest) (stmt := stmt) (check :=
              check)
          (input := input) VE pub Sim T).comap (stmt ∘ Prod.fst)) Q
          (kqOf Mg nr b b))
        (forgerWins A wit refuses pubOf keys Q a ds
          ((seSim (ert := ert) (Λ := Λ) (hb := hb) (honest := honest) (stmt := stmt) (check :=
              check)
          (input := input) VE pub Sim T).comap (stmt ∘ Prod.fst)) Ext)

omit [Nonempty M.NIProof] in
/-- **The bound at fixed keys**: averaged over the auxiliary input and the oracle, the insider game
with a nonempty ring is at most the forger's success at these keys, plus `zkError δ t Q`, the
simulation-extraction error, `2 Q εc` and `Q · refusalGap` (`game_le_sum_winTestProb`, then weak simulation-sound
extractability, `SPBCS.weak_online_simulation_extractability_qrom`, and
`extractFreshTestProb_le`). -/
theorem keys_le [NeZero n] [Nonempty M.NIProof] (hk : 0 < k) (hB : B.OracleFree)
    {refuses : KeyRing B.PK N → ℕ → B.Msg → B.Coins → Prop} {pubOf : B.Coins → B.Pub}
    (hpub : B.PubOfCoins pubOf) (hsound : B.RefusalSound refuses) {εc : ℝ≥0∞}
    (hcorr : B.CorrectWithin εc) (hz : ZKRingHyps B adm stmt check input fw enc relH rel wit)
    (VE : M.ViewEncoder E Qs) {Pub : Type} (pub : X₀ → Pub)
    (Sim : CausalJointSimulator VE.MV Pub) (T : M.Preimages) {δ : NNReal}
    (hvzk : CausalHVZK VE.MV relH honest pub Sim δ)
    {Ext : CausalExtractor P τ X₀ WitK} {St : CausalStateFn P τ X₀}
    {ε : ChIdx P τ → NNReal} (hrbr : CausalRBRKnowledgeSound rel Vr Ext St ε)
    (keys : Fin n → B.KeyCoins) (Q : ℕ) :
    ∑' a, (A.at keys).aux a * ∑' H, PMF.uniformOfFintype (Bits (queryBits k kN kS L) → XOut k e) H *
        ((((A.at keys).alg a).toKindAlg.composeBothOut
          (unforgeChallenger (ofBase B 𝒫 adm) n (SideOracle.none _) keys Q) id).outLaw
          H).toOuterMeasure
        {o | ∃ v ∈ o, Wins keys Q (((A.at keys).alg a).out v.adv.workspace.1)
          (Quantum.requests v.chal.logs) (outEquiv k e ∘ H)} ≤
      ∑ ds, PMF.uniformOfFintype (Fin Q → B.Coins) ds * ∑' a, (A.at keys).aux a *
          simProb (outEquiv k e) (extAdv Qs (seAlg A refuses pubOf keys Q a ds)
              ((seSim (ert := ert) (Λ := Λ) (hb := hb) (honest := honest) (stmt := stmt) (check :=
                  check)
          (input := input) VE pub Sim T).comap (stmt ∘ Prod.fst)) Q
              (kqOf Mg nr b b))
            (forgerWins A wit refuses pubOf keys Q a ds
              ((seSim (ert := ert) (Λ := Λ) (hb := hb) (honest := honest) (stmt := stmt) (check :=
                  check)
          (input := input) VE pub Sim T).comap (stmt ∘ Prod.fst)) Ext) +
        M.simExtractionError (kqOf Mg nr b b) (maxError ε)
          (M.niJointSimulatorProg Λ VE.toViewRead b pub Sim T).q t Q +
        (ENNReal.ofReal (M.zkError δ t Q) + 2 * Q * εc + Q * refusalGap adm keys refuses) := by
  have hkq : ∀ x h π, M.Accepts h x π (Qs x) → (M.queries x π h (Qs x)).length ≤ kqOf Mg nr b b :=
    fun _ _ _ hv => queries_length_le_of_formatBounds hb hv
  have hse := (weak_online_simulation_extractability_qrom (B := b) Qs hkq hrbr
    (seSim (ert := ert) (Λ := Λ) (hb := hb) (honest := honest) (stmt := stmt) (check := check)
      (input := input) VE pub Sim T)
    (simAssignsAtKeys_inertOnNil (ert := ert) (stmt := stmt) (check := check) (input := input) hk VE
        pub Sim T)).unruhSimExtraction_of_queryFreeTest hkq
  have hσ : ∑ ds : Fin Q → B.Coins, PMF.uniformOfFintype (Fin Q → B.Coins) ds = 1 := by
    have h1 := (PMF.uniformOfFintype (Fin Q → B.Coins)).tsum_coe
    rwa [tsum_fintype] at h1
  have hs : ∀ ds : Fin Q → B.Coins, ∑' a, (A.at keys).aux a *
      winTestProb Qs (seAlg A refuses pubOf keys Q a ds)
        ((seSim (ert := ert) (Λ := Λ) (hb := hb) (honest := honest) (stmt := stmt) (check := check)
          (input := input) VE pub Sim T).comap (stmt ∘ Prod.fst)) Q (stmt ∘ Prod.fst)
        (okAt A refuses pubOf keys Q a ds) ≤
      ∑' a, (A.at keys).aux a * simProb (outEquiv k e) (extAdv Qs (seAlg A refuses pubOf keys Q a ds)
          ((seSim (ert := ert) (Λ := Λ) (hb := hb) (honest := honest) (stmt := stmt) (check :=
              check)
          (input := input) VE pub Sim T).comap (stmt ∘ Prod.fst)) Q
          (kqOf Mg nr b b))
        (forgerWins A wit refuses pubOf keys Q a ds
          ((seSim (ert := ert) (Λ := Λ) (hb := hb) (honest := honest) (stmt := stmt) (check :=
              check)
          (input := input) VE pub Sim T).comap (stmt ∘ Prod.fst)) Ext) +
      M.simExtractionError (kqOf Mg nr b b) (maxError ε)
        (M.niJointSimulatorProg Λ VE.toViewRead b pub Sim T).q t Q := fun ds =>
    (hse (RelayStmt B 𝒫 adm n) (stmt ∘ Prod.fst) t Q (seAdversary A refuses pubOf keys Q ds)
      fun a => okAt A refuses pubOf keys Q a ds).trans
      (add_le_add (ENNReal.tsum_le_tsum fun a => mul_le_mul_of_nonneg_left
        (extractFreshTestProb_le A hB hz refuses pubOf keys Q _ a ds _ Ext) zero_le) le_rfl)
  calc _ ≤ ∑' a, (A.at keys).aux a * (∑ ds, PMF.uniformOfFintype (Fin Q → B.Coins) ds *
          winTestProb Qs (seAlg A refuses pubOf keys Q a ds)
            ((seSim (ert := ert) (Λ := Λ) (hb := hb) (honest := honest) (stmt := stmt) (check :=
                check)
          (input := input) VE pub Sim T).comap (stmt ∘ Prod.fst)) Q (stmt ∘ Prod.fst)
            (okAt A refuses pubOf keys Q a ds) +
          (ENNReal.ofReal (M.zkError δ t Q) + 2 * Q * εc + Q * refusalGap adm keys refuses)) :=
        ENNReal.tsum_le_tsum fun a => mul_le_mul_of_nonneg_left
          ((game_le_sum_winTestProb (ert := ert) A hB hpub hsound hcorr hz VE pub Sim T hvzk keys Q
              a).trans_eq
            (by ring)) zero_le
    _ = ∑ ds, PMF.uniformOfFintype (Fin Q → B.Coins) ds * ∑' a, (A.at keys).aux a *
          winTestProb Qs (seAlg A refuses pubOf keys Q a ds)
            ((seSim (ert := ert) (Λ := Λ) (hb := hb) (honest := honest) (stmt := stmt) (check :=
                check)
          (input := input) VE pub Sim T).comap (stmt ∘ Prod.fst)) Q (stmt ∘ Prod.fst)
            (okAt A refuses pubOf keys Q a ds) +
          (ENNReal.ofReal (M.zkError δ t Q) + 2 * Q * εc + Q * refusalGap adm keys refuses) := by
        rw [PMF.tsum_pmf_mul_add, ENNReal.tsum_mul_sum_comm]
    _ ≤ _ := add_le_add (Finset.sum_le_sum fun ds _ => mul_le_mul_of_nonneg_left (hs ds) zero_le)
        le_rfl
    _ = _ := by
        simp_rw [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hσ, one_mul]

/-! ### The headline -/

omit [Nonempty M.NIProof] [Nonempty B.Msg] [Nonempty B.Pub] [Nonempty B.BSig] [DecidableEq X₀]
  ert [Fintype TS.BSig] [DecidableEq TS.BSig] [Nonempty TS.KeyCoins] in
/-- The requests of the history of a run are the first `Q` logged requests. -/
theorem map_request_history (keys : Fin n → B.KeyCoins) (Q : ℕ) (a : (A.at keys).Aux)
    (v : ((A.at keys).alg a).toKindAlg.CW
      (unforgeChallenger (ofBase B 𝒫 adm) n (SideOracle.none _) keys Q)) :
    (((A.at keys).alg a).history _ v).map HistoryEntry.request =
      (Quantum.requests v.chal.logs).take Q :=
  KindAlg.map_request_history_stateAt _ _ _ _

omit [Nonempty B.Msg] [Nonempty B.Pub] [Nonempty B.BSig] in
omit [Fintype TS.BSig] [DecidableEq TS.BSig] in
/-- **The insider game splits by the ring of the forgery**: the forgery probability is at most the
average, over the users' key coins, the auxiliary input and the oracle, of a win with a nonempty
ring (`Wins`), plus the knowledge error at `t + Q · q + kq` queries for the forgeries on the empty
ring, which have no witness (`hz.sound`; `Quantum.AdaptiveIAlg.acceptsTest_le_of_knowledgeBound`). -/
theorem forgeProb_le_wins_add [Nonempty M.NIProof]
    (hz : ZKRingHyps B adm stmt check input fw enc relH rel wit)
    {Ext : CausalExtractor P τ X₀ WitK} {St : CausalStateFn P τ X₀}
    {ε : ChIdx P τ → NNReal} (hrbr : CausalRBRKnowledgeSound rel Vr Ext St ε) (Q : ℕ) :
    insiderForgeProb A Q ≤
      ∑' keys, PMF.uniformOfFintype (Fin n → B.KeyCoins) keys *
        ∑' a, (A.at keys).aux a * ∑' H, PMF.uniformOfFintype (Bits (queryBits k kN kS L) → XOut k e) H *
          ((((A.at keys).alg a).toKindAlg.composeBothOut
            (unforgeChallenger (ofBase B 𝒫 adm) n (SideOracle.none _) keys Q) id).outLaw
            H).toOuterMeasure
          {o | ∃ v ∈ o, Wins keys Q (((A.at keys).alg a).out v.adv.workspace.1)
            (Quantum.requests v.chal.logs) (outEquiv k e ∘ H)} +
        SPBCS.knowledgeError k e (kqOf Mg nr b b)
          (t + Q * (ofBase B 𝒫 adm).q + kqOf Mg nr b b) M.senc.digestsPerInput Mg.nJ
          (maxError ε) := by
  classical
  have hkq : ∀ x h π, M.Accepts h x π (Qs x) → (M.queries x π h (Qs x)).length ≤ kqOf Mg nr b b :=
    fun _ _ _ hv => queries_length_le_of_formatBounds hb hv
  set KE := SPBCS.knowledgeError k e (kqOf Mg nr b b) (t + Q * (ofBase B 𝒫 adm).q + kqOf Mg nr b b)
    M.senc.digestsPerInput Mg.nJ (maxError ε)
  set Ev : (Fin n → B.KeyCoins) → (Bits (queryBits k kN kS L) → Out k e) →
      (Output 𝒫 adm ×
        UnforgeHist (S := ofBase B 𝒫 adm) n (SideOracle.none _)) → Prop :=
    fun keys G y => check ⟨y.1.1, y.1.2.1, y.1.2.2.1⟩ = true ∧
      (∃ c ∈ Ring.spbcsComapClaim M stmt (⟨y.1.1, y.1.2.1, y.1.2.2.1⟩ : RingStmt B) y.1.2.2.2,
        (M.qVerifier Qs b b).Accepted G c) ∧
      FreshAt keys (y.2.map HistoryEntry.request) y.1.1 y.1.2.1 with hEv
  have hE : ∀ keys H y, Forges keys H y.1 y.2 → Ev keys (outEquiv k e ∘ H) y := by
    intro keys H y hf
    have hv : (𝒫).verify H ⟨y.1.1, y.1.2.1, y.1.2.2.1⟩ y.1.2.2.2 = true := hf.verify_eq
    obtain ⟨hck, hacc⟩ :=
      (Ring.verify_spbcsComapProofSystem_eq_true_iff M Λ E hb honest stmt check input H _ _).1 hv
    exact ⟨hck, hacc, Fresh.freshAt hf.fresh⟩
  refine (forgeProb_le_tsum_realLaw A Q Ev hE).trans ?_
  -- the bound at each key and auxiliary value
  have hsplit : ∀ keys a, (((A.runAt Q keys a).realLaw (outEquiv k e))).toOuterMeasure
      {p | ∃ y ∈ p.out, Ev keys p.oracle y} ≤
      ∑' H, PMF.uniformOfFintype (Bits (queryBits k kN kS L) → XOut k e) H *
        ((((A.at keys).alg a).toKindAlg.composeBothOut
          (unforgeChallenger (ofBase B 𝒫 adm) n (SideOracle.none _) keys Q) id).outLaw
          H).toOuterMeasure
        {o | ∃ v ∈ o, Wins keys Q (((A.at keys).alg a).out v.adv.workspace.1)
          (Quantum.requests v.chal.logs) (outEquiv k e ∘ H)} + KE := by
    intro keys a
    have hle : (((A.runAt Q keys a).realLaw (outEquiv k e))).toOuterMeasure
        {p | ∃ y ∈ p.out, Ev keys p.oracle y} ≤
        (((A.runAt Q keys a).realLaw (outEquiv k e))).toOuterMeasure
          {p | ∃ y ∈ p.out, Ev keys p.oracle y ∧ y.1.1.1 ≠ []} +
        (((A.runAt Q keys a).realLaw (outEquiv k e))).toOuterMeasure
          {p | ∃ y ∈ p.out, (M.qVerifier Qs b b).Accepted p.oracle (claimOfOut y.1) ∧
            (y.1.1.1 = [] ∧ check ⟨y.1.1, y.1.2.1, y.1.2.2.1⟩ = true)} := by
      refine le_trans (MeasureTheory.measure_mono ?_) (MeasureTheory.measure_union_le _ _)
      rintro p ⟨y, hy, hev⟩
      by_cases hr : y.1.1.1 = []
      · obtain ⟨c, hc, hacc⟩ := hev.2.1
        exact Or.inr ⟨y, hy, (claimOfOut_eq hc).symm ▸ hacc, hr, hev.1⟩
      · exact Or.inl ⟨y, hy, hev, hr⟩
    refine hle.trans (add_le_add (le_of_eq ?_) ?_)
    · rw [Alg.toOuterMeasure_realLaw_eq_tsum _ _ fun y G => Ev keys G y ∧ y.1.1.1 ≠ []]
      refine tsum_congr fun H => congrArg (_ * ·) ?_
      rw [KindAlg.toOuterMeasure_outLaw_composeBothOut_readout]
      congr 1
      ext o
      refine exists_congr fun v => and_congr_right fun _ => ?_
      rw [hEv]
      dsimp only
      erw [map_request_history A keys Q a v]
      constructor
      · rintro ⟨⟨hck, hacc, hfr⟩, hne⟩
        exact ⟨hck, hacc, hfr, hne⟩
      · rintro ⟨hck, hacc, hfr, hne⟩
        exact ⟨⟨hck, hacc, hfr⟩, hne⟩
    · have h := Quantum.AdaptiveIAlg.acceptsTest_le_of_knowledgeBound
        (M.knowledgeBound rel Ext St hrbr Qs _ hkq) ((A.at keys).alg a)
        (unforgeChallenger (ofBase B 𝒫 adm) n (SideOracle.none _) keys Q)
        (fun v => (((A.at keys).alg a).output _ v, ((A.at keys).alg a).history _ v))
        (fun y => claimOfOut y.1) (fun y => y.1.1.1 = [] ∧ check ⟨y.1.1, y.1.2.1, y.1.2.2.1⟩ = true)
        ((A.at keys).queries_le a)
      refine (h.trans (add_le_add (le_of_eq (simProb_eq_zero _ _ ?_)) le_rfl)).trans ?_
      · rintro y D ⟨⟨hr, hck⟩, w, -, hw⟩
        have hw' : (stmt ⟨y.1.1, y.1.2.1, y.1.2.2.1⟩, w) ∈ rel := by
          have hs := claimOfOut_stmt (M := M) (Λ := Λ) (E := E) (hb := hb) (honest := honest)
            (Qs := Qs) (check := check) (input := input) (adm := adm) y.1
          change ((claimOfOut y.1).stmt, w) ∈ rel at hw
          rw [hs] at hw
          exact hw
        have hl := (hz.sound _ w hck hw').idx_lt
        change _ < y.1.1.1.length at hl
        rw [hr] at hl
        exact Nat.not_lt_zero _ hl
      · have hq : (unforgeChallenger (ofBase B 𝒫 adm) n (SideOracle.none _) keys Q).q =
            (ofBase B 𝒫 adm).q := max_eq_left (Nat.zero_le _)
        rw [zero_add, hq]
        rfl
  calc _ ≤ ∑' keys, PMF.uniformOfFintype (Fin n → B.KeyCoins) keys *
        (∑' a, (A.at keys).aux a * ∑' H, PMF.uniformOfFintype (Bits (queryBits k kN kS L) → XOut k e) H *
          ((((A.at keys).alg a).toKindAlg.composeBothOut
            (unforgeChallenger (ofBase B 𝒫 adm) n (SideOracle.none _) keys Q) id).outLaw
            H).toOuterMeasure
          {o | ∃ v ∈ o, Wins keys Q (((A.at keys).alg a).out v.adv.workspace.1)
            (Quantum.requests v.chal.logs) (outEquiv k e ∘ H)} + KE) :=
        ENNReal.tsum_le_tsum fun keys => mul_le_mul_of_nonneg_left
          (PMF.tsum_pmf_mul_le_add _ _ _ _ (hsplit keys)) zero_le
    _ = _ := PMF.tsum_pmf_mul_add _ _ _

open Classical in
/-- **The success probability of the extraction forger without signing requests at every number of
users**: `zkForgerSuccess` when there is a user and a proof of the compiled format exists; `0`
otherwise (with no user every forgery has the empty ring, and with no proof there is no forgery). -/
noncomputable def zkForgerTerm (wit : RingStmt B → WitK → RingWit B)
    (refuses : KeyRing B.PK N → ℕ → B.Msg → B.Coins → Prop) (pubOf : B.Coins → B.Pub)
    (VE : M.ViewEncoder E Qs) {Pub : Type} (pub : X₀ → Pub)
    (Sim : CausalJointSimulator VE.MV Pub) (T : M.Preimages)
    (Ext : CausalExtractor P τ X₀ WitK) (Q : ℕ) : ℝ≥0∞ :=
  if h : NeZero n ∧ Nonempty M.NIProof then
    haveI := h.1
    haveI := h.2
    zkForgerSuccess (ert := ert) A wit refuses pubOf VE pub Sim T Ext Q
  else 0

/-- **A weighted sum with an affine summand**: `∑ u a (f a + (c + q g a)) = ∑ u a f a + c + q ∑ u a g a`
for a probability mass function `u`. -/
theorem tsum_pmf_mul_add_add {α : Type*} (u : PMF α) (f g : α → ℝ≥0∞) (c q : ℝ≥0∞) :
    ∑' a, u a * (f a + (c + q * g a)) = ∑' a, u a * f a + c + q * ∑' a, u a * g a := by
  have h : ∀ a, u a * (f a + (c + q * g a)) = u a * f a + u a * c + q * (u a * g a) := fun a => by
    ring
  simp_rw [h]
  rw [ENNReal.tsum_add, ENNReal.tsum_add, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul,
    ENNReal.tsum_mul_left]

omit [Nonempty M.NIProof] in
/-- **Unforgeability with respect to insider corruption (BKM06 Definition 7) of the ring signature
compiled by spBCS at a program's statements, at every base message, from zero knowledge and
simulation extraction, at a predicted refusal**, for base signers whose public value is a function
of the signing coins (`hpub`; Falcon's salt, `Unit`) and that refuse whenever `refuses` predicts it
(`hsound`): for an oracle-free base signer (`hB`) with
correctness error `εc` (`hcorr`), the spBCS compilation `M` of a composite over the program's
statements that is honest-verifier zero knowledge with error `δ` for the relation `relH` at the
joint simulator `Sim` (`hvzk`) and round-by-round knowledge sound for the relation `rel` at the
extractor `Ext` with errors `ε` (`hrbr`), the ring signature reading ring statements through
`stmt`, `check` and `input` under the hypotheses `hz` (`ZKRingHyps`), with the proof format bounded
by `b` (`hb`) and digests of at least one byte (`hk`): the forgery probability of an adversary of
BKM06 Definition 7 against `ofBase B (spbcsComapProofSystem …) adm` (start input the honest public
keys, the oracle by at most `t` queries, `Q` requests) is at most the success of the extraction
forger without signing requests (`zkForgerTerm`), plus the zero-knowledge error `zkError δ t Q`,
the simulation-extraction error at the simulator's queries, the knowledge error at `t + Q · q + kq`
queries (forgeries on the empty ring) and `2 Q εc` (a ring signature whose base signature fails to
verify, once in the real game and once in the simulated one), plus `Q` times the average over the
users' key coins of the rate of refusals that `refuses` does not predict (`refusalGap`: the
simulated ring signatures answer them, the game refuses them). -/
theorem insiderForgeProb_le_zk_gap [NeZero k] (hB : B.OracleFree)
    {refuses : KeyRing B.PK N → ℕ → B.Msg → B.Coins → Prop} {pubOf : B.Coins → B.Pub}
    (hpub : B.PubOfCoins pubOf) (hsound : B.RefusalSound refuses) {εc : ℝ≥0∞}
    (hcorr : B.CorrectWithin εc) (hz : ZKRingHyps B adm stmt check input fw enc relH rel wit)
    (VE : M.ViewEncoder E Qs) {Pub : Type} (pub : X₀ → Pub)
    (Sim : CausalJointSimulator VE.MV Pub) (T : M.Preimages) {δ : NNReal}
    (hvzk : CausalHVZK VE.MV relH honest pub Sim δ)
    {Ext : CausalExtractor P τ X₀ WitK} {St : CausalStateFn P τ X₀}
    {ε : ChIdx P τ → NNReal} (hrbr : CausalRBRKnowledgeSound rel Vr Ext St ε)
    (Q : ℕ) :
    insiderForgeProb A Q ≤
      zkForgerTerm (ert := ert) A wit refuses pubOf VE pub Sim T Ext Q + ENNReal.ofReal (M.zkError δ
          t Q) +
        M.simExtractionError (kqOf Mg nr b b) (maxError ε)
          (M.niJointSimulatorProg Λ VE.toViewRead b pub Sim T).q t Q +
        SPBCS.knowledgeError k e (kqOf Mg nr b b)
          (t + Q * (ofBase B 𝒫 adm).q + kqOf Mg nr b b) M.senc.digestsPerInput Mg.nJ
          (maxError ε) +
        2 * Q * εc +
        Q * ∑' keys, PMF.uniformOfFintype (Fin n → B.KeyCoins) keys * refusalGap adm keys refuses := by
  by_cases hP : Nonempty M.NIProof
  swap
  · refine le_trans (le_of_eq ((PMF.toOuterMeasure_apply_eq_zero_iff _ _).2
      (Set.disjoint_left.2 fun x _ hx => ?_))) zero_le
    obtain ⟨p, -, hf⟩ := hx
    have hv : (𝒫).verify x.2.1 ⟨p.1.1, p.1.2.1, p.1.2.2.1⟩ p.1.2.2.2 = true := hf.verify_eq
    obtain ⟨-, c, hc, -⟩ :=
      (Ring.verify_spbcsComapProofSystem_eq_true_iff M Λ E hb honest stmt check input _ _ _).1 hv
    exact hP ⟨c.proof⟩
  refine (forgeProb_le_wins_add A hz hrbr Q).trans ?_
  set KE := SPBCS.knowledgeError k e (kqOf Mg nr b b) (t + Q * (ofBase B 𝒫 adm).q + kqOf Mg nr b b)
    M.senc.digestsPerInput Mg.nJ (maxError ε)
  by_cases hn : n = 0
  · have h0 : ∀ keys : Fin n → B.KeyCoins, ∀ a, ∀ H : Bits (queryBits k kN kS L) → XOut k e,
        ((((A.at keys).alg a).toKindAlg.composeBothOut
          (unforgeChallenger (ofBase B 𝒫 adm) n (SideOracle.none _) keys Q) id).outLaw
          H).toOuterMeasure
        {o | ∃ v ∈ o, Wins keys Q (((A.at keys).alg a).out v.adv.workspace.1)
          (Quantum.requests v.chal.logs) (outEquiv k e ∘ H)} = 0 := by
      intro keys a H
      refine (PMF.toOuterMeasure_apply_eq_zero_iff _ _).2 (Set.disjoint_left.2 fun o _ ho => ?_)
      obtain ⟨v, -, -, -, hfr, hne⟩ := ho
      obtain ⟨pk, rest, hpk⟩ := List.exists_cons_of_ne_nil hne
      obtain ⟨i, -⟩ := hfr.honest_ring pk (by rw [hpk]; exact List.mem_cons_self)
      exact (hn ▸ i : Fin 0).elim0
    simp only [h0, mul_zero, tsum_zero, zero_add]
    exact (le_add_self.trans le_self_add).trans le_self_add
  · have : NeZero n := ⟨hn⟩
    have hdef : zkForgerTerm (ert := ert) A wit refuses pubOf VE pub Sim T Ext Q =
        zkForgerSuccess (ert := ert) A wit refuses pubOf VE pub Sim T Ext Q := by
      unfold zkForgerTerm
      rw [dif_pos ⟨inferInstance, hP⟩]
    rw [hdef]
    have hkeys := fun keys => keys_le (ert := ert) A (NeZero.pos
        k) hB hpub hsound hcorr hz VE pub Sim T hvzk hrbr keys Q
    calc ∑' keys, PMF.uniformOfFintype (Fin n → B.KeyCoins) keys *
          ∑' a, (A.at keys).aux a * ∑' H, PMF.uniformOfFintype (Bits (queryBits k kN kS L) → XOut k e) H *
            ((((A.at keys).alg a).toKindAlg.composeBothOut
              (unforgeChallenger (ofBase B 𝒫 adm) n (SideOracle.none _) keys Q) id).outLaw
              H).toOuterMeasure
            {o | ∃ v ∈ o, Wins keys Q (((A.at keys).alg a).out v.adv.workspace.1)
              (Quantum.requests v.chal.logs) (outEquiv k e ∘ H)} + KE
        ≤ ∑' keys, PMF.uniformOfFintype (Fin n → B.KeyCoins) keys *
          (∑ ds, PMF.uniformOfFintype (Fin Q → B.Coins) ds * ∑' a, (A.at keys).aux a *
            simProb (outEquiv k e) (extAdv Qs (seAlg A refuses pubOf keys Q a ds)
                ((seSim (ert := ert) (Λ := Λ) (hb := hb) (honest := honest) (stmt := stmt) (check :=
                    check)
                  (input := input) VE pub Sim T).comap (stmt ∘ Prod.fst)) Q
                (kqOf Mg nr b b))
              (forgerWins A wit refuses pubOf keys Q a ds
                ((seSim (ert := ert) (Λ := Λ) (hb := hb) (honest := honest) (stmt := stmt) (check :=
                    check)
                  (input := input) VE pub Sim T).comap (stmt ∘ Prod.fst)) Ext) +
            (M.simExtractionError (kqOf Mg nr b b) (maxError ε)
              (M.niJointSimulatorProg Λ VE.toViewRead b pub Sim T).q t Q +
              (ENNReal.ofReal (M.zkError δ t Q) + 2 * Q * εc) +
              Q * refusalGap adm keys refuses)) + KE :=
          add_le_add (ENNReal.tsum_le_tsum fun keys => mul_le_mul_of_nonneg_left
            ((hkeys keys).trans_eq (by ring)) zero_le) le_rfl
      _ = _ := by
          rw [tsum_pmf_mul_add_add, zkForgerSuccess]
          ring

omit [Nonempty M.NIProof] in
/-- **Unforgeability with respect to insider corruption (BKM06 Definition 7) of the ring signature
compiled by spBCS at a program's statements, at every base message, from zero knowledge and
simulation extraction**, for base signers whose public value and refusals are functions of the
signing coins (`hpub`, `href`; Falcon's salt, `Unit`): for an oracle-free base signer (`hB`) with
correctness error `εc` (`hcorr`), the spBCS compilation `M` of a composite over the program's
statements that is honest-verifier zero knowledge with error `δ` for the relation `relH` at the
joint simulator `Sim` (`hvzk`) and round-by-round knowledge sound for the relation `rel` at the
extractor `Ext` with errors `ε` (`hrbr`), the ring signature reading ring statements through
`stmt`, `check` and `input` under the hypotheses `hz` (`ZKRingHyps`), with the proof format bounded
by `b` (`hb`) and digests of at least one byte (`hk`): the forgery probability of an adversary of
BKM06 Definition 7 against `ofBase B (spbcsComapProofSystem …) adm` (start input the honest public
keys, the oracle by at most `t` queries, `Q` requests) is at most the success of the extraction
forger without signing requests (`zkForgerTerm`), plus the zero-knowledge error `zkError δ t Q`,
the simulation-extraction error at the simulator's queries, the knowledge error at `t + Q · q + kq`
queries (forgeries on the empty ring) and `2 Q εc` (a ring signature whose base signature fails to
verify, once in the real game and once in the simulated one). -/
theorem insiderForgeProb_le_zk [NeZero k] (hB : B.OracleFree)
    {refuses : KeyRing B.PK N → ℕ → B.Msg → B.Coins → Prop} {pubOf : B.Coins → B.Pub}
    (hpub : B.PubOfCoins pubOf) (href : B.RefusalOfCoins refuses) {εc : ℝ≥0∞}
    (hcorr : B.CorrectWithin εc) (hz : ZKRingHyps B adm stmt check input fw enc relH rel wit)
    (VE : M.ViewEncoder E Qs) {Pub : Type} (pub : X₀ → Pub)
    (Sim : CausalJointSimulator VE.MV Pub) (T : M.Preimages) {δ : NNReal}
    (hvzk : CausalHVZK VE.MV relH honest pub Sim δ)
    {Ext : CausalExtractor P τ X₀ WitK} {St : CausalStateFn P τ X₀}
    {ε : ChIdx P τ → NNReal} (hrbr : CausalRBRKnowledgeSound rel Vr Ext St ε)
    (Q : ℕ) :
    insiderForgeProb A Q ≤
      zkForgerTerm (ert := ert) A wit refuses pubOf VE pub Sim T Ext Q + ENNReal.ofReal (M.zkError δ
          t Q) +
        M.simExtractionError (kqOf Mg nr b b) (maxError ε)
          (M.niJointSimulatorProg Λ VE.toViewRead b pub Sim T).q t Q +
        SPBCS.knowledgeError k e (kqOf Mg nr b b)
          (t + Q * (ofBase B 𝒫 adm).q + kqOf Mg nr b b) M.senc.digestsPerInput Mg.nJ
          (maxError ε) +
        2 * Q * εc := by
  refine (insiderForgeProb_le_zk_gap (ert := ert) A hB hpub href.refusalSound hcorr hz VE pub Sim T
      hvzk hrbr
    Q).trans_eq ?_
  simp only [refusalGap_eq_zero href, mul_zero, tsum_zero, add_zero]

omit [Nonempty M.NIProof] in
/-- **Unforgeability with respect to insider corruption (BKM06 Definition 7) by zero knowledge and
simulation extraction, for a base signer whose refusals are bounded per key**: the bound of
`insiderForgeProb_le_zk_gap` at the empty refusal predicate (the simulated ring signatures never
refuse), for a per-key refusal rate at most `ρ` (`hρ`, `RefuseAtWithin`), at the cost `Q · ρ`. -/
theorem insiderForgeProb_le_zk_refuseAt [NeZero k] (hB : B.OracleFree) {pubOf : B.Coins → B.Pub}
    (hpub : B.PubOfCoins pubOf) {ρ : ℝ≥0∞} (hρ : B.RefuseAtWithin adm ρ) {εc : ℝ≥0∞}
    (hcorr : B.CorrectWithin εc) (hz : ZKRingHyps B adm stmt check input fw enc relH rel wit)
    (VE : M.ViewEncoder E Qs) {Pub : Type} (pub : X₀ → Pub)
    (Sim : CausalJointSimulator VE.MV Pub) (T : M.Preimages) {δ : NNReal}
    (hvzk : CausalHVZK VE.MV relH honest pub Sim δ)
    {Ext : CausalExtractor P τ X₀ WitK} {St : CausalStateFn P τ X₀}
    {ε : ChIdx P τ → NNReal} (hrbr : CausalRBRKnowledgeSound rel Vr Ext St ε)
    (Q : ℕ) :
    insiderForgeProb A Q ≤
      zkForgerTerm (ert := ert) A wit (fun _ _ _ _ => False) pubOf VE pub Sim T Ext Q +
        ENNReal.ofReal (M.zkError δ t Q) +
        M.simExtractionError (kqOf Mg nr b b) (maxError ε)
          (M.niJointSimulatorProg Λ VE.toViewRead b pub Sim T).q t Q +
        SPBCS.knowledgeError k e (kqOf Mg nr b b)
          (t + Q * (ofBase B 𝒫 adm).q + kqOf Mg nr b b) M.senc.digestsPerInput Mg.nJ
          (maxError ε) +
        2 * Q * εc + Q * ρ := by
  refine (insiderForgeProb_le_zk_gap (ert := ert) A hB hpub B.refusalSound_false hcorr hz VE pub Sim
      T hvzk
    hrbr Q).trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left ?_ zero_le))
  refine (ENNReal.tsum_le_tsum fun keys => mul_le_mul_of_nonneg_left
    (refusalGap_false_le hρ keys) zero_le).trans ?_
  rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

omit [Nonempty M.NIProof] in
/-- **Unforgeability with respect to insider corruption (BKM06 Definition 7) by zero knowledge and
simulation extraction, for a base signer whose refusal rate is bounded on average over the honest
key coins**: the bound of `insiderForgeProb_le_zk_gap` at the empty refusal predicate, for a refusal
rate averaged over the key coins at most `ρ` (`hρ`, `RefuseAvgWithin`), at the cost `Q · n · ρ`
(the adversary chooses the user of each request after seeing the public keys). -/
theorem insiderForgeProb_le_zk_refuseAvg [NeZero k] (hB : B.OracleFree) {pubOf : B.Coins → B.Pub}
    (hpub : B.PubOfCoins pubOf) {ρ : ℝ≥0∞} (hρ : B.RefuseAvgWithin adm ρ) {εc : ℝ≥0∞}
    (hcorr : B.CorrectWithin εc) (hz : ZKRingHyps B adm stmt check input fw enc relH rel wit)
    (VE : M.ViewEncoder E Qs) {Pub : Type} (pub : X₀ → Pub)
    (Sim : CausalJointSimulator VE.MV Pub) (T : M.Preimages) {δ : NNReal}
    (hvzk : CausalHVZK VE.MV relH honest pub Sim δ)
    {Ext : CausalExtractor P τ X₀ WitK} {St : CausalStateFn P τ X₀}
    {ε : ChIdx P τ → NNReal} (hrbr : CausalRBRKnowledgeSound rel Vr Ext St ε)
    (Q : ℕ) :
    insiderForgeProb A Q ≤
      zkForgerTerm (ert := ert) A wit (fun _ _ _ _ => False) pubOf VE pub Sim T Ext Q +
        ENNReal.ofReal (M.zkError δ t Q) +
        M.simExtractionError (kqOf Mg nr b b) (maxError ε)
          (M.niJointSimulatorProg Λ VE.toViewRead b pub Sim T).q t Q +
        SPBCS.knowledgeError k e (kqOf Mg nr b b)
          (t + Q * (ofBase B 𝒫 adm).q + kqOf Mg nr b b) M.senc.digestsPerInput Mg.nJ
          (maxError ε) +
        2 * Q * εc + Q * (n * ρ) := by
  refine (insiderForgeProb_le_zk_gap (ert := ert) A hB hpub B.refusalSound_false hcorr hz VE pub Sim
      T hvzk
    hrbr Q).trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left ?_ zero_le))
  exact tsum_refusalGap_false_le hρ

/-! ### The identity reading and the programs' proof systems -/

end SPBCS'


end RingSignature.Insider


end GordieHowe
