-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Ring.RingInsiderRelays

@[expose] public section

/-!
# The relays of the insider game of `ofBase` whose public values read the key

The relays of `GordieHowe/Applications/Ring/RingInsiderRelays.lean` for an oracle-free base signer
(`BaseSigner.OracleFree`) whose public values and refusals need not be functions of the signing
coins (no `BaseSigner.PubOfCoins`, no `BaseSigner.RefusalOfCoins`). The relays here read the users'
key coins: the base signature of a request is `bsigOf` at its coins, a refusal is `bsigOf … = none`,
and the public value is that of the base signature at the zero oracle.

- `signerInK`: a ring-signing request by a member of a supported ring whose base signature at the
  coins is output; `pubAtK`: the public value of that signature; `stmtAtK`: the statement
  `(R, m, pubAtK …)` of such a request, `dummyStmt` otherwise; `sideAnswerK`: the reply from the
  main reply; `zkStmtK`: the statement of a proof query, `dummyStmt` unless the base signature
  verifies; `zkRelayK enc`: the relay of proof queries, injective per request number
  (`zkRelayK_route_injective`).
- `stmtAtK_of_not`, `stmtAtK_sign`, `mem_ringRel_iffK`, `zkStmtK_of_drawOk`, `zkStmtK_ring_nil`,
  `mem_relZ_iffK`: the relayed queries are in the ring relation, or in a relation `relH` of program
  statements and encoded witnesses, exactly for a member's request that signs and verifies.
- `simReplyK`, `simSplitK`: the simulated challengers with the test `ok`; `coins_simSplitK`.
- `relays_realK`, `relays_sim_zkK`: the checked game relays the real zero-knowledge challenger, the
  checked simulated game the simulated zero-knowledge challenger.
- `simChecked_leK`: unchecking the simulated game costs `Q · ε`.
-/

namespace GordieHowe

open Quantum
open scoped ENNReal

namespace RingSignature.Insider

open GordieHowe.QROM

variable {X Y : Type} {N : ℕ} {TB : BaseTypes}
  (B : BaseSigner X Y N TB) {TPS : PSTypes}
  {PS : ProofSystem X Y (RingStmt B) (RingWit B) TPS}
  {adm : KeyRing B.PK N → Prop} [DecidablePred adm] {n : ℕ}
  [Nonempty B.Msg] [Nonempty B.Pub] [Nonempty B.BSig] [AddGroup Y]

/-! ### Requests, statements and replies read from the keys -/

variable [DecidableEq TB.PK]

/-- **The request is a ring-signing request by a member whose base signature is output**: a
request `(s, R, m)` with the signer's key in the supported ring `R` and `bsigOf` at the signing
coins `sc` outputting a signature. -/
def signerInK (keys : Fin n → B.KeyCoins) (sc : B.Coins) : Req B PS adm n → Prop
  | .sign s R m => B.pk (keys s) ∈ R.1 ∧ adm R ∧ bsigOf B keys sc s R m ≠ none
  | _ => False

/-- **The public value of user `s`'s base signature** at the coins `sc`, at the zero oracle; an
arbitrary value on a refusal. -/
noncomputable def pubAtK (keys : Fin n → B.KeyCoins) (sc : B.Coins) (s : Fin n)
    (R : KeyRing B.PK N) (m : B.Msg) : B.Pub :=
  ((bsigOf B keys sc s R m).map fun σ => (B.pub (B.pk (keys s)) σ).run 0).getD
    (Classical.arbitrary _)

open Classical in
/-- **The statement of request number `c`** read from the keys: for a ring-signing request
`(s, R, m)` by a member whose base signature at the request's coins `ds c` is output,
`(R, m, pubAtK …)`; otherwise `dummyStmt`. -/
noncomputable def stmtAtK (keys : Fin n → B.KeyCoins) {Q : ℕ} (ds : Fin Q → B.Coins) (c : ℕ)
    (r : Req B PS adm n) : RingStmt B :=
  if h : c < Q then
    if signerInK B keys (ds ⟨c, h⟩) r then
      match r with
      | .sign s R m => ⟨R, m, pubAtK B keys (ds ⟨c, h⟩) s R m⟩
      | _ => dummyStmt B
    else dummyStmt B
  else dummyStmt B

open Classical in
/-- **The reply to request number `c < Q`** from the main reply `a`, read from the keys: the key
coins of a corrupted user, or for a ring-signing request by a member whose base signature is
output the main proof with the public value `pubAtK …` as a ring signature; `none` otherwise and
from request `Q` on. -/
noncomputable def sideAnswerK (keys : Fin n → B.KeyCoins) {Q : ℕ} (ds : Fin Q → B.Coins) (c : ℕ)
    (r : Req B PS adm n) (a : Option PS.Proof) : Option (Resp B PS adm) :=
  if h : c < Q then
    match r with
    | .corrupt i => some (.keyCoins (keys i))
    | .sign s R m =>
      if signerInK B keys (ds ⟨c, h⟩) (.sign s R m) then
        a.map fun π => .signature ((pubAtK B keys (ds ⟨c, h⟩) s R m, π) : B.Pub × PS.Proof)
      else none
    | .sideSign _ bm => bm.elim
  else none

open Classical in
/-- **The statement of a proof query** read from the keys: `stmtAtK` of request number `c` when
its base signature at the request's coins verifies (`drawOk`), `dummyStmt` otherwise. -/
noncomputable def zkStmtK (keys : Fin n → B.KeyCoins) {Q : ℕ} (ds : Fin Q → B.Coins) (c : ℕ)
    (r : Req B PS adm n) : RingStmt B :=
  if h : c < Q then
    if drawOk B keys (ds ⟨c, h⟩) r then stmtAtK B keys ds c r else dummyStmt B
  else dummyStmt B

/-- **The relay of proof queries read from the keys** at the users' key coins `keys` and the
signing coins `ds`, with the witnesses encoded by `enc` in `W'`: request number `c` is sent as the
proof query of its statement `zkStmtK` (with the request) and the encoding of its witness `witAt`,
and answered by `sideAnswerK`. -/
noncomputable def zkRelayK {W' : Type} (enc : RingStmt B → RelayWit B → W')
    (keys : Fin n → B.KeyCoins) {Q : ℕ} (ds : Fin Q → B.Coins) :
    SideRelay (Req B PS adm n) (Resp B PS adm) (ProofQuery (RelayStmt B PS adm n) W')
      PS.Proof where
  route c r := ⟨(zkStmtK B keys ds c r, r), enc (zkStmtK B keys ds c r) (witAt B keys ds c r)⟩
  answer := sideAnswerK B keys ds

/-- The relay of proof queries is injective per request number. -/
theorem zkRelayK_route_injective {W' : Type} (enc : RingStmt B → RelayWit B → W')
    (keys : Fin n → B.KeyCoins) {Q : ℕ} (ds : Fin Q → B.Coins) (c : ℕ) :
    Function.Injective ((zkRelayK B enc keys ds (PS := PS) (adm := adm)).route c) :=
  fun _ _ h => congrArg (fun q => q.stmt.2) h

/-! ### The relation on the relayed proof queries -/

variable [Nonempty TB.KeyCoins]

section Relation

variable {B}

omit [Nonempty B.Msg] [Nonempty B.BSig] [Nonempty TB.KeyCoins] in
/-- **The public value of an output base signature** is its public value at the zero oracle. -/
theorem pubAtK_of_eq_some {keys : Fin n → B.KeyCoins} {sc : B.Coins} {s : Fin n}
    {R : KeyRing B.PK N} {m : B.Msg} {σ : B.BSig} (hσ : bsigOf B keys sc s R m = some σ) :
    pubAtK B keys sc s R m = (B.pub (B.pk (keys s)) σ).run 0 := by
  simp only [pubAtK, hσ, Option.map_some, Option.getD_some]

omit [Nonempty B.BSig] [Nonempty TB.KeyCoins] in
/-- A request that is not a ring-signing request by a member that signs has the statement
`dummyStmt`. -/
theorem stmtAtK_of_not {keys : Fin n → B.KeyCoins} {Q : ℕ} {ds : Fin Q → B.Coins} {c : ℕ}
    {r : Req B PS adm n} (h : ¬ ∃ h : c < Q, signerInK B keys (ds ⟨c, h⟩) r) :
    stmtAtK B keys ds c r = dummyStmt B := by
  unfold stmtAtK
  split_ifs with hc hs
  · exact absurd ⟨hc, hs⟩ h
  · rfl
  · rfl

omit [Nonempty B.BSig] [Nonempty TB.KeyCoins] in
/-- The statement of a ring-signing request by a member whose base signature `σ` is output. -/
theorem stmtAtK_sign {keys : Fin n → B.KeyCoins} {Q : ℕ} {ds : Fin Q → B.Coins} {c : ℕ}
    (hc : c < Q) {s : Fin n} {R : KeyRing (ofBase B PS adm).PK N} {m : (ofBase B PS adm).Msg}
    (h : signerInK (PS := PS) (adm := adm) B keys (ds ⟨c, hc⟩) (.sign s R m)) {σ : B.BSig}
    (hσ : bsigOf B keys (ds ⟨c, hc⟩) s R m = some σ) :
    stmtAtK (PS := PS) (adm := adm) B keys ds c (.sign s R m) =
      ⟨R, m, (B.pub (B.pk (keys s)) σ).run 0⟩ := by
  unfold stmtAtK
  rw [dif_pos hc, if_pos h, ← pubAtK_of_eq_some hσ]

omit [Nonempty TB.KeyCoins] in
/-- **The relayed proof query is in the ring relation exactly for a ring-signing request by a
member that signs, numbered below `Q`, whose base signature verifies** (`drawOk`), for an
oracle-free base signer (`hB`). -/
theorem mem_ringRel_iffK (hB : B.OracleFree) (H : X → Y) (keys : Fin n → B.KeyCoins) {Q : ℕ}
    (ds : Fin Q → B.Coins) (c : ℕ) (r : Req B PS adm n) :
    (stmtAtK B keys ds c r, (witAt B keys ds c r).toWit) ∈ ringRel B adm H ↔
      ∃ h : c < Q, signerInK B keys (ds ⟨c, h⟩) r ∧ drawOk B keys (ds ⟨c, h⟩) r := by
  by_cases hex : ∃ h : c < Q, signerInK B keys (ds ⟨c, h⟩) r
  · obtain ⟨hc, hsg⟩ := hex
    cases r with
    | corrupt i => exact hsg.elim
    | sideSign i bm => exact bm.elim
    | sign s R m =>
      obtain ⟨hs, ha, hnr⟩ := id hsg
      obtain ⟨σ, hσ⟩ : ∃ σ, bsigOf B keys (ds ⟨c, hc⟩) s R m = some σ :=
        Option.ne_none_iff_exists'.1 hnr
      rw [stmtAtK_sign hc hsg hσ, witAt_sign keys hc hs, hσ, Option.getD_some]
      have hlt : R.1.idxOf (B.pk (keys s)) < R.1.length := List.idxOf_lt_length_iff.2 hs
      have hget : R.1[R.1.idxOf (B.pk (keys s))]'hlt = B.pk (keys s) := List.getElem_idxOf hlt
      constructor
      · intro h
        have hv := h.verify_eq
        refine ⟨hc, hsg, fun _ _ σ' hσ' => ?_⟩
        rw [hσ] at hσ'
        cases hσ'
        rw [hB.bverify_eq 0 H]
        convert hv using 2
        exact hget.symm
      · rintro ⟨h', -, hd⟩
        refine ⟨ha, hlt, ?_, ?_⟩
        · rw [← hB.bverify_eq 0 H]
          convert hd hs ha σ hσ using 2
        · rw [hB.run_pub_eq _ _ H 0]
          change (B.pub (R.1[R.1.idxOf (B.pk (keys s))]'hlt) σ).run 0 =
            (B.pub (B.pk (keys s)) σ).run 0
          rw [hget]
  · rw [stmtAtK_of_not hex]
    exact iff_of_false (dummyStmt_not_mem_ringRel (adm := adm) H _) (fun ⟨h, h', _⟩ => hex ⟨h, h'⟩)

omit [Nonempty B.BSig] [Nonempty TB.KeyCoins] in
open Classical in
/-- The proof query's statement of a request whose base signature verifies is its statement. -/
theorem zkStmtK_of_drawOk (keys : Fin n → B.KeyCoins) {Q : ℕ} {ds : Fin Q → B.Coins} {c : ℕ}
    (hc : c < Q) {r : Req B PS adm n} (hd : drawOk B keys (ds ⟨c, hc⟩) r) :
    zkStmtK B keys ds c r = stmtAtK B keys ds c r := by
  unfold zkStmtK
  rw [dif_pos hc, if_pos hd]

omit [Nonempty B.BSig] in
open Classical in
omit [Nonempty TB.KeyCoins] in
/-- **The proof query's statement has the empty ring** unless the request is a ring-signing request
by a member that signs whose base signature verifies. -/
theorem zkStmtK_ring_nil (keys : Fin n → B.KeyCoins) {Q : ℕ} {ds : Fin Q → B.Coins} {c : ℕ}
    {r : Req B PS adm n}
    (h : ¬ ∃ h : c < Q, signerInK B keys (ds ⟨c, h⟩) r ∧ drawOk B keys (ds ⟨c, h⟩) r) :
    (zkStmtK B keys ds c r).ring.1 = [] := by
  unfold zkStmtK
  split_ifs with hc hd
  · rw [stmtAtK_of_not fun ⟨hc', hs⟩ => h ⟨hc', hs, hd⟩]
    rfl
  · rfl
  · rfl

omit [Nonempty TB.KeyCoins] in
/-- **The relayed proof query is in a relation `relH` of statements `stmt x` and encoded witnesses
exactly for a ring-signing request by a member that signs, numbered below `Q`, whose base signature
verifies**, when every ring witness's encoding is a witness of `relH` (`hsign`) and no statement of
the empty ring has one (`hnil`), for an oracle-free base signer (`hB`). -/
theorem mem_relZ_iffK (hB : B.OracleFree) {X₀ Wit₀ W' : Type} (stmt : RingStmt B → X₀)
    (fw : W' → Wit₀) (enc : RingStmt B → RelayWit B → W') {relH : Set (X₀ × Wit₀)}
    (hsign : ∀ x (w : RelayWit B), (x, w.toWit) ∈ ringRel B adm 0 → (stmt x, fw (enc x w)) ∈ relH)
    (hnil : ∀ x : RingStmt B, x.ring.1 = [] → ∀ y, (stmt x, y) ∉ relH)
    (keys : Fin n → B.KeyCoins) {Q : ℕ} (ds : Fin Q → B.Coins) (c : ℕ) (r : Req B PS adm n) :
    (stmt (zkStmtK B keys ds c r), fw (enc (zkStmtK B keys ds c r) (witAt B keys ds c r))) ∈
        relH ↔
      ∃ h : c < Q, signerInK B keys (ds ⟨c, h⟩) r ∧ drawOk B keys (ds ⟨c, h⟩) r := by
  by_cases hex : ∃ h : c < Q, signerInK B keys (ds ⟨c, h⟩) r ∧ drawOk B keys (ds ⟨c, h⟩) r
  · refine iff_of_true ?_ hex
    obtain ⟨hc, hs, hd⟩ := hex
    rw [zkStmtK_of_drawOk keys hc hd]
    exact hsign _ _ ((mem_ringRel_iffK hB 0 keys ds c r).2 ⟨hc, hs, hd⟩)
  · exact iff_of_false (hnil _ (zkStmtK_ring_nil keys hex) _) hex

omit [Nonempty B.BSig] [Nonempty TB.KeyCoins] in
/-- The statement of a request depends on the signing coins only at its own number. -/
theorem stmtAtK_congr {keys : Fin n → B.KeyCoins} {Q : ℕ} {ds ds' : Fin Q → B.Coins} {c : ℕ}
    (hc : ∀ h : c < Q, ds ⟨c, h⟩ = ds' ⟨c, h⟩) (r : Req B PS adm n) :
    stmtAtK B keys ds c r = stmtAtK B keys ds' c r := by
  unfold stmtAtK
  split_ifs with h1 h2 h3 h3 <;> first | rfl | (rw [hc h1] at h2; exact absurd h2 h3) |
    (rw [hc h1] at h2; exact absurd h3 h2) | (cases r <;> simp [hc h1])

omit [Nonempty B.Msg] [Nonempty B.BSig] [Nonempty TB.KeyCoins] in
/-- The reply to a request depends on the signing coins only at its own number. -/
theorem sideAnswerK_congr {keys : Fin n → B.KeyCoins} {Q : ℕ} {ds ds' : Fin Q → B.Coins} {c : ℕ}
    (hc : ∀ h : c < Q, ds ⟨c, h⟩ = ds' ⟨c, h⟩) (r : Req B PS adm n) (a : Option PS.Proof) :
    sideAnswerK B keys ds c r a = sideAnswerK B keys ds' c r a := by
  unfold sideAnswerK
  split_ifs with h
  · rw [hc h]
  · rfl

end Relation

/-! ### The challengers at fixed keys -/

variable [Fintype TB.KeyCoins] [DecidableEq TB.KeyCoins]

variable [Fintype TB.PK] [Fintype TB.Msg] [DecidableEq TB.Msg] [Fintype TB.Pub] [DecidableEq TB.Pub]
  [Fintype TB.Coins] [DecidableEq TB.Coins] [Nonempty TB.Coins]

section Challengers

variable [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y] [Fintype TPS.Coins]
  [DecidableEq TPS.Coins] [Nonempty TPS.Coins]

variable {B}

variable {SC : Type} [Fintype SC] [DecidableEq SC]

open Classical in
/-- **The reply of the simulated challengers read from the keys** to request number `i` at the key
coins `keys` and the draw `d` (base signing coins and simulator coins), with the test `ok` of the
draw: a ring-signing request by a member that signs (`signerInK`) whose draw passes `ok` runs `Sim`
on its statement `stmtAtK`, answers with the simulated proof as a ring signature and appends the
simulator's assignments; such a request failing `ok` gets `none`; any other request is answered by
`sideAnswerK` without queries or assignments. -/
noncomputable def simReplyK (keys : Fin n → B.KeyCoins)
    (Sim : NARG.Simulator X Y (RingStmt B) PS.Proof SC) (Q : ℕ)
    (ok : B.Coins → Req B PS adm n → Prop) (d : B.Coins × SC) (i : ℕ) (r : Req B PS adm n) :
    OracleProg X Y (Reply X Y (Resp B PS adm)) :=
  if signerInK B keys d.1 r then
    if ok d.1 r then
      (Sim.prog (stmtAtK B keys (fun _ : Fin Q => d.1) i r) d.2).bind fun o =>
        .pure ⟨sideAnswerK B keys (fun _ : Fin Q => d.1) i r (some o.proof), o.assignments⟩
    else .pure ⟨none, []⟩
  else .pure ⟨sideAnswerK B keys (fun _ : Fin Q => d.1) i r none, []⟩

variable (PS adm) in
/-- **The simulated challengers read from the keys as split challengers**: per request uniform base
signing coins and simulator coins, the replies `simReplyK` with the test `ok`. -/
noncomputable def simSplitK (keys : Fin n → B.KeyCoins)
    (Sim : NARG.Simulator X Y (RingStmt B) PS.Proof SC) (Q : ℕ)
    (ok : B.Coins → Req B PS adm n → Prop) :
    SplitChallenger X Y (Req B PS adm n) (Resp B PS adm) Unit (B.Coins × SC) where
  keys := PMF.pure ()
  draw := (PMF.uniformOfFintype B.Coins).bind fun c => Sim.coins.map fun d => (c, d)
  Q := Q
  q := Sim.q
  reply _ d i r := simReplyK keys Sim Q ok d i r
  reply_queries _ d i r H := by
    unfold simReplyK
    split_ifs
    · rw [OracleProg.trace_bind, OracleProg.trace_pure, List.append_nil]
      exact Sim.prog_queries _ _ H
    · simp
    · simp

omit [Nonempty B.BSig] [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y] [Fintype TPS.Coins]
  [DecidableEq TPS.Coins] [Nonempty TPS.Coins] [Fintype TB.KeyCoins] [DecidableEq TB.KeyCoins]
  [Nonempty TB.KeyCoins] [Fintype TB.PK] [Fintype TB.Msg] [DecidableEq TB.Msg] [Fintype TB.Pub]
  [DecidableEq TB.Pub] in
/-- **The coins of the simulated challengers are uniform signing coins and independent simulator
coins.** -/
theorem coins_simSplitK (keys : Fin n → B.KeyCoins)
    (Sim : NARG.Simulator X Y (RingStmt B) PS.Proof SC) (Q : ℕ)
    (ok : B.Coins → Req B PS adm n → Prop) (ds : Fin Q → B.Coins) (scs : Fin Q → SC) :
    (simSplitK PS adm keys Sim Q ok).toChallenger.coins
        ((coinSplit Q B.Coins SC).symm (ds, scs)) =
      PMF.uniformOfFintype (Fin Q → B.Coins) ds * (PMF.pi fun _ => Sim.coins) scs := by
  change (simSplitK PS adm keys Sim Q ok).coinLaw ((), fun i => (ds i, scs i)) = _
  rw [SplitChallenger.coinLaw_apply, ← PMF.pi_uniformOfFintype, PMF.pi_apply, PMF.pi_apply]
  change PMF.pure () () * ∏ i, ((PMF.uniformOfFintype B.Coins).bind fun c =>
    Sim.coins.map fun d => (c, d)) (ds i, scs i) = _
  rw [PMF.pure_apply_self, one_mul, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i _ => Ring.bind_map_pair_apply _ _ _ _

/-! ### The relays -/

omit [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y] [Fintype SC] [DecidableEq SC] in
open Classical in
omit [Fintype TB.PK] [Fintype TB.Msg] [DecidableEq TB.Msg] [Fintype TB.Pub] [DecidableEq TB.Pub]
  [Fintype TB.KeyCoins] [DecidableEq TB.KeyCoins] [Nonempty TB.KeyCoins] in
/-- **The checked game at fixed keys relays the real zero-knowledge challenger** of a prover `Pz`
of statements `stmt x` on the relayed proof queries read from the keys (`zkRelayK` with the witness
encoding `enc`), for the relation `relH` read at the decoding `fw`, at the signing coins `ds` and
the prover coins `pcs`: when every ring witness's encoding is a witness of `relH` (`hsign`), no
statement of the empty ring has one (`hnil`), and on a ring witness the ring prover is `Pz` at
`(stmt x, fw (enc x w))` (`hP`), for an oracle-free base signer (`hB`). -/
theorem relays_realK (hB : B.OracleFree) {X₀ Wit₀ W' : Type} (stmt : RingStmt B → X₀)
    (fw : W' → Wit₀) (enc : RingStmt B → RelayWit B → W') {relH : Set (X₀ × Wit₀)}
    (hsign : ∀ x (w : RelayWit B), (x, w.toWit) ∈ ringRel B adm 0 → (stmt x, fw (enc x w)) ∈ relH)
    (hnil : ∀ x : RingStmt B, x.ring.1 = [] → ∀ y, (stmt x, y) ∉ relH)
    (Pz : NARG.Prover X Y X₀ Wit₀ PS.Proof PS.Coins)
    (hP : ∀ x (w : RelayWit B) c, (x, w.toWit) ∈ ringRel B adm 0 →
      Pz.prog (stmt x) (fw (enc x w)) c = PS.prove x w.toWit c)
    (keys : Fin n → B.KeyCoins) {Q : ℕ} (ds : Fin Q → B.Coins) (pcs : Fin Q → PS.Coins) :
    (zkRelayK B enc keys ds (PS := PS) (adm := adm)).RelaysChallenger
      (checkedSplit PS adm keys Q).toChallenger ((), fun i => (ds i, pcs i))
      (realChallenger (fun x w => (stmt x.1, fw w) ∈ relH) (Pz.comap (stmt ∘ Prod.fst) fw) (PMF.uniformOfFintype _) Q)
        pcs := by
  refine ⟨rfl, ?_, ?_⟩
  · intro hist hist' r G hrel hQ
    have hlen : hist.length = hist'.length := by
      simpa using (congrArg List.length hrel).symm
    change hist.length < Q at hQ
    have hQ' : hist'.length < Q := hlen ▸ hQ
    have hi : (⟨hist'.length, hQ'⟩ : Fin Q) = ⟨hist.length, hQ⟩ := Fin.ext hlen.symm
    simp only [SplitChallenger.toChallenger, checkedSplit, SplitChallenger.withReply,
      realChallenger, RingScheme.gameSplit, zkRelayK, dif_pos hQ, dif_pos hQ', hi,
      NARG.Prover.comap, Function.comp_apply]
    have hmem := mem_relZ_iffK (PS := PS) (adm := adm) hB stmt fw enc hsign hnil keys ds
      hist.length r
    by_cases hr : ∃ h : hist.length < Q,
        signerInK B keys (ds ⟨hist.length, h⟩) r ∧ drawOk B keys (ds ⟨hist.length, h⟩) r
    · have hxw := (mem_ringRel_iffK hB 0 keys ds hist.length r).2 hr
      obtain ⟨hQ'', hsg, hd⟩ := hr
      rw [if_pos (hmem.2 ⟨hQ'', hsg, hd⟩)]
      rw [zkStmtK_of_drawOk keys hQ'' hd, hP _ _ _ hxw]
      cases r with
      | corrupt i => exact hsg.elim
      | sideSign i bm => exact bm.elim
      | sign s R m =>
        obtain ⟨hs, ha, hnr⟩ := id hsg
        obtain ⟨σ, hσ⟩ : ∃ σ, bsigOf B keys (ds ⟨hist.length, hQ⟩) s R m = some σ :=
          Option.ne_none_iff_exists'.1 hnr
        unfold checkedReply
        rw [if_pos hd]
        erw [run_unforgeReply_sign hB keys _ s R m G]
        rw [if_pos ⟨hs, ha⟩]
        simp only [OracleProg.run_bind, OracleProg.run_pure]
        rw [stmtAtK_sign hQ hsg hσ, witAt_sign keys hQ hs, hσ, Option.getD_some, Option.map_some]
        unfold sideAnswerK
        rw [dif_pos hQ]
        dsimp only
        rw [if_pos hsg, Option.map_some, pubAtK_of_eq_some hσ]
    · rw [if_neg fun h => hr (hmem.1 h)]
      simp only [OracleProg.run_pure]
      cases r with
      | corrupt i =>
        unfold checkedReply
        rw [if_pos (show drawOk (PS := PS) (adm := adm) B keys _ (.corrupt i) from trivial)]
        simp only [RingScheme.unforgeReply, OracleProg.run_pure, sideAnswerK, dif_pos hQ]
      | sideSign i bm => exact bm.elim
      | sign s R m =>
        have hn : sideAnswerK B keys ds hist.length (.sign s R m) (none : Option PS.Proof) =
            none := by
          simp only [sideAnswerK, dif_pos hQ, Option.map_none, ite_self]
        rw [hn]
        unfold checkedReply
        split_ifs with hd
        · erw [run_unforgeReply_sign hB keys _ s R m G]
          split_ifs with hm
          · have hnr : bsigOf B keys (ds ⟨hist.length, hQ⟩) s R m = none := by
              by_contra hnr
              exact hr ⟨hQ, ⟨hm.1, hm.2, hnr⟩, hd⟩
            rw [hnr]
            rfl
          · rfl
        · rfl
  · intro i r h
    change Q ≤ i at h
    simp only [zkRelayK, sideAnswerK, show ¬ i < Q from not_lt.2 h, dite_false]

omit [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y] [Fintype TPS.Coins]
  [DecidableEq TPS.Coins] [Nonempty TPS.Coins] in
open Classical in
omit [Fintype TB.PK] [Fintype TB.Msg] [DecidableEq TB.Msg] [Fintype TB.Pub] [DecidableEq TB.Pub]
  [Fintype TB.KeyCoins] [DecidableEq TB.KeyCoins] [Nonempty TB.KeyCoins] in
/-- **The checked simulated challenger read from the keys relays the simulated zero-knowledge
challenger** of a simulator `Simz` of statements `stmt x` on the relayed proof queries (`zkRelayK`
with the witness encoding `enc`), the simulated ring signatures being `Simz` read at `stmt`, under
the hypotheses of `relays_realK`. -/
theorem relays_sim_zkK (hB : B.OracleFree) {X₀ Wit₀ W' : Type} (stmt : RingStmt B → X₀)
    (fw : W' → Wit₀) (enc : RingStmt B → RelayWit B → W') {relH : Set (X₀ × Wit₀)}
    (hsign : ∀ x (w : RelayWit B), (x, w.toWit) ∈ ringRel B adm 0 → (stmt x, fw (enc x w)) ∈ relH)
    (hnil : ∀ x : RingStmt B, x.ring.1 = [] → ∀ y, (stmt x, y) ∉ relH)
    (keys : Fin n → B.KeyCoins) (Simz : NARG.Simulator X Y X₀ PS.Proof SC) {Q : ℕ}
    (ds : Fin Q → B.Coins) (scs : Fin Q → SC) :
    (zkRelayK B enc keys ds (PS := PS) (adm := adm)).RelaysChallenger
      (simSplitK PS adm keys (Simz.comap stmt) Q (drawOk B keys)).toChallenger
        ((), fun i => (ds i, scs i))
      (simChallenger (fun x w => (stmt x.1, fw w) ∈ relH) (Simz.comap (stmt ∘ Prod.fst)) Q)
        scs := by
  refine ⟨rfl, ?_, ?_⟩
  · intro hist hist' r G hrel hQ
    have hlen : hist.length = hist'.length := by
      simpa using (congrArg List.length hrel).symm
    change hist.length < Q at hQ
    have hQ' : hist'.length < Q := hlen ▸ hQ
    have hi : (⟨hist'.length, hQ'⟩ : Fin Q) = ⟨hist.length, hQ⟩ := Fin.ext hlen.symm
    simp only [SplitChallenger.toChallenger, simSplitK, simChallenger, zkRelayK, dif_pos hQ,
      dif_pos hQ', hi, NARG.Simulator.comap, Function.comp_apply]
    have hst := stmtAtK_congr (PS := PS) (adm := adm) (keys := keys)
      (ds := fun _ : Fin Q => ds ⟨hist.length, hQ⟩) (ds' := ds) (c := hist.length)
      (fun _ => rfl) r
    have hsa := sideAnswerK_congr (PS := PS) (adm := adm) (keys := keys)
      (ds := fun _ : Fin Q => ds ⟨hist.length, hQ⟩) (ds' := ds) (c := hist.length)
      (fun _ => rfl) r
    have hmem := mem_relZ_iffK (PS := PS) (adm := adm) hB stmt fw enc hsign hnil keys ds
      hist.length r
    unfold simReplyK
    simp only [hst, hsa]
    by_cases hs : signerInK B keys (ds ⟨hist.length, hQ⟩) r
    · by_cases hd : drawOk B keys (ds ⟨hist.length, hQ⟩) r
      · rw [if_pos hs, if_pos hd, if_pos (hmem.2 ⟨hQ, hs, hd⟩), zkStmtK_of_drawOk keys hQ hd]
        simp only [OracleProg.run_bind, OracleProg.run_pure]
      · rw [if_pos hs, if_neg hd, if_neg fun h => hd (hmem.1 h).2.2]
        simp only [OracleProg.run_pure]
        cases r with
        | corrupt i => exact hs.elim
        | sideSign i bm => exact bm.elim
        | sign s R m => simp only [sideAnswerK, dif_pos hQ, Option.map_none, ite_self]
    · rw [if_neg hs, if_neg fun h => hs (hmem.1 h).2.1]
      rfl
  · intro i r h
    change Q ≤ i at h
    simp only [zkRelayK, sideAnswerK, show ¬ i < Q from not_lt.2 h, dite_false]

/-! ### The hybrid of the correctness error -/

variable [Nonempty X] [DecidableEq Y] [Fintype TPS.Proof] [DecidableEq TPS.Proof]

omit [Nonempty B.BSig] [Fintype TPS.Coins] [DecidableEq TPS.Coins] [Nonempty TPS.Coins]
  [Nonempty TB.KeyCoins] in
/-- **Replacing the checked simulated replies read from the keys by the unchecked ones costs at
most `Q · ε`** at fixed keys, for a base signer with correctness error `ε`. -/
theorem simChecked_leK {ε : ℝ≥0∞} (hcorr : B.CorrectWithin ε) {O' : Type}
    {ksK : KindShape X Y (Req B PS adm n) (Resp B PS adm)} (K : KindAlg ksK O') (keys : Fin n → B.KeyCoins)
    (Sim : NARG.Simulator X Y (RingStmt B) PS.Proof SC) (Q : ℕ) (H : X → Y)
    (P : DReg K.W K.width X Y (Req B PS adm n) (Resp B PS adm) → LogReg (Req B PS adm n) K.slots →
      (X → Y) → Prop) :
    ((K.composeBothOut (simSplitK PS adm keys Sim Q (drawOk B keys)).toChallenger
        id).outLaw H).toOuterMeasure
        {o | ∃ v ∈ o, P v.adv v.chal.logs (H.reprogram (K.postAss
          (simSplitK PS adm keys Sim Q (drawOk B keys)).toChallenger v.chal))} ≤
      ((K.composeBothOut (simSplitK PS adm keys Sim Q fun _ _ => True).toChallenger
          id).outLaw H).toOuterMeasure
        {o | ∃ v ∈ o, P v.adv v.chal.logs (H.reprogram (K.postAss
          (simSplitK PS adm keys Sim Q fun _ _ => True).toChallenger v.chal))} +
        Q * ε := by
  classical
  refine (simSplitK PS adm keys Sim Q (drawOk B keys)).toOuterMeasure_outLaw_le_add
    (simSplitK PS adm keys Sim Q fun _ _ => True).reply
    (simSplitK PS adm keys Sim Q fun _ _ => True).reply_queries
    (fun κ i r _ => ?_) K H fun a lg _ G => P a lg G
  refine le_trans (MeasureTheory.measure_mono fun d hd => ?_)
    ((Ring.toOuterMeasure_bind_map_fst (α := B.Coins) _ fun c => ¬ drawOk B keys c r).trans_le
      (toOuterMeasure_not_drawOk_le hcorr keys r))
  change ¬ drawOk B keys d.1 r
  intro h
  apply hd
  simp only [simSplitK, simReplyK, if_pos h, if_true]

end Challengers

end RingSignature.Insider

end GordieHowe
