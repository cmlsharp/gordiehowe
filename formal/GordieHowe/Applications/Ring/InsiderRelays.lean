-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Ring.InsiderTools
public import GordieHowe.Model.Quantum.Interactive.SimChallenger

@[expose] public section

/-!
# The side requests of BKM06 Definition 7 and their relays

The requests of an adversary of BKM06 Definition 7 (`BKMRequest`) split into side requests,
answered from values drawn independently of the random oracle, and ring-signing requests, whose
proofs come from a main challenger: the honest prover (`realChallenger`), the zero-knowledge
simulator (`simChallenger`) or the simulator of the simulation-extraction game
(`simExtChallenger`).

- `SideCoins`: the side coins, the users' key-generation coins and, for each of the first `Q`
  requests, signing coins.
- `RelayStmt`, `RelayWit`: the statements and witnesses of the relayed proof queries. A relayed
  statement carries the request, so the relay of each request number is injective.
- `signerIn`: the request is a ring-signing request for an admissible ring that holds the signer's
  key. `stmtAt` is its statement `(R, m, ρ)` with the public value `ρ = pubOf c` of the request's
  signing coins `c` (for a scheme with `SigScheme.PubOfCoins`, the public value of the signature the
  signer computes with them); every other request is sent with `dummyStmt`, a statement with the
  empty ring, which has no witness. `drawVerifies`: the signature drawn for a ring-signing request
  verifies.
- `sideAnswer`: the reply to request number `c` from the main reply: a public key, the coins of a
  corrupted user, or the main proof with the public value as a ring signature.
- `seRelay`, `zkRelay`: the relays of statements and of proof queries (with the honest witness, a
  signature by the signer's secret key).
- `checkedBkmLayer`: the layer of BKM06 whose signer refuses (answers `none`) when its base
  signature fails to verify. `simBKMChallenger S adm pubOf Q`: the challenger of BKM06 with ring
  signatures simulated by `S` on the statements with the public values `pubOf c`;
  `simBKMCheckedChallenger`: the same, refusing when the signature drawn for the request fails to
  verify. The checked challengers differ from the unchecked ones only when a drawn signature fails
  to verify, which the scheme's correctness error bounds.
- `inertOnEmpty S p₀`: the simulator `S`, answering `p₀` without queries or assignments on
  statements with the empty ring.
- `relays_bkm_real`, `relays_sim_zk`, `relays_sim_se`: the checked challenger of BKM06 relays the
  real challenger, the checked simulated challenger relays the zero-knowledge simulation
  challenger, and the simulated challenger relays the simulation-extraction challenger.
-/

namespace GordieHowe.Ring

open Quantum GordieHowe.QROM GordieHowe.SPBCS
open scoped ENNReal

variable {Sch : SigScheme} {n N : ℕ} {RMsg : Type} [Fintype RMsg] [DecidableEq RMsg]

/-- Ring statements as a product. -/
def RingStmt.equivProd (Sch : SigScheme) (RMsg : Type) (N : ℕ) :
    RingStmt Sch RMsg N ≃ RingOf Sch.PK N × RMsg × Sch.Pub where
  toFun x := (x.ring, x.msg, x.pub)
  invFun p := ⟨p.1, p.2.1, p.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance : Fintype (RingStmt Sch RMsg N) :=
  Fintype.ofEquiv _ (RingStmt.equivProd Sch RMsg N).symm

/-! ### Relayed statements and witnesses -/

variable (Sch n N RMsg) in
/-- **The statement register of a relayed request**: a ring statement and the request. -/
abbrev RelayStmt : Type := RingStmt Sch RMsg N × BKMRequest Sch n N RMsg

variable (Sch N) in
/-- **The witness register of a relayed proof query**: a position below `N + 1` and a base
signature. -/
abbrev RelayWit : Type := Fin (N + 1) × Sch.Sig

/-- The ring witness of a witness register. -/
def RelayWit.toWit (w : RelayWit Sch N) : RingWit Sch := ⟨w.1, w.2⟩

variable [Nonempty RMsg]

/-- **The statement of the side requests**: the empty ring, which has no witness. -/
noncomputable def dummyStmt (Sch : SigScheme) (RMsg : Type) [Nonempty RMsg] (N : ℕ) :
    RingStmt Sch RMsg N :=
  ⟨⟨[], Nat.zero_le _⟩, Classical.arbitrary _, Classical.arbitrary _⟩

/-- A base signature, the witness part of the side requests. -/
noncomputable def dummySig (bind : List Sch.PK → RMsg → Sch.Msg) : Sch.Sig :=
  Sch.signWith (Sch.sk (Classical.arbitrary _)) (bind [] (Classical.arbitrary _))
    (Classical.arbitrary _)

noncomputable instance [NeZero n] : Inhabited (RelayStmt Sch n N RMsg) :=
  ⟨(dummyStmt Sch RMsg N, .publicKey 0)⟩

/-! ### The side coins and the relays -/

variable (Sch n) in
/-- **The side coins of `Q` requests**: the users' key-generation coins, and for each request
signing coins. -/
abbrev SideCoins (Q : ℕ) : Type := (Fin n → Sch.KeyCoins) × (Fin Q → Sch.SignCoins)

open Classical in
/-- **The request is a ring-signing request by a member**: for an admissible ring that holds the
signer's key `pkOf s` (at its first position, as `ringSignAfterKey` finds it). -/
def signerIn (pkOf : Fin n → Sch.PK) (adm : List Sch.PK → Prop) : BKMRequest Sch n N RMsg → Prop
  | .ringSign s R _ => adm R.1 ∧ R.1.idxOf (pkOf s) < R.1.length
  | _ => False

open Classical in
/-- **The statement of request number `c`**: for a ring-signing request `(s, R, m)` by a member,
`(R, m, ρ_c)` with the public value `ρ_c` of the request; otherwise `dummyStmt`. -/
noncomputable def stmtAt (pkOf : Fin n → Sch.PK) (adm : List Sch.PK → Prop) {Q : ℕ}
    (pubs : Fin Q → Sch.Pub) (c : ℕ) (r : BKMRequest Sch n N RMsg) : RingStmt Sch RMsg N :=
  if h : c < Q ∧ signerIn pkOf adm r then
    match r with
    | .ringSign _ R m => ⟨R, m, pubs ⟨c, h.1⟩⟩
    | _ => dummyStmt Sch RMsg N
  else dummyStmt Sch RMsg N

open Classical in
/-- **The witness of request number `c`**: for a ring-signing request `(s, R, m)` by a member, the
signer's position in `R` and the signature `signWith sk_s (bind R m) c_c` with the drawn signing
coins; otherwise `(0, dummySig)`. -/
noncomputable def witAt (keys : Fin n → Sch.KeyCoins) (adm : List Sch.PK → Prop)
    (bind : List Sch.PK → RMsg → Sch.Msg) {Q : ℕ} (draws : Fin Q → Sch.SignCoins)
    (c : ℕ) (r : BKMRequest Sch n N RMsg) : RelayWit Sch N :=
  if h : c < Q ∧ signerIn (fun i => Sch.pk (keys i)) adm r then
    match r, h with
    | .ringSign s R m, h =>
      (⟨R.1.idxOf (Sch.pk (keys s)), by
        have h2 : R.1.idxOf (Sch.pk (keys s)) < R.1.length := h.2.2
        have := R.2
        omega⟩,
        Sch.signWith (Sch.sk (keys s)) (bind R.1 m) (draws ⟨c, h.1⟩))
    | .publicKey _, h => absurd h.2 id
    | .corrupt _, h => absurd h.2 id
  else (0, dummySig bind)

omit [Fintype RMsg] [DecidableEq RMsg] [Nonempty RMsg] in
variable (Sch N RMsg) in
/-- **The signature at the signing coins `sc` verifies**: for a ring-signing request `(s, R, m)`,
the signature of user `s` on `bind R m` with `sc` verifies under `s`'s public key; every other
request qualifies. -/
def drawOk (bind : List Sch.PK → RMsg → Sch.Msg) (keys : Fin n → Sch.KeyCoins)
    (sc : Sch.SignCoins) : BKMRequest Sch n N RMsg → Prop
  | .ringSign s R m => Sch.verify (Sch.pk (keys s)) (bind R.1 m)
      (Sch.signWith (Sch.sk (keys s)) (bind R.1 m) sc) = true
  | _ => True

omit [Fintype RMsg] [DecidableEq RMsg] [Nonempty RMsg] in
variable (Sch N RMsg) in
/-- **The signature drawn for request number `c` verifies** (`drawOk` at its drawn signing coins,
for a request numbered below `Q`). -/
def drawVerifies (keys : Fin n → Sch.KeyCoins) (bind : List Sch.PK → RMsg → Sch.Msg) {Q : ℕ}
    (draws : Fin Q → Sch.SignCoins) (c : ℕ) (r : BKMRequest Sch n N RMsg) : Prop :=
  ∀ h : c < Q, drawOk Sch N RMsg bind keys (draws ⟨c, h⟩) r

open Classical in
/-- **The reply to request number `c < Q`** from the main reply `a`: the public key `pkOf i`, the
key-generation coins `kcOf i` of a corrupted user, or for a ring-signing request by a member the
main proof with the request's public value `pubs c` as a ring signature; `none` otherwise and from
request `Q` on. -/
noncomputable def sideAnswer {Resp : Type} (pkOf : Fin n → Sch.PK) (kcOf : Fin n → Sch.KeyCoins)
    (adm : List Sch.PK → Prop) {Q : ℕ} (pubs : Fin Q → Sch.Pub) (c : ℕ)
    (r : BKMRequest Sch n N RMsg) (a : Option Resp) : Option (RingResponse Sch Resp) :=
  if h : c < Q then
    match r with
    | .publicKey i => some (.base (.publicKey (pkOf i)))
    | .corrupt i => some (.base (.keyCoins (kcOf i)))
    | .ringSign s R m =>
      if signerIn pkOf adm (.ringSign s R m) then a.map (.ringSignature (pubs ⟨c, h⟩)) else none
  else none

/-- **The relay of statements** (to the simulator of the simulation-extraction game): request
number `c` is sent as its statement `stmtAt` with the request, and answered by `sideAnswer` from
the public keys `pkOf`, the key-generation coins `kcOf` (read only for corrupted users) and the
public values `pubs`.

Running time: per request, a lookup of the signer's key in the ring and of the public value; per
reply, one lookup of a key or of key-generation coins. This running time is argued here, not
proved in Lean. -/
noncomputable def seRelay {Resp : Type} (pkOf : Fin n → Sch.PK) (kcOf : Fin n → Sch.KeyCoins)
    (adm : List Sch.PK → Prop) {Q : ℕ} (pubs : Fin Q → Sch.Pub) :
    SideRelay (BKMRequest Sch n N RMsg) (RingResponse Sch Resp) (RelayStmt Sch n N RMsg) Resp where
  route c r := (stmtAt pkOf adm pubs c r, r)
  answer := sideAnswer pkOf kcOf adm pubs

/-- **The relay of proof queries** (to the real and the simulated zero-knowledge challengers) at
the side coins `(keys, draws)`, with the public values `pubOf` of the drawn signing coins: request
number `c` is sent as the proof query of its statement `stmtAt` (with the request) and its witness
`witAt`, and answered by `sideAnswer`.

Running time: that of `seRelay`, plus one base signature for a ring-signing request by a member.
This running time is argued here, not proved in Lean. -/
noncomputable def zkRelay {Resp : Type} (adm : List Sch.PK → Prop)
    (bind : List Sch.PK → RMsg → Sch.Msg) (pubOf : Sch.SignCoins → Sch.Pub) {Q : ℕ}
    (s : SideCoins Sch n Q) :
    SideRelay (BKMRequest Sch n N RMsg) (RingResponse Sch Resp)
      (ProofQuery (RelayStmt Sch n N RMsg) (RelayWit Sch N)) Resp where
  route c r := ⟨(stmtAt (fun i => Sch.pk (s.1 i)) adm (fun j => pubOf (s.2 j)) c r, r),
    witAt s.1 adm bind s.2 c r⟩
  answer := sideAnswer (fun i => Sch.pk (s.1 i)) s.1 adm fun j => pubOf (s.2 j)

omit [Fintype RMsg] [DecidableEq RMsg] in
theorem seRelay_route_injective {Resp : Type} (pkOf : Fin n → Sch.PK) (kcOf : Fin n → Sch.KeyCoins)
    (adm : List Sch.PK → Prop) {Q : ℕ} (pubs : Fin Q → Sch.Pub) (c : ℕ) :
    Function.Injective ((seRelay (Resp := Resp) (N := N) (RMsg := RMsg) pkOf kcOf adm pubs).route c) :=
  fun _ _ h => congrArg Prod.snd h

omit [Fintype RMsg] [DecidableEq RMsg] in
theorem zkRelay_route_injective {Resp : Type} (adm : List Sch.PK → Prop)
    (bind : List Sch.PK → RMsg → Sch.Msg) (pubOf : Sch.SignCoins → Sch.Pub) {Q : ℕ}
    (s : SideCoins Sch n Q) (c : ℕ) :
    Function.Injective ((zkRelay (Resp := Resp) (N := N) adm bind pubOf s).route c) :=
  fun _ _ h => congrArg (fun q => q.stmt.2) h

/-! ### The relation on the relayed proof queries -/

omit [Fintype RMsg] [DecidableEq RMsg] in
/-- **The relayed proof query is in the ring relation exactly for a member's ring-signing
request** numbered below `Q` whose drawn signature verifies, when the public value of an honest
signature is `pubOf` of its coins (`hpub`). -/
theorem mem_ringRel_iff_signerIn {pubOf : Sch.SignCoins → Sch.Pub} (hpub : Sch.PubOfCoins pubOf)
    (adm : List Sch.PK → Prop) (bind : List Sch.PK → RMsg → Sch.Msg) {Q : ℕ}
    (s : SideCoins Sch n Q) (c : ℕ) (r : BKMRequest Sch n N RMsg) :
    ((stmtAt (fun i => Sch.pk (s.1 i)) adm (fun j => pubOf (s.2 j)) c r,
      (witAt s.1 adm bind s.2 c r).toWit) ∈ ringRel adm bind) ↔
      c < Q ∧ signerIn (fun i => Sch.pk (s.1 i)) adm r ∧ drawVerifies Sch N RMsg s.1 bind s.2 c r := by
  by_cases hs : c < Q ∧ signerIn (fun i => Sch.pk (s.1 i)) adm r
  · cases r with
    | publicKey i => exact absurd hs.2 id
    | corrupt i => exact absurd hs.2 id
    | ringSign s' R m =>
      rw [stmtAt, witAt, dite_eq_left_of_eq_true (eq_true hs), dite_eq_left_of_eq_true (eq_true hs)]
      have hidx : R.1.idxOf (Sch.pk (s.1 s')) < R.1.length := hs.2.2
      constructor
      · intro h
        refine ⟨hs.1, hs.2, fun hc => ?_⟩
        have hv := h.2.verify_eq
        simp only [RelayWit.toWit, List.getElem_idxOf hidx] at hv
        exact hv
      · rintro ⟨-, -, hv⟩
        refine ⟨hs.2.1, ?_⟩
        have h := RingRel.of_signWith (bind := bind) (m := m) (kc := s.1 s') (R := R) hidx
          (List.getElem_idxOf hidx) (hv hs.1)
        rw [hpub] at h
        exact h
  · refine iff_of_false (fun h => ?_) (fun h => hs ⟨h.1, h.2.1⟩)
    have hl := h.2.idx_lt
    rw [stmtAt, dite_eq_right_of_eq_false (eq_false hs)] at hl
    exact absurd hl (Nat.not_lt_zero _)

omit [Fintype RMsg] [DecidableEq RMsg] in
/-- **The statement of a member's ring-signing request has a nonempty ring**; every other request
has the empty ring of `dummyStmt`. -/
theorem stmtAt_ring_eq_nil_iff (pkOf : Fin n → Sch.PK) (adm : List Sch.PK → Prop) {Q : ℕ}
    (pubs : Fin Q → Sch.Pub) (c : ℕ) (r : BKMRequest Sch n N RMsg) :
    (stmtAt pkOf adm pubs c r).ring.1 = [] ↔ ¬ (c < Q ∧ signerIn pkOf adm r) := by
  by_cases h : c < Q ∧ signerIn pkOf adm r
  · refine iff_of_false ?_ (not_not.2 h)
    cases r with
    | publicKey i => exact h.2.elim
    | corrupt i => exact h.2.elim
    | ringSign s R m =>
      rw [stmtAt, dite_eq_left_of_eq_true (eq_true h)]
      intro hR
      have h2 : R.1.idxOf (pkOf s) < R.1.length := h.2.2
      change R.1 = [] at hR
      simp only [hR, List.length_nil] at h2
      exact Nat.not_lt_zero _ h2
  · rw [stmtAt, dite_eq_right_of_eq_false (eq_false h)]
    exact iff_of_true rfl h

omit [Fintype RMsg] [DecidableEq RMsg] [Nonempty RMsg] in
/-- **The reply to a request that is not a member's ring-signing request** does not read the main
reply. -/
theorem sideAnswer_of_not_signerIn {Resp : Type} {pkOf : Fin n → Sch.PK}
    {kcOf : Fin n → Sch.KeyCoins} {adm : List Sch.PK → Prop} {Q : ℕ} {pubs : Fin Q → Sch.Pub}
    {c : ℕ} {r : BKMRequest Sch n N RMsg} (h : ¬ signerIn pkOf adm r) (a : Option Resp) :
    sideAnswer pkOf kcOf adm pubs c r a = sideAnswer pkOf kcOf adm pubs c r none := by
  unfold sideAnswer
  split_ifs
  · cases r <;> simp only [h, ite_false]
  · rfl

omit [Fintype RMsg] [DecidableEq RMsg] [Nonempty RMsg] in
/-- The reply to a request depends on the public values only at its own number. -/
theorem sideAnswer_pubs_congr {Resp : Type} {pkOf : Fin n → Sch.PK}
    {kcOf : Fin n → Sch.KeyCoins} {adm : List Sch.PK → Prop} {Q : ℕ} {pubs pubs' : Fin Q → Sch.Pub}
    {c : ℕ} (hc : ∀ h : c < Q, pubs ⟨c, h⟩ = pubs' ⟨c, h⟩) (r : BKMRequest Sch n N RMsg)
    (a : Option Resp) : sideAnswer pkOf kcOf adm pubs c r a = sideAnswer pkOf kcOf adm pubs' c r a := by
  unfold sideAnswer
  split_ifs with h
  · rw [hc h]
  · rfl

omit [Fintype RMsg] [DecidableEq RMsg] in
/-- The statement of a request depends on the public values only at its own number. -/
theorem stmtAt_pubs_congr {pkOf : Fin n → Sch.PK} {adm : List Sch.PK → Prop} {Q : ℕ}
    {pubs pubs' : Fin Q → Sch.Pub} {c : ℕ} (hc : ∀ h : c < Q, pubs ⟨c, h⟩ = pubs' ⟨c, h⟩)
    (r : BKMRequest Sch n N RMsg) : stmtAt pkOf adm pubs c r = stmtAt pkOf adm pubs' c r := by
  unfold stmtAt
  split_ifs with h
  · cases r <;> simp [hc h.1]
  · rfl

/-! ### The checked layer of BKM06 -/

variable {m k e : ℕ} {Resp SC : Type} [Fintype SC] [DecidableEq SC]

variable {Coins : Type} [Fintype Coins]
  (Pv : NARG.Prover (Bits m) (XOut k e) (RingStmt Sch RMsg N) (RingWit Sch) Resp Coins)
  (bind : List Sch.PK → RMsg → Sch.Msg) (adm : List Sch.PK → Prop)

omit [Fintype RMsg] [DecidableEq RMsg] [Nonempty RMsg] [Fintype Coins] in
/-- **The checked ring-signing step after the signer's public key `pk`**: as `ringSignAfterKey`,
replying `none` when the base signature fails to verify under `pk`. -/
noncomputable def checkedRingSignAfterKey (s : Fin n) (ring : RingOf Sch.PK N) (mg : RMsg)
    (c : Coins) (pk : Sch.PK) :
    OracleProg (BaseRequest Sch n) (BaseResponse Sch)
      (OracleProg (Bits m) (XOut k e) (Option (RingResponse Sch Resp))) :=
  if ring.1.idxOf pk < ring.1.length then
    .query (.sign s (bind ring.1 mg)) fun
      | .signature σ => if Sch.verify pk (bind ring.1 mg) σ = true then
          .pure ((Pv.prog ⟨ring, mg, Sch.pub σ⟩ ⟨ring.1.idxOf pk, σ⟩ c).bind fun π =>
            .pure (some (.ringSignature (Sch.pub σ) π)))
        else .pure (.pure none)
      | _ => .pure (.pure none)
  else .pure (.pure none)

open Classical in
/-- **The checked layer of BKM06** for the admissible rings `adm`: `bkmLayer`, with the signer
replying `none` when its base signature fails to verify (`checkedRingSignAfterKey`). A proof
device: it differs from `bkmLayer` only on a drawn signature that fails to verify. -/
noncomputable def checkedBkmLayer :
    OracleLayer Sch n (Bits m) (XOut k e) (BKMRequest Sch n N RMsg) (RingResponse Sch Resp) where
  Coins := Coins
  instDecEqCoins := Classical.decEq _
  coins := Pv.coins
  prog r c := if r.Admissible Sch n adm then
      match r with
      | .publicKey i => .query (.publicKey i) fun a => .pure (.pure (some (.base a)))
      | .corrupt i => .query (.corrupt i) fun a => .pure (.pure (some (.base a)))
      | .ringSign s ring mg => .query (.publicKey s) fun
          | .publicKey pk => checkedRingSignAfterKey Pv bind s ring mg c pk
          | _ => .pure (.pure none)
    else .pure (.pure none)
  q := Pv.q
  prog_queries r c O H := by
    split_ifs
    · rcases r with i | i | ⟨s, ring, mg⟩
      · simp
      · simp
      · simp only [OracleProg.run_query]
        rcases O (.publicKey s) with pk | σ | kc
        · simp only [checkedRingSignAfterKey]
          split_ifs
          · simp only [OracleProg.run_query]
            rcases O (.sign s (bind ring.1 mg)) with pk' | σ | kc
            · simp
            · simp only
              split_ifs
              · simp only [OracleProg.run_pure, OracleProg.trace_bind, OracleProg.trace_pure,
                  List.append_nil]
                exact Pv.prog_queries _ _ _ H
              · simp
            · simp
          · simp
        · simp
        · simp
    · simp
  prog_signs_le r c O := by
    split_ifs
    · rcases r with i | i | ⟨s, ring, mg⟩
      · simp [List.filter, BaseRequest.isSign]
      · simp [List.filter, BaseRequest.isSign]
      · simp only [OracleProg.trace_query]
        rcases O (.publicKey s) with pk | σ | kc
        · simp only [checkedRingSignAfterKey]
          split_ifs
          · simp only [OracleProg.trace_query]
            rcases O (.sign s (bind ring.1 mg)) with _ | σ | _
            · simp [List.filter, BaseRequest.isSign]
            · simp only
              split_ifs <;> simp [List.filter, BaseRequest.isSign]
            · simp [List.filter, BaseRequest.isSign]
          · simp [List.filter, BaseRequest.isSign]
        · simp [List.filter, BaseRequest.isSign]
        · simp [List.filter, BaseRequest.isSign]
    · simp

/-! ### The simulated challengers of BKM06 -/

omit [Nonempty RMsg] in
variable (Sch n) in
/-- **The coins of the simulated challengers**: the users' key-generation coins and, per request,
signing coins and simulator coins. -/
abbrev SimCoins (Q : ℕ) (SC : Type) : Type := (Fin n → Sch.KeyCoins) × (Fin Q → Sch.SignCoins × SC)

/-- **The law of the coins of the simulated challengers**: uniform key-generation coins, and per
request independent uniform signing coins and simulator coins. -/
noncomputable def simCoinsLaw (Q : ℕ) (μ : PMF SC) : PMF (SimCoins Sch n Q SC) :=
  (PMF.uniformOfFintype (Fin n → Sch.KeyCoins)).bind fun keys =>
    (PMF.pi fun _ : Fin Q => (PMF.uniformOfFintype Sch.SignCoins).bind fun c =>
      μ.map fun d => (c, d)).map fun r => (keys, r)

open Classical in
/-- **The reply of the simulated challengers** to request number `i` at the keys `κ` and the
draw `d` (signing coins and simulator coins), with the test `ok` of the drawn signature: a
ring-signing request by a member whose drawn signature passes `ok` runs `S` on its statement
`stmtAt` (with the public value `pubOf` of the signing coins), answers with the simulated proof as
a ring signature (`sideAnswer`) and appends the simulator's assignments; a member's request failing
`ok` gets `none`; any other request is answered by `sideAnswer` from the keys, without queries or
assignments. -/
noncomputable def simReply (S : NARG.Simulator (Bits m) (XOut k e) (RingStmt Sch RMsg N) Resp SC)
    (adm : List Sch.PK → Prop) (pubOf : Sch.SignCoins → Sch.Pub) (Q : ℕ)
    (ok : (Fin n → Sch.KeyCoins) → Sch.SignCoins → BKMRequest Sch n N RMsg → Prop)
    (κ : Fin n → Sch.KeyCoins) (d : Sch.SignCoins × SC) (i : ℕ) (r : BKMRequest Sch n N RMsg) :
    OracleProg (Bits m) (XOut k e) (Reply (Bits m) (XOut k e) (RingResponse Sch Resp)) :=
  if signerIn (fun i => Sch.pk (κ i)) adm r then
    if ok κ d.1 r then
      (S.prog (stmtAt (fun i => Sch.pk (κ i)) adm (fun _ : Fin Q => pubOf d.1) i r) d.2).bind fun o =>
        .pure ⟨sideAnswer (fun i => Sch.pk (κ i)) κ adm (fun _ : Fin Q => pubOf d.1) i r
          (some o.proof), o.assignments⟩
    else .pure ⟨none, []⟩
  else .pure ⟨sideAnswer (fun i => Sch.pk (κ i)) κ adm (fun _ : Fin Q => pubOf d.1) i r none, []⟩

/-- **The simulated challengers as split challengers** (`Quantum.SplitChallenger`): uniform keys,
per request uniform signing coins and simulator coins, the replies `simReply` with the test `ok`. -/
noncomputable def simSplit (S : NARG.Simulator (Bits m) (XOut k e) (RingStmt Sch RMsg N) Resp SC)
    (adm : List Sch.PK → Prop) (pubOf : Sch.SignCoins → Sch.Pub) (Q : ℕ)
    (ok : (Fin n → Sch.KeyCoins) → Sch.SignCoins → BKMRequest Sch n N RMsg → Prop) :
    SplitChallenger (Bits m) (XOut k e) (BKMRequest Sch n N RMsg) (RingResponse Sch Resp)
      (Fin n → Sch.KeyCoins) (Sch.SignCoins × SC) where
  keys := PMF.uniformOfFintype _
  draw := (PMF.uniformOfFintype Sch.SignCoins).bind fun c => S.coins.map fun d => (c, d)
  Q := Q
  q := S.q
  reply := simReply S adm pubOf Q ok
  reply_queries κ d i r H := by
    unfold simReply
    split_ifs
    · rw [OracleProg.trace_bind, OracleProg.trace_pure, List.append_nil]
      exact S.prog_queries _ _ H
    · simp
    · simp

/-- **The challenger of BKM06 Definition 7 with simulated ring signatures** answering `Q`
requests, for a simulator `S` of the ring statements and the public values `pubOf` of the drawn
signing coins: uniform keys and, per request, signing coins and simulator coins; a ring-signing
request by a member runs `S` on its statement with the public value of its signing coins. It reads
no secret key (`simSplit` with the trivial test). -/
noncomputable abbrev simBKMChallenger
    (S : NARG.Simulator (Bits m) (XOut k e) (RingStmt Sch RMsg N) Resp SC)
    (adm : List Sch.PK → Prop) (pubOf : Sch.SignCoins → Sch.Pub) (Q : ℕ) :
    Challenger (Bits m) (XOut k e) (BKMRequest Sch n N RMsg) (RingResponse Sch Resp) :=
  (simSplit S adm pubOf Q fun _ _ _ => True).toChallenger

/-- **The checked challenger of BKM06 with simulated ring signatures**: `simBKMChallenger`,
answering `none` to a ring-signing request by a member whose drawn signature fails to verify
(`simSplit` with the test `drawOk`). A proof device: it reads the secret keys. -/
noncomputable abbrev simBKMCheckedChallenger
    (S : NARG.Simulator (Bits m) (XOut k e) (RingStmt Sch RMsg N) Resp SC)
    (adm : List Sch.PK → Prop) (bind : List Sch.PK → RMsg → Sch.Msg)
    (pubOf : Sch.SignCoins → Sch.Pub) (Q : ℕ) :
    Challenger (Bits m) (XOut k e) (BKMRequest Sch n N RMsg) (RingResponse Sch Resp) :=
  (simSplit S adm pubOf Q (drawOk Sch N RMsg bind)).toChallenger

/-- **The simulator inert on the empty ring**: on a statement with the empty ring it returns `p₀`
without queries or assignments; on every other statement it runs `S`.

Running time: that of `S`, plus a test of the ring. This running time is argued here, not proved
in Lean. -/
def inertOnEmpty (S : NARG.Simulator (Bits m) (XOut k e) (RingStmt Sch RMsg N)
    Resp SC) (p₀ : Resp) : NARG.Simulator (Bits m) (XOut k e) (RingStmt Sch RMsg N) Resp SC where
  prog x c := if x.ring.1 = [] then .pure ⟨p₀, []⟩ else S.prog x c
  coins_nonempty := S.coins_nonempty
  q := S.q
  prog_queries x c H := by
    split_ifs
    · simp
    · exact S.prog_queries x c H

/-! ### The coins -/

/-- **Keys and per-request pairs as side coins and per-request second components.** -/
def splitEquiv (Q : ℕ) (C : Type) :
    (Fin n → Sch.KeyCoins) × (Fin Q → Sch.SignCoins × C) ≃ SideCoins Sch n Q × (Fin Q → C) where
  toFun ω := ((ω.1, fun c => (ω.2 c).1), fun c => (ω.2 c).2)
  invFun p := (p.1.1, fun c => (p.1.2 c, p.2 c))
  left_inv _ := rfl
  right_inv _ := rfl

/-- **The coins of the challenger of BKM06 as side coins and prover coins.** -/
abbrev drawEquiv {X Y Req Resp : Type} (L : OracleLayer Sch n X Y Req Resp) (Q : ℕ) :
    L.Draw Q ≃ SideCoins Sch n Q × (Fin Q → L.Coins) :=
  splitEquiv Q L.Coins

/-- **The joint law of `a ← μ` and `b ← ν a`** at `(a, b)`: `μ a · ν a b`. -/
theorem bind_map_pair_apply {α β : Type} (μ : PMF α) (ν : α → PMF β) (a : α) (b : β) :
    (μ.bind fun a => (ν a).map fun b => (a, b)) (a, b) = μ a * ν a b := by
  classical
  rw [PMF.bind_apply, tsum_eq_single a fun a' ha' => ?_]
  · rw [PMF.map_apply, tsum_eq_single b fun b' hb' => by simp [Ne.symm hb']]
    simp
  · rw [PMF.map_apply, ENNReal.tsum_eq_zero.2 fun b' => by simp [Ne.symm ha'], mul_zero]

/-- **The uniform side coins are uniform key-generation coins and independent uniform draws per
request.** -/
theorem uniformOfFintype_sideCoins_apply (Q : ℕ) (s : SideCoins Sch n Q) :
    PMF.uniformOfFintype (SideCoins Sch n Q) s =
      PMF.uniformOfFintype (Fin n → Sch.KeyCoins) s.1 *
        ∏ i, PMF.uniformOfFintype Sch.SignCoins (s.2 i) := by
  simp only [PMF.uniformOfFintype_apply, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    Fintype.card_prod (Fin n → Sch.KeyCoins), Fintype.card_pi, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, Nat.cast_mul, Nat.cast_pow, ← ENNReal.inv_pow]
  exact ENNReal.mul_inv (Or.inr (ENNReal.pow_ne_top (ENNReal.natCast_ne_top _)))
    (Or.inl (ENNReal.pow_ne_top (ENNReal.natCast_ne_top _)))

omit [DecidableEq SC] in
/-- **Keys and per-request pairs drawn as `simCoinsLaw` are uniform side coins and independent
second components.** -/
theorem simCoinsLaw_splitEquiv_symm (Q : ℕ) (μ : PMF SC) (s : SideCoins Sch n Q) (c : Fin Q → SC) :
    simCoinsLaw Q μ ((splitEquiv Q SC).symm (s, c)) =
      PMF.uniformOfFintype (SideCoins Sch n Q) s * (PMF.pi fun _ => μ) c := by
  simp only [simCoinsLaw, splitEquiv, Equiv.coe_fn_symm_mk]
  rw [bind_map_pair_apply, PMF.pi_apply, PMF.pi_apply, uniformOfFintype_sideCoins_apply,
    mul_assoc, ← Finset.prod_mul_distrib]
  congr 2
  funext i
  exact bind_map_pair_apply _ _ _ _

omit [Fintype RMsg] [DecidableEq RMsg] [Nonempty RMsg] in
/-- The draw of side coins `s` and layer coins `c`. -/
theorem drawEquiv_symm_apply {X Y Req Resp : Type} (L : OracleLayer Sch n X Y Req Resp) (Q : ℕ)
    (s : SideCoins Sch n Q) (c : Fin Q → L.Coins) :
    (drawEquiv L Q).symm (s, c) = (s.1, fun i => (s.2 i, c i)) :=
  rfl

/-- **The draws of the challenger of BKM06 are uniform side coins and independent layer coins.** -/
theorem drawLaw_drawEquiv_symm {X Y Req Resp : Type} (L : OracleLayer Sch n X Y Req Resp) (Q : ℕ)
    (s : SideCoins Sch n Q) (c : Fin Q → L.Coins) :
    L.drawLaw Q ((drawEquiv L Q).symm (s, c)) =
      PMF.uniformOfFintype (SideCoins Sch n Q) s * (PMF.pi fun _ => L.coins) c :=
  simCoinsLaw_splitEquiv_symm Q L.coins s c

/-! ### The relays -/

omit [Fintype RMsg] [DecidableEq RMsg] in
open Classical in
/-- **The checked challenger of BKM06 relays the real challenger** of the honest prover `Pv` on
the relayed proof queries (`zkRelay`), at the side coins of its draws, when the public value of an
honest signature is `pubOf` of its coins (`hpub`). -/
theorem relays_bkm_real {pubOf : Sch.SignCoins → Sch.Pub} (hpub : Sch.PubOfCoins pubOf) (Q : ℕ)
    (s : SideCoins Sch n Q) (c : Fin Q → Coins) :
    (zkRelay (N := N) (Resp := Resp) adm bind pubOf s).RelaysChallenger
      ((checkedBkmLayer Pv bind adm).challenger Q)
      ((drawEquiv (checkedBkmLayer Pv bind adm) Q).symm (s, c))
      (realChallenger (fun x w => (x.1, RelayWit.toWit w) ∈ ringRel adm bind)
        (Pv.comap Prod.fst RelayWit.toWit) Q) c := by
  refine ⟨rfl, ?_, ?_⟩
  · intro hist hist' r G hrel hQ
    have hlen : hist.length = hist'.length := by
      simpa using (congrArg List.length hrel).symm
    change hist.length < Q at hQ
    have hQ' : hist'.length < Q := hlen ▸ hQ
    have hi : (⟨hist'.length, hQ'⟩ : Fin Q) = ⟨hist.length, hQ⟩ := Fin.ext hlen.symm
    simp only [OracleLayer.challenger, realChallenger, zkRelay, hQ, hQ', dite_true, hi,
      NARG.Prover.comap, OracleLayer.oracleAt]
    simp only [drawEquiv, splitEquiv, Equiv.coe_fn_symm_mk]
    simp only [checkedBkmLayer]
    cases r with
    | publicKey j =>
      simp [mem_ringRel_iff_signerIn hpub, BKMRequest.Admissible, signerIn, sideAnswer, hQ,
        OracleProg.run_bind, OracleProg.run_query, baseAnswer]
    | corrupt j =>
      simp [mem_ringRel_iff_signerIn hpub, BKMRequest.Admissible, signerIn, sideAnswer, hQ,
        OracleProg.run_bind, OracleProg.run_query, baseAnswer]
    | ringSign s' R m =>
      simp only [BKMRequest.Admissible, sideAnswer, hQ, dite_true, OracleProg.run_bind]
      by_cases ha : adm R.1
      · by_cases hm : R.1.idxOf (Sch.pk (s.1 s')) < R.1.length
        · have h : hist.length < Q ∧ signerIn (fun i => Sch.pk (s.1 i)) adm (.ringSign s' R m) :=
            ⟨hQ, ha, hm⟩
          simp only [ha, hm, ite_true, checkedRingSignAfterKey, OracleProg.run_query, baseAnswer,
            show signerIn (fun i => Sch.pk (s.1 i)) adm (BKMRequest.ringSign s' R m (N := N)) from
              h.2]
          by_cases hv : Sch.verify (Sch.pk (s.1 s')) (bind R.1 m)
              (Sch.signWith (Sch.sk (s.1 s')) (bind R.1 m) (s.2 ⟨hist.length, hQ⟩)) = true
          · have hrel := (mem_ringRel_iff_signerIn hpub adm bind s hist.length
              (.ringSign s' R m)).2 ⟨hQ, h.2, fun _ => hv⟩
            simp only [hv, ite_true, OracleProg.run_bind, OracleProg.run_pure, hrel]
            rw [stmtAt, witAt, dite_eq_left_of_eq_true (eq_true h),
              dite_eq_left_of_eq_true (eq_true h), hpub]
            rfl
          · have hrel : ¬ _ := fun hr => hv (((mem_ringRel_iff_signerIn hpub adm bind s hist.length
              (.ringSign s' R m)).1 hr).2.2 hQ)
            simp only [hv, Bool.false_eq_true, ite_false, OracleProg.run_pure, hrel]
            rfl
        · have hrel : ¬ _ := fun hr => hm ((mem_ringRel_iff_signerIn hpub adm bind s hist.length
            (.ringSign s' R m)).1 hr).2.1.2
          simp only [ha, hm, ite_true, ite_false, checkedRingSignAfterKey, OracleProg.run_query,
            OracleProg.run_pure, baseAnswer, hrel, signerIn, and_false]
      · have hrel : ¬ _ := fun hr => ha ((mem_ringRel_iff_signerIn hpub adm bind s hist.length
          (.ringSign s' R m)).1 hr).2.1.1
        simp only [ha, ite_false, OracleProg.run_pure, hrel, signerIn, false_and]
  · intro i r h
    change Q ≤ i at h
    simp only [zkRelay, sideAnswer, show ¬ i < Q from not_lt.2 h, dite_false]

omit [Fintype RMsg] [DecidableEq RMsg] in
open Classical in
/-- **The checked simulated challenger of BKM06 relays the simulated zero-knowledge challenger** of
the simulator `S` on the relayed proof queries (`zkRelay`), when the public value of an honest
signature is `pubOf` of its coins (`hpub`). -/
theorem relays_sim_zk {pubOf : Sch.SignCoins → Sch.Pub} (hpub : Sch.PubOfCoins pubOf)
    (S : NARG.Simulator (Bits m) (XOut k e) (RingStmt Sch RMsg N) Resp SC) (Q : ℕ)
    (s : SideCoins Sch n Q) (c : Fin Q → SC) :
    (zkRelay (N := N) (Resp := Resp) adm bind pubOf s).RelaysChallenger
      (simBKMCheckedChallenger S adm bind pubOf Q) ((splitEquiv Q SC).symm (s, c))
      (simChallenger (fun x w => (x.1, RelayWit.toWit w) ∈ ringRel adm bind)
        (S.comap Prod.fst) Q) c := by
  refine ⟨rfl, ?_, ?_⟩
  · intro hist hist' r G hrel hQ
    have hlen : hist.length = hist'.length := by
      simpa using (congrArg List.length hrel).symm
    change hist.length < Q at hQ
    have hQ' : hist'.length < Q := hlen ▸ hQ
    have hi : (⟨hist'.length, hQ'⟩ : Fin Q) = ⟨hist.length, hQ⟩ := Fin.ext hlen.symm
    simp only [simBKMCheckedChallenger, SplitChallenger.toChallenger, simSplit, simReply,
      simChallenger, zkRelay, hQ, hQ', dite_true, hi, NARG.Simulator.comap, splitEquiv,
      Equiv.coe_fn_symm_mk]
    have hst : stmtAt (fun i => Sch.pk (s.1 i)) adm (fun _ : Fin Q => pubOf (s.2 ⟨hist.length, hQ⟩))
        hist.length r = stmtAt (fun i => Sch.pk (s.1 i)) adm (fun j => pubOf (s.2 j)) hist.length r :=
      stmtAt_pubs_congr (fun _ => rfl) r
    have hsa : ∀ a : Option Resp, sideAnswer (fun i => Sch.pk (s.1 i)) s.1 adm
        (fun _ : Fin Q => pubOf (s.2 ⟨hist.length, hQ⟩)) hist.length r a =
        sideAnswer (fun i => Sch.pk (s.1 i)) s.1 adm (fun j => pubOf (s.2 j)) hist.length r a :=
      fun a => sideAnswer_pubs_congr (fun _ => rfl) r a
    simp only [hst, hsa]
    by_cases hs : signerIn (fun i => Sch.pk (s.1 i)) adm r
    · by_cases hv : drawVerifies Sch N RMsg s.1 bind s.2 hist.length r
      · have hrel := (mem_ringRel_iff_signerIn hpub adm bind s hist.length r).2 ⟨hQ, hs, hv⟩
        have hok : drawOk Sch N RMsg bind s.1 (s.2 ⟨hist.length, hQ⟩) r := hv hQ
        simp only [hs, hok, hrel, ite_true, OracleProg.run_bind, OracleProg.run_pure]
      · have hrel : ¬ _ := fun h => hv ((mem_ringRel_iff_signerIn hpub adm bind s hist.length r).1 h).2.2
        have hok : ¬ drawOk Sch N RMsg bind s.1 (s.2 ⟨hist.length, hQ⟩) r := fun h => hv fun _ => h
        simp only [hs, hok, hrel, ite_true, ite_false, OracleProg.run_pure]
        unfold sideAnswer
        cases r <;> simp_all [signerIn]
    · simp only [hs, mem_ringRel_iff_signerIn hpub, hQ, true_and, false_and, ite_false,
        OracleProg.run_pure, sideAnswer_of_not_signerIn hs]
  · intro i r h
    change Q ≤ i at h
    simp only [zkRelay, sideAnswer, show ¬ i < Q from not_lt.2 h, dite_false]

omit [Fintype RMsg] [DecidableEq RMsg] in
/-- **The simulated challenger of BKM06 relays the simulation-extraction challenger** of the
simulator inert on the empty ring (`inertOnEmpty`) on the relayed statements (`seRelay`). -/
theorem relays_sim_se (S : NARG.Simulator (Bits m) (XOut k e) (RingStmt Sch RMsg N) Resp SC)
    (pubOf : Sch.SignCoins → Sch.Pub) (p₀ : Resp) (Q : ℕ) (s : SideCoins Sch n Q)
    (c : Fin Q → SC) :
    (seRelay (N := N) (Resp := Resp) (fun i => Sch.pk (s.1 i)) s.1 adm
        (fun j => pubOf (s.2 j))).RelaysChallenger
      (simBKMChallenger S adm pubOf Q) ((splitEquiv Q SC).symm (s, c))
      (simExtChallenger ((inertOnEmpty S p₀).comap Prod.fst) Q) c := by
  refine ⟨rfl, ?_, ?_⟩
  · intro hist hist' r G hrel hQ
    have hlen : hist.length = hist'.length := by
      simpa using (congrArg List.length hrel).symm
    change hist.length < Q at hQ
    have hQ' : hist'.length < Q := hlen ▸ hQ
    have hi : (⟨hist'.length, hQ'⟩ : Fin Q) = ⟨hist.length, hQ⟩ := Fin.ext hlen.symm
    simp only [simBKMChallenger, SplitChallenger.toChallenger, simSplit, simReply,
      simExtChallenger, simExtRespond, seRelay, hQ, hQ', dite_true, hi, inertOnEmpty,
      NARG.Simulator.comap, splitEquiv, Equiv.coe_fn_symm_mk, ite_true]
    have hst : stmtAt (fun i => Sch.pk (s.1 i)) adm (fun _ : Fin Q => pubOf (s.2 ⟨hist.length, hQ⟩))
        hist.length r = stmtAt (fun i => Sch.pk (s.1 i)) adm (fun j => pubOf (s.2 j)) hist.length r :=
      stmtAt_pubs_congr (fun _ => rfl) r
    have hsa : ∀ a : Option Resp, sideAnswer (fun i => Sch.pk (s.1 i)) s.1 adm
        (fun _ : Fin Q => pubOf (s.2 ⟨hist.length, hQ⟩)) hist.length r a =
        sideAnswer (fun i => Sch.pk (s.1 i)) s.1 adm (fun j => pubOf (s.2 j)) hist.length r a :=
      fun a => sideAnswer_pubs_congr (fun _ => rfl) r a
    simp only [hst, hsa]
    by_cases hs : signerIn (fun i => Sch.pk (s.1 i)) adm r
    · have hne : ¬ (stmtAt (fun i => Sch.pk (s.1 i)) adm (fun j => pubOf (s.2 j)) hist.length r).ring.1
          = [] := by
        rw [stmtAt_ring_eq_nil_iff]
        exact not_not.2 ⟨hQ, hs⟩
      simp only [hs, hne, ite_true, ite_false, OracleProg.run_bind, OracleProg.run_pure]
    · have he : (stmtAt (fun i => Sch.pk (s.1 i)) adm (fun j => pubOf (s.2 j)) hist.length r).ring.1
          = [] := by
        rw [stmtAt_ring_eq_nil_iff]
        exact fun h => hs h.2
      simp only [hs, he, ite_true, ite_false, OracleProg.run_bind, OracleProg.run_pure,
        sideAnswer_of_not_signerIn hs]
  · intro i r h
    change Q ≤ i at h
    simp only [seRelay, sideAnswer, show ¬ i < Q from not_lt.2 h, dite_false]

/-! ### The hybrids of the correctness error -/

section Hybrids

/-- **An event of the first coordinate of a pair drawn uniformly then independently** has the
first coordinate's probability. -/
theorem toOuterMeasure_bind_map_fst {α β : Type} [Fintype α] [Nonempty α] (ν : PMF β)
    (p : α → Prop) :
    ((PMF.uniformOfFintype α).bind fun a => ν.map fun b => (a, b)).toOuterMeasure {d | p d.1} =
      (PMF.uniformOfFintype α).toOuterMeasure {a | p a} := by
  classical
  rw [PMF.toOuterMeasure_bind_apply, PMF.toOuterMeasure_apply]
  refine tsum_congr fun a => ?_
  rw [PMF.toOuterMeasure_map_apply]
  by_cases ha : p a
  · have : (fun b => (a, b)) ⁻¹' {d : α × β | p d.1} = Set.univ := by ext; simp [ha]
    have h1 : ν.toOuterMeasure Set.univ = 1 := by
      rw [PMF.toOuterMeasure_apply, Set.indicator_univ, PMF.tsum_coe]
    rw [this, h1, mul_one, Set.indicator_of_mem (show a ∈ {a | p a} from ha)]
  · have : (fun b => (a, b)) ⁻¹' {d : α × β | p d.1} = ∅ := by ext; simp [ha]
    rw [this, MeasureTheory.measure_empty, mul_zero,
      Set.indicator_of_notMem (show a ∉ {a | p a} from ha)]

omit [Fintype RMsg] [DecidableEq RMsg] [Nonempty RMsg] in
/-- **A signature that fails `drawOk` has at most the correctness error**, over uniform signing
coins, at every request. -/
theorem toOuterMeasure_not_drawOk_le {ε : ℝ≥0∞} (hcorr : Sch.CorrectWithin ε)
    (bind : List Sch.PK → RMsg → Sch.Msg) (κ : Fin n → Sch.KeyCoins) (r : BKMRequest Sch n N RMsg) :
    (PMF.uniformOfFintype Sch.SignCoins).toOuterMeasure {c | ¬ drawOk Sch N RMsg bind κ c r} ≤ ε := by
  rcases r with i | i | ⟨s, R, m⟩
  · simp [drawOk]
  · simp [drawOk]
  · exact hcorr (κ s) (bind R.1 m)

variable {m k e : ℕ} {Resp : Type} {Coins : Type} [Fintype Coins]
  (Pv : NARG.Prover (Bits m) (XOut k e) (RingStmt Sch RMsg N) (RingWit Sch) Resp Coins)
  (bind : List Sch.PK → RMsg → Sch.Msg) (adm : List Sch.PK → Prop)

omit [Fintype RMsg] [DecidableEq RMsg] [Nonempty RMsg] in
/-- **The checked layer of BKM06 is the layer of BKM06 with other replies**, as split
challengers. -/
theorem split_checkedBkmLayer (Q : ℕ) :
    (checkedBkmLayer (n := n) Pv bind adm).split Q = ((bkmLayer (n := n) Pv bind adm).split Q).withReply
      ((checkedBkmLayer (n := n) Pv bind adm).split Q).reply ((checkedBkmLayer (n := n) Pv bind adm).split Q).reply_queries :=
  rfl

omit [Fintype RMsg] [DecidableEq RMsg] [Nonempty RMsg] in
open Classical in
/-- **The two layers of BKM06 reply alike** when the signature drawn for the request verifies. -/
theorem reply_bkmLayer_eq_checked (Q : ℕ) (κ : Fin n → Sch.KeyCoins) (d : Sch.SignCoins × Coins)
    (i : ℕ) (r : BKMRequest Sch n N RMsg) (h : drawOk Sch N RMsg bind κ d.1 r) :
    ((bkmLayer (n := n) Pv bind adm).split Q).reply κ d i r = ((checkedBkmLayer (n := n) Pv bind adm).split Q).reply κ d i r := by
  simp only [OracleLayer.split, bkmLayer, checkedBkmLayer]
  split_ifs with ha
  · rcases r with j | j | ⟨s, R, m⟩
    · rfl
    · rfl
    · simp only [BKMRequest.toRingRequest, ringLayer, OracleProg.run_query, baseAnswer,
        ringSignAfterKey, checkedRingSignAfterKey]
      split_ifs
      · rw [OracleProg.run_query, OracleProg.run_query,
          show baseAnswer κ d.1 (BaseRequest.sign s (bind R.1 m)) =
          .signature (Sch.signWith (Sch.sk (κ s)) (bind R.1 m) d.1) from rfl]
        have h' : Sch.verify (Sch.pk (κ s)) (bind R.1 m)
            (Sch.signWith (Sch.sk (κ s)) (bind R.1 m) d.1) = true := h
        simp only [h', ite_true]
      · rfl
  · rfl

omit [Fintype RMsg] [DecidableEq RMsg] [Nonempty RMsg] in
/-- **The two layers of BKM06 disagree with at most the correctness error** at every request. -/
theorem draw_bkmLayer_ne_checked_le {ε : ℝ≥0∞} (hcorr : Sch.CorrectWithin ε) (Q : ℕ)
    (κ : Fin n → Sch.KeyCoins) (i : ℕ) (r : BKMRequest Sch n N RMsg) :
    ((bkmLayer (n := n) Pv bind adm).split Q).draw.toOuterMeasure
      {d | ((bkmLayer (n := n) Pv bind adm).split Q).reply κ d i r ≠
        ((checkedBkmLayer (n := n) Pv bind adm).split Q).reply κ d i r} ≤ ε := by
  refine le_trans (MeasureTheory.measure_mono fun d hd =>
    show ¬ drawOk Sch N RMsg bind κ d.1 r from fun h => hd (reply_bkmLayer_eq_checked Pv bind adm Q κ d i r h)) ?_
  change ((PMF.uniformOfFintype Sch.SignCoins).bind fun s => Pv.coins.map fun c => (s, c)).toOuterMeasure
    {d | ¬ drawOk Sch N RMsg bind κ d.1 r} ≤ ε
  rw [toOuterMeasure_bind_map_fst (p := fun c => ¬ drawOk Sch N RMsg bind κ c r)]
  exact toOuterMeasure_not_drawOk_le hcorr bind κ r

variable {SC : Type} [Fintype SC] [DecidableEq SC]

omit [Fintype RMsg] [DecidableEq RMsg] in
/-- **The simulated challenger is the checked simulated challenger with other replies**, as split
challengers. -/
theorem simSplit_withReply (S : NARG.Simulator (Bits m) (XOut k e) (RingStmt Sch RMsg N) Resp SC)
    (pubOf : Sch.SignCoins → Sch.Pub) (Q : ℕ) :
    simSplit (n := n) S adm pubOf Q (fun _ _ _ => True) = (simSplit (n := n) S adm pubOf Q (drawOk Sch N RMsg bind)).withReply
      (simSplit (n := n) S adm pubOf Q (fun _ _ _ => True)).reply
      (simSplit (n := n) S adm pubOf Q (fun _ _ _ => True)).reply_queries :=
  rfl

omit [Fintype RMsg] [DecidableEq RMsg] in
/-- **The checked and the unchecked simulated challengers disagree with at most the correctness
error** at every request. -/
theorem draw_simSplit_ne_le {ε : ℝ≥0∞} (hcorr : Sch.CorrectWithin ε)
    (S : NARG.Simulator (Bits m) (XOut k e) (RingStmt Sch RMsg N) Resp SC)
    (pubOf : Sch.SignCoins → Sch.Pub) (Q : ℕ) (κ : Fin n → Sch.KeyCoins) (i : ℕ)
    (r : BKMRequest Sch n N RMsg) :
    (simSplit (n := n) S adm pubOf Q (drawOk Sch N RMsg bind)).draw.toOuterMeasure
      {d | (simSplit (n := n) S adm pubOf Q (drawOk Sch N RMsg bind)).reply κ d i r ≠
        (simSplit (n := n) S adm pubOf Q fun _ _ _ => True).reply κ d i r} ≤ ε := by
  classical
  refine le_trans (MeasureTheory.measure_mono fun d hd =>
    show ¬ drawOk Sch N RMsg bind κ d.1 r from fun h => hd ?_) ?_
  · simp only [simSplit, simReply, h, ite_true]
  · change ((PMF.uniformOfFintype Sch.SignCoins).bind fun c => S.coins.map fun d => (c, d)).toOuterMeasure
      {d | ¬ drawOk Sch N RMsg bind κ d.1 r} ≤ ε
    rw [toOuterMeasure_bind_map_fst (p := fun c => ¬ drawOk Sch N RMsg bind κ c r)]
    exact toOuterMeasure_not_drawOk_le hcorr bind κ r

end Hybrids

end GordieHowe.Ring
