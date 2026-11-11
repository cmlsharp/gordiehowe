-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Ring.StrongForger

@[expose] public section

/-!
# Relays of BKM06 Definition 7 publishing the public values of real signatures

The relays and challengers of `InsiderRelays.lean` with the public value of each ring signature
read off a real base signature by the signer, instead of drawn from the signing coins alone: no
`SigScheme.PubOfCoins` is needed, so the public value may depend on the signer's key (ML-DSA's
`w₁`).

- `sigOf keys bind rd t r`: the base signature of a ring-signing request `r = (s, R, m)` at the
  per-request coins `t`, the signing coins of user `s` on `bind R m` read from `t` by the reader
  `rd` (`rdCoins`: the coins themselves; `rdTable`: the entry of a signing table). `sigPubs`: the
  public values of these signatures.
- `seRelayPub`: `seRelay` with the public values depending on the request; `zkRelaySig`: the relay
  of proof queries with the statement's public value that of the witness's signature.
- `mem_ringRel_iff_signerIn_sig`: the relayed proof query is in the ring relation exactly for a
  member's ring-signing request whose drawn signature verifies (no hypothesis on the public value).
- `simSplitSig S adm bind rd Q ok`: the challenger of BKM06 with ring signatures simulated by `S` on
  the statements with the public value of the signer's real signature at the request's coins (read
  by `rd`); it reads the secret keys (a proof device).
- `relays_bkm_real_sig`, `relays_sim_zk_sig`, `relays_sim_se_sig`: the checked layer of BKM06
  relays the real challenger, the checked simulated challenger relays the zero-knowledge simulation
  challenger, and the simulated challenger at any reader relays the simulation-extraction
  challenger.
- `draw_simSplitSig_ne_le`: the checked and the unchecked simulated challengers disagree on a
  request with at most the correctness error.
-/

namespace GordieHowe.Ring

open Quantum GordieHowe.QROM GordieHowe.SPBCS
open scoped ENNReal

variable {Sch : SigScheme} {n N : ℕ} {RMsg : Type} [Fintype RMsg] [DecidableEq RMsg]

/-! ### Coin readers and the signatures of requests -/

variable [Fintype Sch.PK] [DecidableEq Sch.PK] [Fintype Sch.Msg] [DecidableEq Sch.Msg]
  [Fintype Sch.Sig] [DecidableEq Sch.Sig] [Fintype Sch.Pub] [DecidableEq Sch.Pub] [Nonempty Sch.Pub]
  [Fintype Sch.KeyCoins] [DecidableEq Sch.KeyCoins] [Nonempty Sch.KeyCoins] [Fintype Sch.SignCoins]
  [DecidableEq Sch.SignCoins] [Nonempty Sch.SignCoins]

variable (Sch n) in
/-- **The reader of per-request signing coins**: every signing call of the request uses them. -/
def rdCoins : Sch.SignCoins → Fin n → Sch.Msg → Sch.SignCoins := fun c _ _ => c

variable (Sch n) in
/-- **The reader of a signing table**: the signing call of user `i` on `m` uses the entry
`(i, m)`. -/
def rdTable : SignTable Sch n → Fin n → Sch.Msg → Sch.SignCoins := fun t i m => t (i, m)

variable [Nonempty RMsg]

/-- **The base signature of a request at the per-request coins `t`**: for a ring-signing request
`(s, R, m)`, user `s`'s signature on `bind R m` with the signing coins read from `t` by `rd`;
`dummySig` for the other requests. -/
noncomputable def sigOf (keys : Fin n → Sch.KeyCoins) (bind : List Sch.PK → RMsg → Sch.Msg)
    {C : Type} (rd : C → Fin n → Sch.Msg → Sch.SignCoins) (t : C) :
    BKMRequest Sch n N RMsg → Sch.Sig
  | .ringSign s R m => Sch.signWith (Sch.sk (keys s)) (bind R.1 m) (rd t s (bind R.1 m))
  | _ => dummySig bind

/-- **The public values of a request at the draws `draws`**: at number `j`, the public value of
the request's base signature at the draw `draws j` (`sigOf`). -/
noncomputable def sigPubs (keys : Fin n → Sch.KeyCoins) (bind : List Sch.PK → RMsg → Sch.Msg)
    {C : Type} (rd : C → Fin n → Sch.Msg → Sch.SignCoins) {Q : ℕ} (draws : Fin Q → C)
    (r : BKMRequest Sch n N RMsg) : Fin Q → Sch.Pub :=
  fun j => Sch.pub (sigOf keys bind rd (draws j) r)

omit [Fintype RMsg] [DecidableEq RMsg] in
variable (Sch N RMsg) in
/-- **The signature at the coins `t` verifies**: for a ring-signing request `(s, R, m)`, the
signature `sigOf` verifies on `bind R m` under `s`'s public key; every other request qualifies.
At the reader `rdCoins` it is `drawOk`. -/
def drawOkSig (bind : List Sch.PK → RMsg → Sch.Msg) {C : Type}
    (rd : C → Fin n → Sch.Msg → Sch.SignCoins) (keys : Fin n → Sch.KeyCoins) (t : C) :
    BKMRequest Sch n N RMsg → Prop
  | .ringSign s R m => Sch.verify (Sch.pk (keys s)) (bind R.1 m)
      (sigOf keys bind rd t (.ringSign s R m : BKMRequest Sch n N RMsg)) = true
  | _ => True

/-! ### The relays -/

omit [Nonempty Sch.KeyCoins] [Nonempty Sch.SignCoins] in
/-- **The relay of statements with request-dependent public values** (to the simulator of the
simulation-extraction game): request number `c` with request `r` is sent as its statement `stmtAt`
at the public values `pubsOf r` with the request, and answered by `sideAnswer` at the same public
values. `seRelay` is the case of public values independent of the request.

Running time: that of `seRelay`. This running time is argued here, not proved in Lean. -/
noncomputable def seRelayPub {Resp : Type} (pkOf : Fin n → Sch.PK) (kcOf : Fin n → Sch.KeyCoins)
    (adm : List Sch.PK → Prop) {Q : ℕ} (pubsOf : BKMRequest Sch n N RMsg → Fin Q → Sch.Pub) :
    SideRelay (BKMRequest Sch n N RMsg) (RingResponse Sch Resp) (RelayStmt Sch n N RMsg) Resp where
  route c r := (stmtAt pkOf adm (pubsOf r) c r, r)
  answer c r := sideAnswer pkOf kcOf adm (pubsOf r) c r

omit [Fintype RMsg] [DecidableEq RMsg] [Nonempty Sch.KeyCoins] [Nonempty Sch.SignCoins]
  [Fintype Sch.PK] [Fintype Sch.Msg] [DecidableEq Sch.Msg] [Fintype Sch.Sig] [DecidableEq Sch.Sig]
  [Fintype Sch.Pub] [DecidableEq Sch.Pub] [Fintype Sch.KeyCoins] [DecidableEq Sch.KeyCoins]
  [Fintype Sch.SignCoins] [DecidableEq Sch.SignCoins] in
theorem seRelayPub_route_injective {Resp : Type} (pkOf : Fin n → Sch.PK)
    (kcOf : Fin n → Sch.KeyCoins) (adm : List Sch.PK → Prop) {Q : ℕ}
    (pubsOf : BKMRequest Sch n N RMsg → Fin Q → Sch.Pub) (c : ℕ) :
    Function.Injective ((seRelayPub (Resp := Resp) pkOf kcOf adm pubsOf).route c) :=
  fun _ _ h => congrArg Prod.snd h

/-- **The relay of proof queries with the public values of the witnesses' signatures** (to the
real and the simulated zero-knowledge challengers) at the side coins `(keys, draws)`: request
number `c` is sent as the proof query of its statement `stmtAt` at the public value of the
signer's signature with the drawn signing coins, and its witness `witAt` with that signature, and
answered by `sideAnswer`.

Running time: that of `seRelay`, plus one base signature for a ring-signing request by a member.
This running time is argued here, not proved in Lean. -/
noncomputable def zkRelaySig {Resp : Type} (adm : List Sch.PK → Prop)
    (bind : List Sch.PK → RMsg → Sch.Msg) {Q : ℕ} (s : SideCoins Sch n Q) :
    SideRelay (BKMRequest Sch n N RMsg) (RingResponse Sch Resp)
      (ProofQuery (RelayStmt Sch n N RMsg) (RelayWit Sch N)) Resp where
  route c r := ⟨(stmtAt (fun i => Sch.pk (s.1 i)) adm (sigPubs s.1 bind (rdCoins Sch n) s.2 r) c r,
    r), witAt s.1 adm bind s.2 c r⟩
  answer c r := sideAnswer (fun i => Sch.pk (s.1 i)) s.1 adm
    (sigPubs s.1 bind (rdCoins Sch n) s.2 r) c r

omit [Fintype RMsg] [DecidableEq RMsg] [Fintype Sch.PK] [Fintype Sch.Msg] [DecidableEq Sch.Msg]
  [Fintype Sch.Sig] [DecidableEq Sch.Sig] [Fintype Sch.Pub] [DecidableEq Sch.Pub]
  [Fintype Sch.KeyCoins] [DecidableEq Sch.KeyCoins] [Fintype Sch.SignCoins]
  [DecidableEq Sch.SignCoins] in
theorem zkRelaySig_route_injective {Resp : Type} (adm : List Sch.PK → Prop)
    (bind : List Sch.PK → RMsg → Sch.Msg) {Q : ℕ} (s : SideCoins Sch n Q) (c : ℕ) :
    Function.Injective ((zkRelaySig (Resp := Resp) (N := N) adm bind s).route c) :=
  fun _ _ h => congrArg (fun q => q.stmt.2) h

omit [Fintype RMsg] [DecidableEq RMsg] [Fintype Sch.PK] [Fintype Sch.Msg] [DecidableEq Sch.Msg]
  [Fintype Sch.Sig] [DecidableEq Sch.Sig] [Fintype Sch.Pub] [DecidableEq Sch.Pub]
  [Fintype Sch.KeyCoins] [DecidableEq Sch.KeyCoins] [Fintype Sch.SignCoins]
  [DecidableEq Sch.SignCoins] in
/-- **The relayed proof query is in the ring relation exactly for a member's ring-signing
request** numbered below `Q` whose drawn signature verifies: the statement's public value is that
of the witness's signature. -/
theorem mem_ringRel_iff_signerIn_sig (adm : List Sch.PK → Prop)
    (bind : List Sch.PK → RMsg → Sch.Msg) {Q : ℕ} (s : SideCoins Sch n Q) (c : ℕ)
    (r : BKMRequest Sch n N RMsg) :
    ((stmtAt (fun i => Sch.pk (s.1 i)) adm (sigPubs s.1 bind (rdCoins Sch n) s.2 r) c r,
      (witAt s.1 adm bind s.2 c r).toWit) ∈ ringRel adm bind) ↔
      c < Q ∧ signerIn (fun i => Sch.pk (s.1 i)) adm r ∧
        drawVerifies Sch N RMsg s.1 bind s.2 c r := by
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
        exact ⟨hs.2.1, RingRel.of_signWith (bind := bind) (m := m) (kc := s.1 s') (R := R) hidx
          (List.getElem_idxOf hidx) (hv hs.1)⟩
  · refine iff_of_false (fun h => ?_) (fun h => hs ⟨h.1, h.2.1⟩)
    have hl := h.2.idx_lt
    rw [stmtAt, dite_eq_right_of_eq_false (eq_false hs)] at hl
    exact absurd hl (Nat.not_lt_zero _)

/-! ### The simulated challengers -/

variable {m k e : ℕ} {Resp SC : Type} [Fintype SC] [DecidableEq SC]

open Classical in
/-- **The reply of the simulated challengers with real public values** to request number `i` at
the keys `κ` and the draw `d` (per-request coins and simulator coins), with the test `ok` of the
drawn coins: a ring-signing request by a member whose coins pass `ok` runs `S` on its statement
`stmtAt` with the public value of the signer's signature at the coins (`sigOf`), answers with the
simulated proof as a ring signature (`sideAnswer`) and appends the simulator's assignments; a
member's request failing `ok` gets `none`; any other request is answered by `sideAnswer` from the
keys, without queries or assignments. -/
noncomputable def simReplySig (S : NARG.Simulator (Bits m) (XOut k e) (RingStmt Sch RMsg N) Resp SC)
    (adm : List Sch.PK → Prop) (bind : List Sch.PK → RMsg → Sch.Msg) {C : Type}
    (rd : C → Fin n → Sch.Msg → Sch.SignCoins) (Q : ℕ)
    (ok : (Fin n → Sch.KeyCoins) → C → BKMRequest Sch n N RMsg → Prop)
    (κ : Fin n → Sch.KeyCoins) (d : C × SC) (i : ℕ) (r : BKMRequest Sch n N RMsg) :
    OracleProg (Bits m) (XOut k e) (Reply (Bits m) (XOut k e) (RingResponse Sch Resp)) :=
  if signerIn (fun i => Sch.pk (κ i)) adm r then
    if ok κ d.1 r then
      (S.prog (stmtAt (fun i => Sch.pk (κ i)) adm
        (fun _ : Fin Q => Sch.pub (sigOf κ bind rd d.1 r)) i r) d.2).bind fun o =>
        .pure ⟨sideAnswer (fun i => Sch.pk (κ i)) κ adm
          (fun _ : Fin Q => Sch.pub (sigOf κ bind rd d.1 r)) i r (some o.proof), o.assignments⟩
    else .pure ⟨none, []⟩
  else .pure ⟨sideAnswer (fun i => Sch.pk (κ i)) κ adm
    (fun _ : Fin Q => Sch.pub (sigOf κ bind rd d.1 r)) i r none, []⟩

/-- **The simulated challengers with real public values as split challengers**: uniform keys,
per request uniform coins `C` (read by `rd`) and simulator coins, the replies `simReplySig` with
the test `ok`. -/
noncomputable def simSplitSig (S : NARG.Simulator (Bits m) (XOut k e) (RingStmt Sch RMsg N) Resp SC)
    (adm : List Sch.PK → Prop) (bind : List Sch.PK → RMsg → Sch.Msg) {C : Type} [Fintype C]
    [DecidableEq C] [Nonempty C] (rd : C → Fin n → Sch.Msg → Sch.SignCoins) (Q : ℕ)
    (ok : (Fin n → Sch.KeyCoins) → C → BKMRequest Sch n N RMsg → Prop) :
    SplitChallenger (Bits m) (XOut k e) (BKMRequest Sch n N RMsg) (RingResponse Sch Resp)
      (Fin n → Sch.KeyCoins) (C × SC) where
  keys := PMF.uniformOfFintype _
  draw := (PMF.uniformOfFintype C).bind fun c => S.coins.map fun d => (c, d)
  Q := Q
  q := S.q
  reply := simReplySig S adm bind rd Q ok
  reply_queries κ d i r H := by
    unfold simReplySig
    split_ifs
    · rw [OracleProg.trace_bind, OracleProg.trace_pure, List.append_nil]
      exact S.prog_queries _ _ H
    · simp
    · simp

/-! ### The coins -/

/-- **Keys and per-request pairs as keys with per-request first components, and per-request second
components.** -/
def splitEquivOf (Q : ℕ) (C D : Type) :
    (Fin n → Sch.KeyCoins) × (Fin Q → C × D) ≃ ((Fin n → Sch.KeyCoins) × (Fin Q → C)) × (Fin Q → D)
    where
  toFun ω := ((ω.1, fun c => (ω.2 c).1), fun c => (ω.2 c).2)
  invFun p := (p.1.1, fun c => (p.1.2 c, p.2 c))
  left_inv _ := rfl
  right_inv _ := rfl

omit [Fintype RMsg] [DecidableEq RMsg] [Nonempty RMsg] [Fintype SC] [DecidableEq SC]
  [DecidableEq Sch.PK] [Nonempty Sch.Pub] [DecidableEq Sch.KeyCoins] [Nonempty Sch.SignCoins]
  [Fintype Sch.PK] [Fintype Sch.Msg] [DecidableEq Sch.Msg] [Fintype Sch.Sig] [DecidableEq Sch.Sig]
  [Fintype Sch.Pub] [DecidableEq Sch.Pub] [Fintype Sch.SignCoins] [DecidableEq Sch.SignCoins] in
/-- **Uniform keys and per-request draws are uniform keys and independent uniform draws.** -/
theorem uniformOfFintype_keysDraws_apply {C : Type} [Fintype C] [Nonempty C] (Q : ℕ)
    (s : (Fin n → Sch.KeyCoins) × (Fin Q → C)) :
    PMF.uniformOfFintype ((Fin n → Sch.KeyCoins) × (Fin Q → C)) s =
      PMF.uniformOfFintype (Fin n → Sch.KeyCoins) s.1 * ∏ i, PMF.uniformOfFintype C (s.2 i) := by
  simp only [PMF.uniformOfFintype_apply, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    Fintype.card_prod (Fin n → Sch.KeyCoins), Fintype.card_pi, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, Nat.cast_mul, Nat.cast_pow, ← ENNReal.inv_pow]
  exact ENNReal.mul_inv (Or.inr (ENNReal.pow_ne_top (ENNReal.natCast_ne_top _)))
    (Or.inl (ENNReal.pow_ne_top (ENNReal.natCast_ne_top _)))

omit [Fintype RMsg] [DecidableEq RMsg] in
/-- **The coins of the simulated challengers with real public values are uniform side coins and
independent simulator coins.** -/
theorem coinLaw_simSplitSig_splitEquivOf_symm
    (S : NARG.Simulator (Bits m) (XOut k e) (RingStmt Sch RMsg N) Resp SC)
    (adm : List Sch.PK → Prop) (bind : List Sch.PK → RMsg → Sch.Msg) {C : Type} [Fintype C]
    [DecidableEq C] [Nonempty C] (rd : C → Fin n → Sch.Msg → Sch.SignCoins) (Q : ℕ)
    (ok : (Fin n → Sch.KeyCoins) → C → BKMRequest Sch n N RMsg → Prop)
    (s : (Fin n → Sch.KeyCoins) × (Fin Q → C)) (c : Fin Q → SC) :
    (simSplitSig S adm bind rd Q ok).toChallenger.coins ((splitEquivOf Q C SC).symm (s, c)) =
      PMF.uniformOfFintype ((Fin n → Sch.KeyCoins) × (Fin Q → C)) s *
        (PMF.pi fun _ => S.coins) c := by
  change ((PMF.uniformOfFintype (Fin n → Sch.KeyCoins)).bind fun κ =>
    (PMF.pi fun _ : Fin Q => (PMF.uniformOfFintype C).bind fun c => S.coins.map fun d => (c, d)).map
      fun d => (κ, d)) ((splitEquivOf Q C SC).symm (s, c)) = _
  simp only [splitEquivOf, Equiv.coe_fn_symm_mk]
  rw [bind_map_pair_apply, PMF.pi_apply, PMF.pi_apply, uniformOfFintype_keysDraws_apply,
    mul_assoc, ← Finset.prod_mul_distrib]
  congr 2
  funext i
  exact bind_map_pair_apply _ _ _ _

/-! ### The relays of the challengers -/

variable {Coins : Type} [Fintype Coins] [DecidableEq Coins]
  (Pv : NARG.Prover (Bits m) (XOut k e) (RingStmt Sch RMsg N) (RingWit Sch) Resp Coins)
    (μ : PMF Coins)
  (bind : List Sch.PK → RMsg → Sch.Msg) (adm : List Sch.PK → Prop)

omit [Fintype RMsg] [DecidableEq RMsg] [Fintype SC] [DecidableEq SC] in
open Classical in
/-- **The checked layer of BKM06 relays the real challenger** of the honest prover `Pv` on the
relayed proof queries with the public values of the witnesses' signatures (`zkRelaySig`), at the
side coins of its draws. -/
theorem relays_bkm_real_sig (Q : ℕ) (s : SideCoins Sch n Q) (c : Fin Q → Coins) :
    (zkRelaySig (N := N) (Resp := Resp) adm bind s).RelaysChallenger
      ((checkedBkmLayer Pv μ bind adm).challenger Q)
      ((drawEquiv (checkedBkmLayer Pv μ bind adm) Q).symm (s, c))
      (realChallenger (fun x w => (x.1, RelayWit.toWit w) ∈ ringRel adm bind)
        (Pv.comap Prod.fst RelayWit.toWit) μ Q) c := by
  refine ⟨rfl, ?_, ?_⟩
  · intro hist hist' r G hrel hQ
    have hlen : hist.length = hist'.length := by
      simpa using (congrArg List.length hrel).symm
    change hist.length < Q at hQ
    have hQ' : hist'.length < Q := hlen ▸ hQ
    have hi : (⟨hist'.length, hQ'⟩ : Fin Q) = ⟨hist.length, hQ⟩ := Fin.ext hlen.symm
    simp only [OracleLayer.challenger, realChallenger, zkRelaySig, hQ, hQ', dite_true, hi,
      NARG.Prover.comap, OracleLayer.oracleAt]
    simp only [drawEquiv, splitEquiv, Equiv.coe_fn_symm_mk]
    simp only [checkedBkmLayer]
    cases r with
    | publicKey j =>
      simp [mem_ringRel_iff_signerIn_sig, BKMRequest.Admissible, signerIn, sideAnswer, hQ,
        OracleProg.run_bind, OracleProg.run_query, baseAnswer]
    | corrupt j =>
      simp [mem_ringRel_iff_signerIn_sig, BKMRequest.Admissible, signerIn, sideAnswer, hQ,
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
          · have hrel := (mem_ringRel_iff_signerIn_sig adm bind s hist.length
              (.ringSign s' R m)).2 ⟨hQ, h.2, fun _ => hv⟩
            simp only [hv, ite_true, OracleProg.run_bind, OracleProg.run_pure, hrel]
            rw [stmtAt, witAt, dite_eq_left_of_eq_true (eq_true h),
              dite_eq_left_of_eq_true (eq_true h)]
            rfl
          · have hrel : ¬ _ := fun hr => hv (((mem_ringRel_iff_signerIn_sig adm bind s
              hist.length (.ringSign s' R m)).1 hr).2.2 hQ)
            simp only [hv, Bool.false_eq_true, ite_false, OracleProg.run_pure, hrel]
            rfl
        · have hrel : ¬ _ := fun hr => hm ((mem_ringRel_iff_signerIn_sig adm bind s hist.length
            (.ringSign s' R m)).1 hr).2.1.2
          simp only [ha, hm, ite_true, ite_false, checkedRingSignAfterKey, OracleProg.run_query,
            OracleProg.run_pure, baseAnswer, hrel, signerIn, and_false]
      · have hrel : ¬ _ := fun hr => ha ((mem_ringRel_iff_signerIn_sig adm bind s hist.length
          (.ringSign s' R m)).1 hr).2.1.1
        simp only [ha, ite_false, OracleProg.run_pure, hrel, signerIn, false_and]
  · intro i r h
    change Q ≤ i at h
    simp only [zkRelaySig, sideAnswer, show ¬ i < Q from not_lt.2 h, dite_false]

omit [Fintype RMsg] [DecidableEq RMsg] [DecidableEq Sch.PK] [Nonempty Sch.Pub]
  [Fintype Sch.KeyCoins] [DecidableEq Sch.KeyCoins] [Fintype Sch.SignCoins]
  [DecidableEq Sch.SignCoins] [Fintype Sch.PK] [Fintype Sch.Msg] [DecidableEq Sch.Msg]
  [Fintype Sch.Sig] [DecidableEq Sch.Sig] [Fintype Sch.Pub] [DecidableEq Sch.Pub] in
/-- At the reader `rdCoins`, `drawOkSig` is `drawOk`. -/
theorem drawOkSig_rdCoins (keys : Fin n → Sch.KeyCoins) (c : Sch.SignCoins)
    (r : BKMRequest Sch n N RMsg) :
    drawOkSig Sch N RMsg bind (rdCoins Sch n) keys c r ↔ drawOk Sch N RMsg bind keys c r := by
  cases r <;> rfl

omit [Fintype RMsg] [DecidableEq RMsg] in
open Classical in
/-- **The checked simulated challenger with real public values relays the simulated
zero-knowledge challenger** of the simulator `S` on the relayed proof queries (`zkRelaySig`). -/
theorem relays_sim_zk_sig (S : NARG.Simulator (Bits m) (XOut k e) (RingStmt Sch RMsg N) Resp SC)
    (Q : ℕ) (s : SideCoins Sch n Q) (c : Fin Q → SC) :
    (zkRelaySig (N := N) (Resp := Resp) adm bind s).RelaysChallenger
      (simSplitSig S adm bind (rdCoins Sch n) Q (drawOkSig Sch N RMsg bind (rdCoins Sch n))).toChallenger
      ((splitEquiv Q SC).symm (s, c))
      (simChallenger (fun x w => (x.1, RelayWit.toWit w) ∈ ringRel adm bind)
        (S.comap Prod.fst) Q) c := by
  refine ⟨rfl, ?_, ?_⟩
  · intro hist hist' r G hrel hQ
    have hlen : hist.length = hist'.length := by
      simpa using (congrArg List.length hrel).symm
    change hist.length < Q at hQ
    have hQ' : hist'.length < Q := hlen ▸ hQ
    have hi : (⟨hist'.length, hQ'⟩ : Fin Q) = ⟨hist.length, hQ⟩ := Fin.ext hlen.symm
    simp only [SplitChallenger.toChallenger, simSplitSig, simReplySig,
      simChallenger, zkRelaySig, hQ, hQ', dite_true, hi, NARG.Simulator.comap, splitEquiv,
      Equiv.coe_fn_symm_mk]
    have hst : stmtAt (fun i => Sch.pk (s.1 i)) adm
        (fun _ : Fin Q => Sch.pub (sigOf s.1 bind (rdCoins Sch n) (s.2 ⟨hist.length, hQ⟩) r))
        hist.length r =
        stmtAt (fun i => Sch.pk (s.1 i)) adm (sigPubs s.1 bind (rdCoins Sch n) s.2 r) hist.length r :=
      stmtAt_pubs_congr (fun _ => rfl) r
    have hsa : ∀ a : Option Resp, sideAnswer (fun i => Sch.pk (s.1 i)) s.1 adm
        (fun _ : Fin Q => Sch.pub (sigOf s.1 bind (rdCoins Sch n) (s.2 ⟨hist.length, hQ⟩) r))
        hist.length r a =
        sideAnswer (fun i => Sch.pk (s.1 i)) s.1 adm (sigPubs s.1 bind (rdCoins Sch n) s.2 r)
          hist.length r a :=
      fun a => sideAnswer_pubs_congr (fun _ => rfl) r a
    simp only [hst, hsa]
    by_cases hs : signerIn (fun i => Sch.pk (s.1 i)) adm r
    · by_cases hv : drawVerifies Sch N RMsg s.1 bind s.2 hist.length r
      · have hrel := (mem_ringRel_iff_signerIn_sig adm bind s hist.length r).2 ⟨hQ, hs, hv⟩
        have hok : drawOkSig Sch N RMsg bind (rdCoins Sch n) s.1 (s.2 ⟨hist.length, hQ⟩) r :=
          (drawOkSig_rdCoins bind s.1 _ r).2 (hv hQ)
        simp only [hs, hok, hrel, ite_true, OracleProg.run_bind, OracleProg.run_pure]
      · have hrel : ¬ _ := fun h =>
          hv ((mem_ringRel_iff_signerIn_sig adm bind s hist.length r).1 h).2.2
        have hok : ¬ drawOkSig Sch N RMsg bind (rdCoins Sch n) s.1 (s.2 ⟨hist.length, hQ⟩) r :=
          fun h => hv fun _ => (drawOkSig_rdCoins bind s.1 _ r).1 h
        simp only [hs, hok, hrel, ite_true, ite_false, OracleProg.run_pure]
        unfold sideAnswer
        cases r <;> simp_all [signerIn]
    · simp only [hs, mem_ringRel_iff_signerIn_sig, hQ, true_and, false_and, ite_false,
        OracleProg.run_pure, sideAnswer_of_not_signerIn hs]
  · intro i r h
    change Q ≤ i at h
    simp only [zkRelaySig, sideAnswer, show ¬ i < Q from not_lt.2 h, dite_false]

omit [Fintype RMsg] [DecidableEq RMsg] [Fintype Sch.PK] [Fintype Sch.Msg] [DecidableEq Sch.Msg]
  [Fintype Sch.Sig] [DecidableEq Sch.Sig] [Fintype Sch.Pub] [DecidableEq Sch.Pub] in
/-- **The simulated challenger with real public values relays the simulation-extraction
challenger** of the simulator inert on the empty ring (`inertOnEmpty`) on the relayed statements
with the public values of the signers' signatures at the drawn coins (`seRelayPub`), at every
reader `rd`. -/
theorem relays_sim_se_sig (S : NARG.Simulator (Bits m) (XOut k e) (RingStmt Sch RMsg N) Resp SC)
    {C : Type} [Fintype C] [DecidableEq C] [Nonempty C] (rd : C → Fin n → Sch.Msg → Sch.SignCoins)
    (p₀ : Resp) (Q : ℕ) (s : (Fin n → Sch.KeyCoins) × (Fin Q → C)) (c : Fin Q → SC) :
    (seRelayPub (N := N) (Resp := Resp) (fun i => Sch.pk (s.1 i)) s.1 adm
        (sigPubs s.1 bind rd s.2)).RelaysChallenger
      (simSplitSig S adm bind rd Q fun _ _ _ => True).toChallenger
      ((splitEquivOf Q C SC).symm (s, c))
      (simExtChallenger ((inertOnEmpty S p₀).comap Prod.fst) Q) c := by
  refine ⟨rfl, ?_, ?_⟩
  · intro hist hist' r G hrel hQ
    have hlen : hist.length = hist'.length := by
      simpa using (congrArg List.length hrel).symm
    change hist.length < Q at hQ
    have hQ' : hist'.length < Q := hlen ▸ hQ
    have hi : (⟨hist'.length, hQ'⟩ : Fin Q) = ⟨hist.length, hQ⟩ := Fin.ext hlen.symm
    simp only [SplitChallenger.toChallenger, simSplitSig, simReplySig,
      simExtChallenger, simExtRespond, seRelayPub, hQ, hQ', dite_true, hi, inertOnEmpty,
      NARG.Simulator.comap, splitEquivOf, Equiv.coe_fn_symm_mk, ite_true]
    have hst : stmtAt (fun i => Sch.pk (s.1 i)) adm
        (fun _ : Fin Q => Sch.pub (sigOf s.1 bind rd (s.2 ⟨hist.length, hQ⟩) r)) hist.length r =
        stmtAt (fun i => Sch.pk (s.1 i)) adm (sigPubs s.1 bind rd s.2 r) hist.length r :=
      stmtAt_pubs_congr (fun _ => rfl) r
    have hsa : ∀ a : Option Resp, sideAnswer (fun i => Sch.pk (s.1 i)) s.1 adm
        (fun _ : Fin Q => Sch.pub (sigOf s.1 bind rd (s.2 ⟨hist.length, hQ⟩) r)) hist.length r a =
        sideAnswer (fun i => Sch.pk (s.1 i)) s.1 adm (sigPubs s.1 bind rd s.2 r) hist.length r a :=
      fun a => sideAnswer_pubs_congr (fun _ => rfl) r a
    simp only [hst, hsa]
    by_cases hs : signerIn (fun i => Sch.pk (s.1 i)) adm r
    · have hne : ¬ (stmtAt (fun i => Sch.pk (s.1 i)) adm (sigPubs s.1 bind rd s.2 r)
          hist.length r).ring.1 = [] := by
        rw [stmtAt_ring_eq_nil_iff]
        exact not_not.2 ⟨hQ, hs⟩
      simp only [hs, hne, ite_true, ite_false, OracleProg.run_bind, OracleProg.run_pure]
    · have he : (stmtAt (fun i => Sch.pk (s.1 i)) adm (sigPubs s.1 bind rd s.2 r)
          hist.length r).ring.1 = [] := by
        rw [stmtAt_ring_eq_nil_iff]
        exact fun h => hs h.2
      simp only [hs, he, ite_true, ite_false, OracleProg.run_bind, OracleProg.run_pure,
        sideAnswer_of_not_signerIn hs]
  · intro i r h
    change Q ≤ i at h
    simp only [seRelayPub, sideAnswer, show ¬ i < Q from not_lt.2 h, dite_false]

/-! ### The hybrid of the correctness error -/

omit [Fintype RMsg] [DecidableEq RMsg] [Fintype Sch.PK] [Fintype Sch.Msg] [DecidableEq Sch.Msg]
  [Fintype Sch.Sig] [DecidableEq Sch.Sig] [Fintype Sch.Pub] [DecidableEq Sch.Pub] in
/-- **The simulated challenger is the checked one with other replies**, as split challengers. -/
theorem simSplitSig_withReply (S : NARG.Simulator (Bits m) (XOut k e) (RingStmt Sch RMsg N) Resp SC)
    (Q : ℕ) :
    simSplitSig S adm bind (rdCoins Sch n) Q (fun _ _ _ => True) =
      (simSplitSig S adm bind (rdCoins Sch n) Q (drawOkSig Sch N RMsg bind (rdCoins Sch n))).withReply
        (simSplitSig S adm bind (rdCoins Sch n) Q (fun _ _ _ => True)).reply
        (simSplitSig S adm bind (rdCoins Sch n) Q (fun _ _ _ => True)).reply_queries :=
  rfl

omit [Fintype RMsg] [DecidableEq RMsg] in
/-- **The checked and the unchecked simulated challengers with real public values disagree with at
most the correctness error** at every request. -/
theorem draw_simSplitSig_ne_le {ε : ℝ≥0∞} (hcorr : Sch.CorrectWithin ε)
    (S : NARG.Simulator (Bits m) (XOut k e) (RingStmt Sch RMsg N) Resp SC) (Q : ℕ)
    (κ : Fin n → Sch.KeyCoins) (i : ℕ) (r : BKMRequest Sch n N RMsg) :
    (simSplitSig S adm bind (rdCoins Sch n) Q
        (drawOkSig Sch N RMsg bind (rdCoins Sch n))).draw.toOuterMeasure
      {d | (simSplitSig S adm bind (rdCoins Sch n) Q
          (drawOkSig Sch N RMsg bind (rdCoins Sch n))).reply κ d i r ≠
        (simSplitSig S adm bind (rdCoins Sch n) Q fun _ _ _ => True).reply κ d i r} ≤ ε := by
  classical
  refine le_trans (MeasureTheory.measure_mono fun d hd =>
    show ¬ drawOk Sch N RMsg bind κ d.1 r from fun h => hd ?_) ?_
  · simp only [simSplitSig, simReplySig, (drawOkSig_rdCoins bind κ d.1 r).2 h, ite_true]
  · change ((PMF.uniformOfFintype Sch.SignCoins).bind fun c => S.coins.map fun d => (c, d)).toOuterMeasure
      {d | ¬ drawOk Sch N RMsg bind κ d.1 r} ≤ ε
    rw [toOuterMeasure_bind_map_fst (p := fun c => ¬ drawOk Sch N RMsg bind κ c r)]
    exact toOuterMeasure_not_drawOk_le hcorr bind κ r

end GordieHowe.Ring
