-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.RingSignature.Base
public import GordieHowe.Applications.Falcon512.Ring.Native.System.Scheme
public import GordieHowe.Applications.Ring.PublicW1.MLDSAPublicW1

@[expose] public section

/-!
# The base signers of the library's three ring signatures

The shapes of the three constructions as `RingSignature.BaseSigner`s
(`GordieHowe/Model/RingSignature/Base.lean`), so that each ring signature is
`RingSignature.ofBase B PS adm` for its base signer `B`, its proof system `PS` and its supported
rings `adm`. Their completeness facts are in `GordieHowe/Applications/Ring/BaseSignerFacts.lean`.

- `falconBaseSigner G bmsg`: Falcon-512 (`Falcon512.Ring.Native`, FIPS 206 / Falcon specification
  v1.2) with the signer `G` (key generation and signing are not specified in Lean). The base
  signer reads the ring only through `bmsg` (`m`, or `m ‖ encode R`) and never refuses
  (`falconBaseSigner_refuseAtWithin`); the public value is the salt, read off the signature;
  verification is the vendored verifier and reads no oracle
  (`falconBaseSigner_verifiesWithoutOracle`).
- `mldsaBaseSigner p prims maxAttempts bmsg`: ML-DSA (FIPS 204) at the parameter set `p`, with
  the hedged signer `fipsSignWith` (the vendored attempts `fipsSignAttempt` at the 32-byte coins
  `rnd`, Algorithm 7, with at most `maxAttempts` attempts and the bounded `ExpandA` and
  `SampleInBall` of FIPS 204 Appendix C: the signer aborts when `ExpandA(ρ)` or the `SampleInBall`
  of an attempt's commitment hash `c̃` runs out of bytes, and refuses when every attempt is
  rejected) on the base message, and the public value `Unit`. Verification is FIPS 204
  verification with the bounded samplers, `boundedOk p ρ c̃ && fipsVerify`, at the concrete
  primitives the vendored `MLDSA.Concrete.verify` (`mldsaBaseSigner_bverify_concrete`). The
  bounded-sampling check `boundedOk p` is the one of the concrete SHAKE-based `ExpandA` and
  `SampleInBall` (`MLDSA.Concrete.expandA?`, `MLDSA.Concrete.sampleInBallPoly?`) at every `prims`;
  so the base signer is FIPS 204 with bounded samplers at primitives whose `expandA` and
  `sampleInBall` are the concrete ones (`concretePrimitives`, `concretePrimitivesFIPS`). Neither
  reads the oracle (`mldsaBaseSigner_verifiesWithoutOracle`; the FIPS 204 hashes are the vendored
  functions).
- `MLDSAW1.w1BaseSigner`: the ML-DSA ring publishing `w₁`. Published keys `(ρ, t₁, t₀)`; the base
  signature `(c̃, z, h)` without `w₁`; the public value `w₁ = enc(UseHint(h, Â·z − c·t₁·2^d))`
  recomputed from the key and the signature (`w1Of`); verification `ringVerify` against the
  commitment hash `H(H_µ(tr, m), w₁)` read from the oracle (`W1Oracles.hOrc`). The base signer
  reads the ring: it refuses rings failing the public check `RingCheck` against the check oracle
  `G`, which it reads by at most `N · reps` classical queries (`ringCheckProg`,
  `run_ringCheckProg`, `ringCheckProg_queries`), and rings whose members' message representatives
  `µ_j = H_µ(tr_j, m)` are not pairwise distinct (`MuDistinct`, by at most `N` queries:
  `muDistinctProg`, `run_muDistinctProg`, `muDistinctProg_queries`), and otherwise runs the ring
  loop `L.sign` (a parameter `L : W1Loop …`; `GordieHowe/Applications/Ring/MLDSAW1Ring.lean`
  builds the flattened hedged loop). Its ordinary signer is `L.std`.
- `W1Oracles`: the message-representative oracle `H_µ`, the commitment-hash oracle `H` on
  `(µ, w₁)` and the check oracle `G` as parts of the one random oracle `X → Y`: their points
  embedded in `X` and their values decoded from `Y` (domain separation); `W1Oracles.gameOrc`: the
  game's oracles `((H_µ, H), G)` of `GordieHowe/Applications/Ring/PublicW1/MLDSAPublicW1.lean`.
-/

namespace GordieHowe.Ring

open GordieHowe.RingSignature

variable {X Y : Type} {N : ℕ}

/-! ### Falcon-512 -/

section Falcon

open GordieHowe.Falcon512.Ring.Native

variable {msgLen : ℕ}

/-- The types of `falconBaseSigner G bmsg`: Falcon-512 public keys, the keys and coins of `G`, the
ring messages `RMsg`, base messages of `msgLen` bytes, signatures, and the salt as the public value.
-/
abbrev falconBaseT (G : Signer msgLen) (RMsg : Type) [Fintype RMsg] [DecidableEq RMsg] :
    BaseTypes where
  PK := PublicKey
  SK := G.SK
  KeyCoins := G.KeyCoins
  Msg := RMsg
  BMsg := Fin msgLen → UInt8
  BSig := Sig
  Pub := Salt
  Coins := Salt × G.SignCoins

/-- **The Falcon-512 base signer** with the signer `G` and the base message `bmsg` of a ring and a
ring message: keys from `G`, signing `G.signWith` on `bmsg R m` with the drawn salt and private
coins (the ring read only through `bmsg`; no refusal), the ordinary signer on a base message
likewise, verification the vendored Falcon-512 verifier (no oracle), public value the salt. -/
def falconBaseSigner (G : Signer msgLen) {RMsg : Type} [Fintype RMsg] [DecidableEq RMsg]
    (bmsg : KeyRing PublicKey N → RMsg → (Fin msgLen → UInt8)) :
    BaseSigner X Y N (falconBaseT G RMsg) where
  keyGen := G.keyGen
  bmsg := bmsg
  q := 0
  bsign sk R _ m c := .pure (some (G.signWith sk (bmsg R m) c.1 c.2))
  bsign_queries _ _ _ _ _ := OracleProg.QueriesLE.pure _ _
  ssign sk bm c := .pure (some (G.signWith sk bm c.1 c.2))
  ssign_queries _ _ _ := OracleProg.QueriesLE.pure _ _
  bverify _ pk bm σ := verifySig pk bm σ
  qPub := 0
  pub _ σ := .pure σ.1.salt
  pub_queries _ _ := OracleProg.QueriesLE.pure _ _

end Falcon

/-! ### ML-DSA -/

section MLDSA

open _root_.MLDSA LatticeCrypto TransformOps

variable (p : Params) (prims : Primitives p) [nttOps : NTTRingOps]

/-- An ML-DSA public key `(ρ, t₁)` as a pair. -/
def publicKeyEquiv : PublicKey p prims ≃ Bytes 32 × Vector prims.Power2High p.k where
  toFun pk := (pk.rho, pk.t1)
  invFun x := ⟨x.1, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance [Fintype prims.Power2High] : Fintype (PublicKey p prims) :=
  Fintype.ofEquiv _ (publicKeyEquiv p prims).symm

instance [DecidableEq prims.Power2High] : DecidableEq (PublicKey p prims) :=
  (publicKeyEquiv p prims).decidableEq

/-- **The bounded-sampling acceptance check of FIPS 204 Appendix C** at the concrete primitives:
`ExpandA(ρ)` finishes within the vendored bound of every `RejNTTPoly` call (`expandA?`) and
`SampleInBall(c̃)` within its `272` SHAKE256 bytes (`sampleInBallPoly?`). The check is that of
the concrete SHAKE-based samplers at every parameter set, whatever primitives the signer uses. -/
def boundedOk (p : Params) (rho : Bytes 32) (cTilde : CommitHashBytes p) : Bool :=
  (Concrete.expandA? p rho).isSome && (Concrete.sampleInBallPoly? p cTilde).isSome

/-- **The commitment hash of a signing attempt** (FIPS 204 Algorithm 7, lines 11–15): with
`y = ExpandMask(ρ'', κ)`, `c̃ = H(µ ‖ w1Encode(HighBits(Â·y)))`, the commitment hash
`fipsSignAttempt` computes and outputs. -/
def fipsAttemptCommit (aHat : TqMatrix p.k p.l) (mu : Bytes 64) (rhoDoublePrime : Bytes 64)
    (kappa : ℕ) : CommitHashBytes p :=
  prims.hashCommitment mu (prims.w1Encode (prims.highBitsVec (aHat * prims.expandMask rhoDoublePrime
    kappa)))

/-- **A signature of an attempt carries the attempt's commitment hash.** -/
theorem cTilde_of_fipsSignAttempt {sk : SecretKey p} {aHat : TqMatrix p.k p.l} {mu rhoDoublePrime :
    Bytes 64} {kappa : ℕ} {σ : FIPSSignature p prims}
    (h : fipsSignAttempt p prims sk aHat mu rhoDoublePrime kappa = some σ) :
    σ.cTilde = fipsAttemptCommit p prims aHat mu rhoDoublePrime kappa := by
  unfold fipsSignAttempt at h
  dsimp only at h
  split_ifs at h
  rw [Option.some.injEq] at h
  subst h
  rfl

/-- **The hedged FIPS 204 signer** (Algorithm 7) at the coins `rnd`, with the bounded `ExpandA` and
`SampleInBall` of FIPS 204 Appendix C: `µ = H(tr ‖ M)`, `ρ'' = H(K ‖ rnd ‖ µ)`; abort (`none`)
when the bounded `ExpandA(ρ)` runs out of bytes; then at most `maxAttempts` attempts of the
vendored `fipsSignAttempt` (counter `κ = i · l`): an attempt whose bounded `SampleInBall` of its
commitment hash (`fipsAttemptCommit`) runs out of bytes aborts the signer (Appendix C: "return a
constant that represents an error and no other output"), and otherwise the first attempt that is
not rejected is the signature; `none` when every attempt is rejected. -/
def fipsSignWith (maxAttempts : ℕ) (sk : SecretKey p) (msg : List Byte) (rnd : Bytes 32) :
    Option (FIPSSignature p prims) :=
  if (Concrete.expandA? p sk.rho).isSome then
    ((List.range maxAttempts).findSome? fun i =>
      if (Concrete.sampleInBallPoly? p (fipsAttemptCommit p prims (prims.expandA sk.rho)
          (prims.hashMessage sk.tr msg)
          (prims.hashPrivateSeed sk.key rnd (prims.hashMessage sk.tr msg)) (i * p.l))).isSome then
        (fipsSignAttempt p prims sk (prims.expandA sk.rho) (prims.hashMessage sk.tr msg)
          (prims.hashPrivateSeed sk.key rnd (prims.hashMessage sk.tr msg)) (i * p.l)).map some
      else some none).join
  else none

/-- **A signature of the signer is an attempt's signature passing the bounded-sampling check**: it
is the output of `fipsSignAttempt` at some counter `κ = i · l`, and `boundedOk p ρ c̃` holds at the
signer's `ρ`. -/
theorem exists_attempt_of_fipsSignWith {maxAttempts : ℕ} {sk : SecretKey p} {msg : List Byte}
    {rnd : Bytes 32} {σ : FIPSSignature p prims}
    (h : fipsSignWith p prims maxAttempts sk msg rnd = some σ) :
    ∃ i, fipsSignAttempt p prims sk (prims.expandA sk.rho) (prims.hashMessage sk.tr msg)
        (prims.hashPrivateSeed sk.key rnd (prims.hashMessage sk.tr msg)) (i * p.l) = some σ ∧
      boundedOk p sk.rho σ.cTilde = true := by
  unfold fipsSignWith at h
  split_ifs at h with hA
  · rw [Option.join_eq_some_iff] at h
    obtain ⟨i, -, hi⟩ := List.exists_of_findSome?_eq_some h
    split_ifs at hi with hS
    · rw [Option.map_eq_some_iff] at hi
      obtain ⟨σ', hσ', hσσ'⟩ := hi
      cases hσσ'
      refine ⟨i, hσ', ?_⟩
      rw [boundedOk, cTilde_of_fipsSignAttempt p prims hσ', hA, hS, Bool.and_self]
    · simp at hi

/-- **A signature of the signer passes the bounded-sampling check** at the signer's `ρ`. -/
theorem boundedOk_of_fipsSignWith {maxAttempts : ℕ} {sk : SecretKey p} {msg : List Byte}
    {rnd : Bytes 32} {σ : FIPSSignature p prims}
    (h : fipsSignWith p prims maxAttempts sk msg rnd = some σ) :
    boundedOk p sk.rho σ.cTilde = true :=
  (exists_attempt_of_fipsSignWith p prims h).choose_spec.2

variable [Fintype prims.Power2High] [DecidableEq prims.Power2High] [Fintype prims.Hint]
  [DecidableEq prims.Hint]

/-- The types of `mldsaBaseSigner`: ML-DSA keys from 32-byte seeds, the ring messages `RMsg`, base
messages of `len` bytes, FIPS 204 signatures, no public value, 32-byte signing coins. -/
abbrev mldsaBaseT (len : ℕ) (RMsg : Type) [Fintype RMsg] [DecidableEq RMsg] : BaseTypes where
  PK := PublicKey p prims
  SK := SecretKey p
  KeyCoins := Bytes 32
  Msg := RMsg
  BMsg := Bytes len
  BSig := FIPSSignature p prims
  Pub := Unit
  Coins := Bytes 32

/-- **The ML-DSA base signer of the generic ring** with base messages of `len` bytes: keys from a
seed (`keyGenFromSeed`, Algorithm 6), the hedged FIPS 204 signer `fipsSignWith` on `bmsg R m` (the
ring read only through `bmsg`; it refuses when a bounded sampler runs out of bytes or every attempt
is rejected), the ordinary signer
on a base message likewise, and FIPS 204 verification (Algorithm 8 with the bounded `ExpandA` and
`SampleInBall` of Appendix C): the bounded-sampling check `boundedOk p ρ c̃` and `fipsVerify`,
the shape of the vendored `MLDSA.Concrete.verify` (`mldsaBaseSigner_bverify_concrete`). Public
value `Unit`. No oracle is read. -/
def mldsaBaseSigner (maxAttempts : ℕ) {len : ℕ} {RMsg : Type} [Fintype RMsg] [DecidableEq RMsg]
    (bmsg : KeyRing (PublicKey p prims) N → RMsg → Bytes len) :
    BaseSigner X Y N (mldsaBaseT p prims len RMsg) where
  keyGen := keyGenFromSeed p prims
  bmsg := bmsg
  q := 0
  bsign sk R _ m rnd := .pure (fipsSignWith p prims maxAttempts sk (bmsg R m).toList rnd)
  bsign_queries _ _ _ _ _ := OracleProg.QueriesLE.pure _ _
  ssign sk bm rnd := .pure (fipsSignWith p prims maxAttempts sk bm.toList rnd)
  ssign_queries _ _ _ := OracleProg.QueriesLE.pure _ _
  bverify _ pk bm σ := boundedOk p pk.rho σ.cTilde && fipsVerify p prims pk bm.toList σ
  qPub := 0
  pub _ _ := .pure ()
  pub_queries _ _ := OracleProg.QueriesLE.pure _ _

end MLDSA

section MLDSAConcrete

open _root_.MLDSA

/-- **At the concrete primitives and `boundedOk`, the base verification is the vendored
`MLDSA.Concrete.verify`**: FIPS 204 Algorithm 8, rejecting when the bounded `ExpandA` or the
bounded `SampleInBall` runs out of candidates. -/
theorem mldsaBaseSigner_bverify_concrete (p : Params)
    [Fintype (Concrete.concretePrimitives p).Power2High]
    [DecidableEq (Concrete.concretePrimitives p).Power2High]
    [Fintype (Concrete.concretePrimitives p).Hint] [DecidableEq (Concrete.concretePrimitives p).Hint]
    (maxAttempts : ℕ) {len : ℕ}
    {RMsg : Type} [Fintype RMsg] [DecidableEq RMsg]
    (bmsg : KeyRing (PublicKey p (Concrete.concretePrimitives p)) N → RMsg → Bytes len)
    (H : X → Y) (pk : PublicKey p (Concrete.concretePrimitives p)) (bm : Bytes len)
    (σ : FIPSSignature p (Concrete.concretePrimitives p)) :
    (mldsaBaseSigner (X := X) (Y := Y) (nttOps := Concrete.concreteNTTRingOps) p
        (Concrete.concretePrimitives p) maxAttempts bmsg).bverify H pk bm σ =
      Concrete.verify p pk bm.toList σ :=
  rfl

end MLDSAConcrete

/-! ### The ML-DSA ring publishing `w₁` -/

namespace MLDSAW1

open _root_.MLDSA GordieHowe.MLDSA

variable {p : Params} (prims : Primitives p) [NeZero (bucketCount p)] [nttOps : NTTRingOps]
  {Msg : Type} {reps : ℕ}

/-- **The oracles of the ring publishing `w₁` inside the one random oracle `X → Y`**: the points of
the message-representative oracle `H_µ(tr, m)` (`µ = H(tr ‖ M′)`, FIPS 204 Algorithm 7 line 6), of
the commitment-hash oracle `H(µ, w₁)` (`c̃ = H(µ ‖ w1Encode(w₁))`, line 15) and of the check oracle
`G(R, j, r)` embedded in `X`, and their values decoded from `Y`. Distinct embeddings are the domain
separation of the oracles. -/
structure W1Oracles (X Y : Type) (p : Params) (prims : Primitives p) (Msg : Type) (N reps : ℕ) where
  /-- The points of the message-representative oracle. -/
  muPt : Bytes 64 × Msg → X
  /-- The values of the message-representative oracle. -/
  muAns : Y → Bytes 64
  /-- The points of the commitment-hash oracle. -/
  chPt : Bytes 64 × BucketVec p → X
  /-- The values of the commitment-hash oracle. -/
  chAns : Y → CommitHashBytes p
  /-- The points of the check oracle. -/
  gPt : KeyRing (PubKey p prims) N × Fin N × Fin reps → X
  /-- The values of the check oracle. -/
  gAns : Y → CommitHashBytes p

variable {prims}

/-- The message-representative oracle `H_µ` read from the oracle. -/
def W1Oracles.muOrc (O : W1Oracles X Y p prims Msg N reps) (H : X → Y) : MuOrc Msg :=
  fun pt => O.muAns (H (O.muPt pt))

/-- The commitment-hash oracle on `(µ, w₁)` read from the oracle. -/
def W1Oracles.chOrc (O : W1Oracles X Y p prims Msg N reps) (H : X → Y) : ChOrc p :=
  fun pt => O.chAns (H (O.chPt pt))

/-- **The commitment hash** `H((tr, m), w₁) = H(H_µ(tr, m), w₁)` read from the oracle
(`schemeOrc`). -/
def W1Oracles.hOrc (O : W1Oracles X Y p prims Msg N reps) (H : X → Y) : Orc p Msg :=
  schemeOrc (O.muOrc H, O.chOrc H)

/-- The check oracle `G` read from the oracle. -/
def W1Oracles.gOrc (O : W1Oracles X Y p prims Msg N reps) (H : X → Y) :
    CheckOrc p prims N reps :=
  fun pt => O.gAns (H (O.gPt pt))

/-- **The game's oracles** `((H_µ, H), G)` of `MLDSAPublicW1.lean` read from the oracle. -/
def W1Oracles.gameOrc (O : W1Oracles X Y p prims Msg N reps) (H : X → Y) :
    GameOrc prims Msg N reps :=
  ((O.muOrc H, O.chOrc H), O.gOrc H)

variable (prims)

/-- **The recomputed commitment** of a signature `(c̃, z, h)` under a published key `(ρ, t₁, t₀)`:
`w₁ = enc(UseHint(h, Â·z − c·t₁·2^d))` with `Â = ExpandA(ρ)` and `c = SampleInBall(c̃)` (FIPS 204
Algorithm 8, lines 9–10). -/
def w1Of (enc : Vector prims.High p.k → BucketVec p) (pk : PubKey p prims)
    (σ : FIPSSignature p prims) : BucketVec p :=
  enc (prims.useHintVec σ.h (computeWApprox p prims (prims.expandA pk.1)
    (prims.sampleInBall σ.cTilde) σ.z pk.2.1))

/-- **The public ring check as a classical oracle program**: query the check oracle at
`(R, j, r)` for every `j < N` and `r < reps`, then decide `RingCheck` at the cut-off `β_min` with
tolerance `tol` on the answers (at most `N · reps` queries, `ringCheckProg_queries`). -/
def ringCheckProg (O : W1Oracles X Y p prims Msg N reps) (βmin : ℚ≥0) (tol : ℕ)
    (R : KeyRing (PubKey p prims) N) : OracleProg X Y Bool :=
  (OracleProg.tabulate (fun _ => none) (List.finRange N ×ˢ List.finRange reps)
      fun jr => .query (O.gPt (R, jr.1, jr.2)) fun y => .pure (some y)).mapOutput fun T =>
    decide (RingCheck prims βmin tol
      (fun pt : KeyRing (PubKey p prims) N × Fin N × Fin reps =>
        ((T (pt.2.1, pt.2.2)).map O.gAns).getD default) R)

omit [NeZero (bucketCount p)] in
/-- The public ring check makes `N · reps` queries. -/
theorem ringCheckProg_queries (O : W1Oracles X Y p prims Msg N reps) (βmin : ℚ≥0) (tol : ℕ)
    (R : KeyRing (PubKey p prims) N) : (ringCheckProg prims O βmin tol R).QueriesLE (N * reps) :=
  fun h => by
    rw [ringCheckProg, OracleProg.trace_mapOutput, OracleProg.length_trace_tabulate]
    simp [List.length_product]

/-- **The distinct-µ check as a classical oracle program**: query the message-representative
oracle at `(tr_j, m)` for every member `j` of `R` and decide whether the answers `µ_j` are pairwise
distinct (`MuDistinct`; `|R| ≤ N` queries, `muDistinctProg_queries`). -/
def muDistinctProg (O : W1Oracles X Y p prims Msg N reps) (R : KeyRing (PubKey p prims) N)
    (m : Msg) : OracleProg X Y Bool :=
  (OracleProg.queryAll (R.1.map fun x => O.muPt (pubTr prims x, m))).mapOutput fun ys =>
    decide (ys.map O.muAns).Nodup

omit [NeZero (bucketCount p)] nttOps in
/-- The distinct-µ check makes at most `N` queries. -/
theorem muDistinctProg_queries (O : W1Oracles X Y p prims Msg N reps)
    (R : KeyRing (PubKey p prims) N) (m : Msg) : (muDistinctProg prims O R m).QueriesLE N :=
  fun h => by
    rw [muDistinctProg, OracleProg.trace_mapOutput, OracleProg.trace_queryAll, List.length_map]
    exact R.2

omit [NeZero (bucketCount p)] nttOps in
/-- **The distinct-µ check decides `MuDistinct`** at the message-representative oracle read from
the oracle. -/
theorem run_muDistinctProg (O : W1Oracles X Y p prims Msg N reps) (R : KeyRing (PubKey p prims) N)
    (m : Msg) (H : X → Y) :
    (muDistinctProg prims O R m).run H = true ↔ MuDistinct prims (O.muOrc H) R m := by
  simp only [muDistinctProg, OracleProg.run_mapOutput, OracleProg.run_queryAll, List.map_map,
    decide_eq_true_eq]
  rfl

omit [NeZero (bucketCount p)] in
/-- **The public ring check decides `RingCheck`** at the check oracle read from the oracle. -/
theorem run_ringCheckProg (O : W1Oracles X Y p prims Msg N reps) (βmin : ℚ≥0) (tol : ℕ)
    (R : KeyRing (PubKey p prims) N) (H : X → Y) :
    (ringCheckProg prims O βmin tol R).run H = true ↔ RingCheck prims βmin tol (O.gOrc H) R := by
  simp only [ringCheckProg, OracleProg.run_mapOutput, OracleProg.run_tabulate, OracleProg.run_query,
    OracleProg.run_pure, List.mem_product, List.mem_finRange, and_self, ite_true,
    Option.map_some, Option.getD_some, decide_eq_true_eq]
  rfl

/-- **The ring loop of the ring publishing `w₁`** with the signing coins `Coins`, a parameter of
the base signer: the ring loop `sign` from the secret key, the ring, the signer's position, the base
message and coins, the ordinary signer `std`, and a bound `q` on their queries. -/
structure W1Loop (X Y : Type) (p : Params) (prims : Primitives p) (Msg : Type) (N : ℕ)
    (Coins : Type) where
  /-- The bound on the queries. -/
  q : ℕ
  /-- The ring loop. -/
  sign : SecretKey p → KeyRing (PubKey p prims) N → ℕ → Msg → Coins →
    OracleProg X Y (Option (FIPSSignature p prims))
  /-- It makes at most `q` queries. -/
  sign_queries : ∀ sk R i m c, (sign sk R i m c).QueriesLE q
  /-- The ordinary hedged signer. -/
  std : SecretKey p → Msg → Coins → OracleProg X Y (Option (FIPSSignature p prims))
  /-- It makes at most `q` queries. -/
  std_queries : ∀ sk m c, (std sk m c).QueriesLE q

variable [Fintype prims.Power2High] [DecidableEq prims.Power2High] [Fintype prims.Hint]
  [DecidableEq prims.Hint] [Fintype Msg] [DecidableEq Msg]

variable (Msg) in
/-- The types of the base signer of the ML-DSA ring publishing `w₁` with the signing coins `Coins`:
published keys, secret keys from 32-byte seeds, the ring messages `RMsg`, the base messages `Msg`,
FIPS 204 signatures and the public value `w₁`. -/
abbrev w1BaseT (RMsg Coins : Type) [Fintype RMsg] [DecidableEq RMsg] [Fintype Coins]
    [DecidableEq Coins] [Nonempty Coins] : BaseTypes where
  PK := PubKey p prims
  SK := SecretKey p
  KeyCoins := Bytes 32
  Msg := RMsg
  BMsg := Msg
  BSig := FIPSSignature p prims
  Pub := BucketVec p
  Coins := Coins
  -- the instance constants themselves, not their eta-expansions, so that a projection of this
  -- record and concrete instance search reach the same terms
  instDecEqPK := instDecidableEqPubKeyOf
  instDecEqKeyCoins := instDecidableEqVector
  instDecEqBSig := instDecEqFIPSSignature prims
  instDecEqPub := Fintype.decidablePiFintype

/-- **The base signer of the ML-DSA ring publishing `w₁`** with the oracles `O`, the check's
cut-off `β_min` and tolerance `tol`, the encoding `enc` of recomputed commitments, the ring loop `L`
and the base message `bmsg`: published keys `(ρ, t₁, t₀)` (`keyGen`), base signatures `(c̃, z, h)`,
public value `w₁ = w1Of enc pk σ`. The base signer refuses rings failing the public check
(`ringCheckProg`) or whose members' message representatives `µ_j` are not pairwise distinct
(`muDistinctProg`), and otherwise runs `L.sign`; the ordinary signer is `L.std`. Verification is
`ringVerify` against the commitment hash read from the oracle, at the recomputed `w₁`. -/
def w1BaseSigner (O : W1Oracles X Y p prims Msg N reps) (βmin : ℚ≥0) (tol : ℕ)
    (enc : Vector prims.High p.k → BucketVec p) {CL : Type} [Fintype CL] [DecidableEq CL] [Nonempty CL] (L : W1Loop X Y p prims Msg N CL) {RMsg : Type}
    [Fintype RMsg] [DecidableEq RMsg] (bmsg : KeyRing (PubKey p prims) N → RMsg → Msg) :
    BaseSigner X Y N (w1BaseT prims Msg RMsg CL) where
  keyGen := keyGen prims
  bmsg := bmsg
  q := N * reps + (N + L.q)
  bsign sk R i m c := (ringCheckProg prims O βmin tol R).bind fun ok =>
    (muDistinctProg prims O R (bmsg R m)).bind fun ok' =>
      if ok ∧ ok' then L.sign sk R i (bmsg R m) c else .pure none
  bsign_queries sk R i m c := (ringCheckProg_queries prims O βmin tol R).bind fun ok =>
    (muDistinctProg_queries prims O R (bmsg R m)).bind fun ok' => by
      split_ifs
      · exact L.sign_queries _ _ _ _ _
      · exact OracleProg.QueriesLE.pure _ _
  ssign sk bm c := L.std sk bm c
  ssign_queries sk bm c := (L.std_queries sk bm c).mono (by omega)
  bverify H pk bm σ := ringVerify prims (O.hOrc H) enc (pubPk prims pk) bm (w1Of prims enc pk σ) σ
  qPub := 0
  pub pk σ := .pure (w1Of prims enc pk σ)
  pub_queries _ _ := OracleProg.QueriesLE.pure _ _

/-- The public values of the base signer publishing `w₁` are inhabited. -/
instance [NeZero (bucketCount p)] (O : W1Oracles X Y p prims Msg N reps) (βmin : ℚ≥0) (tol : ℕ)
    (enc : Vector prims.High p.k → BucketVec p) {CL : Type} [Fintype CL] [DecidableEq CL] [Nonempty CL] (L : W1Loop X Y p prims Msg N CL) {RMsg : Type}
    [Fintype RMsg] [DecidableEq RMsg] (bmsg : KeyRing (PubKey p prims) N → RMsg → Msg) :
    Inhabited (w1BaseSigner prims O βmin tol enc L bmsg).Pub :=
  inferInstanceAs (Inhabited (BucketVec p))

end MLDSAW1

end GordieHowe.Ring
