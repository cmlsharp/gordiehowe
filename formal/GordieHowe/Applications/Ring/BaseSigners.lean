-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.RingSignature.Base
public import GordieHowe.Applications.Falcon512.Scheme
public import GordieHowe.Applications.Falcon512.Ring.Native.System.Scheme
public import GordieHowe.Applications.Ring.PublicW1.MLDSAPublicW1
public import GordieHowe.Applications.MLDSA.Scheme
public import GordieHowe.Applications.MLDSA.SchemeT0

@[expose] public section

/-!
# The base signers of the library's three ring signatures

The shapes of the three constructions as `RingSignature.BaseSigner`s
(`GordieHowe/Model/RingSignature/Base.lean`), so that each ring signature is
`RingSignature.ofBase B PS adm` for its base signer `B`, its proof system `PS` and its supported
rings `adm`. Their completeness facts are in `GordieHowe/Applications/Ring/BaseSignerFacts.lean`.

- `falconBaseSigner G bmsg`: the Falcon-512 signature scheme `Falcon512.falconBaseScheme G`
  (`GordieHowe/Applications/Falcon512/Scheme.lean`; FIPS 206 / Falcon specification v1.2) with the
  signer `G` (key generation and signing are not specified in Lean). The base signer reads the ring only through `bmsg` (`m`, or `m ‖ encode R`) and never refuses
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
  commitment hash `H(H_µ(tr, m), w₁)` read from the oracle (`MLDSAOracles.hOrc`). The base signer
  reads the ring: it refuses rings failing the public check `sampledRingCheck` against the check
  oracle `G`, which it reads by at most `N · reps` classical queries (`ringCheckProg`,
  `run_ringCheckProg`, `ringCheckProg_queries`), and rings whose members' message representatives
  `µ_j = H_µ(tr_j, m)` are not pairwise distinct (`MuDistinct`, by at most `N` queries:
  `muDistinctProg`, `run_muDistinctProg`, `muDistinctProg_queries`), and otherwise runs the ring
  loop `L.sign` (a parameter `L : W1Loop …`; `GordieHowe/Applications/Ring/MLDSAW1Ring.lean`
  builds the flattened hedged loop). Its ordinary signer is `L.std` (`w1BaseSigner_ssign`).
- `W1Oracles`: the oracles of ML-DSA (`MLDSAOracles`, `Applications/MLDSA/Signing/Oracles.lean`)
  and the check oracle `G` as parts of the one random oracle `X → Y`: their points embedded in `X`
  and their values decoded from `Y` (domain separation);
  `W1Oracles.gameOrc`: the game's oracles `((H_µ, H), G)` of
  `GordieHowe/Applications/Ring/PublicW1/MLDSAPublicW1.lean`.
-/

namespace GordieHowe.Ring

open GordieHowe.RingSignature

variable {X Y : Type} {N : ℕ}

/-! ### Falcon-512 -/

section Falcon

open GordieHowe.Falcon512 (Signer PublicKey falconSchemeT falconBaseScheme)

variable {msgLen : ℕ}


/-- **The Falcon-512 base signer** with the signer `G` and the base message `bmsg` of a ring and a
ring message: the Falcon-512 signature scheme `falconBaseScheme G` signing `bmsg R m` (the ring read
only through `bmsg`). -/
def falconBaseSigner (G : Signer msgLen) {RMsg : Type}
    (bmsg : KeyRing PublicKey N → RMsg → (Fin msgLen → UInt8)) :
    BaseSigner X Y N (falconSchemeT G) RMsg :=
  BaseSigner.ofCore (falconBaseScheme G) bmsg

end Falcon

/-! ### ML-DSA -/

section MLDSA

open _root_.MLDSA GordieHowe.MLDSA LatticeCrypto TransformOps

variable (p : Params) (prims : Primitives p) [nttOps : NTTRingOps]


variable [Fintype prims.Power2High] [DecidableEq prims.Power2High] [Fintype prims.Hint]
  [DecidableEq prims.Hint]

/-- **The ML-DSA base signer of the generic ring** with base messages of `len` bytes: the ML-DSA
signature scheme `mldsaBaseScheme` signing `bmsg R m` (the ring read only through `bmsg`). -/
def mldsaBaseSigner (maxAttempts : ℕ) {len : ℕ} {RMsg : Type}
    (bmsg : KeyRing (PublicKey p prims) N → RMsg → Bytes len) :
    BaseSigner X Y N (mldsaSchemeT p prims len) RMsg :=
  BaseSigner.ofCore (mldsaBaseScheme p prims maxAttempts len) bmsg

end MLDSA

section MLDSAConcrete

open _root_.MLDSA GordieHowe.MLDSA

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

/-- **The oracles of the ring publishing `w₁` inside the one random oracle `X → Y`**: the oracles
of ML-DSA (`MLDSAOracles`) and the check oracle `G(R, j, r)`, its points embedded in `X` and its
values decoded from `Y`. Distinct embeddings are the domain separation of the oracles. -/
structure W1Oracles (X Y : Type) (p : Params) (prims : Primitives p) (Msg : Type) (N reps : ℕ)
    extends MLDSAOracles X Y p Msg where
  /-- The points of the check oracle. -/
  gPt : KeyRing (PubKey p prims) N × Fin N × Fin reps → X
  /-- The values of the check oracle. -/
  gAns : Y → CommitHashBytes p

variable {prims}

/-- The check oracle `G` read from the oracle. -/
def W1Oracles.gOrc (O : W1Oracles X Y p prims Msg N reps) (H : X → Y) :
    CheckOrc p prims N reps :=
  fun pt => O.gAns (H (O.gPt pt))

/-- **The game's oracles** `((H_µ, H), G)` of `MLDSAPublicW1.lean` read from the oracle. -/
def W1Oracles.gameOrc (O : W1Oracles X Y p prims Msg N reps) (H : X → Y) :
    GameOrc prims Msg N reps :=
  ((O.muOrc H, O.chOrc H), O.gOrc H)

variable (prims)

/-- **A ring check as a classical oracle program**: query the check oracle at `(R, j, r)` for
every `j < N` and `r < reps`, then run the test `test` (`RingCheck.adm`) on the ring and the
answers (at most `N · reps` queries, `ringCheckProgOf_queries`). -/
def ringCheckProgOf (O : W1Oracles X Y p prims Msg N reps)
    (test : RingOf (PubKey p prims) N → (Fin N → Fin reps → CommitHashBytes p) → Bool)
    (R : KeyRing (PubKey p prims) N) : OracleProg X Y Bool :=
  (OracleProg.tabulate (fun _ => none) (List.finRange N ×ˢ List.finRange reps)
      fun jr => .query (O.gPt (R, jr.1, jr.2)) fun y => .pure (some y)).mapOutput fun T =>
    test R fun j r => ((T (j, r)).map O.gAns).getD default

omit [NeZero (bucketCount p)] nttOps in
/-- A ring check makes `N · reps` queries. -/
theorem ringCheckProgOf_queries (O : W1Oracles X Y p prims Msg N reps)
    (test : RingOf (PubKey p prims) N → (Fin N → Fin reps → CommitHashBytes p) → Bool)
    (R : KeyRing (PubKey p prims) N) : (ringCheckProgOf prims O test R).QueriesLE (N * reps) :=
  fun h => by
    rw [ringCheckProgOf, OracleProg.trace_mapOutput, OracleProg.length_trace_tabulate]
    simp [List.length_product]

omit [NeZero (bucketCount p)] nttOps in
/-- **A ring check as a program runs the test** at the check oracle read from the oracle. -/
theorem run_ringCheckProgOf (O : W1Oracles X Y p prims Msg N reps)
    (test : RingOf (PubKey p prims) N → (Fin N → Fin reps → CommitHashBytes p) → Bool)
    (R : KeyRing (PubKey p prims) N) (H : X → Y) :
    (ringCheckProgOf prims O test R).run H = test R (fun j r => O.gOrc H (R, j, r)) := by
  simp only [ringCheckProgOf, OracleProg.run_mapOutput, OracleProg.run_tabulate,
    OracleProg.run_query, OracleProg.run_pure, List.mem_product, List.mem_finRange, and_self,
    ite_true, Option.map_some, Option.getD_some]
  rfl

/-- **The public ring check as a classical oracle program**: query the check oracle at
`(R, j, r)` for every `j < N` and `r < reps`, then decide `sampledRingCheck` at the cut-off `β_min`
with tolerance `tol` on the answers (at most `N · reps` queries, `ringCheckProg_queries`). -/
abbrev ringCheckProg (O : W1Oracles X Y p prims Msg N reps) (βmin : ℚ≥0) (tol : ℕ)
    (R : KeyRing (PubKey p prims) N) : OracleProg X Y Bool :=
  ringCheckProgOf prims O (sampledAdm prims (constCut prims βmin) tol) R

omit [NeZero (bucketCount p)] in
/-- The public ring check makes `N · reps` queries. -/
theorem ringCheckProg_queries (O : W1Oracles X Y p prims Msg N reps) (βmin : ℚ≥0) (tol : ℕ)
    (R : KeyRing (PubKey p prims) N) : (ringCheckProg prims O βmin tol R).QueriesLE (N * reps) :=
  ringCheckProgOf_queries prims O _ R

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

/-- **The public ring check decides `sampledRingCheck`** at the check oracle read from the
oracle. -/
theorem run_ringCheckProg (O : W1Oracles X Y p prims Msg N reps) (βmin : ℚ≥0) (tol : ℕ)
    (R : KeyRing (PubKey p prims) N) (H : X → Y) :
    (ringCheckProg prims O βmin tol R).run H = true ↔ sampledRingCheck prims βmin tol (O.gOrc
        H) R := by
  rw [ringCheckProg, run_ringCheckProgOf]
  exact decide_eq_true_iff

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

variable {prims} in
/-- **The ring loop's ordinary signer** at the ring signer's query bound `N · reps + (N + L.q)`
(a base signer has one bound for both signers): `L.std`. -/
def W1Loop.stdSigner {CL : Type} (L : W1Loop X Y p prims Msg N CL) (reps : ℕ) :
    T0Signer X Y p prims Msg CL :=
  ⟨N * reps + (N + L.q), L.std, fun sk m c => (L.std_queries sk m c).mono (by omega)⟩

variable (Msg) in

variable [Fintype prims.Power2High] [DecidableEq prims.Power2High] [Fintype prims.Hint]
  [DecidableEq prims.Hint] [Fintype Msg] [DecidableEq Msg]

/-- **The base signer of the ML-DSA ring publishing `w₁` at a ring check** with the oracles `O`,
the test `test`, the encoding `enc` of recomputed commitments, the ring loop `L` and the base
message `bmsg`: published keys `(ρ, t₁, t₀)` (`keyGen`), base signatures `(c̃, z, h)`, public value
`w₁ = w1Of enc pk σ`. Its ring-aware signer runs the test `test` on the ring's check samples
(`ringCheckProgOf`) and the distinct-µ check (`muDistinctProg`), refuses when either fails, and
otherwise runs `L.sign`; the ordinary signer is `L.std`. Verification is `ringVerify` against the
commitment hash read from the oracle, at the recomputed `w₁`. -/
def w1BaseSignerOf (O : W1Oracles X Y p prims Msg N reps)
    (test : RingOf (PubKey p prims) N → (Fin N → Fin reps → CommitHashBytes p) → Bool)
    (enc : Vector prims.High p.k → BucketVec p) {CL : Type} (L : W1Loop X Y p prims Msg N CL)
    {RMsg : Type} (bmsg : KeyRing (PubKey p prims) N → RMsg → Msg) :
    BaseSigner X Y N (mldsaT0SchemeT prims Msg CL) RMsg :=
  ⟨mldsaT0BaseScheme prims O.toMLDSAOracles enc (L.stdSigner reps), bmsg,
    fun sk R i m c => (ringCheckProgOf prims O test R).bind fun ok =>
      (muDistinctProg prims O R (bmsg R m)).bind fun ok' =>
        if ok ∧ ok' then L.sign sk R i (bmsg R m) c else .pure none,
    fun sk R i m c => (ringCheckProgOf_queries prims O test R).bind fun ok =>
      (muDistinctProg_queries prims O R (bmsg R m)).bind fun ok' => by
        split_ifs
        · exact L.sign_queries _ _ _ _ _
        · exact OracleProg.QueriesLE.pure _ _⟩

/-- **The base signer of the ML-DSA ring publishing `w₁`** with the oracles `O`, the check's
cut-off `β_min` and tolerance `tol`, the encoding `enc` of recomputed commitments, the ring loop `L`
and the base message `bmsg`: published keys `(ρ, t₁, t₀)` (`keyGen`), base signatures `(c̃, z, h)`,
public value `w₁ = w1Of enc pk σ`. The base signer refuses rings failing the public check
(`ringCheckProg`) or whose members' message representatives `µ_j` are not pairwise distinct
(`muDistinctProg`), and otherwise runs `L.sign`; the ordinary signer is `L.std`. Verification is
`ringVerify` against the commitment hash read from the oracle, at the recomputed `w₁`.
`w1BaseSignerOf` at the sampled test of the constant cut-off family. -/
abbrev w1BaseSigner (O : W1Oracles X Y p prims Msg N reps) (βmin : ℚ≥0) (tol : ℕ)
    (enc : Vector prims.High p.k → BucketVec p) {CL : Type} (L : W1Loop X Y p prims Msg N CL)
    {RMsg : Type} (bmsg : KeyRing (PubKey p prims) N → RMsg → Msg) :
    BaseSigner X Y N (mldsaT0SchemeT prims Msg CL) RMsg :=
  w1BaseSignerOf prims O (sampledAdm prims (constCut prims βmin) tol) enc L bmsg

omit [NeZero (bucketCount p)] in
/-- The scheme of the base signer publishing `w₁` at a ring check is ML-DSA with `t₀` published at
the ring loop's ordinary signer. -/
theorem w1BaseSignerOf_core (O : W1Oracles X Y p prims Msg N reps)
    (test : RingOf (PubKey p prims) N → (Fin N → Fin reps → CommitHashBytes p) → Bool)
    (enc : Vector prims.High p.k → BucketVec p) {CL : Type} (L : W1Loop X Y p prims Msg N CL)
    {RMsg : Type} (bmsg : KeyRing (PubKey p prims) N → RMsg → Msg) :
    (w1BaseSignerOf prims O test enc L bmsg).core =
      mldsaT0BaseScheme prims O.toMLDSAOracles enc (L.stdSigner reps) :=
  rfl

/-- The scheme of the base signer publishing `w₁` is ML-DSA with `t₀` published at the ring
loop's ordinary signer. -/
theorem w1BaseSigner_core (O : W1Oracles X Y p prims Msg N reps) (βmin : ℚ≥0) (tol : ℕ)
    (enc : Vector prims.High p.k → BucketVec p) {CL : Type} (L : W1Loop X Y p prims Msg N CL)
    {RMsg : Type} (bmsg : KeyRing (PubKey p prims) N → RMsg → Msg) :
    (w1BaseSigner prims O βmin tol enc L bmsg).core =
      mldsaT0BaseScheme prims O.toMLDSAOracles enc (L.stdSigner reps) :=
  rfl

omit [NeZero (bucketCount p)] in
/-- The ordinary signer of the base signer publishing `w₁` is the ring loop's ordinary signer. -/
theorem w1BaseSigner_ssign (O : W1Oracles X Y p prims Msg N reps) (βmin : ℚ≥0) (tol : ℕ)
    (enc : Vector prims.High p.k → BucketVec p) {CL : Type} [Fintype CL] [DecidableEq CL]
    [Nonempty CL] (L : W1Loop X Y p prims Msg N CL) {RMsg : Type} [Fintype RMsg] [DecidableEq RMsg]
    (bmsg : KeyRing (PubKey p prims) N → RMsg → Msg) (sk : SecretKey p) (bm : Msg) (c : CL) :
    (w1BaseSigner prims O βmin tol enc L bmsg).ssign sk bm c = L.std sk bm c :=
  rfl

/-- The public values of the base signer publishing `w₁` are inhabited. -/
instance [NeZero (bucketCount p)] (O : W1Oracles X Y p prims Msg N reps) (βmin : ℚ≥0) (tol : ℕ)
    (enc : Vector prims.High p.k → BucketVec p) {CL : Type} (L : W1Loop X Y p prims Msg N CL)
    {RMsg : Type} (bmsg : KeyRing (PubKey p prims) N → RMsg → Msg) :
    Inhabited (w1BaseSigner prims O βmin tol enc L bmsg).Pub :=
  inferInstanceAs (Inhabited (BucketVec p))

end MLDSAW1

end GordieHowe.Ring
