-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

import GordieHowe.Applications.Ring.MLDSAW1KeyFreeRoute2

/-! # Scheme types are computed from types data (unbundle M2)

Each test compares two scheme, statement, proof or instance types by `rfl` under a 20000-heartbeat
cap (a cap, not a bump), with `diagnostics` on so the unfolding counts are recorded:
- the public keys of the fresh scheme are `PubKey p prims`, without unfolding `freshScheme`,
  `w1BaseSigner` or the loops;
- the ring statements of the hedged and the fresh base signer are one type;
- the proofs of the fresh scheme's proof system are the spBCS responses;
- the decidable equality of the scheme's keys, as `ofBase` reads it in `List.idxOf`, is the
  instance at `PubKey p prims`.
-/

namespace GordieHoweTest.UnbundleSchemes

open _root_.MLDSA GordieHowe GordieHowe.MLDSA GordieHowe.Ring GordieHowe.Ring.MLDSAW1
open GordieHowe.RingSignature GordieHowe.RingSignature.OracleSplit
open GordieHowe.Quantum GordieHowe.QROM GordieHowe.SPBCS IOP SPTerm GordieHowe.IOP

variable {p : Params} {T : ℕ} {Msg : Type} {N reps : ℕ}
  {kh kN kS L e : ℕ} {I J Y₁ : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  [AddGroup Y₁] [Fintype Y₁] [DecidableEq Y₁] [Nonempty Y₁] {sp : OracleSplit (BitStr I J) Y₁
    (XOut kh e)}
  {prims : Primitives p}
  [NeZero (bucketCount p)] [nttOps : NTTRingOps] [Fintype prims.Power2High]
  [DecidableEq prims.Power2High] [Fintype prims.Hint] [DecidableEq prims.Hint]
  [Nonempty (MaskBox p)] [Fintype Msg] [DecidableEq Msg]
  {O : W1Oracles (Bits (queryBits kh kN kS L)) (BitStr I J) p prims Msg N reps}
  {Mo : MaskOracle (Bits (queryBits kh kN kS L)) (BitStr I J) p T Msg} {βmin : ℚ≥0} {tol : ℕ}
  {enc : Vector prims.High p.k → BucketVec p} {k D : ℕ} [NeZero D] {RMsg : Type} [Fintype RMsg]
  [DecidableEq RMsg] [Nonempty RMsg] [Fintype (BucketVec p)] [Nonempty (BucketVec p)] [Nonempty
    (FIPSSignature p prims)]
  {bmsg : KeyRing (PubKey p prims) N → RMsg → Msg}
  {ι : Type} {τ : SPTerm ι} {Mg : Merges τ} {nr : ι → ℕ}
  {P : (j : ι) → ProtocolSpec (nr j)} [∀ j i, Fintype ((P j).Challenge i)]
  [∀ j i, DecidableEq ((P j).Challenge i)] [∀ j i, Nonempty ((P j).Challenge i)]
  {Mc : SPBCS Mg P (W1ExpStmt prims RMsg N)
    kh kN kS L e}
  {Λ : SiteLayout Mg} {b : ℕ} [∀ j i, Fintype ((Mc.comp j).MessageWrite i)]
  {E : (j : ι) → (Mc.comp j).Encoder}
  {Vr : W1ExpStmt prims RMsg N → FullTr P τ → Bool}
  {Qs : ∀ x, Mc.IOPQueries Vr x} {hb : Mc.FormatBounds Qs b b} {R : Type} [Fintype R] [Nonempty R]
  {honest : RingSignature.RingWit (freshBase prims O Mo βmin tol enc k D bmsg) → R →
    CausalProver P τ (W1ExpStmt prims RMsg N)}
  {adm : KeyRing (PubKey p prims) N → Prop}
  [hadm : DecidablePred adm] {n Q : ℕ} [NeZero n]
  {chk : RingSignature.RingStmt (freshBase prims O Mo βmin tol enc k D bmsg) → Bool}

local notation "Bh" => hedgedBase prims O Mo βmin tol enc k D bmsg
local notation "Bf" => freshBase prims O Mo βmin tol enc k D bmsg
local notation "PSh" => w1HPS sp prims O Mo βmin tol enc k D bmsg Mc Λ E hb honest chk
local notation "PSf" => PSh
local notation "Sf" => freshScheme prims O Mo βmin tol enc k D bmsg PSh adm

set_option diagnostics true

set_option maxHeartbeats 20000 in
/-- The fresh scheme's public keys are the published ML-DSA keys. -/
example : (Sf).PK = PubKey p prims := rfl

set_option maxHeartbeats 20000 in
/-- The same, at reducible transparency. -/
example : (Sf).PK = PubKey p prims := by with_reducible rfl

set_option maxHeartbeats 20000 in
/-- The hedged and the fresh base signer have one ring-statement type. -/
example : RingSignature.RingStmt (Bh) = RingSignature.RingStmt (Bf) := rfl

set_option maxHeartbeats 20000 in
/-- The same, at reducible transparency. -/
example : RingSignature.RingStmt (Bh) = RingSignature.RingStmt (Bf) := by with_reducible rfl

set_option maxHeartbeats 20000 in
/-- The hedged and the fresh base signer have one ring-witness type. -/
example : RingSignature.RingWitOf (FIPSSignature p prims) = RingSignature.RingWitOf (FIPSSignature p prims) := by with_reducible rfl

set_option maxHeartbeats 20000 in
/-- The proofs of the fresh scheme's proof system are the spBCS responses in the format `b`. -/
example : (PSf).Proof = Mc.Response b := rfl

set_option maxHeartbeats 20000 in
/-- The same, at reducible transparency. -/
example : (PSf).Proof = Mc.Response b := by with_reducible rfl

set_option maxHeartbeats 20000 in
/-- The key equality `ofBase` reads (the types record's instance) is the one at `PubKey p prims`,
so `List.idxOf` at the scheme's keys is `List.idxOf` at `PubKey p prims`. -/
example : @List.idxOf (Sf).PK (@instBEqOfDecidableEq _ (RingTypes.instDecEqPK _)) =
    @List.idxOf (PubKey p prims) instBEqOfDecidableEq := rfl

set_option maxHeartbeats 20000 in
/-- The same, at reducible transparency. -/
example : @List.idxOf (Sf).PK (@instBEqOfDecidableEq _ (RingTypes.instDecEqPK _)) =
    @List.idxOf (PubKey p prims) instBEqOfDecidableEq := by with_reducible rfl

end GordieHoweTest.UnbundleSchemes
