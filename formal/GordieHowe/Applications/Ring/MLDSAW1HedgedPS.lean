-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Ring.MLDSAW1KeyFreeRoute2
public import GordieHowe.Applications.Ring.MLDSAW1EmptyRing

@[expose] public section

/-!
# The hedged proof system of the key-free chain is the spBCS proof system of the ring

The statements and witnesses of the ring relation depend only on the base signer's key, message,
public-value and signature types (`RingStmtOf`, `RingWitOf`), and these do not depend on the loop.
So an spBCS argument `Sc` compiled for the program statements of the hedged base signer also
serves the fresh base signer, and the proof system `w1HPS` of the key-free chain at `Sc` is the
proof system of the ring scheme.

- `w1HPS_eq_w1PS`: at the check `fun _ => true`, `w1HPS` is `w1PS`.
- `w1HPS_eq_w1PSNonempty`: at the check of a nonempty ring, `w1HPS` is `w1PSNonempty`.
-/

namespace GordieHowe.Ring.MLDSAW1

open _root_.MLDSA GordieHowe.MLDSA GordieHowe.RingSignature GordieHowe.RingSignature.OracleSplit
open GordieHowe.Signature Quantum GordieHowe.QROM GordieHowe.SPBCS IOP SPTerm GordieHowe.IOP

variable {p : Params} {T : ℕ} {Msg : Type} {N reps : ℕ}
  {kh kN kS L e : ℕ} {Y Y₁ : Type} [AddGroup Y] [AddGroup Y₁] [Fintype Y] [DecidableEq Y]
  [Nonempty Y] (sp : OracleSplit Y Y₁ (XOut kh e))
  (prims : Primitives p)
  [NeZero (bucketCount p)] [nttOps : NTTRingOps] [Fintype prims.Power2High]
  [DecidableEq prims.Power2High] [Fintype prims.Hint] [DecidableEq prims.Hint]
  [Nonempty (MaskBox p)] [Fintype Msg] [DecidableEq Msg]
  (O : W1Oracles (Bits (queryBits kh kN kS L)) Y p prims Msg N reps)
  (Mo : MaskOracle (Bits (queryBits kh kN kS L)) Y p T Msg) (βmin : ℚ≥0) (tol : ℕ)
  (enc : Vector prims.High p.k → BucketVec p) (k D : ℕ) [NeZero D] {RMsg : Type} [Fintype RMsg]
  [DecidableEq RMsg] (bmsg : KeyRing (PubKey p prims) N → RMsg → Msg)
  {ι : Type} {τ : SPTerm ι} {Mg : Merges τ} {nr : ι → ℕ}
  {P : (j : ι) → ProtocolSpec (nr j)} [∀ j i, Fintype ((P j).Challenge i)]
  [∀ j i, DecidableEq ((P j).Challenge i)] [∀ j i, Nonempty ((P j).Challenge i)]
  (Sc : SPBCS Mg P (W1ExpStmt prims RMsg N)
    kh kN kS L e)
  (Λ : SiteLayout Mg) {b : ℕ} [∀ j i, Fintype ((Sc.comp j).MessageWrite i)]
  (E : (j : ι) → (Sc.comp j).Encoder)
  {Vr : W1ExpStmt prims RMsg N → FullTr P τ → Bool}
  {Qs : ∀ x, Sc.IOPQueries Vr x} (hb : Sc.FormatBounds Qs b b) {R : Type} [Fintype R]
  [Nonempty R]
  (honest : RingSignature.RingWit (hedgedBase prims O Mo βmin tol enc k D bmsg) → R →
    CausalProver P τ (W1ExpStmt prims RMsg N))

/-- **At every ring statement checked, the hedged proof system of the key-free chain is the
spBCS proof system of the ring**: `w1HPS` at `Sc` and the check `fun _ => true` is `w1PS`. -/
theorem w1HPS_eq_w1PS :
    w1HPS sp prims O Mo βmin tol enc k D bmsg Sc Λ E hb honest (fun _ => true) =
      w1PS sp prims O βmin tol enc (hedgedLoop prims O Mo βmin k D) bmsg Sc Λ E hb honest :=
  rfl

/-- **At the nonempty rings checked, the hedged proof system of the key-free chain is the spBCS
proof system of the ring rejecting the empty ring**: `w1HPS` at `Sc` and the check of a
nonempty ring is `w1PSNonempty`. -/
theorem w1HPS_eq_w1PSNonempty :
    w1HPS sp prims O Mo βmin tol enc k D bmsg Sc Λ E hb honest
        (fun x => decide (x.ring.1 ≠ [])) =
      w1PSNonempty sp prims O βmin tol enc (hedgedLoop prims O Mo βmin k D) bmsg Sc Λ E hb
        honest :=
  rfl

end GordieHowe.Ring.MLDSAW1
