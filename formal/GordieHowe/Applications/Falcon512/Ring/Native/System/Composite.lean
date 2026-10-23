-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Falcon512.Ring.Native.System.Algebra
public import GordieHowe.Foundations.Probability.RangeGroups
public import GordieHowe.Applications.Falcon512.Native.System.Source
public import GordieHowe.Applications.Falcon512.Ring.Native.System.Params
public import GordieHowe.Language.Realizations.Lowering
public import GordieHowe.Language.Realizations.Bits
public import GordieHowe.Foundations.Probability.ChallengeEventCount

@[expose] public section

/-!
# Falcon ring, native arm: the statement and the relation

* **The statement**: the ring statement of `GordieHowe/Applications/Ring/Scheme.lean` at Falcon-512 with the signer `G`
  (`scheme G`): a ring of public keys, an `msgLen`-byte message and the salt `r`, with the base
  message `m` (`bindMsg`: `bind R m = m`). The C++ statement is the ring and
  `c = HashToPoint(r ‖ m)` (`falcon_ring.h:5-6`); the Lean verifier computes `c` from the statement
  (`stmtChallenge`, `stmtChallenge_lt`, `ofCoeff_stmtChallenge`: the vendored hash-to-point with
  the empty verification-key string) and reads the ring's keys by position (`ringKey`,
  `ringKey_eq`).
* **The honest algebra facts** (`honestAlgebra_of_mem`): a pair of the ring relation gives
  Falcon's algebraic verifier on the statement's challenge and the decompressed signature
  polynomial (`witnessS2`), and the encoding bounds (`HonestAlgebra`).
* **The core witness** (`CoreWit`: the position and the integer `s2`): a lowering's projection reads
  no statement, so the system extracts the core witness and the signature is encoded with the
  statement's salt (`CoreWit.withSalt`).
-/

namespace GordieHowe.Falcon512.Ring.Native

open IOP RealizedProgram.ProofSystem.PhaseLayout GordieHowe.Ring Params
open GordieHowe.Falcon512.Native (Committed)
open scoped NNReal

variable {msgLen : ℕ}

/-! ### The statement and the relation -/

variable (G : Signer msgLen)

/-- **The base message of a ring message**: the message itself (converted signatures). -/
abbrev bindMsg : List PublicKey → (Fin msgLen → UInt8) → (Fin msgLen → UInt8) := fun _ m => m

variable {G}

/-- **The key at a position of the ring** (the default key past the end). -/
def ringKey {N : ℕ} (x : RingStmt (scheme G) (Fin msgLen → UInt8) N) (j : ℕ) : PublicKey := x.ring.1.getD j (default : PublicKey)

theorem ringKey_eq {N : ℕ} {x : RingStmt (scheme G) (Fin msgLen → UInt8) N} {j : ℕ} (hj : j < x.ring.1.length) : ringKey x j = x.ring.1[j]'hj := by
  unfold ringKey
  simp [hj]

/-- **The challenge coefficients of a statement**: the coefficients of `HashToPoint(r ‖ m)` as
naturals below `q` (zero if the hash fails). -/
def stmtChallenge {N : ℕ} (x : RingStmt (scheme G) (Fin msgLen → UInt8) N) :
    Fin falcon512.n → ℕ :=
  match ringChallenge x.pub x.msg with
  | some c => fun i => (Falcon512.coeff c i).val
  | none => 0

/-- The challenge coefficients are below `q`. -/
theorem stmtChallenge_lt {N : ℕ} (x : RingStmt (scheme G) (Fin msgLen → UInt8) N)
    (i : Fin falcon512.n) : stmtChallenge x i < 12289 := by
  cases h : ringChallenge x.pub x.msg with
  | some c => simp only [stmtChallenge, h]; exact ZMod.val_lt _
  | none => simp only [stmtChallenge, h, Pi.zero_apply]; decide

/-- On a successful hash, the challenge polynomial is the polynomial of the coefficients. -/
theorem ofCoeff_stmtChallenge {N : ℕ} {x : RingStmt (scheme G) (Fin msgLen → UInt8) N} {c : _root_.Falcon.Rq falcon512.n}
    (hc : ringChallenge x.pub x.msg = some c) :
    Falcon512.ofCoeff (fun i => (stmtChallenge x i : _root_.Falcon.Coeff)) = c := by
  have h1 : Falcon512.coeff c = fun i => (stmtChallenge x i : _root_.Falcon.Coeff) := by
    funext i
    simp only [stmtChallenge, hc]
    exact (ZMod.natCast_zmod_val _).symm
  rw [← h1, Falcon512.ofCoeff_coeff]

/-- **The signature polynomial of a ring witness**: the decompressed `s2` (zero if decompression
fails).

Running time: the vendored `decompress` on `625` bytes. This running time is argued here, not proved
in Lean. -/
-- spec-side
def witnessS2 (w : RingWit (scheme G)) : _root_.Falcon.IntPoly 512 :=
  (GordieHowe.Falcon512.prims512.decompress w.sig.1.compressedS2 _root_.Falcon.Concrete.params512.sbytelen).getD 0

/-- **A pair of the ring relation gives the honest algebra facts** at any ring size and admissible
rings: the signature decompresses to `s2` (`witnessS2`), the hash-to-point succeeds and is the
statement's challenge, and Falcon's algebraic verifier holds; decompression gives the encoding
bounds. -/
theorem honestAlgebra_of_mem {N : ℕ} {adm : List PublicKey → Prop}
    {x : RingStmt (scheme G) (Fin msgLen → UInt8) N} {w : RingWit (scheme G)}
    (hw : (x, w) ∈ GordieHowe.Ring.ringRel adm bindMsg) :
    HonestAlgebra (ringKey x w.idx) (stmtChallenge x) (witnessS2 w) ∧
      (ringChallenge x.pub x.msg).isSome = true := by
  obtain ⟨-, hrel⟩ := hw
  have hver : GordieHowe.Falcon512.verify (x.ring.1[w.idx]'hrel.idx_lt) (List.ofFn x.msg) w.sig.1 :=
    verifySig_eq_true_iff.mp hrel.verify_eq
  obtain ⟨s, c, hd, hc, ha⟩ := (GordieHowe.Falcon512.verify_iff_algebraOk _ _ _).mp hver
  have hpub : w.sig.1.salt = x.pub := hrel.pub_eq
  have hc' : ringChallenge x.pub x.msg = some c := by
    rw [← hpub, ← hashToPoint_eq_ringChallenge _
      (GordieHowe.Falcon512.prims512.publicKeyBytes (x.ring.1[w.idx]'hrel.idx_lt).h)]
    exact hc
  have hs : witnessS2 w = s := by
    unfold witnessS2
    rw [hd]
    rfl
  rw [ringKey_eq hrel.idx_lt, hs]
  refine ⟨⟨?_, ?_⟩, by rw [hc']; rfl⟩
  · rw [ofCoeff_stmtChallenge hc']
    exact ha
  · exact GordieHowe.Falcon512.decompress_success_encodingBounds hd

/-- **The core witness**: the signer's position and the integer `s2`. -/
@[ext] structure CoreWit where
  /-- The position of the signer's key in the ring. -/
  idx : ℕ
  /-- The signature polynomial, centered. -/
  s2 : _root_.Falcon.IntPoly 512

instance : Inhabited CoreWit := ⟨⟨0, Vector.replicate 512 0⟩⟩

/-- **The ring witness of a core witness** at the salt `r`: the position and the signature encoded
from `r` and `s2` (`extractSig`). -/
def CoreWit.withSalt (w : CoreWit) (r : Salt) : RingWit (scheme G) := ⟨w.idx, extractSig r w.s2⟩

end GordieHowe.Falcon512.Ring.Native
