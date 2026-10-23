/-
New file: not from VCVio. Instantiates the abstract `MLDSA.Primitives` record
(`Vendor/LatticeCrypto/MLDSA/Primitives.lean`, vendored verbatim from VCVio) with
executable hash/XOF-based primitives, built from the vendored `SLHDSA.Concrete.Keccak.shake128`
/ `shake256` and from VCVio's own executable `MLDSA.Concrete` pieces (NTT, rounding,
encoding), so that `MLDSA.fipsVerify` becomes a closed, executable function.

Faithfully implemented, against FIPS 204 (Module-Lattice-Based Digital Signature Standard):

- `expandA`      — Algorithm 32 (`ExpandA`), via the rejection-sampled NTT-domain coefficients
                    of Algorithm 30 (`RejNTTPoly`).
- `sampleInBall` — Algorithm 29 (`SampleInBall`).
- `hashMessage`  — `μ = H(tr ‖ M′, 64)`.
- `hashCommitment` — `c̃ = H(μ ‖ w1Encode(w₁), λ/4)`.
- `hashPublicKey`  — `tr = H(pkEncode(ρ, t₁), 64)`.
- `expandSeed`     — `(ρ, ρ′, K) = H(ξ ‖ IntegerToBytes(k,1) ‖ IntegerToBytes(l,1), 128)`.
- `hashPrivateSeed` — `ρ″ = H(K ‖ rnd ‖ μ, 64)`.

`expandS` and `expandMask` are signing-only fields of `Primitives`; `fipsVerify` never reads
them (see `Vendor/LatticeCrypto/MLDSA/Verify.lean`, which does not even parameterize over
them — the full `Primitives` record is only needed here because `fipsVerify` is stated
against it). They are given placeholder all-zero implementations below, clearly marked, purely
so `Primitives` can be instantiated; nothing in this file relies on them being spec-faithful.

Both rejection-sampling loops (`ExpandA`, `SampleInBall`) are standards specified as "squeeze
the XOF until enough candidates are accepted." Since the vendored `shake128`/`shake256` take a
fixed output length, each loop instead squeezes a generous fixed number of bytes up front and
walks it; the exact budget is documented at each definition. On exhaustion both
return `none` and `verify` rejects; `ExpandA`'s budget is
768 candidates (2304 SHAKE128 bytes) per polynomial, above the FIPS 204 Appendix C minimum of 298
iterations (894 bytes) for a bounded `RejNTTPoly`. The fixed-length XOF-stream variants that a circuit
would actually use (a single absorb, one giant squeeze, no data-dependent restart) live outside
this vendored code, in the owning `PQ/Spec/*` files.

No known-answer test vectors were available to check `expandA`, `sampleInBall`, `hashMessage`,
`hashCommitment`, or `hashPublicKey` against (ML-DSA ACVP vectors require the FFI-backed
reference implementation, which is out of scope here; see `Vendor/README.md`). What is checked,
in `LatticeCryptoTest/MLDSA/ConcretePrimitivesTests.lean`, is internal to this file's own
output: `sampleInBall` produces exactly `τ` coefficients in `{-1, 0, 1}` for every approved
parameter set, and `expandA` produces a `k × l` matrix. Byte-level fidelity to FIPS 204 is
NOT independently verified; treat these primitives as unverified until checked against ACVP.
-/

module

public import LatticeCrypto.MLDSA.Verify
public import LatticeCrypto.MLDSA.Concrete.NTT
public import LatticeCrypto.MLDSA.Concrete.Rounding
public import LatticeCrypto.MLDSA.Concrete.Encoding
public import HashSig.SLHDSA.Concrete.Keccak

@[expose] public section

namespace MLDSA.Concrete

open MLDSA
open SLHDSA.Concrete.Keccak

/-! ## Byte/XOF plumbing -/

/-- Absorb a `List Byte` and squeeze `outLen` bytes with SHAKE256. -/
def shake256List (input : List Byte) (outLen : ℕ) : ByteArray :=
  shake256 (ByteArray.mk input.toArray) outLen

/-- Absorb a `ByteArray` and squeeze `outLen` bytes with SHAKE128. -/
def shake128Bytes (input : ByteArray) (outLen : ℕ) : ByteArray :=
  shake128 input outLen

/-! ## `ExpandA` (Algorithm 32) -/

/-- Decode one little-endian 3-byte candidate into a coefficient, masking the top bit of the
third byte (giving a 23-bit value) and rejecting values `≥ q`, per the `SampleNTT` /
`RejNTTPoly` procedure Algorithm 32 calls. -/
def decodeCoeffLE3 (b0 b1 b2 : UInt8) : Option Coeff :=
  let d := b0.toNat + 256 * b1.toNat + 65536 * (b2.toNat &&& 0x7F)
  if d < modulus then some (d : Coeff) else none

/-- The number of 3-byte candidates `expandAPoly?` draws before rejecting: 768 (2304 SHAKE128
bytes). FIPS 204 Appendix C says implementations should not bound `RejNTTPoly`, and a bounded
one must allow at least 298 iterations (894 XOF bytes); this definition must terminate, so it
takes a budget above that minimum. Each candidate is accepted with probability
`q / 2^23 ≈ 0.9990`, so the expected number of candidates needed is about 256.3, and needing more
than 768 (at least 513 rejections among 768 candidates) has probability about `2^-4431` per
polynomial under the random-oracle reading. -/
def expandACandidateBudget : ℕ := 768

/-- One entry `Â[i][j]` of `ExpandA(ρ)` (Algorithm 32) with a bounded candidate stream:
SHAKE128 on `ρ ‖ j ‖ i` (the column byte before the row byte, matching the reference
`(i << 8) + j` little-endian nonce), rejection sampled into 256 NTT-domain coefficients, or
`none` if the `expandACandidateBudget` 3-byte candidates hold fewer than 256 acceptances.
Algorithm 32 squeezes until 256 are accepted, and the C++ reference squeezes without a bound;
this definition rejects at the keys the budget cannot expand. -/
def expandAPoly? (rho : Bytes 32) (row col : ℕ) : Option Tq :=
  let seed := vectorToByteArray rho ++ ByteArray.mk #[col.toUInt8, row.toUInt8]
  let stream := shake128Bytes seed (3 * expandACandidateBudget)
  let coeffs := Id.run do
    let mut out : Array Coeff := #[]
    let mut cursor := 0
    while out.size < ringDegree ∧ cursor + 3 ≤ stream.size do
      match decodeCoeffLE3 stream[cursor]! stream[cursor + 1]! stream[cursor + 2]! with
      | some c => out := out.push c
      | none => pure ()
      cursor := cursor + 3
    return out
  if coeffs.size < ringDegree then none
  else some (LatticeCrypto.TransformPoly.ofPoly (Vector.ofFn fun i : Fin ringDegree => coeffs[i]!))

/-- The total entry the `Primitives` record needs: `expandAPoly?`, and `0` where it rejects.
`verify` checks `expandA?` succeeds, so it never reads the `0`. -/
def expandAPoly (rho : Bytes 32) (row col : ℕ) : Tq :=
  (expandAPoly? rho row col).getD 0

/-- `ExpandA(ρ)` (Algorithm 32): the `k × l` matrix of NTT-domain polynomials, total
(`expandAPoly`). -/
def expandA (p : Params) (rho : Bytes 32) : TqMatrix p.k p.l :=
  Vector.ofFn fun i : Fin p.k => Vector.ofFn fun j : Fin p.l => expandAPoly rho i.val j.val

/-- `ExpandA(ρ)` (Algorithm 32) with bounded candidate streams: the matrix `expandA p ρ` when
every entry's `expandAPoly?` succeeds, `none` otherwise. -/
def expandA? (p : Params) (rho : Bytes 32) : Option (TqMatrix p.k p.l) :=
  if ∀ i : Fin p.k, ∀ j : Fin p.l, (expandAPoly? rho i.val j.val).isSome then some (expandA p rho)
  else none

/-! ## `SampleInBall` (Algorithm 29) -/

/-- The number of candidate bytes `sampleInBallPoly?` squeezes (beyond the 8 sign bytes) before
rejecting: `264`, so the stream is `272` SHAKE256 bytes, two blocks. Adapted:
VCVio's value is `256`; `264` is the candidate range of the C++ circuit
(`lib/gordiehowe/examples/mldsa_hash.h`, `kSibBytes = 272`), above the FIPS 204 Appendix C minimum of `221` bytes for a
bounded SampleInBall. `τ ≤ 60` positions each need a candidate `j ≤ i` with `i ≥ 256 - τ ≥ 196`,
so each candidate is accepted with probability `≥ 197/256 ≈ 0.77`, and running out is negligible
(expected candidates needed `≤ 60 / 0.77 ≈ 78`). -/
def sampleInBallCandidateBudget : ℕ := 264

/-- Starting from `cursor`, find the next candidate byte `≤ i`, trying at most `fuel` bytes:
the accepted value and the cursor just past it, or `none` if the candidates or the fuel run out
first. Algorithm 29 squeezes until a candidate is accepted; a bounded implementation rejects
instead. -/
def sampleInBallFindAccepted (candidates : Array UInt8) (i : ℕ) : ℕ → ℕ → Option (ℕ × ℕ)
  | _, 0 => none
  | cursor, fuel + 1 =>
    match candidates[cursor]? with
    | none => none
    | some b =>
      if b.toNat ≤ i then some (b.toNat, cursor + 1)
      else sampleInBallFindAccepted candidates i (cursor + 1) fuel

/-- One placement of Algorithm 29 at the write index `i`: find the next accepted candidate `j`
and execute `c[i] := c[j]; c[j] := ±1` with the sign of placement `i - start`; `none` once a
search has failed. The state is the coefficient array and the candidate cursor. -/
def sampleInBallStep (candidates : Array UInt8) (start : ℕ) (signBit : ℕ → Bool)
    (s : Option (Array Coeff × ℕ)) (i : ℕ) : Option (Array Coeff × ℕ) :=
  s.bind fun st => (sampleInBallFindAccepted candidates i st.2 candidates.size).map fun r =>
    ((st.1.set! i st.1[r.1]!).set! r.1 (if signBit (i - start) then (-1 : Coeff) else 1), r.2)

/-- `SampleInBall(ρ̃)` (Algorithm 29) with a bounded candidate stream: derive the weight-`τ`
challenge polynomial with coefficients in `{-1, 0, 1}` from the commitment hash, or `none` if the
`sampleInBallCandidateBudget` candidates run out. Reads the `τ` sign bits from the first 8
squeezed bytes, little-endian (bit `k` of byte `k / 8`), then walks the following candidates one
byte per position with the Algorithm 29 rejection `j > i` (`sampleInBallStep`). -/
def sampleInBallPoly? (p : Params) (cTilde : CommitHashBytes p) : Option Rq :=
  let stream := shake256List (byteArrayToList (vectorToByteArray cTilde)) (8 + sampleInBallCandidateBudget)
  let signBytes := stream.extract 0 8
  let candidates := stream.extract 8 (8 + sampleInBallCandidateBudget)
  let signBit (k : ℕ) : Bool := ((signBytes[k / 8]! >>> (k % 8).toUInt8) &&& 1) == 1
  let start := ringDegree - p.tau
  ((List.range' start p.tau).foldl (sampleInBallStep candidates.data start signBit)
      (some (Array.replicate ringDegree 0, 0))).map
    fun st => Vector.ofFn fun i : Fin ringDegree => st.1[i]!

/-- The total `SampleInBall` the `Primitives` record needs: `sampleInBallPoly?`, and `0` where it
rejects. `verify` checks `sampleInBallPoly?` succeeds, so it never reads the `0`. -/
def sampleInBallPoly (p : Params) (cTilde : CommitHashBytes p) : Rq :=
  (sampleInBallPoly? p cTilde).getD 0

/-! ## Message and commitment hashing -/

/-- `μ = H(tr ‖ M′, 64)`. -/
def hashMessage (tr : Bytes 64) (msg : List Byte) : Bytes 64 :=
  byteArrayToVector (shake256List (byteArrayToList (vectorToByteArray tr) ++ msg) 64) 0 64

/-- `c̃ = H(μ ‖ w1Encode(w₁), λ/4)`. -/
def hashCommitment (p : Params) (mu : Bytes 64) (w1Encoded : List Byte) : CommitHashBytes p :=
  byteArrayToVector
    (shake256List (byteArrayToList (vectorToByteArray mu) ++ w1Encoded) (p.lambda / 4))
    0 (p.lambda / 4)

/-- `tr = H(pkEncode(ρ, t₁), 64)`. -/
def hashPublicKey (p : Params) (rho : Bytes 32) (t1 : Vector Power2High p.k) : Bytes 64 :=
  byteArrayToVector (shake256 (pkEncode p rho t1) 64) 0 64

/-- `(ρ, ρ′, K) = H(ξ ‖ IntegerToBytes(k,1) ‖ IntegerToBytes(l,1), 128)`, used by key generation.
Not read by `fipsVerify`; implemented faithfully anyway since it is a single hash call. -/
def expandSeed (p : Params) (seed : Bytes 32) : Bytes 32 × Bytes 64 × Bytes 32 :=
  let out := shake256List (byteArrayToList (vectorToByteArray seed) ++ [p.k.toUInt8, p.l.toUInt8]) 128
  (byteArrayToVector out 0 32, byteArrayToVector out 32 64, byteArrayToVector out 96 32)

/-- `ρ″ = H(K ‖ rnd ‖ μ, 64)`, used by signing. Not read by `fipsVerify`; implemented faithfully
anyway since it is a single hash call. -/
def hashPrivateSeed (key rnd : Bytes 32) (mu : Bytes 64) : Bytes 64 :=
  byteArrayToVector
    (shake256List
      (byteArrayToList (vectorToByteArray key) ++ byteArrayToList (vectorToByteArray rnd) ++
        byteArrayToList (vectorToByteArray mu)) 64)
    0 64

/-! ## Signing-only placeholders

`expandS` (Algorithm 33) and `expandMask` (Algorithm 34) are needed only by `fipsSign`, which is
not vendored (see `Vendor/LatticeCrypto/MLDSA/Verify.lean`). `fipsVerify` never calls them; they
are given trivial all-zero bodies purely so `Primitives` can be instantiated. -/

/-- Placeholder, not spec-faithful: `fipsVerify` never reads this field. -/
def expandS (p : Params) (_rhoPrime : Bytes 64) : RqVec p.l × RqVec p.k :=
  (Vector.replicate p.l 0, Vector.replicate p.k 0)

/-- Placeholder, not spec-faithful: `fipsVerify` never reads this field. -/
def expandMask (p : Params) (_rhoDoublePrime : Bytes 64) (_kappa : ℕ) : RqVec p.l :=
  Vector.replicate p.l 0

/-- Lift `MLDSA.Concrete.hintWeight` (the weight of one polynomial's hint bits) to the
`Primitives.hintWeight` field's shape: the total weight across a length-`k` hint vector. -/
def hintWeightVec {k : ℕ} (h : Vector Hint k) : ℕ :=
  (h.toList.map hintWeight).sum

/-! ## The instantiated `Primitives` record -/

/-- Concrete, executable `MLDSA.Primitives` for a given approved parameter set, built from the
vendored SHAKE128/SHAKE256 and the FIPS 204 algorithms above, reusing VCVio's executable
`MLDSA.Concrete` rounding, hint, and encoding operations for everything else. -/
def concretePrimitives (p : Params) : Primitives p where
  High := High
  Power2High := Power2High
  Hint := Hint
  expandSeed := expandSeed p
  expandA := expandA p
  expandS := expandS p
  expandMask := expandMask p
  sampleInBall := sampleInBallPoly p
  hashMessage := hashMessage
  hashPrivateSeed := hashPrivateSeed
  hashCommitment := hashCommitment p
  hashPublicKey := hashPublicKey p
  highBits := highBits p
  highBitsShift := highBitsShift p
  lowBits := lowBits p
  makeHint := makeHint p
  useHint := useHint p
  power2Round := power2Round
  power2RoundShift := power2RoundShift
  w1Encode := w1Encode p
  hintWeight := hintWeightVec

/-- `MLDSA.fipsVerify`, closed over the concrete primitives and the concrete NTT, for a given
approved parameter set, rejecting when the bounded `ExpandA` (`expandA?`) or the bounded
`SampleInBall` (`sampleInBallPoly?`) runs out of candidates. -/
def verify (p : Params) (pk : PublicKey p (concretePrimitives p)) (msg : List Byte)
    (sig : FIPSSignature p (concretePrimitives p)) : Bool :=
  (expandA? p pk.rho).isSome && (sampleInBallPoly? p sig.cTilde).isSome &&
    fipsVerify p (concretePrimitives p) pk msg sig (nttOps := concreteNTTRingOps)

/-- `MLDSA.fipsVerify` specialized to ML-DSA-44. -/
def verify44 (pk : PublicKey mldsa44 (concretePrimitives mldsa44)) (msg : List Byte)
    (sig : FIPSSignature mldsa44 (concretePrimitives mldsa44)) : Bool :=
  verify mldsa44 pk msg sig

/-- `MLDSA.fipsVerify` specialized to ML-DSA-65. -/
def verify65 (pk : PublicKey mldsa65 (concretePrimitives mldsa65)) (msg : List Byte)
    (sig : FIPSSignature mldsa65 (concretePrimitives mldsa65)) : Bool :=
  verify mldsa65 pk msg sig

/-- `MLDSA.fipsVerify` specialized to ML-DSA-87. -/
def verify87 (pk : PublicKey mldsa87 (concretePrimitives mldsa87)) (msg : List Byte)
    (sig : FIPSSignature mldsa87 (concretePrimitives mldsa87)) : Bool :=
  verify mldsa87 pk msg sig

end MLDSA.Concrete
