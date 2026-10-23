/-
New file: not from VCVio. Instantiates the `Falcon.VerifyPrimitives` record
(`Vendor/LatticeCrypto/Falcon/Verify.lean`, itself adapted from VCVio's `Falcon.Primitives` —
see that file's header) with executable primitives, built from the vendored
`SLHDSA.Concrete.Keccak.shake256` and VCVio's own executable `Falcon.Concrete` encoding
(`publicKeyBytes`, `decompress`), so that `Falcon.verify` becomes a closed, executable function.

`hashToPoint` implements Falcon specification v1.2, Algorithm 3 (`HashToPoint`), extended with
the FIPS 206 draft's "raw-message" binding to the verification-key bytes (`vrfyKey`), matching
what `VerifyPrimitives.hashToPoint`'s docstring (copied from VCVio's `Primitives.hashToPoint`)
documents: absorb `salt ‖ vrfyKey ‖ msg` with SHAKE256, then squeeze 16-bit big-endian samples,
accepting each that is `< 5q = 61445` and reducing it mod `q`, until `n` coefficients are
accepted. The classic (non-FIPS-206) Algorithm 3 omits `vrfyKey` from the absorbed input
(`SHAKE256(salt ‖ msg)`); both share the same sampling loop.

The rejection loop is a standard specified as "squeeze the XOF until `n` candidates are
accepted." Since the vendored `shake256` takes a fixed output length, it instead squeezes a
generous fixed number of candidates up front and walks them; if the budget is exhausted before
`n` are accepted (probability negligible; see `hashToPointCandidateBudget`), it returns `none`
and `Falcon.verify` rejects. The fixed-length XOF-stream variant a circuit would actually use lives
outside this vendored code, in the owning `PQ/Spec/*` files.

No known-answer test vectors were available to check `hashToPoint` against (Falcon test vectors
require the FFI-backed reference implementation, out of scope here; see `Vendor/README.md`).
`LatticeCryptoTest/Falcon/ConcretePrimitivesTests.lean` checks only that its output has the
right degree and that every coefficient is a valid `ZMod q` value (true by construction) and
that distinct inputs give distinct outputs on a handful of samples. Byte-level fidelity to the
standard is NOT independently verified; treat this primitive as unverified until checked
against a KAT.
-/

module

public import LatticeCrypto.Falcon.Verify
public import LatticeCrypto.Falcon.Concrete.Encoding
public import HashSig.SLHDSA.Concrete.Keccak

@[expose] public section

namespace Falcon.Concrete

open Falcon
open SLHDSA.Concrete.Keccak

/-- The number of 2-byte candidates `hashToPoint` draws before giving up and returning `none`. Each candidate is accepted with probability `5q / 2^16 ≈ 0.9377`, so the
expected number of candidates needed for `n` coefficients is about `1.067 n`; `1.5 n + 256`
candidates make running out negligible for both `n = 512` and `n = 1024`. -/
def hashToPointCandidateBudget (n : ℕ) : ℕ := n + n / 2 + 256

/-- `HashToPoint(salt, vrfyKey, msg)` (Falcon specification v1.2, Algorithm 3, extended with the
FIPS 206 draft's verification-key binding — see the file header): absorb `salt ‖ vrfyKey ‖ msg`
with SHAKE256, then rejection-sample `n` coefficients from 16-bit big-endian candidates, each
accepted iff `< 5q` and reduced mod `q`; `none` if `hashToPointCandidateBudget n` candidates
hold fewer than `n` acceptances. -/
def hashToPoint (n : ℕ) (salt : Falcon.Bytes 40) (vrfyKey : ByteArray) (msg : List Byte) :
    Option (Rq n) :=
  let input := ByteArray.mk salt.toArray ++ vrfyKey ++ ByteArray.mk msg.toArray
  let budget := hashToPointCandidateBudget n
  let stream := shake256 input (2 * budget)
  let coeffs := Id.run do
    let mut out : Array Falcon.Coeff := #[]
    let mut cursor := 0
    while out.size < n ∧ cursor + 2 ≤ stream.size do
      let d := (stream[cursor]!.toNat <<< 8) + stream[cursor + 1]!.toNat
      if d < 5 * modulus then
        out := out.push ((d % modulus : ℕ) : Falcon.Coeff)
      cursor := cursor + 2
    return out
  if coeffs.size < n then none else some (Vector.ofFn fun i : Fin n => coeffs[i]!)

/-- The primitives `Falcon.verify` needs, concretely: `hashToPoint` above, VCVio's executable
`publicKeyBytes` (public-key header plus packed 14-bit coefficients), and its executable
`decompress` (Golomb-Rice signature decoding, Algorithm 18). -/
def concretePrimitives (p : Params) : VerifyPrimitives p where
  publicKeyBytes h := Falcon.Concrete.publicKeyBytes p.logn h
  hashToPoint salt vrfyKey msg := hashToPoint p.n salt vrfyKey msg
  decompress bytes dlen := Falcon.Concrete.decompress p.n bytes dlen

/-- `Falcon.verify`, closed over the concrete primitives, for a given approved parameter set. -/
def verify (p : Params) (pk : PublicKey p) (msg : List Byte) (sig : Signature) : Bool :=
  Falcon.verify p (concretePrimitives p) pk msg sig

/-- A computable stand-in for `Falcon.falcon512`, carrying only the fields `Falcon.verify`
reads: `n`, `betaSquared`, `sbytelen`. `verify` never reads `sigma`/`sigmaMin` (those govern
the signing-side Gaussian sampler), so they are set to `0` here rather than to
`Falcon.falcon512`'s real-valued constants, which involve real division and so are
`noncomputable`; using them here would make `verify512` noncomputable too, defeating the point
of closing `verify` into an executable function. -/
def params512 : Params where
  n := 512
  sigma := 0
  sigmaMin := 0
  betaSquared := 34034726
  sbytelen := 625

/-- A computable stand-in for `Falcon.falcon1024`; see `params512`. -/
def params1024 : Params where
  n := 1024
  sigma := 0
  sigmaMin := 0
  betaSquared := 70265242
  sbytelen := 1239

/-- `Falcon.verify` specialized to Falcon-512 (see `params512` for why this does not use
`Falcon.falcon512` directly). -/
def verify512 (pk : PublicKey params512) (msg : List Byte) (sig : Signature) : Bool :=
  verify params512 pk msg sig

/-- `Falcon.verify` specialized to Falcon-1024 (see `params512` for why this does not use
`Falcon.falcon1024` directly). -/
def verify1024 (pk : PublicKey params1024) (msg : List Byte) (sig : Signature) : Bool :=
  verify params1024 pk msg sig

end Falcon.Concrete
