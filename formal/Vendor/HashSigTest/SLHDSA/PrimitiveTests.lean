/-
Copyright (c) 2026 Nicolas Consigny, Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolas Consigny, Alexander Hicks

Adapted from VCVio HashSigTest/SLHDSA/PrimitiveTests.lean at commit
eb0f6e456a8dffee6a0ba8a2f66ca2a5b50dfd79.
adapted: this file is not a verbatim copy. It keeps only the pure SHAKE128 /
SHAKE256 / SHA3 / Keccak-256 known-answer checks from the source file's
`testShake` (and the hex helpers `hexValue`, `parseHex`, `ensure`, `checkHex`
it uses), inlining their expected-output literals. The source file's
`testSha2`, `testHmacAndMgf`, `testAddressAndProfiles`, `testProjection`, and
the FIPS-205 per-profile fingerprints depend on `HashSig.SLHDSA.Concrete.FIPS`
(SHA-2, HMAC, MGF1, `Adrs`, the twelve approved parameter sets) and on reading
`HashSigTest/SLHDSA/PrimitiveVectors/vectors.json` from disk; neither that
module nor that data file is vendored here (see `Vendor/README.md`), so those
checks are left out. The `#eval` at the bottom is new: it is what actually
runs the checks, replacing the source repository's separate test-runner
executable. This file also drops the `module`/`public import`/`public section`
module-system markers the source repository uses: `lake build` (and even bare
`lean`) on a `module` file whose body contains a top-level `#eval` fails here
with "Could not find native implementation of external declaration" the first
time it reaches an imported module's function, because module files evaluate
`#eval` against native code rather than the bytecode interpreter; a plain
`import` file uses the interpreter instead and has no such problem. Every
other vendored file keeps its `module`/`public import` markers unchanged,
since none of them use `#eval`.
-/

import HashSig.SLHDSA.Concrete.Keccak

/-!
# SHAKE / SHA3 / Keccak-256 known-answer checks

Runtime checks for the FIPS 202 SHAKE128, SHAKE256, SHA3-224/384/512 test
vectors, plus the domain-separation checks that SHAKE, SHA-3, and Ethereum's
Keccak-256 disagree on the same input. All are pure and executable: no
network, no filesystem, no FFI.
-/

namespace HashSigTest.SLHDSA.PrimitiveTests

open SLHDSA.Concrete.Keccak

private def hexValue (c : Char) : UInt8 :=
  if '0' ≤ c ∧ c ≤ '9' then (c.toNat - '0'.toNat).toUInt8
  else if 'a' ≤ c ∧ c ≤ 'f' then (c.toNat - 'a'.toNat + 10).toUInt8
  else if 'A' ≤ c ∧ c ≤ 'F' then (c.toNat - 'A'.toNat + 10).toUInt8
  else 0

private def parseHex (hex : String) : ByteArray := Id.run do
  let chars := hex.toList.toArray
  let mut out := ByteArray.empty
  for i in [0:chars.size / 2] do
    out := out.push (hexValue chars[2 * i]! <<< 4 ||| hexValue chars[2 * i + 1]!)
  return out

private def ensure (label : String) (condition : Bool) : IO Unit :=
  unless condition do throw (IO.userError s!"SHAKE/SHA3 KAT failed: {label}")

private def checkHex (label : String) (actual : ByteArray) (expected : String) : IO Unit :=
  ensure label (actual == parseHex expected)

private def shakeEmpty272Expected : String :=
  "46b9dd2b0ba88d13233b3feb743eeb243fcd52ea62b81b82b50c27646ed5762fd75dc4dd\
    d8c0f200cb05019d67b592f6fc821c49479ab48640292eacb3b7c4be141e96616fb13957\
    692cc7edd0b45ae3dc07223c8e92937bef84bc0eab862853349ec75546f58fb7c2775c38\
    462c5010d846c185c15111e595522a6bcd16cf86f3d122109e3b1fdd943b6aec468a2d6\
    21a7c06c6a957c62b54dafc3be87567d677231395f6147293b68ceab7a9e0c58d864e8e\
    fde4e1b9a46cbe854713672f5caaae314ed9083dab4b099f8e300f01b8650f1f4b1d8f\
    cf3f3cb53fb8e9eb2ea203bdc970f50ae55428a91f7f53ac266b28419c3778a15fd248\
    d339ede785fb7f5a1aaa96d313eacc890936c173cdcd0f"

def testShake : IO Unit := do
  checkHex "SHA3-224 abc" (sha3_224 "abc".toUTF8)
    "e642824c3f8cf24ad09234ee7d3c766fc9a3a5168d0c94ad73b46fdf"
  checkHex "SHA3-224 exact-rate padding"
    (sha3_224 (ByteArray.mk (Array.replicate 144 0x61)))
    "f9019111996dcf160e284e320fd6d8825cabcd41a5ffdc4c5e9d64b6"
  checkHex "SHA3-384 abc" (sha3_384 "abc".toUTF8)
    "ec01498288516fc926459f58e2c6ad8df9b473cb0fc08c2596da7cf0e49be4b\
      298d88cea927ac7f539f1edf228376d25"
  checkHex "SHA3-384 exact-rate padding"
    (sha3_384 (ByteArray.mk (Array.replicate 104 0x61)))
    "3a4f3b6284e571238884e95655e8c8a60e068e4059a9734abc08823a900d1615\
      92860243f00619ae699a29092ed91a16"
  checkHex "SHA3-512 abc" (sha3_512 "abc".toUTF8)
    "b751850b1a57168a5693cd924b6b096e08f621827444f70d884f5d0240d2712e\
      10e116e9192af3c91a7ec57647e3934057340b4cf408d5a56592f8274eec53f0"
  checkHex "SHA3-512 exact-rate padding"
    (sha3_512 (ByteArray.mk (Array.replicate 72 0x61)))
    "a8ae722a78e10cbbc413886c02eb5b369a03f6560084aff566bd597bb7ad8c1c\
      cd86e81296852359bf2faddb5153c0a7445722987875e74287adac21adebe952"
  checkHex "SHAKE128 abc 32" (shake128 "abc".toUTF8 32)
    "5881092dd818bf5cf8a3ddb793fbcba74097d5c526a6d35f97b83351940f2cc8"
  checkHex "SHAKE128 exact-rate padding"
    (shake128 (ByteArray.mk (Array.replicate 168 0x61)) 32)
    "c22e11586c22b713bde373fce93314d76829de2c21d940a28eb659b8dec953a2"
  checkHex "SHAKE128 multi-block squeeze 200" (shake128 ByteArray.empty 200)
    "7f9c2ba4e88f827d616045507605853ed73b8093f6efbc88eb1a6eacfa66ef263cb1eea\
      988004b93103cfb0aeefd2a686e01fa4a58e8a3639ca8a1e3f9ae57e235b8cc873c23d\
      c62b8d260169afa2f75ab916a58d974918835d25e6a435085b2badfd6dfaac359a5efbb\
      7bcc4b59d538df9a04302e10c8bc1cbf1a0b3a5120ea17cda7cfad765f5623474d368c\
      cca8af0007cd9f5e4c849f167a580b14aabdefaee7eef47cb0fca9767be1fda69419dfb\
      927e9df07348b196691abaeb580b32def58538b8d23f877"
  checkHex "SHAKE256 empty 32"
    (shake256 ByteArray.empty 32)
    "46b9dd2b0ba88d13233b3feb743eeb243fcd52ea62b81b82b50c27646ed5762f"
  let empty137 :=
    "46b9dd2b0ba88d13233b3feb743eeb243fcd52ea62b81b82b50c27646ed5762fd75dc4dd\
      d8c0f200cb05019d67b592f6fc821c49479ab48640292eacb3b7c4be141e96616fb13957\
      692cc7edd0b45ae3dc07223c8e92937bef84bc0eab862853349ec75546f58fb7c2775c38\
      462c5010d846c185c15111e595522a6bcd16cf86f3d122109e3b1fdd94"
  checkHex "SHAKE256 squeeze 135" (shake256 ByteArray.empty 135)
    (empty137.take (2 * 135)).toString
  checkHex "SHAKE256 squeeze 136" (shake256 ByteArray.empty 136)
    (empty137.take (2 * 136)).toString
  checkHex "SHAKE256 squeeze 137 rate crossing" (shake256 ByteArray.empty 137) empty137
  checkHex "SHAKE256 squeeze 272 two blocks" (shake256 ByteArray.empty 272)
    shakeEmpty272Expected
  checkHex "SHAKE256 1600-bit absorb"
    (shake256 (ByteArray.mk (Array.replicate 200 0xa3)) 64)
    "cd8a920ed141aa0407a22d59288652e9d9f1a7ee0c1e7c1ca699424da84a904d2d700caae\
      7396ece96604440577da4f3aa22aeb8857f961c4cd8e06f0ae6610b"
  checkHex "SHAKE256 absorb 135"
    (shake256 (ByteArray.mk (Array.replicate 135 0x61)) 32)
    "55b991ece1e567b6e7c2c714444dd201cd51f4f3832d08e1d26bebc63e07a3d7"
  checkHex "SHAKE256 absorb 136"
    (shake256 (ByteArray.mk (Array.replicate 136 0x61)) 32)
    "8fcc5a08f0a1f6827c9cf64ee8d16e0443106359ca6c8efd230759256f44996a"
  checkHex "SHAKE256 absorb 137"
    (shake256 (ByteArray.mk (Array.replicate 137 0x61)) 32)
    "a44e1a438dad6273d540be65ee26386c59588efb09139dc086385d2db0c25782"
  ensure "SHAKE domain differs from SHA3" (shake256 ByteArray.empty 32 != sha3_256 ByteArray.empty)
  ensure "SHAKE domain differs from Ethereum Keccak"
    (shake256 ByteArray.empty 32 != keccak256 ByteArray.empty)

end HashSigTest.SLHDSA.PrimitiveTests

-- Running this `#eval` at elaboration time is the check: `testShake` throws
-- `IO.userError` on the first mismatch, which fails elaboration.
#eval HashSigTest.SLHDSA.PrimitiveTests.testShake
