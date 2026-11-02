# Vendored specifications and coding-theory proofs

Pure-Lean specifications of ML-DSA verification, Falcon verification, the negacyclic ring with
NTT, and SHAKE256, vendored from [VCVio](https://github.com/Verified-zkEVM/VCVio) (Apache-2.0) so they
build here with Mathlib as the only dependency.

- Source repository: <https://github.com/Verified-zkEVM/VCVio>
- Source commit: `eb0f6e456a8dffee6a0ba8a2f66ca2a5b50dfd79` (Tue Sep 22 06:13:24 2026 +0000)
- Vendored on: 2026-09-22
- Toolchain: `leanprover/lean4:v4.34.0`, same Mathlib commit as this package
  (`5ed2965256430c3649e86755f9576b54eca72435`), pinned in `../lakefile.toml`.
- `Vendor/VCVio-LICENSE` is VCVio's Apache-2.0 `LICENSE` file, copied verbatim.

Every copied file, edited or not, carries a one-line provenance comment naming its VCVio source
path and this commit; edited files additionally say `adapted: <what>`. This document expands on
those comments file by file.

## Build

```
lake build LatticeCrypto HashSig HashSigTest LatticeCryptoTest
```

builds cleanly (2379 jobs, no `sorry`, no `axiom`, no `native_decide`, anywhere in `Vendor/`), and
runs both known-answer test suites and both structural sanity-check suites (output reproduced
under "Test results" below). No target under `Vendor/` compiles anything under
`.lake/packages/mathlib`: Mathlib comes from the cache (`lake exe cache get`).

Root aggregator files `Vendor/LatticeCrypto.lean`, `Vendor/HashSig.lean`,
`Vendor/HashSigTest.lean`, `Vendor/LatticeCryptoTest.lean` are new (not from VCVio): each just
`import`s every module under its namespace, mirroring `../GordieHowe.lean`'s role for `GordieHowe`, and is what
lets `lake build LatticeCrypto` (the bare library target) succeed instead of only individual
module targets.

## Lake / module-system notes

VCVio's files use Lean's `module` keyword with `public import` and `@[expose] public section`.
These build unchanged in this non-module package — `lake build` accepted every vendored file
with `module`/`public import` intact, no stripping needed — **except** for the two test files
(`Vendor/HashSigTest/SLHDSA/PrimitiveTests.lean`,
`Vendor/LatticeCryptoTest/{MLDSA,Falcon}/ConcretePrimitivesTests.lean`), each of which has a
top-level `#eval` of an `IO Unit` action. A `module` file with a top-level `#eval` failed both
under `lake build` and under bare `lake env lean <file>` with:

```
libc++abi: terminating due to uncaught exception of type lean::exception: Could not find native
implementation of external declaration '...'
```

— module files evaluate `#eval` against native code rather than the bytecode interpreter, and
the imported module's native code was not yet loaded. Dropping `module`/`public import`/
`public section` for a plain `import`/`section` (still importing the exact same modules) fixed
this: plain-import files evaluate `#eval` with the interpreter and have no such problem. No other
vendored file uses `#eval`, so no other file needed this change. This is recorded in each of
those three files' own header comment too.

Two files (`LatticeCrypto/MLDSA/Params.lean`, `LatticeCrypto/Falcon/Params.lean`) and
`HashSig/SLHDSA/Concrete/Keccak.lean` imported only `VCVio.OracleComp.Constructions.SampleableType`
(or, for `Keccak.lean`, `HashSig.SLHDSA.Params`) without using anything from it — the import was
vestigial, there transitively for Mathlib's `ℕ`/`ZMod` notation rather than for its own content.
Dropping it and importing the actual notation source directly (`Mathlib.Data.Nat.Notation`, plus
`Mathlib.Data.ZMod.Basic` for `Params.lean` and `Mathlib.Analysis.SpecialFunctions.Pow.NNReal`
for `Falcon/Params.lean`) fixed the resulting "unknown identifier `ℕ`" errors. `MLDSA/Arithmetic.lean`
and `Falcon/Arithmetic.lean` similarly imported `LatticeCrypto.Ring.Sampling` without using
anything from it; dropped with no replacement needed (nothing in either file needed the dropped
import for anything, unlike the `Params.lean` case).

## What was copied, file by file

### `LatticeCrypto/Ring/*` — the negacyclic ring, NTT-agnostic layer

Copied unmodified (provenance comment only): `Core.lean`, `VectorBackend.lean`, `Kernel.lean`,
`SchoolbookCert.lean`, `Transform.lean`, `NTTCert.lean`, `Norms.lean`, `Rounding.lean`,
`IntegralLift.lean`.

Not copied:
- `Sampling.lean` — imports `VCVio.OracleComp.Constructions.SampleableType` for real (its whole
  content is `SampleableType` instances for uniform sampling on ring carriers); this is
  monadic/probabilistic and out of scope for a pure spec.
- `Smoke.lean` — a compile-only smoke test that imports `LatticeCrypto.MLKEM.Arithmetic`, which
  is not vendored (out of scope: only ML-DSA and Falcon are vendored). Its role — checking the
  generic ring layer instantiates — is already exercised by `LatticeCrypto/MLDSA/Arithmetic.lean`
  and `LatticeCrypto/Falcon/Arithmetic.lean` building successfully.

### `LatticeCrypto/MLDSA/*` — ML-DSA (FIPS 204)

Copied unmodified: `Primitives.lean`, `Encoding.lean`,
`Concrete/Rounding.lean`, `Concrete/Encoding.lean`, `Concrete/LawBounds.lean`.

Copied with edits: `Params.lean` (dropped vestigial import, added the two replacements above),
`Arithmetic.lean` (dropped vestigial `Ring.Sampling` import), `Concrete/NTT.lean` (module
docstring only: VCVio's caveat that no theorem relates the `@[implemented_by]` loop kernels
`loopNTT`, `loopInvNTT`, `loopMultiplyNTTs` to the structural `ntt`, `invNTT`, `multiplyNTTs` is
replaced by the names of the theorems in `GordieHowe/Applications/MLDSA44/Spec/NTTLoop.lean`
that prove each pair equal).

Not copied in the first pass: `Scheme.lean`, `Signature.lean`, `Security.lean`,
`SecurityHVZK.lean`, `SecurityNMA.lean`; the pure parts needed for verification were extracted into
`Verify.lean` (below). `Scheme.lean` and `Signature.lean` were added later; see "ML-DSA key
generation and signing" below. `Security.lean`, `SecurityHVZK.lean` and `SecurityNMA.lean` are not
copied.

**New file** `Verify.lean`: not a straight copy of any one VCVio file. Collects the pure,
non-monadic declarations `fipsVerify` depends on, taken from `Scheme.lean` (`PublicKey`,
`computeWApprox`) and `Signature.lean` (`FIPSSignature`, `fipsVerify` itself), each copied
verbatim from its source; left out are `SecretKey`, `SigningState`, `Commitment`, `Response`,
`validKeyPair`, `identificationScheme`, `keyGenFromSeed`, the monadic `fipsSign`/`fipsKeyGen`, and
every correctness theorem about signing — none of which `fipsVerify` needs. The file's own header
records this precisely.

**New file** `ConcretePrimitives.lean`: instantiates `Primitives p` with
SHAKE-based primitives — see "Concrete primitives" below.

### `LatticeCrypto/Falcon/*` — Falcon

Copied unmodified: `Concrete/NTT.lean`, `Concrete/SmallPrimeNTT.lean`, `Concrete/Encoding.lean`.

Copied with edits: `Params.lean`, `Arithmetic.lean` (same vestigial-import pattern as ML-DSA's).

Not copied: `Primitives.lean`, recorded here because it
matters. Unlike ML-DSA's `Primitives.lean` (a pure interface record), Falcon's `Primitives.lean`
is fundamentally about **signing**: it defines `ffSampling`, `FalconTree`, `splitFFT`/`mergeFFT`,
and the field `samplerZ : ℝ → ℝ → ProbComp ℤ` where `ProbComp := OracleComp unifSpec` — genuinely
monadic, plus it imports `LatticeCrypto.DiscreteGaussian` (real-analysis discrete Gaussian PMF)
and `Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic`. None of this is used by
`Falcon.verify` (confirmed by reading `Scheme.lean`'s `verify`, reproduced below). `Encoding.lean`
was also not copied as its own file: it only imports `Falcon.Primitives` for the `Rq`/`IntPoly`
types it references, and is not used by `verify` either (`verify` decompresses via `prims.decompress`
directly, never through the abstract `Encoding` structure); with `Primitives.lean` out of scope,
copying it would have meant re-pointing its import for a structure `Falcon.verify` never uses
regardless.

**New file** `Verify.lean`: takes `Falcon.verify`, `PublicKey`, `Signature` verbatim from
`Scheme.lean`, and in place of `Primitives p` declares `VerifyPrimitives`, a new structure with
exactly the three fields `verify` actually reads off `Primitives`
(`publicKeyBytes`, `hashToPoint`, `decompress`) plus `hashToPointForPublicKey` specialized to it.
The file's header records this precisely; `Falcon.verify`'s body is unchanged (`Primitives p`
replaced by `VerifyPrimitives p` throughout, and `Primitives.hashToPointForPublicKey` likewise).

Not copied (out of scope for verification): `Coset.lean`,
`PackedFFT.lean`, `SamplerMinEntropy.lean`, `Security.lean`, `Concrete/{BigInt31,FloatLike,FPR,
FXR,GMTable,NTRUSolver,PolyBigInt}.lean`.

**New file** `ConcretePrimitives.lean`: instantiates `VerifyPrimitives p`
with a SHAKE256-based `HashToPoint` — see "Concrete primitives" below.

### `HashSig/SLHDSA/Concrete/Keccak.lean` — SHAKE128/SHAKE256/SHA-3/Keccak-256

Copied with one edit: dropped the vestigial `import HashSig.SLHDSA.Params` (nothing in the file
refers to any `SLHDSA.Params` declaration), replaced by `import Mathlib.Data.Nat.Notation` for
the `ℕ` notation it had pulled in transitively. `HashSig/SLHDSA/Params.lean` itself was **not**
copied — nothing in `Keccak.lean` needs it, confirming the import was vestigial.

### `HashSigTest/SLHDSA/PrimitiveTests.lean` — known-answer tests

Not copied wholesale: the source file also exercises SHA-2, HMAC, MGF1, `Adrs`, and the twelve
approved FIPS 205 parameter-set fingerprints, all via `HashSig.SLHDSA.Concrete.FIPS` (not
vendored: SLH-DSA verification is out of scope) and a JSON test-vector
file read from disk (`HashSigTest/SLHDSA/PrimitiveVectors/vectors.json`, also not vendored).

**New file** `Vendor/HashSigTest/SLHDSA/PrimitiveTests.lean` keeps only the pure SHAKE128 /
SHAKE256 / SHA3-224/384/512 / Keccak-256 known-answer checks from the source file's `testShake`
(plus the small hex/`ensure`/`checkHex` helpers it uses), with their expected-output literals
inlined instead of read from the JSON file, and drops `module`/`public import`/`public section`
for the `#eval`-under-`module` reason above.

### `LatticeCryptoTest/{MLDSA,Falcon,Ring}/*` — not copied

Surveyed but not copied. `LatticeCryptoTest/MLDSA/{Helpers,Main,ACVPVectors}.lean` and
`LatticeCryptoTest/Falcon/{Helpers,Main,TestVectors,SamplerMinEntropy}.lean` all import from
`Extern.{MLDSA,Falcon}.*` (FFI bindings to the reference C implementations) to cross-check the
Lean spec against them; only pure, non-FFI vectors are vendored, and none of these
qualify — every ML-DSA/Falcon test vector in VCVio is checked by running it through the FFI
reference implementation, not against inlined literals. `LatticeCryptoTest/Ring/*` (`CenteredRepr.lean`,
`VectorAPI.lean`) are pure `decide`-based lemma sanity gates on the ring layer, not ML-DSA/Falcon
test vectors, so they are out of scope.

## ML-DSA key generation and signing

Vendored 2026-10-23 from VCVio commit `eb0f6e456a8dffee6a0ba8a2f66ca2a5b50dfd79`, the commit of the
ML-DSA files above: `LatticeCrypto/MLDSA/Scheme.lean` and `LatticeCrypto/MLDSA/Signature.lean`, the
only two files added. VCVio's head at the time (`f3df0ac18aa5ae72b3e920ad5460492aa039b4f7`) changes
these two files only in docstrings and imports; its imports move to a measure-based probability
API that changes 28 of the 54 VCVio/`ToMathlib` files the Johnson MCA subset shares (pinned at
VCVio `d7089e46`, which `eb0f6e45` leaves unchanged) and needs Lean v4.35.0.

- `Scheme.lean` keeps `SecretKey`, `keyGenFromSeed`, `validKeyPair`, `validKeyPairShort` and the
  key-generation lemmas. Dropped: `PublicKey` and `computeWApprox` (identical copies are in
  `Verify.lean`, imported in place of `Primitives`); `identificationScheme` and
  `identificationSchemeShort`, with the import `VCVio.CryptoFoundations.IdenSchemeWithAbort` that
  only they need and the types `SigningState`, `Commitment`, `Response` that only they use. The
  reason: their commitment samples the mask `y` uniformly over all of `R_q^l`, not over the
  FIPS 204 mask range `[-γ₁+1, γ₁]` (ExpandMask, Algorithm 34), so they model a different scheme.
  `VCVio.OracleComp.Constructions.SampleableType` is replaced by its already-vendored
  `SampleableType.Basic` (the kept declarations sample only `Bytes 32`). The module docstring is
  shortened to the kept content.
- `Signature.lean` keeps `fipsKeyGen`, `fipsSignAttempt`, `fipsSignLoop`, `fipsSign`, the hint
  lemmas and `fipsSign_fipsVerify_correct'` / `fipsSign_fipsVerify_correct`. Dropped:
  `FIPSSignature` and `fipsVerify` (identical copies are in `Verify.lean`).

Not copied: `LearningWithErrors.lean` would add 40 more files (through
`VCVio.CryptoFoundations.HardnessAssumptions.NoisyLearning`). `Vendor/LatticeCrypto.lean` imports
the two new modules. `lake build LatticeCrypto` builds (2829 jobs), and `#print axioms` on
`MLDSA.fipsSign_fipsVerify_correct` reports only `propext`, `Classical.choice`, `Quot.sound`.

## Concrete primitives

`Vendor/LatticeCrypto/MLDSA/ConcretePrimitives.lean` and
`Vendor/LatticeCrypto/Falcon/ConcretePrimitives.lean` are new files (not from VCVio) instantiating the
primitive records with concrete hash functions. Full rationale, budgets, and citations are in their own header comments and
docstrings; summary:

- **ML-DSA** `MLDSA.Concrete.concretePrimitives (p : Params) : Primitives p` — `expandA`
  (Algorithm 32, SHAKE128, rejection-sampled 3-byte little-endian candidates, budget 768 per
  entry (2304 SHAKE128 bytes, above the FIPS 204 Appendix C minimum of 298 iterations for a bounded
  `RejNTTPoly`; FIPS 204 and the C++ reference are unbounded); `expandA?` returns `none` on exhaustion and `verify` rejects), `sampleInBall` (Algorithm 29, SHAKE256, 8 sign bytes + budget-264 one-byte candidates (272 bytes, the C++ `kSibBytes`; adapted from VCVio's 256),
  `j > i` rejection), `hashMessage`, `hashCommitment`, `hashPublicKey`, `expandSeed`,
  `hashPrivateSeed` all via SHAKE256; `highBits`/`lowBits`/`makeHint`/`useHint`/`power2Round`/
  `power2RoundShift`/`w1Encode`/`hintWeight` reuse VCVio's own executable `MLDSA.Concrete`
  definitions unchanged. `expandS` and `expandMask` (signing-only fields `fipsVerify` never
  reads) are explicit all-zero placeholders, clearly marked as such — not spec-faithful, and not
  meant to be. `MLDSA.Concrete.verify44`/`verify65`/`verify87` close `fipsVerify` into an
  executable `Bool` function at each approved parameter set.
- **Falcon** `Falcon.Concrete.concretePrimitives (p : Params) : VerifyPrimitives p` —
  `hashToPoint` (Algorithm 3, extended with the FIPS 206 draft's verification-key binding per
  `VerifyPrimitives.hashToPoint`'s own docstring: SHAKE256(salt ‖ vrfyKey ‖ msg), 16-bit
  big-endian candidates, accept `< 5q = 61445`, reduce mod `q`, budget `1.5n + 256`);
  `publicKeyBytes`/`decompress` reuse VCVio's executable `Falcon.Concrete.publicKeyBytes`/
  `decompress` unchanged. `Falcon.Concrete.verify512`/`verify1024` close `Falcon.verify` into an
  executable `Bool` function. These use new computable parameter records `params512`/`params1024`
  (same `n`/`betaSquared`/`sbytelen` as VCVio's `Falcon.falcon512`/`falcon1024`, but `sigma`/
  `sigmaMin` set to `0` instead of VCVio's real-division values) because `falcon512`/`falcon1024`
  are `noncomputable` (real division has no computable inverse) and `verify` never reads
  `sigma`/`sigmaMin` in the first place (those govern the signing-side Gaussian sampler).

Both rejection loops are specified as "squeeze the XOF until enough candidates are accepted."
Since the vendored `shake128`/`shake256` take a fixed output length, both instead squeeze a
generous fixed number of bytes up front and walk them, falling back (documented, probability
negligible, never observed in testing) if the budget is exhausted; the exact budgets and fallback
behavior are documented at each definition. **The fixed-length XOF-stream variants a circuit
would actually use (a single absorb, one giant squeeze, no data-dependent restart) live outside
this vendored code**, in the `Spec/` directories of `GordieHowe/Applications/` (for example
`GordieHowe/Applications/MLDSA44/Spec/`).

**Important caveat, stated plainly**: the vendored test libraries contain no known-answer test
vectors for `expandA`, `sampleInBall`, `hashMessage`, `hashCommitment`, `hashPublicKey`, or
Falcon's `hashToPoint` — ML-DSA ACVP vectors and Falcon's test vectors both require the FFI-backed
reference implementation (`Extern.*`), deliberately out of scope here (see "not copied" above).
The ML-DSA primitives are checked against known answers outside `Vendor/`, in `Test/` (see "ML-DSA
known-answer tests" under "Test results"); Falcon's `hashToPoint` is not. What the vendored tests
check — reported fully under "Test results" — is internal structural consistency: `sampleInBall`'s output always has exactly `τ` nonzero coefficients in `{-1, 1}`
(checked at all three ML-DSA parameter sets, several inputs each); `expandA`'s output always has
the right matrix shape; `hashToPoint`'s output always has all `n` coefficients determined (no
budget exhaustion) and differs on distinct salts/messages (checked at both Falcon parameter
sets, several inputs each). These structural checks are not a claim of byte-level fidelity to
FIPS 204 or the Falcon specification; for ML-DSA, the known-answer tests of `Test/` are. Falcon's
`hashToPoint` remains unchecked against known answers.

## Test results

### SHAKE128/SHAKE256/SHA3-224/384/512/Keccak-256 known-answer tests

`lake build HashSigTest.SLHDSA.PrimitiveTests` (also runnable directly via
`lake env lean Vendor/HashSigTest/SLHDSA/PrimitiveTests.lean`): **all checks pass**, no output
(the `#eval` only prints on failure, via `IO.userError`, which would fail the build). Covers:
SHA3-224/384/512 (`abc` and exact-rate-padding vectors), SHAKE128 (`abc`, exact-rate padding,
200-byte multi-block squeeze), SHAKE256 (empty input at several output lengths including a
rate-crossing 137-byte squeeze and a two-block 272-byte squeeze, absorbing 135/136/137-byte
inputs, a full 1600-bit/200-byte absorb), and that SHAKE256 disagrees with both SHA3-256 and
Ethereum Keccak-256 on the same input (domain separation).

### `MLDSA.Concrete.ConcretePrimitives` structural checks

`lake build LatticeCryptoTest.MLDSA.ConcretePrimitivesTests`:

```
SampleInBall weight/coefficient checks:
  ok: mldsa44 seed=0 (weight 39 = τ = 39)
  ok: mldsa44 seed=1 (weight 39 = τ = 39)
  ok: mldsa44 seed=127 (weight 39 = τ = 39)
  ok: mldsa44 seed=255 (weight 39 = τ = 39)
  ok: mldsa65 seed=0 (weight 49 = τ = 49)
  ok: mldsa65 seed=1 (weight 49 = τ = 49)
  ok: mldsa65 seed=127 (weight 49 = τ = 49)
  ok: mldsa65 seed=255 (weight 49 = τ = 49)
  ok: mldsa87 seed=0 (weight 60 = τ = 60)
  ok: mldsa87 seed=1 (weight 60 = τ = 60)
  ok: mldsa87 seed=127 (weight 60 = τ = 60)
  ok: mldsa87 seed=255 (weight 60 = τ = 60)

ExpandA shape checks:
  ok: mldsa44 (4 × 4 matrix)
  ok: mldsa65 (6 × 5 matrix)
  ok: mldsa87 (8 × 7 matrix)
```

### ML-DSA known-answer tests (`Test/GordieHoweTest/`)

`scripts/lake.sh build GordieHoweTest` runs `Test/GordieHoweTest/MLDSAVectors.lean`, which checks
the vendored ML-DSA specification against known answers: `expandA` at ML-DSA-44 and ML-DSA-65 and
`sampleInBall` at ML-DSA-44 against the vectors of the C++ reference implementation, `verify44`
against an ML-DSA-44 signature made by OpenSSL, and `verify65` against an ML-DSA-65 example
signature from the C++ tests, each with its flipped-byte rejection (the signature is rejected
after one message byte is flipped):

```
(a) ExpandA (ML-DSA-44) vs kExpectedExpandAVectors[4][4][256]:
PASS ExpandA44

(b) SampleInBall (ML-DSA-44) vs the 10 GetSampleInBallTests() vectors:
PASS SampleInBall44

(c) verify44 vs the ML-DSA-44 benchmark (message, pk, ctx, sig) fixture, positive and negative (flipped message byte):
  ok: Verify44 positive (verify44 pk M' sig = true)
  ok: Verify44 negative (flipped message byte correctly rejected)
PASS Verify44

(d) ExpandA (ML-DSA-65) vs kExpectedExpandAVectors[6][5][256]:
PASS ExpandA65

(d) verify65 vs the first GetMlDsa65Examples() (message, pk, ctx, sig) fixture, positive and negative (flipped message byte):
  ok: Verify65 positive (verify65 pk M' sig = true)
  ok: Verify65 negative (flipped message byte correctly rejected)
PASS Verify65

(e) Falcon hashToPoint / verify512: SKIPPED, no known-answer vectors exist in the C++ Falcon tests (see this file's header).

ALL CHECKS PASSED
```

### `Falcon.Concrete.ConcretePrimitives` structural checks

`lake build LatticeCryptoTest.Falcon.ConcretePrimitivesTests`:

```
HashToPoint determinacy checks:
  ok: n=512 salt=0 msg=[] (0 zero coefficients out of 512)
  ok: n=512 salt=1 msg=[1,2,3] (0 zero coefficients out of 512)
  ok: n=512 salt=0xff msg=long (0 zero coefficients out of 512)
  ok: n=1024 salt=0 msg=[] (0 zero coefficients out of 1024)
  ok: n=1024 salt=1 msg=[1,2,3] (0 zero coefficients out of 1024)
  ok: n=1024 salt=0xff msg=long (0 zero coefficients out of 1024)

Distinctness checks:
  ok: distinct messages/salts give distinct outputs
```

("0 zero coefficients" is unsurprising, not a bug: a `ZMod 12289` coefficient lands on `0` with
probability about `1/12289`, so `0` zeros out of 512 or 1024 samples is the typical case.)

### `sorry` / `native_decide` / `axiom` audit

```
grep -rl sorry Vendor/*.lean Vendor/**/*.lean         # no output
grep -rn 'native_decide\|axiom' Vendor/*.lean Vendor/**/*.lean
  # Ring/SchoolbookCert.lean:  "Each ring axiom is lifted from `NegacyclicQuotient`..."
  # MLDSA/Primitives.lean:     "correspond to the axioms in EasyCrypt's `DRing.eca`..."
  # Ring/Kernel.lean:          "the four kernel axioms", "the coefficient axioms"
  # — all four are docstring prose about CommRing/AdjoinRoot axioms or the source EasyCrypt
  # development, not a Lean `axiom` declaration. No `native_decide` anywhere.
```

No `sorry`, `native_decide`, or added `axiom` declaration anywhere under `Vendor/`.

## Map: vendored definitions to the concepts they implement

All names below are fully qualified Lean names, buildable from this package's root (no `Vendor.`
prefix — the `lean_lib`s use `srcDir = "Vendor"` precisely so module names match VCVio's).

| Concept | Lean name | Type |
|---|---|---|
| `R_q` (ML-DSA) | `MLDSA.Rq` | `Type` (= `MLDSA.coeffRing.Poly`, `q = 8380417`, degree 256) |
| `R_q` (Falcon) | `Falcon.Rq (n : ℕ)` | `Type` (`q = 12289`, degree `n ∈ {512, 1024}`) |
| Negacyclic multiplication (generic) | `LatticeCrypto.negacyclicMulPure` | `{Coeff} [Ring Coeff] (backend : PolyBackend Coeff) → backend.Poly → backend.Poly → backend.Poly`, proved sound by `LatticeCrypto.negacyclicMulPure_sound` |
| Negacyclic multiplication (ML-DSA) | `MLDSA.negacyclicMul` | `Rq → Rq → Rq` |
| Negacyclic multiplication (Falcon) | `Falcon.negacyclicMul` | `{n} → Rq n → Rq n → Rq n` |
| `Decompose` | `MLDSA.Concrete.decomposeCoeff` | `Coeff → (gamma2 : ℕ) → ℕ × ℤ` (FIPS 204 Algorithm 36, one coefficient) |
| `HighBits` | `MLDSA.Concrete.highBits` | `(p : Params) → Rq → MLDSA.Concrete.High` (`:= Rq`), polynomial-level Algorithm 37 |
| `LowBits` | `MLDSA.Concrete.lowBits` | `(p : Params) → Rq → Rq`, Algorithm 38 |
| `MakeHint` | `MLDSA.Concrete.makeHint` | `(p : Params) → Rq → Rq → MLDSA.Concrete.Hint` (`:= Vector Bool 256`), Algorithm 39 |
| `UseHint` | `MLDSA.Concrete.useHint` | `(p : Params) → MLDSA.Concrete.Hint → Rq → MLDSA.Concrete.High`, Algorithm 40 |
| `w1Encode` | `MLDSA.Concrete.w1Encode` | `(p : Params) → Vector MLDSA.Concrete.High p.k → List Byte`, Algorithm 28 |
| `SampleInBall` (abstract) | `MLDSA.Primitives.sampleInBall` (field) | `MLDSA.CommitHashBytes p → MLDSA.ChallengePoly` (`:= Rq`) |
| `SampleInBall` (concrete) | `MLDSA.Concrete.sampleInBallPoly` | `(p : Params) → CommitHashBytes p → Rq`, Algorithm 29, `H = SHAKE256` |
| `ExpandA` (abstract) | `MLDSA.Primitives.expandA` (field) | `Bytes 32 → MLDSA.TqMatrix p.k p.l` |
| `ExpandA` (concrete) | `MLDSA.Concrete.expandA?` (`expandA` the total record field) | `(p : Params) → Bytes 32 → Option (TqMatrix p.k p.l)`, Algorithm 32, `H128 = SHAKE128`, 768 candidates per entry |
| `μ` | `MLDSA.Concrete.hashMessage` | `Bytes 64 → List Byte → Bytes 64`, `= SHAKE256(tr ‖ M′, 64)` |
| `tr` | `MLDSA.Concrete.hashPublicKey` | `(p : Params) → Bytes 32 → Vector Power2High p.k → Bytes 64`, `= SHAKE256(pkEncode(ρ,t₁), 64)` |
| ML-DSA verify (abstract) | `MLDSA.fipsVerify` | `(p : Params) → (prims : Primitives p) → PublicKey p prims → List Byte → FIPSSignature p prims → [NTTRingOps] → Bool` |
| ML-DSA verify (closed, per parameter set) | `MLDSA.Concrete.verify44` / `verify65` / `verify87` | `PublicKey mldsaNN (concretePrimitives mldsaNN) → List Byte → FIPSSignature mldsaNN (concretePrimitives mldsaNN) → Bool` |
| Falcon `HashToPoint` (abstract field) | `Falcon.VerifyPrimitives.hashToPoint` (field) | `Falcon.Bytes 40 → ByteArray → List Byte → Rq p.n` |
| Falcon `HashToPoint` (concrete) | `Falcon.Concrete.hashToPoint` | `(n : ℕ) → Falcon.Bytes 40 → ByteArray → List Byte → Rq n`, Algorithm 3 (+ FIPS 206 raw-message `vrfyKey` binding) |
| Falcon verify (abstract) | `Falcon.verify` | `(p : Params) → VerifyPrimitives p → PublicKey p → List Byte → Signature → Bool` |
| Falcon verify (closed, per parameter set) | `Falcon.Concrete.verify512` / `verify1024` | `PublicKey paramsNNN → List Byte → Signature → Bool` |
| Centered representative | `LatticeCrypto.centeredRepr` | `{q : ℕ} → ZMod q → ℤ` (`:= x.valMinAbs`) |
| ℓ∞ norm (bundle field) | `LatticeCrypto.NormOps.cInfNorm` | `NormOps backend → backend.Poly → ℕ` |
| ℓ∞ norm (ML-DSA) | `MLDSA.polyNorm` / `MLDSA.polyVecNorm` | `Rq → ℕ` / `{k} → RqVec k → ℕ` |
| ℓ2 norm squared (bundle field) | `LatticeCrypto.NormOps.l2NormSq` / `.pairL2NormSq` | `NormOps backend → backend.Poly → ℕ` / `→ backend.Poly → backend.Poly → ℕ` |
| ℓ2 norm squared (Falcon) | `Falcon.polyL2NormSq` / `Falcon.pairL2NormSq` | `{n} → Rq n → ℕ` / `{n} → Rq n → Rq n → ℕ` |
| `shake256` | `SLHDSA.Concrete.Keccak.shake256` | `ByteArray → (outLen : ℕ) → ByteArray` |
| `shake128` | `SLHDSA.Concrete.Keccak.shake128` | `ByteArray → (outLen : ℕ) → ByteArray` |

## Remaining `sorry`s

None, anywhere under `Vendor/` (see the audit above).

## Reed–Solomon proximity subset (unique decoding and Johnson MCA)

`ArkLib/` and `CompPoly/` contain the mathematical dependency subset for
BCIKS20 correlated agreement on lines and for Johnson-radius mutual correlated
agreement (MCA), under their Apache-2.0 licenses (`ArkLib-LICENSE`,
`CompPoly-LICENSE`). The source repositories are
<https://github.com/Verified-zkEVM/ArkLib>, <https://github.com/Verified-zkEVM/CompPoly>,
<https://github.com/Verified-zkEVM/VCVio>, <https://github.com/Verified-zkEVM/PolyFun> and
<https://github.com/leanprover/cslib>. `rs-provenance.json` records, for every file, its
repository, commit, original SHA-256 and vendored SHA-256; the source hashes
identify local source content independently of the repository revision.

Unique decoding (vendored 2026-09-22, ArkLib `0b5b67c6`, CompPoly `7e3683ba`).
The ArkLib root is `ProximityGap.BCIKS20.AffineLines.JointAgreement`. GordieHowe adapts
this line theorem to its indexed code domains in
`GordieHowe/Foundations/ReedSolomon/CorrelatedLine.lean`. The coefficient-counting and matrix
extension are local proofs in `AffineLineCounting` and `AffineRSProximity`. Its
probability-wrapper imports and the unused probability-to-cardinality lemma are
omitted: GordieHowe uses finite cardinalities directly.

Johnson MCA (vendored 2026-10-03, ArkLib `ace55c3e2`, which pins Lean v4.34.0
and Mathlib `5ed29652`, ours). Roots:
`ReedSolomon.MutualCorrelatedAgreement.{Johnson.Agreement, Johnson.Probability,
LineToAffine}`. The whole textual import closure is copied unchanged (303
modules): 204 ArkLib, 21 CompPoly (`df591bb8`), and the probability layer that
ArkLib's `mcaError` is stated in, VCVio and its `ToMathlib` (`d7089e46`, 54),
PolyFun and its `ToCslib` (`3710d71b`, 18) and cslib (`990e65a6`, 6). Their
licenses are `VCVio-LICENSE`, `PolyFun-LICENSE`, `cslib-LICENSE` (all
Apache-2.0). The list-size bound `JohnsonBound.Pairwise`
(`Code.finset_card_le_pairwiseJohnson`, alphabet-independent) and its two
imports `ListDecodability`, `Finset.PairwiseIntersection` are added unchanged. Shared files that the unique-decoding subset already had were
moved to the new commit; the BCIKS20, Berlekamp–Welch and Polishchuk–Spielman
files outside the new closure stay at `0b5b67c6` and build unchanged. cslib
needs Lean's default auto-bound implicits (`lakefile.toml`). GordieHowe adapts the
affine theorem in `GordieHowe/Foundations/ReedSolomon/JohnsonAgreement.lean`.

Adaptations (both subsets): the admitted declarations `Fin.sumCases`
(`Data/Fin/Basic.lean`) and `MvPolynomial.basis`
(`Data/MvPolynomial/Interpolation.lean`) are omitted; nothing references them.
Before omitting them, `#print axioms` on the upstream-unchanged closure showed
that no Johnson MCA theorem depends on `sorryAx`. No imported mathematical
theorem is replaced by a hypothesis or an axiom.
