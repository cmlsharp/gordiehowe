/-
New file: not from VCVio. Structural sanity checks for
`Vendor/LatticeCrypto/MLDSA/ConcretePrimitives.lean`. These are NOT known-answer tests: no
ML-DSA ACVP vectors were available to check `expandA`/`sampleInBall`/the hash primitives
against (see that file's header and `Vendor/README.md`). What is checked here is internal
consistency of `sampleInBallPoly`'s output against the shape Algorithm 29 promises: exactly
`τ` nonzero coefficients, every nonzero coefficient in `{-1, 1}`, for every approved ML-DSA
parameter set, on several distinct commitment-hash inputs.
-/

import LatticeCrypto.MLDSA.ConcretePrimitives

open MLDSA MLDSA.Concrete

private def countNonzero {n : ℕ} (v : Vector Coeff n) : ℕ :=
  (v.toList.filter (· ≠ 0)).length

private def allPM1 {n : ℕ} (v : Vector Coeff n) : Bool :=
  v.toList.all fun c => c = 0 ∨ c = 1 ∨ c = (modulus - 1 : ℕ)

private def testCTilde (p : Params) (seedByte : UInt8) : CommitHashBytes p :=
  Vector.ofFn fun i : Fin (p.lambda / 4) => seedByte + i.val.toUInt8

private def checkSampleInBall (label : String) (p : Params) (cTilde : CommitHashBytes p) :
    IO Unit := do
  let c := sampleInBallPoly p cTilde
  let weight := countNonzero c
  unless weight == p.tau do
    throw (IO.userError
      s!"{label}: sampleInBall weight {weight} ≠ τ = {p.tau}")
  unless allPM1 c do
    throw (IO.userError s!"{label}: sampleInBall produced a coefficient outside the set -1, 0, 1")
  IO.println s!"  ok: {label} (weight {weight} = τ = {p.tau})"

private def checkExpandAShape (label : String) (p : Params) (rho : Bytes 32) : IO Unit := do
  let a := expandA p rho
  unless a.size == p.k do
    throw (IO.userError s!"{label}: expandA row count {a.size} ≠ k = {p.k}")
  unless a.toList.all (fun row => row.size == p.l) do
    throw (IO.userError s!"{label}: expandA column count ≠ l = {p.l}")
  IO.println s!"  ok: {label} ({p.k} × {p.l} matrix)"

def testMLDSAConcretePrimitives : IO Unit := do
  IO.println "SampleInBall weight/coefficient checks:"
  for (name, p) in [("mldsa44", mldsa44), ("mldsa65", mldsa65), ("mldsa87", mldsa87)] do
    for seedByte in [(0 : UInt8), 1, 0x7f, 0xff] do
      checkSampleInBall s!"{name} seed={seedByte}" p (testCTilde p seedByte)
  IO.println ""
  IO.println "ExpandA shape checks:"
  for (name, p) in [("mldsa44", mldsa44), ("mldsa65", mldsa65), ("mldsa87", mldsa87)] do
    checkExpandAShape name p (Vector.ofFn fun i : Fin 32 => i.val.toUInt8)

#eval testMLDSAConcretePrimitives
