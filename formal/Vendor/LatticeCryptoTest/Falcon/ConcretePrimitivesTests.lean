/-
New file: not from VCVio. Structural sanity checks for
`Vendor/LatticeCrypto/Falcon/ConcretePrimitives.lean`. Not known-answer tests: no Falcon test
vectors were available to check `hashToPoint` against (see that file's header and
`Vendor/README.md`). What is checked here: `hashToPoint` does not exhaust its candidate budget on several distinct
inputs at both approved degrees, and distinct salts or messages give distinct outputs.
-/

import LatticeCrypto.Falcon.ConcretePrimitives

open Falcon Falcon.Concrete

private def testSalt (b : UInt8) : Falcon.Bytes 40 := Vector.ofFn fun i : Fin 40 => b + i.val.toUInt8

private def checkDetermined (label : String) (n : ℕ) (salt : Falcon.Bytes 40)
    (msg : List Byte) : IO Unit := do
  match hashToPoint n salt ByteArray.empty msg with
  | none =>
    throw (IO.userError s!"{label}: the candidate budget was exhausted")
  | some c =>
    -- A loose sanity bound on the zero coefficients, not a distribution test.
    let zeros := (c.toList.filter (· = 0)).length
    let looseBound := n / 4 + 8
    unless zeros ≤ looseBound do
      throw (IO.userError
        s!"{label}: {zeros} zero coefficients out of {n}, more than the loose bound {looseBound}")
    IO.println s!"  ok: {label} ({zeros} zero coefficients out of {n})"

def testFalconConcretePrimitives : IO Unit := do
  IO.println "HashToPoint determinacy checks:"
  for n in [512, 1024] do
    checkDetermined s!"n={n} salt=0 msg=[]" n (testSalt 0) []
    checkDetermined s!"n={n} salt=1 msg=[1,2,3]" n (testSalt 1) [1, 2, 3]
    checkDetermined s!"n={n} salt=0xff msg=long" n (testSalt 0xff) (List.replicate 200 (7 : UInt8))
  IO.println ""
  IO.println "Distinctness checks:"
  let a := hashToPoint 512 (testSalt 0) ByteArray.empty [0]
  let b := hashToPoint 512 (testSalt 0) ByteArray.empty [1]
  let c := hashToPoint 512 (testSalt 1) ByteArray.empty [0]
  unless a ≠ b do
    throw (IO.userError "hashToPoint: distinct messages gave the same output")
  unless a ≠ c do
    throw (IO.userError "hashToPoint: distinct salts gave the same output")
  IO.println "  ok: distinct messages/salts give distinct outputs"

#eval testFalconConcretePrimitives
