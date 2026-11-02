-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

import GordieHowe.Language.Realizations.Circuit.RelTable
import Mathlib.Data.ZMod.Basic

/-!
# The staged transform rule on a small transform

The relational check's rule for a staged negacyclic transform (`staged?`, `nttBlocksT`,
`RelTable.lean`) on transforms of length `8` over `F_17` at `ψ = 3` (`3^8 = −1`). The aux values
are the working arrays of a transcription of the C++'s scheme-order loop (`StagedNtt::forward`,
`lib/gordiehowe/ops/operators.h`) after every stage but the last. With them, every cut the rule
states holds and its outputs are `Σ_i x_i ψ^((2·br(m)+1) i)`, for one transform and for its
`batched 2` form; the cuts fail with one aux value changed, and with the transform read in natural
order. A `batched 0` operator is refused.
-/

namespace GordieHoweTest.GKRStagedNtt

open GordieHowe GordieHowe.RealizedProgram GordieHowe.GKR.Rel GordieHowe.GKR.Fold

/-- The field. -/
abbrev K := ZMod 17

/-- The environment of the code arithmetic modulo `17`. -/
def env : TEnv := ⟨⟨0, .ident⟩, primeArith 17, 16, 9, false, 0⟩

/-- The codes' decoding. -/
def κ (c : ℕ) : K := c

/-- The C++'s scheme-order loop (`StagedNtt::forward`), transcribed: the working array after each
stage. -/
def refStages (n L : ℕ) (ψ : K) (x : Array K) : List (Array K) := Id.run do
  let mut a := x
  let mut z := 1
  let mut len := n / 2
  let mut out : List (Array K) := []
  for _ in [0:L] do
    for g in [0:n / (2 * len)] do
      let start := g * (2 * len)
      let zeta := ψ ^ bitRevNat L z
      z := z + 1
      for j in [start:start + len] do
        let u := a[j]!
        let zv := zeta * a[j + len]!
        a := a.set! j (u + zv)
        a := a.set! (j + len) (u - zv)
    out := out ++ [a]
    len := len / 2
  return out

/-- The scheme-order transform by its formula. -/
def nttFormula (n L : ℕ) (ψ : K) (x : Array K) (m : ℕ) : K :=
  ((List.range n).map fun i => x[i]! * ψ ^ ((2 * bitRevNat L m + 1) * i)).sum

/-- Two blocks of inputs. -/
def xs0 : Array K := #[5, 1, 0, 16, 7, 3, 3, 12]
def xs1 : Array K := #[2, 9, 11, 4, 0, 6, 15, 8]

/-- The wire values: the inputs at nodes `8b + i`, block `b`'s stage `s` array at
`100 + 56b + 8s + p`. -/
def vals (blocks : List (Array K)) (q : ℕ) : K :=
  if q < 100 then (blocks.getD (q / 8) #[])[q % 8]!
  else
    let r := q - 100
    ((refStages 8 3 3 (blocks.getD (r / 56) #[])).getD (r % 56 / 8) #[])[r % 8]!

/-- The input wires of `k` blocks. -/
def inWires (k : ℕ) : List TE := (List.range (8 * k)).map fun i => .wire 0 1 i

/-- The aux wires of `k` blocks: two cut stages of `8` per block. -/
def auxWires (k : ℕ) : List Wire := (List.range (16 * k)).map fun j =>
  ⟨0, 1, 100 + 56 * (j / 16) + j % 16⟩

/-- Every cut holds at the values, every aux wire is read, and output `j` is the formula's
transform of block `j / 8` at `j mod 8`. -/
def ruleOk (o : NttOrder) (blocks : List (Array K)) (v : ℕ → K) (aux : List Wire) : Bool :=
  match nttBlocksT env 8 3 3 o blocks.length (inWires blocks.length) aux with
  | some (out, [], cs) =>
    cs.all (fun p => decide ((teW p.1).eval κ v = p.2.eval κ v)) &&
      out.length == 8 * blocks.length &&
      (List.range (8 * blocks.length)).all fun j =>
        decide ((out.getD j default).eval κ v =
          nttFormula 8 3 3 (blocks.getD (j / 8) #[]) (j % 8))
  | _ => false

/-- The transcription's last stage is the formula (a check of the reference). -/
example : (refStages 8 3 3 xs0).getD 2 #[] =
    ((List.range 8).map (nttFormula 8 3 3 xs0)).toArray := by
  decide +kernel

/-- Accepted: one scheme-order transform. -/
example : staged? (.staged (.ntt 8 3 .scheme) 1) = some (8, 3, .scheme, 8) := by decide +kernel

example : ruleOk .scheme [xs0] (vals [xs0]) (auxWires 1) = true := by decide +kernel

/-- Accepted: its `batched 2` form, two blocks of `8`, block-major aux. -/
example : staged? (.staged (.batched 2 (.ntt 8 3 .scheme)) 1) = some (8, 3, .scheme, 16) := by
  decide +kernel

example : ruleOk .scheme [xs0, xs1] (vals [xs0, xs1]) (auxWires 2) = true := by decide +kernel

/-- Rejected: one aux value changed. -/
example : ruleOk .scheme [xs0, xs1]
    (fun q => if q = 100 + 56 + 11 then vals [xs0, xs1] q + 1 else vals [xs0, xs1] q)
    (auxWires 2) = false := by
  decide +kernel

/-- Rejected: the scheme-order aux read as a natural-order transform. -/
example : ruleOk .natural [xs0] (vals [xs0]) (auxWires 1) = false := by decide +kernel

/-- Rejected: an aux wire missing. -/
example : ruleOk .scheme [xs0] (vals [xs0]) ((auxWires 1).dropLast) = false := by decide +kernel

/-- Refused: a `batched 0` operator. -/
example : staged? (.staged (.batched 0 (.ntt 8 3 .scheme)) 1) = none := by decide +kernel

end GordieHoweTest.GKRStagedNtt
