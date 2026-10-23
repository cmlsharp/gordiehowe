-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA44.System.Source
public import GordieHowe.Applications.MLDSA44.Emulated.System.Params

@[expose] public section

/-!
# ML-DSA emulated: the source assignment

The assignment of ML-DSA emulated before the randomized lowerings
(`lib/gordiehowe/examples/mldsa/mldsa_emulated.h`, `mldsa_gadgets.h`, `mldsa_hash.h`): ML-DSA
native's (`GordieHowe.MLDSA44.Native.Source`: the message bits, the Keccak trace, H's `w1` and decoded challenge,
the hint, the challenge bits, `signature.w`, `z` and UseHint's advice), since the hash constraints,
the challenge and UseHint's advice are the same gadgets, and the quotient digits of the signature
relation, `signature.relation.d0`, `d1`, `d2` (`[K][N]` each; `mod.h:541-650`, `committed_digits`).

In domain A of the emulated arm, `z` is the signed coefficient in the carrier (`p - |z|` below
zero, `mldsa_emulated.h:268-277`), `signature.w` is the natural `w'` below `T^2` (bound to two
digits, `mldsa_emulated.h:200`), and `hint.offset`, `hint.slack` are bound to their digits.

**Modelling note on the quotient digits.** The C++ commits them in the `mod` lowering's
committed-digit form (`mod.h`, `PlanRecords::Mod::kCommittedDigits`): the lowering allocates the
cells, emits the row `lhs - rhs - q qlo - q Σ_j B^j d_j = 0` and requests each digit below `B`. The
Lean takes the digits as application advice in the source assignment, because their honest values
read the key (the quotient of `w' + 2^d t1 c - A z` by `q`). The cells, the row and the
requests are the C++'s: the row is a constraint of the algebra (`GordieHowe.MLDSA44.Emulated.SigRow`) and the
requests are in domain A's range plan.

The crossing is native's: `MLDSANative.xhOf P a.toSource` and `MLDSANative.xaOf P a.toSource`.
-/

namespace GordieHowe.MLDSA44.Emulated

open Params
open Native.Params (N nRows)

/-- **The source assignment of ML-DSA emulated**, for a `msgLen`-byte message, with domain H's
field `KH` and domain A's field `F`: native's, and the quotient digits of the signature relation. -/
structure Source (KH F : Type) (msgLen : ℕ) extends Native.Source KH F msgLen where
  /-- The quotient digits of the signature relation (`signature.relation.d0`, `d1`, `d2`):
  coefficient `(i, k)`, digit `j`. -/
  quot : Fin nRows → Fin N → Fin sigDigits → F

end GordieHowe.MLDSA44.Emulated
