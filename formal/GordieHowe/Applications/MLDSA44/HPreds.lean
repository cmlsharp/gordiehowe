-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

@[expose] public section

/-!
# GordieHowe: the bounds of the native ML-DSA-44 program's domain `H` predicates

Domain `H` of the native ML-DSA-44 program (C++ `lib/gordiehowe/examples/mldsa/mldsa_native.h`) is
one run of predicates: `μ`'s hash from `h2c.mu.blocks.r0`, then the core from `h2c.c_tilde.r0`
(`c̃'`'s absorbs, SampleInBall's stream, the selection and the memory check) through
`h2c.sample.mem.fresh`. The native frontend's statements (`GordieHowe.MLDSA44.HSat`,
`GordieHowe.MLDSA44.HSatCore`) and the embeddings that hold these parts read the run's bounds by
these names; each program's facts decide its predicates against them.
-/

namespace GordieHowe.MLDSA44

/-- The first predicate of domain `H`'s part, `h2c.mu.blocks.r0`. -/
def hPredLo : Nat := 18

/-- The first predicate of domain `H`'s core, `h2c.c_tilde.r0`. -/
def corePredLo : Nat := 48

/-- The last predicate of domain `H`'s part and core, `h2c.sample.mem.fresh`. -/
def hPredHi : Nat := 270

end GordieHowe.MLDSA44
