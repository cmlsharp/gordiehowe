# Planned changes

Items 5 and 6 rewrite part of an application's program in a form the
library or the compiler offers. Each changes the realized program (its
nodes, predicates, range requests or operators), so the plan exports,
system digests and proofs of the affected configurations change with it.
The released code keeps the programs that produced the papers' figures and
the checked-in plan exports. These changes are held for a later release,
which will regenerate the plans and rerun the affected benchmarks. The code
marks each place with a comment `Planned change N (docs/planned-changes.md)`.

## 5. Falcon emulated: `assert_mod` with a spectral right-hand side

The signature equation in `lib/gordiehowe/examples/falcon/falcon_emulated.h`
is an `assert_spectral` with an explicit bias and a committed quotient. It
will be an `assert_mod` whose right-hand side is the spectral product, so
the lowering derives the bias and commits the quotient. The nodes and range
requests change.

Affects Falcon-512 emulated, at both parameter sets.

## 6. ML-DSA ring, carrier arm: `assert_mod` with a spectral right-hand side

The relation rows in `lib/gordiehowe/examples/rings/mldsa_ring_carrier.h`
take the same form as item 5: an `assert_spectral` with an explicit bias and
committed quotients `dq`. They will be `assert_mod` with the spectral
product as the right-hand side. The nodes and their creation order change.

Affects the ML-DSA-44 ring's carrier arm, at both parameter sets.
