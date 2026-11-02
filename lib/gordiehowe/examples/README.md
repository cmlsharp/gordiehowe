# Example applications

Each directory holds one application: its relation headers, the host code
that builds statements and witnesses, its tests and its bench executable.
Read the relation header named below first; it states what is proved and
which domains prove it.

`sha256/` proves knowledge of a message whose SHA-256 digest is public, in
one binary domain, with SHA-256 either batched or in GKR. Read
`sha256_preimage.h`. The comparison harness in `../bench/hash_comparisons/`
runs it.

`keccak/` proves knowledge of a message whose SHA3-256 digest is public, in
one binary domain, with Keccak batched. Read `sha3_preimage.h`. The
comparison harness in `../bench/hash_comparisons/` runs it.

`mldsa/` proves possession of an ML-DSA signature (ML-DSA-44, -65 or
-87, `mldsa_params.h`) on a private message under a public key. Domain H hashes and domain A checks the signature's
algebra, either in an extension of the ML-DSA field F_q (native arm) or in
a Goldilocks extension, where congruences mod q are checked over the
integers (emulated arm). Read `mldsa_native.h`, then `mldsa_emulated.h`;
`mldsa_hash.h` holds domain H.

`falcon/` proves possession of a Falcon-512 or Falcon-1024 signature on a
private message under a public key, with the same two arms as ML-DSA. Read
`falcon_params.h`, which holds the two parameter sets the relations take
as a template parameter, then `falcon_emulated.h`, which states the
relation, then `falcon_native.h`; `falcon_hash.h` holds domain H.

`rings/` proves that the prover holds a signature on a message under one
key of a public ring of ML-DSA (any of the three sets), Falcon-512 or
Falcon-1024 keys without revealing which. Read `mldsa_ring.h` (with
`mldsa_ring_native.h` and `mldsa_ring_carrier.h`, its two arms) and
`falcon_ring.h`.

`rsa/` proves possession of an RSA-2048 PKCS#1 v1.5 signature with SHA-256
on a private message. Read `rsa_pkcs1.h`.

`p256/` holds the P-256 gadgets the ECDSA verifications use: fixed-base and
variable-base scalar multiplication, complete addition and the checks on r.
Read `p256_ecdsa.h`; `p256_scalar_mult.h` is a stand-alone scalar
multiplication that tests the placement rule.

`mdoc/` proves Longfellow's ZkSpec v7 mDL relation: the MSO's digest, its
validity dates and requested attributes in domain H, and the issuer's and
the device's ECDSA signatures in domain A. Read `mdoc.h`, then
`mdoc_hash.h` and `mdoc_signatures.h`.

`pq_mdoc/` proves the same mDL relation with ML-DSA-44 in place of both
ECDSA signatures. Read `pq_mdoc.h`.

`composite/` proves possession of a composite ML-DSA-44 and ECDSA P-256
signature on one private message, in three domains. Read `composite.h`.

`shared/` holds what several applications use: the domain profiles and
compile profiles (`domain_profile.h`, `setup.h`) and test helpers. The
private message of a proof of possession and cutoff selection are library
functions (`../lib/message.h`, `../lib/cutoff_select.h`).

## File names

In an application directory `<x>`:

- `<x>.h` and the other headers without a suffix below are relation code:
  they declare constraints.
- `<x>_params.h` holds the application's constants and shapes.
- `<x>_witness.h` holds the host code that the relation's generators
  call; `<x>_host.h` holds the host code of public computations, which the
  prover and the verifier both run.
- `<x>_builders.h` builds the statement and the witness from application
  values (keys, signatures, messages).
- `<x>_testing.h` holds test support that any test, bench or other
  application may include: the `*System` wrapper that compiles the relation
  with example values, host references and the plan export.
- `<x>_fixture.h` holds the fixture that one application's tests and bench
  executable share, in an anonymous namespace (each translation unit has
  its own copy). Only that application's tests and bench executable,
  and compiler tests in `../tests/` that run its fixture, include it; a
  fixture with a single user lives in its `_test.cc`.
- `<x>_test.cc` are the tests and `<x>_bench.cc` the bench executable.
- Test data has its own name: `rsa/rsa_vectors.h` (the RSA key and
  signatures the tests use) and `pq_mdoc/pq_mdoc_data.h` (an issuer and a
  device with ML-DSA-44 keys).
- `instantiations/` instantiates the application's builders explicitly for
  both parameter sets (`instances.h`).
