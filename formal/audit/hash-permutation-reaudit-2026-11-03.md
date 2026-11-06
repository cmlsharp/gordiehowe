# Hash-count and permutation-event re-audit, 2026-11-03

Scope: three declarations at source commit `054c7c9f7`, compared with their
last matching historical snapshot `f01311529` in the predecessor repository.
Original audit references are C62 for the hash count and C69 for the two
permutation declarations. No Lean source or headline changes in this audit.

| Declaration | Previous fingerprint | Reviewed fingerprint |
|---|---:|---:|
| `GordieHowe.HashCircuit.falconPerms` | 7924243325419423787 | 18160176241984605145 |
| `GordieHowe.PermutationEvent.prodPoly` | 14447493480246281345 | 12779484326995391166 |
| `GordieHowe.PermutationEvent.permEvent` | 5720621681709628195 | 3305935557195102639 |

## Falcon permutation count

`HashCircuit.falconPerms` changes `falconExtra msgLen + 10` to
`falconExtra msgLen + 11`, corresponding to the fixed candidate count increasing
from 639 to 717. The input is the 40-byte nonce followed by the message; at the
SHAKE256 rate of 136 bytes, padding requires `floor((40+msgLen)/136)+1` absorb
permutations, including when the unpadded length is an exact multiple of 136.
The output now contains `2*717=1434` bytes, requiring eleven blocks, of which
the first is already available from the final absorb. Ten additional squeeze
permutations give exactly the new definition. For the old 1278-byte output,
ten blocks required nine additional squeezes, explaining the old constant.

Reviewed conformance points are `falcon_hash.h`'s use of `Set::kOutBytes`,
`falcon_params.h`'s `kOutBytes=2*kSamples`, and the formula
`blocks + ceil(out_bytes/rate) - 1` in `lib/gordiehowe/lib/keccak.h`.
Empty messages and the boundary at message length 96 are covered by the same
padding arithmetic. This is a real shape change, not a rename or an equality
between the two counts. No randomness is discarded by this count definition.

Disposition: passes current arithmetic and conformance review.

## Product polynomial

`PermutationEvent.prodPoly` is generalized from `[Field K]` to `[CommRing R]`;
its body remains the product of the factors `X-C(a)` over the list in order.
This definition needs only commutative-ring operations. It has no field-specific
cancellation, division, nonzero assumption or probabilistic premise. Empty lists
produce one; duplicate entries retain their multiplicity. Over a field it remains
the same product, with the commutative-ring instance inherited from that field.
The generalized degree bound is an inequality, so cancellation and the trivial
ring do not invalidate it. This review accepts the generalization; it does not
claim a syntactically unchanged type fingerprint.

Disposition: passes the definition and boundary-case review.

## Permutation challenge event

`PermutationEvent.permEvent` still requires `[Field K]` and constructs the
polynomial `prodPoly l1 - prodPoly l2`, degree allowance
`max l1.length l2.length`, and its proved upper bound. Its changed elaboration
passes the field's commutative-ring instance to the generalized `prodPoly`.
No assumption that the two lists differ is added to the constructor.

The adjoining `multiset_eq_or_badAt` theorem handles the zero-polynomial case
by concluding equal multisets, and the other case by recording both nonzeroness
and evaluation zero in `ChallengeEvent.BadAt`. Thus equal lists do not become an
unbounded exceptional event. Unequal lengths are handled by the maximum length;
empty lists have product one and degree allowance zero when both are empty.
The theorem retains the field hypothesis needed for the polynomial identity
argument. It does not generalize root-counting to an arbitrary ring.

The C++ `assert_products_equal` in `lib/gordiehowe/lib/permutation.h` checks
products of the factors `delta - packed_record`, matching polynomial evaluation.
The event's degree bounds the root count over the field; it does not by itself
claim a uniform challenge distribution or remove the surrounding sampling
obligation. No extra premise restricts a cheating prover.

Disposition: passes the challenge-event statement and conformance review.

## Validation scope

All three own fingerprints agree with the completed combined environment and
tracked closure. Their source files are byte-identical to that built environment.
This commit changes only these three ledger rows and this report. It does not
clear other stale entries or replace final closure and gate reconciliation.
