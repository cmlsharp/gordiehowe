# Extraction error and sampler constructor re-audit, 2026-11-03

Scope: 3 declarations at source commit `c7c1e4cd6`.

| Declaration | Previous fingerprint | Reviewed fingerprint |
|---|---:|---:|
| `GordieHowe.SPBCS.knowledgeError` | 3110842099956408589 | 2026509420695358959 |
| `GordieHowe.SPBCS.knowledgeErrorROM` | 9171732676751255080 | 15459845963024302027 |
| `GordieHowe.SPBCS.Sampler.mk` | 4187928097 | 1458511791 |

Historical sources reviewed: the single-chain and fork/join knowledge-error definitions
at `d9a8886d`, and `Sampler` at `c267c54b`. Current source and fingerprints match the
compiled acceptance closure. This is a semantic re-audit of three ledger entries;
no Lean source or headline statement is changed.

`knowledgeError` now names the former fork/join formula, with an explicit `cP` bound
for extra seeded digests. The expression is
`2 * esqrt (kq / card (Out k e)) + 6 * t^2 * (κ + (max 2 c + cP + 1) * t / 2^(8*k))`.
The old single-chain formula lacked `cP`; the old fork/join formula already contained
exactly this term. The renamed current interface must not be identified with the old
single-chain interface at arbitrary `cP`. The extra collision contribution is retained,
not dropped. Natural-number multiplication inside the cast is exact and cannot overflow.
The denominator `2^(8*k)` is positive even at `k = 0`, and `Out k e` has positive finite
cardinality, including zero byte lengths. The bound is an extended nonnegative real;
values above one are allowed bounds rather than a silently truncated probability.
At `t = 0`, the instability contribution vanishes while the verifier simulation term
still depends on `kq`. The QROM expression retains both contributions.

`knowledgeErrorROM` is the analogous current fork/join classical expression
`t * (κ + (max 2 c + cP + 1) * t / 2^(8*k))`. Its historical fork/join source has the same
formula. The absence of the square-root simulation term is specific to the classical
model, not a simplification of the QROM claim. Current `KnowledgeROM` callers use
`tq + kq` for the adversary-plus-verifier query budget and `Mg.nJ` for seeded digests;
the internal database bound uses its supplied full query budget. The formula is
monotone in the round-error bound and contains no adversary-side premise. Both these
noncomputable declarations are numerical probability bounds, not runtime algorithms.

`Sampler.mk` adds an explicit default challenge to the old partial sampler and equal
preimage-count law. The successful sample map remains `Option C`; uniformity is exact
conditional on success and does not require success to have positive probability.
The default inhabits the challenge type for total transcript reads, while the actual
acceptance predicate requires every challenge sample to be `isSome`. Thus failure is
still rejected and charged by `rejectionProb`; no fallback acceptance or discarded
bad-randomness event is introduced. This does not certify the separately parked
challenge-default redesign, and does not imply that arbitrary choices of default
are definitionally identical in headline expressions.

Historical namespace/interface changes explain the stale fingerprints. The current
formulas and sampler law have been checked directly; this report does not claim a
whole-library definitional equivalence or refresh unrelated ledger entries.
