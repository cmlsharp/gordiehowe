# Ligero prefix-test review, 2026-11-03

Scope: 31 declarations at source commit `15dc27615`.

| Declaration | Previous fingerprint | Reviewed fingerprint |
|---|---:|---:|
| `GordieHowe.Ligero.MaskTest.Hiding.mk` | 2646456005 | 153787072 |
| `GordieHowe.Ligero.MaskTest.Input` | 5068981936929318631 | 4481831124007891983 |
| `GordieHowe.Ligero.MaskTest.commitProve` | 2130801413071040452 | 2062761093680166885 |
| `GordieHowe.Ligero.MaskTest.honest` | 11865413148861224183 | 3021546738299546428 |
| `GordieHowe.Ligero.MaskTest.innerHonest` | 398352306507085061 | 2625689333517776716 |
| `GordieHowe.Ligero.MaskTest.jointCheck` | 8357735475985592275 | 16442668792389742277 |
| `GordieHowe.Ligero.MaskTest.ligeroJoint` | 6608453511635900043 | 453917916450972068 |
| `GordieHowe.Ligero.MaskTest.ligeroQuery` | 18414118761718746819 | 15441152696755440504 |
| `GordieHowe.Ligero.MaskTest.ligeroQuery_acceptsWithin` | 419251454 | 646319348 |
| `GordieHowe.Ligero.MaskTest.proofEmpty` | 16029602365637249735 | 990537670974529749 |
| `GordieHowe.Ligero.MaskTest.proofJoint` | 4769312673141578293 | 11137316360030731704 |
| `GordieHowe.Ligero.MaskTest.proofPhase` | 9555263833853728745 | 11272022318673567963 |
| `GordieHowe.Ligero.MaskTest.proofPhase_V` | 4257398724 | 3268816946 |
| `GordieHowe.Ligero.MaskTest.soundIP` | 7884551873948057721 | 14950290216905576057 |
| `GordieHowe.Ligero.MaskTest.verdict` | 2120283688844251258 | 16258044203813129017 |
| `GordieHowe.Ligero.MaskTest.verdict_of_eq_zero` | 2182055229 | 2617323925 |
| `GordieHowe.Ligero.UntestedMask.Input` | 5087643529545993727 | 17348634171006912817 |
| `GordieHowe.Ligero.UntestedMask.commitProve` | 14321029874953753810 | 13401202586107765768 |
| `GordieHowe.Ligero.UntestedMask.honest` | 12179716827624636784 | 1688956888746066584 |
| `GordieHowe.Ligero.UntestedMask.innerHonest` | 176479974361486980 | 3378559877335857676 |
| `GordieHowe.Ligero.UntestedMask.jointCheck` | 8908596147102783347 | 3815375255838944078 |
| `GordieHowe.Ligero.UntestedMask.ligeroJoint` | 12953448310202010674 | 6850829927369203408 |
| `GordieHowe.Ligero.UntestedMask.ligeroQuery` | 2850672872669255189 | 2342272127655024100 |
| `GordieHowe.Ligero.UntestedMask.ligeroQuery_acceptsWithin` | 115637943 | 480699419 |
| `GordieHowe.Ligero.UntestedMask.proofEmpty` | 3733118766597528347 | 4039260966851036261 |
| `GordieHowe.Ligero.UntestedMask.proofJoint` | 3021907992405008448 | 17516457704882888188 |
| `GordieHowe.Ligero.UntestedMask.proofPhase` | 17316808616970600425 | 12128408530969478316 |
| `GordieHowe.Ligero.UntestedMask.proofPhase_V` | 267359248 | 2907435721 |
| `GordieHowe.Ligero.UntestedMask.soundIP` | 9027367495460046301 | 9922555352845039777 |
| `GordieHowe.Ligero.UntestedMask.verdict` | 4996848717014894118 | 8235862897359999469 |
| `GordieHowe.Ligero.UntestedMask.verdict_of_eq_zero` | 2299484557 | 3296929504 |

## Evidence and classification

Reviewed both prefix-test wrappers, their setup, placement, soundness and honest
construction, and the shared joint-subfield counting argument in
Applications/Keccak/HashCircuit/Packed/Basic. Historical counterparts at
b67250008 and c0304fc4a used the Prefix/ListRadius and Prefix/SplitMask paths;
the later f01311529 and aaf4876b8 counterparts use the reorganized paths.
The saved comparisons cover every selected declaration. Source bytes and
fingerprints match the accepted compiled closure.

The changes include repeated low-degree tests and their common agreement set,
computational finite data, separate completeness and hiding data, and the
separately named simulator. These are substantive changes, not just renames.
The joint subfield argument already existed in the historical wrappers.

## Per-declaration review

Each entry below applies separately to both `GordieHowe.Ligero.MaskTest` and
`GordieHowe.Ligero.UntestedMask`, except the explicitly named constructor.
Their underlying systems are respectively Pieces and AgreementThreshold.

- `Input`: retains context, commitment and commit-round transcript, now with
  explicit nrep. MaskTest holds rows directly; UntestedMask includes the
  commitment's mask data. Neither erases the repetitions from the input type.
- `verdict`: conjoins the actual underlying Bool verdict with membership in E
  for every prefix row at every queried column. It uses the representative
  tableau row, not an extracted value supplied by the prover.
- `commitProve`: keeps N leaves, exact leaf reconstruction, two commit rounds,
  three proof rounds, extraction and query positions. The reads proof derives
  representative-row equality from equality of the actual queried columns;
  UntestedMask first projects the column from its larger leaf. Only the
  prefix check is added to the underlying verifier.
- `ligeroQuery`: packages the underlying sound proof with its existing errors,
  query index and identity query equivalence. It does not select a different
  challenge distribution or drop the repeated commit challenge.
- `jointCheck`: uses the actual prefix placement rows, code evaluation points,
  degree bound and common agreement set across repetitions. Off the commit
  event, a failed extracted prefix coordinate supplies a pinned polynomial
  with a coefficient outside E using extract_eq_eval and node membership.
  This existence argument is proof data, not a choice-based runtime extractor.
- `ligeroQuery_acceptsWithin`: derives membership of every queried column in
  commonAgreement from the actual underlying acceptance proposition. It does
  not assume that a cheating transcript is a low-degree codeword.
- `ligeroJoint`: adds withJointSubfield and its verified accepts-within premise.
  The joint counting proof charges one `(k-1)_t/(N)_t` term, independent of
  prefix count. It selects one failing row within a proof and bounds the
  simultaneous event by that row's event; it is not a union bound that forgot
  to multiply by the number of prefix rows.
- `verdict_of_eq_zero`: identifies the underlying verdict with the wrapper
  when np=0, because the extra universal test ranges over Fin 0.
- `proofEmpty`: uses that exact verdict equation and increases the underlying
  error only by a nonnegative term. No subfield premise is introduced.
- `proofJoint`: retains the joint proof with precisely the nonempty-prefix
  error expression; the error transport reduces to equality.
- `proofPhase`: chooses between the preceding proofs only by the public size
  np. It does not branch on a challenge or on whether an adversary succeeds.
- `proofPhase_V`: verifies that both size branches use the concrete verdict.
- `soundIP`: uses the original commit event and bound, the actual proof phase,
  and proofPhase_claim. The conjunction of the two exceptional-or-good claims
  is equivalent to exceptional-or-(RowsHold and PrefixIn). UntestedMask reads
  commitment.rows while MaskTest uses the rows directly. Prefix membership is
  a soundness conclusion, not an assumption about a cheating input.
- `innerHonest`: keeps the underlying honest construction and references its
  separately named simulator. Its existing noncomputability is retained and
  is not granted an exception by this audit.
- `honest`: retains the placement coins, commitment, rounds and proof; its
  admissibility is exactly the inner predicate. Completeness holds for every
  honest coin and challenge using prefixRow_mem. Hiding is the inner law
  pushed through viewOfInner, preserving leaves, rounds and transcript. The
  simulator's own coin type and map are separate computable definitions;
  this refactoring does not replace their probability law.
- `GordieHowe.Ligero.MaskTest.Hiding.mk`: requires the complete Pieces hiding
  data, including its query and split-coverage bounds, plus the prefix-row
  blinding-field inclusion. It does not replace those bounds with the weaker
  Placement data used only for completeness.

## Boundaries and scope

The empty prefix makes the prefix condition vacuous intentionally, leaving the
underlying proof system and errors intact. For nonempty prefixes, code points
and the appropriate message nodes must lie in E. Honest prefix source rows
are nonzero; in the split system they are outside piece rows, so the original
honest values are preserved. Hiding conditions remain separate from soundness
and completeness assumptions. The shared counting proof handles t>N through
an empty challenge type rather than a division by a nonpositive cardinality;
valid concrete parameters supply the meaningful query range.

This closes the original stale-entry cohort against the accepted compiled
snapshot. It does not certify the final implementation head before its new
closure is checked. Only ledger records and this report change: no headline,
protocol, distribution, hypothesis or CostLint exception changes.
