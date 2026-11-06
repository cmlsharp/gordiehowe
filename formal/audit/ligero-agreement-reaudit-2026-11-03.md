# Ligero agreement-threshold audit, 2026-11-03

Scope: 35 declarations at source commit `76bfd2af8`.

| Declaration | Previous fingerprint | Reviewed fingerprint |
|---|---:|---:|
| `GordieHowe.Ligero.AgreementThreshold.Bad` | 14605168554685863779 | 16653111026273489466 |
| `GordieHowe.Ligero.AgreementThreshold.Claim` | 1325893096630858306 | 13955410017509568608 |
| `GordieHowe.Ligero.AgreementThreshold.CommitRounds` | 1846194926569153965 | 7101296290867614589 |
| `GordieHowe.Ligero.AgreementThreshold.Input` | 12888772227453752577 | 13109260593018637310 |
| `GordieHowe.Ligero.AgreementThreshold.Parameters` | 803133670 | 565143509 |
| `GordieHowe.Ligero.AgreementThreshold.Setup.mk` | 659274860 | 3020500754 |
| `GordieHowe.Ligero.AgreementThreshold.TableauSetup.Hiding.mk` | 4267332940 | 1883810237 |
| `GordieHowe.Ligero.AgreementThreshold.TableauSetup.extract` | 17692753624921405105 | 15511967578747733264 |
| `GordieHowe.Ligero.AgreementThreshold.TableauSetup.mk` | 3683651436 | 2750439573 |
| `GordieHowe.Ligero.AgreementThreshold.TableauSetup.t` | 15744423607244194253 | 5239193780102788102 |
| `GordieHowe.Ligero.AgreementThreshold.Threshold.Exceptional` | 16681467622410594957 | 16472913391782847669 |
| `GordieHowe.Ligero.AgreementThreshold.Threshold.commitError` | 11016388756149602746 | 2871767273265565988 |
| `GordieHowe.Ligero.AgreementThreshold.Threshold.commitEvent` | 633279722042236140 | 9911349715671701828 |
| `GordieHowe.Ligero.AgreementThreshold.Threshold.pinnedRows` | 10733194435838600696 | 9208990840308416380 |
| `GordieHowe.Ligero.AgreementThreshold.commitProve` | 12874717912865920960 | 7992339549711805679 |
| `GordieHowe.Ligero.AgreementThreshold.commitSpec` | 17325635968886573979 | 21124828439362302 |
| `GordieHowe.Ligero.AgreementThreshold.commitTranscript` | 5170444162961567331 | 15906791101577860138 |
| `GordieHowe.Ligero.AgreementThreshold.honest` | 16696159020489104532 | 4612484537224598175 |
| `GordieHowe.Ligero.AgreementThreshold.honestCommitRounds` | 5761122708218100731 | 965178296245538487 |
| `GordieHowe.Ligero.AgreementThreshold.honestLdtResponse` | 217444968989892539 | 5716434216115938582 |
| `GordieHowe.Ligero.AgreementThreshold.instDecidableEqChallengeCommitSpec` | 3222052170648859511 | 10804901579038390755 |
| `GordieHowe.Ligero.AgreementThreshold.instFintypeChallengeCommitSpec` | 11685895931578872026 | 14810683993793975502 |
| `GordieHowe.Ligero.AgreementThreshold.interpolatedRows` | 8399742903668682956 | 11358455400142652651 |
| `GordieHowe.Ligero.AgreementThreshold.ldtChallenge` | 8337169399171979260 | 2977429458601663179 |
| `GordieHowe.Ligero.AgreementThreshold.ldtIdx` | 5387653172148336284 | 7788123868736610928 |
| `GordieHowe.Ligero.AgreementThreshold.ldtResponse` | 8026248538269224512 | 16961734195746148608 |
| `GordieHowe.Ligero.AgreementThreshold.query_count` | 1715482641 | 4234616991 |
| `GordieHowe.Ligero.AgreementThreshold.simulate` | 11325420936887188236 | 250829371153468763 |
| `GordieHowe.Ligero.AgreementThreshold.sound` | 6832917528538666550 | 7522684074180105132 |
| `GordieHowe.Ligero.AgreementThreshold.testAccept` | 9485016125076463063 | 8126391535539324451 |
| `GordieHowe.Ligero.AgreementThreshold.testProof` | 8154542022060027199 | 3075023034915586734 |
| `GordieHowe.Ligero.AgreementThreshold.test_count` | 3782067083 | 2285598091 |
| `GordieHowe.Ligero.AgreementThreshold.verdict` | 3949414527170678945 | 11621741464910588155 |
| `GordieHowe.Ligero.AgreementThreshold.viewLeaves` | 2272638568907200016 | 9432978891751828140 |
| `GordieHowe.Ligero.AgreementThreshold.viewOf` | 16706395597384045480 | 5541537598519674678 |

## Evidence and classification

Read AgreementThreshold and the supporting arbitrary-mask rate lemma and selected
constraint event. Compared its historical counterpart, ListRadius at 5831d8fbc,
with the current definitions. Checked the paper's Ligero appendix, common
agreement construction and repeated low-degree challenge discussion, and the
implementation's repetition-major transcript and per-repetition column checks.
These 35 entries are individually reviewed below. Their source bytes and
fingerprints match the accepted compiled statement closure.

The principal substantive change is repeated low-degree testing with independent
ILDT rows, a common agreement set and an all-repetitions exceptional event. The
old separate strict rate field was removed: the required `2*k-1 ≤ N` follows
from the arbitrary-mask Johnson assumptions, via `rate_of_johnson` at degree
`2*k-2`. This is a proved parameter implication, not an assumed restriction on
an adversary. Honest completeness was separated from hiding, and the simulator
was separated from the noncomputable honest bundle. Namespace/API changes are
also present; this report does not treat this cohort as a rename-only update.

## Per-declaration review

All names below have prefix `GordieHowe.Ligero.AgreementThreshold`.

- `commitSpec`: exactly two rounds, a verifier vector of all repetition
  challenges followed by all low-degree responses. Each repetition has R field
  coefficients and k response values; masks have coefficient one.
- `ldtIdx`: round zero is the unique challenge round, with its direction proof.
- `instFintypeChallengeCommitSpec`: eliminates the impossible prover-round
  challenge and uses the full finite function space for the verifier vector.
- `instDecidableEqChallengeCommitSpec`: uses the supplied field equality on that
  same full function space; it does not filter challenges.
- `CommitRounds`: the complete two-round transcript, with the final index two.
- `ldtChallenge`: reads entry zero at its complete repetition-indexed type.
- `ldtResponse`: reads entry one, retaining every repetition's k values.
- `commitTranscript`: puts these two entries back at precisely those indices;
  the accessor equations are reflexive.
- `honestCommitRounds`: emits the response function of the received challenge
  only. Causality checks the strict earlier-round index, with no later query.
- `interpolatedRows`: independently interpolates each row at the supplied k
  distinct columns. Generalizing the number of rows does not alter the formula.
- `Threshold.pinnedRows`: uses the first k columns of the common agreement set
  if its cardinality is at least A, and zero otherwise. `k_le_A` proves the
  columns exist; the choice of columns is fixed, not selected after a query.
- `Threshold.Exceptional`: requires every repetition's challenge to be in its
  matrix's exceptional set. The matrices are fixed by the committed rows.
- `Threshold.commitError`: raises the single-repetition density bound
  `B/(|F|-1)` to nrep; the supporting finite product count uses independent
  challenge coordinates. No fresh independence assumption is inserted.
- `Threshold.commitEvent`: tests the received challenge vector against the
  product of those fixed exceptional sets. It does not inspect a later response.
- `TableauSetup.mk`: retains placement and prepared-row equivalence, the query
  bound t ≤ N, and now a positive repetition count. The removed strict rate
  field is not needed by the shared setup; the untested-mask setup derives the
  weaker sufficient rate from its list parameters.
- `TableauSetup.t`: projects the chosen query count. Its bound is a setup fact,
  not a condition on which adversarial transcripts are considered.
- `TableauSetup.extract`: computes each placed cell by Lagrange evaluation on
  the same first k common-agreement columns, or zero in the small-set case.
  It does not choose a successful repetition. `extract_eq` identifies this
  executable map with the semantic pinned-row readout.
- `TableauSetup.Hiding.mk`: extends the placement/alignment conditions with
  t ≤ k minus the witness-position count. This is the privacy budget for the
  honest distribution; soundness does not assume it of adversaries.
- `honestLdtResponse`: for each repetition interpolates its own ILDT values
  plus the challenge-weighted data-row values. It uses neither the context's
  constraint system nor the later constraint challenge.
- `viewLeaves`: returns the view's column only at the queried positions and
  `none` elsewhere. The finite search is unique because the query is injective;
  an empty query exposes no columns.
- `Setup.mk`: adds the mask agreement threshold, list size and the proved
  arbitrary-mask list conditions to the shared tableau setup.
- `Parameters`: keeps k ≤ A, the code's line certificate and the arbitrary-mask
  list hypotheses as parameter facts. It does not assume a cheating word is a
  codeword or that an accepting transcript has an extracted witness.
- `Input`: includes context, actual oracle commitment and complete commit
  rounds, with all repetition indices; no witness is supplied as proof input.
- `verdict`: runs the actual Bool tableau acceptance on committed rows/masks,
  recorded low-degree challenges/responses and the three proof-phase entries.
- `commitProve`: supplies all N commitment leaves, their inverse encoding,
  concrete extractor, two commit rounds and three proof rounds. Its read
  congruence uses equality of queried columns and both mask values; it does not
  drop a verifier check or grant access to unqueried data.
- `Claim`: the commit exceptional event OR row/product satisfaction at the
  named extracted cells. The exceptional disjunct is explicitly charged by the
  commit error; it is not silently assumed absent.
- `Bad`: the selected constraint-list event on the pinned rows and arbitrary
  masks, using the derived mask-code rate. The selection depends on whether a
  linear constraint fails, rather than choosing after the challenge.
- `testAccept`: the same tableau verifier with masks made explicit for the
  two-stage analysis; it retains the low-degree response from the commit phase.
- `test_count`: bounds the bad constraint challenges by l/|F| for every fixed
  input and arbitrary mask. The positive field cardinality justifies division.
- `query_count`: for a false claim and a nonbad constraint challenge, bounds
  acceptance for every masked response. In the small common-agreement case it
  uses (A-1) descending factorial t; in the large case pinned-row agreement and
  the selected mask test give a descending factorial t. Their sum is divided
  by the full injective-query count, justified by t ≤ N.
- `testProof`: assembles the two-stage round proof from those two counts; its
  noncomputability belongs to proof/error data and is not a simulator.
- `sound`: fixes the already committed masks when dropping the analytical mask
  round, retains the same Bool verdict by reflexivity, and matches its claim
  using the event-occurrence equivalence. It charges the repeated commit event
  and both proof errors explicitly.
- `viewOf`: reassembles queried leaves and both transcripts from the simulated
  tableau view, retaining the original low-degree and constraint challenges.
- `simulate`: runs the named tableau simulator on public context, actual
  challenges, query and explicit simulator coins, then `viewOf`. It has no
  witness argument and remains a computable definition.
- `honest`: supplies the placement's named commitment/rounds/prover, explicit
  admissibility, all-coins/all-challenges completeness, and hiding against the
  separately named `honestSim`. Hiding uses admissibility and row satisfaction
  only for the honest input. This bundle remains noncomputable through the
  existing admissibility-dependent cell construction; the audit does not
  certify compliance with the separate runtime computability goal or add an
  exception for it.

## Boundary and scope checks

A positive repetition count is present wherever repetition zero represents the
shared tableau. Outside the all-exceptional event, a good repetition supplies
agreement for the data rows; repetition zero's own check reconstructs its ILDT
row on the common set. Thus no unproved selection of a good repetition enters
the extractor. The first-k selection is justified by k ≤ A ≤ set cardinality.
Distinct query sampling is reflected by descending factorial counts, not a
with-replacement power. Bounds can be uninformative for degenerate parameters
such as t=0, but the statement does not incorrectly claim a strict security gain
there. Parameter facts and honest privacy conditions remain explicit.

This change updates the audit ledger and report only. It changes no protocol,
headline, hypothesis, distribution or trust exception. Final-head closure
reconciliation and the strict computability gate remain separate obligations.
