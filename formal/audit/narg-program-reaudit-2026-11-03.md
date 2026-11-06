# NARG program re-audit, 2026-11-03

Scope: seventeen declarations at source commit `fa2516fd5`.

| Declaration | Previous fingerprint | Reviewed fingerprint |
|---|---:|---:|
| `GordieHowe.OracleProg.iterate` | 5889835611545010158 | 4672151428479369728 |
| `GordieHowe.OracleProg.mapQuery` | 13208801036822885445 | 15236665192758184042 |
| `GordieHowe.OracleProg.tabulate` | 9761083380981861593 | 15429429923316858733 |
| `GordieHowe.OracleProg.translate` | 11324651001912709611 | 16492707073936566040 |
| `GordieHowe.NARG.Prover` | 479739594 | 2512274476 |
| `GordieHowe.NARG.Prover.coins` | 3272848108430414632 | 14375591670973623404 |
| `GordieHowe.NARG.Prover.comap` | 849064567286795636 | 5880270810001884071 |
| `GordieHowe.NARG.Prover.mk` | 199537987 | 1564821501 |
| `GordieHowe.NARG.Prover.prog` | 7290282832146575817 | 15368612478816189894 |
| `GordieHowe.NARG.Prover.q` | 14392828402108833735 | 11979379966833837127 |
| `GordieHowe.NARG.Simulator` | 3180220209 | 2661034683 |
| `GordieHowe.NARG.Simulator.coins` | 12901929072317920120 | 12683435913644179486 |
| `GordieHowe.NARG.Simulator.coins_nonempty` | 1480758308 | 2774250735 |
| `GordieHowe.NARG.Simulator.comap` | 146607751770543645 | 15753571411189072537 |
| `GordieHowe.NARG.Simulator.mk` | 2267554572 | 2937069542 |
| `GordieHowe.NARG.Simulator.prog` | 4123538471274285867 | 241689492686852971 |
| `GordieHowe.NARG.Simulator.q` | 2995388411712105874 | 15396154733876912567 |

## Historical identity

The original audit is `1641c27f`, closure audit C65. The current program
structures descend from `Quantum.NIZK.ProverProg` and `SimulatorProg`, then
`QROM.ProverProg` and `SimulatorProg`. Pass P5 (`88a4fb37b`) explicitly maps
those names to `NARG.Prover` and `Simulator`, while mapping the earlier
function-valued `NARG.Prover` and `Simulator` to `ProverFn` and `SimulatorFn`.
Following a current name backwards without that distinction selects the wrong
object. Every one of the thirteen recorded program-form fingerprints was
matched at its actual old name in `3761d930` or `f01311529`.

The four combinators were originally in `BCS/Chain/ZeroKnowledgeProg.lean`
(mapQuery, tabulate, iterate) and `BCS/SimExtract/Lemmas.lean` (translate).
Their recursive equations match the current equations after namespace changes.
This review also checks current behavior; ancestry alone is not an audit.

## Oracle programs

`OracleProg.mapQuery` leaves a pure result unchanged. Each old query `a`
becomes exactly one query `f a`, and its answer is passed through `g` before
continuing. The maps need not be injective: the simulation is against the
composed oracle `g ∘ h' ∘ f`, not a claim that two different queries remain
independent. The run and trace lemmas state exactly that composed semantics,
and trace length is unchanged for that run.

`OracleProg.translate` similarly emits one query `ι a`, but decodes its answer
with `g a`, retaining the original query in the decoder. It does not execute an
arbitrary answer-supplying program. The pure case emits no query, and the
recursive case neither drops nor duplicates a query. No injectivity or
randomness-preservation claim is implicit in this combinator.

`OracleProg.tabulate` runs the head program before the tail programs and then
updates the returned function at the head index. The empty list returns the
supplied default without querying. Duplicate indices still execute each
occurrence and are counted separately; against a fixed oracle they return the
same value, so the membership-based run lemma is valid without a nodup premise.
Outside the list the result is the default. Equality on indices is the explicit
`DecidableEq` parameter. The length lemma sums over the list, including repeats,
so it does not undercount repeated queries.

`OracleProg.iterate` returns the initial state at zero and executes step `m`
after the first `m` steps in the successor case. Thus a run of length `m` uses
indices zero through `m-1`, each on the preceding result. The query bound sums
per-step bounds over exactly `Finset.range m`; it assumes each step bound at
every state, not merely at the initial state. These four definitions introduce
no validity assumption on an adversary and do not select a favorable oracle.

Disposition: all four combinator entries pass recursion, boundary and query
accounting review.

## Prover and its fields

`NARG.Prover` stores a program of statement, witness and coins, a PMF on those
same coins, a natural query budget, and a proof of that budget for every input.
The original structure used `Type`; the current one permits independent
universes with `Type*`. The explicit bound on every oracle trace is now named
`OracleProg.QueriesLE`; unfolding that predicate gives the same universal
static-oracle bound. This is not a bound over arbitrary inconsistent answer
sequences. Quantum execution and its operational obligations are separate.

`Prover.mk` requires all four fields, including the universal bound proof; it
cannot manufacture a bound for a program that lacks one. `Prover.prog`,
`coins` and `q` are the corresponding projections, with the same parameter
order and no substituted program, distribution or budget.

`Prover.comap` changes only the statement and witness supplied to the stored
program. It forwards the exact PMF and budget and specializes the existing
bound proof to the mapped inputs. Neither map needs to be surjective, because
this definition makes no security or completeness claim about a transported
relation. Such claims must state their relation separately. No coins are
resampled or conditioned by comap.

Disposition: the structure, constructor, three projections and comap pass.
This semantic review does not certify efficient construction of an arbitrary
stored PMF. The existing PMF/runtime separation issue remains outside this
ledger update and is not waived by it.

## Simulator and its fields

`NARG.Simulator` stores a program of statement and coins, a proof that the coin
type is nonempty, a natural budget and the corresponding universal static-oracle
trace bound. Its result is a proof plus an assignment list. There is no witness
argument. The universe generalization and named query predicate have the same
meaning as for the prover.

`Simulator.mk` requires all those fields; `prog`, `coins_nonempty` and `q`
project them unchanged. In particular `coins_nonempty` is a proposition, not a
chosen seed. It prevents a uniform experiment from being defined over an empty
coin space without placing a restriction on adversary behavior.

`Simulator.coins` uses the supplied finite instance and the stored nonemptiness
proof to define `PMF.uniformOfFintype`. It does not choose one favorable coin,
weight the distribution by the statement, or depend on the assignment list.
It is explicitly noncomputable mathematical probability data, separate from
the program field. This audit does not assert that a PMF is executable sampling
code or create a computability exception.

`Simulator.comap` feeds only the mapped statement to the original program,
forwards nonemptiness and the budget, and specializes the query proof. The
proof, assignment list and coin space remain those of the original run. This
combinator does not bound assignment-list length by itself or prove polynomial
running time; those obligations belong to the concrete simulator and the
separate cost review. There is no hidden witness or conditioned distribution.

Disposition: the structure, constructor, three projections, coin-law definition
and comap pass the stated semantic review.

## Validation scope

All seventeen current own fingerprints match both the tracked closure and the
completed combined environment. The three reviewed source modules are identical
to that compiled snapshot. No Lean source, hypothesis, distribution or detector
exception changes. Only these individually reviewed ledger rows and this report
change; final-head closure reconciliation remains required.
