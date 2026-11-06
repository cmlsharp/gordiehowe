# QROM game re-audit, 2026-11-03

Scope: 5 declarations at source commit `37e0dc823`.

| Declaration | Previous fingerprint | Reviewed fingerprint |
|---|---:|---:|
| `GordieHowe.QROM.BaseGame` | 14419615514034380524 | 3945113386102470204 |
| `GordieHowe.QROM.simProb` | 3963739757733715773 | 1631790659833217256 |
| `GordieHowe.QROM.realEnv` | 7748187751089860600 | 4032173234246320082 |
| `GordieHowe.QROM.simEnv` | 3348045960726836084 | 10821791123842921892 |
| `GordieHowe.QROM.tapeDist` | 5578392783967954629 | 2243235856953732796 |

## Base-game representation

`QROM.BaseGame` at the last matching snapshot `3688cc383` was a set of
nested triples `(Fin k → A) × (Fin k → B) × C`. It is now a set of the named
`BaseGame.Tuple A B C k`, whose three fields are the queries, claimed answers
and output. No validity or distinct-query premise was added to that tuple.
In particular repeated queries and inconsistent claimed answers remain
representable; the separate `AnsweredBy` and `InDB` predicates reject their
inconsistencies when the relevant win event requires them. At `k=0`, a base
game is still meaningful; the lemma excluding the empty database explicitly
requires `0 < k` instead of assuming a query exists.

Disposition: the abbreviation passes representation and boundary review.
It names a set of possible outputs, not a promise that every tuple is answered
by an oracle or stored in a database.

## Output/database event

`QROM.simProb`, compared with the source at `f01311529`, applies the same
`simLaw e A` to the event `R p.1.out p.2`. The first argument of R is the
actual adversary output field, and the second is the database from that same
joint measured outcome. It does not replace the output by a favorable
existential choice or combine the marginals independently. It also does not
implicitly intersect with `winS` or an oracle-consistency event: R is the
complete event supplied by the caller. For an output-independent R this is
the database marginal, and the existing zero-event, monotonicity and disjunction
lemmas match these event semantics. This declaration is probability data; it
is not an implementation of an executable simulator.

Disposition: the event selector passes the output-correlation review. This
row does not independently re-audit the complete quantum lifting theorem.

## Tape distribution

The three environment definitions were last matched at `54b23c22b`, in
`PQ/Quantum/NIZK.lean`. `QROM.tapeDist` still draws a uniform function `X → Y`,
then draws a product of Q copies of the supplied PMF and pairs them with that
function. The second law does not depend on the sampled function, so the
initial oracle and the per-request coins are independent. The input PMF need
not be uniform; the real game retains exactly the prover's law. The simulated
game supplies the simulator's uniform law separately. `Fin Q` prevents
out-of-budget indexing; when Q is zero its function space is a singleton,
not an empty probability space. Finiteness of X and Y and nonemptiness of Y
supply a finite nonempty oracle space, including when X is empty.

Disposition: the tape law passes independence, distribution and zero-budget
review. No distribution is changed by this audit.

## Real and simulated environments

`QROM.realEnv` initializes the oracle from the tape and, for a valid request,
returns the prover's result on the current oracle, requested statement and
witness, and the coins at that request index. An invalid request returns none.
Both branches return the same oracle they received. Thus repeated real
responses preserve the initial oracle, while the definition also behaves
correctly when called as a response function at an explicitly supplied oracle.
The request's old pair projections became the named `ProofQuery.stmt` and
`wit` fields. The old function-valued prover is now named `NARG.ProverFn`;
it has not been replaced by a program with a different coin law.

`QROM.simEnv` tests exactly the same relation on the request. On success it
calls the simulator with the current oracle, the statement and that request's
coins, without passing the witness. The witness is read only by the common
validity test. It returns the simulator's proof and reprograms the current
oracle using the simulator's actual assignment list. Reprogramming is a
left fold of updates, so later duplicate assignments take precedence and an
empty list preserves the oracle. On failure it returns none and leaves the
oracle unchanged; it does not run the simulator or apply assignments in that
branch. The old pair-valued result became the named proof/assignments record,
and the old function-valued simulator is now `NARG.SimulatorFn`.

The relation check is part of the stated proof-query game in both experiments,
not a new premise asserting that adversaries only submit valid requests. It
can make a particular game uninformative when its relation is empty, but these
definitions alone do not assert zero knowledge for an unspecified relation.
The shared finite request budget and initial tape are unchanged. The enclosing
quantum environment stores mathematical PMFs and is noncomputable; this review
does not certify it as runtime code or add an exception for concrete provers
or simulators.

Disposition: both environments pass the branch, witness-access, oracle-update
and coin-index review.

## Validation scope

The five own fingerprints match both the tracked closure and the completed
combined environment. Both reviewed source modules are identical to that
compiled snapshot. Only the five ledger rows and this report change; final
closure reconciliation and separate runtime acceptance remain required.
