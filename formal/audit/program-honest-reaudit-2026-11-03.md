# Program honest composition review, 2026-11-03

Scope: 38 declarations at source commit `c674ef684`.

| Declaration | Previous fingerprint | Reviewed fingerprint |
|---|---:|---:|
| `GordieHowe.RealizedProgram.ProofSystem.PhaseStep.AvoidsEvents` | 4067612068893118663 | 10556981554084308748 |
| `GordieHowe.RealizedProgram.ProofSystem.PhaseStep.Honest` | 1855217889 | 1726940665 |
| `GordieHowe.RealizedProgram.ProofSystem.PhaseStep.Honest.Avoids` | 18219966950004630811 | 15704265167759257683 |
| `GordieHowe.RealizedProgram.ProofSystem.PhaseStep.Honest.Pads` | 1245144746836232470 | 8031497271815925442 |
| `GordieHowe.RealizedProgram.ProofSystem.PhaseStep.Honest.bad` | 2603660204079516352 | 3995280243107660037 |
| `GordieHowe.RealizedProgram.ProofSystem.PhaseStep.Honest.fintype` | 6480686402656133158 | 8795375919691278034 |
| `GordieHowe.RealizedProgram.ProofSystem.PhaseStep.Honest.mk` | 44885939 | 2881825020 |
| `GordieHowe.RealizedProgram.ProofSystem.PhaseStep.Honest.prover` | 7649785155433541668 | 5029113490099928801 |
| `GordieHowe.RealizedProgram.ProofSystem.PhaseStep.Honest.wit` | 16565762448413141502 | 3689043588317516130 |
| `GordieHowe.MultiCircuitIOP.Honest` | 1463982789 | 1883067955 |
| `GordieHowe.MultiCircuitIOP.Honest.Coins` | 9896552577373144085 | 384997416497751517 |
| `GordieHowe.MultiCircuitIOP.Honest.In` | 6268026378849442739 | 5379428245023893874 |
| `GordieHowe.MultiCircuitIOP.Honest.app` | 11274298166658357361 | 2103863212645515566 |
| `GordieHowe.MultiCircuitIOP.Honest.circuit` | 6328680185323561619 | 2379184959890090419 |
| `GordieHowe.MultiCircuitIOP.Honest.dom` | 11300852154238945250 | 17662647638539921908 |
| `GordieHowe.MultiCircuitIOP.Honest.mk` | 2881862444 | 1926440046 |
| `GordieHowe.MultiCircuitIOP.honest` | 11168615833191270702 | 13586213789684158926 |
| `GordieHowe.MultiCircuitIOP.simulator` | 16436792110012434862 | 14221891631264443356 |
| `GordieHowe.RealizedProgram.ProofSystem.PhaseStep.Coins` | 4035683648 | 4033975367 |
| `GordieHowe.RealizedProgram.ProofSystem.PhaseStep.Coins.circuits` | 15534441443668382457 | 4300317984230171928 |
| `GordieHowe.RealizedProgram.ProofSystem.PhaseStep.Coins.mk` | 104600897 | 1298181042 |
| `GordieHowe.RealizedProgram.ProofSystem.PhaseStep.Coins.pads` | 3874504944071903124 | 7083990649505406836 |
| `GordieHowe.RealizedProgram.ProofSystem.PhaseStep.coinsEquiv` | 9196369219300075586 | 4796014617502303516 |
| `GordieHowe.RealizedProgram.ProofSystem.PhaseStep.committedFamily` | 7610367921434189444 | 1378699389243867401 |
| `GordieHowe.RealizedProgram.ProofSystem.PhaseStep.fullFamily` | 13008508074608232257 | 6190852491545853168 |
| `GordieHowe.RealizedProgram.ProofSystem.PhaseStep.fullHonest` | 10127805739143558246 | 12036169782953644889 |
| `GordieHowe.RealizedProgram.ProofSystem.PhaseStep.fullSimulator` | 18446406617289812157 | 770774573530733936 |
| `GordieHowe.RealizedProgram.ProofSystem.PhaseStep.instFintypeCoins` | 13285543253699372335 | 13763153490631345338 |
| `GordieHowe.RealizedProgram.ProofSystem.PhaseStep.instNonemptyCoins` | 3212085415 | 1640511469 |
| `GordieHowe.RealizedProgram.ProofSystem.Phased.Honest.bad` | 16009948140939293247 | 11810217599229626079 |
| `GordieHowe.RealizedProgram.ProofSystem.Phased.Honest.mk` | 3689238299 | 1377890550 |
| `GordieHowe.RealizedProgram.ProofSystem.Phased.Honest.toAppHonest` | 11343200442676508876 | 15464509884407474513 |
| `GordieHowe.DomainProof.Honest` | 243464110 | 844652206 |
| `GordieHowe.DomainProof.Honest.In` | 15559812629177443351 | 12473689336474127392 |
| `GordieHowe.DomainProof.Honest.circuit` | 16345219723480338367 | 5725479118473518944 |
| `GordieHowe.DomainProof.Honest.dom` | 6397659849006312647 | 12439263157012913643 |
| `GordieHowe.DomainProof.Honest.encode` | 17041888684465413016 | 18254691219970113389 |
| `GordieHowe.DomainProof.Honest.mk` | 4224015732 | 461590723 |

## Method and change classification

Reviewed the current application-phase, phased, multi-circuit, and domain honest
interfaces, their constructors/projections, actual transcript assembly, and named
simulator assembly. Historical comparisons use `AppPhase`, `Basic`, and `System`
at `f01311529`, the earlier application events at `5831d8fbc`, and phased honesty
at `4cd3a9bb1`. Current fingerprints and source bytes are checked against the
compiled review snapshot before updating the ledger.

Two substantive historical changes must not be described as mere renaming:
completeness events now may depend on the entire challenge vector, and named
simulator data has been separated from honest-law records. The former retains
uniform conditional bounds for every setting of the other challenges, and a
bound on the union event. The latter keeps explicit equal-law obligations against
the named simulator. Neither supplies an existential simulator for free.

## Application-phase entries

Names in this section are relative to
`GordieHowe.RealizedProgram.ProofSystem.PhaseStep`.

- `AvoidsEvents`: universally excludes each indexed completeness event at the full
  challenge vector; an empty challenge index gives the expected empty conjunction.
  It is an honest-completeness premise, not a restriction on adversarial behavior.
- `Honest`: provides finite nonempty precommitment pads, circuit inputs, a causal
  transcript family, event predicates, acceptance and circuit-domain obligations
  off the events, and the transcript law at every challenge vector on `relI`.
  Bad events must subsequently be charged; this record alone supplies no small error.
- `Honest.mk`: requires all those obligations, including the named simulator's
  equality in distribution. A false `relI` would make a generic honest-law instance
  vacuous, so concrete use must supply related inputs; no arbitrary-relation
  nonvacuity is inferred here.
- `Honest.Pads`: the prover's randomness chosen before commitment, not challenges.
- `Honest.fintype`: enumerates those exact pads for uniform sampling.
- `Honest.wit`: constructs every circuit's input from honest input and pads,
  without reading future public challenges.
- `Honest.prover`: returns a causal transcript family. Access to the full challenge
  vector in the separate event predicates does not permit future-dependent messages.
- `Honest.bad`: may read all challenges but has a distinguished charged round.
  `BadBound` quantifies over every fixing of the other challenges; `ErrorBound`
  bounds the union directly. An always-true event cannot yield a small error bound.
- `Honest.Avoids`: exactly applies `AvoidsEvents` to the record's events; it does not
  select only some rounds or replace an event by its complement incorrectly.

## Phased entries

Names are relative to `GordieHowe.RealizedProgram.ProofSystem.Phased`.

- `Honest.bad`: has one event per `Fin K` phase and reads the complete phase
  challenge tuple. Its historical one-coordinate form was deliberately generalized.
- `Honest.mk`: retains challenge causality, strict pad dependency order, and
  acceptance/domain proofs outside all phase events. The generalized event field
  does not remove either causality obligation.
- `Honest.toAppHonest`: preserves the circuit inputs and pads, constructs the
  transcript from `honestRun`, and assigns event `k` to precisely `L.chalIdx k`.
  Injectivity of that index mapping and the characterization theorem prevent
  missing or double-counted phase events. `PadOrder.uniform` establishes the law
  of the named uniform-message simulator at fixed challenges. With zero phases,
  the event quantification is empty and the same construction remains meaningful.
  The error transport uses uniform restriction to phase challenges; failures are
  charged rather than removed from the sample space.

## Coin and transcript assembly entries

Names are relative to `GordieHowe.RealizedProgram.ProofSystem.PhaseStep`.

- `Coins`: pairs the application pads with the full dependent family of circuit coins.
- `Coins.mk`: requires both components; there is no shared-coin substitution.
- `Coins.pads`: reads the application component.
- `Coins.circuits`: reads every circuit's coin component.
- `coinsEquiv`: is the direct product equivalence, with both inverses by reflexivity.
- `instFintypeCoins`: transports the product enumeration through that equivalence;
  it does not filter a subset of coins.
- `instNonemptyCoins`: transports product nonemptiness, ensuring uniform sampling
  has an inhabited space without choosing a computational default here.
- `committedFamily`: sends the complete circuit commitment first, then its honest
  commit rounds, then the application transcript using the already fixed pads.
  The application does not alter the committed circuit inputs after challenges.
- `fullFamily`: appends all circuit proofs to that prefix, using the public inputs
  and commit rounds read from the actual prefix. Causal append exposes only the
  available prefix to the later family.
- `fullHonest`: realizes exactly `fullFamily` as a prover. Its existing
  `noncomputable` marker and the challenge-default dependency are unchanged from
  the historical source. This semantic review does not certify executable code
  for it or waive the separately recorded runtime repair.
- `fullSimulator`: uses product coins for the named application simulator and the
  circuit simulator family, derives circuit public inputs from that same simulated
  application transcript, and assembles the complete view. Commit and proof-phase
  challenges use their respective projections. Re-evaluating the application
  function with identical coins is deterministic; it is not a second random draw.
  The dependent composition proof uses domain obligations off the charged events,
  rather than assuming independent views with dependent public inputs.

## Multi-circuit entries

Names are relative to `GordieHowe.MultiCircuitIOP`.

- `Honest`: ties each honest circuit input/domain and the application honest phase
  to the corresponding component of named `SimData`.
- `Honest.mk`: requires the application record and every circuit record, so one
  missing circuit proof cannot silently be replaced by a vacuous default.
- `Honest.In`: the circuit-indexed input types.
- `Honest.dom`: each circuit's honest-input domain at its public input. These are
  completeness conditions, not restrictions on cheating witnesses in soundness.
- `Honest.app`: the application honest record establishes each domain off its events.
- `Honest.circuit`: supplies honest completeness and simulation for every circuit
  on those domains, using the selected simulator component.
- `Honest.Coins`: aliases the same application/circuit coin product, retaining all
  circuit indices and distributions.
- `honest`: delegates to the exact `fullHonest` family with each circuit's honest
  shape. Its inherited noncomputability is explicitly retained, not cured by this
  audit; no new marker or exception is introduced.
- `simulator`: assembles `SimData.app` and every `SimData.circuit` through
  `fullSimulator`. It does not depend on a secret honest input or an existential
  soundness witness. The simulator remains a named computational definition.

## Domain entries

Names are relative to `GordieHowe.DomainProof`.

- `Honest`: links the domain's cells, named honest predicate, input encoding, and
  circuit honest proof at the named simulator.
- `Honest.mk`: requires the encoding-domain implication and the circuit honest
  record, not just a chosen encoding.
- `Honest.In`: the circuit's actual honest input type.
- `Honest.dom`: its honest domain, indexed by the circuit public input.
- `Honest.encode`: maps the committed cells to that input type without a claim of
  injectivity that downstream completeness does not need.
- `Honest.circuit`: the supplied honest circuit record on exactly this domain and
  simulator. `dom_of` proves it applicable whenever `hpred` holds; arbitrary false
  domains cannot be used to prove completeness of an actually supplied honest input.

## Outcome and limits

These 38 entries pass the current semantic and historical-change review. The two
existing noncomputable prover wrappers remain a separately tracked runtime concern;
this audit is not a CostLint exception or a claim that the strict runtime gate passes.
No production source, headline, distribution, or hypothesis is changed. Final-head
closure reconciliation remains required after the implementation streams land.
