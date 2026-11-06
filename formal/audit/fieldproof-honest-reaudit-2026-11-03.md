# Field-proof honest interfaces and simulation re-audit, 2026-11-03

Scope: 29 declarations at source commit `c19b86831`.

| Declaration | Previous fingerprint | Reviewed fingerprint |
|---|---:|---:|
| `GordieHowe.FieldProof.Honest` | 732801233 | 4089984570 |
| `GordieHowe.FieldProof.Honest.Coins` | 2451471019 | 1825237139 |
| `GordieHowe.FieldProof.Honest.Coins.blinding` | 6808684016441238862 | 15166757064639409996 |
| `GordieHowe.FieldProof.Honest.Coins.mk` | 741525536 | 1157142567 |
| `GordieHowe.FieldProof.Honest.Coins.pads` | 12867463680065471614 | 2011284671784843390 |
| `GordieHowe.FieldProof.Honest.cells` | 17320049412779811502 | 1726736221116933423 |
| `GordieHowe.FieldProof.Honest.coinsEquiv` | 16580407075462788243 | 10330026834322811021 |
| `GordieHowe.FieldProof.Honest.commit` | 10624469310124826852 | 17239842154464957276 |
| `GordieHowe.FieldProof.Honest.commitRounds` | 2599981274733225988 | 7639135565234295075 |
| `GordieHowe.FieldProof.Honest.cp` | 10749507486357019313 | 815517008750777083 |
| `GordieHowe.FieldProof.Honest.ip` | 16155445599825800098 | 7860796858558791493 |
| `GordieHowe.FieldProof.Honest.mk` | 286241301 | 2622388047 |
| `GordieHowe.FieldProof.Honest.prove` | 7045750296228423282 | 9046840004568904725 |
| `GordieHowe.FieldProof.Honest.rounds` | 1576352904676524765 | 4308191861003270371 |
| `GordieHowe.FieldProof.Honest.toShape` | 2684979728689951151 | 17763577922670695194 |
| `GordieHowe.FieldProof.instFintypeCoins` | 1520964038254670049 | 2927736575043908584 |
| `GordieHowe.FieldProof.instFintypeSimCoins` | 17839787767625208985 | 1129693101467185271 |
| `GordieHowe.FieldProof.instNonemptyCoins` | 1267013698 | 4075128971 |
| `GordieHowe.FieldProof.instNonemptySimCoins` | 3725623838 | 3418078721 |
| `GordieHowe.FieldProof.simulator` | 12173929325875669368 | 7821608310242874029 |
| `GordieHowe.FieldProof.CommitProve.Honest` | 2785768597 | 1257503226 |
| `GordieHowe.FieldProof.CommitProve.Honest.Admissible` | 12337578086103632151 | 5044469814028420712 |
| `GordieHowe.FieldProof.CommitProve.Honest.Coins` | 8072634043322374528 | 10593782644801330949 |
| `GordieHowe.FieldProof.CommitProve.Honest.commit` | 5721781244234591723 | 9136635908334791836 |
| `GordieHowe.FieldProof.CommitProve.Honest.commitRounds` | 5575069215386910337 | 12750062043472652360 |
| `GordieHowe.FieldProof.CommitProve.Honest.fintype` | 17745815826080776654 | 740062691749041437 |
| `GordieHowe.FieldProof.CommitProve.Honest.mk` | 1952016993 | 3635105267 |
| `GordieHowe.FieldProof.CommitProve.Honest.nonempty` | 469805607 | 2133441813 |
| `GordieHowe.FieldProof.CommitProve.Honest.prove` | 15661007661974671978 | 9200808962850062605 |

Reviewed `FieldProof/Basic` at `407240beb` and `f01311529`, and `CommitProve` at
`f01311529`, against current source. The relevant historical change extracts simulator
coins and code into explicit `Sim` data and indexes honest correctness by that fixed
simulator. Current source bytes and all29 fingerprints match the compiled acceptance
closure. This report does not claim byte identity with the historical interfaces.

For `FieldProof`:

- `Honest` requires both component honest provers at the fixed simulator, actual
  cells, their commitment proof and admissibility. Cells depend on the honest
  input and pads, not the public input or future verifier challenges.
- `Honest.mk` retains all those data and proofs. No default proof of commitment,
  admissibility or distribution equality is synthesized by the constructor.
- `Honest.ip` selects the masked-row honest prover simulated by `S.ip`.
- `Honest.cp` selects the commit-and-prove honest prover simulated by `S.cp`.
- `Honest.cells` projects the actual precommitted cells. Correctness at the honest
  domain is separately required, so a vacuous commitment predicate cannot imply
  acceptance of a supplied valid input without its commitment proof.
- `Honest.Coins` pairs the masked-row pads and commit-system blinding, retaining
  both random sources. It does not substitute one for the other or reuse their bits.
- `Honest.Coins.mk` constructs exactly that pair from supplied components.
- `Honest.Coins.pads` returns the original masked-row pads.
- `Honest.Coins.blinding` returns the independent commit-system coin component.
- `Honest.coinsEquiv` is the direct pairing/unpairing equivalence, with both inverse
  laws by reflexivity. Under the transported finite uniform distribution this is
  the product of the two component uniform distributions.
- `instFintypeCoins` transports the entire finite product through that equivalence;
  no coin values are filtered.
- `instNonemptyCoins` derives inhabitance from the same pair and component
  nonemptiness, rather than assuming existence of a successful proof.
- `Honest.commit` commits the cells computed with the pads using the blinding
  component, with no context or challenge argument.
- `Honest.commitRounds` uses those same cells and blinding to build a causal
  commit-phase transcript; it is not supplied the future challenge vector.
- `Honest.rounds` evaluates that causal transcript on the supplied commit challenges.
- `Honest.prove` first runs the masked-row prover, then passes the actual resulting
  transcript with the public input as the commit-and-prove context. The second
  prover receives the same cells, blinding and commit rounds. The causal append
  preserves that order and does not permit the first prover to read the later phase.
- `Honest.toShape` forwards the same coins, commit, commit rounds and proof function
  to the computational shape. It inserts no new acceptance condition or randomness.
- `instFintypeSimCoins` enumerates the product of the two named simulator coin
  spaces, transported through `Sim.simCoinsEquiv`; it no longer depends on an
  honest prover's hidden implementation.
- `instNonemptySimCoins` derives nonemptiness of that product from the two simulator
  bundles. This is not an existentially selected simulator.
- `simulator` runs `S.ip.sim` on the public input and first-phase challenges, then
  `S.cp.sim` at the context containing that simulated transcript, using the other
  coin component and the corresponding challenges. It assembles the queried leaves,
  commit rounds and complete joined transcript. It has no honest-input or witness
  parameter and preserves correlation between the two phases. The existing HVZK
  proof uses dependent distribution composition, not an unjustified independent
  product of the output views.

For `FieldProof.CommitProve`:

- `Honest` retains finite nonempty prover coins, pre-context commitment and causal
  commit rounds, the proof function, admissibility, universal completeness and
  perfect hiding at the supplied named simulator. Moving simulator data out does
  not delete its distribution obligation.
- `Honest.mk` requires both correctness laws for the supplied data; the simulator
  is fixed as a parameter rather than chosen by an unrestricted existence proof.
- `Honest.Coins` is the prover's blinding space and is distinct from simulator coins.
- `Honest.fintype` supplies enumeration of that whole coin space.
- `Honest.nonempty` supplies its inhabitance, ensuring the uniform law is meaningful;
  it does not assert any input is admissible.
- `Honest.commit` reads cells and coins only, so commitment is fixed before context.
- `Honest.commitRounds` likewise builds a causal transcript from cells and coins.
- `Honest.prove` receives the context and already supplied commit rounds, plus the
  same committed cells and coins, and returns a causal proof-phase transcript.
- `Honest.Admissible` is the explicit honest-cell predicate. Completeness and hiding
  require it together with all linear/product rows via `Admits`. The laws quantify
  over every such fixed cell vector and every challenge vector; they do not discard
  bad coins. Admissibility is not a restriction on adversaries in the separate
  soundness model. An empty admissible set would make these generic honest laws
  vacuous, so actual instantiations must prove admissibility of their honest cells.

The separate perfect-simulation proof combines the masked-row law with hiding at each
fixed padded cell assignment. It retains complete views rather than only marginal
outputs. No new hypothesis, distribution, runtime marker or exception is introduced
by this audit-only update; historical simulator separation is reviewed explicitly.
