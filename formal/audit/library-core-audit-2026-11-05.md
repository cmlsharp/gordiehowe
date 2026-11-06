# Library core audit, 2026-11-05

Scope: new closure declarations of the library core at source commit `c9a2dabc0`: the program
conditions, the certified and runtime interfaces, the field registry, the program data descriptors,
the packing descriptor, the Johnson certificate arithmetic, the fields' code arithmetic, the source
role library, the P-256 curve constants and `SPBCS.simVerifier`. Frontends still being migrated are
excluded. This report records 167 definitions read individually and 140 rows that are shallow by
nature. It compares definitions with their names, docstrings and the certificate design, and
evaluates hypotheses at the generated programs' numbers. Lean was not run for it.

Fingerprints come from the tracked `statement_closure.txt`, last regenerated at `c1e6c8a1c`. Every
source module of these rows is byte-identical between `c1e6c8a1c` and `c9a2dabc0`. The next closure
regeneration must reconcile them.

## Findings

No row has a semantic defect, and no hypothesis of the reached interfaces is vacuous at a program
that uses it. Open items, none affecting a current headline:

- `Export.Plan.opaqueSet` (`GordieHoweNative/Language/Export.lean:669`) is read by nothing, and no
  check compares it or the arguments of opaque values with the field table's `OpaqueKey`. A descriptor
  `.none` gives every opaque value with arguments the constant `0` read through `decode`, and its
  `OpaqueBit` fact holds trivially, so a wrong key would change a program's meaning unchecked. All 32
  programs currently agree: the 32 plan tags equal the 32 keys, the 16 `.none` programs have no opaque
  value with arguments, and the argument-taking names are `mac.target_bits` in `.targetBits`
  programs; `mac.target_bits` and `key.coefficients` in `.falcon` programs; `device.e2_point`,
  `issuer.q_table` and `mac.target_bits` in the `.mdoc` program.
- The docstrings of `FieldTable.productFree` and `FieldTable.noFieldForm`
  (`GordieHoweNative/Language/ProgramData.lean:154-157`) state the property. The value `false` makes
  no claim: the 12 SHA programs have `noFieldForm := false`, and `NoFieldForm` and `NoProduct` are
  implications from the flags.
- The docstring of `CheckedConditions` (`GordieHowe/Applications/Program/Conditions.lean:390-394`)
  omits the challenge and pad orders, the roles, `noFieldForm` and the source roles.

## Hypotheses at real parameters

- `JohnsonDesc.Ok`: evaluated exactly at all 21 distinct generated Johnson descriptors with
  `N = blockEnc - (2 block - 1)`, `D = block - 1`. Each satisfies every clause, and each `exceptions`
  equals the ceiling of `johnsonWeightedRefinedExceptionCount`, so none is padded.
- `FieldOkAt`, `TableausFit` and `FiguresOk` quantify over proofs of an earlier condition, so taken
  alone each holds vacuously when that condition fails. Every reached use supplies the proof from the
  same structure: `ready` uses `h.fields i h.tableaus`, and `certifiedProgram` uses
  `h.figures h.toCoreConditions h.coded`.
- `CodedOk` is unsatisfiable for `MDL.ECDSA.ROMParams` (P-256 has no codec). That program is
  core-only: it proves no `coded` and has no `ProgramConditions`.
- `NoProduct` is vacuous at the 4 Carrier programs (`productFree := false`), where `SelSound` must be
  supplied separately through `proofSystemOf`. `NoFieldForm` is vacuous at the flag-false programs.
  Consumers apply them to `rfl`, which fails to elaborate at a false flag.
- `SourceRolesPartOk` is vacuous without a table. Consumers must prove `sourceRoles = some roles`.

## Declarations read

Names are relative to `GordieHowe` unless shown otherwise.

**Conditions.** `CoreConditions` and `ProgramConditions` hold the facts their consumers use.
`ProgramData.interp` is the field table's descriptor. `FieldOkAt` and `FieldsOk` state `fieldOkB` at
the program's domain field and the indexed tableau. `FieldTableOk` applies `RealizedProgram.FieldTable`
to the table's lengths and lookups. `RealizedProgram.FieldTable` has the five clauses `fieldTableB`
tests. `CircuitsOk` ranges over the program's circuits and includes the characteristic equation.
`NoProduct`, `NoFieldForm`, `CompletionOk`, `RolesOk` and `CodedOk` are as named. `ProgramData.TableausOk`
and `TableausOk.at` cover the list; past it the default is a library tableau, which `tableauFitB` still
compares with the plan. `tableauDesc` and `tableau` read that descriptor. `ReadersOk`, `FitsOk`,
`FiguresAt` and `FiguresOk` state the figures at ready data. `cod`, `fieldBytes`, `fieldReader`,
`chalLoadMax`, `samplerReaders`, `maxArray`, `maxRead`, `restRead`, `numbers` and `ready` assemble the
registry objects, with `nthOr` reading short lists as `0`. `ProgramData.circuitData` and `circuitCode`
read the supplied data and the table's field key. `CircuitData.sourceParts` is the layered circuit,
width and constants.

**Tableaus.** `JohnsonDesc`, `JohnsonDesc.shape` and `JohnsonDesc.Ok` are read with
`lineCertificate_of_weightedJohnson`: `D = block - 1`, `2 <= block <= agree <= N`, `B <= 2D + 1` and
the refined count. `JohnsonDesc.cert` passes these and fixes masking to `.split`, matching
`JohnsonDesc.nums`. `TableauDesc`, `TableauDesc.Ok` and `TableauDesc.cert` dispatch on the descriptor.
`TableauKey` and `TableauKey.cert` map keys to named certificates; the bodies of those certificates are
outside this report, and `cert_nums` ties them to the numbers. `ReedSolomon.HiddenDerivative.johnsonWeightedN`,
`johnsonWeightedW`, `johnsonWeightedR`, `johnsonWeightedT`, `johnsonWeightedSlope`,
`johnsonWeightedMoment`, `johnsonWeightedHeightInt`, `johnsonWeightedHeight` and
`IsJohnsonWeightedCertificate` match the formulas in their module docstring. They are hypotheses of a
proved line certificate, so an arithmetic error there could not produce an unproved bound.

**Descriptors.** `ProgramData`, `Hints`, `FiguresData`, `FieldTable`, `FieldTable.domainField`,
`FieldTable.circuitDomain`, `FieldTable.circuitField`, `InterpDesc`, `InterpDesc.key`, `FieldKey`,
`OpaqueKey` and `TableauDesc` are small data as the design states. `PackingDesc` is read with
`Packing.desc`, `fieldOkB_of_desc` and the checker: a missing edge, node or skip answers `false` or
`none`, which fails the check; mask queries are covered by `masksCoverB`, and duplicate keys are
harmless because every entry is checked against the packing.

**Registry.** `FieldKey.interp`, `FieldKey.packing`, `FieldKey.code` and `FieldKey.codec` dispatch to
named constants. Element sizes match the coefficient widths: `fq6` 18, `fq9` 18, `fq11` 32, `fq20` 35,
`gold2` 16, `gold4` 32. `FieldKey.name` matches all nine names in `lib/gordiehowe/compiler/field_registry.h`.
`FieldKey.Coded` excludes only P-256. `OpaqueKey.fn` dispatches; a value with no arguments reads the
statement (`Semantics.lean:512-514`), so `.none` affects only values with arguments. `InterpDesc.interp`,
`Interp.twoField` and `Interp.twoFieldAt` place field `0` and every other identifier as documented.
`InterpDesc.provide`, `provideOn`, `packing`, `codec`, `bytes`, `reader`, `card` and `Coded` follow the
same cases.

**Code arithmetic.** `GKR.Fold.primeArith`, `undigits`, `ExtCode`, `ExtCode.add`, `stepDigit`, `step`,
`mul`, `arith`, `overPrime`, `BinCode`, `BinCode.spread`, `unspread`, `arith` and `CodeArith.withPrime`,
and `BinarySpread.Exec`, `Exec.fold` and `Exec.mul`, match their docstrings. `fq6Code`, `fq9Code`,
`fq11Code`, `fq20QuarticCode`, `fq20Code`, `gold2Code`, `gold4Code`, `gf2_128CodeExec`, `gf2_128Code`,
`gf2_256CodeExec` and `gf2_256Code` have the documented widths, moduli and betas. The binary taps are
digits 0, 1, 2, 7 and 0, 2, 5, 10. `FieldKey.codeHom` proves the homomorphisms, so these numbers
cannot be wrong for a proof that reads them. The P-256 prime in `FieldKey.code` was recomputed.

**P-256.** `P256.p`, `P256.b`, `P256.gx` and `P256.gy` were compared in hexadecimal with the SEC 2
constants. `P256.curve` has `a4 = -3`. `P256.instIsEllipticCurve`, `P256.gen_equation`, `P256.gen`,
`P256.Point` and `P256.ofAffine` are as documented. `RealizedProgram.p256` and `p256Node` are `ZMod p`
with every node the whole field. The primality certificate and `p256Packing` were not read and have no
row.

**Interfaces.** `CertifiedSystem` and `CertifiedData` are the documented bundles. `RuntimeInputs`,
`CompletionInputs`, `ProgramData.runtimeInputs`, `ProgramData.completionInputs`,
`ProgramData.runtimeFullFacts`, `SourceParts.ofTriples`, `RuntimeInputs.ReadyFacts`, `CoreFacts`,
`FullFacts`, `FiguresFacts`, `TableausOk`, `TableausOk.at`, `tableauDesc`, `tableau`, `interp`, `ready`,
`CodedOk`, `cod`, `fieldBytes`, `fieldReader`, `chalLoadMax`, `ReadersOk`, `samplerReaders`, `maxArray`,
`maxRead`, `restRead`, `branchName`, `FitsOk`, `numbers`, `proofSystemOf` and `certified` mirror the
specification. `runtime_ready_eq`, `runtime_certified_eq` and `runtime_proofSystemOf_eq` state their
equality by `rfl`. `FiguresFacts` omits `loads`; consumers take that from `ProgramConditions`.
`ProgramFigures.DefaultLoadsOk` is the Chernoff test at the default stream's byte count.

**Source roles.** `SourceRole`, `SourceRoleEntry`, `SourceRoleClassifier`, `SourceRoleClassifier.lookup`,
`sourceRoleTable`, `sourceRoleClassifier`, `Value.needsSourceRole`, `SourceRolesOk` and
`SourceRolesPartOk` carry no witness data. Placement, order and coverage are stated as the checker
tests them. What a tag means is left to each application.

**`SPBCS.simVerifier`.** This row was absent from the ledger though the declaration is in the closure
and changed at 8a647492b. It accepts on `AcceptsFinal`, the spBCS acceptance under the base oracle
reprogrammed by the assignments in force, and returns the adversary's statement. `ctrlExpansionAt` runs
the verifier's queries through the final answers, then the simulator's query inputs. The change replaces
the quantum completion's slots with `A.slots`; `ctrlExpansion` is the same object as an abbreviation.

## Shallow rows

The rows marked shallow in the table are structure projections, constructors, recursors, enumeration
constructors and derived instances. Their content is the declaring structure's, reviewed above.

## Rows

| Declaration | Kind | Fingerprint |
|---|---|---:|
| `GordieHowe.BinarySpread.Exec` | read | 3931117990 |
| `GordieHowe.BinarySpread.Exec.fold` | read | 8429471752045137175 |
| `GordieHowe.BinarySpread.Exec.k` | shallow | 11211857635639365051 |
| `GordieHowe.BinarySpread.Exec.mask` | shallow | 9774787065755545106 |
| `GordieHowe.BinarySpread.Exec.mk` | shallow | 3952529187 |
| `GordieHowe.BinarySpread.Exec.mul` | read | 5130663057251058222 |
| `GordieHowe.BinarySpread.Exec.n` | shallow | 6074570916561039320 |
| `GordieHowe.BinarySpread.Exec.tapN` | shallow | 5409398694545673474 |
| `GordieHowe.CertifiedData` | read | 3854987981 |
| `GordieHowe.CertifiedData.cp` | shallow | 12237837934157773160 |
| `GordieHowe.CertifiedData.mk` | shallow | 590491244 |
| `GordieHowe.CertifiedData.toCertifiedSystem` | shallow | 10197942018424585509 |
| `GordieHowe.CertifiedSystem` | read | 3854987981 |
| `GordieHowe.CertifiedSystem.mk` | shallow | 1782593129 |
| `GordieHowe.CertifiedSystem.proofSystemOf` | shallow | 15974719150315535968 |
| `GordieHowe.CompletionInputs` | read | 3931117990 |
| `GordieHowe.CompletionInputs.cderivs` | shallow | 10775426037163332267 |
| `GordieHowe.CompletionInputs.gens` | shallow | 5689126668525960561 |
| `GordieHowe.CompletionInputs.mk` | shallow | 1176278583 |
| `GordieHowe.CompletionInputs.nodes` | shallow | 10021190844761741861 |
| `GordieHowe.CompletionInputs.records` | shallow | 15906948963820321761 |
| `GordieHowe.CoreConditions` | read | 1632735777 |
| `GordieHowe.CoreConditions.tableaus` | shallow | 4119821251 |
| `GordieHowe.CoreConditions.wellFormed` | shallow | 4064180033 |
| `GordieHowe.FieldKey` | read | 3931117990 |
| `GordieHowe.FieldKey.Coded` | read | 9352494422828078452 |
| `GordieHowe.FieldKey.code` | read | 9098346323518782776 |
| `GordieHowe.FieldKey.codec` | read | 8153071365603944794 |
| `GordieHowe.FieldKey.fq11` | shallow | 807304720 |
| `GordieHowe.FieldKey.fq20` | shallow | 807304720 |
| `GordieHowe.FieldKey.fq6` | shallow | 807304720 |
| `GordieHowe.FieldKey.fq9` | shallow | 807304720 |
| `GordieHowe.FieldKey.gf128` | shallow | 807304720 |
| `GordieHowe.FieldKey.gf256` | shallow | 807304720 |
| `GordieHowe.FieldKey.gold2` | shallow | 807304720 |
| `GordieHowe.FieldKey.gold4` | shallow | 807304720 |
| `GordieHowe.FieldKey.interp` | read | 2277829917870897456 |
| `GordieHowe.FieldKey.name` | read | 6256143622807176930 |
| `GordieHowe.FieldKey.p256` | shallow | 807304720 |
| `GordieHowe.FieldKey.packing` | read | 12050013113360117434 |
| `GordieHowe.FieldKey.rec` | shallow | 291479676 |
| `GordieHowe.FieldTable` | read | 3931117990 |
| `GordieHowe.FieldTable.circuitDomain` | read | 1409337393982024861 |
| `GordieHowe.FieldTable.circuitDomains` | shallow | 16377138265614329708 |
| `GordieHowe.FieldTable.circuitField` | read | 11733282162975769669 |
| `GordieHowe.FieldTable.domainField` | read | 2884681544784925510 |
| `GordieHowe.FieldTable.domainFields` | shallow | 5477291761820927587 |
| `GordieHowe.FieldTable.interp` | shallow | 116756768650530684 |
| `GordieHowe.FieldTable.mk` | shallow | 2520762833 |
| `GordieHowe.FieldTable.noFieldForm` | shallow | 6184341571944960604 |
| `GordieHowe.FieldTable.productFree` | shallow | 8169884697191828392 |
| `GordieHowe.FiguresData` | read | 3931117990 |
| `GordieHowe.FiguresData.defaultLoads` | shallow | 8164361667253972037 |
| `GordieHowe.FiguresData.figures` | shallow | 17637778156162979533 |
| `GordieHowe.FiguresData.grantMax` | shallow | 10013059839831306966 |
| `GordieHowe.FiguresData.grants` | shallow | 641500959789195406 |
| `GordieHowe.FiguresData.maxArray` | shallow | 153445062504193082 |
| `GordieHowe.FiguresData.maxRead` | shallow | 1515469321480731754 |
| `GordieHowe.FiguresData.mk` | shallow | 4214994880 |
| `GordieHowe.FiguresData.restRead` | shallow | 4028863295412857493 |
| `GordieHowe.FiguresData.sourceErrors` | shallow | 15948127922660564449 |
| `GordieHowe.GKR.Fold.BinCode` | read | 3931117990 |
| `GordieHowe.GKR.Fold.BinCode.E` | shallow | 14741378946639367387 |
| `GordieHowe.GKR.Fold.BinCode.arith` | read | 15169355309110470708 |
| `GordieHowe.GKR.Fold.BinCode.mk` | shallow | 2060679792 |
| `GordieHowe.GKR.Fold.BinCode.rep` | shallow | 8222232623326126903 |
| `GordieHowe.GKR.Fold.BinCode.spread` | read | 14887260546788704813 |
| `GordieHowe.GKR.Fold.BinCode.unspread` | read | 7811200614187197925 |
| `GordieHowe.GKR.Fold.CodeArith.withPrime` | read | 11742576666801382905 |
| `GordieHowe.GKR.Fold.ExtCode` | read | 3931117990 |
| `GordieHowe.GKR.Fold.ExtCode.add` | read | 11977114566964461563 |
| `GordieHowe.GKR.Fold.ExtCode.arith` | read | 2169264847967403175 |
| `GordieHowe.GKR.Fold.ExtCode.base` | shallow | 18285862709136806774 |
| `GordieHowe.GKR.Fold.ExtCode.beta` | shallow | 15457536614058464067 |
| `GordieHowe.GKR.Fold.ExtCode.mk` | shallow | 2768898650 |
| `GordieHowe.GKR.Fold.ExtCode.mul` | read | 18186919814357334065 |
| `GordieHowe.GKR.Fold.ExtCode.n` | shallow | 9304851539761908139 |
| `GordieHowe.GKR.Fold.ExtCode.overPrime` | read | 599311644426342800 |
| `GordieHowe.GKR.Fold.ExtCode.s` | shallow | 16230632006113315811 |
| `GordieHowe.GKR.Fold.ExtCode.step` | read | 4237373234588543110 |
| `GordieHowe.GKR.Fold.ExtCode.stepDigit` | read | 12084877477504124988 |
| `GordieHowe.GKR.Fold.primeArith` | read | 8742220368399564409 |
| `GordieHowe.GKR.Fold.undigits` | read | 799235356489123574 |
| `GordieHowe.Hints` | read | 3931117990 |
| `GordieHowe.Hints.cderivs` | shallow | 743592430448159082 |
| `GordieHowe.Hints.gens` | shallow | 16001257741109915693 |
| `GordieHowe.Hints.mk` | shallow | 3675773332 |
| `GordieHowe.Hints.nodes` | shallow | 16137688842021736489 |
| `GordieHowe.Hints.tableaus` | shallow | 14434230245419687409 |
| `GordieHowe.InterpDesc` | read | 3931117990 |
| `GordieHowe.InterpDesc.Coded` | read | 9062624768107557794 |
| `GordieHowe.InterpDesc.bytes` | read | 7495159836639429819 |
| `GordieHowe.InterpDesc.card` | read | 3805685923 |
| `GordieHowe.InterpDesc.codec` | read | 16479035938677512138 |
| `GordieHowe.InterpDesc.interp` | read | 7678124933675846149 |
| `GordieHowe.InterpDesc.key` | read | 9294505479615312490 |
| `GordieHowe.InterpDesc.one` | shallow | 1866875843 |
| `GordieHowe.InterpDesc.packing` | read | 13364947638442659724 |
| `GordieHowe.InterpDesc.provide` | read | 8002681265451114594 |
| `GordieHowe.InterpDesc.provideOn` | read | 4597370336641828754 |
| `GordieHowe.InterpDesc.reader` | read | 11538281816820688873 |
| `GordieHowe.InterpDesc.rec` | shallow | 3206694747 |
| `GordieHowe.InterpDesc.two` | shallow | 3408206404 |
| `GordieHowe.JohnsonDesc` | read | 3931117990 |
| `GordieHowe.JohnsonDesc.B` | shallow | 5504265681473555646 |
| `GordieHowe.JohnsonDesc.H` | shallow | 3752271661150137943 |
| `GordieHowe.JohnsonDesc.Ok` | read | 3918881399 |
| `GordieHowe.JohnsonDesc.agree` | shallow | 17559103181047420080 |
| `GordieHowe.JohnsonDesc.blockEnc` | shallow | 6030626611667817135 |
| `GordieHowe.JohnsonDesc.cert` | read | 4412874294982033253 |
| `GordieHowe.JohnsonDesc.exceptions` | shallow | 17084002034516558516 |
| `GordieHowe.JohnsonDesc.m` | shallow | 12217012295902411819 |
| `GordieHowe.JohnsonDesc.mk` | shallow | 806497187 |
| `GordieHowe.JohnsonDesc.nrep` | shallow | 7391816670838653433 |
| `GordieHowe.JohnsonDesc.nreq` | shallow | 15357828670316290287 |
| `GordieHowe.JohnsonDesc.r` | shallow | 6550558789465163059 |
| `GordieHowe.JohnsonDesc.rate` | shallow | 6864939502279101899 |
| `GordieHowe.JohnsonDesc.shape` | read | 7568731593933034024 |
| `GordieHowe.OpaqueKey` | read | 3931117990 |
| `GordieHowe.OpaqueKey.falcon` | shallow | 3825519751 |
| `GordieHowe.OpaqueKey.fn` | read | 3211081610639212505 |
| `GordieHowe.OpaqueKey.mdoc` | shallow | 3825519751 |
| `GordieHowe.OpaqueKey.none` | shallow | 3825519751 |
| `GordieHowe.OpaqueKey.rec` | shallow | 357835874 |
| `GordieHowe.OpaqueKey.targetBits` | shallow | 3825519751 |
| `GordieHowe.P256.Point` | read | 14858068047719220640 |
| `GordieHowe.P256.b` | read | 632428216838128697 |
| `GordieHowe.P256.curve` | read | 3381238329746841688 |
| `GordieHowe.P256.gen` | read | 9535195123648798711 |
| `GordieHowe.P256.gen_equation` | read | 1508241046 |
| `GordieHowe.P256.gx` | read | 2716229298465568608 |
| `GordieHowe.P256.gy` | read | 10176162552590018651 |
| `GordieHowe.P256.instIsEllipticCurve` | read | 2542924583 |
| `GordieHowe.P256.ofAffine` | read | 12092666909125454815 |
| `GordieHowe.P256.p` | read | 16193805593666084672 |
| `GordieHowe.PackingDesc` | read | 3931117990 |
| `GordieHowe.PackingDesc.mk` | shallow | 216835175 |
| `GordieHowe.ProgramConditions` | read | 1632735777 |
| `GordieHowe.ProgramData` | read | 3931117990 |
| `GordieHowe.ProgramData.CircuitsOk` | read | 6202538637309929686 |
| `GordieHowe.ProgramData.CodedOk` | read | 1309214445783032736 |
| `GordieHowe.ProgramData.CompletionOk` | read | 2725437887877094867 |
| `GordieHowe.ProgramData.FieldOkAt` | read | 12054802773500408691 |
| `GordieHowe.ProgramData.FieldTableOk` | read | 2196786505477598582 |
| `GordieHowe.ProgramData.FieldsOk` | read | 7721285661769508115 |
| `GordieHowe.ProgramData.FiguresAt` | read | 2589067699 |
| `GordieHowe.ProgramData.FiguresOk` | read | 15482946431440996060 |
| `GordieHowe.ProgramData.FitsOk` | read | 12833541302296285666 |
| `GordieHowe.ProgramData.NoFieldForm` | read | 5949107459938735543 |
| `GordieHowe.ProgramData.NoProduct` | read | 6058033848037195364 |
| `GordieHowe.ProgramData.ReadersOk` | read | 4025537801908289177 |
| `GordieHowe.ProgramData.RolesOk` | read | 1221187543643253672 |
| `GordieHowe.ProgramData.TableausOk` | read | 4791112360084531728 |
| `GordieHowe.ProgramData.TableausOk.at` | read | 3731683772 |
| `GordieHowe.ProgramData.chalLoadMax` | read | 7442254051564314529 |
| `GordieHowe.ProgramData.circuitCode` | read | 11327806607814003905 |
| `GordieHowe.ProgramData.circuitData` | read | 3708216546590104333 |
| `GordieHowe.ProgramData.circuits` | shallow | 5838087634994506861 |
| `GordieHowe.ProgramData.cod` | read | 15713613589860949267 |
| `GordieHowe.ProgramData.completionInputs` | read | 3929545735533388389 |
| `GordieHowe.ProgramData.fieldBytes` | read | 806369050656935043 |
| `GordieHowe.ProgramData.fieldReader` | read | 3951980745578827829 |
| `GordieHowe.ProgramData.fieldTable` | shallow | 8579577849496641815 |
| `GordieHowe.ProgramData.figures` | shallow | 2243201474452115915 |
| `GordieHowe.ProgramData.hints` | shallow | 1642738678731212135 |
| `GordieHowe.ProgramData.interp` | read | 17729133388880806800 |
| `GordieHowe.ProgramData.maxArray` | read | 4045569863188562828 |
| `GordieHowe.ProgramData.maxRead` | read | 8298589622437194499 |
| `GordieHowe.ProgramData.mk` | shallow | 4138150971 |
| `GordieHowe.ProgramData.numbers` | read | 16497653007560958604 |
| `GordieHowe.ProgramData.plan` | shallow | 6088581766219116827 |
| `GordieHowe.ProgramData.program` | shallow | 3263155252983505235 |
| `GordieHowe.ProgramData.ready` | read | 4975470566623393492 |
| `GordieHowe.ProgramData.records` | shallow | 18267887159181355662 |
| `GordieHowe.ProgramData.restRead` | read | 3028566357075840060 |
| `GordieHowe.ProgramData.runtimeFullFacts` | read | 3940794090 |
| `GordieHowe.ProgramData.runtimeInputs` | read | 12689621081196277504 |
| `GordieHowe.ProgramData.samplerReaders` | read | 6044966016858789018 |
| `GordieHowe.ProgramData.shapes` | shallow | 10470335467097854865 |
| `GordieHowe.ProgramData.sourceRoles` | shallow | 11118908136935521628 |
| `GordieHowe.ProgramData.tableau` | read | 13789215289128848813 |
| `GordieHowe.ProgramData.tableauDesc` | read | 4306863503387578850 |
| `GordieHowe.RealizedProgram.CertifiedProgram.restRead` | shallow | 12455620506292158782 |
| `GordieHowe.RealizedProgram.CircuitData.sourceParts` | read | 16245861758319367857 |
| `GordieHowe.RealizedProgram.FieldTable` | read | 1679785832 |
| `GordieHowe.RealizedProgram.Interp.twoField` | read | 758799453491757864 |
| `GordieHowe.RealizedProgram.Interp.twoFieldAt` | read | 671219090449982717 |
| `GordieHowe.RealizedProgram.ProgramFigures.DefaultLoadsOk` | read | 10122046155139696866 |
| `GordieHowe.RealizedProgram.SourceParts.ofTriples` | read | 5326782668202662769 |
| `GordieHowe.RealizedProgram.SourceRole` | read | 3931117990 |
| `GordieHowe.RealizedProgram.SourceRole.aWitness` | shallow | 2826635320 |
| `GordieHowe.RealizedProgram.SourceRole.carry` | shallow | 2826635320 |
| `GordieHowe.RealizedProgram.SourceRole.ctorIdx` | shallow | 8141774870187194905 |
| `GordieHowe.RealizedProgram.SourceRole.hashBit` | shallow | 2826635320 |
| `GordieHowe.RealizedProgram.SourceRole.hashWord` | shallow | 2826635320 |
| `GordieHowe.RealizedProgram.SourceRole.input` | shallow | 2826635320 |
| `GordieHowe.RealizedProgram.SourceRole.rec` | shallow | 1278322972 |
| `GordieHowe.RealizedProgram.SourceRole.ringSigma` | shallow | 2826635320 |
| `GordieHowe.RealizedProgram.SourceRole.selection` | shallow | 2826635320 |
| `GordieHowe.RealizedProgram.SourceRole.stmtMember` | shallow | 2826635320 |
| `GordieHowe.RealizedProgram.SourceRoleClassifier` | read | 3931117990 |
| `GordieHowe.RealizedProgram.SourceRoleClassifier.lookup` | read | 7715086321058762130 |
| `GordieHowe.RealizedProgram.SourceRoleClassifier.mk` | shallow | 757294254 |
| `GordieHowe.RealizedProgram.SourceRoleClassifier.table` | shallow | 18215705592597345300 |
| `GordieHowe.RealizedProgram.SourceRoleEntry` | read | 3931117990 |
| `GordieHowe.RealizedProgram.SourceRoleEntry.field` | shallow | 16894331717988487071 |
| `GordieHowe.RealizedProgram.SourceRoleEntry.mk` | shallow | 1646897956 |
| `GordieHowe.RealizedProgram.SourceRoleEntry.node` | shallow | 13663822917467258535 |
| `GordieHowe.RealizedProgram.SourceRoleEntry.role` | shallow | 12082664561638442344 |
| `GordieHowe.RealizedProgram.SourceRoleEntry.slot` | shallow | 15150447846458760294 |
| `GordieHowe.RealizedProgram.SourceRoleEntry.value` | shallow | 7330414647991772390 |
| `GordieHowe.RealizedProgram.SourceRolesOk` | read | 1438376848 |
| `GordieHowe.RealizedProgram.SourceRolesPartOk` | read | 2405735678661533380 |
| `GordieHowe.RealizedProgram.Value.needsSourceRole` | read | 17347989539405410131 |
| `GordieHowe.RealizedProgram.fq11Code` | read | 11398039251144673504 |
| `GordieHowe.RealizedProgram.fq20Code` | read | 15792581655483398828 |
| `GordieHowe.RealizedProgram.fq20QuarticCode` | read | 1894894441928182627 |
| `GordieHowe.RealizedProgram.fq6Code` | read | 13573192240956206726 |
| `GordieHowe.RealizedProgram.fq9Code` | read | 5592000708138533943 |
| `GordieHowe.RealizedProgram.gf2_128Code` | read | 2078588448885701277 |
| `GordieHowe.RealizedProgram.gf2_128CodeExec` | read | 6225546515499989094 |
| `GordieHowe.RealizedProgram.gf2_256Code` | read | 2183410900052952134 |
| `GordieHowe.RealizedProgram.gf2_256CodeExec` | read | 681571210067983861 |
| `GordieHowe.RealizedProgram.gold2Code` | read | 18095417848501075865 |
| `GordieHowe.RealizedProgram.gold4Code` | read | 3313930122444880523 |
| `GordieHowe.RealizedProgram.p256` | read | 11895548290308769967 |
| `GordieHowe.RealizedProgram.p256Node` | read | 6553882160291935200 |
| `GordieHowe.RealizedProgram.sourceRoleClassifier` | read | 6377813292868737524 |
| `GordieHowe.RealizedProgram.sourceRoleTable` | read | 4888675930175833887 |
| `GordieHowe.RuntimeInputs` | read | 3931117990 |
| `GordieHowe.RuntimeInputs.CodedOk` | read | 17641545125843202289 |
| `GordieHowe.RuntimeInputs.CoreFacts` | read | 731313142 |
| `GordieHowe.RuntimeInputs.CoreFacts.checks` | shallow | 2601301852 |
| `GordieHowe.RuntimeInputs.CoreFacts.hdom` | shallow | 172311115 |
| `GordieHowe.RuntimeInputs.CoreFacts.model` | shallow | 2341560544 |
| `GordieHowe.RuntimeInputs.CoreFacts.ready` | shallow | 539070295 |
| `GordieHowe.RuntimeInputs.FiguresFacts` | read | 3967140224 |
| `GordieHowe.RuntimeInputs.FitsOk` | read | 935371654032906389 |
| `GordieHowe.RuntimeInputs.FullFacts` | read | 1568875344 |
| `GordieHowe.RuntimeInputs.FullFacts.coded` | shallow | 928961191 |
| `GordieHowe.RuntimeInputs.FullFacts.completion` | shallow | 1512610349 |
| `GordieHowe.RuntimeInputs.FullFacts.roles` | shallow | 3730956972 |
| `GordieHowe.RuntimeInputs.ReadersOk` | read | 14462664771329206947 |
| `GordieHowe.RuntimeInputs.ReadyFacts` | read | 731313142 |
| `GordieHowe.RuntimeInputs.ReadyFacts.fields` | shallow | 2717589470 |
| `GordieHowe.RuntimeInputs.ReadyFacts.tableaus` | shallow | 4072966895 |
| `GordieHowe.RuntimeInputs.ReadyFacts.wellFormed` | shallow | 1561798290 |
| `GordieHowe.RuntimeInputs.TableausOk` | read | 3298913301676509838 |
| `GordieHowe.RuntimeInputs.TableausOk.at` | read | 1243922411 |
| `GordieHowe.RuntimeInputs.branchName` | read | 8438684697292571034 |
| `GordieHowe.RuntimeInputs.certified` | read | 10449948671042562028 |
| `GordieHowe.RuntimeInputs.chalLoadMax` | read | 13545621498621448960 |
| `GordieHowe.RuntimeInputs.cod` | read | 13920649997888437486 |
| `GordieHowe.RuntimeInputs.fieldBytes` | read | 14449557495347020400 |
| `GordieHowe.RuntimeInputs.fieldReader` | read | 11943988891479647957 |
| `GordieHowe.RuntimeInputs.fieldTable` | shallow | 13957145604837414434 |
| `GordieHowe.RuntimeInputs.figures` | shallow | 14335097884141460661 |
| `GordieHowe.RuntimeInputs.interp` | read | 14017347088633194986 |
| `GordieHowe.RuntimeInputs.maxArray` | read | 17878303204403030543 |
| `GordieHowe.RuntimeInputs.maxRead` | read | 17475153748392529869 |
| `GordieHowe.RuntimeInputs.mk` | shallow | 3826111962 |
| `GordieHowe.RuntimeInputs.numbers` | read | 12906817473438712404 |
| `GordieHowe.RuntimeInputs.plan` | shallow | 12101112568550236085 |
| `GordieHowe.RuntimeInputs.program` | shallow | 4787280029201009604 |
| `GordieHowe.RuntimeInputs.proofSystemOf` | read | 11669507111107264171 |
| `GordieHowe.RuntimeInputs.ready` | read | 2601267683803868237 |
| `GordieHowe.RuntimeInputs.restRead` | read | 17377460037774763531 |
| `GordieHowe.RuntimeInputs.samplerReaders` | read | 12957136572954093562 |
| `GordieHowe.RuntimeInputs.tableau` | read | 2729473509766620412 |
| `GordieHowe.RuntimeInputs.tableauDesc` | read | 8428245078707237534 |
| `GordieHowe.RuntimeInputs.tableaus` | shallow | 13720527850108183706 |
| `GordieHowe.SPBCS.simVerifier` | read | 11602922087585866158 |
| `GordieHowe.TableauDesc` | read | 3931117990 |
| `GordieHowe.TableauDesc.Ok` | read | 4160988496192287564 |
| `GordieHowe.TableauDesc.cert` | read | 17702434565323390683 |
| `GordieHowe.TableauDesc.johnson` | shallow | 733346686 |
| `GordieHowe.TableauDesc.library` | shallow | 2111664954 |
| `GordieHowe.TableauDesc.rec` | shallow | 214656296 |
| `GordieHowe.TableauKey` | read | 3931117990 |
| `GordieHowe.TableauKey.cert` | read | 14932768232725080163 |
| `GordieHowe.TableauKey.falconNativeROMA` | shallow | 3531578484 |
| `GordieHowe.TableauKey.falconRingNativeROMA` | shallow | 3531578484 |
| `GordieHowe.TableauKey.fq20K271` | shallow | 3531578484 |
| `GordieHowe.TableauKey.gf128K265R2` | shallow | 3531578484 |
| `GordieHowe.TableauKey.gf128K282R2` | shallow | 3531578484 |
| `GordieHowe.TableauKey.gf128K300R2` | shallow | 3531578484 |
| `GordieHowe.TableauKey.gf256K339R2` | shallow | 3531578484 |
| `GordieHowe.TableauKey.gold2K512R2` | shallow | 3531578484 |
| `GordieHowe.TableauKey.gold4K1024` | shallow | 3531578484 |
| `GordieHowe.TableauKey.gold4K512` | shallow | 3531578484 |
| `GordieHowe.TableauKey.gold4K512R2` | shallow | 3531578484 |
| `GordieHowe.TableauKey.rec` | shallow | 3335906579 |
| `GordieHowe.instInhabitedCircuitData_gordieHowe` | shallow | 729227639553493258 |
| `GordieHowe.instInhabitedTableauDesc` | shallow | 12712147798137742073 |
| `GordieHowe.instInhabitedTableauDesc.default` | shallow | 3054408435563924300 |
| `GordieHowe.instInhabitedTableauKey` | shallow | 3341786870008242682 |
| `GordieHowe.instInhabitedTableauKey.default` | shallow | 9565816168265808405 |
| `GordieHowe.nthOr` | read | 10414245827353971253 |
| `ReedSolomon.HiddenDerivative.IsJohnsonWeightedCertificate` | read | 5213074508199703936 |
| `ReedSolomon.HiddenDerivative.johnsonWeightedHeight` | read | 12790266790481384318 |
| `ReedSolomon.HiddenDerivative.johnsonWeightedHeightInt` | read | 4531622014631138780 |
| `ReedSolomon.HiddenDerivative.johnsonWeightedMoment` | read | 17631210540766259894 |
| `ReedSolomon.HiddenDerivative.johnsonWeightedN` | read | 4227157128921128510 |
| `ReedSolomon.HiddenDerivative.johnsonWeightedR` | read | 2017741198925233052 |
| `ReedSolomon.HiddenDerivative.johnsonWeightedSlope` | read | 4396839245032164437 |
| `ReedSolomon.HiddenDerivative.johnsonWeightedT` | read | 11378394306398268636 |
| `ReedSolomon.HiddenDerivative.johnsonWeightedW` | read | 17551743939539102348 |
