-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

import GordieHowe

/-!
# Guardrail lints for the ring-signature headlines

The ring headlines are the `@[headline]` theorems (`GordieHowe/Headline.lean`) whose statement
mentions one of the ring-signature games of `GordieHowe/Model/RingSignature/` (`ringGames`:
completeness, anonymity, unforgeability, key-reuse unforgeability). Three checks run over them.

**Scheme constants** (section "One scheme per construction"). A *scheme
constant* is a definition outside the model namespace `GordieHowe.RingSignature` whose type ends,
after its binders, in `RingSignature.RingScheme`, and not listed in `genericConstructors`: a
construction's scheme (`mldsaScheme`, `w1BindScheme44`, the Falcon `convertedScheme` and
`bindingScheme`). The model's generic constructors (`ofBase`, `RingScheme.trivial`) are not scheme
constants, so a generic headline (over `ofBase B PS adm` with `B` and `PS` variables, or over a
program form such as `StmtVerifiesRing`) names none, and neither do the
constructors generic in the base message (`w1Scheme`, `w1Concrete`, `w1Scheme44`). The rule:

1. every ring headline names at most one scheme constant;
2. for every scheme constant named by a ring headline, the ring headlines naming it cover the three
   games of `requiredGames` (completeness, anonymity, unforgeability), except the pairs listed in
   `knownMissingGames` with the reason; a listed pair whose game is covered fails the lint (remove it
   from the list), so the list records the open work exactly.

So each construction's completeness, anonymity and unforgeability headlines name the same scheme
constant, and a headline about a different scheme value (an idealized one, a second copy) is a
scheme constant of its own without the other games, which fails rule 2.

**Hypothesis registry** (section "Satisfiable hypotheses"). Every hypothesis of
a ring headline (an explicit or implicit binder whose type is a proposition, or whose type is one of
the hypothesis structures of `hypothesisStructures`) has a *head*: the constant applied in its
conclusion after its own binders. Every head must be listed in `registry`, with one of

* `.witness names`: declarations proving the predicate at concrete objects (a real instance, or a
  satisfiability lemma at an idealized object); each must exist and mention the predicate (or the
  head of its definition) in its type;
* `.trustBase reason`: a trust-base hypothesis of the project, discharged outside Lean (the
  compiler's certificates);
* `.assumption reason`: a cryptographic assumption on a primitive (a hardness or
  collision-resistance statement with its citation), not proved in Lean; the lint prints these
  apart from the trust base;
* `.gap reason`: no satisfiability lemma or instance yet; the lint prints these as the open gaps.

Heads in `elementaryHeads` (order relations, equalities, `Ne`, `Not`, injectivity, connectives) and
hypotheses whose head is a local variable are parameter conditions; they are not registered, and
the lint lists the elementary hypotheses of the instance headlines (those naming a scheme constant)
so they stay visible. Instance arguments (`[...]`) are resolved by type-class inference at each use
and are not checked.

This is a registry, not a proof that each headline's hypotheses hold together: a head with a witness
can still occur at an argument where it fails. Lemmas stating the hypotheses of one headline jointly
(`completeAtWithin_ofBase_satisfiable`, `w1Concrete.completeWithin_satisfiable`) are the stronger
form.

**Idealized objects** (section "No idealized objects"). No headline statement
(any `@[headline]` theorem) mentions a constant of `idealized`: the idealized base signers, schemes,
mask sources and proof systems used inside proofs (the fresh-mask signer of the `w₁` ring, the
uniform-signature base signer, the accepting proof system, the ideal distance). The check reads the
statement's constants, and the values of the scheme constants it names (unfolded through
definitions of the `GordieHowe` namespace), so a scheme defined from an idealized object is caught
too.

Every name listed in the configuration (`registry`, `knownMissingGames`, `idealized`,
`genericConstructors`, `hypothesisStructures`) must be a declaration of the environment, so a
renamed or removed declaration fails the lint instead of dropping out of the checks. The exception:
without the certificate library `GordieHoweCerts` (`scripts/check.sh` without `--certs`), a
registry witness that is not a declaration is listed and skipped, since the witnesses at a concrete
configuration live in that library.

Run by `scripts/check.sh` as `lake env lean scripts/RingLint.lean`; it prints the ring headlines with
their scheme constants and games, the registered gaps, the trust base, the cryptographic assumptions
and the elementary hypotheses, and fails with the list of violations.
-/

open Lean Meta Elab Command

namespace RingLint

/-- The ring-signature games: a constant of the game's statement and the game's name. -/
def ringGames : List (Name × String) :=
  [(``GordieHowe.RingSignature.RingScheme.CompleteWithin, "completeness"),
   (``GordieHowe.RingSignature.RingScheme.CompleteAtWithin, "completeness"),
   (``GordieHowe.RingSignature.anonAdvantage, "anonymity"),
   (``GordieHowe.RingSignature.insiderForgeProb, "unforgeability"),
   (``GordieHowe.RingSignature.forgeProb, "unforgeability"),
   (``GordieHowe.RingSignature.keyReuseForgeProb, "key-reuse unforgeability")]

/-- The games every construction's headlines cover (key-reuse unforgeability is a
strengthening stated only for ring-binding base messages). -/
def requiredGames : List String := ["completeness", "anonymity", "unforgeability"]

/-- The model namespace: its definitions returning a `RingScheme` are generic constructors. -/
def modelNamespace : Name := `GordieHowe.RingSignature

/-- **The open games**: a scheme constant, a required game its headlines do not yet cover, and
the reason. -/
def knownMissingGames : List (Name × String × String) :=
  []

/-- **Generic constructors** outside the model namespace: constructors generic in the base message;
headlines about them cover no concrete constant. -/
def genericConstructors : List Name :=
  [`GordieHowe.Ring.MLDSAW1.w1Concrete, `GordieHowe.Ring.MLDSAW1.w1Scheme44,
   `GordieHowe.Ring.MLDSAW1.w1Scheme65, `GordieHowe.Ring.MLDSAW1.w1Scheme87,
   `GordieHowe.Ring.MLDSAW1.w1Scheme]

/-- How a hypothesis predicate is known to be satisfiable. -/
inductive Witness where
  /-- Declarations proving (or constructing) the predicate at concrete objects. -/
  | witness (names : List Name)
  /-- A trust-base hypothesis, discharged outside Lean. -/
  | trustBase (reason : String)
  /-- A cryptographic assumption on a primitive, cited, not proved in Lean. -/
  | assumption (reason : String)
  /-- No satisfiability lemma or instance yet. -/
  | gap (reason : String)

/-- Data arguments that act as hypotheses: structures bundling the conditions of a theorem
(a program form, a soundness or honesty certificate), checked like propositions. -/
def hypothesisStructures : List Name :=
  [`GordieHowe.Ring.StmtVerifiesRing, `GordieHowe.Ring.BaseVerifiesRing,
   `GordieHowe.Ring.ProgramHypotheses, `GordieHowe.RealizedProgram.ProofSystem.IOP.Sound,
   `GordieHowe.RealizedProgram.ProofSystem.IOP.Honest,
   `GordieHowe.NARG.QROM.Verifier.KnowledgeBound,
   `GordieHowe.RingSignature.ProofSystem.CompiledBy]

/-- Heads of parameter conditions, not registered. -/
def elementaryHeads : List Name :=
  [``LE.le, ``LT.lt, ``GE.ge, ``GT.gt, ``Eq, ``Ne, ``Not, ``Iff, ``And, ``Or, ``True,
   ``Function.Injective, ``Membership.mem]

/-- **The hypothesis registry**: each head predicate of a ring headline's hypotheses, with its
satisfiability witnesses, or the reason it is trusted or open. -/
def registry : List (Name × Witness) :=
  [(`GordieHowe.RingSignature.BaseSigner.CorrectWithin, .witness
      [`GordieHowe.RingSignature.BaseSigner.correctWithin_one,
       `GordieHowe.RingSignature.BaseSigner.uniformSig_correctWithin,
       `GordieHowe.Ring.MLDSAW1.correctWithin_w1ConcreteBase,
       `GordieHowe.Ring.mldsaBaseSigner_correctWithin_zero_concreteKeyGen,
       `GordieHowe.Ring.mldsaBaseSigner_correctWithin_zero_concrete]),
   (`GordieHowe.RingSignature.BaseSigner.RefuseWithin, .witness
      [`GordieHowe.RingSignature.BaseSigner.refuseWithin_one,
       `GordieHowe.RingSignature.BaseSigner.uniformSig_refuseWithin,
       `GordieHowe.Ring.refuseWithin_mldsaRefuseMsg]),
   (`GordieHowe.RingSignature.BaseSigner.RefuseAvgWithin, .witness
      [`GordieHowe.RingSignature.BaseSigner.refuseAvgWithin_one,
       `GordieHowe.Ring.refuseAvgWithin_mldsaRefuseAvg]),
   (`GordieHowe.Ring.MLDSAW1.W1CheckDefectMgf, .gap
      ("conjecture on an honest key's check defect, supported only by the numerical estimate " ++
        "of the PublicW1 README (w1CheckDefectMgf_pow: B = x^reps)")),
   (`GordieHowe.Ring.MLDSAW1.HonestTrDistinct, .witness
      [`GordieHowe.Ring.MLDSAW1.honestTrDistinct_one]),
   (`GordieHowe.Ring.MLDSAW1.HonestTrDistinct44, .assumption
      "seed collisions and SHAKE256 collision resistance (FIPS 202 Appendix A.1, FIPS 204 Algorithm 6)"),
   (`GordieHowe.Ring.MLDSAW1.HonestTrDistinct65, .assumption
      "seed collisions and SHAKE256 collision resistance (FIPS 202 Appendix A.1, FIPS 204 Algorithm 6)"),
   (`GordieHowe.Ring.MLDSAW1.HonestTrDistinct87, .assumption
      "seed collisions and SHAKE256 collision resistance (FIPS 202 Appendix A.1, FIPS 204 Algorithm 6)"),
   (`GordieHowe.RingSignature.BaseSigner.RefuseAtWithin, .witness
      [`GordieHowe.RingSignature.BaseSigner.refuseAtWithin_one,
       `GordieHowe.Ring.falconBaseSigner_refuseAtWithin,
       `GordieHowe.RingSignature.BaseSigner.uniformSig_refuseAtWithin]),
   (`GordieHowe.RingSignature.BaseSigner.OracleFree, .witness
      [`GordieHowe.Ring.falconBaseSigner_oracleFree, `GordieHowe.Ring.mldsaBaseSigner_oracleFree,
       `GordieHowe.RingSignature.BaseSigner.uniformSig_oracleFree]),
   (`GordieHowe.RingSignature.BaseSigner.VerifiesWithoutOracle, .witness
      [`GordieHowe.Ring.falconBaseSigner_verifiesWithoutOracle,
       `GordieHowe.Ring.mldsaBaseSigner_verifiesWithoutOracle,
       `GordieHowe.RingSignature.BaseSigner.uniformSig_verifiesWithoutOracle]),
   (`GordieHowe.RingSignature.BaseSigner.ReadsOnly, .witness
      [`GordieHowe.RingSignature.BaseSigner.OracleFree.readsOnly,
       `GordieHowe.Ring.MLDSAW1.readsOnly_freshBase]),
   (`GordieHowe.RingSignature.BaseSigner.PubOfCoins, .witness
      [`GordieHowe.Ring.falconBaseSigner_pubOfCoins,
       `GordieHowe.RingSignature.BaseSigner.pubOfCoins_unique,
       `GordieHowe.RingSignature.BaseSigner.uniformSig_pubOfCoins]),
   (`GordieHowe.RingSignature.BaseSigner.BindsRing, .witness
      [`GordieHowe.Falcon512.Ring.bindsRing_encodeRingMsg,
       `GordieHowe.MLDSA44.Ring.bindsRing_bindingMsg,
       `GordieHowe.Ring.exists_bindsRing_mldsaBaseSigner]),
   (`GordieHowe.RingSignature.ProofSystem.CompleteWithin, .witness
      [`GordieHowe.Ring.spbcsProofSystem_completeWithin,
       `GordieHowe.Ring.spbcsComapProofSystem_completeWithin,
       `GordieHowe.RingSignature.ProofSystem.acceptAll_completeWithin]),
   (`GordieHowe.RingSignature.RingRel, .witness
      [`GordieHowe.Ring.ringRel_of_mem_ringRelAll]),
   (`GordieHowe.Ring.PubWI, .witness
      [`GordieHowe.Ring.StmtVerifiesRing.pubWI_proofSystem,
       `GordieHowe.Ring.pubWI_spbcsComapProofSystem,
       `GordieHowe.Ring.MLDSAW1.pubWI_acceptAll, `GordieHowe.Ring.PubWI.of_forall_not_mem]),
   (`GordieHowe.Ring.MLDSAW1.W1Oracles.UniformSplit, .witness
      [`GordieHowe.Ring.MLDSAW1.uniformSplit_sumOracles_satY]),
   (`GordieHowe.Ring.MLDSAW1.W1OracleFacts, .witness
      [`GordieHowe.Ring.MLDSAW1.w1OraclesPlaced_exists44,
       `GordieHowe.Ring.MLDSAW1.w1OraclesPlaced_exists65,
       `GordieHowe.Ring.MLDSAW1.w1OraclesPlaced_exists87]),
   (`GordieHowe.Ring.MLDSAW1.W1Oracles.ReadsFst, .witness
      [`GordieHowe.Ring.MLDSAW1.W1Oracles.readsFst_unit,
       `GordieHowe.Ring.MLDSAW1.W1Oracles.readsFst_viaBase]),
   (`GordieHowe.Ring.MLDSAW1.MaskOracle.ReadsFst, .witness
      [`GordieHowe.Ring.MLDSAW1.MaskOracle.readsFst_unit,
       `GordieHowe.Ring.MLDSAW1.MaskOracle.readsFst_viaBase]),
   (`GordieHowe.RingSignature.ProofSystem.ReadsOff, .witness
      [`GordieHowe.RingSignature.ProofSystem.ReadsSnd.readsOff,
       `GordieHowe.RingSignature.ProofSystem.readsOff_acceptAll]),
   (`GordieHowe.RingSignature.ProofSystem.ReadsSnd, .witness
      [`GordieHowe.RingSignature.ProofSystem.readsSnd_viaPrf]),
   (`GordieHowe.RingSignature.OracleView.ReadsOff, .witness
      [`GordieHowe.RingSignature.OracleView.readsOff_tableOn_compl,
       `GordieHowe.RingSignature.OracleView.readsOff_queriesOnly]),
   (`GordieHowe.Ring.MLDSAW1.CheckParams, .witness
      [`GordieHowe.Ring.MLDSAW1.checkParams_tol2, `GordieHowe.Ring.MLDSAW1.checkParams_tol8]),
   (`GordieHowe.Falcon512.Ring.Native.Signer.CarriesSalt, .witness
      [`GordieHowe.Ring.exists_carriesSalt]),
   (`MLDSA.Params.isApproved, .witness
      [`GordieHowe.MLDSA.Regularity.isApproved_mldsa44, `GordieHowe.Ring.MLDSAW1.isApproved_mldsa65,
       `GordieHowe.Ring.MLDSAW1.isApproved_mldsa87]),
   (`GordieHowe.RealizedProgram.ProofSystem.PhaseStep.Honest.ErrorBound, .witness
      [`GordieHowe.Falcon512.Ring.Native.QROMParams.ringHonest_errorBound]),
   (`GordieHowe.SPBCS.ProofSystemTranscript.MergeBounds, .witness
      [`GordieHowe.Falcon512.Ring.Native.QROMParams.ringMergeBounds]),
   (`GordieHowe.SPBCS.ProofSystemTranscript.ProofFormat, .witness
      [`GordieHowe.Falcon512.Ring.Native.QROMParams.ringProofFormat]),
   (`GordieHowe.SPBCS.FormatBounds, .witness
      [`GordieHowe.SPBCS.ProofSystemTranscript.formatBounds]),
   (`GordieHowe.IOP.CausalRBRKnowledgeSound, .witness
      [`GordieHowe.Falcon512.Ring.Native.QROMParams.iop_rbr_knowledge_soundness]),
   (`GordieHowe.IOP.CausalHVZK, .witness
      [`GordieHowe.Falcon512.Ring.Native.QROMParams.iop_hvzk]),
   (`GordieHowe.Ring.StmtVerifiesRing, .witness
      [`GordieHowe.Falcon512.Ring.ringVerifies]),
   (`GordieHowe.Ring.BaseVerifiesRing, .witness
      [`GordieHowe.Falcon512.Ring.Native.QROMParams.ringBaseVerifies]),
   (`GordieHowe.Ring.ProgramHypotheses, .witness
      [`GordieHowe.Falcon512.Ring.Native.QROMParams.ringProgramHypotheses]),
   (`GordieHowe.RealizedProgram.ProofSystem.IOP.Sound, .witness
      [`GordieHowe.Falcon512.Ring.Native.QROMParams.ringIopSound]),
   (`GordieHowe.RealizedProgram.ProofSystem.IOP.Honest, .witness
      [`GordieHowe.Falcon512.Ring.Native.QROMParams.ringHonest]),
   (`GordieHowe.NARG.QROM.Verifier.KnowledgeBound, .witness
      [`GordieHowe.SPBCS.knowledgeBound]),
   (`GordieHowe.RingSignature.ProofSystem.CompiledBy, .witness
      [`GordieHowe.Ring.compiledBy_spbcsComapProofSystem]),
   (`GordieHowe.RingSignature.BaseSigner.RefusalOfCoins, .witness
      [`GordieHowe.Ring.falconBaseSigner_refusalOfCoins]),
   (`GordieHowe.RingSignature.BaseSigner.RingSignsStd, .witness
      [`GordieHowe.Ring.falconBaseSigner_ringSignsStd, `GordieHowe.Ring.mldsaBaseSigner_ringSignsStd]),
   (`GordieHowe.RingSignature.GameAdversary.ScheduleLE, .witness
      [`GordieHowe.RingSignature.GameAdversary.exists_scheduleLE]),
   (`GordieHowe.RingSignature.Insider.ZKRingHyps, .witness
      [`GordieHowe.Ring.StmtVerifiesRing.zkRingHyps,
       `GordieHowe.RingSignature.Insider.zkRingHyps_id]),
   (`GordieHowe.Ring.MLDSASufCma, .assumption
      "ML-DSA SUF-CMA (FIPS 204 §3.1; KLS18 Definition 2.9), for a named class"),
   (`GordieHowe.Ring.MLDSAMUSufCma, .assumption
      "ML-DSA MU-SUF-CMA^corr (FIPS 204 §3.1; DGJL21 Definition 2), for a named class"),
   (`GordieHowe.Ring.MLDSA44MUSufCma, .assumption "MLDSAMUSufCma at ML-DSA-44"),
   (`GordieHowe.Ring.MLDSA65MUSufCma, .assumption "MLDSAMUSufCma at ML-DSA-65"),
   (`GordieHowe.Ring.MLDSA87MUSufCma, .assumption "MLDSAMUSufCma at ML-DSA-87"),
   (`GordieHowe.Ring.Falcon512EufCma, .assumption
      "Falcon-512 EUF-CMA (Falcon specification v1.2), for a named class"),
   (`GordieHowe.Ring.Falcon512MUEufCma, .assumption
      "Falcon-512 MU-EUF-CMA^corr (BHJKL15 Definition 2), for a named class"),
   (`GordieHowe.Ring.MLDSAMUSufCmaWithin, .assumption
      "MLDSAMUSufCma with at most Qs signing and corruption requests counted"),
   (`GordieHowe.Ring.MLDSA44MUSufCmaWithin, .assumption "MLDSAMUSufCmaWithin at ML-DSA-44"),
   (`GordieHowe.Ring.MLDSA65MUSufCmaWithin, .assumption "MLDSAMUSufCmaWithin at ML-DSA-65"),
   (`GordieHowe.Ring.MLDSA87MUSufCmaWithin, .assumption "MLDSAMUSufCmaWithin at ML-DSA-87"),
   (`GordieHowe.Ring.Falcon512MUEufCmaWithin, .assumption
      "Falcon512MUEufCma with at most Qs signing and corruption requests counted")]

/-- **Idealized objects**: constants no headline statement mentions, with
what they idealize. -/
def idealized : List (Name × String) :=
  [(`GordieHowe.Ring.MLDSAW1.freshBase, "the fresh-mask (ideal-mask) base signer of the w₁ ring"),
   (`GordieHowe.Ring.MLDSAW1.freshScheme, "the fresh-mask ring signature of the w₁ ring"),
   (`GordieHowe.Ring.MLDSAW1.freshLoop, "the fresh-mask signing loop of the w₁ ring"),
   (`GordieHowe.Ring.MLDSAW1.freshChallenger, "the anonymity challenger of the fresh-mask signer"),
   (`GordieHowe.Ring.MLDSAW1.MaskSource.fresh, "fresh uniform masks in place of the mask oracle"),
   (`GordieHowe.Ring.MLDSAW1.idealDist, "the public-value distance of the fresh-mask signer"),
   (`GordieHowe.RingSignature.BaseSigner.uniformSig, "the uniform-signature base signer"),
   (`GordieHowe.RingSignature.ProofSystem.acceptAll, "the proof system accepting every proof"),
   (`GordieHowe.RingSignature.RingScheme.trivial, "the trivial ring signature")]

/-- A formatted expression on one line. -/
def oneLine (f : Format) : String :=
  (f.pretty 100000).replace "\n" " "

/-- Whether `c` is a scheme constant: a definition outside the model namespace and not in
`genericConstructors` whose type ends in `RingScheme`. -/
def isSchemeConst (c : Name) : MetaM Bool := do
  if modelNamespace.isPrefixOf c then return false
  if genericConstructors.contains c then return false
  let some info := (← getEnv).find? c | return false
  unless info matches .defnInfo _ do return false
  try
    forallTelescopeReducing info.type fun _ b => do
      return (← whnfR b).isAppOf ``GordieHowe.RingSignature.RingScheme
  catch _ => return false

/-- A ring headline: name, games, scheme constants. -/
structure RingHeadline where
  name : Name
  games : List String
  schemes : List Name

/-- The ring headlines, sorted by name. -/
def ringHeadlines : MetaM (Array RingHeadline) := do
  let env ← getEnv
  let heads := (GordieHowe.headlines env).toList.toArray.qsort (·.toString < ·.toString)
  let mut out := #[]
  for n in heads do
    let some info := env.find? n | continue
    let cs := info.type.getUsedConstants
    let games := (ringGames.filter fun (g, _) => cs.contains g).map (·.2) |>.eraseDups
    if games.isEmpty then continue
    let schemes ← cs.filterM isSchemeConst
    out := out.push { name := n, games, schemes := schemes.toList }
  return out

/-- Whether the certificate library `GordieHoweCerts` is imported (`scripts/check.sh --certs`). Its
modules hold the applications' instantiations, so some registry witnesses (declarations at a
concrete configuration) exist only with it; without it a missing witness is reported, not failed. -/
def certsLoaded (env : Environment) : Bool :=
  (env.getModuleIdx? `GordieHoweCerts).isSome

/-- The registry's witnesses. -/
def witnessNames : List Name :=
  registry.flatMap fun
    | (_, .witness ns) => ns
    | _ => []

/-- Names of the configuration that are not declarations. -/
def missingNames : MetaM (List Name) := do
  let env ← getEnv
  let names := knownMissingGames.map (·.1) ++ idealized.map (·.1) ++ genericConstructors ++
    hypothesisStructures ++
    registry.map (·.1) ++ registry.flatMap fun
      | (_, .witness ns) => ns
      | _ => []
  return names.filter (!env.contains ·)

/-! ### One scheme per construction -/

/-- The violations of the scheme-constant rule. -/
def schemeViolations (hs : Array RingHeadline) : MetaM (List String) := do
  let mut bad : List String := []
  for h in hs do
    if h.schemes.length > 1 then
      bad := bad ++ [s!"{h.name} names {h.schemes.length} scheme constants: {h.schemes}"]
  let schemes := (hs.toList.flatMap (·.schemes)).eraseDups
  for s in schemes do
    let games := (hs.toList.filter (·.schemes.contains s)).flatMap (·.games)
    for g in requiredGames do
      let listed := knownMissingGames.any fun (s', g', _) => s' == s && g' == g
      if games.contains g && listed then
        bad := bad ++ [s!"{s}: {g} is covered but listed in knownMissingGames (remove it)"]
      if !games.contains g && !listed then
        bad := bad ++ [s!"{s}: no {g} headline (headlines name it for {games.eraseDups})"]
  for (s, g, _) in knownMissingGames do
    unless schemes.contains s do
      bad := bad ++ [s!"{s} ({g}) is listed in knownMissingGames but no ring headline names it"]
  return bad

/-! ### Satisfiable hypotheses -/

/-- The head of a hypothesis type: the constant applied in its conclusion, if any. -/
def hypHead (ty : Expr) : MetaM (Option Name) :=
  forallTelescope ty fun _ b => pure b.getAppFn.constName?

/-- Whether a witness declaration's type mentions the predicate, or the head of the predicate's
definition. -/
def mentionsPred (w pred : Name) : MetaM Bool := do
  let env ← getEnv
  let some wi := env.find? w | return false
  let cs := wi.type.getUsedConstants
  if cs.contains pred then return true
  let some pi := env.find? pred | return false
  let some v := pi.value? | return false
  let hd ← lambdaTelescope v fun _ b => forallTelescope b fun _ c => pure c.getAppFn.constName?
  return match hd with
    | some h => cs.contains h
    | none => false

/-- The hypotheses of the ring headlines: unregistered heads, and the elementary hypotheses of the
instance headlines (headline, binder, statement). -/
def hypothesisReport (hs : Array RingHeadline) :
    MetaM (List String × List String) := do
  let env ← getEnv
  let mut unregistered : List String := []
  let mut elementary : List String := []
  for h in hs do
    let some info := env.find? h.name | continue
    let (u, e) ← forallTelescope info.type fun xs _ => do
      let mut u : List String := []
      let mut e : List String := []
      for x in xs do
        let bi ← x.fvarId!.getBinderInfo
        if bi.isInstImplicit then continue
        let ty ← inferType x
        let hd ← hypHead ty
        let isHyp ← (do
          if ← isProp ty then return true
          return match hd with
            | some c => hypothesisStructures.contains c
            | none => false)
        unless isHyp do continue
        let nm ← x.fvarId!.getUserName
        match hd with
        | some c =>
          if elementaryHeads.contains c then
            unless h.schemes.isEmpty do
              e := e ++ [s!"{h.name} ({nm}): {oneLine (← ppExpr ty)}"]
          else unless registry.any (·.1 == c) do
            u := u ++ [s!"{h.name} ({nm}): head {c}"]
        | none =>
          unless h.schemes.isEmpty do
            e := e ++ [s!"{h.name} ({nm}): {oneLine (← ppExpr ty)}"]
      return (u, e)
    unregistered := unregistered ++ u
    elementary := elementary ++ e
  return (unregistered, elementary)

/-- Registered witnesses whose type does not mention their predicate. -/
def badWitnesses : MetaM (List String) := do
  let mut bad : List String := []
  for (p, w) in registry do
    if let .witness ns := w then
      if ns.isEmpty then bad := bad ++ [s!"{p}: empty witness list"]
      for n in ns do
        -- a witness absent without the certificate library is checked with it
        unless certsLoaded (← getEnv) || (← getEnv).contains n do continue
        unless ← mentionsPred n p do
          bad := bad ++ [s!"{p}: witness {n} does not mention it"]
  return bad

/-! ### No idealized objects -/

/-- The constants of the values of the given definitions, unfolded through definitions of the
`GordieHowe` namespace (theorems contribute nothing). -/
partial def unfoldClosure (roots : List Name) : MetaM NameSet := do
  let env ← getEnv
  let mut seen : NameSet := {}
  let mut todo := roots
  while !todo.isEmpty do
    let c := todo.head!
    todo := todo.tail!
    if seen.contains c then continue
    seen := seen.insert c
    unless (`GordieHowe).isPrefixOf c do continue
    let some info := env.find? c | continue
    let some v := (match info with
      | .defnInfo d => some d.value
      | _ => none) | continue
    for d in v.getUsedConstants do
      unless seen.contains d do todo := d :: todo
  return seen

/-- Headlines whose statement, or the unfolded value of a scheme constant it names, mentions an
idealized object. -/
def idealizedViolations : MetaM (List String) := do
  let env ← getEnv
  let mut bad : List String := []
  -- `isSchemeConst` once per constant: the headlines share most of their constants
  let mut memo : Std.HashMap Name Bool := {}
  let mut closures : Std.HashMap Name NameSet := {}
  for n in (GordieHowe.headlines env).toList do
    let some info := env.find? n | continue
    let cs := info.type.getUsedConstants
    for (c, what) in idealized do
      if cs.contains c then bad := bad ++ [s!"{n} mentions {c} ({what})"]
    let mut schemes : Array Name := #[]
    for c in cs do
      let mut isS := false
      match memo[c]? with
      | some b => isS := b
      | none =>
        isS ← isSchemeConst c
        memo := memo.insert c isS
      if isS then schemes := schemes.push c
    -- each scheme constant's closure once: a certified configuration's reaches its certificate data
    let mut cl : NameSet := {}
    for sc in schemes do
      let mut k : NameSet := {}
      match closures[sc]? with
      | some k' => k := k'
      | none =>
        k ← unfoldClosure [sc]
        closures := closures.insert sc k
      cl := k.foldl (·.insert ·) cl
    for (c, what) in idealized do
      if cl.contains c && !cs.contains c then
        bad := bad ++ [s!"{n} names a scheme constant defined from {c} ({what})"]
  return bad

end RingLint

open RingLint in
run_cmd liftTermElabM do
  let mut missing ← missingNames
  unless certsLoaded (← getEnv) do
    let deferred := missing.filter witnessNames.contains
    unless deferred.isEmpty do
      IO.println s!"ring lint: {deferred.length} registry witness(es) are declarations only with the \
        certificate library GordieHoweCerts, checked by scripts/check.sh --certs: {deferred}"
    missing := missing.filter (!witnessNames.contains ·)
  unless missing.isEmpty do
    throwError m!"ring lint: {missing.length} configured name(s) are not declarations: {missing}"
  let hs ← ringHeadlines
  IO.println s!"ring headlines: {hs.size}"
  for h in hs do
    IO.println s!"  {h.name}\t{h.games}\t{h.schemes}"
  let mut fails : List String := []
  let sv ← schemeViolations hs
  fails := fails ++ sv.map ("scheme constants: " ++ ·)
  let (unreg, elem) ← hypothesisReport hs
  fails := fails ++ unreg.map ("unregistered hypothesis: " ++ ·)
  fails := fails ++ (← badWitnesses).map ("registry: " ++ ·)
  fails := fails ++ (← idealizedViolations).map ("idealized object: " ++ ·)
  IO.println "open games (knownMissingGames):"
  for (s, g, r) in knownMissingGames do IO.println s!"  {s}\t{g}\t{r}"
  IO.println "hypothesis predicates without a satisfiability witness (registry gaps):"
  for (p, w) in registry do
    if let .gap r := w then IO.println s!"  {p}\t{r}"
  IO.println "trust-base hypotheses:"
  for (p, w) in registry do
    if let .trustBase r := w then IO.println s!"  {p}\t{r}"
  IO.println "cryptographic assumptions:"
  for (p, w) in registry do
    if let .assumption r := w then IO.println s!"  {p}\t{r}"
  IO.println s!"elementary hypotheses of instance headlines (not registered): {elem.length}"
  for e in elem do IO.println s!"  {e}"
  unless fails.isEmpty do
    throwError m!"ring lint: {fails.length} violation(s):\n{"\n".intercalate fails}"
  IO.println "ring lint: ok"
