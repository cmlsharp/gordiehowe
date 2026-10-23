#!/usr/bin/env python3
# Copyright 2026 Chad Sharp and Paul Grubbs
# SPDX-License-Identifier: Apache-2.0

"""The non-Ligero round errors of a GordieHowe configuration, from its plan exports.

The plan export (GordieHowe/Generated/<Lean name>/Plan.lean, lib/gordiehowe/plan_export.h) and
the realized program (Program.lean beside it, lib/gordiehowe/compiler/plan_program.h; plan_files
also reads the flat layout <Name>.lean and <Name>Program.lean) of a configuration hold every count
the Lean's round errors read. This module evaluates them with the Lean's formulas, exactly
(Fractions). Lean paths below are files of the Lean library.

Per domain d over the field K_d (|K_d| elements):
  commit    (B/(|K| - 1))^rho, rho the low-degree      Ligero/ListRadius.lean:448
            test's repetitions (ldtReps, 1 when
            absent)
  test      1/|K| (split masks), l/|K| (untested       GordieHowe/ProofSystem/Ligero/
            masks, l = listBound N (2k-2) a)           MaskRow/Layout.lean Masking.bounds
  column    ((A-1)_t + m_t)/(N)_t, m = 2k - 1 (split)
            or a = johnsonAgreement N (2k-2)
            (untested), plus the joint subfield         Numbers.proofError
            term (k-1)_t/(N)_t
  batches   the domain's batch errors, summed: per     ForkFigures.lean batchNum, mergedNum
            batch (r + D(w-1) + (D+1)r + 1)/|K| (r
            rounds, degree D, width w), (parts-1)/|K|
            when merged, and 2/|K| per round of its
            bit-index sumcheck (bitSumcheck, 4 rounds)
  gkr       each GKR round (gkr_errors below)          paper lem:gkr(1)
  combin.   |edges|/|K|, one per packing edge
(GordieHowe/ProofSystem/Program/*.lean of the Lean library.) Each of these is one round's error, checked
against the target on its own: no error is added to another's (thm:backend(2), FieldRoundsLe).
Per phase k (GordieHowe/Plan/Errors.lean:47-48, Realized.lean:364-372):
  phase_k   sum over the phase's challenges j of the source error degreeBound_j/|K_j| (source
            challenges only) and the realization error
            (sum over j's table groups of (N_g + T - 1) + sum over MACs keyed by j of chunks)
            / (|K_j| - tmax_j), tmax_j the table range the sampler avoids (0 for .full)
Per GKR circuit of a domain (paper lem:gkr(1); thm:backend(2) charges each challenge its error,
and each of these challenges is its own verifier message), with L the circuit's layers and m_j
the variables of wire layer j (layer 0 the output, layer L the input):
  initial point r^(0) in K^(m_0)          2 m_0/|K|
  (mu_j, beta_j), each layer j < L        2/|K|
  sumcheck round k of layer j             3/|K| for even k, 2/|K| for odd k (2 m_(j+1) rounds)
  input combination mu_in                 1/|K|
  summed: (2 m_0 + 2L + 5 sum_(j<L) m_(j+1) + 1)/|K|
The plan export records L and wires = the sum over the layers of their input wires
(lib/gordiehowe/compiler/compiled_domain.h, report()), not each m_j or the output layer's m_0. So
m_(j+1) <= w = ceil(log2 max(wires, inputs)) (the Lean's Program.circuitWidth,
GordieHowe/Plan/Enforce.lean:290), and m_0 <= 40 = GKR_OUTPUT_VARS (the C++ verifier's
LayerProof::kMaxBindings, lib/sumcheck/circuit.h:112). Every GKR round is then charged at most
max(2 m_0, 3)/|K| = 80/|K|. The Lean bounds m_0 by w instead (Source.ShapeAtMost.outDim_le under
the trust's shape) and charges max(3, 2 gkrWidth)/|K| (Program.gkrRoundError), never more.

The Lean's kappa is the bound on every round error of the series-parallel composite
(the Lean library's GordieHowe/ProofSystem/Program/FieldFJ.lean fieldForkError_le): each phase is
charged its phaseError, and each domain's rounds their own terms (Program.FieldRoundsLe,
FieldDomain.lean): the commit round its commit error, each batch branch's rounds the domain's
batch errors summed (batchesError), each GKR round max(3, 2 gkrWidth)/|K| (gkrRoundError), the
join's combination rounds |edges|/|K|, Ligero's constraint challenge the test error and its
column query the column error with the joint subfield term. The "lean" charges of case_errors
are these.
"""
import re
from fractions import Fraction

# The bound on the output layer's variables m_0 (module docstring): LayerProof::kMaxBindings,
# lib/sumcheck/circuit.h:112.
# The plan export does not record m_0.
GKR_OUTPUT_VARS = 40


# ------------------------------------------------------------------ parsing --

def _field(block):
    m = re.search(r"field := \{ name := \"([^\"]+)\",\s*characteristic := (\d+),\s*degree := (\d+)",
                  block)
    if not m:
        raise ValueError("domain block without a field")
    return m.group(1), int(m.group(2)) ** int(m.group(3))


def parse_plan(text):
    """The plan export: its header, and per domain its field, tableau, packing edges, circuit and
    batches; the challenges' degree bounds by label."""
    head = {k: (re.search(rf'^\s*{k} := "([^"]*)"', text, re.M) or [None, None])[1]
            for k in ("config", "cppCommit", "runId", "digest", "hash")}
    starts = [m.start() for m in re.finditer(r'\{ name := "[A-Z]\w*",\n\s*field := \{', text)]
    end = re.search(r"^    requests := ", text, re.M)
    end = end.start() if end else len(text)
    doms = {}
    for i, s in enumerate(starts):
        blk = text[s:(starts[i + 1] if i + 1 < len(starts) else end)]
        name = re.match(r'\{ name := "(\w+)"', blk).group(1)
        fname, F = _field(blk)
        lig = re.search(r"ligero := \{(.*?)\}", blk, re.S).group(1)

        def g(key, src=lig):
            return int(re.search(rf"\b{key} := (\d+)", src).group(1))
        masking = re.search(r"masking := \.(\w+)", lig).group(1)
        pack = re.search(r"packing := \[(.*?)\],\n\s*(?:coords|circuits|params)", blk, re.S)
        circ = re.search(r'circuits := \[\{ name := "\w+", layers := (\d+), wires := (\d+)', blk)
        cl = re.search(r"circuits := \[(.*?)\]", blk, re.S)
        circs = [dict(name=c.group(1), layers=int(c.group(2)), wires=int(c.group(3)))
                 for c in re.finditer(r'\{ name := "(\w+)", layers := (\d+), wires := (\d+)',
                                      cl.group(1) if cl else "")]
        reps = re.search(r"\bldtReps := (\d+)", lig)
        inputs = re.search(r"^\s*inputs := (\d+),", blk, re.M)
        doms[name] = dict(name=name, field=fname, F=F, N=g("N"), k=g("k"), t=g("t"),
                          nrow=g("nrow"), masking=masking,
                          ldt_reps=int(reps.group(1)) if reps else 1,
                          edges=pack.group(1).count("child :=") if pack else 0,
                          circuit=(int(circ.group(1)), int(circ.group(2))) if circ else None,
                          circuits=circs,
                          inputs=int(inputs.group(1)) if inputs else 0)
    chal = re.search(r"^    challenges := \[(.*?)^    \w+ := ", text, re.S | re.M)
    degree = {}
    if chal:
        for c in re.finditer(r'label := "([^"]+)",.*?degreeBound := (\d+)', chal.group(1), re.S):
            degree[c.group(1)] = int(c.group(2))
    return dict(head=head, domains=doms, degree=degree)


def program_from_plan(text):
    """The realized program's counts rebuilt from the plan export alone, for a system whose
    program the exporter does not cover (the same dict as parse_program): fields and domains in
    the plan's domain order; one LogUp group per table, its needles the table's static and late
    needles; a challenge's excluded range tmax the largest table it samples around
    (field-minus-tables); the MACs' chunk counts (nch) keyed by their challenges; a challenge is
    a source challenge when no table and no MAC is keyed by it; the domains' batches; the
    domains' circuits, each with its domain's input count (the plan records the inputs per
    domain, so a domain with several circuits is refused); a batch on bits with its bit-index
    sumcheck (_plan_bit_phase).
    eval_params_test.py checks it against every program in formal/GordieHowe/Generated."""
    plan = parse_plan(text)
    names = list(plan["domains"])
    fields = [plan["domains"][n]["F"] for n in names]
    chal = re.search(r"^    challenges := \[(.*?)(?:^    \w+ := |\Z)", text, re.S | re.M)
    challenges = []
    for c in re.finditer(r'label := "([^"]+)",\s*domain := "(\w+)",\s*phase := (\d+),'
                         r'\s*sampler := "([^"]+)"', chal.group(1) if chal else ""):
        challenges.append(dict(name=c.group(1), field=names.index(c.group(2)),
                               phase=int(c.group(3)), sampler=c.group(4), tmax=0, source=True))
    index = {c["name"]: j for j, c in enumerate(challenges)}
    tables = []
    tab = re.search(r"^    tables := \[(.*?)^    \w+ := ", text, re.S | re.M)
    for body in re.split(r'\{ domain := "', tab.group(1) if tab else "")[1:]:
        dom = body.split('"', 1)[0]

        def gi(key):
            return int(re.search(rf"\b{key} := (\d+)", body).group(1))
        j = index[re.search(r'challenge := "([^"]+)"', body).group(1)]
        tables.append(dict(name=re.search(r'name := "([^"]+)"', body).group(1),
                           domain=names.index(dom), size=gi("size"), alpha=j,
                           groups=[gi("staticNeedles") + gi("lateNeedles")]))
        challenges[j]["source"] = False
        if challenges[j]["sampler"] == "field-minus-tables":
            challenges[j]["tmax"] = max(challenges[j]["tmax"], gi("size"))
    macs = []
    mac = re.search(r"^    macs := \[(.*?)^    \w+ := ", text, re.S | re.M)
    for m in re.finditer(r"nch := (\d+),.*?challenge := \"([^\"]+)\"",
                         mac.group(1) if mac else "", re.S):
        j = index[m.group(2)]
        macs.append((j, int(m.group(1))))
        challenges[j]["source"] = False
    batches = []
    starts = [m.start() for m in re.finditer(r'\{ name := "[A-Z]\w*",\n\s*field := \{', text)]
    end = re.search(r"^    requests := ", text, re.M)
    end = end.start() if end else len(text)
    for i, st in enumerate(starts):
        blk = text[st:(starts[i + 1] if i + 1 < len(starts) else end)]
        bt = re.search(r"batches := \[(.*?)\],\n\s*streamPoints", blk, re.S)
        for b in re.finditer(r'\{ name := "([^"]+)",(.*?)pads := \d+ \}',
                             bt.group(1) if bt else "", re.S):
            def gb(key, body=b.group(2)):
                return int(re.search(rf"\b{key} := (\d+)", body).group(1))
            batches.append(dict(name=b.group(1), domain=i, degree=gb("degree"),
                                width=gb("width"), rounds=gb("rounds"),
                                instances=gb("instances"), merged=_merged(b.group(2)),
                                bit_phase=_plan_bit_phase(b.group(2))))
    circuits = []
    for i, n in enumerate(names):
        d = plan["domains"][n]
        if len(d["circuits"]) > 1:
            raise ValueError(f"domain {n}: {len(d['circuits'])} circuits; the plan records one "
                             "input count per domain")
        circuits += [dict(c, domain=i, inputCount=d["inputs"]) for c in d["circuits"]]
    phases = int(re.search(r"^    phases := (\d+)", text, re.M).group(1))
    return dict(phases=phases, fields=fields, domains=[(n, i) for i, n in enumerate(names)],
                tables=tables, challenges=challenges, batches=batches, macs=macs,
                circuits=circuits)


def _line(text, key):
    m = re.search(rf"^\s*(?:\{{ )?{key} := (.*)$", text, re.M)
    if not m:
        raise ValueError(f"program without {key}")
    return m.group(1)


def _items(line):
    """The top-level records of a one-line list, split at each '{ name := "'."""
    return [p for p in re.split(r'\{ name := "', line)[1:]]


def _merged(record):
    """A batch is merged when it has a merging challenge (Program.merged, `gamma.isSome`,
    GordieHowe/Plan/BatchRelation.lean); `gamma` defaults to `none` (Plan/IR.lean Batch)."""
    return re.search(r"\bgamma := (?:some )?\(?\d+", record) is not None


def _parts(record):
    """The batch's merged relations (`parts := [...]`, the Lean's Batch.parts), their count;
    None when the record has none."""
    m = re.search(r"\bparts := \[([^\]]*)\]", record)
    if not m:
        return None
    return len([x for x in m.group(1).split(",") if x.strip()])


def _bit_phase(record):
    """The batch's bit-index sumcheck rounds: 4 (the 4 bit-index variables of a GF(2^16) word)
    when the program's batch has `bitSumcheck := true` (the Lean's Batch.bitSumcheck), else 0. The plan export does not record it (_plan_bit_phase)."""
    return 4 if re.search(r"\bbitSumcheck := true\b", record) else 0


def _plan_bit_phase(record):
    """A plan batch's bit-index sumcheck rounds, which the plan does not record: 4 for a batch
    on bits (`operandField := "bit"`), since the compiler runs it on every batch on bits by
    default (every export's program agrees), else 0."""
    return 4 if re.search(r'\boperandField := "bit"', record) else 0


def _circuits(text):
    """The program's GKR circuits (`circuits := [«c.X», ...]`), each from its `def «c.X» :
    Circuit`: its domain, inputCount, layers and wires, at the structure's defaults (inputCount
    1, layers 0, wires 0; Plan/IR.lean Circuit) where the export omits one."""
    lst = re.search(r"^    circuits := \[(.*?)\]", text, re.M | re.S)
    defs = {n: body for n, body in re.findall(
        r"^(?:noncomputable )?def «([^»]+)» : Circuit :=\n  (\{ name := .*)$", text, re.M)}
    out = []
    for n in re.findall(r"«([^»]+)»", lst.group(1) if lst else ""):
        body = defs[n]

        def g(key, default):
            m = re.search(rf"[{{,] {key} := (\d+)", body)
            return int(m.group(1)) if m else default
        out.append(dict(name=n, domain=g("domain", 0), inputCount=g("inputCount", 1),
                        layers=g("layers", 0), wires=g("wires", 0)))
    return out


def parse_program(text):
    """The realized program: fields, domains, tables (groups' needle counts), challenges
    (field, phase, sampler range, role), batches (with whether each is merged), the MACs' keys
    and chunk counts, and the GKR circuits' shapes (domain, inputCount, layers, wires)."""
    phases = int(re.search(r"\{ phases := (\d+),", text).group(1))
    fields = [int(c) ** int(d) for c, d in re.findall(
        r'\{ name := "[^"]+", characteristic := (\d+), degree := (\d+) \}', _line(text, "fields"))]
    domains = [(n, int(f)) for n, f in re.findall(r'\{ name := "(\w+)", field := (\d+) \}',
                                                     _line(text, "domains"))]
    tables = []
    for it in _items(_line(text, "tables")):
        rows = re.search(r"rows := \.range (\d+)", it)
        groups = [sum(int(x) for x in re.findall(r"\(\d+, \d+, \d+, (\d+)\)", mem))
                  for mem in re.findall(r"members := \[([^\]]*)\]", it)]
        tables.append(dict(name=it.split('"', 1)[0],
                           domain=int(re.search(r"domain := (\d+)", it).group(1)),
                           size=int(rows.group(1)) if rows else 0,
                           alpha=int(re.search(r"alpha := (\d+)", it).group(1)),
                           groups=groups))
    challenges = []
    for it in _items(_line(text, "challenges")):
        tm = re.search(r"\.fieldMinusTables \(\.range (\d+)\)", it)
        challenges.append(dict(name=it.split('"', 1)[0],
                               field=int(re.search(r"field := (\d+)", it).group(1)),
                               phase=int(re.search(r"phase := (\d+)", it).group(1)),
                               tmax=int(tm.group(1)) if tm else 0,
                               source="role := .source" in it))
    batches = []
    for it in _items(_line(text, "batches")):
        def g(key):
            return int(re.search(rf"\b{key} := (\d+)", it).group(1))
        batches.append(dict(name=it.split('"', 1)[0], domain=g("domain"), degree=g("degree"),
                            width=g("width"), rounds=g("rounds"), instances=g("instances"),
                            merged=_merged(it), bit_phase=_bit_phase(it),
                            parts=_parts(it)))
    macs = [(int(k), int(c)) for k, c in
            re.findall(r"\.cross [^\n]*?key := (\d+),[^\n]*?chunks := (\d+)", text)]
    return dict(phases=phases, fields=fields, domains=domains, tables=tables,
                challenges=challenges, batches=batches, macs=macs, circuits=_circuits(text))


# ------------------------------------------------------------- the errors --

def phase_errors(prog, degree):
    """phase k (1-based) -> its error (Errors.lean:47-48): per challenge the source error
    degreeBound/|K| and the realization error (Realized.lean:364-372)."""
    out = {k: Fraction(0) for k in range(1, prog["phases"] + 1)}
    terms = {}
    for j, c in enumerate(prog["challenges"]):
        F = prog["fields"][c["field"]]
        e = Fraction(0)
        if c["source"]:
            if c["name"] not in degree:
                raise ValueError(f"source challenge {c['name']} has no degree bound in the plan")
            e += Fraction(degree[c["name"]], F)
        num = sum(n + t["size"] - 1 for t in prog["tables"] if t["alpha"] == j
                  for n in t["groups"])
        num += sum(ch for key, ch in prog["macs"] if key == j)
        if num:
            e += Fraction(num, F - c["tmax"])
        terms[c["name"]] = e
        out[c["phase"]] += e
    return out, terms


def batch_error(F, b):
    """A batch's errors, summed (the Lean's batchNum and mergedNum,
    GordieHowe/ProofSystem/Program/ForkFigures.lean): (r + D(w-1) + (D+1)r + 1)/|K| (r rounds,
    degree D, width w), the merging challenge's (parts - 1)/|K| when merged, and with its
    bit-index sumcheck (bitSumcheck) 2/|K| for each of its rounds."""
    r, w, D = b["rounds"], b["width"], b["degree"]
    num = r + D * (w - 1) + (D + 1) * r + 1 + 2 * b.get("bit_phase", 0)
    if b["merged"]:
        if b.get("parts") is None:
            raise ValueError(f"batch {b['name']}: merged, and its parts are not recorded")
        num += b["parts"] - 1
    return Fraction(num, F)


def gkr_width(layers, wires, inputs):
    """w = ceil(log2 max(wires, inputs)), the bound on every m_(j+1) (module docstring): a
    layer's input wires are at most wires, their sum over the layers."""
    if layers < 1:
        raise ValueError(f"a GKR circuit with {layers} layers")
    return max(1, (max(wires, inputs) - 1).bit_length())


def gkr_errors(F, layers, wires, inputs, m0=GKR_OUTPUT_VARS):
    """The GKR circuit's errors (paper lem:gkr(1), module docstring) at the plan's shape,
    exactly: each challenge kind's round error, their largest, and the sum over every challenge,
    at m_0 <= m0 and m_(j+1) <= w = gkr_width(layers, wires, inputs)."""
    w = gkr_width(layers, wires, inputs)
    if m0 > GKR_OUTPUT_VARS or w > GKR_OUTPUT_VARS:
        raise ValueError(f"a GKR circuit of width 2^{max(m0, w)}, above the verifier's 2^40")
    per = {"initial": Fraction(2 * m0, F), "layer": Fraction(2, F),
           "sumcheck_even": Fraction(3, F), "sumcheck_odd": Fraction(2, F),
           "input": Fraction(1, F)}
    return dict(per, round_max=max(per.values()),
                sum=Fraction(2 * m0 + 2 * layers + 5 * layers * w + 1, F),
                m0=m0, w=w, layers=layers)


def domain_gkr(dom):
    """The domain's GKR errors (gkr_errors), None when it has no circuit."""
    if dom["circuit"] is None:
        return None
    layers, wires = dom["circuit"]
    return gkr_errors(dom["F"], layers, wires, dom.get("inputs", 0))


def domain_ip(prog, dom, d_index):
    """The domain's masked-IP errors, summed: its batches, GKR's errors summed (gkr_errors),
    its combinations."""
    F = dom["F"]
    parts = {f"batch.{b['name']}": batch_error(F, b)
             for b in prog["batches"] if b["domain"] == d_index}
    gkr = domain_gkr(dom)
    if gkr is not None:
        parts["gkr"] = gkr["sum"]
    if dom["edges"]:
        parts["combinations"] = Fraction(dom["edges"], F)
    return parts


def plan_mismatch(plan, records):
    """None when the plan's tableaus, masking and circuit shapes equal the run's PQ_PARAMS
    records (half -> record), else the first difference."""
    if set(plan["domains"]) != set(records):
        return f"plan domains {sorted(plan['domains'])}, run {sorted(records)}"
    for h, e in sorted(records.items()):
        d = plan["domains"][h]
        lg, ci = e["half_params"]["ligero"], e["half_params"].get("circuit") or {}
        circuit = (ci.get("layers"), ci.get("wires"))
        # A domain without a circuit: its record's shape is (0, 0), its plan's none.
        if circuit == (0, 0):
            circuit = (None, None)
        run = (lg["N"], lg["k"], lg["t"], lg["nrow"], lg.get("ldt_reps", 1)) + circuit
        got = (d["N"], d["k"], d["t"], d["nrow"], d["ldt_reps"]) + (d["circuit"] or (None, None))
        if run != got:
            return (f"domain {h}: run (N, k, t, nrow, ldt_reps, layers, wires) {run}, "
                    f"plan {got}")
        if lg.get("masking") is not None and \
                (lg["masking"] == "split") != (d["masking"] == "split"):
            return f"domain {h}: run masking {lg['masking']}, plan {d['masking']}"
    return None


def gkr_round_lean(prog, dom, d_index):
    """The Lean's charge of a GKR round of the domain (Program.gkrRoundError,
    GordieHowe/ProofSystem/Program/FieldClaim.lean): max(3, 2 gkrWidth)/|K|, gkrWidth the largest
    circuitWidth = clog2 max(wires, inputCount) of its circuits; None without a circuit."""
    circs = [c for c in prog["circuits"] if c["domain"] == d_index]
    if not circs:
        return None
    w = max((max(c["wires"], c["inputCount"]) - 1).bit_length()
            if max(c["wires"], c["inputCount"]) > 1 else 0 for c in circs)
    return Fraction(max(3, 2 * w), dom["F"])


def case_errors(plan, prog, ligero):
    """Every error of a configuration. ligero: domain name -> dict(F, masking ('split' or
    'untested'), commit, test, column, subfield), the Ligero errors at the run's A and B (column
    without the subfield term).

    Returns dict(rounds, lean, domains, phases, terms):
      rounds      every round, or sub-protocol whose errors are summed (a batch, a phase), with
                  its error; "<domain>.gkr" is the largest GKR round (gkr_errors' round_max); the
                  per-round maximum is their largest
      lean        the charges of kappa (module docstring), each challenge charged its own error
                  (Program.FieldRoundsLe): phases, and per domain its commit, its batches summed,
                  a GKR round max(3, 2 gkrWidth)/|K| (gkr_round_lean), its combinations, the
                  test, and the column with the joint subfield term
      domains     per domain its masked inner-product parts (ip: each batch, GKR's summed
                  errors, the combinations) and Ligero parts (cp: test, column, subfield), and
                  its gkr_errors where it has a circuit
    Every domain is a tree domain, with one combination per packing edge, at either masking."""
    names = [n for n, _ in prog["domains"]]
    rounds, lean, domains = {}, {}, {}
    for i, n in enumerate(names):
        if n not in plan["domains"] or n not in ligero:
            raise ValueError(f"domain {n} is not in the plan and the run")
        lg = ligero[n]
        dom = dict(plan["domains"][n], F=lg["F"], config=plan["head"]["config"])
        untested = lg["masking"] != "split"
        ip = domain_ip(prog, dom, i)
        cp = {"test": lg["test"], "column": lg["column"], "subfield": lg["subfield"]}
        domains[n] = dict(ip=ip, cp=cp, untested=untested)
        rounds[f"{n}.commit"] = lg["commit"]
        rounds[f"{n}.test"] = lg["test"]
        rounds[f"{n}.column"] = lg["column"] + lg["subfield"]
        for key, v in ip.items():
            rounds[f"{n}.{key}"] = v
        # Each GKR round is charged its own error: the largest is the initial point's.
        gkr = domain_gkr(dom)
        if gkr is not None:
            rounds[f"{n}.gkr"] = gkr["round_max"]
            domains[n]["gkr"] = gkr
        lean[f"{n}.commit"] = lg["commit"]
        batches = sum(v for key, v in ip.items() if key.startswith("batch."))
        if batches:
            lean[f"{n}.batches"] = batches
        g = gkr_round_lean(prog, dom, i)
        if g is not None:
            lean[f"{n}.gkr"] = g
        if "combinations" in ip:
            lean[f"{n}.combinations"] = ip["combinations"]
        lean[f"{n}.test"] = lg["test"]
        lean[f"{n}.column"] = lg["column"] + lg["subfield"]
    phases, terms = phase_errors(prog, plan["degree"])
    for ph, v in phases.items():
        rounds[f"phase{ph}"] = lean[f"phase{ph}"] = v
    return dict(rounds=rounds, lean=lean, domains=domains, phases=phases, terms=terms)


def worst(errors):
    """The largest error of a dict and its key."""
    key = max(errors, key=errors.__getitem__)
    return errors[key], key


def read_lean(path):
    """The text of a .lean or .lean.gz file."""
    import gzip
    return (gzip.decompress(path.read_bytes()).decode() if path.suffix == ".gz"
            else path.read_text())


def plan_files(plans_dir):
    """[(plan, program)] paths of every plan export (.lean or .lean.gz) in the directory or below
    it, sorted: GordieHowe/Generated/<Lean name>/Plan.lean with Program.lean beside it, or
    the flat layout <Name>.lean with <Name>Program.lean. The program need not exist."""
    from pathlib import Path
    plans_dir = Path(plans_dir)
    out = []
    for p in sorted([*plans_dir.rglob("*.lean"), *plans_dir.rglob("*.lean.gz")]):
        stem = p.name.split(".")[0]
        # Program.lean is the plan's companion; Valid, Realize and Honest are
        # the Lean library's proof modules beside a configuration's plan, with
        # their per-condition modules in directories of the same names.
        proof = ("Valid", "Realize", "Honest")
        if stem.endswith("Program") or stem in proof or p.parent.name in proof:
            continue
        prog = "Program" if stem == "Plan" else stem + "Program"
        out.append((p, p.with_name(prog + p.name[len(stem):])))
    return out


def load_plans(plans_dir):
    """config -> [(plan, program, path)] for every plan export of plan_files, with its realized
    program, or the counts rebuilt from the plan where it has none (lean/ring-<R>/ holds the rings
    at other sizes; the file names carry no ring size), none when the directory is missing."""
    from pathlib import Path
    out = {}
    plans_dir = Path(plans_dir) if plans_dir is not None else None
    if plans_dir is None or not plans_dir.is_dir():
        return out
    read = read_lean
    for p, prog in plan_files(plans_dir):
        text = read(p)
        plan = parse_plan(text)
        name = str(p.relative_to(plans_dir))
        if prog.exists() and prog.stat().st_size > 0:
            program = parse_program(read(prog))
        else:
            # No realized program (the exporter does not cover the system): its counts from the
            # plan (program_from_plan).
            program = program_from_plan(text)
            name += " (plan only)"
        out.setdefault(plan["head"]["config"], []).append((plan, program, name))
    return out


def find_plan(plans, cfg, records):
    """The first plan of configuration CFG matching the records, as (plan, program, path), or a
    string saying why there is none."""
    if cfg not in plans:
        return f"no plan export for {cfg}"
    why = []
    for plan, prog, name in plans[cfg]:
        w = plan_mismatch(plan, records)
        if w is None:
            return plan, prog, name
        why.append(f"{name}: {w}")
    return "no plan matches the run: " + "; ".join(why)
