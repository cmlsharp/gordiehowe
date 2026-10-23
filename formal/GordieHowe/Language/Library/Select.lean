-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.Library.Eval
public import GordieHowe.Language.Library.Cross
public import GordieHowe.Applications.Falcon512.Gadgets.SelectFirstN
public import GordieHowe.Foundations.ToMathlib.ListRange
public import GordieHowe.Foundations.ToMathlib.List

@[expose] public section

/-!
# GordieHowe frontend: the first-`n` selection

The source program's selection of the first `n` of `S` samples below `bound` (the C++ `gp_select`):
four predicates and three shared expressions of a binary domain, which together are the gadget
`SelectFirstN.run` (`GordieHowe/Applications/Falcon512/Gadgets/SelectFirstN.lean`) on the samples, the selected words and
the route:

* `start`: `count[0] + 1 = 0`;
* `step`: `count[i+1] + count[i] · mux(acc[i], g, 1) = 0` for `i < S − 1`;
* `done`: `full[t] · (count[n + t] + g^n) = 0` for `t < S − n`;
* `route`: `Π_{t<S} mux(acc[t], δ + count[t] + X Σ_u stream[t w + u] e_u, 1) +
  Π_{j<n} (δ + g^j + X Σ_u raw[j w + u] e_u) = 0`;
* `acc[t]`: `lt[t]` for `t < n`, `lt[t] (1 − full[t − n])` after; `lt[t] = Logic::lt` of word `t` of
  the stream against the bits of `bound`; the stream a view of a bit view.

In characteristic two `a + b = 0` is `a = b` and `δ + x` is `δ − x`, which is how the gadget writes
them. The constants (`1`, `0`, `g`, `g^n`, `e_u`, `g^j`, the bits of `bound`, and `X = decode 2`)
are the program's constant values, whose decoded entries the caller supplies
(`SelectShape.Consts`).

* **The shape** (`GordieHowe.RealizedProgram.selectShape?`, `GordieHowe.RealizedProgram.SelectMatches`): Option-valued matchers on the
  four bodies and the three shared expressions return their identifiers when they have the shape
  above, with `S`, `n`, `w` the index maps' lengths.
* **The gadget** (`GordieHowe.RealizedProgram.SelectMatches.run`): where the four predicates and the source program
  hold, `SelectFirstN.run` holds on the readings `SelectShape.sample`, `SelectShape.word`,
  `SelectShape.route`, `SelectShape.deltaAt`.
* **Its soundness** (`GordieHowe.RealizedProgram.SelectMatches.firstAccepted_or_badAt`): the selected words are the
  first accepted samples, or the challenge `δ` is a root of the gadget's event
  (`SelectFirstN.badEvent`, degree `S`), which reads only the committed values
  (`GordieHowe.RealizedProgram.selectReadings_congr`).

The native Falcon programs' selection (`h2p.select.*` at `(S, n, w) = (639, 512, 16)`,
`bound = 61445 = 5q`) is read in `GordieHowe/Applications/Falcon512/Native/ROMParams/Frontend/Basic.lean`.
-/

namespace GordieHowe.RealizedProgram

open Export

/-! ## Characteristic two -/

/-- **In characteristic two, `a + b = 0` is `a = b`.** -/
theorem eq_of_add_eq_zero_charTwo {K : Type*} [Ring K] [CharP K 2] {a b : K} (h : a + b = 0) :
    a = b := by
  rw [eq_neg_of_add_eq_zero_left h, CharTwo.neg_eq]

/-! ## Matchers -/

/-- **`start`**: `count[0] + one = zero` in domain `d`. -/
structure SelectStart where
  /-- The domain. -/
  d : ℕ
  /-- The counter. -/
  count : ℕ
  /-- The constant `1`. -/
  one : ℕ
  /-- The constant `0`. -/
  zero : ℕ
  deriving DecidableEq, Repr

/-- **`start`**, read off a predicate body. -/
def PredBody.selectStart? : PredBody → Option SelectStart
  | .equal d (.add (.reindex i (.leaf c)) (.leaf one)) (.leaf z) _ =>
    if i = [(0, 0, 1)] then some ⟨d, c, one, z⟩ else none
  | _ => none

/-- **The body of a matched `start`.** -/
theorem PredBody.eq_of_selectStart? {b : PredBody} {s : SelectStart} (h : b.selectStart? = some s) :
    ∃ t, b = .equal s.d (.add (.reindex [(0, 0, 1)] (.leaf s.count)) (.leaf s.one))
      (.leaf s.zero) t := by
  unfold selectStart? at h
  split at h
  · split_ifs at h with hi
    cases h
    subst hi
    exact ⟨_, rfl⟩
  · cases h

/-- **`step`**: `count[i+1] + count[i] · mux(acc[i], g, one) = zeros` for `i < S − 1`. -/
structure SelectStep where
  /-- The domain. -/
  d : ℕ
  /-- The counter. -/
  count : ℕ
  /-- The acceptance bits (a shared expression). -/
  acc : ℕ
  /-- The constant `g`. -/
  g : ℕ
  /-- The constant `1`. -/
  one : ℕ
  /-- The constant zeros. -/
  zeros : ℕ
  deriving DecidableEq, Repr

/-- **`step`**, read off a predicate body, for `S` samples. -/
def PredBody.selectStep? (S : ℕ) : PredBody → Option SelectStep
  | .equal d (.add (.reindex i1 (.leaf c)) (.mul (.reindex i2 (.leaf c'))
      (.mux (.reindex i3 (.ref acc)) (.reindex i4 (.leaf g)) (.reindex i5 (.leaf one)))))
      (.leaf zeros) _ =>
    if c' = c ∧ i1 = [(1, 1, S - 1)] ∧ i2 = [(0, 1, S - 1)] ∧ i3 = [(0, 1, S - 1)] ∧
      i4 = [(0, 0, S - 1)] ∧ i5 = [(0, 0, S - 1)] then some ⟨d, c, acc, g, one, zeros⟩ else none
  | _ => none

/-- **The body of a matched `step`.** -/
theorem PredBody.eq_of_selectStep? {S : ℕ} {b : PredBody} {s : SelectStep}
    (h : b.selectStep? S = some s) :
    ∃ t, b = .equal s.d (.add (.reindex [(1, 1, S - 1)] (.leaf s.count))
      (.mul (.reindex [(0, 1, S - 1)] (.leaf s.count))
        (.mux (.reindex [(0, 1, S - 1)] (.ref s.acc)) (.reindex [(0, 0, S - 1)] (.leaf s.g))
          (.reindex [(0, 0, S - 1)] (.leaf s.one))))) (.leaf s.zeros) t := by
  unfold selectStep? at h
  split at h
  · split_ifs at h with hi
    cases h
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := hi
    exact ⟨_, rfl⟩
  · cases h

/-- **`done`**: `full[t] · (count[n + t] + gN) = zeros` for `t < S − n`. -/
structure SelectDone where
  /-- The domain. -/
  d : ℕ
  /-- The completion flags. -/
  full : ℕ
  /-- The counter. -/
  count : ℕ
  /-- The constant `g^n`. -/
  gN : ℕ
  /-- The constant zeros. -/
  zeros : ℕ
  deriving DecidableEq, Repr

/-- **`done`**, read off a predicate body, for `n` of `S` samples. -/
def PredBody.selectDone? (S n : ℕ) : PredBody → Option SelectDone
  | .equal d (.mul (.leaf full) (.add (.reindex i1 (.leaf c)) (.reindex i2 (.leaf gN))))
      (.leaf zeros) _ =>
    if i1 = [(n, 1, S - n)] ∧ i2 = [(0, 0, S - n)] then some ⟨d, full, c, gN, zeros⟩ else none
  | _ => none

/-- **The body of a matched `done`.** -/
theorem PredBody.eq_of_selectDone? {S n : ℕ} {b : PredBody} {s : SelectDone}
    (h : b.selectDone? S n = some s) :
    ∃ t, b = .equal s.d (.mul (.leaf s.full) (.add (.reindex [(n, 1, S - n)] (.leaf s.count))
      (.reindex [(0, 0, S - n)] (.leaf s.gN)))) (.leaf s.zeros) t := by
  unfold selectDone? at h
  split at h
  · split_ifs at h with hi
    cases h
    obtain ⟨rfl, rfl⟩ := hi
    exact ⟨_, rfl⟩
  · cases h

/-- **`route`**: the candidates' product plus the claims' product is `zero`. -/
structure SelectRoute where
  /-- The domain. -/
  d : ℕ
  /-- The acceptance bits (a shared expression). -/
  acc : ℕ
  /-- The challenge value `δ`. -/
  delta : ℕ
  /-- The counter. -/
  count : ℕ
  /-- The stream bits (a shared expression). -/
  stream : ℕ
  /-- The constant subfield basis `e_u`. -/
  basis : ℕ
  /-- The constant `1`. -/
  one : ℕ
  /-- The constant labels `g^j`. -/
  gpow : ℕ
  /-- The selected words' bits. -/
  raw : ℕ
  /-- The constant `0`. -/
  zero : ℕ
  deriving DecidableEq, Repr

/-- **`route`**, read off a predicate body, for `n` of `S` samples of `w` bits. -/
def PredBody.selectRoute? (S n w : ℕ) : PredBody → Option SelectRoute
  | .equal d (.add
      (.prod S' (.mux (.ref acc) (.add (.reindex i1 (.leaf δ)) (.add (.leaf c)
        (.scale (.const two) (.apply (.sum w') (.mul (.reindex i2 (.ref str))
          (.reindex i3 (.leaf basis))))))) (.reindex i4 (.leaf one))))
      (.prod n' (.add (.reindex i5 (.leaf δ')) (.add (.leaf gpow)
        (.scale (.const two') (.apply (.sum w'') (.mul (.reindex i6 (.leaf raw))
          (.reindex i7 (.leaf basis')))))))))
      (.leaf z) _ =>
    if S' = S ∧ n' = n ∧ w' = w ∧ w'' = w ∧ two = 2 ∧ two' = 2 ∧ δ' = δ ∧ basis' = basis ∧
      i1 = [(0, 0, S)] ∧ i2 = [(0, 1, w * S)] ∧ i3 = List.replicate S (0, 1, w) ∧
      i4 = [(0, 0, S)] ∧ i5 = [(0, 0, n)] ∧ i6 = [(0, 1, w * n)] ∧
      i7 = List.replicate n (0, 1, w) then
      some ⟨d, acc, δ, c, str, basis, one, gpow, raw, z⟩
    else none
  | _ => none

/-- **The body of a matched `route`.** -/
theorem PredBody.eq_of_selectRoute? {S n w : ℕ} {b : PredBody} {s : SelectRoute}
    (h : b.selectRoute? S n w = some s) :
    ∃ t, b = .equal s.d (.add
      (.prod S (.mux (.ref s.acc) (.add (.reindex [(0, 0, S)] (.leaf s.delta)) (.add (.leaf s.count)
        (.scale (.const 2) (.apply (.sum w) (.mul (.reindex [(0, 1, w * S)] (.ref s.stream))
          (.reindex (List.replicate S (0, 1, w)) (.leaf s.basis))))))) (.reindex [(0, 0, S)]
            (.leaf s.one))))
      (.prod n (.add (.reindex [(0, 0, n)] (.leaf s.delta)) (.add (.leaf s.gpow)
        (.scale (.const 2) (.apply (.sum w) (.mul (.reindex [(0, 1, w * n)] (.leaf s.raw))
          (.reindex (List.replicate n (0, 1, w)) (.leaf s.basis)))))))))
      (.leaf s.zero) t := by
  unfold selectRoute? at h
  split at h
  · split_ifs at h with hi
    cases h
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hi
    exact ⟨_, rfl⟩
  · cases h

/-- **The acceptance bits**: `lt` for the first `n` samples, `lt · (ones − full)` after. -/
structure SelectAcc where
  /-- The comparisons (a shared expression). -/
  lt : ℕ
  /-- The constant ones. -/
  ones : ℕ
  /-- The completion flags. -/
  full : ℕ
  deriving DecidableEq, Repr

/-- **The acceptance bits**, read off an expression, for `n` of `S` samples. -/
def Expr.selectAcc? (S n : ℕ) : Expr → Option SelectAcc
  | .reindex i1 (.concat (.reindex i2 (.ref lt)) (.mul (.reindex i3 (.ref lt'))
      (.sub (.leaf ones) (.leaf full)))) =>
    if lt' = lt ∧ i1 = [(0, 1, S)] ∧ i2 = [(0, 1, n)] ∧ i3 = [(n, 1, S - n)] then
      some ⟨lt, ones, full⟩
    else none
  | _ => none

/-- **The matched acceptance bits.** -/
theorem Expr.eq_of_selectAcc? {S n : ℕ} {e : Expr} {s : SelectAcc} (h : e.selectAcc? S n = some s) :
    e = .reindex [(0, 1, S)] (.concat (.reindex [(0, 1, n)] (.ref s.lt))
      (.mul (.reindex [(n, 1, S - n)] (.ref s.lt)) (.sub (.leaf s.ones) (.leaf s.full)))) := by
  unfold selectAcc? at h
  split at h
  · split_ifs at h with hi
    cases h
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
    rfl
  · cases h

/-- **The comparisons**: `Logic::lt` of word `t` of the stream against the bits of a constant. -/
structure SelectLt where
  /-- The stream bits (a shared expression). -/
  stream : ℕ
  /-- The constant bits of the bound. -/
  cutoff : ℕ
  deriving DecidableEq, Repr

/-- **The comparisons**, read off an expression, for `S` samples of `w` bits. -/
def Expr.selectLt? (S w : ℕ) : Expr → Option SelectLt
  | .logic .lt w' [.ref str, .reindex i (.leaf cutoff)] =>
    if w' = w ∧ i = List.replicate S (0, 1, w) then some ⟨str, cutoff⟩ else none
  | _ => none

/-- **The matched comparisons.** -/
theorem Expr.eq_of_selectLt? {S w : ℕ} {e : Expr} {s : SelectLt} (h : e.selectLt? S w = some s) :
    e = .logic .lt w [.ref s.stream, .reindex (List.replicate S (0, 1, w)) (.leaf s.cutoff)] := by
  unfold selectLt? at h
  split at h
  · split_ifs at h with hi
    cases h
    obtain ⟨rfl, rfl⟩ := hi
    rfl
  · cases h

/-! ## The selection's shape -/

/-- **The identifiers of a first-`n` selection** in a program: the domain, the values (the counter,
the completion flags, the challenge value `δ`, the selected words' bits), the shared expressions
(stream, comparisons, acceptance bits) and the constants. -/
structure SelectShape where
  /-- The domain. -/
  d : ℕ
  /-- The counter (`count`). -/
  count : ℕ
  /-- The completion flags (`full`). -/
  full : ℕ
  /-- The challenge value `δ`. -/
  delta : ℕ
  /-- The selected words' bits (`raw`). -/
  raw : ℕ
  /-- The stream bits (a shared expression). -/
  stream : ℕ
  /-- The comparisons (a shared expression). -/
  lt : ℕ
  /-- The acceptance bits (a shared expression). -/
  acc : ℕ
  /-- The constant `1`. -/
  one : ℕ
  /-- The constant `0`. -/
  zero : ℕ
  /-- The constant zeros of `step`. -/
  zerosStep : ℕ
  /-- The constant zeros of `done`. -/
  zerosDone : ℕ
  /-- The constant ones of the acceptance bits. -/
  ones : ℕ
  /-- The constant `g`. -/
  g : ℕ
  /-- The constant `g^n`. -/
  gN : ℕ
  /-- The constant subfield basis. -/
  basis : ℕ
  /-- The constant labels `g^j`. -/
  gpow : ℕ
  /-- The constant bits of the bound. -/
  cutoff : ℕ
  deriving DecidableEq, Repr

section

variable (ir : RealizedProgram)

/-- **Whether value `v` is a source value of type `Bit` whose node enforces it, of `m`
coordinates** (the completion flags). -/
def isNodeBit (v m : ℕ) : Bool :=
  decide (v < ir.values.length) && decide (ir.IsSourceValue v) &&
    (ir.value v).type == .bit && (ir.value v).typeSource == .node && (ir.value v).size == m

/-- **Whether value `z` is a constant whose entries are all `0`.** -/
def isZeroConst (z : ℕ) : Bool := ir.isConstant z && (ir.constEntries z).all (· == 0)

/-- **The coordinates of an expression of bits that may be nonzero**, when its structure makes every
coordinate `0` or `1` and the value `zv` reads `0`: a view of a bit view (every coordinate); a
view of a bit view `a` concatenated with `zv` (the coordinates that read `a`);
a sum of two such expressions with supports of one length and disjoint (the masked sum of views the
C++ writes for a sponge's squeezed stream). `none` for any other expression. -/
def bitSupport? (zv : ℕ) : Expr → Option (List Bool)
  | .reindex m (.leaf v) => if ir.isBitView v then some (m.toList.map fun _ => true) else none
  | .reindex m (.concat (.leaf a) (.leaf z)) =>
    if ir.isBitView a && z == zv then
      some (m.toList.map fun j => decide (j < (ir.value a).size))
    else none
  | .add x y =>
    match bitSupport? zv x, bitSupport? zv y with
    | some s, some s' =>
      if s.length = s'.length ∧ (List.zipWith (· && ·) s s').all (! ·) then
        some (List.zipWith (· || ·) s s')
      else none
    | _, _ => none
  | _ => none

/-- **The first-`n` selection of `S` samples of `w` bits** of the predicates `pStart`, `pStep`,
`pDone`, `pRoute`, when they and their shared expressions have the selection's shape: the bodies'
identifiers agree, the shared expressions are entries of the program, the constants are
constants, the selected words are a bit view, the stream is an expression of bits by its structure
(`bitSupport?`) over its `S w` coordinates, the constant `0` has only zero entries, and the
completion flags are a node-typed `Bit` source value of `S − n` coordinates. -/
def selectShape? (S n w pStart pStep pDone pRoute : ℕ) : Option SelectShape := do
  let st ← (ir.predicate pStart).body.selectStart?
  let sp ← (ir.predicate pStep).body.selectStep? S
  let dn ← (ir.predicate pDone).body.selectDone? S n
  let rt ← (ir.predicate pRoute).body.selectRoute? S n w
  let ac ← (ir.expr rt.acc).selectAcc? S n
  let lt ← (ir.expr ac.lt).selectLt? S w
  let sup ← ir.bitSupport? st.zero (ir.expr lt.stream)
  if sp.d = st.d ∧ dn.d = st.d ∧ rt.d = st.d ∧ sp.count = st.count ∧ dn.count = st.count ∧
      rt.count = st.count ∧ sp.one = st.one ∧ rt.one = st.one ∧ rt.zero = st.zero ∧
      sp.acc = rt.acc ∧ dn.full = ac.full ∧ lt.stream = rt.stream ∧
      rt.acc < ir.exprs.length ∧ ac.lt < ir.exprs.length ∧ rt.stream < ir.exprs.length ∧
      ir.isBitView rt.raw ∧ S * w ≤ sup.length ∧ ir.isZeroConst st.zero ∧
      ir.isNodeBit ac.full (S - n) ∧
      [st.one, st.zero, sp.g, sp.zeros, dn.gN, dn.zeros, rt.basis, rt.gpow, ac.ones,
        lt.cutoff].all ir.isConstant then
    some ⟨st.d, st.count, ac.full, rt.delta, rt.raw, rt.stream, ac.lt, rt.acc, st.one,
      st.zero, sp.zeros, dn.zeros, ac.ones, sp.g, dn.gN, rt.basis, rt.gpow, lt.cutoff⟩
  else none

variable {ir}

/-- **A selection's shape in a program** (what `selectShape?` checks): the four bodies, the three
shared expressions (entries of the program), the bit views, the completion flags and the
constants. -/
structure SelectMatches (S n w pStart pStep pDone pRoute : ℕ) (s : SelectShape) : Prop where
  /-- The body of `start`. -/
  start : ∃ t, (ir.predicate pStart).body = .equal s.d (.add (.reindex [(0, 0, 1)] (.leaf s.count))
    (.leaf s.one)) (.leaf s.zero) t
  /-- The body of `step`. -/
  step : ∃ t, (ir.predicate pStep).body = .equal s.d
    (.add (.reindex [(1, 1, S - 1)] (.leaf s.count))
      (.mul (.reindex [(0, 1, S - 1)] (.leaf s.count))
      (.mux (.reindex [(0, 1, S - 1)] (.ref s.acc)) (.reindex [(0, 0, S - 1)] (.leaf s.g))
        (.reindex [(0, 0, S - 1)] (.leaf s.one))))) (.leaf s.zerosStep) t
  /-- The body of `done`. -/
  done : ∃ t, (ir.predicate pDone).body = .equal s.d (.mul (.leaf s.full)
    (.add (.reindex [(n, 1, S - n)] (.leaf s.count)) (.reindex [(0, 0, S - n)] (.leaf s.gN))))
    (.leaf s.zerosDone) t
  /-- The body of `route`. -/
  route : ∃ t, (ir.predicate pRoute).body = .equal s.d (.add
    (.prod S (.mux (.ref s.acc) (.add (.reindex [(0, 0, S)] (.leaf s.delta)) (.add (.leaf s.count)
      (.scale (.const 2) (.apply (.sum w) (.mul (.reindex [(0, 1, w * S)] (.ref s.stream))
        (.reindex (List.replicate S (0, 1, w)) (.leaf s.basis))))))) (.reindex [(0, 0, S)]
          (.leaf s.one))))
    (.prod n (.add (.reindex [(0, 0, n)] (.leaf s.delta)) (.add (.leaf s.gpow)
      (.scale (.const 2) (.apply (.sum w) (.mul (.reindex [(0, 1, w * n)] (.leaf s.raw))
        (.reindex (List.replicate n (0, 1, w)) (.leaf s.basis)))))))))
    (.leaf s.zero) t
  /-- The acceptance bits. -/
  acc : ir.expr s.acc = .reindex [(0, 1, S)] (.concat (.reindex [(0, 1, n)] (.ref s.lt))
    (.mul (.reindex [(n, 1, S - n)] (.ref s.lt)) (.sub (.leaf s.ones) (.leaf s.full))))
  /-- The comparisons. -/
  lt : ir.expr s.lt = .logic .lt w [.ref s.stream, .reindex (List.replicate S (0, 1, w))
    (.leaf s.cutoff)]
  /-- The stream is an expression of bits by its structure, over its `S w` coordinates. -/
  stream : ∃ sup, ir.bitSupport? s.zero (ir.expr s.stream) = some sup ∧ S * w ≤ sup.length
  /-- The acceptance bits are an entry. -/
  acc_lt : s.acc < ir.exprs.length
  /-- The comparisons are an entry. -/
  lt_lt : s.lt < ir.exprs.length
  /-- The stream is an entry. -/
  stream_lt : s.stream < ir.exprs.length
  /-- The selected words are a bit view. -/
  raw : ir.isBitView s.raw = true
  /-- The constant `0` has only zero entries. -/
  zeroConst : ir.isZeroConst s.zero = true
  /-- The completion flags are a node-typed `Bit` source value of `S − n` coordinates. -/
  full : ir.isNodeBit s.full (S - n) = true
  /-- The constants are constants. -/
  consts : ∀ v ∈ [s.one, s.zero, s.g, s.zerosStep, s.gN, s.zerosDone, s.basis, s.gpow, s.ones,
    s.cutoff], ir.isConstant v = true

/-- **What `selectShape?` checks.** -/
theorem selectMatches_of_selectShape? {S n w pStart pStep pDone pRoute : ℕ} {s : SelectShape}
    (h : ir.selectShape? S n w pStart pStep pDone pRoute = some s) :
    ir.SelectMatches S n w pStart pStep pDone pRoute s := by
  unfold selectShape? at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨st, hst, sp, hsp, dn, hdn, rt, hrt, ac, hac, lt, hlt, sup, hsup, h⟩ := h
  split_ifs at h with hc
  cases h
  obtain ⟨hd1, hd2, hd3, hc1, hc2, hc3, ho1, ho2, hz, hacc, hfull, hstr, hacl, hltl, hstl, hraw,
    hbv, hzc, hnb, hcs⟩ := hc
  obtain ⟨t1, e1⟩ := PredBody.eq_of_selectStart? hst
  obtain ⟨t2, e2⟩ := PredBody.eq_of_selectStep? hsp
  obtain ⟨t3, e3⟩ := PredBody.eq_of_selectDone? hdn
  obtain ⟨t4, e4⟩ := PredBody.eq_of_selectRoute? hrt
  have e5 := Expr.eq_of_selectAcc? hac
  have e6 := Expr.eq_of_selectLt? hlt
  rw [List.all_eq_true] at hcs
  refine ⟨⟨t1, e1⟩, ⟨t2, ?_⟩, ⟨t3, ?_⟩, ⟨t4, ?_⟩, ?_, ?_, ⟨sup, ?_, hbv⟩, hacl, hltl, hstl, hraw,
    hzc, hnb, ?_⟩
  · rw [e2, hd1, hc1, hacc, ho1]
  · rw [e3, hd2, hc2, hfull]
  · rw [e4, hd3, hc3, ho2, hz]
  · exact e5
  · rw [e6, hstr]
  · rw [← hstr]
    exact hsup
  · exact hcs

end

/-! ## The readings -/

namespace Ops

variable {R : Type*} [CommRing R]

/-- **`a < b` on words of `w` bits reads only the first `w` coordinates.** -/
theorem ltWord_congr {w : ℕ} {a b a' b' : ℕ → R} (ha : ∀ t < w, a t = a' t)
    (hb : ∀ t < w, b t = b' t) : ltWord w a b = ltWord w a' b' := by
  unfold ltWord
  congr 1
  exact ltReduce_congr w 0 (fun t ht => by simpa using ha t ht) (fun t ht => by simpa using hb t ht)

end Ops

namespace SelectShape

variable {ir : RealizedProgram} {I : Interp} (s : SelectShape)

variable (ir) in
/-- **The selection's field**: its domain's. -/
abbrev field : ℕ := ir.domainField s.d

variable (ir) in
/-- **Sample `i` of the stream**: coordinates `i w, …, i w + w − 1` of the stream (a shared
expression), read in the selection's field. -/
def sample {S w : ℕ} (rd : ir.Valuation I) (i : Fin S) : BitWires (I (s.field ir)).K w :=
  fun b => ir.evalE rd (s.field ir) (.ref s.stream) (i * w + b)

variable (ir) in
/-- **Selected word `j`**: word `j` of `w` bits of the selected words' bits. -/
def word {n w : ℕ} (rd : ir.Valuation I) (j : Fin n) : BitWires (I (s.field ir)).K w :=
  ir.wordAt rd (s.field ir) s.raw w j

variable (ir) in
/-- **The route at sample `i`**: the counter's coordinate `i`, and from sample `n` on the completion
flag `i − n` (`0` before). -/
def route {S : ℕ} (rd : ir.Valuation I) (n : ℕ) (i : Fin S) :
    Falcon512.Route (I (s.field ir)).K :=
  ⟨ir.evalE rd (s.field ir) (.leaf s.count) i,
    if n ≤ (i : ℕ) then ir.evalE rd (s.field ir) (.leaf s.full) (i - n) else 0⟩

variable (ir) in
/-- **The challenge `δ`**: coordinate `0` of the challenge value. -/
def deltaAt (rd : ir.Valuation I) : (I (s.field ir)).K := ir.evalE rd (s.field ir) (.leaf s.delta) 0

variable (ir I) in
/-- **The selection's constants** for the selection field `F` and the bound `bound`, read in the
selection's field (`RealizedProgram.constRead`): `1`, `0`, the zeros, the ones, `g`, `g^n`, the subfield
basis `e_u`, the labels `g^j`, the bits of `bound`, and `X` the decoding of `2`. -/
structure Consts {S w : ℕ} (F : SelectionField (I (s.field ir)).K S w) (n bound : ℕ) : Prop where
  /-- `1`. -/
  one : ir.constRead I (s.field ir) s.one 0 = 1
  /-- `0`. -/
  zero : ir.constRead I (s.field ir) s.zero 0 = 0
  /-- The zeros of `step`. -/
  zerosStep : ∀ i < S - 1, ir.constRead I (s.field ir) s.zerosStep i = 0
  /-- The zeros of `done`. -/
  zerosDone : ∀ t < S - n, ir.constRead I (s.field ir) s.zerosDone t = 0
  /-- The ones of the acceptance bits. -/
  ones : ∀ t < S - n, ir.constRead I (s.field ir) s.ones t = 1
  /-- `g`. -/
  g : ir.constRead I (s.field ir) s.g 0 = F.g
  /-- `g^n`. -/
  gN : ir.constRead I (s.field ir) s.gN 0 = F.g ^ n
  /-- The subfield basis. -/
  basis : ∀ u : Fin w, ir.constRead I (s.field ir) s.basis u = F.e u
  /-- The labels `g^j`. -/
  gpow : ∀ j < n, ir.constRead I (s.field ir) s.gpow j = F.g ^ j
  /-- The bits of the bound. -/
  cutoff : ∀ u < w, ir.constRead I (s.field ir) s.cutoff u = Bits.constBit bound u
  /-- `X`, the decoding of `2`. -/
  two : (I (s.field ir)).decode 2 = F.X

end SelectShape

section

variable {ir : RealizedProgram} {I : Interp} {S n w pStart pStep pDone pRoute : ℕ} {s : SelectShape}

/-- **An expression of bits by its structure has bit coordinates** (`RealizedProgram.bitSupport?`): every
coordinate below its support's length is `0` or `1`, and `0` off the support, where the bit views
read bits (`hbit`) and the value `zv` reads `0` (`hz`). -/
theorem bitSupport?_spec {zv f : ℕ} {rd : ir.Valuation I}
    (hbit : ∀ v, ir.isBitView v = true → ∀ j,
      ir.evalE rd f (.leaf v) j = 0 ∨ ir.evalE rd f (.leaf v) j = 1)
    (hz : ∀ j, ir.evalE rd f (.leaf zv) j = 0) :
    ∀ (x : Expr) {sup : List Bool}, ir.bitSupport? zv x = some sup →
      ∀ (i : ℕ) (hi : i < sup.length), (sup[i] = false → ir.evalE rd f x i = 0) ∧
        (ir.evalE rd f x i = 0 ∨ ir.evalE rd f x i = 1)
  | .add x y, sup, h, i, hi => by
    simp only [bitSupport?] at h
    split at h
    · rename_i s s' hs hs'
      split_ifs at h with hc
      cases h
      obtain ⟨hlen, hdis⟩ := hc
      have hi' : i < s.length := by
        simp only [List.length_zipWith, hlen, Nat.min_self] at hi
        rw [hlen]
        exact hi
      have hi'' : i < s'.length := hlen ▸ hi'
      obtain ⟨hx0, hxb⟩ := bitSupport?_spec hbit hz x hs i hi'
      obtain ⟨hy0, hyb⟩ := bitSupport?_spec hbit hz y hs' i hi''
      have hd : (!(s[i] && s'[i])) = true := by
        have hmem := List.getElem_mem (l := List.zipWith (· && ·) s s')
          (n := i) (by simp only [List.length_zipWith, hlen, Nat.min_self]; exact hi'')
        have := (List.all_eq_true.1 hdis) _ hmem
        simpa [List.getElem_zipWith] using this
      rw [List.getElem_zipWith, evalE_add]
      cases hsi : s[i]
      · rw [hx0 hsi, zero_add]
        refine ⟨fun h' => ?_, hyb⟩
        simp only [Bool.false_or] at h'
        exact hy0 h'
      · have hs'i : s'[i] = false := by simpa [hsi] using hd
        rw [hy0 hs'i, add_zero]
        exact ⟨fun h' => by simp [hsi] at h', hxb⟩
    · cases h
  | .reindex m x, sup, h, i, hi => by
    unfold bitSupport? at h
    split at h
    · rename_i v heq
      cases heq
      split_ifs at h with hv
      cases h
      refine ⟨fun h' => by simp at h', ?_⟩
      rw [evalE_reindex]
      exact hbit v hv _
    · rename_i a z heq
      cases heq
      split_ifs at h with hc
      cases h
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      obtain ⟨ha, rfl⟩ := hc
      have hi' : i < m.toList.length := by simpa using hi
      have hentry : m.entry i = m.toList[i] := by
        rw [IndexMap.entry_eq_getD_toList, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi',
          Option.getD_some]
      rw [evalE_reindex, evalE_concat, exprLen_leaf, hentry]
      simp only [List.getElem_map]
      split_ifs with hlt
      · exact ⟨fun h' => by simp [hlt] at h', hbit a ha _⟩
      · exact ⟨fun _ => hz _, .inl (hz _)⟩
    · rename_i heq
      cases heq
    · cases h
  | .leaf _, _, h, _, _ => by simp [bitSupport?] at h
  | .sub _ _, _, h, _, _ => by simp [bitSupport?] at h
  | .scale _ _, _, h, _, _ => by simp [bitSupport?] at h
  | .mul _ _, _, h, _, _ => by simp [bitSupport?] at h
  | .concat _ _, _, h, _, _ => by simp [bitSupport?] at h
  | .linear _ _, _, h, _, _ => by simp [bitSupport?] at h
  | .prod _ _, _, h, _, _ => by simp [bitSupport?] at h
  | .mux _ _ _, _, h, _, _ => by simp [bitSupport?] at h
  | .apply _ _, _, h, _, _ => by simp [bitSupport?] at h
  | .ref _, _, h, _, _ => by simp [bitSupport?] at h
  | .logic _ _ _, _, h, _, _ => by simp [bitSupport?] at h

/-- **A constant all of whose entries are `0` reads `0`** at every coordinate where it reads `0` at
coordinate `0`. -/
theorem constRead_of_isZeroConst {z : ℕ} (hz : ir.isZeroConst z = true) (f j : ℕ) :
    ir.constRead I f z j = ir.constRead I f z 0 := by
  unfold isZeroConst at hz
  simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at hz
  have hzero : ∀ k, (ir.constEntries z).getD k 0 = 0 := fun k => by
    rw [List.getD_eq_getElem?_getD]
    cases h : (ir.constEntries z)[k]? with
    | none => rfl
    | some c =>
      rw [Option.getD_some]
      exact hz.2 c (List.mem_of_getElem? h)
  unfold constRead
  rw [hzero j, hzero 0]

/-- **The stream's coordinates are bits**, below `S w`: an expression of bits by its structure
(`bitSupport?`), whose bit views read bits and whose zero constant is the selection's `0`
(`Consts.zero`). -/
theorem SelectMatches.stream_bool (hm : ir.SelectMatches S n w pStart pStep pDone pRoute s)
    (ho : ir.RefsOrdered) {F : SelectionField (I (s.field ir)).K S w} {bound : ℕ}
    (hc : s.Consts ir I F n bound) (e : ir.Env I) {i : ℕ} (hi : i < S * w) :
    ir.evalE (ir.reader e) (s.field ir) (.ref s.stream) i = 0 ∨
      ir.evalE (ir.reader e) (s.field ir) (.ref s.stream) i = 1 := by
  obtain ⟨sup, hsup, hlen⟩ := hm.stream
  have hz0 := hm.consts s.zero (by simp)
  rw [evalE_ref ho _ _ hm.stream_lt]
  refine (bitSupport?_spec (fun v hv j => evalE_leaf_bool_of_isBitView e hv _ j) (fun j => ?_)
    _ hsup i (by omega)).2
  rw [evalE_leaf_of_isConstant e hz0, constRead_of_isZeroConst hm.zeroConst _ j, hc.zero]

/-- **Coordinate `t` of sample `i` lies below `S w`.** -/
theorem sample_coord_lt {S w i t : ℕ} (hi : i < S) (ht : t < w) : i * w + t < S * w :=
  calc i * w + t < (i + 1) * w := by rw [Nat.succ_mul]; omega
    _ ≤ S * w := Nat.mul_le_mul_right _ hi

/-- **The stream's samples are Boolean.** -/
theorem SelectMatches.stream_allBool (hm : ir.SelectMatches S n w pStart pStep pDone pRoute s)
    (ho : ir.RefsOrdered) {F : SelectionField (I (s.field ir)).K S w} {bound : ℕ}
    (hc : s.Consts ir I F n bound) (e : ir.Env I) (i : Fin S) :
    Bits.AllBool (s.sample ir (w := w) (ir.reader e) i) := fun b =>
  hm.stream_bool ho hc e (sample_coord_lt i.isLt b.isLt)

/-- **The selected words are Boolean.** -/
theorem SelectMatches.out_allBool (hm : ir.SelectMatches S n w pStart pStep pDone pRoute s)
    (e : ir.Env I) (j : Fin n) : Bits.AllBool (s.word ir (w := w) (ir.reader e) j) :=
  fun _ => evalE_leaf_bool_of_isBitView e hm.raw _ _

/-- **A constant of the selection reads its constant.** -/
theorem SelectMatches.evalE_const (hm : ir.SelectMatches S n w pStart pStep pDone pRoute s)
    (e : ir.Env I) {v : ℕ}
    (hv : v ∈ [s.one, s.zero, s.g, s.zerosStep, s.gN, s.zerosDone, s.basis, s.gpow, s.ones,
      s.cutoff]) (f i : ℕ) :
    ir.evalE (ir.reader e) f (.leaf v) i = ir.constRead I f v i :=
  evalE_leaf_of_isConstant e (hm.consts v hv) f i

/-- **The comparison of sample `i` with the bound** (`Logic::lt` against the bound's bits) is the
gadget's comparator `Bits.ltConst`. -/
theorem SelectMatches.lt_eq (hm : ir.SelectMatches S n w pStart pStep pDone pRoute s)
    (ho : ir.RefsOrdered) {F : SelectionField (I (s.field ir)).K S w} {bound : ℕ}
    (hc : s.Consts ir I F n bound) (hb : bound < 2 ^ w) (e : ir.Env I) (i : Fin S) :
    ir.evalE (ir.reader e) (s.field ir) (.ref s.lt) i =
      Bits.ltConst (s.sample ir (w := w) (ir.reader e) i) bound := by
  rw [evalE_ref ho _ _ hm.lt_lt, hm.lt, evalE_logic_lt]
  rw [Ops.ltWord_congr (b' := fun t => Bits.constBit bound t) (fun _ _ => rfl) fun t ht => by
    rw [evalE_reindex, IndexMap.entry_replicate (by
      have := i.isLt
      nlinarith), hm.evalE_const e (by simp) _ _]
    have : (i * w + t) % w = t := by
      rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt ht]
    rw [this]
    simpa using hc.cutoff t ht]
  exact Ops.ltWord_eq_ltConst (fun t ht => hm.stream_bool ho hc e (sample_coord_lt i.isLt ht)) hb

/-- **The acceptance bit of sample `i`** is the gadget's `SelectFirstN.selected`: the comparison
for the first `n` samples, the comparison times `1 − full` after. -/
theorem SelectMatches.acc_eq (hm : ir.SelectMatches S n w pStart pStep pDone pRoute s)
    (ho : ir.RefsOrdered) {F : SelectionField (I (s.field ir)).K S w} {bound : ℕ}
    (hc : s.Consts ir I F n bound) (hb : bound < 2 ^ w) (e : ir.Env I) (i : Fin S) :
    ir.evalE (ir.reader e) (s.field ir) (.ref s.acc) i =
      Falcon512.SelectFirstN.selected n bound (s.sample ir (w := w) (ir.reader e))
        (s.route ir (ir.reader e) n) i := by
  rw [evalE_ref ho _ _ hm.acc_lt, hm.acc, evalE_reindex, IndexMap.entry_step_one i.isLt,
    Nat.zero_add, evalE_concat, exprLen_reindex, IndexMap.size_single]
  unfold Falcon512.SelectFirstN.selected
  by_cases hi : (i : ℕ) < n
  · rw [if_pos hi, if_pos hi, evalE_reindex, IndexMap.entry_step_one hi, Nat.zero_add]
    exact hm.lt_eq ho hc hb e i
  · have hni : n ≤ (i : ℕ) := Nat.le_of_not_lt hi
    have hlt : (i : ℕ) - n < S - n := by have := i.isLt; omega
    rw [if_neg hi, if_neg hi, evalE_mul, evalE_reindex, IndexMap.entry_step_one hlt, evalE_sub,
      hm.evalE_const e (v := s.ones) (by simp), hc.ones _ hlt, show n + ((i : ℕ) - n) = i by omega,
      hm.lt_eq ho hc hb e i]
    simp [SelectShape.route, hni]

/-- **The completion flags are bits** where the source program holds: a node-typed `Bit` source
value. -/
theorem SelectMatches.full_bool (hm : ir.SelectMatches S n w pStart pStep pDone pRoute s)
    {e : ir.Env I} (h : ir.SourceSatAt e) (f : ℕ) {t : ℕ} (ht : t < S - n) :
    ir.evalE (ir.reader e) f (.leaf s.full) t = 0 ∨
      ir.evalE (ir.reader e) f (.leaf s.full) t = 1 := by
  have hf := hm.full
  simp only [isNodeBit, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hf
  obtain ⟨⟨⟨⟨hlen, hsrc⟩, hty⟩, hts⟩, hsz⟩ := hf
  have := h.types s.full hlen hsrc hts t (by rw [hsz]; exact ht)
  rw [hty] at this
  exact castElt_bool this

/-- **The counter starts at `1`** (`start`). -/
theorem SelectMatches.count_zero (hm : ir.SelectMatches S n w pStart pStep pDone pRoute s)
    {F : SelectionField (I (s.field ir)).K S w} {bound : ℕ} (hc : s.Consts ir I F n bound)
    [CharP (I (s.field ir)).K 2] {e : ir.Env I} (h : ir.HoldsAt e (ir.predicate pStart).body) :
    ir.evalE (ir.reader e) (s.field ir) (.leaf s.count) 0 = 1 := by
  obtain ⟨t, hbody⟩ := hm.start
  rw [hbody] at h
  have h0 := h 0 (by rw [exprLen_add, exprLen_reindex, IndexMap.size_single]; omega)
  change ir.evalE _ _ _ 0 + ir.evalE _ _ _ 0 = ir.evalE _ _ _ 0 at h0
  rw [evalE_reindex, IndexMap.entry_step_zero (by omega), hm.evalE_const e (v := s.one) (by simp),
    hm.evalE_const e (v := s.zero) (by simp), hc.one, hc.zero] at h0
  exact eq_of_add_eq_zero_charTwo h0

/-- **The counter advances by `g` exactly on an accepted sample** (`step`). -/
theorem SelectMatches.count_succ (hm : ir.SelectMatches S n w pStart pStep pDone pRoute s)
    (ho : ir.RefsOrdered) {F : SelectionField (I (s.field ir)).K S w} {bound : ℕ}
    (hc : s.Consts ir I F n bound) (hb : bound < 2 ^ w) [CharP (I (s.field ir)).K 2]
    {e : ir.Env I} (h : ir.HoldsAt e (ir.predicate pStep).body) (i : Fin S) (hi : (i : ℕ) + 1 < S) :
    ir.evalE (ir.reader e) (s.field ir) (.leaf s.count) (i + 1) =
      ir.evalE (ir.reader e) (s.field ir) (.leaf s.count) i *
        SelectScan.mux (Falcon512.SelectFirstN.selected n bound (s.sample ir (w := w) (ir.reader e))
          (s.route ir (ir.reader e) n) i) F.g 1 := by
  obtain ⟨t, hbody⟩ := hm.step
  rw [hbody] at h
  have hi' : (i : ℕ) < S - 1 := by omega
  have h0 := h i (by rw [exprLen_add, exprLen_reindex, IndexMap.size_single]; exact hi')
  change ir.evalE _ _ _ i + ir.evalE _ _ _ i * (ir.evalE _ _ _ i * ir.evalE _ _ _ i +
    (1 - ir.evalE _ _ _ i) * ir.evalE _ _ _ i) = ir.evalE _ _ _ i at h0
  simp only [evalE_reindex, IndexMap.entry_step_one hi', IndexMap.entry_step_zero hi'] at h0
  rw [hm.evalE_const e (v := s.g) (by simp), hm.evalE_const e (v := s.one) (by simp),
    hm.evalE_const e (v := s.zerosStep) (by simp), hc.g, hc.one, hc.zerosStep _ hi', Nat.zero_add,
    hm.acc_eq ho hc hb e i, Nat.add_comm 1] at h0
  rw [eq_of_add_eq_zero_charTwo h0, SelectScan.mux, mul_one]

/-- **A completion flag is a bit, and is `0` unless the counter has reached `g^n`** (`done`). -/
theorem SelectMatches.full_done (hm : ir.SelectMatches S n w pStart pStep pDone pRoute s)
    {F : SelectionField (I (s.field ir)).K S w} {bound : ℕ} (hc : s.Consts ir I F n bound)
    [CharP (I (s.field ir)).K 2] {e : ir.Env I} (hs : ir.SourceSatAt e)
    (h : ir.HoldsAt e (ir.predicate pDone).body) (i : Fin S) (hi : n ≤ (i : ℕ)) :
    (s.route ir (ir.reader e) n i).full * ((s.route ir (ir.reader e) n i).full - 1) = 0 ∧
      (s.route ir (ir.reader e) n i).full *
        ((s.route ir (ir.reader e) n i).count_enc - F.g ^ n) = 0 := by
  have ht : (i : ℕ) - n < S - n := by have := i.isLt; omega
  simp only [SelectShape.route, if_pos hi]
  refine ⟨?_, ?_⟩
  · rcases hm.full_bool hs (s.field ir) ht with h0 | h1
    · rw [h0, zero_mul]
    · rw [h1, sub_self, mul_zero]
  · obtain ⟨t, hbody⟩ := hm.done
    rw [hbody] at h
    have hf := hm.full
    simp only [isNodeBit, Bool.and_eq_true, beq_iff_eq] at hf
    have h0 := h ((i : ℕ) - n) (by rw [exprLen_mul, exprLen_leaf, hf.2]; exact ht)
    change ir.evalE _ _ _ _ * (ir.evalE _ _ _ _ + ir.evalE _ _ _ _) = ir.evalE _ _ _ _ at h0
    simp only [evalE_reindex, IndexMap.entry_step_one ht, IndexMap.entry_step_zero ht] at h0
    rw [hm.evalE_const e (v := s.gN) (by simp), hm.evalE_const e (v := s.zerosDone) (by simp),
      hc.gN, hc.zerosDone _ ht, show n + ((i : ℕ) - n) = i by omega] at h0
    rw [CharTwo.sub_eq_add]
    exact h0

/-- Coordinate `u` of word `i` of `w` lies below `S w` for `i < S`, `u < w`. -/
theorem mul_add_lt_mul {i S u w : ℕ} (hi : i < S) (hu : u < w) : i * w + u < S * w :=
  calc i * w + u < i * w + w := by omega
    _ = (i + 1) * w := by ring
    _ ≤ S * w := Nat.mul_le_mul_right _ hi

/-- **The packed sample `i`** (`sum_w` of the stream's word times the basis) is the gadget's
`embedBits` of sample `i`. -/
theorem SelectMatches.sum_sample (hm : ir.SelectMatches S n w pStart pStep pDone pRoute s)
    {F : SelectionField (I (s.field ir)).K S w} {bound : ℕ} (hc : s.Consts ir I F n bound)
    (e : ir.Env I) (i : Fin S) :
    ∑ u : Fin w, ir.evalE (ir.reader e) (s.field ir)
      (.mul (.reindex [(0, 1, w * S)] (.ref s.stream))
        (.reindex (List.replicate S (0, 1, w)) (.leaf s.basis))) (i * w + u) =
      F.embedBits le_rfl (s.sample ir (w := w) (ir.reader e) i) := by
  unfold SelectionField.embedBits
  refine Finset.sum_congr rfl fun u _ => ?_
  have hl := mul_add_lt_mul i.isLt u.isLt
  rw [evalE_mul, evalE_reindex, IndexMap.entry_step_one (by rw [Nat.mul_comm w]; exact hl),
    Nat.zero_add, evalE_reindex, IndexMap.entry_replicate hl,
    hm.evalE_const e (v := s.basis) (by simp)]
  have hu : (((0 : ℕ) : ℤ) + 1 * (((i : ℕ) * w + u) % w : ℕ)).toNat = u := by
    rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt u.isLt]
    simp
  rw [hu, hc.basis u, Fin.castLE_rfl, id]
  rfl

/-- **The packed selected word `j`** is the gadget's `embedBits` of word `j`. -/
theorem SelectMatches.sum_word (hm : ir.SelectMatches S n w pStart pStep pDone pRoute s)
    {F : SelectionField (I (s.field ir)).K S w} {bound : ℕ} (hc : s.Consts ir I F n bound)
    (e : ir.Env I) (j : Fin n) :
    ∑ u : Fin w, ir.evalE (ir.reader e) (s.field ir) (.mul (.reindex [(0, 1, w * n)] (.leaf s.raw))
      (.reindex (List.replicate n (0, 1, w)) (.leaf s.basis))) (j * w + u) =
      F.embedBits le_rfl (s.word ir (w := w) (ir.reader e) j) := by
  unfold SelectionField.embedBits
  refine Finset.sum_congr rfl fun u _ => ?_
  have hl := mul_add_lt_mul j.isLt u.isLt
  rw [evalE_mul, evalE_reindex, IndexMap.entry_step_one (by rw [Nat.mul_comm w]; exact hl),
    Nat.zero_add, evalE_reindex, IndexMap.entry_replicate hl,
    hm.evalE_const e (v := s.basis) (by simp)]
  have hu : (((0 : ℕ) : ℤ) + 1 * (((j : ℕ) * w + u) % w : ℕ)).toNat = u := by
    rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt u.isLt]
    simp
  rw [hu, hc.basis u, Fin.castLE_rfl, id]
  rfl

/-- **The fingerprint** (`route`): the candidates' product over the accepted samples equals the
claims' product over the selected words, at `δ`. -/
theorem SelectMatches.fingerprint (hm : ir.SelectMatches S n w pStart pStep pDone pRoute s)
    (ho : ir.RefsOrdered) {F : SelectionField (I (s.field ir)).K S w} {bound : ℕ}
    (hc : s.Consts ir I F n bound) (hb : bound < 2 ^ w) [CharP (I (s.field ir)).K 2]
    (hS : 0 < S) {e : ir.Env I} (h : ir.HoldsAt e (ir.predicate pRoute).body) :
    (List.finRange S).foldl (fun acc i => acc *
        SelectScan.mux (Falcon512.SelectFirstN.selected n bound (s.sample ir (w := w) (ir.reader e))
          (s.route ir (ir.reader e) n) i)
          (s.deltaAt ir (ir.reader e) - Falcon512.SelectFirstN.enc F (s.route ir (ir.reader e) n i).count_enc
            (s.sample ir (ir.reader e) i)) 1) 1 =
      (List.finRange n).foldl (fun acc (j : Fin n) => acc *
        (s.deltaAt ir (ir.reader e) - Falcon512.SelectFirstN.enc F (F.g ^ (j : ℕ))
          (s.word ir (w := w) (ir.reader e) j))) 1 := by
  obtain ⟨t, hbody⟩ := hm.route
  rw [hbody] at h
  have h0 := h 0 (by
    rw [exprLen_add, exprLen_prod, exprLen_mux, exprLen_add, exprLen_reindex,
      IndexMap.size_single, Nat.div_self hS]
    omega)
  change ir.evalE _ _ (.prod S _) 0 + ir.evalE _ _ (.prod n _) 0 = ir.evalE _ _ _ 0 at h0
  rw [evalE_prod, evalE_prod, List.prod_map_range, List.prod_map_range,
    hm.evalE_const e (v := s.zero) (by simp), hc.zero] at h0
  rw [List.finRange_foldl_mul_eq_prod, List.finRange_foldl_mul_eq_prod]
  refine eq_of_add_eq_zero_charTwo (Eq.trans ?_ h0)
  congr 1
  · refine Finset.prod_congr rfl fun i _ => ?_
    rw [Nat.zero_mul, Nat.zero_add, evalE_mux, hm.acc_eq ho hc hb e i, evalE_add, evalE_reindex,
      IndexMap.entry_step_zero i.isLt, evalE_add, evalE_scale_const, evalE_apply_sum,
      hm.sum_sample hc e i, evalE_reindex, IndexMap.entry_step_zero i.isLt,
      hm.evalE_const e (v := s.one) (by simp), hc.one, hc.two, SelectScan.mux, Falcon512.SelectFirstN.enc,
      CharTwo.sub_eq_add]
    rfl
  · refine Finset.prod_congr rfl fun j _ => ?_
    rw [Nat.zero_mul, Nat.zero_add, evalE_add, evalE_reindex, IndexMap.entry_step_zero j.isLt,
      evalE_add, hm.evalE_const e (v := s.gpow) (by simp), hc.gpow _ j.isLt, evalE_scale_const,
      evalE_apply_sum, hm.sum_word hc e j, hc.two, Falcon512.SelectFirstN.enc, CharTwo.sub_eq_add]
    rfl

/-- **The selection's predicates are the gadget `SelectFirstN.run`** on the stream's samples, the
selected words, the route and `δ`, where they hold and the source program holds (the completion
flags' Booleanity is the source program's type check). -/
theorem SelectMatches.run (hm : ir.SelectMatches S n w pStart pStep pDone pRoute s)
    (ho : ir.RefsOrdered) {F : SelectionField (I (s.field ir)).K S w} {bound : ℕ}
    (hc : s.Consts ir I F n bound) (hb : bound < 2 ^ w) [CharP (I (s.field ir)).K 2]
    (hS : 0 < S) {e : ir.Env I} (hs : ir.SourceSatAt e)
    (hstart : ir.HoldsAt e (ir.predicate pStart).body)
    (hstep : ir.HoldsAt e (ir.predicate pStep).body)
    (hdone : ir.HoldsAt e (ir.predicate pDone).body)
    (hroute : ir.HoldsAt e (ir.predicate pRoute).body) :
    Falcon512.SelectFirstN.run F bound (s.sample ir (ir.reader e)) (s.word ir (n := n) (ir.reader e))
      (s.route ir (ir.reader e) n) (s.deltaAt ir (ir.reader e)) = true := by
  unfold Falcon512.SelectFirstN.run
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_finRange, forall_const,
    decide_eq_true_eq, Bool.or_eq_true]
  refine ⟨⟨⟨⟨fun i => Bits.ltConst_mul_sub_one (hm.stream_allBool ho hc e i) hb, fun i => ?_⟩,
    fun i => ?_⟩, fun i => ?_⟩, hm.fingerprint ho hc hb hS hroute⟩
  · by_cases hi : (i : ℕ) = 0
    · right
      have h0 := hm.count_zero hc hstart
      simp only [SelectShape.route, hi]
      exact h0
    · left
      simpa using hi
  · by_cases hi : (i : ℕ) < n
    · left
      exact hi
    · right
      obtain ⟨h1, h2⟩ := hm.full_done hc hs hdone i (Nat.le_of_not_lt hi)
      exact ⟨h1, h2⟩
  · split
    · rename_i hi
      exact decide_eq_true (hm.count_succ ho hc hb hstep i hi)
    · rfl

/-- **The gadget's constraints give the selection's predicates** (the converse of
`SelectMatches.run`): where `SelectFirstN.run` holds on the readings, `start`, `step`, `done` and
`route` hold. -/
theorem SelectMatches.holds_of_run (hm : ir.SelectMatches S n w pStart pStep pDone pRoute s)
    (ho : ir.RefsOrdered) {F : SelectionField (I (s.field ir)).K S w} {bound : ℕ}
    (hc : s.Consts ir I F n bound) (hb : bound < 2 ^ w) [CharP (I (s.field ir)).K 2]
    (hS : 0 < S) {e : ir.Env I}
    (h : Falcon512.SelectFirstN.run F bound (s.sample ir (ir.reader e)) (s.word ir (n := n) (ir.reader e))
      (s.route ir (ir.reader e) n) (s.deltaAt ir (ir.reader e)) = true) :
    ir.HoldsAt e (ir.predicate pStart).body ∧ ir.HoldsAt e (ir.predicate pStep).body ∧
      ir.HoldsAt e (ir.predicate pDone).body ∧ ir.HoldsAt e (ir.predicate pRoute).body := by
  unfold Falcon512.SelectFirstN.run at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_finRange, forall_const,
    decide_eq_true_eq, Bool.or_eq_true] at h
  obtain ⟨⟨⟨⟨-, h1⟩, h2⟩, h3⟩, h4⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨t, hbody⟩ := hm.start
    rw [HoldsAt, hbody]
    intro i hi
    rw [exprLen_add, exprLen_reindex, IndexMap.size_single] at hi
    obtain rfl : i = 0 := by omega
    change ir.evalE _ _ _ 0 + ir.evalE _ _ _ 0 = ir.evalE _ _ _ 0
    rw [evalE_reindex, IndexMap.entry_step_zero (by omega), hm.evalE_const e (v := s.one) (by simp),
      hm.evalE_const e (v := s.zero) (by simp), hc.one, hc.zero]
    rcases h1 ⟨0, hS⟩ with h0 | h0
    · exact absurd rfl h0
    · simp only [SelectShape.route] at h0
      rw [h0]
      exact CharTwo.add_self_eq_zero 1
  · obtain ⟨t, hbody⟩ := hm.step
    rw [HoldsAt, hbody]
    intro i hi
    rw [exprLen_add, exprLen_reindex, IndexMap.size_single] at hi
    change ir.evalE _ _ _ i + ir.evalE _ _ _ i * (ir.evalE _ _ _ i * ir.evalE _ _ _ i +
      (1 - ir.evalE _ _ _ i) * ir.evalE _ _ _ i) = ir.evalE _ _ _ i
    simp only [evalE_reindex, IndexMap.entry_step_one hi, IndexMap.entry_step_zero hi]
    rw [hm.evalE_const e (v := s.g) (by simp), hm.evalE_const e (v := s.one) (by simp),
      hm.evalE_const e (v := s.zerosStep) (by simp), hc.g, hc.one, hc.zerosStep _ hi, Nat.zero_add,
      hm.acc_eq ho hc hb e ⟨i, by omega⟩, Nat.add_comm 1]
    have h3i := h3 ⟨i, by omega⟩
    rw [dif_pos (show i + 1 < S by omega)] at h3i
    have h3i := of_decide_eq_true h3i
    simp only [SelectShape.route] at h3i
    rw [h3i]
    unfold SelectScan.mux at *
    rw [mul_one]
    exact CharTwo.add_self_eq_zero _
  · obtain ⟨t, hbody⟩ := hm.done
    rw [HoldsAt, hbody]
    intro i hi
    have hf := hm.full
    simp only [isNodeBit, Bool.and_eq_true, beq_iff_eq] at hf
    rw [exprLen_mul, exprLen_leaf, hf.2] at hi
    change ir.evalE _ _ _ _ * (ir.evalE _ _ _ _ + ir.evalE _ _ _ _) = ir.evalE _ _ _ _
    simp only [evalE_reindex, IndexMap.entry_step_one hi, IndexMap.entry_step_zero hi]
    rw [hm.evalE_const e (v := s.gN) (by simp), hm.evalE_const e (v := s.zerosDone) (by simp),
      hc.gN, hc.zerosDone _ hi]
    rcases h2 ⟨n + i, by omega⟩ with h0 | ⟨-, h0⟩
    · exact absurd h0 (by simp)
    · simp only [SelectShape.route, show n ≤ n + i by omega, if_true,
        show n + i - n = i by omega] at h0
      rw [← CharTwo.sub_eq_add]
      exact h0
  · obtain ⟨t, hbody⟩ := hm.route
    rw [HoldsAt, hbody]
    intro i hi
    rw [exprLen_add, exprLen_prod, exprLen_mux, exprLen_add, exprLen_reindex,
      IndexMap.size_single, Nat.div_self hS] at hi
    obtain rfl : i = 0 := by omega
    change ir.evalE _ _ (.prod S _) 0 + ir.evalE _ _ (.prod n _) 0 = ir.evalE _ _ _ 0
    rw [evalE_prod, evalE_prod, List.prod_map_range, List.prod_map_range,
      hm.evalE_const e (v := s.zero) (by simp), hc.zero]
    rw [List.finRange_foldl_mul_eq_prod, List.finRange_foldl_mul_eq_prod] at h4
    have hl : ∏ i : Fin S, ir.evalE (ir.reader e) (s.field ir) (.mux (.ref s.acc)
        (.add (.reindex [(0, 0, S)] (.leaf s.delta)) (.add (.leaf s.count)
          (.scale (.const 2) (.apply (.sum w) (.mul (.reindex [(0, 1, w * S)] (.ref s.stream))
            (.reindex (List.replicate S (0, 1, w)) (.leaf s.basis)))))))
        (.reindex [(0, 0, S)] (.leaf s.one))) (0 * S + i) =
        ∏ i : Fin S, SelectScan.mux (Falcon512.SelectFirstN.selected n bound
          (s.sample ir (w := w) (ir.reader e)) (s.route ir (ir.reader e) n) i)
          (s.deltaAt ir (ir.reader e) - Falcon512.SelectFirstN.enc F (s.route ir (ir.reader e) n i).count_enc
            (s.sample ir (ir.reader e) i)) 1 := by
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [Nat.zero_mul, Nat.zero_add, evalE_mux, hm.acc_eq ho hc hb e i, evalE_add, evalE_reindex,
        IndexMap.entry_step_zero i.isLt, evalE_add, evalE_scale_const, evalE_apply_sum,
        hm.sum_sample hc e i, evalE_reindex, IndexMap.entry_step_zero i.isLt,
        hm.evalE_const e (v := s.one) (by simp), hc.one, hc.two, SelectScan.mux, Falcon512.SelectFirstN.enc]
      simp only [CharTwo.sub_eq_add]
      rfl
    have hr : ∏ j : Fin n, ir.evalE (ir.reader e) (s.field ir)
        (.add (.reindex [(0, 0, n)] (.leaf s.delta)) (.add (.leaf s.gpow)
          (.scale (.const 2) (.apply (.sum w) (.mul (.reindex [(0, 1, w * n)] (.leaf s.raw))
            (.reindex (List.replicate n (0, 1, w)) (.leaf s.basis))))))) (0 * n + j) =
        ∏ j : Fin n, (s.deltaAt ir (ir.reader e) - Falcon512.SelectFirstN.enc F (F.g ^ (j : ℕ))
          (s.word ir (w := w) (ir.reader e) j)) := by
      refine Finset.prod_congr rfl fun j _ => ?_
      rw [Nat.zero_mul, Nat.zero_add, evalE_add, evalE_reindex, IndexMap.entry_step_zero j.isLt,
        evalE_add, hm.evalE_const e (v := s.gpow) (by simp), hc.gpow _ j.isLt, evalE_scale_const,
        evalE_apply_sum, hm.sum_word hc e j, hc.two, Falcon512.SelectFirstN.enc]
      simp only [CharTwo.sub_eq_add]
      rfl
    rw [hl, hr]
    unfold SelectScan.mux at *
    rw [h4]
    exact CharTwo.add_self_eq_zero _

/-- **The selection's soundness**: where its predicates and the source program hold, the selected
words are the first `n` samples below `bound` (`firstAccepted`), or `δ` is a root of the gadget's
event (`SelectFirstN.badEvent`, fixed by the committed values). -/
theorem SelectMatches.firstAccepted_or_badAt
    (hm : ir.SelectMatches S n w pStart pStep pDone pRoute s)
    (ho : ir.RefsOrdered) {F : SelectionField (I (s.field ir)).K S w} {bound : ℕ}
    (hc : s.Consts ir I F n bound) (hb : bound < 2 ^ w) [CharP (I (s.field ir)).K 2]
    (hnS : n ≤ S) (hS : 0 < S) {e : ir.Env I} (hs : ir.SourceSatAt e)
    (hstart : ir.HoldsAt e (ir.predicate pStart).body)
    (hstep : ir.HoldsAt e (ir.predicate pStep).body)
    (hdone : ir.HoldsAt e (ir.predicate pDone).body)
    (hroute : ir.HoldsAt e (ir.predicate pRoute).body) :
    firstAccepted (fun v => decide (v < bound))
        (fun i : Fin S => Bits.natOfBits (s.sample ir (w := w) (ir.reader e) i)) n =
        some (fun j => Bits.natOfBits (s.word ir (w := w) (ir.reader e) j)) ∨
      (Falcon512.SelectFirstN.badEvent F bound (s.sample ir (ir.reader e)) (s.word ir (ir.reader e))
        (s.route ir (ir.reader e) n) hnS).BadAt (s.deltaAt ir (ir.reader e)) :=
  Falcon512.SelectFirstN.sound hnS hb (hm.stream_allBool ho hc e) (hm.out_allBool e)
    (hm.run ho hc hb hS hs hstart hstep hdone hroute)

/-- **The selection's readings depend only on the counter, the completion flags, the selected
words and the values the stream reads.** -/
theorem selectReadings_congr {rd rd' : ir.Valuation I}
    (h : ∀ v ∈ s.count :: s.full :: s.raw :: ir.exprNodes (.ref s.stream), rd v = rd' v) :
    s.sample ir (S := S) (w := w) rd = s.sample ir rd' ∧
      s.word ir (n := n) (w := w) rd = s.word ir rd' ∧
      s.route ir (S := S) rd n = s.route ir rd' n := by
  have hleaf : ∀ v ∈ [s.count, s.full, s.raw], ∀ f,
      ir.evalE rd f (.leaf v) = ir.evalE rd' f (.leaf v) :=
    fun v hv f => evalE_congr fun u hu => by
      simp only [exprNodes, closure, Expr.directNodes, Expr.refs, List.flatMap_nil,
        List.append_nil, List.mem_singleton] at hu
      subst hu
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl <;> simp [h]
  refine ⟨?_, ?_, ?_⟩
  · funext i b
    unfold SelectShape.sample
    rw [evalE_congr (e := .ref s.stream) fun v hv => h v (by simp [hv])]
  · funext j b
    unfold SelectShape.word wordAt
    rw [hleaf s.raw (by simp)]
  · funext i
    unfold SelectShape.route
    rw [hleaf s.count (by simp), hleaf s.full (by simp)]

end

end GordieHowe.RealizedProgram
