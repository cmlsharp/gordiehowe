-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.Realizations.Realize

@[expose] public section

/-!
# GordieHowe: derivations, the facts and the steps

The facts a derivation establishes (`GordieHowe.RealizedProgram.Fact`, `GordieHowe.RealizedProgram.Fact.HoldsWith`), the rule set
(`GordieHowe.RealizedProgram.Step`, every constructor), and the model facts the rules read
(`GordieHowe.RealizedProgram.DerivModel`). The rules' checkers and soundness lemmas are in
`GordieHowe/Language/Realizations/Derivation/*.lean`; the dispatcher and the theorems in
`GordieHowe/Language/Realizations/Derivation.lean`. A new rule adds a constructor here, a file of
its own with `<rule>Fact` and `<rule>Fact_sound`, and one line each in `stepFact` and
`stepFact_sound`.
-/

namespace GordieHowe.RealizedProgram

open Export Range IOP


/-! ## Facts and steps -/

/-- **A fact of a derivation** about the environment, over program items named by id. -/
inductive Fact where
  /-- `e₁ = e₂` in domain `d`'s field, at every coordinate below `e₁`'s length. -/
  | eq (d : ℕ) (e₁ e₂ : Expr)
  /-- Every coordinate of `e` is the cast of a natural below `N`. -/
  | nat (d : ℕ) (e : Expr) (N : ℕ)
  /-- Every coordinate's integer reading of `e` lies in `[lo, hi]` and casts to its value. -/
  | ivl (d : ℕ) (e : Expr) (lo hi : ℤ)
  /-- The integer readings of `e₁` and `e₂` are equal below `e₁`'s length. -/
  | intEq (d : ℕ) (e₁ e₂ : Expr)
  /-- Every coordinate's integer reading of `e` is a multiple of `q`. -/
  | dvd (d : ℕ) (e : Expr) (q : ℕ)
  /-- Every coordinate of `e` is a row of table `t`, read in its challenge's field. -/
  | inRows (t : ℕ) (e : Expr)
  /-- The body of predicate `p` holds. -/
  | holds (p : ℕ)
  deriving Repr, Inhabited

/-- **The source of a leaf's interval** in a `src` step. -/
inductive IvlSrc where
  /-- A constant: the hull of its centred entries. -/
  | const
  /-- The declared bound `sr[k]`. -/
  | declared (k : ℕ)
  /-- The `nat` fact of premise `k`. -/
  | nat (k : ℕ)
  /-- A value stored at a prime-subfield node: `[0, p − 1]`. -/
  | prime
  /-- An opaque `Bit` value computed from arguments: `[0, 1]`. -/
  | opaqueBit
  /-- A shifted range (not implemented: concludes nothing). -/
  | shift (k : ℕ)
  /-- The quadratic root equation of predicate `q`, its `m` with the interval of premise `r`
  (`quadSrcN`): `[0, c]`. -/
  | quadRoot (q r : ℕ)
  /-- The root-set equations of the predicates `qs`, covering every coordinate: the hull of their
  roots (`rootSetSrc`). -/
  | rootSet (qs : List ℕ)
  deriving Repr, Inhabited

/-- **An instance of the linear-operator rule** (`linopFact`). -/
inductive LinOpStep where
  /-- From `eq d a b` (premise `k`), `e` an operator applied to `a` (`.apply op a`, or `.linear rows
  a` reading `a` below its length): `e` equals the operator applied to `b`. -/
  | congr (k : ℕ) (e : Expr)
  /-- `.apply op x` equals `.linear R x`, or `.linear R x − .linear N x` for `N` nonempty, `R` and
  `N` the core-language operator's added and subtracted sparse rows (`opRows`). -/
  | rows (op : NamedOp) (x : Expr) (R N : List (List (ℕ × Coef)))
  /-- From the body of the products predicate of the spectrally realized convolution `c` (premise
  `k`): its source equals its reading through the transform. -/
  | spectral (c k : ℕ)
  /-- `INTT(NTT x) = x` at the root `ψ` of size `n` (`nttFact`). -/
  | nttInv (n psi : ℕ) (x : Expr)
  /-- `NTT(INTT y) = y` at the root `ψ` of size `n` (`nttFact`). -/
  | inttInv (n psi : ℕ) (y : Expr)
  /-- `negacyclicConv h (ntt ψ) x = INTT(h · NTT x)`, `x` one block (`nttFact`). -/
  | convNtt (h psi : ℕ) (x : Expr)
  /-- `NTT(negacyclicConv h x) = NTT h · NTT x`, `x` one block (`nttFact`). -/
  | convCoef (h psi : ℕ) (x : Expr)
  /-- `nttTranspose ψ' (ntt_natural ψ x) = n · x`, `ψ ψ' ≡ 1` (`nttFact`). -/
  | transposeInv (n psi psi' : ℕ) (x : Expr)
  /-- `polyBroadcast t K (ntt ψ) x = INTT(t · NTT x)` per output block, `x` one block
  (`nttFact`). -/
  | convBcastNtt (t K psi : ℕ) (x : Expr)
  /-- `polyMatVec a K L (ntt ψ) x = INTT(Σ_l a_{il} · NTT x_l)` per output block `i`, `x` one
  operand (`nttFact`). -/
  | convMatNtt (a K L psi : ℕ) (x : Expr)
  /-- The adjoint pairing `Σ (nttTranspose ψ y) ⊙ x = Σ y ⊙ ntt_natural ψ x`, `x` and `y` of
  length `n` (`nttFact`). -/
  | adjoint (n psi : ℕ) (y x : Expr)
  deriving Repr, Inhabited

/-- **A step of a derivation**: premises are indices into the facts of the earlier steps; program
items are ids in named fields. -/
inductive Step where
  /-- `p` is a field `equal` or a `mod_0`: its field equation (`RealizedAt`). -/
  | realized (p : ℕ)
  /-- `e₁ = e₂` after one unfolding of a shared expression or a bound value. -/
  | subst (e₁ e₂ : Expr)
  /-- `Σ c_k (lhs_k − rhs_k) − (e₁ − e₂)` vanishes modulo `p` as a linear form, the `eq` premises
  `k` with coefficients `c_k`. -/
  | linear (cs : List (ℕ × ℤ)) (e₁ e₂ : Expr)
  /-- The members `(t, g, m)` (member `m` of group `g` of table `t`), slices in order covering one
  needle: its coordinates are rows of `t`, or one of the groups' challenge is bad. -/
  | lookup (ms : List (ℕ × ℕ × ℕ))
  /-- From `inRows t e` with `t` the range `[0, T)`: `nat d e T`. -/
  | rangeNat (k : ℕ)
  /-- From `holds q` with `q` the `in` `e ∈ [0, N)`: `nat d e N`. -/
  | holdsIn (k : ℕ)
  /-- The interval of the leaf `v` from the source `s`. -/
  | src (v : ℕ) (s : IvlSrc)
  /-- From `nat d (leaf v) N`, `v` neither a constant nor bound: `ivl d (leaf v) 0 (N − 1)`. -/
  | ivlNat (k : ℕ)
  /-- Interval propagation (`ivlOf`) through `e`, its leaves' intervals the `ivl` premises `ks`. -/
  | ivlExpr (ks : List ℕ) (e : Expr) (lo hi : ℤ)
  /-- From `intEq d e₁ e₂` (`k`), the `ivl` facts `ks` of the other atoms of `e₁ − e₂` in its
  linear form's order, and an `ivl` fact of `a` (`j`, its cast): `a`'s solved interval within
  `[lo, hi]` (`ivlSolveFact`). -/
  | ivlSolve (k : ℕ) (ks : List ℕ) (a : Expr) (j : ℕ) (lo hi : ℤ)
  /-- `e = .apply op x`: from the interval of `x` (`k`) and of the public operand (`a`), the
  operator's interval within `[lo, hi]` (`ivlApplyFact`). -/
  | ivlApply (k : ℕ) (a : Option ℕ) (e : Expr) (lo hi : ℤ)
  /-- `e = .logic op w args`: from intervals within `[0, 1]` of the arguments (`ks`), `[0, 1]`
  (`ivlLogicFact`). -/
  | ivlLogic (ks : List ℕ) (e : Expr)
  /-- From two intervals of one expression: their intersection. -/
  | ivlMeet (a b : ℕ)
  /-- From the intervals of `x` (`a`) and `y` (`b`), masked views of disjoint supports: the hull of
  the two for `x + y` (`ivlDisjointFact`). -/
  | ivlDisjoint (a b : ℕ)
  /-- From the field equation `x = y` (`k`) and the intervals of `x` (`a`) and `y` (`b`): their
  integer readings agree modulo the characteristic, `dvd d (x − y) p` (`fieldDvdFact`). -/
  | fieldDvd (k a b : ℕ)
  /-- From `ivl d e lo hi` with `0 ≤ lo`: `nat d e (hi + 1)`. -/
  | natIvl (k : ℕ)
  /-- From `nat d e A` (`k`) and `nat d X B` (`j`) with `X + e` the constant `c` as a linear form
  and `A + B − 1 ≤ p`: `nat d e (c + 1)`. -/
  | natComp (k j : ℕ)
  /-- From `eq d e s` (`k`) with `s = Σ_j c_j x_j` as linear forms, `nat d x_j N_j` (`ks`),
  `0 < c_j < p` and `Σ_j c_j (N_j − 1) < p`: `nat d e (Σ_j c_j (N_j − 1) + 1)`. -/
  | natLin (k : ℕ) (ks : List ℕ)
  /-- A field `equal` `v · v = v` (predicate `p`): `nat d (leaf v) 2`. -/
  | natBool (p : ℕ)
  /-- From `eq d x C` (`k`), `C` a constant `c` (centred `c'`), and `x`'s interval (`a`): `dvd d x q`
  for the derivation's `mod_q`, `q` dividing `c'`. -/
  | liftConst (k a : ℕ)
  /-- From `eq d e₁ e₂` (`k`) and `nat d e₁ N` or `inRows t e₁` (`j`): the same of `e₂`. -/
  | transport (k j : ℕ)
  /-- From `eq d e₁ e₂` (`k`) and `e₁`'s interval (`a`): `intEq d e₁ e₂` with `e₂`'s interval
  (`b`), or `dvd d e₁ q` with `e₂ = q · Q + C` and `Q`'s range (`b`). -/
  | lift (k a b : ℕ)
  /-- From `eq d e (Σ_j T^j D_j)` (`k`) and `nat d D_j T` (`ds`): `nat d e (T^n)`. -/
  | digits (k : ℕ) (ds : List ℕ) (T : ℕ)
  /-- From `dvd d (e − e') q` (`k`): the `mod_q` `e ≡ e'`. -/
  | congr (k : ℕ)
  /-- A cross-field `equal` by its MAC (`macFact`): its tails `ts` and H predicate `h` cited by rank, its operands' and blinds' `[0, 1]` intervals `ivs` by index. -/
  | mac (ts : List ℕ) (h : Option ℕ) (ivs : List ℕ)
  /-- A linear operator: congruence, its sparse rows, or the spectral convolution (`linopFact`). -/
  | linop (s : LinOpStep)
  /-- The fact `k` is the body of the derivation's predicate. -/
  | conclude (k : ℕ)
  /-- The body of predicate `q` holds: `q`'s derivation has a smaller rank. -/
  | hyp (q : ℕ)
  /-- The fact of shared entry `k`: the entry has a smaller rank. -/
  | fact (k : ℕ)
  /-- Step `s` read in domain `d`, as in a shared entry of domain `d` (no `conclude`, `congr`
  or own `realized`): the facts of a cross-field `equal`'s other domain. -/
  | inDom (d : ℕ) (s : Step)
  /-- A `mod_q` in the grouped form (`groupedFact`): its rows cited by rank, its facts by index. -/
  | groupedMod (rows ivs : List ℕ)
  deriving Repr, Inhabited

/-- **A derivation**: its steps in order. -/
abbrev Derivation : Type := List Step

/-- **A shared fact**: a fact derived once, with its rank and its derivation; derivations cite it
by `fact k`. -/
structure SharedEntry where
  /-- The fact. -/
  fact : Fact
  /-- Its rank: it cites only predicates and entries of smaller rank. -/
  rank : ℕ
  /-- Its derivation. -/
  steps : List Step
  deriving Repr, Inhabited

/-- **The derivations of a program**: the derivations of the listed predicates, as `(pid, steps)`
sorted by strictly increasing `pid` (every unlisted predicate takes `defaultSteps`), the
predicates' ranks (a derivation cites only predicates and shared entries of smaller rank; an
unlisted predicate cites nothing, so rank `0`, the value past the end of `ranks`, serves it), and
the shared fact table. -/
structure Derivations where
  /-- The derivations of the listed predicates, sorted by predicate. -/
  derivs : List (ℕ × List Step)
  /-- The predicates' ranks. -/
  ranks : List ℕ
  /-- The shared facts. -/
  shared : List SharedEntry := []
  deriving Repr, Inhabited

/-- **The derivation of an unlisted predicate**: a field `equal` realized as written. -/
def defaultSteps (pid : ℕ) : List Step := [.realized pid, .conclude 0]

/-- **The steps of predicate `pid` in a sparse derivation list**: its listed steps, else
`defaultSteps`. -/
def sparseSteps : List (ℕ × List Step) → ℕ → List Step
  | [], pid => defaultSteps pid
  | d :: ds, pid => if d.1 = pid then d.2 else sparseSteps ds pid

/-- **The steps of predicate `pid`** (`sparseSteps`). -/
def Derivations.stepsOf (D : Derivations) (pid : ℕ) : List Step := sparseSteps D.derivs pid

theorem sparseSteps_of_lt : ∀ {ds : List (ℕ × List Step)} {pid : ℕ}, (∀ d ∈ ds, pid < d.1) →
    sparseSteps ds pid = defaultSteps pid
  | [], _, _ => rfl
  | d :: ds, pid, h => by
    have h1 := h d (by simp)
    simp only [sparseSteps, if_neg (Nat.ne_of_gt h1)]
    exact sparseSteps_of_lt fun d' hd' => h d' (by simp [hd'])

/-- **The width of a packed rank**, in bits. -/
def rankWidth : ℕ := 32

/-- **Ranks packed into one natural**, `rankWidth` bits each, read in constant kernel time by
`rankOf`. -/
def packRanks (rs : List ℕ) : ℕ := rs.foldr (fun r acc => r + acc * 2 ^ rankWidth) 0

/-- **Rank `q` of a packed rank list.** -/
def rankOf (P q : ℕ) : ℕ := (P / 2 ^ (rankWidth * q)) % 2 ^ rankWidth

/-- **What a derivation may cite**: the predicates' ranks, the shared entries' ranks, and the
shared entries' facts. -/
structure DerivCtx where
  /-- The predicates' ranks. -/
  rank : ℕ → ℕ
  /-- The shared entries' ranks. -/
  srank : ℕ → ℕ
  /-- The shared entries' facts. -/
  sfact : ℕ → Option Fact

/-- **The context of a program's derivations**: the packed ranks and the shared table. -/
def Derivations.ctx (D : Derivations) : DerivCtx :=
  let P := packRanks D.ranks
  let SP := packRanks (D.shared.map (·.rank))
  ⟨rankOf P, rankOf SP, fun k => D.shared[k]?.map (·.fact)⟩

/-- **The structural equality of facts.** -/
def Fact.beq : Fact → Fact → Bool
  | .eq d a b, .eq d' a' b' => d == d' && a.beq a' && b.beq b'
  | .nat d e N, .nat d' e' N' => d == d' && e.beq e' && N == N'
  | .ivl d e lo hi, .ivl d' e' lo' hi' => d == d' && e.beq e' && lo == lo' && hi == hi'
  | .intEq d a b, .intEq d' a' b' => d == d' && a.beq a' && b.beq b'
  | .dvd d e q, .dvd d' e' q' => d == d' && e.beq e' && q == q'
  | .inRows t e, .inRows t' e' => t == t' && e.beq e'
  | .holds p, .holds p' => p == p'
  | _, _ => false

theorem Expr.beq_iff {e e' : Expr} : e.beq e' = true ↔ e = e' :=
  ⟨Expr.eq_of_beq, fun h => h ▸ Expr.beq_self e⟩

/-- **Structurally equal facts are equal.** -/
theorem Fact.eq_of_beq {f g : Fact} (h : f.beq g = true) : f = g := by
  cases f <;> cases g <;> simp_all [Fact.beq, Expr.beq_iff]

/-- **The domain of a fact** (`0` for the rows of a table and a predicate's body). -/
def Fact.dom : Fact → ℕ
  | .eq d _ _ => d
  | .nat d _ _ => d
  | .ivl d _ _ _ => d
  | .intEq d _ _ => d
  | .dvd d _ _ => d
  | .inRows _ _ => 0
  | .holds _ => 0

/-- **The body a shared entry is checked against** in domain `d`: an `in` with no records, which
no rule concludes. -/
def entryBody (d : ℕ) : PredBody := .mem d [] (.range 0) default

/-- **The domain of a predicate body** (the `x` domain of a cross-field `equal`). -/
def PredBody.dom : PredBody → ℕ
  | .equal d _ _ _ => d
  | .mem d _ _ _ => d
  | .mod d _ _ _ _ => d
  | .cross dx _ _ _ _ _ => dx

/-- Whether a value's integer reading is its natural (`intOf`): neither a constant nor bound. -/
def isPlainKind : Kind → Bool
  | .constant _ => false
  | .bound _ => false
  | _ => true

/-- **A value of kind `k` reads a natural below `N` as itself** at the characteristic `p`: a plain
value (its integer reading is its natural), or a bound value with `2 N ≤ p` (its integer reading
is its natural read centred, which is the natural below `p / 2`). -/
def natReadB (k : Kind) (N p : ℕ) : Bool := isPlainKind k || (k.isBound && decide (2 * N ≤ p))

section

variable (ir : RealizedProgram) {I : Interp}

/-- **A fact holds** at the reader `rd`. -/
def Fact.HoldsWith (rd : ir.Valuation I) : Fact → Prop
  | .eq d e₁ e₂ => ∀ i < ir.exprLen e₁, ir.evalWith rd d e₁ i = ir.evalWith rd d e₂ i
  | .nat d e N => ∀ i < ir.exprLen e, IsNatBelow N (ir.evalWith rd d e i)
  | .ivl d e lo hi => ∀ i < ir.exprLen e, lo ≤ ir.evalIntWith rd d e i ∧
      ir.evalIntWith rd d e i ≤ hi ∧
      ((ir.evalIntWith rd d e i : ℤ) : (I (ir.domainField d)).K) = ir.evalWith rd d e i
  | .intEq d e₁ e₂ => ∀ i < ir.exprLen e₁, ir.evalIntWith rd d e₁ i = ir.evalIntWith rd d e₂ i
  | .dvd d e q => ∀ i < ir.exprLen e, (q : ℤ) ∣ ir.evalIntWith rd d e i
  | .inRows t e => ∀ i < ir.exprLen e, ∃ j, ir.tableRow rd (ir.chalField (ir.alphaOf t)) t j =
      ir.evalE rd (ir.chalField (ir.alphaOf t)) e i
  | .holds p => ir.HoldsWith rd (ir.predicate p).body

variable {ir} in
/-- **A fact holds in the environment `e`**: at its reader. -/
def Fact.Holds (e : ir.Env I) (f : Fact) : Prop := f.HoldsWith ir (ir.reader e)


variable {ir} in
/-- **What a derivation of rank `self` may cite holds**: every predicate and every shared entry of
smaller rank. -/
def CitesHold (e : ir.Env I) (ctx : DerivCtx) (self : ℕ) : Prop :=
  (∀ q < ir.predicates.length, ctx.rank q < self → ir.HoldsAt e (ir.predicate q).body) ∧
    ∀ k f, ctx.srank k < self → ctx.sfact k = some f → f.Holds e

/-- **The body a derivation is checked against** is its predicate's or a shared entry's. -/
def OwnBody (pid : ℕ) (body : PredBody) : Prop :=
  (pid < ir.predicates.length ∧ (ir.predicate pid).body = body) ∨ ∃ d, body = entryBody d

variable (I) in
/-- **The model facts the rules read**: the program is well formed, the interpretation registered
and lawful, and every table valid (`TableOk`). -/
structure DerivModel (primeNodes : ℕ → List String) : Prop where
  /-- The program is well formed. -/
  wf : ir.WellFormed
  /-- The interpretation is registered. -/
  registered : I.Registered ir
  /-- The integer readings are lawful. -/
  lawful : I.Lawful ir primeNodes
  /-- Every table is valid. -/
  tables : ∀ t < ir.tables.length, ir.TableOk t
  /-- The MAC fields are modelled (`Interp.MacModel`). -/
  mac : I.MacModel ir


end

end GordieHowe.RealizedProgram
