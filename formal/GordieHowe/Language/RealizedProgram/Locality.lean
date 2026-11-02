-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.Program.Domain
public import GordieHowe.Language.Realizations.RealizeHonest
public import GordieHoweNative.Language.RealizedProgram.Locality

@[expose] public section

/-!
# GordieHowe: the locality of a program's domains

A program with several committing domains commits each value in the cells of its own domain
(`RealizedProgram.Cell d`), and each domain's predicate (`RealizedProgram.domainOf d`) reads the values through
its own cells only (`RealizedProgram.cellValuation d`: the committed assignment read from `d`'s cells, `0`
at every other domain's coordinates). The realized program reads the committed assignment of all
domains (`GordieHowe.RealizedProgram.ofAllCells`). The two readings agree at a value that reads only domain `d`'s part
of the committed assignment, which the decided check `GordieHowe.RealizedProgram.Local` establishes for everything a
domain's constraints read.

* **What a value reads of the committed assignment** (`GordieHowe.RealizedProgram.asgReads`, as `GordieHowe.RealizedProgram.read`): a
  committed value, a pad copy or a late value itself (a late value is its message minus its pad), a
  value bound to its digits the values of its expression (`GordieHowe.RealizedProgram.bindAsg`), a public expression,
  an opaque value or a bit view what the values it reads read; a message reads nothing (its pad
  cancels), nor do a statement value, a constant or a challenge.
* **Readings agree where the assignments agree** (`GordieHowe.RealizedProgram.read_bindAsg_congr`): at two committed
  assignments agreeing on the values a value reads (`GordieHowe.RealizedProgram.AsgAgree`: committed values and pads,
  and pads off the late values' coordinates), the value reads the same at their realized
  assignments.
* **The assignment of all domains** (`GordieHowe.RealizedProgram.ofAllCells`): each value's coordinates from its
  domain's cells. It agrees with domain `d`'s cells at the values of `d` (`asgAgree_ofAllCells`), so
  at a value reading only `d` the cells' valuation of `d` is the reader of all domains
  (`cellValuation_eq_reader`).
* **The check** (`GordieHowe.RealizedProgram.Local`, decided by `GordieHowe.RealizedProgram.localB` for a well-formed program,
  `Local.of_localB`): every predicate of a domain reads only its domain (a cross-field `equal`, of two
  domains, has no domain and is not checked; its H half `RealCircuit.macH` reads only its circuit's
  domain, `GordieHowe.RealizedProgram.macHNodes`); every predicate placed in a GKR circuit and every part of a batch is of the
  circuit's or the batch's domain; every LogUp identity reads only its circuit's domain; every
  input block of a circuit holds a value of its domain; every late value's pad space is the whole
  field or a node of its domain's packing tree.
* **The congruences** used by the cells lowering: a placed predicate's truth (`placedHolds_congr`)
  and a LogUp identity's (`logupHoldsAt_congr`) depend only on the values they read
  (`GordieHowe.RealizedProgram.predNodes`, `GordieHowe.RealizedProgram.logupNodes`).

The definitions are in `GordieHoweNative/Language/RealizedProgram/Locality.lean`
(the compiled library `GordieHoweNative`); this module has their lemmas.
-/

namespace GordieHowe.RealizedProgram

open Export

/-- **The domain of a predicate body**: a field `equal`'s, an `in`'s or a `mod_q`'s; none for a
cross-field `equal`, which relates two domains. -/
def PredBody.domain? : PredBody → Option ℕ
  | .equal d .. => some d
  | .mem d .. => some d
  | .mod d .. => some d
  | .cross .. => none

/-- **The value of an input block**: a public, committed, pad or view block's; none for a
realization input, filler or batch pads. -/
def InputBlock.value? : InputBlock → Option ℕ
  | .pub u _ _ => some u
  | .committed u _ _ => some u
  | .pad u _ _ => some u
  | .view u _ _ => some u
  | _ => none

section

variable (ir : RealizedProgram)

/-! ## What a value reads of the committed assignment -/

/-- **Value `v` reads only domain `d`'s part of the committed assignment**: everything it reads of
the committed assignment (`asgReads`) is a value of `d`. -/
def ReadsIn (d v : ℕ) : Prop := ∀ u ∈ ir.asgReads ir.fuel v, (ir.value u).domain = d

/-- **The values the rows of table `t` read** (`RealizedProgram.tableRow`): none for a range, the first
column for a committed table, the values the expression reads for a table of an expression's
coordinates. -/
def tableNodes (t : ℕ) : List ℕ :=
  match (ir.table t).rows with
  | .range _ => []
  | .columns cols => [cols.headD 0]
  | .expr e' => ir.exprNodes e'

/-- **The values the LogUp identity of group `g` of table `t` reads, the challenges' values
read through `ch`**: the value holding the table's challenge, the values of its members' needles,
its histograms, and the values its rows read (`tableNodes`). -/
def logupNodesWith (ch : ℕ → Option ℕ) (t g : ℕ) : List ℕ :=
  (ch (ir.alphaOf t)).toList ++
    (ir.members t g).flatMap (fun m => ir.exprNodes (ir.needleExpr m.pred m.needle)) ++
    (ir.groupOf t g).staticMult.toList ++ (ir.groupOf t g).lateMult.toList ++
    ir.tableNodes t

/-- **The values the LogUp identity of group `g` of table `t` reads** (`logupNodesWith` at the
value holding each challenge, `chalNode`). -/
def logupNodes (t g : ℕ) : List ℕ := ir.logupNodesWith ir.chalNode t g

/-- **The values the H half of cross-field `equal` `p` reads, the challenges' values read through
`ch`** (`MacHHolds`): the value holding the key, the tag, the values of the H operand. -/
def macHNodesWith (ch : ℕ → Option ℕ) (p : ℕ) : List ℕ :=
  match (ir.predicate p).body with
  | .cross _ x _ _ _ real => (ch real.key).toList ++ real.tag :: ir.exprNodes x
  | _ => []

/-- **The values the H half of cross-field `equal` `p` reads** (`macHNodesWith` at `chalNode`). -/
def macHNodes (p : ℕ) : List ℕ := ir.macHNodesWith ir.chalNode p

variable (I : Interp)

/-- **Two committed assignments agree on the values `S`**: their committed values and their pads
agree at every value of `S`, and their pads agree off the late values' coordinates. -/
structure AsgAgree (S : ℕ → Prop) (A A' : ir.Assignment I) : Prop where
  /-- The committed values agree on `S`. -/
  val : ∀ u, S u → A.val u = A'.val u
  /-- The pads agree on `S`. -/
  pad : ∀ u, S u → A.pad u = A'.pad u
  /-- The pads agree off the late values' coordinates. -/
  off : ir.PadsAgreeOff I A A'

variable {ir I}

/-- **Readings agree where the assignments agree**: a value reads the same at the realized
assignments of two committed assignments agreeing on everything it reads of the committed
assignment (`asgReads`). -/
theorem read_bindAsg_congr {x : ir.Valuation I} {r : (ir.layout I).Run} {S : ℕ → Prop}
    {A A' : ir.Assignment I} (h : ir.AsgAgree I S A A') :
    ∀ n v, (∀ u ∈ ir.asgReads n v, S u) →
      ir.read (ir.layoutEnv I x (ir.bindAsg A) r) n v =
        ir.read (ir.layoutEnv I x (ir.bindAsg A') r) n v
  | 0, _, _ => rfl
  | n + 1, v, hS => by
    funext i
    rcases hk : (ir.value v).kind with
      _ | ⟨_ | ⟨name, args⟩ | e⟩ | es | c | _ | ⟨w, sel⟩ | ⟨u, m⟩ | u | xb <;>
      simp only [asgReads, hk] at hS
    case priv =>
      simp only [read, hk, layoutEnv, ir.bindAsg_val_of_isBound (v := v) _ (by rw [hk]; rfl),
        h.val v (hS v (List.mem_singleton_self _))]
    case padCopy =>
      simp only [read, hk, layoutEnv, ir.bindAsg_val_of_isBound (v := v) _ (by rw [hk]; rfl),
        h.val v (hS v (List.mem_singleton_self _))]
    case late =>
      simp only [read, hk, layoutEnv, bindAsg, h.pad v (hS v (List.mem_singleton_self _))]
    case bound =>
      simp only [read, hk, layoutEnv, bindAsg]
      refine congrFun (evalE_congr fun u hu => funext fun j => ?_) i
      simp only [committedRead]
      split
      · rfl
      · rw [h.val u (hS u hu)]
    case pub.opaque =>
      simp only [read, hk]
      split_ifs
      · rfl
      · have hargs : args.map (fun u j => (I (ir.valueField u)).toNat
              (ir.read (ir.layoutEnv I x (ir.bindAsg A) r) n u j)) =
            args.map (fun u j => (I (ir.valueField u)).toNat
              (ir.read (ir.layoutEnv I x (ir.bindAsg A') r) n u j)) :=
          List.map_congr_left fun u hu => by
            rw [read_bindAsg_congr h n u fun w hw => hS w (List.mem_flatMap.2 ⟨u, hu, hw⟩)]
        rw [hargs]
    case pub.expr =>
      simp only [read, hk]
      exact congrFun (evalE_congr fun u hu =>
        read_bindAsg_congr h n u fun w hw => hS w (List.mem_flatMap.2 ⟨u, hu, hw⟩)) i
    case bits =>
      simp only [read, hk, bitView, read_bindAsg_congr h n w hS]
    case message =>
      simp only [read, hk, layoutEnv, bindAsg]
      by_cases hi : u < ir.values.length ∧ ir.IsLate u ∧ i < (ir.value u).size
      · rw [if_pos hi, if_pos hi, sub_add_cancel, sub_add_cancel]
      · rw [if_neg hi, if_neg hi, h.off u i hi]
    all_goals simp only [read, hk, layoutEnv]

/-- **The reader agrees where the assignments agree** (`read_bindAsg_congr` at the program's
fuel). -/
theorem reader_bindAsg_congr {x : ir.Valuation I} {r : (ir.layout I).Run} {S : ℕ → Prop}
    {A A' : ir.Assignment I} (h : ir.AsgAgree I S A A') {v : ℕ}
    (hv : ∀ u ∈ ir.asgReads ir.fuel v, S u) :
    ir.reader (ir.layoutEnv I x (ir.bindAsg A) r) v =
      ir.reader (ir.layoutEnv I x (ir.bindAsg A') r) v :=
  read_bindAsg_congr h _ v hv

/-! ## The assignment of all domains -/

variable (I) in
/-- **The committed assignment read from every domain's cells** `a`: each value's coordinates from
the cells of its domain (`RealizedProgram.ofCells`), `0` for a value of no domain of the program. -/
def ofAllCells (a : ∀ d : Fin ir.domains.length, ir.Cell d → (I (ir.domainField d)).K) :
    ir.Assignment I where
  val u i := if h : (ir.value u).domain < ir.domains.length then
    (ir.ofCells I _ (a ⟨_, h⟩)).val u i else 0
  pad u i := if h : (ir.value u).domain < ir.domains.length then
    (ir.ofCells I _ (a ⟨_, h⟩)).pad u i else 0

/-- Reading a domain's cells at an index equal to the domain. -/
theorem ofCells_of_eq (a : ∀ d : Fin ir.domains.length, ir.Cell d → (I (ir.domainField d)).K)
    {n : ℕ} (h : n < ir.domains.length) {d : Fin ir.domains.length} (hn : n = d) :
    ir.ofCells I n (a ⟨n, h⟩) = ir.ofCells I d (a d) := by
  subst hn
  rfl

/-- **The assignment of all domains agrees with domain `d`'s cells at the values of `d`**, and both
are `0` off the late values' coordinates. -/
theorem asgAgree_ofAllCells (a : ∀ d : Fin ir.domains.length, ir.Cell d → (I (ir.domainField d)).K)
    (d : Fin ir.domains.length) :
    ir.AsgAgree I (fun u => (ir.value u).domain = d) (ir.ofAllCells I a)
      (ir.ofCells I d (a d)) where
  val u hu := by
    funext i
    simp only [ofAllCells, dif_pos (show (ir.value u).domain < ir.domains.length by omega),
      ofCells_of_eq a _ hu]
  pad u hu := by
    funext i
    simp only [ofAllCells, dif_pos (show (ir.value u).domain < ir.domains.length by omega),
      ofCells_of_eq a _ hu]
  off u i hu := by
    have h2 := padsAgreeOff_ofCells d (a d) u i hu
    simp only [Pi.zero_apply] at h2
    rw [h2]
    simp only [ofAllCells]
    split
    · exact padsAgreeOff_ofCells _ _ u i hu
    · rfl

/-- **At a value reading only domain `d`, the cells' valuation of `d` is the reader of all
domains.** -/
theorem cellValuation_eq_reader
    (a : ∀ d : Fin ir.domains.length, ir.Cell d → (I (ir.domainField d)).K)
    (d : Fin ir.domains.length) {x : ir.Valuation I} {r : (ir.layout I).Run} {v : ℕ}
    (hv : ir.ReadsIn d v) :
    ir.cellValuation I d x r (a d) v =
      ir.reader (ir.layoutEnv I x (ir.bindAsg (ir.ofAllCells I a)) r) v :=
  (reader_bindAsg_congr (asgAgree_ofAllCells a d) hv).symm

/-! ## Truth depends on the values read -/

/-- **`t` reads no value or shared expression `e` does not read directly**: the values `t` reads
directly are `e`'s, and its shared expressions are `e`'s. -/
def SubReads (t e : Expr) : Prop :=
  (∀ v ∈ t.directNodes, v ∈ e.directNodes) ∧ ∀ k ∈ t.refs, k ∈ e.refs

/-- An expression reads what it reads. -/
theorem SubReads.refl (e : Expr) : SubReads e e := ⟨fun _ h => h, fun _ h => h⟩

/-- Reading through reads is transitive. -/
theorem SubReads.trans {a b c : Expr} (h₁ : SubReads a b) (h₂ : SubReads b c) : SubReads a c :=
  ⟨fun v hv => h₂.1 v (h₁.1 v hv), fun k hk => h₂.2 k (h₁.2 k hk)⟩

/-- A sum reads its left summand's reads. -/
theorem SubReads.add_left (a b : Expr) : SubReads a (.add a b) :=
  ⟨fun _ h => List.mem_append_left _ h, fun _ h => List.mem_append_left _ h⟩

/-- A sum reads its right summand's reads. -/
theorem SubReads.add_right (a b : Expr) : SubReads b (.add a b) :=
  ⟨fun _ h => List.mem_append_right _ h, fun _ h => List.mem_append_right _ h⟩

/-- A concatenation reads its left part's reads. -/
theorem SubReads.concat_left (a b : Expr) : SubReads a (.concat a b) :=
  ⟨fun _ h => List.mem_append_left _ h, fun _ h => List.mem_append_left _ h⟩

/-- A concatenation reads its right part's reads. -/
theorem SubReads.concat_right (a b : Expr) : SubReads b (.concat a b) :=
  ⟨fun _ h => List.mem_append_right _ h, fun _ h => List.mem_append_right _ h⟩

/-- **A sub-reading expression reads only values its parent reads.** -/
theorem exprNodes_of_subReads {t e : Expr} (h : SubReads t e) {v : ℕ} (hv : v ∈ ir.exprNodes t) :
    v ∈ ir.exprNodes e := by
  unfold exprNodes closure at hv ⊢
  rcases List.mem_append.1 hv with hv | hv
  · exact List.mem_append_left _ (h.1 v hv)
  · obtain ⟨k, hk, hkv⟩ := List.mem_flatMap.1 hv
    exact List.mem_append_right _ (List.mem_flatMap.2 ⟨k, h.2 k hk, hkv⟩)

/-- **A summand of an add tree reads only what the tree reads.** -/
theorem subReads_of_mem_summands : ∀ {e t : Expr}, t ∈ e.summands → SubReads t e
  | .add a b, t, h => by
    simp only [Expr.summands, List.mem_append] at h
    rcases h with h | h
    · exact (subReads_of_mem_summands h).trans (SubReads.add_left a b)
    · exact (subReads_of_mem_summands h).trans (SubReads.add_right a b)
  | .leaf _, t, h | .sub _ _, t, h | .scale _ _, t, h | .mul _ _, t, h | .reindex _ _, t, h
  | .concat _ _, t, h | .linear _ _, t, h | .prod _ _, t, h | .mux _ _ _, t, h | .apply _ _, t, h
  | .ref _, t, h | .logic _ _ _, t, h => by
    simp only [Expr.summands, List.mem_singleton] at h
    subst h
    exact SubReads.refl _

/-- **A row of a side reads only what the side reads.** -/
theorem subReads_of_mem_rowsAt {n : ℕ} : ∀ {e t : Expr}, t ∈ ir.rowsAt n e → SubReads t e
  | .concat a b, t, h => by
    simp only [rowsAt] at h
    split_ifs at h
    · rcases List.mem_append.1 h with h | h
      · exact (subReads_of_mem_rowsAt h).trans (SubReads.concat_left a b)
      · exact (subReads_of_mem_rowsAt h).trans (SubReads.concat_right a b)
    · simp only [List.mem_singleton] at h
      subst h
      exact SubReads.refl _
  | .leaf _, t, h | .add _ _, t, h | .sub _ _, t, h | .scale _ _, t, h | .mul _ _, t, h
  | .reindex _ _, t, h | .linear _ _, t, h | .prod _ _, t, h | .mux _ _ _, t, h | .apply _ _, t, h
  | .ref _, t, h | .logic _ _ _, t, h => by
    simp only [rowsAt, List.mem_singleton] at h
    subst h
    exact SubReads.refl _

/-- **A kernel's core reads its operand and its spectra's value.** -/
theorem kernelCore?_reads {c : ℕ} {t : Expr} {κ : KernelPart} (h : ir.kernelCore? c t = some κ) :
    SubReads κ.operand t ∧ κ.value ∈ t.directNodes := by
  have hop : ∀ op : NamedOp, ∀ v K psi nat, op.kernel? = some (v, K, psi, nat) →
      v ∈ op.operands := by
    intro op v K psi nat hk
    unfold NamedOp.kernel? at hk
    split at hk <;> simp_all [NamedOp.operands]
  unfold kernelCore? at h
  split at h
  · rename_i op x
    split at h
    · rename_i v K psi nat hk
      split_ifs at h
      cases h
      refine ⟨⟨fun u hu => ?_, fun k hk' => hk'⟩, ?_⟩
      · exact List.mem_append_right _ hu
      · exact List.mem_append_left _ (List.mem_append_left _ (hop op v K psi nat hk))
    · cases h
  · rename_i idx op x
    split at h
    · rename_i v K psi nat hk
      split at h
      · rename_i b hb
        split_ifs at h
        cases h
        refine ⟨⟨fun u hu => ?_, fun k hk' => hk'⟩, ?_⟩
        · exact List.mem_append_right _ hu
        · exact List.mem_append_left _ (List.mem_append_left _ (hop op v K psi nat hk))
      · cases h
    · cases h
  · cases h

/-- **A kernel part reads its operand and its spectra's value.** -/
theorem kernelPart?_reads {t : Expr} {κ : KernelPart} (h : ir.kernelPart? t = some κ) :
    SubReads κ.operand t ∧ κ.value ∈ t.directNodes := by
  unfold kernelPart? at h
  split at h
  · rename_i c e
    obtain ⟨h1, h2⟩ := kernelCore?_reads h
    exact ⟨⟨fun u hu => List.mem_append_right _ (h1.1 u hu), h1.2⟩, List.mem_append_right _ h2⟩
  · exact kernelCore?_reads h

/-- **A product form's placed equation depends only on the values its sides and its quotient
read.** -/
theorem productPlaced_congr {rd rd' : ir.Valuation I} {d m : ℕ} {P N : Expr}
    {real : ModRealization}
    (hP : ∀ v ∈ ir.exprNodes P, rd v = rd' v) (hN : ∀ v ∈ ir.exprNodes N, rd v = rd' v)
    (hQ : ∀ Q, real.quotient = some Q → ∀ v ∈ ir.exprNodes Q, rd v = rd' v) :
    ir.ProductPlaced rd d m P N real ↔ ir.ProductPlaced rd' d m P N real := by
  have hev : ∀ {e t : Expr}, SubReads t e → (∀ v ∈ ir.exprNodes e, rd v = rd' v) →
      ir.evalWith rd d t = ir.evalWith rd' d t := fun hs he =>
    evalE_congr fun v hv => he v (exprNodes_of_subReads hs hv)
  have hq : ∀ i, ir.quotTerm rd d m real i = ir.quotTerm rd' d m real i := by
    intro i
    unfold quotTerm
    cases hr : real.quotient with
    | none => rfl
    | some Q => simp only [hev (SubReads.refl Q) (hQ Q hr)]
  have hk : ∀ {e t : Expr}, (∀ v ∈ ir.exprNodes e, rd v = rd' v) → SubReads t e →
      ∀ κ, ir.kernelPart? t = some κ → ∀ nat n ψ k,
        ir.kernelTerm rd d nat n ψ κ k = ir.kernelTerm rd' d nat n ψ κ k := by
    intro e t he hs κ hκ nat n ψ k
    obtain ⟨h1, h2⟩ := kernelPart?_reads hκ
    unfold kernelTerm
    rw [hev (h1.trans hs) he, he κ.value (exprNodes_of_subReads hs (by
      unfold exprNodes closure; exact List.mem_append_left _ h2))]
  have hrowE : ∀ {e row : Expr}, (∀ v ∈ ir.exprNodes e, rd v = rd' v) → SubReads row e →
      ∀ i, ((ir.rowExprs row).map fun t => ir.evalWith rd d t i).sum =
        ((ir.rowExprs row).map fun t => ir.evalWith rd' d t i).sum := by
    intro e row he hs i
    refine congrArg List.sum (List.map_congr_left fun t ht => ?_)
    have ht' : t ∈ row.summands := (List.mem_filter.1 ht).1
    rw [hev ((subReads_of_mem_summands ht').trans hs) he]
  have hrowK : ∀ {e row : Expr}, (∀ v ∈ ir.exprNodes e, rd v = rd' v) → SubReads row e →
      ∀ nat n ψ k, ((ir.rowKernels row).map fun κ => ir.kernelTerm rd d nat n ψ κ k).sum =
        ((ir.rowKernels row).map fun κ => ir.kernelTerm rd' d nat n ψ κ k).sum := by
    intro e row he hs nat n ψ k
    refine congrArg List.sum (List.map_congr_left fun κ hκ => ?_)
    obtain ⟨t, ht, hκt⟩ := List.mem_filterMap.1 hκ
    exact hk he ((subReads_of_mem_summands ht).trans hs) κ hκt nat n ψ k
  unfold ProductPlaced
  split
  · refine forall₂_congr fun i _ => ?_
    rw [hev (SubReads.refl P) hP, hev (SubReads.refl N) hN, hq]
  · split
    · rename_i sh hsh
      refine and_congr_right fun hlen => forall₂_congr fun r hr => forall₂_congr fun k _ => ?_
      unfold productShape? at hsh
      obtain ⟨κ, -, rfl⟩ := Option.map_eq_some_iff.1 hsh
      dsimp only at hr hlen ⊢
      have hr' : r < (ir.rowsAt ((ir.value κ.value).size / κ.blocks) N).length := by
        rw [← hlen]
        exact hr
      have hsP := subReads_of_mem_rowsAt (List.getElem_mem hr)
      have hsN := subReads_of_mem_rowsAt (List.getElem_mem hr')
      unfold SpectralRowHolds
      simp only [List.getD_eq_getElem _ _ hr, List.getD_eq_getElem _ _ hr']
      simp only [hrowE hP hsP, hrowE hN hsN, hq, hrowK hP hsP, hrowK hN hsN]
    · exact Iff.rfl
  · exact Iff.rfl

/-- **A placed predicate's truth depends only on the values it reads** (`RealizedProgram.predNodes`). -/
theorem placedHolds_congr {rd rd' : ir.Valuation I} {b : PredBody}
    (h : ∀ v ∈ ir.predNodes b, rd v = rd' v) : ir.PlacedHolds rd b ↔ ir.PlacedHolds rd' b := by
  cases b with
  | mod d q e e' real =>
    have hx : ∀ e₀, (d, e₀) ∈ (PredBody.mod d q e e' real).exprs →
        ir.evalWith rd d e₀ = ir.evalWith rd' d e₀ := fun e₀ he₀ =>
      funext fun i => congrFun (evalE_congr (f := ir.domainField d) fun v hv =>
        h v (List.mem_append_left _ (List.mem_flatMap.2 ⟨(d, e₀), he₀, hv⟩))) i
    have hnodes : ∀ e₀, (d, e₀) ∈ (PredBody.mod d q e e' real).exprs →
        ∀ v ∈ ir.exprNodes e₀, rd v = rd' v := fun e₀ he₀ v hv =>
      h v (List.mem_append_left _ (List.mem_flatMap.2 ⟨(d, e₀), he₀, hv⟩))
    have hpp : ir.ProductPlaced rd d q e e' real ↔ ir.ProductPlaced rd' d q e e' real := by
      by_cases hf : real.form.isProduct = true
      · exact productPlaced_congr (hnodes e (by simp [PredBody.exprs]))
          (hnodes e' (by simp [PredBody.exprs]))
          fun Q hQ => hnodes Q (by simp [PredBody.exprs, hQ, hf])
      · unfold ProductPlaced
        cases hform : real.form <;> simp_all [ModForm.isProduct]
    simp only [PlacedHolds, hx e (by simp [PredBody.exprs]), hx e' (by simp [PredBody.exprs]), hpp]
  | equal => exact holdsWith_congr h
  | mem => exact holdsWith_congr h
  | cross => exact holdsWith_congr h

/-- **A LogUp identity's truth depends only on the values it reads** (`RealizedProgram.logupNodes`). -/
theorem logupHoldsAt_congr {rd rd' : ir.Valuation I} {t g : ℕ}
    (h : ∀ v ∈ ir.logupNodes t g, rd v = rd' v) :
    ir.LogupHoldsAt rd t g ↔ ir.LogupHoldsAt rd' t g := by
  unfold LogupHoldsAt
  split
  · rename_i v hv
    have hα : rd v = rd' v := h v (by simp [logupNodes, logupNodesWith, hv])
    have hn : ir.groupNeedles rd (ir.chalField (ir.alphaOf t)) t g =
        ir.groupNeedles rd' (ir.chalField (ir.alphaOf t)) t g := by
      unfold groupNeedles
      refine List.flatMap_congr fun m hm => ?_
      unfold memberVals
      refine List.map_congr_left fun c _ => congrFun (evalE_congr fun u hu => h u ?_) _
      simp only [logupNodes, logupNodesWith, List.mem_append, List.mem_flatMap]
      exact .inl (.inl (.inl (.inr ⟨m, hm, hu⟩)))
    have hhist : ∀ o : Option ℕ, (∀ u ∈ o.toList, rd u = rd' u) →
        ∀ T, ir.histRead rd (ir.chalField (ir.alphaOf t)) T o =
          ir.histRead rd' (ir.chalField (ir.alphaOf t)) T o := by
      intro o ho T
      funext j
      cases o with
      | none => rfl
      | some u => simp only [histRead, ho u (by simp)]
    have hs : ir.staticHist rd (ir.chalField (ir.alphaOf t)) t g =
        ir.staticHist rd' (ir.chalField (ir.alphaOf t)) t g :=
      hhist _ (fun u hu => h u (by
        simp only [logupNodes, logupNodesWith, List.mem_append]; exact .inl (.inl (.inr hu))))
        _
    have hl : ir.lateHist rd (ir.chalField (ir.alphaOf t)) t g =
        ir.lateHist rd' (ir.chalField (ir.alphaOf t)) t g :=
      hhist _ (fun u hu => h u
        (by simp only [logupNodes, logupNodesWith, List.mem_append]; exact .inl (.inr hu))) _
    have hrow : ir.tableRow rd (ir.chalField (ir.alphaOf t)) t =
        ir.tableRow rd' (ir.chalField (ir.alphaOf t)) t := by
      funext j
      unfold tableRow
      split
      · rfl
      · rename_i cols hc
        rw [h (cols.headD 0) (by simp [logupNodes, logupNodesWith, tableNodes, hc])]
      · rename_i e' hc
        exact congrFun (evalE_congr fun u hu => h u
          (by simp [logupNodes, logupNodesWith, tableNodes, hc, hu])) j
    unfold logupAt
    rw [hα, hn, hs, hl, hrow]
  · exact Iff.rfl

/-- **The H half of a cross-field `equal`'s truth depends only on the values it reads**
(`RealizedProgram.macHNodes`). -/
theorem macHHolds_congr {rd rd' : ir.Valuation I} {p : ℕ}
    (h : ∀ v ∈ ir.macHNodes p, rd v = rd' v) : ir.MacHHolds rd p ↔ ir.MacHHolds rd' p := by
  unfold MacHHolds
  unfold macHNodes macHNodesWith at h
  split
  · rename_i dx x dy y k real hb
    rw [hb] at h
    simp only at h
    split
    · rename_i v _ hv
      rw [hv] at h
      have hx : ∀ i, ir.evalWith rd dx x i = ir.evalWith rd' dx x i := fun i =>
        congrFun (evalE_congr (f := ir.domainField dx) fun u hu =>
          h u (by simp [hu])) i
      simp only [MacHHoldsAt, macChunkH, evalPad, hx, h v (by simp), h real.tag (by simp)]
    · exact Iff.rfl
    · exact Iff.rfl
  · exact Iff.rfl

/-! ## The check -/

variable (ir) in
/-- **The domains of a program are local** (see the module docstring), the nodes of each domain's
packing tree being `treeNodes`. -/
structure Local (treeNodes : ℕ → List String) : Prop where
  /-- Every predicate of a domain reads only its domain. -/
  preds : ∀ p ∈ ir.predicates, ∀ d, p.body.domain? = some d →
    ∀ v ∈ ir.predNodes p.body, ir.ReadsIn d v
  /-- Every predicate placed in a GKR circuit is of the circuit's domain. -/
  placed : ∀ c < ir.circuits.length, ∀ p,
    (CircuitEntry.pred p ∈ (ir.circuit c).entries ∨
      CircuitEntry.typeCheck p ∈ (ir.circuit c).entries) →
    (ir.predicate p).body.domain? = some (ir.circuit c).domain
  /-- Every LogUp identity reads only its circuit's domain. -/
  logup : ∀ c < ir.circuits.length, ∀ t g,
    CircuitEntry.realization (.logup t g) ∈ (ir.circuit c).entries →
    ∀ v ∈ ir.logupNodes t g, ir.ReadsIn (ir.circuit c).domain v
  /-- Every H half of a cross-field `equal` reads only its circuit's domain. -/
  macH : ∀ c < ir.circuits.length, ∀ p,
    CircuitEntry.realization (.macH p) ∈ (ir.circuit c).entries →
    ∀ v ∈ ir.macHNodes p, ir.ReadsIn (ir.circuit c).domain v
  /-- Every part of a batch is of the batch's domain. -/
  batches : ∀ b < ir.batches.length, ∀ p ∈ (ir.batch b).parts,
    (ir.predicate p).body.domain? = some (ir.batch b).domain
  /-- Every input block of a circuit holds a value of the circuit's domain. -/
  inputs : ∀ c < ir.circuits.length, ∀ blk ∈ (ir.circuit c).inputs, ∀ u, blk.value? = some u →
    (ir.value u).domain = (ir.circuit c).domain
  /-- Every late value's pad space is the whole field or a node of its domain's packing tree. -/
  pads : ∀ v < ir.values.length, ir.IsLate v → ∀ s, (ir.value v).padSpace = .node s →
    s ∈ treeNodes (ir.value v).domain

/-- **A quadratic predicate of domain `d` is of `d`.** -/
theorem domain_of_isQuad {d p : ℕ} (hq : ir.isQuad d p = true) :
    (ir.predicate p).body.domain? = some d := by
  obtain ⟨⟨a, b, c⟩, hl⟩ := Option.isSome_iff_exists.1 hq
  rw [(quadLeaves_spec hl).1]
  rfl

/-- **A predicate lowered into domain `d` is of `d`** (`RealizedProgram.Lowered`): an affine row or a row
on views by its sides, a placed predicate and a part of a batch (on columns or on bits) by the
check, a quadratic triple by its shape. -/
theorem Local.domain_of_lowered {treeNodes : ℕ → List String} (hl : ir.Local treeNodes)
    {d p : ℕ} (h : ir.Lowered d p) : (ir.predicate p).body.domain? = some d := by
  have hrow : ∀ {e e' : Expr}, (ir.predicate p).body.rowSides d = some (e, e') →
      (ir.predicate p).body.domain? = some d := by
    intro e e' hs
    unfold PredBody.rowSides at hs
    split at hs
    · rename_i hb
      split_ifs at hs with hd
      rw [hb, ← hd]
      rfl
    · rename_i hb
      split_ifs at hs with hd
      rw [hb, ← hd.1]
      rfl
    · cases hs
  rcases h with ⟨-, hr⟩ | ⟨-, hr⟩ | ⟨c, -, hmem⟩ | ⟨b, hmem⟩ | ⟨b, hok, hmem⟩ | ⟨-, hq⟩
  · unfold isRow at hr
    split at hr
    · exact hrow (by assumption)
    · cases hr
  · unfold isViewRow at hr
    split at hr
    · exact hrow (by assumption)
    · cases hr
  · rw [← c.2]
    exact hl.placed c.1 c.1.2 p hmem
  · have hb := colsBatchOk b.2
    rw [← hb.1.domain]
    exact hl.batches b.1 b.1.2 p hmem
  · have hb := bitsBatchOk hok
    rw [← hb.1.domain]
    exact hl.batches b b.2 p hmem
  · exact domain_of_isQuad hq

/-! ## The checker -/

theorem asgReads_succ (n v : ℕ) : ir.asgReads (n + 1) v = ir.asgReadsStep (ir.asgReads n) v :=
  rfl

theorem asgStep_congr (hwf : ir.WellFormed) : MemoDeps ir.asgStep ir.values ir.valueDeps := by
  refine ⟨fun v hv => hwf.valueDeps_lt hv, fun v hv r r' h => ?_⟩
  rw [← value_eq_getD]
  change ir.asgStep r v (ir.value v) = ir.asgStep r' v (ir.value v)
  unfold valueDeps at h
  unfold asgStep
  rcases hk : (ir.value v).kind with _ | ⟨_ | ⟨_, args⟩ | e⟩ | _ | _ | _ | ⟨w, sel⟩ | _ | _ <;>
    (rw [hk] at h; try simp only)
  · rw [List.flatMap_congr h]
  · have he := hwf.pubExpr_refs hv hk
    rw [List.flatMap_congr fun u hu => h u ((mem_nodesOf hwf.refsOrdered he u).1 hu)]
  · exact h w (List.mem_singleton_self _)

/-- **The table holds what each value reads of the committed assignment** (`asgReads` at the
program's fuel). -/
theorem mem_asgReadsT (hwf : ir.WellFormed) {v : ℕ} (hv : v < ir.values.length) (u : ℕ) :
    u ∈ ir.asgReads ir.fuel v ↔ u ∈ ir.asgReadsT.getD v [] := by
  refine iter_rel_memo (R := fun l l' => ∀ x, x ∈ l ↔ x ∈ l') asgReads_succ
    (fun v hv r r' h x => ?_) (asgStep_congr hwf) ir.fuel v (by simp [fuel]; omega) hv u
  rw [← value_eq_getD]
  change x ∈ ir.asgReadsStep r v ↔ x ∈ ir.asgStep r' v (ir.value v)
  unfold valueDeps at h
  unfold asgReadsStep asgStep
  rcases hk : (ir.value v).kind with _ | ⟨_ | ⟨_, args⟩ | e⟩ | _ | _ | _ | ⟨w, sel⟩ | _ | _ <;>
    rw [hk] at h <;> simp only [mem_insertAll, List.not_mem_nil, false_or, List.mem_flatMap]
  · exact exists_congr fun u => and_congr_right fun hu => h u hu x
  · have he := hwf.pubExpr_refs hv hk
    simp only [mem_nodesOf hwf.refsOrdered he]
    exact exists_congr fun u => and_congr_right fun hu => h u hu x
  · exact h w (List.mem_singleton_self _) x

variable (ir) in
/-- **The values outside domain `d`**, as a bit set (`failBits`), for `inDomB`. -/
def domFailBits (d : ℕ) : ℕ := failBits (fun _ (x : Value) => x.domain == d) ir.values 0

variable (ir) in
/-- **Value `u` is of domain `d`, as a test** (`inDomB_eq`): one `Nat.testBit` of `domFailBits`, where
`(ir.value u).domain` looks the value up in the values' trie. -/
def inDomB (d u : ℕ) : Bool :=
  bitTest (ir.domFailBits d) ir.values.length ((default : Value).domain == d) u

theorem inDomB_eq (d u : ℕ) : ir.inDomB d u = ((ir.value u).domain == d) := by
  rw [inDomB, domFailBits, bitTest_eq (fun _ (x : Value) => x.domain == d), value_eq_getD]

variable (ir) in
/-- **What each value reads of the committed assignment, in value order** (`asgReadsT`'s entries,
`getD_memoList`), for a walk of them. -/
def asgReadsL : List (List ℕ) := memoList ir.asgStep [] ir.values

variable (ir) in
/-- **The values reading the committed assignment outside domain `d`**, as a bit set (`failBits`
over `asgReadsL`, each read tested by `inDomB`). -/
def readsInFail (d : ℕ) : ℕ := failBits (fun _ rs => rs.all (ir.inDomB d)) ir.asgReadsL 0

variable (ir) in
/-- **`ReadsIn`, through the tables** (`readsInB_eq`): a value of the program whose bit is clear in
`readsInFail`, one `Nat.testBit` where a lookup of the reads' table and of each value read costs a
walk down a trie. -/
def readsInB (d v : ℕ) : Bool :=
  decide (v < ir.values.length) && bitTest (ir.readsInFail d) ir.asgReadsL.length true v

theorem readsInB_eq (d v : ℕ) : ir.readsInB d v =
    (decide (v < ir.values.length) && (ir.asgReadsT.getD v []).all fun u => (ir.value u).domain == d) := by
  rw [readsInB]
  by_cases hv : v < ir.values.length
  · have h := bitTest_eq (fun _ (rs : List ℕ) => rs.all (ir.inDomB d)) ir.asgReadsL v
    change bitTest (ir.readsInFail d) ir.asgReadsL.length true v = _ at h
    rw [h, show (default : List ℕ) = [] from rfl, asgReadsL, getD_memoList, ← asgReadsT]
    exact congrArg _ (all_congr_mem fun u _ => inDomB_eq d u)
  · simp [hv]

theorem readsIn_of_readsInB (hwf : ir.WellFormed) {d v : ℕ} (h : ir.readsInB d v = true) :
    ir.ReadsIn d v := fun u hu => by
  simp only [readsInB_eq, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, beq_iff_eq] at h
  exact h.2 u ((mem_asgReadsT hwf h.1 u).1 hu)

variable (ir) in
/-- **A circuit entry of domain `d` is local**, the challenges' values read through `ch`: a placed
predicate is of `d`, a LogUp identity reads only `d`. -/
def entryLocalWithB (ch : ℕ → Option ℕ) (d : ℕ) : CircuitEntry → Bool
  | .pred p => (ir.predicate p).body.domain? == some d
  | .typeCheck p => (ir.predicate p).body.domain? == some d
  | .realization (.logup t g) => (ir.logupNodesWith ch t g).all (ir.readsInB d)
  | .realization (.macH p) => (ir.macHNodesWith ch p).all (ir.readsInB d)
  | _ => true

variable (ir) in
/-- **A circuit entry of domain `d` is local** (`entryLocalWithB` at `chalNode`). -/
def entryLocalB (d : ℕ) : CircuitEntry → Bool := ir.entryLocalWithB ir.chalNode d

variable (ir) in
/-- **An input block of a circuit of domain `d` holds a value of `d`.** -/
def blockLocalB (d : ℕ) (blk : InputBlock) : Bool :=
  match blk.value? with
  | some u => (ir.value u).domain == d
  | none => true

variable (ir) in
/-- **A late value's pad space is the whole field or a node of its domain's tree.** -/
def padLocalB (treeNodes : ℕ → List String) (v : ℕ) (x : Value) : Bool :=
  !(decide (ir.IsLate v)) ||
    match x.padSpace with
    | .node s => decide (s ∈ treeNodes x.domain)
    | .full => true

variable (ir) in
/-- **`Local`, through the tables**, the challenges' values read through `ch`
(`Local.of_localWithB` for a well-formed program, where `ch` is `chalNode`). -/
def localWithB (ch : ℕ → Option ℕ) (treeNodes : ℕ → List String) : Bool :=
  ir.predicates.all (fun p =>
      match p.body.domain? with
      | some d => p.body.exprs.all (ir.closFlag Expr.directNodes (ir.readsInB d) ·.2) &&
          (ir.tableCols p.body).all (ir.readsInB d)
      | none => true) &&
    allIdx (fun _ c => c.entries.all (ir.entryLocalWithB ch c.domain) &&
      c.inputs.all (ir.blockLocalB c.domain)) ir.circuits 0 &&
    allIdx (fun _ b => b.parts.all fun p => (ir.predicate p).body.domain? == some b.domain)
      ir.batches 0 &&
    allIdx (ir.padLocalB treeNodes) ir.values 0

variable (ir) in
/-- **`Local`, through the tables** (`localWithB` at `chalNode`; `Local.of_localB` for a
well-formed program). -/
def localB (treeNodes : ℕ → List String) : Bool := ir.localWithB ir.chalNode treeNodes

/-- **The checker gives `Local`** for a well-formed program. -/
theorem Local.of_localB (hwf : ir.WellFormed) {treeNodes : ℕ → List String}
    (h : ir.localB treeNodes = true) : ir.Local treeNodes := by
  simp only [localB, localWithB, Bool.and_eq_true, allIdx_iff, zero_add, List.all_eq_true] at h
  obtain ⟨⟨⟨hp, hc⟩, hb⟩, hv⟩ := h
  refine ⟨fun p hpm d hd v hvm => ?_, fun c hcl p hmem => ?_, fun c hcl t g hmem v hvm => ?_,
    fun c hcl p hmem v hvm => ?_, fun b hbl p hpm => ?_, fun c hcl blk hblk u hu => ?_,
    fun v hvl hlate s hs => ?_⟩
  · have h1 := hp p hpm
    rw [hd] at h1
    simp only [Bool.and_eq_true, List.all_eq_true] at h1
    refine readsIn_of_readsInB hwf ?_
    rcases List.mem_append.1 hvm with hu | hu
    · obtain ⟨de, hde, hu⟩ := List.mem_flatMap.1 hu
      have := h1.1 de hde
      rw [closFlag_eq hwf.refsOrdered _ _ (hwf.bodyRefsOk hpm de hde), List.all_eq_true] at this
      exact this v hu
    · exact h1.2 v hu
  · have h1 := (hc c hcl).1
    rcases hmem with hm | hm
    · have h2 := h1 _ hm
      simp only [entryLocalWithB, beq_iff_eq] at h2
      exact h2
    · have h2 := h1 _ hm
      simp only [entryLocalWithB, beq_iff_eq] at h2
      exact h2
  · have h1 := (hc c hcl).1 _ hmem
    simp only [entryLocalWithB, List.all_eq_true] at h1
    exact readsIn_of_readsInB hwf (h1 v hvm)
  · have h1 := (hc c hcl).1 _ hmem
    simp only [entryLocalWithB, List.all_eq_true] at h1
    exact readsIn_of_readsInB hwf (h1 v hvm)
  · have h2 := hb b hbl p hpm
    simp only [beq_iff_eq] at h2
    exact h2
  · have h1 := (hc c hcl).2 blk hblk
    simp only [blockLocalB, hu, beq_iff_eq] at h1
    exact h1
  · have h1 := hv v hvl
    simp only [padLocalB, Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
      decide_eq_false_iff_not] at h1
    rcases h1 with h1 | h1
    · exact absurd hlate h1
    · rw [← value_eq_getD] at h1
      change (match (ir.value v).padSpace with
        | .node s => decide (s ∈ treeNodes (ir.value v).domain)
        | .full => true) = true at h1
      rw [hs] at h1
      exact of_decide_eq_true h1

/-- **The checker gives `Local`** for a well-formed program, the challenges' values read through
any `ch` that agrees with `chalNode` (`Structure.chalOf`, checked by `chalNode_eq_chalOf`). -/
theorem Local.of_localWithB (hwf : ir.WellFormed) {ch : ℕ → Option ℕ}
    (hch : ∀ j, ir.chalNode j = ch j) {treeNodes : ℕ → List String}
    (h : ir.localWithB ch treeNodes = true) : ir.Local treeNodes := by
  have : ch = ir.chalNode := funext fun j => (hch j).symm
  subst this
  exact Local.of_localB hwf h

end

end GordieHowe.RealizedProgram
