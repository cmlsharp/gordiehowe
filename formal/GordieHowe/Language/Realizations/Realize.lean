-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.Realizations.RealizeField
public import GordieHowe.Language.Realizations.RealizeCommitted

@[expose] public section

/-!
# GordieHowe: the realization step's reading lemmas

Lemmas the realization step (`GordieHowe.RealizedProgram.realizeLowering_of_derivs`) and its honest
domains read:

* **Reads before a challenge**: a value read before challenge `j` reads alike in two environments
  that agree on what is fixed before `j` (`reader_eq_of_readsBefore`), so the needles, the
  histograms, the table rows and the MAC events read alike off the challenge
  (`groupNeedles_congr`, `histRead_congr`, `tableRow_congr`, `groupEvent_congr`, `macEvent_congr`).
* **The realized assignment** (`GordieHowe.RealizedProgram.bindAsg`): a value bound to its digits
  reads its expression, from the committed values and constants (`reader_bindAsg_of_boundOk`,
  `GordieHowe.RealizedProgram.BoundOk`).
* **The opaque functions' ranges** (`OpaqueRanges`): the value ranges the opaque values computed
  from the statement meet (`reader_of_declared`, `ranges_reader`).
-/

namespace GordieHowe.RealizedProgram

open Export Range IOP ProofSystem.PhaseLayout
open scoped NNReal ENNReal

section

variable {ir : RealizedProgram} {I : Interp}

/-! ## Reads before a challenge -/

/-- **A value read before challenge `j` reads alike** in two environments that agree on the
statement, the committed assignment, the challenges other than `j` drawn no later than `j`, and the
late values of the phases before `j`'s. -/
theorem reader_eq_of_readsBefore {j v : ℕ} (hr : ir.ReadsBefore j v) {e e' : ir.Env I}
    (hs : e.stmt = e'.stmt) (ha : e.asg = e'.asg)
    (hc : ∀ c, c ≠ j → ir.ChalBefore c j → e.chal c = e'.chal c)
    (hl : ∀ u, (ir.value u).phase < (ir.challenge j).phase → e.late u = e'.late u) :
    ir.reader e v = ir.reader e' v :=
  read_congr _ v
    { stmt := hs
      asg := ha
      chal := fun c hcr => (hr _ hcr).elim fun hne hb => hc c hne hb
      late := fun u hur => hl u (hr _ hur) }

/-- **Two environments that agree up to `j` read a value read before `j` alike.** -/
theorem reader_eq_of_eqUpTo {j v : ℕ} (hr : ir.ReadsBefore j v) {e e' : ir.Env I}
    (h : Env.EqUpTo j e e') : ir.reader e v = ir.reader e' v :=
  reader_eq_of_readsBefore hr h.stmt h.asg (fun c _ hb => h.chal c hb) h.late

/-- **Setting challenge `j` leaves a value read before `j` unchanged.** -/
theorem reader_setChal {j v : ℕ} (hr : ir.ReadsBefore j v) (e : ir.Env I) (c : ir.ChalVal I j) :
    ir.reader (e.setChal j c) v = ir.reader e v :=
  reader_eq_of_readsBefore hr rfl rfl (fun _ hne _ => Function.update_of_ne hne _ _)
    fun _ _ => rfl

/-- **A group's needles depend only on its members' values.** -/
theorem groupNeedles_congr {rd rd' : ir.Valuation I} {f t g : ℕ}
    (h : ∀ m ∈ ir.members t g, ∀ v ∈ ir.exprNodes (ir.needleExpr m.pred m.needle), rd v = rd' v) :
    ir.groupNeedles rd f t g = ir.groupNeedles rd' f t g := by
  refine List.flatMap_congr fun m hm => ?_
  simp only [memberVals, evalE_congr (f := f) (h m hm)]

/-- **A histogram depends only on its value.** -/
theorem histRead_congr {rd rd' : ir.Valuation I} {f T : ℕ} {o : Option ℕ}
    (h : ∀ v ∈ o.toList, rd v = rd' v) : ir.histRead rd f T o = ir.histRead rd' f T o := by
  cases o with
  | none => rfl
  | some v =>
    funext j
    simp only [histRead, h v (List.mem_singleton_self v)]

/-- **A valid table's rows are the same in two readers that agree on the values read before its
challenge**: a committed table's column is read before it (`ColumnsOk.reads`), and so is every
value an expression's coordinates read (`ExprRowsOk.reads`). -/
theorem tableRow_congr {t : ℕ} (ht : ir.TableOk t) {rd rd' : ir.Valuation I} (f : ℕ)
    (h : ∀ v, ir.ReadsBefore (ir.alphaOf t) v → rd v = rd' v) :
    ir.tableRow rd f t = ir.tableRow rd' f t := by
  funext j
  unfold tableRow
  split
  · rfl
  · rename_i cols hc
    have hcols := ht.rows
    rw [hc] at hcols
    rw [h _ (hcols : ir.ColumnsOk t cols).reads]
  · rename_i e' hc
    have hrows := ht.rows
    rw [hc] at hrows
    exact congrFun (evalE_congr fun v hv => h v ((hrows : ir.ExprRowsOk t e').reads v hv)) j

/-- **A valid group's lookup polynomial is the same in two readers that agree on the values read
before its table's challenge.** -/
theorem groupEvent_congr {t g : ℕ} (ht : ir.TableOk t) (hg : g < ir.groupCountOf t)
    {rd rd' : ir.Valuation I} (f : ℕ)
    (h : ∀ v, ir.ReadsBefore (ir.alphaOf t) v → rd v = rd' v) :
    ir.groupEvent rd f t g = ir.groupEvent rd' f t g := by
  have hgo := ht.groups g hg
  simp only [groupEvent, staticHist, lateHist]
  rw [groupNeedles_congr fun m hm v hv => h v ((hgo.members m hm).reads v hv),
    histRead_congr fun v hv => h v (hgo.hists v (List.mem_append_left _ hv)),
    histRead_congr fun v hv => h v (hgo.hists v (List.mem_append_right _ hv)),
    tableRow_congr ht f h]

/-! ## The MAC's event before its key -/

variable {primeNodes : ℕ → List String} {L : ℕ → ℕ → Option Ivl}

/-- **A MAC's binding event is the same in two environments** that agree on the committed
assignment (the tag's pad) and on the values its operands and its blinds read. -/
theorem macEvent_congr {e e' : ir.Env I} {dx dy : ℕ} {x y : Expr} {real : MacRealization}
    (ha : e.asg = e'.asg) (hx : ∀ v ∈ ir.exprNodes x, ir.reader e v = ir.reader e' v)
    (hy : ∀ v ∈ ir.exprNodes y, ir.reader e v = ir.reader e' v)
    (hb : ir.reader e (real.blind.getD 0) = ir.reader e' (real.blind.getD 0))
    (hbx : ∀ bx ∈ real.blindX, ir.reader e bx = ir.reader e' bx) :
    ir.macEvent e dx x dy y real = ir.macEvent e' dx x dy y real := by
  have hX : ∀ f, ir.evalE (ir.reader e) f x = ir.evalE (ir.reader e') f x := fun _ => evalE_congr hx
  have hY : ∀ f, ir.evalE (ir.reader e) f y = ir.evalE (ir.reader e') f y := fun _ => evalE_congr hy
  unfold macEvent
  split
  · unfold macChunkH macChunkA macBlindTag evalPad evalWith
    rw [hX, hY, hb, ha]
  · rename_i bx hbx'
    unfold macChunkA macBlindTag evalPad evalWith
    rw [hX, hY, hb, hbx bx hbx']

/-! ## Values bound to their digits -/

/-- **The realized assignment reads a bound value through its digits** (`BoundOk`): in an
environment at the realized assignment `bindAsg a`, a value bound to its digits reads its expression
`e` at the environment's reader, since `e` reads only committed values (which `bindAsg` keeps) and
constants. -/
theorem reader_bindAsg_of_boundOk (hbd : ∀ v < ir.values.length, ir.BoundOk v) {e : ir.Env I}
    {a : ir.Assignment I} (he : e.asg = ir.bindAsg a) {v : ℕ} (hvl : v < ir.values.length)
    {x : Expr} (hk : (ir.value v).kind = .bound x) :
    ir.reader e v = ir.evalE (ir.reader e) (ir.valueField v) x := by
  have hb := hbd v hvl
  rw [BoundOk, hk] at hb
  funext i
  have hrd : ir.reader e v i = (ir.bindAsg a).val v i := by
    simp only [reader, fuel, read, hk, he]
  rw [hrd]
  simp only [bindAsg, hk]
  refine congrFun (evalE_congr fun u hu => ?_) i
  funext j
  have hu' := hb.2 u hu
  unfold isPrivOrConst at hu'
  unfold committedRead
  split at hu'
  · rename_i hku
    rw [hku, reader_of_priv e hku, he, ir.bindAsg_val_of_isBound (v := u) _ (by rw [hku]; rfl)]
  · rename_i es hku
    rw [hku, reader_of_constant e hku]
  · cases hu'

/-- Whether a value's kind is an opaque statement value with no arguments. -/
def isOpaqueNil : Kind → Bool
  | .pub (.opaque _ []) => true
  | _ => false

variable (I) in
/-- **The ranges of the opaque functions** `orng`, a property of the interpretation: for every
entry `(v, N)`, `v` is an opaque statement value computed from arguments, of a field of the program
of characteristic at least `N`, whose function returns naturals below `N`. These are the C++
operators' entry bounds on public values the verifier computes from the statement (the plan's
`op-bound` `entryBound`), which the program does not check. -/
def OpaqueRanges (orng : List (ℕ × ℕ)) : Prop :=
  ∀ vN ∈ orng, ir.valueField vN.1 < ir.fields.length ∧ vN.2 ≤ ir.charOf (ir.valueField vN.1) ∧
    ∃ name args, (ir.value vN.1).kind = .pub (.opaque name args) ∧ args ≠ [] ∧
      ∀ xs i, I.opaqueFn name xs i < vN.2

/-- **No opaque ranges hold.** -/
theorem opaqueRanges_nil : ir.OpaqueRanges I [] := fun _ h => absurd h List.not_mem_nil

/-- **A value with a declared bound is read from the statement.** -/
theorem reader_of_declared (e : ir.Env I) {vN : ℕ × ℕ} (h : vN ∈ ir.declaredRanges) :
    ir.reader e vN.1 = e.stmt vN.1 := by
  unfold declaredRanges at h
  obtain ⟨v, -, hv⟩ := List.mem_filterMap.1 h
  split_ifs at hv with hk
  obtain ⟨N, -, rfl⟩ := Option.map_eq_some_iff.1 hv
  funext i
  unfold isStmtLeaf at hk
  split at hk
  · rename_i hk'
    simp [reader, fuel, read, hk']
  · rename_i name hk'
    simp [reader, fuel, read, hk']
  · cases hk

/-- **The value ranges hold at the reader** (`ShiftFacts.stmt` at `declaredRanges ++ orng`): at a
statement within the declared bounds, every declared value's coordinates are casts of naturals
below its bound, and every opaque value listed in `orng` is (its function's range, `hO`). -/
theorem ranges_reader (hL : I.Lawful ir primeNodes) {orng : List (ℕ × ℕ)}
    (hO : ir.OpaqueRanges I orng) (e : ir.Env I) (hB : ir.StmtBounded I e.stmt) :
    ∀ vN ∈ ir.declaredRanges ++ orng, ∀ i < (ir.value vN.1).size,
      ∃ n < vN.2, ir.reader e vN.1 i = ((n : ℕ) : (I (ir.valueField vN.1)).K) := by
  intro vN hvN i hi
  rcases List.mem_append.1 hvN with hd | ho
  · rw [reader_of_declared e hd]
    exact hB vN hd i hi
  · obtain ⟨hf, hNc, name, args, hk, hne, hlt⟩ := hO vN ho
    obtain ⟨xs, hrd⟩ := reader_opaque e hk hne i
    refine ⟨_, hlt xs i, ?_⟩
    rw [hrd, hL.decode_natCast _ hf _ (lt_of_lt_of_le (hlt xs i) hNc)]

/-! ## The events' probability -/

/-- **The groups at challenge `j`.** -/
theorem mem_realGroups {j : ℕ} {tg : ℕ × ℕ} :
    tg ∈ ir.realGroups j ↔ tg.1 < ir.tables.length ∧ ir.alphaOf tg.1 = j ∧
      tg.2 < ir.groupCountOf tg.1 := by
  obtain ⟨t, g⟩ := tg
  simp only [realGroups, List.mem_flatMap, List.mem_filter, List.mem_range, decide_eq_true_eq,
    List.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨t', ⟨ht', hj⟩, g', hg', rfl, rfl⟩
    exact ⟨ht', hj, hg'⟩
  · rintro ⟨ht, hj, hg⟩
    exact ⟨t, ⟨ht, hj⟩, g, hg, rfl, rfl⟩

/-- **A sum over the values of a partial map is the sum of the values with `0` where it has none.** -/
theorem sum_filterMap_eq_sum_map_getD {α : Type} (g : α → Option ℕ) :
    ∀ l : List α, (l.filterMap g).sum = (l.map fun a => (g a).getD 0).sum
  | [] => rfl
  | a :: l => by
    rw [List.filterMap_cons, List.map_cons, List.sum_cons, ← sum_filterMap_eq_sum_map_getD g l]
    cases g a <;> simp

/-! ## The lowering -/

/-- **Runs that agree through phase `k + 1` give environments that agree up to each challenge of
that phase.** -/
theorem layoutEnv_eqUpTo {x : ir.Valuation I} {a : ir.Assignment I} {k : Fin ir.phases}
    {r r' : (ir.layout I).Run} (h : r.EqThrough k r') (jj : ir.ChalAt k) :
    Env.EqUpTo jj.1 (ir.layoutEnv I x a r) (ir.layoutEnv I x a r') where
  stmt := rfl
  asg := rfl
  chal j' hj' := by
    have hp : (ir.challenge j').phase ≤ k + 1 := by
      rw [← jj.2]
      rcases hj' with hj' | ⟨hj', _⟩ <;> omega
    exact chalRead_eq_of_le h.chal hp
  late u hu := by
    funext i
    have hp : (ir.value u).phase < k + 1 := by rw [← jj.2]; exact hu
    simp only [layoutEnv, msgRead_eq_of_lt h.msg hp]

/-- **Updating one challenge of a phase sets it in the layout's environment.** -/
theorem layoutEnv_setChal_update (x : ir.Valuation I) (a : ir.Assignment I)
    (r : (ir.layout I).Run) {k : Fin ir.phases} (f : (ir.layout I).Ch k) (jj : ir.ChalAt k)
    (v : ir.ChalVal I jj.1) :
    ir.layoutEnv I x a (r.setChal k (Function.update f jj v)) =
      (ir.layoutEnv I x a (r.setChal k f)).setChal jj.1 v := by
  simp only [layoutEnv, Env.setChal]
  congr 1
  funext j' i
  by_cases hj : j' = jj.1
  · subst hj
    rw [Function.update_self]
    have hvalid : (jj.1 : ℕ) < ir.challenges.length ∧ 1 ≤ (ir.challenge jj.1).phase ∧
        (ir.challenge jj.1).phase ≤ ir.phases := by
      have := jj.2
      have := k.2
      exact ⟨jj.1.2, by omega, by omega⟩
    unfold chalRead
    by_cases hi : i < (ir.challenge jj.1).size
    · rw [dite_eq_left_of_eq_true (eq_true ⟨hvalid.1, hvalid.2.1, hvalid.2.2, hi⟩),
        dite_eq_left_of_eq_true (eq_true hi)]
      congr 1
      have hh := setChal_update_chal_self r f jj v
        ⟨(ir.challenge jj.1).phase - 1, by omega⟩ ⟨⟨jj.1, hvalid.1⟩, by simp only; omega⟩
        (Fin.ext (by have := jj.2; simp only; omega)) rfl
      exact congrFun (eq_of_heq hh) ⟨i, hi⟩
    · rw [dite_eq_right_of_eq_false (eq_false fun h => hi h.2.2.2),
        dite_eq_right_of_eq_false (eq_false hi)]
  · rw [Function.update_of_ne hj]
    unfold chalRead
    split_ifs with hvalid
    · congr 1
      have hh := setChal_update_chal r f jj v (f jj) ⟨(ir.challenge j').phase - 1, by omega⟩
        ⟨⟨j', hvalid.1⟩, by simp only; omega⟩ (by simpa using hj)
      rw [Function.update_eq_self] at hh
      exact congrFun hh _
    · rfl

open Classical in
end

end GordieHowe.RealizedProgram
