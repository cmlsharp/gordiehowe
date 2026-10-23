-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.RealizedProgram.Annotations

@[expose] public section

/-!
# GordieHowe: the exported reads through a reads annotation

`readsB` builds what every value reads from the run (`readsT`) and every predicate's values
through the closures' table. The compiler emits a **reads annotation** (`ReadsAnn`): for every
value the codes of the reads it covers (`Read.code`), as packed lists. One local rule per value
checks that its reads cover its own (a challenge, a late value, a message's late value) and those
of the values it reads (a public expression's, through the packed closures of `closuresOkB`, an
opaque value's arguments, a bit view's words); every predicate's values' reads must lie among its
exported reads (`readsAnnOkB`). The rules give `ReadsSound` (`readsSound_of_ann`) without building
the tables.

The annotation also gives, per value, whether it reads a late value, or a late value of a given
kind (`readsLateB`): the masks the honest checks read.
-/

namespace GordieHowe.RealizedProgram

/-- **The code of a read**: `3 c` for challenge `c`, `3 v + 1` for late value `v`, `3 v + 2` for
its pad. -/
def Read.code : Read → ℕ
  | .chal c => 3 * c
  | .late v => 3 * v + 1
  | .pad v => 3 * v + 2

theorem Read.code_inj {r r' : Read} (h : r.code = r'.code) : r = r' := by
  cases r <;> cases r' <;> simp only [Read.code] at h <;> first | (congr 1; omega) | omega

theorem Read.mem_of_code_mem {r : Read} {l : List Read} (h : r.code ∈ l.map Read.code) : r ∈ l := by
  obtain ⟨r', hr', he⟩ := List.mem_map.1 h
  rw [← Read.code_inj he]
  exact hr'

/-- **The reads annotation**: per value, the codes of its reads. -/
structure ReadsAnn where
  /-- The values' reads, packed. -/
  reads : PackedLists

section Check

variable (ir : RealizedProgram)

/-- **The values an expression reads, through packed closures**: its own, then its shared
expressions' (`closuresOkB`). -/
def nodesC (c : PackedLists) (e : Expr) : List ℕ := e.directNodes ++ e.refs.flatMap c.get

/-- **`a` lies within `b`**, as lists of codes. -/
def readsSubB (a b : List ℕ) : Bool := a.all fun x => b.contains x

/-- **The local rule of value `v`'s reads**: they cover its own and those of the values it
reads. -/
def readsOwnB (c : PackedLists) (r : PackedLists) (v : ℕ) (x : Value) : Bool :=
  match x.kind with
  | .pub (.expr e) => (nodesC c e).all fun u => readsSubB (r.get u) (r.get v)
  | .pub (.opaque _ args) => args.all fun u => readsSubB (r.get u) (r.get v)
  | .challenge c' => (r.get v).contains (Read.chal c').code
  | .late => (r.get v).contains (Read.late v).code
  | .bits w _ => readsSubB (r.get w) (r.get v)
  | .message u => (r.get v).contains (Read.late u).code
  | _ => true

/-- **The reads annotation checks**, in one pass over the values and one over the predicates:
every value's reads pass their local rule, and every predicate's values' reads lie among its
exported reads. -/
def readsAnnOkB (c : PackedLists) (a : ReadsAnn) : Bool :=
  allIdx (fun v x => readsOwnB c a.reads v x) ir.values 0 &&
    ir.predicates.all fun p =>
      ((p.body.exprs.flatMap fun de => nodesC c de.2) ++ ir.tableCols p.body).all fun u =>
        readsSubB (a.reads.get u) (p.reads.map Read.code)

/-- **Value `v` reads a late value passing `q`**, through the annotation. -/
def readsLateB (a : ReadsAnn) (q : ℕ → Bool) (v : ℕ) : Bool :=
  (a.reads.get v).any fun x => x % 3 == 1 && q (x / 3)

end Check

variable {ir : RealizedProgram}

theorem readsSubB_mem {a b : List ℕ} (h : readsSubB a b = true) {x : ℕ} (hx : x ∈ a) : x ∈ b := by
  unfold readsSubB at h
  exact List.contains_iff_mem.1 (List.all_eq_true.1 h x hx)

/-- **The values an expression reads are those through the packed closures**, for its shared
expressions among the program's. -/
theorem mem_nodesC {c : PackedLists} (hc : ir.closuresOkB c = true) {e : Expr}
    (he : ∀ k ∈ e.refs, k < ir.exprs.length) {u : ℕ} (hu : u ∈ ir.exprNodes e) :
    u ∈ nodesC c e := by
  unfold exprNodes closure at hu
  unfold nodesC
  rcases List.mem_append.1 hu with hu | hu
  · exact List.mem_append_left _ hu
  · obtain ⟨k, hk, hu⟩ := List.mem_flatMap.1 hu
    exact List.mem_append_right _ (List.mem_flatMap.2 ⟨k, hk,
      (mem_get_of_closuresOk hc _ k (he k hk) (he k hk) u).1 hu⟩)

/-- **The annotation covers every value's reads**, at every level. -/
theorem nodeReads_code_mem (hwf : ir.WellFormed) {c : PackedLists} (hc : ir.closuresOkB c = true)
    {a : ReadsAnn} (h : ir.readsAnnOkB c a = true) :
    ∀ n v, ∀ rd ∈ ir.nodeReads n v, rd.code ∈ a.reads.get v := by
  unfold readsAnnOkB at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨hv, -⟩ := h
  rw [allIdx_iff] at hv
  intro n
  induction n with
  | zero => intro v rd hrd; simp [nodeReads] at hrd
  | succ n ih =>
    intro v rd hrd
    by_cases hvl : v < ir.values.length
    · have hr := hv v hvl
      simp only [Nat.zero_add] at hr
      change readsOwnB c a.reads v (ir.value v) = true at hr
      unfold readsOwnB at hr
      simp only [nodeReads] at hrd
      split at hrd
      · rename_i e he
        rw [he] at hr
        obtain ⟨u, hu, hru⟩ := List.mem_flatMap.1 hrd
        exact readsSubB_mem (List.all_eq_true.1 hr u
          (mem_nodesC hc (hwf.pubExpr_refs hvl he) hu)) (ih u rd hru)
      · rename_i nm args he
        rw [he] at hr
        obtain ⟨u, hu, hru⟩ := List.mem_flatMap.1 hrd
        exact readsSubB_mem (List.all_eq_true.1 hr u hu) (ih u rd hru)
      · rename_i c' he
        rw [he] at hr
        simp only [List.mem_singleton] at hrd
        subst hrd
        exact List.contains_iff_mem.1 hr
      · rename_i he
        rw [he] at hr
        simp only [List.mem_singleton] at hrd
        subst hrd
        exact List.contains_iff_mem.1 hr
      · rename_i w sel he
        rw [he] at hr
        exact readsSubB_mem hr (ih w rd hrd)
      · rename_i u he
        rw [he] at hr
        simp only [List.mem_singleton] at hrd
        subst hrd
        exact List.contains_iff_mem.1 hr
      · simp at hrd
    · have hd : ir.value v = default := by
        rw [RealizedProgram.value, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
        rfl
      simp only [nodeReads, hd] at hrd
      exact absurd hrd List.not_mem_nil

/-- **The exported reads are sound** from a reads annotation that checks, at packed closures that
check. -/
theorem readsSound_of_ann (hwf : ir.WellFormed) {c : PackedLists} (hc : ir.closuresOkB c = true)
    {a : ReadsAnn} (h : ir.readsAnnOkB c a = true) : ir.ReadsSound := by
  have hn := nodeReads_code_mem hwf hc h
  unfold readsAnnOkB at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨-, hp⟩ := h
  unfold ReadsSound
  intro p hpm rd hrd
  unfold predReads predNodes at hrd
  simp only [List.mem_flatMap] at hrd
  obtain ⟨u, hu, hru⟩ := hrd
  have hall := List.all_eq_true.1 (List.all_eq_true.1 hp p hpm)
  have hu' : u ∈ (p.body.exprs.flatMap fun de => nodesC c de.2) ++ ir.tableCols p.body := by
    rcases List.mem_append.1 hu with hu | hu
    · obtain ⟨de, hde, hu⟩ := List.mem_flatMap.1 hu
      exact List.mem_append_left _ (List.mem_flatMap.2
        ⟨de, hde, mem_nodesC hc (hwf.bodyRefsOk hpm de hde) hu⟩)
    · exact List.mem_append_right _ hu
  exact Read.mem_of_code_mem (readsSubB_mem (hall u hu') (hn _ u rd hru))

/-- **A value reading a late value passing `q`** has it in the annotation (`readsLateB`). -/
theorem readsLateB_of_mem (hwf : ir.WellFormed) {c : PackedLists} (hc : ir.closuresOkB c = true)
    {a : ReadsAnn} (h : ir.readsAnnOkB c a = true) {q : ℕ → Bool} {v u : ℕ}
    (hu : Read.late u ∈ ir.nodeReads ir.fuel v) (hq : q u = true) : readsLateB a q v = true := by
  have hm := nodeReads_code_mem hwf hc h _ v _ hu
  unfold readsLateB
  refine List.any_eq_true.2 ⟨_, hm, ?_⟩
  simp only [Read.code, Bool.and_eq_true, beq_iff_eq]
  refine ⟨by omega, ?_⟩
  rwa [show (3 * u + 1) / 3 = u by omega]

end GordieHowe.RealizedProgram
