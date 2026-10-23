-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.Assumptions

@[expose] public section

/-!
# GordieHowe: the committed cells of a program's domain

The committed coordinates of domain `d` of a program (`RealizedProgram.Cell d`): every coordinate of a
value of `d` committed in phase `0` (a committed value or a pad copy), every coordinate of the pad
of a late value of `d`, and every filler input of a GKR circuit of `d`. Derived values (bit views,
public values, values bound to their digits) have no cell.

* `GordieHowe.RealizedProgram.ofCells`: the committed assignment of the program read from the cells (`0` at every
  coordinate that is not a cell);
* `GordieHowe.RealizedProgram.cellBase`: the base of a cell, the set its value lies in by the domain's packing tree:
  the packing-tree node of its value, the pad space of its late value, the whole field for filler.
-/

namespace GordieHowe.RealizedProgram

open Export

/-- **A committed coordinate** of a program: coordinate `i` of the committed value `v`, coordinate
`i` of the pad of late value `v`, or filler input `j` of circuit `c`. -/
inductive CellKey where
  /-- Coordinate `i` of committed value `v`. -/
  | val (v i : ℕ)
  /-- Coordinate `i` of the pad of late value `v`. -/
  | pad (v i : ℕ)
  /-- Filler input `j` of circuit `c`. -/
  | filler (c j : ℕ)
  deriving DecidableEq, Repr

/-- The cell keys as a sum of pairs of naturals. -/
def CellKey.equivSum : CellKey ≃ (ℕ × ℕ) ⊕ (ℕ × ℕ) ⊕ (ℕ × ℕ) where
  toFun
    | .val v i => .inl (v, i)
    | .pad v i => .inr (.inl (v, i))
    | .filler c j => .inr (.inr (c, j))
  invFun
    | .inl (v, i) => .val v i
    | .inr (.inl (v, i)) => .pad v i
    | .inr (.inr (c, j)) => .filler c j
  left_inv k := by cases k <;> rfl
  right_inv x := by rcases x with ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ <;> rfl

/-- The cell keys are encoded as a sum of pairs of naturals (`CellKey.equivSum`). -/
instance : Encodable CellKey := Encodable.ofEquiv _ CellKey.equivSum

/-- The filler inputs of circuit `c` in one of its input blocks. -/
def InputBlock.fillerKeys (c : ℕ) : InputBlock → List CellKey
  | .filler a n => (List.range n).map fun j => .filler c (a + j)
  | _ => []

section

variable (ir : RealizedProgram)

/-- **Value `v` is committed in domain `d`**: a committed value or a pad copy of `d`. -/
def isCellValue (d v : ℕ) : Bool :=
  (ir.value v).domain == d &&
    match (ir.value v).kind with
    | .priv => true
    | .padCopy _ _ => true
    | _ => false

/-- **Value `v` is a late value of domain `d`**: a late value of `d` that lies in its domain (not
the tag of a MAC that no domain hosts, whose field no domain commits and whose pad is a cell of no
domain). -/
def isLateOf (d v : ℕ) : Bool :=
  (ir.value v).field.isNone && (ir.value v).domain == d && decide (ir.IsLate v)

/-- **The committed coordinates of domain `d`**, as keys: the coordinates of its committed values,
of the pads of its late values, and its circuits' filler inputs. -/
def cellKeys (d : ℕ) : List CellKey :=
  (List.range ir.values.length).flatMap (fun v =>
      if ir.isCellValue d v then (List.range (ir.value v).size).map (.val v)
      else if ir.isLateOf d v then (List.range (ir.value v).size).map (.pad v)
      else []) ++
    (List.range ir.circuits.length).flatMap fun c =>
      if (ir.circuit c).domain = d then (ir.circuit c).inputs.flatMap (·.fillerKeys c) else []

/-- **The committed cells of domain `d`** (see the module docstring). -/
def Cell (d : ℕ) : Type := {k : CellKey // k ∈ ir.cellKeys d}

instance (d : ℕ) : Fintype (ir.Cell d) := inferInstanceAs (Fintype {k // k ∈ ir.cellKeys d})

instance (d : ℕ) : DecidableEq (ir.Cell d) := inferInstanceAs (DecidableEq {k // k ∈ ir.cellKeys d})

/-- The cells are encoded by their keys. -/
instance (d : ℕ) : Encodable (ir.Cell d) := inferInstanceAs (Encodable {k // k ∈ ir.cellKeys d})

theorem mem_cellKeys_val {d u i : ℕ} :
    CellKey.val u i ∈ ir.cellKeys d ↔
      u < ir.values.length ∧ ir.isCellValue d u = true ∧ i < (ir.value u).size := by
  simp only [cellKeys, List.mem_append, List.mem_flatMap, List.mem_range]
  constructor
  · rintro (⟨v, hv, h⟩ | ⟨c, -, h⟩)
    · split_ifs at h with h1 h2
      · simp only [List.mem_map, List.mem_range, CellKey.val.injEq] at h
        obtain ⟨j, hj, rfl, rfl⟩ := h
        exact ⟨hv, h1, hj⟩
      · simp at h
      · simp at h
    · split_ifs at h
      · simp only [List.mem_flatMap] at h
        obtain ⟨b, -, hb⟩ := h
        cases b <;> simp [InputBlock.fillerKeys] at hb
      · simp at h
  · rintro ⟨hu, h1, hi⟩
    exact .inl ⟨u, hu, by simp [h1, hi]⟩

theorem mem_cellKeys_pad {d u i : ℕ} :
    CellKey.pad u i ∈ ir.cellKeys d ↔
      u < ir.values.length ∧ ir.isCellValue d u = false ∧ ir.isLateOf d u = true ∧
        i < (ir.value u).size := by
  simp only [cellKeys, List.mem_append, List.mem_flatMap, List.mem_range]
  constructor
  · rintro (⟨v, hv, h⟩ | ⟨c, -, h⟩)
    · split_ifs at h with h1 h2
      · simp at h
      · simp only [List.mem_map, List.mem_range, CellKey.pad.injEq] at h
        obtain ⟨j, hj, rfl, rfl⟩ := h
        exact ⟨hv, by simpa using h1, h2, hj⟩
      · simp at h
    · split_ifs at h
      · simp only [List.mem_flatMap] at h
        obtain ⟨b, -, hb⟩ := h
        cases b <;> simp [InputBlock.fillerKeys] at hb
      · simp at h
  · rintro ⟨hu, h1, h2, hi⟩
    exact .inl ⟨u, hu, by simp [h1, h2, hi]⟩

/-- The value of a committed cell is a value of the domain. -/
theorem isCellValue_domain {d u : ℕ} (h : ir.isCellValue d u = true) : (ir.value u).domain = d := by
  simp only [isCellValue, Bool.and_eq_true, beq_iff_eq] at h
  exact h.1

/-- A late value of a domain is a value of the domain. -/
theorem isLateOf_domain {d u : ℕ} (h : ir.isLateOf d u = true) : (ir.value u).domain = d := by
  simp only [isLateOf, Bool.and_eq_true, beq_iff_eq] at h
  exact h.1.2

theorem isLateOf_isLate {d u : ℕ} (h : ir.isLateOf d u = true) : ir.IsLate u := by
  simp only [isLateOf, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.2

/-- **A committed value of a domain has the domain's field.** -/
theorem isCellValue_valueField {d u : ℕ} (h : ir.isCellValue d u = true) :
    ir.valueField u = ir.domainField d := by
  rw [← ir.isCellValue_domain h]
  refine ir.valueField_of_allowsField ?_
  simp only [isCellValue, Bool.and_eq_true] at h
  revert h
  cases (ir.value u).kind <;> simp [Kind.allowsField]

/-- **A late value of a domain has the domain's field.** -/
theorem isLateOf_valueField {d u : ℕ} (h : ir.isLateOf d u = true) :
    ir.valueField u = ir.domainField d := by
  rw [← ir.isLateOf_domain h]
  refine ir.valueField_of_field_none ?_
  simp only [isLateOf, Bool.and_eq_true, Option.isNone_iff_eq_none] at h
  exact h.1.1

variable (I : Interp)

/-- **The committed assignment read from the cells `a` of domain `d`**: each cell's value at its
coordinate, `0` at every coordinate that is not a cell. -/
def ofCells (d : ℕ) (a : ir.Cell d → (I (ir.domainField d)).K) : ir.Assignment I where
  val u i := if h : CellKey.val u i ∈ ir.cellKeys d then castElt (a ⟨_, h⟩) else 0
  pad u i := if h : CellKey.pad u i ∈ ir.cellKeys d then castElt (a ⟨_, h⟩) else 0

variable {ir I}

/-- **The cells' assignment agrees with the zero assignment off the late values' coordinates**:
a pad cell is a coordinate of a late value. -/
theorem padsAgreeOff_ofCells (d : ℕ) (a : ir.Cell d → (I (ir.domainField d)).K) :
    ir.PadsAgreeOff I (ir.ofCells I d a) ⟨0, 0⟩ := by
  intro u i hu
  simp only [ofCells, Pi.zero_apply]
  rw [dif_neg]
  intro h
  obtain ⟨h1, -, h3, h4⟩ := (ir.mem_cellKeys_pad).1 h
  exact hu ⟨h1, ir.isLateOf_isLate h3, h4⟩

variable (ir I)

/-- **The base of a cell of domain `d`**: the set its value lies in by the domain's packing tree,
the packing-tree node of its value (the whole field for a value at no node), the pad space of its
late value, the whole field for a filler input. -/
def cellBase (d : ℕ) : ir.Cell d → Set (I (ir.domainField d)).K
  | ⟨.val v _, _⟩ =>
    match (ir.value v).node with
    | some nr => ((I (ir.domainField d)).node nr.name : Set (I (ir.domainField d)).K)
    | none => Set.univ
  | ⟨.pad v _, _⟩ => ((I (ir.domainField d)).space (ir.value v).padSpace : Set _)
  | ⟨.filler _ _, _⟩ => Set.univ

end

end GordieHowe.RealizedProgram
