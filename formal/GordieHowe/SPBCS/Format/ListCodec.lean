-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.SPBCS.Format.Codec

@[expose] public section

/-!
# A codec for lists

`Codec.list C` writes a list of values as one continuation byte `1` before each value's bytes
and a final `0` (`ser`), and reads them back (`parse`, with fuel the input's length: every value
consumes at least its continuation byte). It is self-delimiting, so the statement writes of a
statement holding a list (a ring of keys) are prefix-free (`Codec.prefixFree`).
-/

namespace GordieHowe.SPBCS

open GordieHowe.QROM

namespace Codec

variable {A : Type}

/-- Read a list off the front of `s` with `fuel` steps: `0` ends the list, `1` precedes a value. -/
def parseList (C : Codec A) : ℕ → List Byte → Option (List A × List Byte)
  | 0, _ => none
  | _ + 1, [] => none
  | fuel + 1, b :: s =>
    if b = 0 then some ([], s)
    else if b = 1 then
      (C.parse s).bind fun p => (parseList C fuel p.2).map fun q => (p.1 :: q.1, q.2)
    else none

/-- The bytes of a list: `1 ‖ ser a` for every value, then `0`. -/
def serList (C : Codec A) : List A → List Byte
  | [] => [0]
  | a :: l => 1 :: (C.ser a ++ serList C l)

theorem length_serList_ge (C : Codec A) (l : List A) : l.length + 1 ≤ (C.serList l).length := by
  induction l with
  | nil => simp [serList]
  | cons a l ih =>
    simp only [serList, List.length_cons, List.length_append]
    omega

theorem parseList_serList (C : Codec A) :
    ∀ (l : List A) (t : List Byte) (fuel : ℕ), (C.serList l).length ≤ fuel →
      C.parseList fuel (C.serList l ++ t) = some (l, t)
  | [], t, fuel, h => by
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp [serList] at h; omega⟩
    simp [serList, parseList]
  | a :: l, t, fuel, h => by
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp [serList] at h; omega⟩
    have hf : (C.serList l).length ≤ f := by
      simp only [serList, List.length_cons, List.length_append] at h
      omega
    simp only [serList, List.cons_append, parseList, one_ne_zero, ite_false, ite_true,
      List.append_assoc, C.parse_ser, Option.bind_some, parseList_serList C l t f hf,
      Option.map_some]

theorem serList_of_parseList (C : Codec A) :
    ∀ (fuel : ℕ) {s : List Byte} {l : List A} {t : List Byte},
      C.parseList fuel s = some (l, t) → s = C.serList l ++ t
  | 0, _, _, _, h => by simp [parseList] at h
  | f + 1, [], _, _, h => by simp [parseList] at h
  | f + 1, b :: s, l, t, h => by
    simp only [parseList] at h
    split_ifs at h with h0 h1
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some_inj.1 h)
      simp [serList, h0]
    · obtain ⟨⟨a, u⟩, ha, hb⟩ := Option.bind_eq_some_iff.1 h
      obtain ⟨⟨l', v⟩, hl, he⟩ := Option.map_eq_some_iff.1 hb
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
      have hu : u = C.serList l' ++ v := serList_of_parseList C f hl
      rw [C.ser_parse ha, hu]
      simp [serList, h1]

/-- **The codec of lists**: `1 ‖ ser a` for every value, then `0`. -/
def list (C : Codec A) : Codec (List A) where
  ser := C.serList
  parse s := C.parseList s.length s
  parse_ser l t := C.parseList_serList l t _ (by simp)
  ser_parse {_ _ _} h := C.serList_of_parseList _ h

theorem length_ser_list (C : Codec A) {m : ℕ} (hm : ∀ a, (C.ser a).length = m) (l : List A) :
    ((list C).ser l).length = l.length * (m + 1) + 1 := by
  change (C.serList l).length = _
  induction l with
  | nil => simp [serList]
  | cons a l ih =>
    simp only [serList, List.length_cons, List.length_append, hm, ih]
    ring

end Codec

end GordieHowe.SPBCS
