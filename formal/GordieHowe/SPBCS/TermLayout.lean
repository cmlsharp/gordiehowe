-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.SPBCS.Term
public import GordieHowe.SPBCS.Bytes

@[expose] public section

/-!
# The site layout of a term with merges

A `SiteLayout` of the merges of every term with merges (`MTerm.siteLayout`), so the byte encoding
of chain inputs (`MergeBytes.bytes`) applies to every term with merges.

* `Site.code`: a tag byte per constructor (`0`, `1` into the subterms of a node, `2` a branch of a
  merge, `3` inside a branch, `4` inside the part), the branch index in unary (`unary`), then the
  code of the site inside; prefix-free (`code_append_inj`).
* `siteList`: the sites in term order, without repetitions (`nodup_siteList`), all of them
  (`mem_siteList`).
-/

namespace GordieHowe.SPBCS

open GordieHowe.QROM

variable {ι : Type}

/-- **A natural number in unary**: `i` zero bytes, then a one. -/
def unary (i : ℕ) : List Byte := List.replicate i 0 ++ [1]

/-- **Unary codes are prefix-free.** -/
theorem unary_append_inj : ∀ {i j : ℕ} {u v : List Byte}, unary i ++ u = unary j ++ v → i = j ∧ u = v
  | 0, 0, u, v, h => ⟨rfl, by simpa [unary] using h⟩
  | 0, j + 1, u, v, h => by simp [unary, List.replicate_succ] at h
  | i + 1, 0, u, v, h => by simp [unary, List.replicate_succ] at h
  | i + 1, j + 1, u, v, h => by
    simp only [unary, List.replicate_succ, List.cons_append, List.append_assoc, List.cons.injEq,
      true_and] at h
    obtain ⟨rfl, rfl⟩ := unary_append_inj (by simpa [unary, List.append_assoc] using h)
    exact ⟨rfl, rfl⟩

namespace MTerm

namespace Site

/-- **The code of a site** (module docstring). -/
def code : {t : MTerm ι} → Site t → List Byte
  | _, left s => 0 :: s.code
  | _, right s => 1 :: s.code
  | _, top i => 2 :: unary i
  | _, inBr i s => 3 :: (unary i ++ s.code)
  | _, inD s => 4 :: s.code

/-- **Site codes are prefix-free.** -/
theorem code_append_inj : {t : MTerm ι} → {s s' : Site t} → {u u' : List Byte} →
    s.code ++ u = s'.code ++ u' → s = s' ∧ u = u'
  | _, left s, left s', _, _, h => by
    simp only [code, List.cons_append, List.cons.injEq, true_and] at h
    obtain ⟨rfl, rfl⟩ := code_append_inj h
    exact ⟨rfl, rfl⟩
  | _, right s, right s', _, _, h => by
    simp only [code, List.cons_append, List.cons.injEq, true_and] at h
    obtain ⟨rfl, rfl⟩ := code_append_inj h
    exact ⟨rfl, rfl⟩
  | _, top i, top i', _, _, h => by
    simp only [code, List.cons_append, List.cons.injEq, true_and] at h
    obtain ⟨hi, rfl⟩ := unary_append_inj h
    exact ⟨congrArg top (Fin.ext hi), rfl⟩
  | _, inBr i s, inBr i' s', _, _, h => by
    simp only [code, List.cons_append, List.cons.injEq, true_and, List.append_assoc] at h
    obtain ⟨hi, h⟩ := unary_append_inj h
    obtain rfl : i = i' := Fin.ext hi
    obtain ⟨rfl, rfl⟩ := code_append_inj h
    exact ⟨rfl, rfl⟩
  | _, inD s, inD s', _, _, h => by
    simp only [code, List.cons_append, List.cons.injEq, true_and] at h
    obtain ⟨rfl, rfl⟩ := code_append_inj h
    exact ⟨rfl, rfl⟩
  | _, left _, right _, _, _, h => by simp [code] at h
  | _, right _, left _, _, _, h => by simp [code] at h
  | _, top _, inBr _ _, _, _, h => by simp [code] at h
  | _, top _, inD _, _, _, h => by simp [code] at h
  | _, inBr _ _, top _, _, _, h => by simp [code] at h
  | _, inBr _ _, inD _, _, _, h => by simp [code] at h
  | _, inD _, top _, _, _, h => by simp [code] at h
  | _, inD _, inBr _ _, _, _, h => by simp [code] at h

end Site

/-- **The sites of a term in term order.** -/
def siteList : (t : MTerm ι) → List (Site t)
  | leaf _ => []
  | node _ a b => (siteList a).map .left ++ (siteList b).map .right
  | merge r br d => (List.finRange r).map .top ++
      ((List.finRange r).flatMap fun i => (siteList (br i)).map (.inBr i)) ++ (siteList d).map .inD

/-- **Every site is listed.** -/
theorem mem_siteList : {t : MTerm ι} → (s : Site t) → s ∈ t.siteList
  | _, .left s => List.mem_append_left _ (List.mem_map_of_mem (mem_siteList s))
  | _, .right s => List.mem_append_right _ (List.mem_map_of_mem (mem_siteList s))
  | _, .top i => List.mem_append_left _ (List.mem_append_left _
      (List.mem_map_of_mem (List.mem_finRange i)))
  | _, .inBr i s => List.mem_append_left _ (List.mem_append_right _
      (List.mem_flatMap.2 ⟨i, List.mem_finRange i, List.mem_map_of_mem (mem_siteList s)⟩))
  | _, .inD s => List.mem_append_right _ (List.mem_map_of_mem (mem_siteList s))

theorem inBr_injective {r : ℕ} {br : Fin r → MTerm ι} {d : MTerm ι} (i : Fin r) :
    Function.Injective (Site.inBr (br := br) (d := d) i) := fun _ _ h => by
  cases h
  rfl

/-- **No site is listed twice.** -/
theorem nodup_siteList : (t : MTerm ι) → t.siteList.Nodup
  | leaf _ => List.nodup_nil
  | node _ a b => by
    refine List.Nodup.append ((nodup_siteList a).map fun _ _ h => by cases h; rfl)
      ((nodup_siteList b).map fun _ _ h => by cases h; rfl) ?_
    intro x hx hy
    obtain ⟨_, -, rfl⟩ := List.mem_map.1 hx
    obtain ⟨_, -, hq⟩ := List.mem_map.1 hy
    cases hq
  | merge r br d => by
    have hbr : ((List.finRange r).flatMap fun i => (siteList (br i)).map (Site.inBr (d := d) i)).Nodup := by
      refine List.nodup_flatMap.2 ⟨fun i _ => (nodup_siteList (br i)).map (inBr_injective i), ?_⟩
      refine (List.nodup_finRange r).pairwise_of_forall_ne fun i _ j _ hij x hx hy => ?_
      obtain ⟨_, -, rfl⟩ := List.mem_map.1 hx
      obtain ⟨_, -, hq⟩ := List.mem_map.1 hy
      cases hq
      exact hij rfl
    refine List.Nodup.append (List.Nodup.append ((List.nodup_finRange r).map fun _ _ h => by
      cases h; rfl) hbr ?_) ((nodup_siteList d).map fun _ _ h => by cases h; rfl) ?_
    · intro x hx hy
      obtain ⟨_, -, rfl⟩ := List.mem_map.1 hx
      obtain ⟨_, -, hq⟩ := List.mem_flatMap.1 hy
      obtain ⟨_, -, hq⟩ := List.mem_map.1 hq
      cases hq
    · intro x hx hy
      obtain ⟨_, -, rfl⟩ := List.mem_map.1 hy
      rcases List.mem_append.1 hx with hx | hx
      · obtain ⟨_, -, hq⟩ := List.mem_map.1 hx
        cases hq
      · obtain ⟨_, -, hq⟩ := List.mem_flatMap.1 hx
        obtain ⟨_, -, hq⟩ := List.mem_map.1 hq
        cases hq

/-- **The site layout of a term with merges** (module docstring). -/
def siteLayout (t : MTerm ι) : SiteLayout t.merges where
  sites := t.siteList
  nodup := t.nodup_siteList
  mem_sites := mem_siteList
  code := Site.code
  code_append_inj := Site.code_append_inj

end MTerm

end GordieHowe.SPBCS
