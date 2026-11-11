-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.Realizations.Circuit.Emit
public import GordieHowe.Language.RealizedProgram.Interval
public import GordieHoweNative.Language.Realizations.Circuit.OpRows

@[expose] public section

/-!
# GordieHowe: the rows of a circuit's linear operators

A GKR circuit expands a linear operator of an affine term or of a `kApply` node
(`lib/gordiehowe/expr.h`, `expand_operator`) into rows of constant codes over its operand's
coordinates. This file holds those rows and their lemmas, by the operator's printed form:

* **Rows** (`GordieHowe.RealizedProgram.rowEval`): a row of `(column, code)` entries, read as the
  sum of the decoded codes times the operand's coordinates.
* **Constant codes** (`GordieHowe.RealizedProgram.constCodes?`): a constant value of the circuit's
  field gives its entries' codes, which decode to the reader's values (`constCodes?_read`).
* **Named operators** (`GordieHowe.RealizedProgram.emitRows`, `linear.h`'s `emit`): `sum`,
  `fromDigits`, `constDiagonal` and `batched` of these, the rows lemma `emitRows_sound` proved once
  per kind; per block of the operand the rows shifted by the block (`shiftRows`).
* **Sparse rows** (`GordieHowe.RealizedProgram.coefCode`): each printed coefficient a constant's
  code or the code of an entry of a constant of the circuit's field.
* **Lists** (`GordieHowe.RealizedProgram.OpList`): a list as a positional tree (`PTree.ofList`), split
  by parity, by blocks and transposed, with Horner evaluation and code powers, which the staged
  transforms read.

The definitions are in `GordieHoweNative/Language/Realizations/Circuit/OpRows.lean`
(the compiled library `GordieHoweNative`); this module has their lemmas.
-/

namespace GordieHowe.RealizedProgram

open GordieHowe.GKR.Fold (CodeArith)

namespace OpList

/-! ## Lists split by parity -/

section Parity

variable {α β : Type*}

theorem evenPart_map (f : α → β) : ∀ l : List α, evenPart (l.map f) = (evenPart l).map f
  | [] => rfl
  | [_] => rfl
  | _ :: _ :: l => by simp [evenPart, evenPart_map f l]

theorem oddPart_map (f : α → β) : ∀ l : List α, oddPart (l.map f) = (oddPart l).map f
  | [] => rfl
  | [_] => rfl
  | _ :: _ :: l => by simp [oddPart, oddPart_map f l]

theorem length_evenPart : ∀ l : List α, (evenPart l).length = (l.length + 1) / 2
  | [] => by simp [evenPart]
  | [_] => by simp [evenPart]
  | _ :: _ :: l => by
    simp only [evenPart, List.length_cons, length_evenPart l]
    omega

theorem length_oddPart : ∀ l : List α, (oddPart l).length = l.length / 2
  | [] => by simp [oddPart]
  | [_] => by simp [oddPart]
  | _ :: _ :: l => by
    simp only [oddPart, List.length_cons, length_oddPart l]
    omega

theorem getD_evenPart (d : α) : ∀ (l : List α) (i : ℕ), (evenPart l).getD i d = l.getD (2 * i) d
  | [], _ => by simp [evenPart]
  | [_], 0 => rfl
  | [_], i + 1 => by simp [evenPart]
  | _ :: _ :: _, 0 => rfl
  | _ :: _ :: l, i + 1 => by
    rw [show 2 * (i + 1) = 2 * i + 1 + 1 by ring]
    simp only [evenPart, List.getD_cons_succ]
    exact getD_evenPart d l i

theorem getD_oddPart (d : α) :
    ∀ (l : List α) (i : ℕ), (oddPart l).getD i d = l.getD (2 * i + 1) d
  | [], _ => by simp [oddPart]
  | [_], _ => by simp [oddPart]
  | _ :: _ :: _, 0 => rfl
  | _ :: _ :: l, i + 1 => by
    rw [show 2 * (i + 1) + 1 = 2 * i + 1 + 1 + 1 by ring]
    simp only [oddPart, List.getD_cons_succ]
    exact getD_oddPart d l i

/-- The even entries of a list of pairs flattened are the first members. -/
theorem evenPart_flatMap_pair (f g : α → β) :
    ∀ l : List α, evenPart (l.flatMap fun a => [f a, g a]) = l.map f
  | [] => rfl
  | a :: l => by
    simp only [List.flatMap_cons, List.cons_append, List.nil_append, evenPart, List.map_cons]
    rw [evenPart_flatMap_pair f g l]

/-- The odd entries of a list of pairs flattened are the second members. -/
theorem oddPart_flatMap_pair (f g : α → β) :
    ∀ l : List α, oddPart (l.flatMap fun a => [f a, g a]) = l.map g
  | [] => rfl
  | a :: l => by
    simp only [List.flatMap_cons, List.cons_append, List.nil_append, oddPart, List.map_cons]
    rw [oddPart_flatMap_pair f g l]

theorem length_flatMap_pair (f g : α → β) :
    ∀ l : List α, (l.flatMap fun a => [f a, g a]).length = 2 * l.length
  | [] => rfl
  | a :: l => by
    simp only [List.flatMap_cons, List.cons_append, List.nil_append, List.length_cons,
      length_flatMap_pair f g l]
    ring

/-- **A list split `j` times by parity**: `2^j` parts, part `g` holding the entries at the
positions `p` with `br_j(g) = p mod 2^j` (the parts of the radix-2 decimation in time). -/
def splitParity : ℕ → List α → List (List α)
  | 0, l => [l]
  | j + 1, l => (splitParity j l).flatMap fun P => [evenPart P, oddPart P]

theorem splitParity_map (f : α → β) :
    ∀ (j : ℕ) (l : List α), splitParity j (l.map f) = (splitParity j l).map (List.map f)
  | 0, _ => rfl
  | j + 1, l => by
    simp only [splitParity, splitParity_map f j l, List.flatMap_map, List.map_flatMap,
      List.map_cons, List.map_nil, evenPart_map, oddPart_map]

theorem length_splitParity : ∀ (j : ℕ) (l : List α), (splitParity j l).length = 2 ^ j
  | 0, _ => rfl
  | j + 1, l => by
    rw [splitParity, length_flatMap_pair, length_splitParity j l, pow_succ, mul_comm]

/-- Every part of a list of length `2^j · L` split `j` times has length `L`. -/
theorem length_of_mem_splitParity :
    ∀ (j : ℕ) {l : List α} {L : ℕ}, l.length = 2 ^ j * L → ∀ P ∈ splitParity j l, P.length = L
  | 0, l, L, h, P, hP => by
    simp only [splitParity, List.mem_singleton] at hP
    subst hP
    simpa using h
  | j + 1, l, L, h, P, hP => by
    simp only [splitParity, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hP
    obtain ⟨Q, hQ, hPQ⟩ := hP
    have hQ2 := length_of_mem_splitParity j (L := 2 * L) (by rw [h, pow_succ]; ring) Q hQ
    rcases hPQ with rfl | rfl
    · rw [length_evenPart, hQ2]
      omega
    · rw [length_oddPart, hQ2]
      omega

end Parity

end OpList

open OpList

/-! ## Horner evaluation and code powers -/

section Horner

variable {F : Type*} [CommRing F]

/-- **The value at `r` of the polynomial with coefficient list `l`**, constant term first, by
Horner's rule. -/
def hornerEval : List F → F → F
  | [], _ => 0
  | a :: l, r => a + r * hornerEval l r

theorem hornerEval_singleton (a r : F) : hornerEval [a] r = a := by
  simp [hornerEval]

theorem hornerEval_append (l₁ l₂ : List F) (r : F) :
    hornerEval (l₁ ++ l₂) r = hornerEval l₁ r + r ^ l₁.length * hornerEval l₂ r := by
  induction l₁ with
  | nil => simp [hornerEval]
  | cons a l ih =>
    simp only [List.cons_append, hornerEval, ih, List.length_cons, pow_succ]
    ring

/-- **The value splits by parity**: `p(r) = p_even(r²) + r · p_odd(r²)`. -/
theorem hornerEval_parity : ∀ (l : List F) (r : F),
    hornerEval l r = hornerEval (evenPart l) (r ^ 2) + r * hornerEval (oddPart l) (r ^ 2)
  | [], _ => by simp [hornerEval, evenPart, oddPart]
  | [_], _ => by simp [hornerEval, evenPart, oddPart]
  | x :: y :: l, r => by
    simp only [hornerEval, evenPart, oddPart]
    rw [hornerEval_parity l r]
    ring

/-- The value as a sum of monomials. -/
theorem hornerEval_eq_sum (l : List F) (r : F) :
    hornerEval l r = ∑ i ∈ Finset.range l.length, l.getD i 0 * r ^ i := by
  induction l with
  | nil => simp [hornerEval]
  | cons a l ih =>
    rw [hornerEval, ih, List.length_cons, Finset.sum_range_succ', Finset.mul_sum]
    simp only [List.getD_cons_succ, List.getD_cons_zero, pow_zero, mul_one, pow_succ]
    rw [add_comm]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    ring

/-- **The upper half of a butterfly row**: `u + c·v` per offset. -/
theorem hornerEval_zipWith_add (c r : F) :
    ∀ (lo hi : List F), lo.length = hi.length →
      hornerEval (List.zipWith (fun u v => u + c * v) lo hi) r =
        hornerEval lo r + c * hornerEval hi r
  | [], [], _ => by simp [hornerEval]
  | u :: lo, v :: hi, h => by
    simp only [List.zipWith_cons_cons, hornerEval]
    rw [hornerEval_zipWith_add c r lo hi (by simpa using h)]
    ring
  | [], _ :: _, h | _ :: _, [], h => by simp at h

/-- **The lower half of a butterfly row**: `u − c·v` per offset. -/
theorem hornerEval_zipWith_sub (c r : F) :
    ∀ (lo hi : List F), lo.length = hi.length →
      hornerEval (List.zipWith (fun u v => u - c * v) lo hi) r =
        hornerEval lo r - c * hornerEval hi r
  | [], [], _ => by simp [hornerEval]
  | u :: lo, v :: hi, h => by
    simp only [List.zipWith_cons_cons, hornerEval]
    rw [hornerEval_zipWith_sub c r lo hi (by simpa using h)]
    ring
  | [], _ :: _, h | _ :: _, [], h => by simp at h

/-- **The twist**: coordinate `i` scaled by `c·ψ^i`. -/
def twistV (c ψ : F) : List F → List F
  | [] => []
  | x :: l => c * x :: twistV (c * ψ) ψ l

theorem hornerEval_twistV (ψ r : F) :
    ∀ (c : F) (l : List F), hornerEval (twistV c ψ l) r = c * hornerEval l (ψ * r)
  | _, [] => by simp [twistV, hornerEval]
  | c, x :: l => by
    simp only [twistV, hornerEval]
    rw [hornerEval_twistV ψ r (c * ψ) l]
    ring

end Horner

/-! ## Powers by codes -/

section Codes

variable {F : Type*} [CommRing F] {κc : ℕ → F}

theorem codePowF_hom {ar : CodeArith} (hA : ar.Hom κc) :
    ∀ (fuel c e : ℕ), e ≤ fuel → κc (codePowF ar fuel c e) = κc c ^ e
  | 0, c, e, he => by
    obtain rfl : e = 0 := by omega
    simp [codePowF, hA.one]
  | fuel + 1, c, e, he => by
    simp only [codePowF, Bool.cond_eq_ite, Nat.beq_eq]
    split_ifs with h0 h1
    · subst h0
      simp [hA.one]
    · rw [hA.mul, codePowF_hom hA fuel _ _ (by omega), hA.mul, ← pow_two, ← pow_mul, ← pow_succ]
      congr 1
      omega
    · rw [codePowF_hom hA fuel _ _ (by omega), hA.mul, ← pow_two, ← pow_mul]
      congr 1
      omega

theorem codePow_hom {ar : CodeArith} (hA : ar.Hom κc) (c e : ℕ) :
    κc (codePow ar c e) = κc c ^ e :=
  codePowF_hom hA e c e le_rfl

theorem map_powList {ar : CodeArith} (hA : ar.Hom κc) (c : ℕ) :
    ∀ (L w : ℕ), (powList ar c L w).map κc = (List.range L).map fun j => κc w * κc c ^ j
  | 0, _ => rfl
  | L + 1, w => by
    rw [powList, List.range_succ_eq_map, List.map_cons, List.map_cons, map_powList hA c L,
      List.map_map, pow_zero, mul_one]
    congr 1
    refine List.map_congr_left fun j _ => ?_
    simp only [Function.comp, hA.mul, pow_succ]
    ring

end Codes

namespace OpList

/-! ## Lists of lists -/

section Matrix

variable {α β : Type*}

/-- **The transpose** of a list of rows of width `w`: `w` columns. -/
def transposeW (w : ℕ) : List (List α) → List (List α)
  | [] => List.replicate w []
  | r :: M => List.zipWith List.cons r (transposeW w M)

theorem transposeW_map (f : α → β) (w : ℕ) :
    ∀ M : List (List α), transposeW w (M.map (List.map f)) = (transposeW w M).map (List.map f)
  | [] => by simp [transposeW]
  | r :: M => by
    simp only [List.map_cons, transposeW, transposeW_map f w M, List.zipWith_map,
      List.map_zipWith, List.map_cons]

theorem length_transposeW (w : ℕ) :
    ∀ M : List (List α), (∀ r ∈ M, r.length = w) → (transposeW w M).length = w
  | [], _ => by simp [transposeW]
  | r :: M, h => by
    simp only [transposeW, List.length_zipWith, h r (by simp),
      length_transposeW w M fun r' hr' => h r' (by simp [hr']), min_self]

theorem transposeW_succ_zipWith (h : ℕ) :
    ∀ (r : List α) (T : List (List α)), r.length = T.length →
      transposeW (h + 1) (List.zipWith List.cons r T) = r :: transposeW h T
  | [], [], _ => by simp [transposeW, List.replicate_succ]
  | a :: r, t :: T, hl => by
    simp only [List.zipWith_cons_cons, transposeW]
    rw [transposeW_succ_zipWith h r T (by simpa using hl)]
    rfl
  | [], _ :: _, hl | _ :: _, [], hl => by simp at hl

/-- **The transpose of the transpose** of rows of one width is the list itself. -/
theorem transposeW_transposeW (w : ℕ) :
    ∀ M : List (List α), (∀ r ∈ M, r.length = w) → transposeW M.length (transposeW w M) = M
  | [], _ => by
    cases w with
    | zero => rfl
    | succ w => simp [transposeW, List.replicate_succ]
  | r :: M, h => by
    have hM : ∀ r' ∈ M, r'.length = w := fun r' hr' => h r' (by simp [hr'])
    simp only [transposeW, List.length_cons]
    rw [transposeW_succ_zipWith _ r _ (by rw [h r (by simp), length_transposeW w M hM]),
      transposeW_transposeW w M hM]

theorem zipWith_map_map_self {γ δ : Type*} (g : β → γ → δ) (f₁ : α → β) (f₂ : α → γ) :
    ∀ l : List α, List.zipWith g (l.map f₁) (l.map f₂) = l.map fun a => g (f₁ a) (f₂ a)
  | [] => rfl
  | a :: l => by simp [zipWith_map_map_self g f₁ f₂ l]

/-- Entry `i` of blocks of width `w` concatenated is entry `i mod w` of block `i / w`. -/
theorem getD_flatten_of_length {w : ℕ} (hw : 0 < w) (d : α) :
    ∀ (B : List (List α)), (∀ b ∈ B, b.length = w) →
      ∀ i, B.flatten.getD i d = (B.getD (i / w) []).getD (i % w) d
  | [], _, i => by simp
  | b :: B, hB, i => by
    have hb := hB b (by simp)
    rw [List.flatten_cons]
    by_cases hi : i < w
    · rw [List.getD_append _ _ _ _ (hb ▸ hi), Nat.div_eq_of_lt hi, Nat.mod_eq_of_lt hi]
      rfl
    · have e1 : i / w = (i - w) / w + 1 := Nat.div_eq_sub_div hw (by omega)
      have e2 : i % w = (i - w) % w := Nat.mod_eq_sub_mod (by omega)
      rw [List.getD_append_right _ _ _ _ (by omega), hb,
        getD_flatten_of_length hw d B (fun b' hb' => hB b' (by simp [hb'])), e1, e2]
      rfl

theorem getD_of_forall₂ {R : α → β → Prop} {d₁ : α} {d₂ : β} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → ∀ {i : ℕ}, i < l₁.length →
      R (l₁.getD i d₁) (l₂.getD i d₂)
  | _, _, .nil, _, hi => by simp at hi
  | _, _, .cons h _, 0, _ => h
  | _, _, .cons _ hl, i + 1, hi => getD_of_forall₂ hl (by simpa using hi)

theorem map_eq_map_of_forall₂ {γ : Type*} {R : α → β → Prop} (f : α → γ) (g : β → γ)
    (H : ∀ a b, R a b → f a = g b) :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → l₁.map f = l₂.map g
  | _, _, .nil => rfl
  | _, _, .cons h hl => by
    rw [List.map_cons, List.map_cons, H _ _ h, map_eq_map_of_forall₂ f g H hl]

/-- **Pairs related entry by entry** to the entries of a zip: their images are the zip's images. -/
theorem map_zip_of_forall₂ {γ δ δ' ε : Type*} {R : α × β → γ → Prop} (F : δ → δ' → ε)
    (f : α → δ) (g : β → δ') (h : γ → ε) (H : ∀ q p, R q p → h p = F (f q.1) (g q.2)) :
    ∀ (l₁ : List α) (l₂ : List β) {ps : List γ}, List.Forall₂ R (l₁.zip l₂) ps →
      ps.map h = List.zipWith F (l₁.map f) (l₂.map g)
  | [], _, _, hF => by cases hF; rfl
  | _ :: _, [], _, hF => by cases hF; rfl
  | a :: l₁, b :: l₂, _, hF => by
    simp only [List.zip_cons_cons] at hF
    cases hF with
    | cons hq hr =>
      rw [List.map_cons, H _ _ hq, map_zip_of_forall₂ F f g h H l₁ l₂ hr]
      rfl

end Matrix

end OpList

namespace OpList

/-! ## Helpers on entries -/

section Entries

variable {α β : Type*}

theorem getD_map_of_lt (f : α → β) {l : List α} {i : ℕ} (hi : i < l.length) (d : β) (d' : α) :
    (l.map f).getD i d = f (l.getD i d') := by
  simp [List.getD_eq_getElem?_getD, hi]

theorem getD_take_of_lt {l : List α} {n t : ℕ} (ht : t < n) (d : α) :
    (l.take n).getD t d = l.getD t d := by
  simp [List.getD_eq_getElem?_getD, ht]

theorem getD_drop' (l : List α) (n j : ℕ) (d : α) : (l.drop n).getD j d = l.getD (n + j) d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_drop]

theorem exists_of_mem_forall₂ {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → ∀ a ∈ l₁, ∃ b, R a b
  | _, _, .nil, _, ha => by simp at ha
  | _, _, .cons h hl, a, ha => by
    rcases List.mem_cons.1 ha with rfl | ha
    · exact ⟨_, h⟩
    · exact exists_of_mem_forall₂ hl a ha

/-- **Chunks of a list whose length is a multiple of `n`**: each has length `n`, there are
`length / n` of them, and entry `t` of chunk `b` is entry `b·n + t` of the list. -/
theorem chunksF_spec {n : ℕ} (hn : 0 < n) :
    ∀ (fuel : ℕ) (l : List α), n ∣ l.length → l.length ≤ fuel * n →
      (∀ c ∈ chunksF n fuel l, c.length = n) ∧ (chunksF n fuel l).length = l.length / n ∧
      ∀ (b t : ℕ) (d : α), t < n → b < l.length / n →
        ((chunksF n fuel l).getD b []).getD t d = l.getD (b * n + t) d
  | fuel, [], _, _ => by
    cases fuel <;> exact ⟨by simp [chunksF], by simp [chunksF], fun b t d _ hb => by simp at hb⟩
  | 0, _ :: _, _, hle => by simp at hle
  | fuel + 1, x :: xs, hd, hle => by
    have hnl : n ≤ (x :: xs).length := Nat.le_of_dvd (by simp) hd
    have hdl : ((x :: xs).drop n).length = (x :: xs).length - n := List.length_drop ..
    obtain ⟨hc, hcl, hcg⟩ := chunksF_spec hn fuel ((x :: xs).drop n)
      (by rw [hdl]; exact Nat.dvd_sub hd (dvd_refl n))
      (by rw [hdl]; rw [add_mul, one_mul] at hle; omega)
    have hdiv : (x :: xs).length / n = ((x :: xs).length - n) / n + 1 :=
      Nat.div_eq_sub_div hn hnl
    refine ⟨fun c hc' => ?_, ?_, fun b t d ht hb => ?_⟩
    · rw [chunksF, List.mem_cons] at hc'
      rcases hc' with rfl | hc'
      · simpa using hnl
      · exact hc c hc'
    · rw [chunksF, List.length_cons, hcl, hdl, hdiv]
    · rw [chunksF]
      cases b with
      | zero =>
        rw [List.getD_cons_zero, getD_take_of_lt ht, zero_mul, zero_add]
      | succ b =>
        rw [List.getD_cons_succ, hcg b t d ht (by rw [hdl]; omega), getD_drop']
        congr 1
        ring

theorem length_flatten_of_length {w : ℕ} :
    ∀ B : List (List α), (∀ b ∈ B, b.length = w) → B.flatten.length = B.length * w
  | [], _ => by simp
  | b :: B, h => by
    rw [List.flatten_cons, List.length_append, h b (by simp),
      length_flatten_of_length B fun b' hb' => h b' (by simp [hb']), List.length_cons]
    ring

theorem exists_of_mem_forall₂_right {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → ∀ b ∈ l₂, ∃ a, R a b
  | _, _, .nil, _, hb => by simp at hb
  | _, _, .cons h hl, b, hb => by
    rcases List.mem_cons.1 hb with rfl | hb
    · exact ⟨_, h⟩
    · exact exists_of_mem_forall₂_right hl b hb

end Entries

end OpList

/-! ## A list as a trie -/

section ListTree

variable {α : Type}

namespace PNode

theorem getH_nil [Inhabited α] (h i : ℕ) : (nil : PNode α).getH h i = default := by
  cases h <;> rfl

/-- **Position `i` of a row of subtrees of height `h`.** -/
def getL [Inhabited α] (h : ℕ) (ts : List (PNode α)) (i : ℕ) : α :=
  (ts.getD (i / 2 ^ h) nil).getH h (i % 2 ^ h)

theorem getH_node [Inhabited α] (l r : PNode α) (h i : ℕ) :
    (node l r).getH (h + 1) i = if i < 2 ^ h then l.getH h i else r.getH h (i - 2 ^ h) := by
  simp only [getH]
  cases hb : Nat.blt i (2 ^ h)
  · have hh : ¬i < 2 ^ h := fun h' => by simp [Nat.blt_eq.mpr h'] at hb
    simp [hh]
  · have hh : i < 2 ^ h := Nat.blt_eq.mp hb
    simp [hh]

theorem length_pairUp : ∀ ts : List (PNode α), (pairUp ts).length = (ts.length + 1) / 2
  | [] => by simp [pairUp]
  | [_] => by simp [pairUp]
  | _ :: _ :: ts => by
    simp only [pairUp, List.length_cons, length_pairUp ts]
    omega

theorem getL_pairUp [Inhabited α] (h : ℕ) :
    ∀ (ts : List (PNode α)) (i : ℕ), getL (h + 1) (pairUp ts) i = getL h ts i
  | [], i => by simp [pairUp, getL, getH_nil]
  | [a], i => by
    have hP : 0 < 2 ^ h := Nat.two_pow_pos h
    unfold getL
    rw [Nat.pow_succ]
    by_cases hi : i < 2 ^ h * 2
    · rw [Nat.div_eq_of_lt hi, Nat.mod_eq_of_lt hi]
      simp only [pairUp, List.getD_cons_zero, getH_node]
      by_cases hl : i < 2 ^ h
      · simp only [hl, ↓reduceIte]
        rw [Nat.div_eq_of_lt hl, Nat.mod_eq_of_lt hl]
        rfl
      · simp only [hl, ↓reduceIte]
        rw [getH_nil]
        have h1 : i / 2 ^ h = 1 := by
          exact Nat.div_eq_of_lt_le (by omega) (by omega)
        rw [h1]
        simp [getH_nil]
    · have h1 : 1 ≤ i / (2 ^ h * 2) := (Nat.le_div_iff_mul_le (by positivity)).2 (by omega)
      have h2 : 1 ≤ i / 2 ^ h := (Nat.le_div_iff_mul_le hP).2 (by omega)
      simp only [pairUp]
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega),
        List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)]
      simp [getH_nil]
  | a :: b :: rest, i => by
    have hP : 0 < 2 ^ h := Nat.two_pow_pos h
    have ih := getL_pairUp h rest
    unfold getL at ih ⊢
    rw [Nat.pow_succ] at ih ⊢
    by_cases hi : i < 2 ^ h * 2
    · rw [Nat.div_eq_of_lt hi, Nat.mod_eq_of_lt hi]
      simp only [pairUp, List.getD_cons_zero, getH_node]
      by_cases hl : i < 2 ^ h
      · simp only [hl, ↓reduceIte]
        rw [Nat.div_eq_of_lt hl, Nat.mod_eq_of_lt hl]
        rfl
      · simp only [hl, ↓reduceIte]
        have h1 : i / 2 ^ h = 1 := by
          exact Nat.div_eq_of_lt_le (by omega) (by omega)
        have h2 : i % 2 ^ h = i - 2 ^ h := by
          rw [Nat.mod_eq_sub_mul_div, h1, Nat.mul_one]
        rw [h1, h2]
        rfl
    · obtain ⟨j, rfl⟩ : ∃ j, i = j + 2 ^ h * 2 := ⟨i - 2 ^ h * 2, by omega⟩
      have e1 : (j + 2 ^ h * 2) / (2 ^ h * 2) = j / (2 ^ h * 2) + 1 := by
        rw [Nat.add_div_right _ (by positivity)]
      have e2 : (j + 2 ^ h * 2) % (2 ^ h * 2) = j % (2 ^ h * 2) := Nat.add_mod_right _ _
      have e3 : (j + 2 ^ h * 2) / 2 ^ h = j / 2 ^ h + 2 := by
        rw [show j + 2 ^ h * 2 = j + 2 * 2 ^ h by ring, Nat.add_mul_div_right _ _ hP]
      have e4 : (j + 2 ^ h * 2) % 2 ^ h = j % 2 ^ h := by
        rw [show j + 2 ^ h * 2 = j + 2 * 2 ^ h by ring, Nat.add_mul_mod_self_right]
      rw [e1, e2, e3, e4]
      simp only [pairUp, List.getD_cons_succ]
      exact ih j

theorem getH_build [Inhabited α] :
    ∀ (f h : ℕ) (ts : List (PNode α)) (n : ℕ), ts.length ≤ f + 1 → n ≤ ts.length * 2 ^ h →
      ∀ i < n, (build f h ts).1.getH (build f h ts).2 i = getL h ts i
  | _, h, [], n, _, hn, i, hi => by simp at hn; omega
  | _, h, [t], n, _, hn, i, hi => by
    have hi' : i < 2 ^ h := by simp at hn; omega
    simp only [build, getL, Nat.div_eq_of_lt hi', Nat.mod_eq_of_lt hi', List.getD_cons_zero]
  | 0, h, _ :: _ :: _, n, hf, _, i, hi => by simp at hf
  | f + 1, h, a :: b :: ts, n, hf, hn, i, hi => by
    simp only [build]
    have hq : ts.length + 1 + 1 ≤ (ts.length + 1 + 1 + 1) / 2 * 2 := by omega
    rw [getH_build f (h + 1) _ n (by rw [length_pairUp]; simp only [List.length_cons] at hf ⊢; omega)
      (by
        rw [length_pairUp, Nat.pow_succ]
        simp only [List.length_cons] at hn ⊢
        calc n ≤ (ts.length + 1 + 1) * 2 ^ h := hn
          _ ≤ ((ts.length + 1 + 1 + 1) / 2 * 2) * 2 ^ h := Nat.mul_le_mul_right _ hq
          _ = _ := by ring) i hi,
      getL_pairUp]

end PNode

theorem PTree.get_ofList [Inhabited α] (l : List α) {k : ℕ} (hk : k < l.length) :
    (PTree.ofList l).get k = l.getD k default := by
  unfold PTree.ofList PTree.get
  simp only
  rw [PNode.getH_build l.length 0 (l.map .leaf) l.length (by simp) (by simp) k hk]
  simp only [PNode.getL, pow_zero, Nat.div_one, Nat.mod_one]
  simp [List.getD_eq_getElem?_getD, hk, PNode.getH]

/-! ## Reading a list by an index map -/

theorem takeL_eq {n L : ℕ} {l : List α} (h : l.length = L) : takeL n L l = l.take n := by
  unfold takeL
  cases hb : Nat.beq n L
  · rfl
  · rw [Nat.beq_eq] at hb
    simp [hb, ← h]

theorem flattenL_eq : ∀ ls : List (List α), flattenL ls = ls.flatten
  | [] => rfl
  | [_] => by simp [flattenL]
  | _ :: _ :: _ => rfl

theorem pickRun_eq [Inhabited α] {xs : List α} {T : PTree α} {s : ℕ} {d : ℤ} {c : ℕ}
    (hT : ∀ k < xs.length, T.get k = xs.getD k default)
    (hr : IndexMap.inRange [(s, d, c)] xs.length = true) :
    pickRun xs xs.length T s d c =
      (List.range c).map fun t : ℕ => xs.getD ((s : ℤ) + d * t).toNat default := by
  have hlt : ∀ t < c, ((s : ℤ) + d * t).toNat < xs.length := fun t ht => by
    have := IndexMap.entry_lt_of_inRange hr (i := t) (by simp [IndexMap.size, ht])
    simpa [IndexMap.entry, ht] using this
  have hgen : ((List.range c).map fun t : ℕ => T.get ((s : ℤ) + d * t).toNat) =
      (List.range c).map fun t : ℕ => xs.getD ((s : ℤ) + d * t).toNat default :=
    List.map_congr_left fun t ht => hT _ (hlt t (List.mem_range.1 ht))
  unfold pickRun
  by_cases h1 : d = 1 ∧ s ≤ c
  · obtain ⟨rfl, hsc'⟩ := h1
    have hdrop : (xs.drop s).take c = (List.range c).map
        fun t : ℕ => xs.getD ((s : ℤ) + 1 * t).toNat default := by
      have hsc : c = 0 ∨ s + c ≤ xs.length := by
        rcases Nat.eq_zero_or_pos c with h0 | h0
        · exact .inl h0
        · have := hlt (c - 1) (by omega)
          right
          have h' : ((s : ℤ) + 1 * ((c - 1 : ℕ) : ℤ)).toNat = s + (c - 1) := by omega
          omega
      refine List.ext_getElem ?_ fun t h₁ h₂ => ?_
      · simp only [List.length_take, List.length_drop, List.length_map, List.length_range]
        omega
      · simp only [List.getElem_take, List.getElem_drop, List.getElem_map, List.getElem_range]
        have h' : ((s : ℤ) + 1 * (t : ℤ)).toNat = s + t := by omega
        rw [h', List.getD_eq_getElem]
    have hb : ((1 : ℤ) == 1 && Nat.ble s c) = true := by simpa using hsc'
    rw [hb, Bool.cond_true]
    cases hs : Nat.beq s 0
    · exact hdrop
    · rw [Nat.beq_eq] at hs
      subst hs
      rw [Bool.cond_true, takeL_eq rfl, ← hdrop, List.drop_zero]
  · have h1' : (d == 1 && Nat.ble s c) = false := by
      cases h : (d == 1 && Nat.ble s c)
      · rfl
      · simp only [Bool.and_eq_true, beq_iff_eq, Nat.ble_eq] at h
        exact absurd h h1
    rw [h1', Bool.cond_false]
    by_cases h0 : d = 0
    · subst h0
      simp only [beq_self_eq_true, Bool.cond_true]
      rcases Nat.eq_zero_or_pos c with hc | hc
      · subst hc
        rfl
      · have hs : s < xs.length := by simpa using hlt 0 hc
        have hx : cond (Nat.ble s c) (xs.getD s default) (T.get s) = xs.getD s default := by
          cases Nat.ble s c
          · exact hT s hs
          · rfl
        rw [hx]
        simp
    · have h0' : (d == 0) = false := by simpa using h0
      rw [h0', Bool.cond_false]
      exact hgen

theorem pickRuns_eq [Inhabited α] {xs : List α} {T : PTree α}
    (hT : ∀ k < xs.length, T.get k = xs.getD k default) :
    ∀ {idx : IndexMap}, IndexMap.inRange idx xs.length = true →
      pickRuns xs xs.length T idx = idx.toList.map fun i => xs.getD i default
  | [], _ => rfl
  | (s, d, c) :: rest, h => by
    have h' := h
    simp only [IndexMap.inRange, List.all_cons, Bool.and_eq_true] at h'
    have hr : IndexMap.inRange [(s, d, c)] xs.length = true := by
      simpa [IndexMap.inRange] using h'.1
    rw [pickRuns, pickRun_eq hT hr, pickRuns_eq hT (by simpa [IndexMap.inRange] using h'.2)]
    simp [IndexMap.toList, List.map_append, List.map_map, Function.comp_def]

/-- **Reading by runs is reading by the positional tree**, for an index map in range. -/
theorem pickL_eq [Inhabited α] {xs : List α} {idx : IndexMap}
    (h : IndexMap.inRange idx xs.length = true) :
    pickL xs idx = idx.toList.map (PTree.ofList xs).get := by
  rw [pickL, pickRuns_eq (fun k hk => PTree.get_ofList xs hk) h]
  have hm : ∀ i ∈ idx.toList, i < xs.length := fun i hi => by
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hi
    rw [← List.getD_eq_getElem _ 0, ← IndexMap.entry_eq_getD_toList]
    exact IndexMap.entry_lt_of_inRange h (by rwa [IndexMap.length_toList] at hj)
  exact List.map_congr_left fun i hi => (PTree.get_ofList xs (hm i hi)).symm

end ListTree

/-! ## Rows -/

/-- **The value of a row** of codes on the operand `x`. -/
def rowEval {F : Type*} [CommRing F] (κc : ℕ → F) (row : List (ℕ × ℕ)) (x : ℕ → F) : F :=
  (row.map fun t => κc t.2 * x t.1).sum

section Codes

variable (ir : RealizedProgram)

variable {ir} {I : Interp}

/-- **A constant of the circuit's field reads its codes**, decoded in the circuit's field `f`. -/
theorem constCodes?_read {rd : ir.Valuation I}
    (hK : ∀ v es, (ir.value v).kind = .constant es → ∀ i,
      rd v i = (I (ir.valueField v)).decode (es.getD i 0))
    {c f v : ℕ} (hf : ir.circField c = f) {es : List ℕ} (h : constCodes? ir c v = some es)
    (i : ℕ) : (castElt (rd v i) : (I f).K) = (I f).decode (es.getD i 0) := by
  unfold constCodes? at h
  cases hb : (Nat.beq (ir.valueField v) (ir.circField c) && ir.isConstant v)
  · rw [hb] at h
    simp at h
  · rw [hb, Bool.cond_true, Option.some.injEq] at h
    subst h
    simp only [Bool.and_eq_true, Nat.beq_eq] at hb
    rw [hK v _ (kind_of_isConstant hb.2) i]
    exact castElt_decode (hb.1.trans hf) _

end Codes

/-! ## Named operators -/

section Named

variable (ir : RealizedProgram)

variable {ir}

variable {F : Type*} [CommRing F]

theorem length_shiftRows (C m : ℕ) (rows : List (List (ℕ × ℕ))) :
    (shiftRows C m rows).length = m * rows.length := by
  rw [shiftRows, List.length_flatten, List.map_map]
  have : (List.range m).map (List.length ∘ fun b => rows.map fun r => r.map fun t =>
      (t.1 + b * C, t.2)) = (List.range m).map fun _ => rows.length :=
    List.map_congr_left fun b _ => by simp
  rw [this, sum_map_range]
  simp

theorem getD_shiftRows {C m R : ℕ} {rows : List (List (ℕ × ℕ))} (hR : rows.length = R)
    (hR0 : 0 < R) {j : ℕ} (hj : j < m * R) :
    (shiftRows C m rows).getD j [] =
      (rows.getD (j % R) []).map fun t => (t.1 + j / R * C, t.2) := by
  have hjm : j / R < m := Nat.div_lt_of_lt_mul (by rwa [mul_comm])
  rw [shiftRows, getD_flatten_of_length hR0 [] _ (fun b hb => by
      obtain ⟨a, -, rfl⟩ := List.mem_map.1 hb
      simp [hR]),
    getD_map_of_lt _ (by simpa using hjm) [] 0,
    getD_map_of_lt _ (by rw [hR]; exact Nat.mod_lt _ hR0) [] []]
  simp [List.getD_eq_getElem?_getD, hjm]

theorem rowEval_shift {F : Type*} [CommRing F] (κc : ℕ → F) (row : List (ℕ × ℕ)) (s : ℕ)
    (x : ℕ → F) :
    rowEval κc (row.map fun t => (t.1 + s, t.2)) x = rowEval κc row (fun c => x (s + c)) := by
  rw [rowEval, rowEval, List.map_map]
  congr 1
  refine List.map_congr_left fun t _ => ?_
  simp [add_comm]

theorem rowEval_opDigitRow {F : Type*} [CommRing F] {κc : ℕ → F} {ar : GKR.Fold.CodeArith}
    (hA : ar.Hom κc) (base : ℕ) (x : ℕ → F) :
    ∀ (k l w : ℕ), rowEval κc (opDigitRow ar base l k w) x =
      ∑ i ∈ Finset.range k, κc w * κc base ^ i * x (l + i)
  | 0, _, _ => by simp [opDigitRow, rowEval]
  | k + 1, l, w => by
    have ih := rowEval_opDigitRow hA base x k (l + 1) (ar.mul w base)
    rw [rowEval, opDigitRow, List.map_cons, List.sum_cons, ← rowEval, ih, Finset.sum_range_succ',
      hA.mul, add_comm]
    congr 1
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [show l + 1 + i = l + (i + 1) by ring, pow_succ]
      ring
    · simp

/-- **The rows of a named operator compute it** in circuit `c`'s field `f`, once per kind: `sum`
and `fromDigits` by their defining sums, `constDiagonal` by its constant's codes, `batched` block by
block. -/
theorem emitRows_sound {I : Interp} {f c : ℕ} (rd : ir.Valuation I) {env : TEnv}
    (hA : env.ar.Hom (I f).decode)
    (hK : ∀ v es, (ir.value v).kind = .constant es → ∀ i,
      rd v i = (I (ir.valueField v)).decode (es.getD i 0))
    (hf : ir.circField c = f) :
    ∀ (op : NamedOp) {rows : List (List (ℕ × ℕ))}, emitRows ir env c op = some rows →
      rows.length = NamedOp.rows ir op ∧
        ∀ (x : ℕ → (I f).K) (j : ℕ), j < NamedOp.rows ir op →
          rowEval (I f).decode (rows.getD j []) x = NamedOp.block ir f rd op x j := by
  intro op
  induction op with
  | sum w =>
    intro rows h
    simp only [emitRows, Option.some.injEq] at h
    subst h
    refine ⟨rfl, fun x j hj => ?_⟩
    obtain rfl : j = 0 := by simpa [NamedOp.rows] using hj
    rw [List.getD_cons_zero, rowEval, sumRow, List.map_map, sum_map_range, NamedOp.block, Ops.sum,
      ite_eq_left rfl, ← Finset.sum_range]
    simp [hA.one]
  | fromDigits k base =>
    intro rows h
    simp only [emitRows, Option.some.injEq] at h
    subst h
    refine ⟨rfl, fun x j hj => ?_⟩
    obtain rfl : j = 0 := by simpa [NamedOp.rows] using hj
    rw [List.getD_cons_zero, rowEval_opDigitRow hA, NamedOp.block, Ops.fromDigits, ite_eq_left rfl,
      ← Finset.sum_range fun l => (I f).decode base ^ l * x l]
    simp [hA.one]
  | constDiagonal d =>
    intro rows h
    simp only [emitRows, Option.map_eq_some_iff] at h
    obtain ⟨es, hes, rfl⟩ := h
    refine ⟨by simp [diagRows, NamedOp.rows], fun x j hj => ?_⟩
    have hj' : j < (ir.value d).size := hj
    have hrow : (diagRows (ir.value d).size es).getD j [] = [(j, es.getD j 0)] := by
      simp [diagRows, List.getD_eq_getElem?_getD, hj']
    show _ = Ops.diagonal (ir.value d).size (fun s => castElt (rd d s)) x j
    rw [hrow, Ops.diagonal, ite_eq_left hj', constCodes?_read hK hf hes j]
    simp [rowEval]
  | batched b op ih =>
    intro rows h
    simp only [emitRows, Option.map_eq_some_iff] at h
    obtain ⟨one, h1, rfl⟩ := h
    obtain ⟨hl, hv⟩ := ih h1
    refine ⟨by rw [length_shiftRows, hl]; rfl, fun x j hj => ?_⟩
    have hj' : j < b * NamedOp.rows ir op := hj
    have hR0 : 0 < NamedOp.rows ir op := Nat.pos_of_ne_zero fun h0 => by simp [h0] at hj'
    rw [getD_shiftRows hl hR0 hj', rowEval_shift, NamedOp.block]
    beta_reduce
    rw [ite_eq_left hj']
    exact hv _ _ (Nat.mod_lt _ hR0)
  | _ =>
    intro rows h
    simp [emitRows] at h

end Named

/-! ## Sparse rows -/

section Sparse

variable (ir : RealizedProgram)

variable {ir : RealizedProgram} {I : Interp}

theorem coefCode_sound {f c : ℕ} {rd : ir.Valuation I}
    (hK : ∀ v es, (ir.value v).kind = .constant es → ∀ i,
      rd v i = (I (ir.valueField v)).decode (es.getD i 0))
    (hf : ir.circField c = f) {t : Coef} {a : ℕ} (h : coefCode ir c t = some a) :
    (I f).decode a = Coef.eval ir f rd t := by
  cases t with
  | const a' =>
    simp only [coefCode, Option.some.injEq] at h
    subst h
    rfl
  | node v i =>
    simp only [coefCode, Option.map_eq_some_iff] at h
    obtain ⟨es, hes, rfl⟩ := h
    exact (constCodes?_read hK hf hes i).symm

theorem rowEval_of_forall₂ {f : ℕ} (rd : ir.Valuation I) (x : ℕ → (I f).K) :
    ∀ {r : List (ℕ × Coef)} {r' : List (ℕ × ℕ)},
      List.Forall₂ (fun t p => p.1 = t.1 ∧ (I f).decode p.2 = Coef.eval ir f rd t.2) r r' →
      rowEval (I f).decode r' x = (r.map fun t => Coef.eval ir f rd t.2 * x t.1).sum
  | [], [], .nil => rfl
  | _ :: _, _ :: _, .cons ⟨h1, h2⟩ hs => by
    rw [rowEval, List.map_cons, List.sum_cons, ← rowEval, rowEval_of_forall₂ rd x hs,
      List.map_cons, List.sum_cons, h1, h2]

end Sparse

end GordieHowe.RealizedProgram
