-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.GKR.CertificateBridge

@[expose] public section

/-!
# GordieHowe: the certificate's completeness direction

* **The scheduling certificate** (`GordieHowe.GKR.Certificate.check_complete`): an accepted
  certificate whose DAG holds has its layered circuit satisfied: every gate's assertion products
  vanish (the DAG's asserted nodes), and every last-layer wire is zero (an assertion's operand, an
  output node, or an assertion gate: `lastCoverB`).
* **The bridge**: the converse of `GordieHowe.GKR.CertificateBridge.toSource_satisfied`: a layered
circuit satisfied at `vecRead v` gives the source circuit satisfied at `v`
(`GordieHowe.GKR.CertificateBridge.toSource_satisfied_of`), layer by layer
(`GordieHowe.GKR.CertificateBridge.build_complete`).
-/

namespace GordieHowe.GKR.CertificateBridge
open Certificate RealizedProgram

variable {F : Type} [Field F] [DecidableEq F]

omit [DecidableEq F] in
/-- Satisfaction of a concatenation gives satisfaction of the second part after the first. -/
theorem sat_append_right {w : ℕ} {κ : ℕ → F} :
    ∀ (as ms : List (List ℕ)) (v : ℕ → F), Sat w κ (as ++ ms) v → Sat w κ ms (run w κ as v)
  | [], _, _, h => h
  | _ :: as, ms, _, h => sat_append_right as ms _ h.2

/-- A source layer meets its assertions when the layered layer's assertion products vanish. -/
theorem assertions_layerOf_zero {w : ℕ} {κ : ℕ → F} {l : List ℕ} {n wp : ℕ}
    (u : Fin (2 ^ n) → F) (hwp : wp ≤ 2 ^ n) (hr : LayerReads w l wp)
    (has : ∀ g < l.length, ∀ t ∈ gateTerms w (l.getD g 0), t.k = 0 →
      vecRead u t.a * vecRead u t.b = 0) (g : Fin (2 ^ dim l)) :
    Layer.assertions (layerOf w κ l n) u g = 0 := by
  rw [assertions_layerOf]
  by_cases hg : (g : ℕ) < l.length
  · have hmem : l.getD g 0 ∈ l := by
      rw [List.getD_eq_getElem _ _ hg]
      exact List.getElem_mem hg
    apply List.sum_eq_zero
    intro x hx
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hx
    by_cases hk : t.k = 0
    · have hab := hr _ hmem t ht
      rw [ite_eq_left_of_eq_true _ _ (eq_true hk),
        vecRead_wire u (by omega), vecRead_wire u (by omega)]
      exact has g hg t ht hk
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hk)]
  · rw [gateTerms_getD_of_le (by omega)]
    rfl

/-- A source layer's output is the layered layer's values when its assertion products vanish. -/
theorem output_layerOf_eq {w : ℕ} {κ : ℕ → F} {l : List ℕ} {n wp : ℕ} (u : Fin (2 ^ n) → F)
    (hwp : wp ≤ 2 ^ n) (hr : LayerReads w l wp)
    (hasrt : ∀ g < l.length, ∀ t ∈ gateTerms w (l.getD g 0), t.k = 0 →
      vecRead u t.a * vecRead u t.b = 0) :
    vecRead (GKR.Circuit.output (layerOf w κ l n) u) = layerValue w κ l (vecRead u) := by
  funext g
  by_cases hg : g < l.length
  · have hlt : g < 2 ^ dim l := lt_of_lt_of_le hg (Nat.le_pow_clog (by norm_num) _)
    have hmem : l.getD g 0 ∈ l := by
      rw [List.getD_eq_getElem _ _ hg]
      exact List.getElem_mem hg
    simp only [vecRead, hlt, ↓reduceDIte]
    rw [output_layerOf, layerValue, sum_map_filter]
    refine congrArg List.sum (List.map_congr_left fun t ht => ?_)
    have hab := hr _ hmem t ht
    rw [vecRead_wire u (by omega), vecRead_wire u (by omega)]
    by_cases hk : t.k = 0
    · have hz := hasrt g hg t ht hk
      simp [keep, coef, hk, mul_assoc, hz]
    · by_cases hκ : κ t.k = 0
      · simp [keep, hk, hκ]
      · simp [keep, coef, hk, hκ, mul_assoc]
  · have hn : gateTerms w (l.getD g 0) = [] := gateTerms_getD_of_le (by omega)
    rw [layerValue, hn]
    by_cases hlt : g < 2 ^ dim l
    · have hn' : gateTerms w (l.getD ((⟨g, hlt⟩ : Fin (2 ^ dim l)) : ℕ) 0) = [] := hn
      simp only [vecRead, hlt, ↓reduceDIte]
      rw [output_layerOf, hn']
      rfl
    · simp [vecRead, hlt]

/-- **The completeness induction over the source's layers**: if the layered circuit is satisfied
through the layers `rs` (listed from the output down) and any layers `ms` above them, the source
meets its assertions and its output is the layered circuit's values after the layers. -/
theorem build_complete {w : ℕ} {κ : ℕ → F} {d n0 : ℕ} (hfit : n0 ≤ 2 ^ d) :
    ∀ (rs : List (List ℕ)) (u : Fin (2 ^ (build w κ d rs).inputDim) → F) (ms : List (List ℕ)),
      RevReads w n0 rs → Sat w κ (rs.reverse ++ ms) (vecRead u) →
        (build w κ d rs).AssertionsHold u ∧
          vecRead ((build w κ d rs).eval u) = run w κ rs.reverse (vecRead u)
  | [], _, _, _, _ => ⟨trivial, rfl⟩
  | l :: rs, u, ms, hr, hs => by
    rw [List.reverse_cons, List.append_assoc, List.singleton_append] at hs
    obtain ⟨ih1, ih2⟩ := build_complete hfit rs u (l :: ms) hr.2 hs
    have hl : ∀ g < l.length, ∀ t ∈ gateTerms w (l.getD g 0), t.k = 0 →
        vecRead ((build w κ d rs).eval u) t.a * vecRead ((build w κ d rs).eval u) t.b = 0 := by
      rw [ih2]
      exact (sat_append_right _ _ _ hs).1
    refine ⟨⟨assertions_layerOf_zero _ (lowWidth_le hfit rs) hr.1 hl, ih1⟩, ?_⟩
    rw [List.reverse_cons, run_append_singleton]
    exact (output_layerOf_eq _ (lowWidth_le hfit rs) hr.1 hl).trans
      (congrArg (layerValue w κ l) ih2)

/-- **Completeness of the bridge**: if every term of `C` reads wires of the layer below it and
the inputs fit in `2 ^ d`, then wherever the layered circuit is satisfied by `vecRead v`, the
source circuit `toSource C w κ d` is satisfied by `v`. -/
theorem toSource_satisfied_of {C : Layered} {w : ℕ} {κ : ℕ → F} {d : ℕ}
    (hfit : C.inputs ≤ 2 ^ d) (hr : C.ReadsBelow w)
    {v : Fin (2 ^ d) → F}
    (h : C.Satisfied w κ (vecRead v)) : (toSource C w κ d).Satisfied v := by
  have hR := revReads_reverse w C.layers C.inputs hr
  unfold Layered.Satisfied at h
  rw [← List.reverse_reverse C.layers] at h
  unfold toSource LayeredCircuit.Satisfied LayeredCircuit.circuit LayeredCircuit.inputIndex
  generalize C.layers.reverse = rs at hR h ⊢
  cases rs with
  | nil =>
    refine ⟨fun ⟨g, hg⟩ => ?_, fun g => ?_, trivial⟩
    · have hz := h g
      have hg' : g < 2 ^ d := hg
      unfold vecRead at hz
      split_ifs at hz
      change (∑ i : Fin (2 ^ d), if i = ⟨g, hg⟩ then (1 : F) * (v i * v i) else 0) = 0
      rw [Finset.sum_eq_single ⟨g, hg⟩ (fun j _ hj => by simp [hj])
        (fun h => absurd (Finset.mem_univ _) h)]
      simp only [ite_true, one_mul]
      rw [hz, mul_zero]
    · unfold Layer.assertions
      refine Finset.sum_eq_zero fun i _ => ?_
      split_ifs with hc
      · exact absurd hc.1 (show (1 : F) ≠ 0 from one_ne_zero)
      · rfl
  | cons l rs =>
    have hc := congrArg (fun m => 2 ^ m) (build_inputDim w κ d (l :: rs))
    have hs : Sat w κ ((l :: rs).reverse ++ []) (vecRead (v ∘ Fin.cast hc)) := by
      rw [vecRead_comp_cast, List.append_nil]
      exact h
    obtain ⟨h1, h2⟩ := build_complete hfit (l :: rs) (v ∘ Fin.cast hc) [] hR hs
    have hz := sat_append_right _ _ _ hs
    rw [vecRead_comp_cast, ← vecRead_comp_cast hc, ← h2] at hz
    refine ⟨fun g => ?_, h1⟩
    have := hz g
    unfold vecRead at this
    split_ifs at this with hg
    · exact this
    · exact absurd g.isLt hg

end GordieHowe.GKR.CertificateBridge

namespace GordieHowe.GKR.Certificate

section Completeness

variable {F : Type*} [CommSemiring F]

/-- A merge keeps every element of its inputs. -/
theorem mem_mergeNat_of {n : ℕ} :
    ∀ (f : ℕ) (xs ys : List ℕ), n ∈ xs ∨ n ∈ ys → n ∈ mergeNat f xs ys
  | 0, xs, ys, h => List.mem_append.mpr h
  | _ + 1, [], ys, h => by simpa [mergeNat] using h
  | _ + 1, x :: xs, [], h => by simpa [mergeNat] using h
  | f + 1, x :: xs, y :: ys, h => by
    simp only [mergeNat]
    cases hb : Nat.ble x y
    · rw [Bool.cond_false]
      by_cases hy : n = y
      · exact hy ▸ List.mem_cons_self ..
      · refine List.mem_cons_of_mem _ (mem_mergeNat_of f (x :: xs) ys ?_)
        rcases h with h | h
        · exact Or.inl h
        · exact Or.inr ((List.mem_cons.mp h).resolve_left hy)
    · rw [Bool.cond_true]
      by_cases hx : n = x
      · exact hx ▸ List.mem_cons_self ..
      · refine List.mem_cons_of_mem _ (mem_mergeNat_of f xs (y :: ys) ?_)
        rcases h with h | h
        · exact Or.inl ((List.mem_cons.mp h).resolve_left hx)
        · exact Or.inr h

/-- Pairwise merging keeps every element of the runs. -/
theorem mem_mergePairs_of {n : ℕ} :
    ∀ ls : List (List ℕ), n ∈ ls.flatten → n ∈ (mergePairs ls).flatten
  | a :: b :: rest, h => by
    simp only [mergePairs, List.flatten_cons, List.mem_append] at h ⊢
    rcases h with h | h | h
    · exact Or.inl (mem_mergeNat_of _ a b (Or.inl h))
    · exact Or.inl (mem_mergeNat_of _ a b (Or.inr h))
    · exact Or.inr (mem_mergePairs_of rest h)
  | [], h => h
  | [_], h => h

/-- Merging all runs keeps every element of the runs. -/
theorem mem_mergeAll_of {n : ℕ} :
    ∀ (f : ℕ) (ls : List (List ℕ)), n ∈ ls.flatten → n ∈ mergeAll f ls
  | _, [], h => by simp at h
  | _, [a], h => by simpa [mergeAll] using h
  | 0, _ :: _ :: _, h => h
  | f + 1, a :: b :: rest, h => mem_mergeAll_of f _ (mem_mergePairs_of _ h)

/-- Sorting keeps every element of the input. -/
theorem mem_sortNat_of {n : ℕ} {l : List ℕ} (h : n ∈ l) : n ∈ sortNat l :=
  mem_mergeAll_of _ _ (by simpa using h)

/-- An accepted run cover: every wire `g, …, g + n − 1` occurs in the list. -/
theorem mem_of_coverRun : ∀ (n g : ℕ) (l : List ℕ), coverRun n g l = true →
    ∀ i, g ≤ i → i < g + n → i ∈ l
  | 0, _, _, _, i, h1, h2 => by omega
  | n + 1, g, l, h, i, h1, h2 => by
    unfold coverRun at h
    have hsub : ∀ m, m ∈ l.dropWhile (fun y => Nat.blt y g) → m ∈ l :=
      fun m hm => (List.dropWhile_suffix _).subset hm
    split at h
    · next y ys hd =>
      simp only [Bool.and_eq_true, Nat.beq_eq] at h
      obtain ⟨rfl, h⟩ := h
      rcases Nat.eq_or_lt_of_le h1 with rfl | hlt
      · exact hsub _ (hd ▸ List.mem_cons_self ..)
      · exact hsub _ (hd ▸ mem_of_coverRun n (y + 1) _ h i hlt (by omega))
    · exact absurd h (by simp)

/-- Accepted term lists carry assertions back: if the node's assertion products vanish, so do
the gate's. -/
theorem termsOk_assert_of {w : ℕ} {D : Dag} {κ x : ℕ → F} {T : Table} {wp r : ℕ} {v : ℕ → F}
    (hv : Carried w D κ x T wp v) :
    ∀ ts us, termsOk w T wp r ts us = true →
      (∀ u ∈ us, u.k = 0 → D.val w κ x u.a * D.val w κ x u.b = 0) →
        ∀ t ∈ ts, t.k = 0 → v t.a * v t.b = 0
  | [], [], _, _ => by simp
  | t :: ts, u :: us, h, ha => by
    simp only [termsOk, Bool.and_eq_true, Nat.beq_eq, Nat.blt_eq] at h
    obtain ⟨⟨⟨⟨⟨⟨hk, hta⟩, htb⟩, _⟩, _⟩, hc⟩, hrest⟩ := h
    intro t' ht' hk'
    rcases List.mem_cons.mp ht' with rfl | ht'
    · rw [carries_prod hc v (D.val w κ x) (hv _ hta) (hv _ htb)]
      exact ha u (List.mem_cons_self ..) (hk.symm.trans hk')
    · exact termsOk_assert_of hv ts us hrest (fun u' hu' => ha u' (List.mem_cons_of_mem _ hu'))
        t' ht' hk'
  | [], _ :: _, h, _ => by simp [termsOk] at h
  | _ :: _, [], h, _ => by simp [termsOk] at h

/-- An accepted output-wire list: each listed wire is below the width and carries a listed
node. -/
theorem outWiresOk_mem {w : ℕ} {T : Table} {wl : ℕ} :
    ∀ ns gs, outWiresOk w T wl ns gs = true → ∀ g ∈ gs, g < wl ∧ cell w T g ∈ ns
  | [], [], _ => by simp
  | n :: ns, g :: gs, h => by
    simp only [outWiresOk, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h
    obtain ⟨⟨hg, hn⟩, hrest⟩ := h
    intro g' hg'
    rcases List.mem_cons.mp hg' with rfl | hg'
    · exact ⟨hg, hn ▸ List.mem_cons_self ..⟩
    · obtain ⟨h1, h2⟩ := outWiresOk_mem ns gs hrest g' hg'
      exact ⟨h1, List.mem_cons_of_mem _ h2⟩
  | [], _ :: _, h => by simp [outWiresOk] at h
  | _ :: _, [], h => by simp [outWiresOk] at h

/-- An accepted last-layer assertion's wire is zero when its node's assertion holds. -/
theorem outputOk_zero {w : ℕ} {D : Dag} {κ x : ℕ → F} {T : Table} {wl : ℕ} {v : ℕ → F}
    (hone : D.val w κ x 0 = 1) (hv : Carried w D κ x T wl v) {o : ℕ × ℕ}
    (h : outputOk w D T wl o = true) (ho : D.AssertHolds w κ x o.2) : v o.1 = 0 := by
  simp only [outputOk, Bool.and_eq_true, Nat.blt_eq] at h
  obtain ⟨⟨hg, hle⟩, h⟩ := h
  have hmem := ho
  unfold Dag.AssertHolds at hmem
  rw [nodeTerms_of_le hle] at hmem
  generalize hts : terms w (D.tree.get o.2) = ts at h hmem
  match ts, h, hmem with
  | [t], h, hmem =>
    simp only [Bool.and_eq_true, Nat.beq_eq] at h
    obtain ⟨⟨hk, ha⟩, hb⟩ := h
    have := hmem t (List.mem_singleton_self _) hk
    rw [ha, hone, one_mul] at this
    rw [hv _ hg, hb, this]

/-- A zero gate of a layer is one of its wires, and every term of its gate is an assertion
term. -/
theorem mem_zeroGates {w g : ℕ} {l : List ℕ} (h : g ∈ zeroGates w l) :
    g < l.length ∧ ∀ t ∈ gateTerms w (l.getD g 0), t.k = 0 := by
  simp only [zeroGates, List.mem_filterMap] at h
  obtain ⟨⟨c, i⟩, hp, hc⟩ := h
  cases hall : (gateTerms w c).all fun t => Nat.beq t.k 0
  · rw [hall] at hc
    exact absurd hc (by simp)
  · rw [hall] at hc
    simp only [Bool.cond_true, Option.some.injEq] at hc
    subst hc
    rw [List.mem_zipIdx_iff_getElem?] at hp
    obtain ⟨hlt, hget⟩ := List.getElem?_eq_some_iff.mp hp
    refine ⟨hlt, fun t ht => ?_⟩
    rw [List.getD_eq_getElem _ _ hlt, hget] at ht
    simpa using (List.all_eq_true.mp hall) t ht

/-- An accepted layer's assertion products vanish when the nodes it collects hold. -/
theorem layerOk_asserts {w : ℕ} {D : Dag} {κ x : ℕ → F} {Tp Tc : Table} {wp : ℕ} {l : List ℕ}
    {v : ℕ → F} (hv : Carried w D κ x Tp wp v) (h : layerOk w D Tp wp Tc l = true) {acc : List ℕ}
    (hcol : ∀ n ∈ collectGates w l acc, D.AssertHolds w κ x n) :
    ∀ g < l.length, ∀ t ∈ gateTerms w (l.getD g 0), t.k = 0 → v t.a * v t.b = 0 := by
  intro g hg t ht hk
  obtain ⟨-, hc⟩ := gatesOk_get 0 l h g hg
  unfold gateOk at hc
  simp only [Bool.and_eq_true] at hc
  cases hf : flagged w (l.getD g 0)
  · rw [hf, Bool.cond_false] at hc
    simp only [Bool.and_eq_true] at hc
    have hA := hcol _ (gateNode_mem_collectGates l acc g hg hf
      (CertificateBridge.hasAssert_of_mem ht hk))
    refine termsOk_assert_of hv _ _ hc.2.2 (fun u hu hku => hA u ?_ hku) t ht hk
    rw [nodeTerms_of_le hc.2.1]
    exact hu
  · rw [hf, Bool.cond_true] at hc
    have hcp := hc.2
    generalize gateTerms w (l.getD g 0) = ts at hcp ht
    match ts, hcp, ht with
    | [t'], hcp, ht =>
      simp only [copyOk, Bool.and_eq_true, Nat.beq_eq] at hcp
      rw [List.mem_singleton.mp ht] at hk
      rw [hk] at hcp
      exact absurd hcp.1.1.1 (by decide)

/-- The last layer's wires are zero: an assertion's output wire, an output node's wire, or an
assertion gate. -/
theorem lastLayer_zero {w : ℕ} {D : Dag} {κ x : ℕ → F} {outs : List (ℕ × ℕ)} {outw : List ℕ}
    {Tp T : Table} {wp : ℕ} {l : List ℕ} {v : ℕ → F} (hκ : κ 1 = 1) (hone : D.val w κ x 0 = 1)
    (houts : ∀ o ∈ outs, D.AssertHolds w κ x o.2) (hout : ∀ n ∈ D.outputs, D.val w κ x n = 0)
    (hv : Carried w D κ x Tp wp v) (hl : layerOk w D Tp wp T l = true)
    (h : layersOk w D outs outw T l.length [] [] = true)
    (has : ∀ g < l.length, ∀ t ∈ gateTerms w (l.getD g 0), t.k = 0 → v t.a * v t.b = 0)
    (hcov : ∀ g < l.length, g ∈ outs.map Prod.fst ++ outw ++ zeroGates w l) :
    ∀ g, layerValue w κ l v g = 0 := by
  have hv' := layerOk_carried hκ hone hv hl
  simp only [layersOk, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨hos, hws⟩ := h
  intro g
  by_cases hg : g < l.length
  · rcases List.mem_append.mp (hcov g hg) with hm | hm
    · rcases List.mem_append.mp hm with hm | hm
      · obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hm
        exact outputOk_zero hone hv' (hos o ho) (houts o ho)
      · obtain ⟨hg', hn⟩ := outWiresOk_mem _ _ hws g hm
        rw [hv' _ hg', hout _ hn]
    · have hz := (mem_zeroGates hm).2
      rw [layerValue]
      refine List.sum_eq_zero fun y hy => ?_
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hy
      rw [mul_assoc, has g hg t ht (hz t ht), mul_zero]
  · rw [layerValue, CertificateBridge.gateTerms_getD_of_le (by omega)]
    rfl

/-- **Completeness of the layers**: from a carried depth, if the DAG holds and every wire of the
last layer is covered, the rest of the circuit is satisfied. -/
theorem layersOk_complete {w : ℕ} {D : Dag} {κ x : ℕ → F} {outs : List (ℕ × ℕ)} {outw : List ℕ}
    (hκ : κ 1 = 1) (hone : D.val w κ x 0 = 1)
    (houts : ∀ o ∈ outs, D.AssertHolds w κ x o.2) (hout : ∀ n ∈ D.outputs, D.val w κ x n = 0) :
    ∀ (Tp : Table) (wp : ℕ) (Ts : List Table) (l : List ℕ) (ls : List (List ℕ)) (v : ℕ → F)
      (acc : List ℕ), layersOk w D outs outw Tp wp Ts (l :: ls) = true →
        Carried w D κ x Tp wp v → (∀ n ∈ collect w (l :: ls) acc, D.AssertHolds w κ x n) →
          (∀ g < ((l :: ls).getLast (List.cons_ne_nil _ _)).length,
            g ∈ outs.map Prod.fst ++ outw ++
              zeroGates w ((l :: ls).getLast (List.cons_ne_nil _ _))) →
            Sat w κ (l :: ls) v
  | Tp, wp, T :: Ts, l, ls, v, acc, h, hv, hcol, hcov => by
    simp only [layersOk, Bool.and_eq_true] at h
    have hcol' : ∀ n ∈ collectGates w l acc, D.AssertHolds w κ x n :=
      fun n hn => hcol n (mem_collect_of_acc ls _ hn)
    have has := layerOk_asserts hv h.1 hcol'
    refine ⟨has, ?_⟩
    cases ls with
    | nil =>
      cases Ts with
      | nil => exact lastLayer_zero hκ hone houts hout hv h.1 h.2 has hcov
      | cons _ _ => simp [layersOk] at h
    | cons l' ls =>
      exact layersOk_complete hκ hone houts hout T l.length Ts l' ls (layerValue w κ l v)
        (collectGates w l acc) h.2 (layerOk_carried hκ hone hv h.1) hcol
        (by simpa only [List.getLast_cons_cons] using hcov)
  | _, _, [], _, _, _, _, h, _, _, _ => by simp [layersOk] at h

/-- **Completeness of the certificate checker.** If `check` accepts, the constant `1` has index
`1` and the input `0` is one, then on every input on which every assertion of the DAG holds and
every output node of the DAG is zero, the layered circuit is satisfied. -/
theorem check_complete {D : Dag} {C : Layered} {K : Cert} (h : check D C K = true)
    {κ x : ℕ → F} (hκ : κ 1 = 1) (hx : x 0 = 1)
    (hD : D.Holds K.width κ x) : C.Satisfied K.width κ x := by
  simp only [check, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨hone, hin⟩, hlay⟩, hasrt⟩, hcov⟩ := h
  have hone' := val_zero (w := K.width) (κ := κ) hone hx
  have hv : Carried K.width D κ x .ident C.inputs x := by
    intro g hg
    have hi : Nat.blt g D.inputs = true := by
      simp only [Nat.beq_eq] at hin
      simpa [Nat.blt_eq, ← hin] using hg
    rw [cell, Dag.val_eq, hi, Bool.cond_true]
  have hasm : ∀ n ∈ collect K.width C.layers (K.outputs.map Prod.snd), n ∈ D.asserts := by
    intro n hn
    rw [listEq_eq _ _ hasrt]
    exact mem_sortNat_of hn
  have houts : ∀ o ∈ K.outputs, D.AssertHolds K.width κ x o.2 := fun o ho =>
    hD.1 _ (hasm _ (mem_collect_of_acc _ _ (List.mem_map_of_mem ho)))
  unfold Layered.Satisfied
  unfold lastCoverB at hcov
  generalize hL : C.layers = L at hlay hasm hcov
  cases L with
  | nil => simp at hcov
  | cons l ls =>
    rw [List.getLast?_eq_some_getLast (List.cons_ne_nil _ _)] at hcov
    exact layersOk_complete hκ hone' houts hD.2 Table.ident C.inputs K.tables l ls x _ hlay hv
      (fun n hn => hD.1 n (hasm n hn))
      (fun g hg => mem_of_mem_sortNat (mem_of_coverRun _ 0 _ hcov g (Nat.zero_le _) (by omega)))

end Completeness

end GordieHowe.GKR.Certificate
