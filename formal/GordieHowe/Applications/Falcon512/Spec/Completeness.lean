-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Falcon512.Spec.Encoding
import all LatticeCrypto.Falcon.Concrete.Encoding

@[expose] public section

namespace GordieHowe.Falcon512
open _root_.Falcon.Concrete

 theorem parseUnary_success_shape {t : Bool} {m : ℕ} {bs : List Bool} {x : ℤ} {rest : List Bool}
    (h : parseUnary t m bs = some (x, rest)) :
    ∃ q : ℕ, bs = List.replicate q false ++ true :: rest ∧
      x = if t then -((m + 128 * q : ℕ) : ℤ) else ((m + 128 * q : ℕ) : ℤ) := by
  induction bs generalizing m x rest with
  | nil => simp [parseUnary] at h
  | cons b bs ih =>
    cases b with
    | false =>
      by_cases hov : 2047 < m + 128
      · simp [parseUnary, hov] at h
      · have h' : parseUnary t (m + 128) bs = some (x, rest) := by
          simpa [parseUnary, hov] using h
        obtain ⟨q, hbs, hx⟩ := ih (m := m + 128) h'
        refine ⟨q + 1, ?_, ?_⟩
        · rw [List.replicate_succ, List.cons_append, hbs]
        · cases t with
          | false => simp only [Bool.false_eq_true, ↓reduceIte] at hx ⊢; omega
          | true => simp only [↓reduceIte] at hx ⊢; omega
    | true =>
      by_cases hz : m = 0 ∧ t = true
      · simp [parseUnary, hz] at h
      · have hs : some (if t then -((m : ℕ) : ℤ) else ((m : ℕ) : ℤ), bs) =
              some (x, rest) := by simpa [parseUnary, hz] using h
        have hp := Option.some.inj hs
        have heq := congrArg Prod.fst hp
        have hrest := congrArg Prod.snd hp
        refine ⟨0, by simpa using hrest, ?_⟩
        simpa using heq.symm
 theorem parseUnary_success_bound {t : Bool} {m : ℕ} {bs : List Bool} {x : ℤ} {rest : List Bool}
    (hm : m ≤ 2047) (h : parseUnary t m bs = some (x, rest)) : x.natAbs ≤ 2047 := by
  induction bs generalizing m x rest with
  | nil => simp [parseUnary] at h
  | cons b bs ih =>
    cases b with
    | false =>
      by_cases hov : 2047 < m + 128
      · simp [parseUnary, hov] at h
      · have h' : parseUnary t (m + 128) bs = some (x, rest) := by
          simpa [parseUnary, hov] using h
        exact ih (m := m + 128) (by omega) h'
    | true =>
      by_cases hz : m = 0 ∧ t = true
      · simp [parseUnary, hz] at h
      · have hs : some (if t then -((m : ℕ) : ℤ) else ((m : ℕ) : ℤ), bs) =
              some (x, rest) := by simpa [parseUnary, hz] using h
        have hp := Option.some.inj hs
        have heq := congrArg Prod.fst hp
        have hnat : ((m : ℤ).natAbs) = m := by
          have hh := Int.natAbs_of_nonneg (a := (m : ℤ)) (by positivity)
          exact_mod_cast hh
        cases t with
        | false =>
            simp only [Bool.false_eq_true, ↓reduceIte] at heq
            rw [← heq, hnat]
            exact hm
        | true =>
            simp only [↓reduceIte] at heq
            rw [← heq, Int.natAbs_neg, hnat]
            exact hm
 theorem parseCoeff_success_shape {bs : List Bool} {x : ℤ} {rest : List Bool}
    (h : parseCoeff bs = some (x, rest)) :
    ∃ t : Bool, ∃ low : List Bool, ∃ q : ℕ,
      bs = t :: (low ++ List.replicate q false ++ true :: rest) ∧
      low.length = 7 ∧ x.natAbs = natOfBits low + 128 * q ∧ x.natAbs ≤ 2047 := by
  cases bs with
  | nil => simp [parseCoeff] at h
  | cons t tail =>
    by_cases hlen : 7 ≤ tail.length
    · have hu : parseUnary t (natOfBits (tail.take 7)) (tail.drop 7) = some (x, rest) := by
        simpa [parseCoeff, hlen] using h
      obtain ⟨q, hshape, hx⟩ := parseUnary_success_shape hu
      have hxbound : x.natAbs ≤ 2047 := by
        exact parseUnary_success_bound (t := t) (m := natOfBits (tail.take 7))
          (bs := tail.drop 7) (x := x) (rest := rest)
          (by
            have hh := natOfBits_lt (tail.take 7)
            rw [List.length_take, min_eq_left hlen] at hh
            norm_num at hh ⊢
            omega) hu
      refine ⟨t, tail.take 7, q, ?_, ?_, ?_, hxbound⟩
      · have htail : tail = tail.take 7 ++ tail.drop 7 := (List.take_append_drop 7 tail).symm
        have htail' := htail.trans (congrArg (fun u => tail.take 7 ++ u) hshape)
        simpa [List.append_assoc] using congrArg (fun u => t :: u) htail'
      · rw [List.length_take, min_eq_left hlen]
      · have hnat : ∀ n : ℕ, ((n : ℤ).natAbs) = n := by
          intro n
          have hh := Int.natAbs_of_nonneg (a := (n : ℤ)) (by positivity)
          exact_mod_cast hh
        cases t with
        | false =>
            have hn := congrArg Int.natAbs hx
            have hnonneg : (0 : ℤ) ≤
                (natOfBits (List.take 7 tail) + 128 * q : ℕ) := by positivity
            rw [ite_eq_right (by decide)] at hn
            have hh := Int.natAbs_of_nonneg
              (a := ((natOfBits (List.take 7 tail) + 128 * q : ℕ) : ℤ)) hnonneg
            have hh' : (((natOfBits (List.take 7 tail) + 128 * q : ℕ) : ℤ).natAbs) =
                natOfBits (List.take 7 tail) + 128 * q := by exact_mod_cast hh
            rw [hh'] at hn
            exact hn
        | true =>
            have hn := congrArg Int.natAbs hx
            rw [ite_eq_left (by decide), Int.natAbs_neg, hnat] at hn
            exact hn
    · simp [parseCoeff, hlen] at h
 theorem parseCoeff_success_shape_div {bs : List Bool} {x : ℤ} {rest : List Bool}
    (h : parseCoeff bs = some (x, rest)) :
    ∃ t : Bool, ∃ low : List Bool, ∃ q : ℕ,
      bs = t :: (low ++ List.replicate q false ++ true :: rest) ∧
      low.length = 7 ∧ x.natAbs = natOfBits low + 128 * q ∧ q = x.natAbs / 128 ∧ x.natAbs ≤ 2047 := by
  obtain ⟨t, low, q, hbs, hlow, hx, hxbound⟩ := parseCoeff_success_shape h
  have hnat : natOfBits low < 128 := by
    have hh := natOfBits_lt low
    rw [hlow] at hh
    simpa using hh
  have hq : q = x.natAbs / 128 := by
    rw [hx]
    omega
  exact ⟨t, low, q, hbs, hlow, hx, hq, hxbound⟩

 theorem parseCoeffs_success_length {n : ℕ} {bits : List Bool} {xs : List ℤ} {rest : List Bool}
    (h : parseCoeffs n bits = some (xs, rest)) :
    xs.length = n ∧ (∀ x ∈ xs, x.natAbs ≤ 2047) ∧
      bits.length = 9 * n + (xs.map (fun x => x.natAbs / 128)).sum + rest.length := by
  induction n generalizing bits xs rest with
  | zero =>
      simp only [parseCoeffs] at h
      have hp := Option.some.inj h
      rcases hp with ⟨hxs, hrest⟩
      simp
  | succ n ih =>
      simp only [parseCoeffs] at h
      cases hpc : parseCoeff bits with
      | none => simp [hpc] at h
      | some pr =>
          cases pr with
          | mk x mid =>
              simp only [hpc] at h
              cases hrec : parseCoeffs n mid with
              | none => simp [hrec] at h
              | some pr2 =>
                  cases pr2 with
                  | mk ys rest' =>
                      simp [hrec] at h
                      rcases h with ⟨hxs, hrest⟩
                      subst xs
                      subst rest
                      obtain ⟨t, low, q, hbits, hlow, hx, hq, hxbound⟩ := parseCoeff_success_shape_div hpc
                      obtain ⟨hyl, hyb, hlen⟩ := ih hrec
                      refine ⟨?_, ?_, ?_⟩
                      · simp [hyl]
                      · intro z hz
                        simp only [List.mem_cons] at hz
                        rcases hz with hz | hz
                        · subst z
                          exact hxbound
                        · exact hyb z hz
                      · rw [hbits]
                        simp [hlow, hq, hlen, List.length_append]
                        omega

 theorem sum_list_map_fin {n : ℕ} (l : List ℤ) (g : ℤ → ℕ) (hl : l.length = n) :
    (∑ i : Fin n, g (l.getD i.val 0)) = (l.map g).sum := by
  induction n generalizing l with
  | zero =>
      have : l = [] := by simpa using hl
      subst l
      simp
  | succ n ih =>
      cases l with
      | nil => simp at hl
      | cons a l =>
          simp only [List.length_cons] at hl
          rw [Fin.sum_univ_succ]
          simp only [List.getD_eq_getElem?_getD, List.getElem?_cons_succ, Fin.val_succ]
          change g a + (∑ i : Fin n, g (l.getD i.val 0)) = _
          rw [ih l (by omega)]
          simp

 theorem decompress_success_encodingBounds {d : List UInt8} {s : _root_.Falcon.IntPoly falcon512.n}
    (h : _root_.Falcon.Concrete.decompress falcon512.n d 625 = some s) :
    EncodingBounds falcon512 s := by
  unfold _root_.Falcon.Concrete.decompress at h
  by_cases hlen : d.length ≠ 625
  · simp [hlen] at h
  · have hlen' : d.length = 625 := by omega
    simp only [hlen, ↓reduceIte] at h
    cases hp : _root_.Falcon.Concrete.parseCoeffs falcon512.n
        (_root_.Falcon.Concrete.bytesToBits d) with
    | none => simp [hp] at h
    | some pr =>
        cases pr with
        | mk vals tail =>
            simp only [hp] at h
            by_cases hall : tail.all (fun b => !b) = true
            · simp only [hall, ↓reduceIte] at h
              have hvec : LatticeCrypto.Poly.ofPi
                    (fun i : Fin falcon512.n => vals.getD i.val 0) = s := by
                change Vector.ofFn (fun i : Fin falcon512.n => vals.getD i.val 0) = s
                exact Option.some.inj h
              have hlenbits : (_root_.Falcon.Concrete.bytesToBits d).length = 8 * 625 := by
                rw [_root_.Falcon.Concrete.bytesToBits]
                simp only [List.length_flatMap, _root_.Falcon.Concrete.byteBits,
                  _root_.Falcon.Concrete.natBits_length]
                have hsum8 : ∀ l : List UInt8,
                    (l.map (fun _ => 8)).sum = 8 * l.length := by
                  intro l
                  induction l with
                  | nil => simp
                  | cons a l ih =>
                      simp only [List.map_cons, List.sum_cons, List.length_cons]
                      omega
                rw [hsum8, hlen']
              obtain ⟨hvl, hvb, hagg⟩ := parseCoeffs_success_length hp
              have hn : falcon512.n = 512 := rfl
              have hsum : (vals.map (fun x => x.natAbs / 128)).sum ≤ 392 := by
                rw [hagg] at hlenbits
                rw [hn] at hlenbits
                omega
              have hsget : ∀ i : Fin 512, s.get i = vals.getD i.val 0 := by
                intro i
                rw [← hvec]
                exact LatticeCrypto.Poly.get_vectorOfFn _ i
              refine { coefficients := ?_, highSum := ?_ }
              · intro i
                have hi512 : i.val < 512 := by simpa [hn] using i.isLt
                let j : Fin 512 := ⟨i.val, hi512⟩
                have hsj : s.get i = vals.getD i.val 0 := by
                  have hij : i = (j : Fin falcon512.n) := by
                    apply Fin.ext
                    rfl
                  rw [hij]
                  simpa [j] using hsget j
                have hi : i.val < vals.length := by rw [hvl]; exact i.isLt
                have hm : vals.getD i.val 0 ∈ vals := by
                  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
                  simp
                have hb := hvb _ hm
                rw [hsj]
                simp only [Codec.magnitudeBound_eq]
                omega
              · calc
                  ∑ i : Fin 512, (s.get i).natAbs / 128 =
                      ∑ i : Fin 512, (vals.getD i.val 0).natAbs / 128 := by
                        apply Finset.sum_congr rfl
                        intro i hi
                        rw [hsget i]
                  _ = (vals.map (fun x => x.natAbs / 128)).sum :=
                    sum_list_map_fin vals (fun x => x.natAbs / 128) hvl
                  _ ≤ 392 := hsum
            · simp [hall] at h

end GordieHowe.Falcon512
