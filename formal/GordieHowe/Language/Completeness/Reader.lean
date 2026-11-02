-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.RealizedProgram.Reader
public import GordieHowe.Language.Completeness.CommDigits
public import GordieHowe.Language.Completeness.MacCheck
public import GordieHoweNative.Language.Completeness.Reader

/-!
# GordieHowe: the certificate reader's lemmas

The kernel's certificate reader (`CReader.ofProgram`) reads the program's checks (its fields,
`ofProgram_*`; a site check at a site is its check, `siteCheckAt_of_some`), and the compiled
checker's reader of a built context equals it (`CReader.ofCtx_build`): each thunk evaluates the
check it caches (`thunkAt_thunks`, `ofCtx_build_site`).
-/

public section

namespace GordieHowe.RealizedProgram

namespace CReader

variable (ir : RealizedProgram) (primeNodes : ℕ → List String) (S : Structure) (G : Gens)

@[simp] theorem ofProgram_toPReader :
    (CReader.ofProgram ir primeNodes S G).toPReader = PReader.ofProgram ir :=
  rfl

@[simp] theorem ofProgram_site :
    (CReader.ofProgram ir primeNodes S G).site = siteCheckAt ir primeNodes S G :=
  rfl

@[simp] theorem ofProgram_commMod :
    (CReader.ofProgram ir primeNodes S G).commMod = ir.commModCB primeNodes S :=
  rfl

@[simp] theorem ofProgram_value : (CReader.ofProgram ir primeNodes S G).value = ir.value := rfl

@[simp] theorem ofProgram_predicate :
    (CReader.ofProgram ir primeNodes S G).predicate = ir.predicate :=
  rfl

@[simp] theorem ofProgram_nValues :
    (CReader.ofProgram ir primeNodes S G).nValues = ir.values.length :=
  rfl

@[simp] theorem ofProgram_nPreds :
    (CReader.ofProgram ir primeNodes S G).nPreds = ir.predicates.length :=
  rfl

@[simp] theorem ofProgram_reads (v : ℕ) :
    (CReader.ofProgram ir primeNodes S G).reads v = ir.readsT.getD v [] :=
  rfl

end CReader

/-- **A site check at a site is the check at it.** -/
theorem siteCheckAt_of_some {ir : RealizedProgram} {primeNodes : ℕ → List String}
    {S : Structure} {G : Gens} {g i : ℕ} {st : MacSite} (h : ir.macSiteAt S g i = some st)
    (k : SiteCheck) : siteCheckAt ir primeNodes S G k g i = k.eval ir primeNodes S G st := by
  rw [siteCheckAt, h]

/-- **A thunk table of `f` reads `f`.** -/
theorem thunkAt_thunks (f : ℕ → Bool) (n m : ℕ) : thunkAt (thunks f n) m (fun _ => f m) = f m := by
  unfold thunkAt thunks
  rw [List.getElem?_toArray, List.getElem?_map]
  by_cases h : m < n
  · rw [List.getElem?_range h]
    rfl
  · rw [List.getElem?_eq_none (by simpa using h)]
    rfl

/-- **The position of a check in `SiteCheck.all` holds it.** -/
theorem SiteCheck.getElem?_all (k : SiteCheck) : SiteCheck.all[k.idx]? = some k := by
  cases k <;> rfl

/-- **The site checks at the program's reader are the site checks.** -/
theorem siteCheckAtR_ofProgram (ir : RealizedProgram) (primeNodes : ℕ → List String)
    (S : Structure) (G : Gens) :
    @siteCheckAtR ir (PReader.ofProgram ir) primeNodes S G = siteCheckAt ir primeNodes S G := by
  funext k g i
  unfold siteCheckAtR siteCheckAt
  cases ir.macSiteAt S g i with
  | none => rfl
  | some st =>
    cases k
    case base => exact macBaseB_ofProgram ir primeNodes S G st
    case digits => exact digitsMacB_ofProgram ir G st
    case tail =>
      simp only [SiteCheck.evalR, SiteCheck.eval, macTailCB]
      split_ifs
      · rfl
      · rfl
      · exact digitsMacB_ofProgram ir G st
    all_goals rfl

/-- **The site thunks of a built context read the site checks.** -/
theorem ofCtx_build_site (ir : RealizedProgram) (primeNodes : ℕ → List String) (S : Structure)
    (G : Gens) (k : SiteCheck) (g i : ℕ) :
    (CReader.ofCtx (CCtx.build ir primeNodes S G)).site k g i =
      siteCheckAt ir primeNodes S G k g i := by
  rw [← siteCheckAtR_ofProgram, ← PReader.ofCtx_build]
  change (match (CCtx.build ir primeNodes S G).site[g]? with
    | some a =>
      match a[i]? with
      | some t =>
        thunkAt t k.idx fun _ => @siteCheckAtR ir (PReader.ofCtx (PCtx.build ir)) primeNodes S G k g i
      | none => @siteCheckAtR ir (PReader.ofCtx (PCtx.build ir)) primeNodes S G k g i
    | none => @siteCheckAtR ir (PReader.ofCtx (PCtx.build ir)) primeNodes S G k g i) = _
  simp only [CCtx.build, thunkAt, List.getElem?_toArray, List.getElem?_map]
  by_cases hg : g < S.gadgets.length
  · rw [List.getElem?_range hg, Option.map_some]
    by_cases hi : i < (S.gadgets[g]?.map (·.preds.length)).getD 0
    · simp only [List.getElem?_toArray, List.getElem?_map, List.getElem?_range hi, Option.map_some,
        SiteCheck.getElem?_all]
      rfl
    · simp only [List.getElem?_toArray, List.getElem?_map,
        List.getElem?_eq_none (show (List.range _).length ≤ i by simpa using hi), Option.map_none]
  · rw [List.getElem?_eq_none (by simpa using hg), Option.map_none]

/-- **The compiled checker's reader of the built context is the kernel's.** -/
theorem CReader.ofCtx_build (ir : RealizedProgram) (primeNodes : ℕ → List String) (S : Structure)
    (G : Gens) :
    CReader.ofCtx (CCtx.build ir primeNodes S G) = CReader.ofProgram ir primeNodes S G := by
  have hs :
      (CReader.ofCtx (CCtx.build ir primeNodes S G)).site = siteCheckAt ir primeNodes S G := by
    funext k g i
    exact ofCtx_build_site ir primeNodes S G k g i
  have hc : (CReader.ofCtx (CCtx.build ir primeNodes S G)).commMod = ir.commModCB primeNodes S := by
    funext m
    refine (thunkAt_thunks _ _ m).trans ?_
    show @PReader.commModCB (ir.srcLeafIvl primeNodes S) ir (PReader.ofCtx (PCtx.build ir)) m = _
    rw [PReader.ofCtx_build]
    exact commModCB_ofProgram ir primeNodes S m
  have hp : (CReader.ofCtx (CCtx.build ir primeNodes S G)).toPReader = PReader.ofProgram ir :=
    PReader.ofCtx_build ir
  calc CReader.ofCtx (CCtx.build ir primeNodes S G)
      = @CReader.mk (CReader.ofCtx (CCtx.build ir primeNodes S G)).toPReader
          (CReader.ofCtx (CCtx.build ir primeNodes S G)).site
          (CReader.ofCtx (CCtx.build ir primeNodes S G)).commMod := rfl
    _ = CReader.ofProgram ir primeNodes S G := by rw [hs, hc, hp]; rfl

end GordieHowe.RealizedProgram
