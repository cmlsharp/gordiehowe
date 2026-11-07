-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweCerts.Applications.MLDSA44.Ring.Carrier.HonestA
public import GordieHoweCerts.Applications.MLDSA44.Ring.Native.HonestValues
public import GordieHoweCerts.Applications.MLDSA44.Ring.Carrier.Frontend.Readings

@[expose] public section

/-!
# GordieHowe: the honest values of the ML-DSA-44 ring carriers

The honest committed values of an ML-DSA-44 ring carrier (`MLDSA44.Ring.Carrier.ROMParams`,
`MLDSA44.Ring.Carrier.QROMParams`; C++ `lib/gordiehowe/examples/rings/mldsa_ring_testing.h`,
`ring_witness`, and `lib/gordiehowe/examples/rings/mldsa_ring_carrier.h`) on an honest input
(`GordieHowe.MLDSA44.Ring.RingIn`), and the parts of its source program the proofs of possession's
predicates give through the two renamings (`CarrierHEmbed`, `CarrierAEmbed`).

* **The renamings' inverses** (`hOf`, `aOf`): the native value of domain `H`'s core (of `hV`) and
  the emulated value of domain `A`'s gadgets (of `aV`) a carrier value renames, if any.
* **The program facts** (`MldsaCarrierHonest`, decided per carrier): the signature relation's
  quotient digits (`qD`), the member's and the quotient's values outside the renamings' images, the
  held committed values committed in the carrier, domain `H`'s core and domain `A`'s values held,
  and the carrier's bound values reading committed values and constants.
* **The honest values** (`honestVal`): `member.a_hat` and `member.t1` the scheme-order transforms
  at `ψ = psi512` of the signer's carrier row (`specE`), `member.mu` the bits of the signer's `μ`,
  the index bits the signer's position's, the quotient digits the digits of the signature
  relation's honest quotient (`quotN`, of the relation's honest integer `sigZ`); at the renamed
  value of a held native value domain `H`'s core (`GordieHowe.MLDSA44.Ring.Native.hValCore`), at the
  renamed value of a held emulated value domain `A`'s (`aValE`).
* **The proofs of possession's view** (`readsCells_pullH`, `readsAE_pullA`): at the source
  environment of the honest values, the environment read as the native program's reads the core's
  honest values on the held values and `0` on the other committed values, and the environment read
  as the emulated program's reads domain `A`'s honest values; so domain `H`'s core and domain `A`'s
  gadgets hold there, and by the renamings' correspondences (`holdsAt_pullEnv`,
  `holdsAt_pullEnv_body`) so do the carrier's predicates (`core_holds`, `aSource_holds`).
-/

namespace GordieHowe.MLDSA44.Ring.Carrier

open GordieHowe.Bits RealizedProgram
open MLDSA44.NativeAlgebraCircuit (flat)
open MLDSA44.NativeAlgebraCircuit.Honest (zCentered)
open GordieHowe.MLDSA44.Ring.Native (muBitNat hValCore hashValCore coreHashB jFR lowFR memFR
  castElt_dep kindCorr_bound coreHashB_cases castElt_evalE_of_eq hPreds_core)
open MLDSA44.Emulated (MldsaELayout aValues MldsaEAlgebra MldsaEmulatedHonest DigitLayout rdA)

set_option linter.unusedSectionVars false

variable {msgLen : ℕ}

/-! ## The renamings' inverses -/

/-- **The native value a carrier value renames** under `σH`, if any (`hV`'s first). -/
def hOf (v : ℕ) : Option ℕ := hV.find? fun u => σH.val u == v

/-- **The emulated value a carrier value renames** under `σA`, if any (`aV`'s first). -/
def aOf (v : ℕ) : Option ℕ := aV.find? fun u => σA.val u == v

/-- `hOf` inverts `σH` on `hV`. -/
theorem hOf_val : ∀ u ∈ hV, hOf (σH.val u) = some u := by
  decide +kernel

/-- `aOf` inverts `σA` on `aV`. -/
theorem aOf_val : ∀ u ∈ aV, aOf (σA.val u) = some u := by
  decide +kernel

/-- The images of the two renamings are disjoint. -/
theorem hOf_valA : ∀ u ∈ aV, hOf (σA.val u) = none := by
  decide +kernel

/-! ## The program facts -/

/-- **The program facts of an ML-DSA-44 ring carrier's honest values** (decided per carrier): the
signature relation's quotient (value `64`) bound to its digits `qD`, which hold every natural up to
the quotient's bound `qmax = 268274655`; the member's values (`55 … 58`) and the quotient's digits
distinct, outside the renamings' images, committed cells of field `0`, with their sizes; the held
committed values committed in the carrier; domain `H`'s core hash values and SampleInBall's cells
held (`hV`); domain `A`'s committed values and bound values held (`aV`), the bound values reading
held values through no shared expression; and the carrier's bound values reading committed values
and constants. -/
class MldsaCarrierHonest (program : RealizedProgram) [CarrierHEmbed program] [CarrierAEmbed program]
    [MldsaEAlgebra (CarrierAEmbed.emu program)] where
  /-- The signature relation's quotient digits. -/
  qD : DigitLayout
  /-- The quotient is bound to its digits. -/
  kind64 : (program.value 64).kind = .bound qD.expr
  /-- The digits hold every natural up to `qmax`. -/
  qFits : qD.Fits 268274656
  /-- The member's values and the quotient's digits are distinct. -/
  member_nodup : ([55, 56, 57, 58] ++ qD.ids).Nodup
  /-- The member's values and the quotient's digits are no renamed values. -/
  member_none : ∀ v ∈ [55, 56, 57, 58] ++ qD.ids, hOf v = none
  /-- The member's values and the quotient's digits rename no committed value of domain `A`. -/
  member_noneA : ∀ v ∈ [55, 56, 57, 58] ++ qD.ids,
    ∀ u ∈ aValues (MldsaEAlgebra.layout (CarrierAEmbed.emu program)), σA.val u ≠ v
  /-- The member's values and the quotient's digits are committed cells of field `0`. -/
  member_cells : ∀ v ∈ [55, 56, 57, 58] ++ qD.ids, program.privCellB v = true ∧
    program.valueField v = 0
  /-- The quotient's digits have one coordinate per coefficient. -/
  qSizes : ∀ v ∈ qD.ids, (program.value v).size = 1024
  /-- The held native committed values are committed values of the carrier. -/
  privCellH : ∀ u ∈ hV, (CarrierHEmbed.nat program).privCellB u = true →
    program.privCellB (σH.val u) = true
  /-- The held emulated committed values are committed values of the carrier. -/
  privCellA : ∀ u ∈ aV, (CarrierAEmbed.emu program).privCellB u = true →
    program.privCellB (σA.val u) = true
  /-- Domain `H`'s core hash values are held. -/
  coreV : (69 ∈ hV ∧ 119 ∈ hV) ∧ ∀ p : Fin 10, (p : ℕ) ≠ 0 → ∀ t : Fin 24, wordsVal p t ∈ hV
  /-- SampleInBall's cells are held. -/
  selV : ∀ u ∈ [556, 557, 560, 561, 562, 563, 564, 565], u ∈ hV
  /-- Domain `A`'s committed values and bound values are held. -/
  aVals : ∀ u ∈ aValues (MldsaEAlgebra.layout (CarrierAEmbed.emu program)) ++ [58, 61, 65, 66],
    u ∈ aV
  /-- The emulated bound values of domain `A` read held values through no shared expression. -/
  boundExprs : ∀ u ∈ [58, 61, 65, 66], (match ((CarrierAEmbed.emu program).value u).kind with
    | .bound E => E.opsFree && E.directNodes.all (· ∈ aV) && E.refs.isEmpty
    | _ => false) = true
  /-- Every value bound to its digits reads committed values and constants. -/
  bound : ∀ v < program.values.length, program.BoundOk v

/-! ## The honest naturals of the member and the quotient -/

section Naturals

variable (y : RingIn msgLen)

/-- **The honest spectra of the signer's carrier row** in a field: coordinate `256 b + m`
(`b < 20`, `m < 256`) is coordinate `m` of the scheme-order transform at `ψ = psi512` of block `b`
of the signer's carrier row (`keyEntry`: `A`'s `16` blocks, then `2^d t1`'s `4`); `0` past
`5120`. -/
-- spec-side
noncomputable def specE (K : Type*) [Field K] (j : ℕ) : K :=
  if j < 5120 then
    Ops.nttScheme 256 (psi512 : K) (fun k => ((keyEntry y.key (256 * (j / 256) + k) : ℕ) : K))
      (j % 256)
  else 0

/-- **The honest centered `z`** of row `j`, at coefficient `t < 256`, `0` past. -/
-- spec-side
def zZ (j : Fin 4) (t : ℕ) : ℤ := if h : t < 256 then zCentered y.z j ⟨t, h⟩ else 0

/-- **The honest challenge** at coefficient `t < 256`, `0` past. -/
-- spec-side
def cZ (t : ℕ) : ℤ := if h : t < 256 then y.c ⟨t, h⟩ else 0

/-- **The honest integer of the signature relation** at coefficient `(i, k)`: `w′` less
`Σ_j A_ij ⊛ z_j − 2^d t1_i ⊛ c` over the integers, `A` and `2^d t1` the signer's keys
(`Emulated.Rows.aKeyOf`, `Emulated.Rows.tKeyOf`), `z` the centered response and `c` the challenge. -/
-- spec-side
noncomputable def sigZ (i : Fin 4) (k : Fin 256) : ℤ :=
  (wNR y (finProdFinEquiv (i, k)) : ℤ) -
    (∑ j : Fin 4, ∑ t : Fin 256,
        Ops.negCoef 256 (keyZ (Emulated.Rows.aKeyOf y.key i j)) k t * zZ y j t -
      ∑ t : Fin 256, Ops.negCoef 256 (keyZ (Emulated.Rows.tKeyOf y.key i)) k t * cZ y t)

/-- **The honest quotient of the signature relation** at coordinate `j = 256 i + k`: `Q` of
`sigZ = q (qlo + Q)` at `qlo = −134137327` (`mldsa_ring_carrier.h`, the quotient of `assert_mod`);
`0` past `1024`. -/
-- spec-side
noncomputable def quotN (j : ℕ) : ℕ :=
  if h : j < 1024 then
    (sigZ y ⟨j / 256, by omega⟩ ⟨j % 256, by omega⟩ / 8380417 + 134137327).toNat
  else 0

end Naturals

/-! ## The honest values -/

section Values

variable {program : RealizedProgram} [CarrierHEmbed program] [CarrierAEmbed program]
  [MldsaEAlgebra (CarrierAEmbed.emu program)] [MldsaCarrierHonest program]
  {F0 FH : FieldInterp} [HField FH]

set_option hygiene false in
local notation "interp" => mldsaInterpOf F0 FH

set_option hygiene false in
local notation "nat" => CarrierHEmbed.nat program

set_option hygiene false in
local notation "emu" => CarrierAEmbed.emu program

set_option hygiene false in
local notation "L" => MldsaEAlgebra.layout (CarrierAEmbed.emu program)

set_option hygiene false in
local notation "qD" => MldsaCarrierHonest.qD program

variable [MldsaHHonest nat] [MldsaHShuffle nat] [MldsaHSelHonest nat] [MldsaHConsts nat FH]

variable (program F0 FH) in
/-- **The honest committed values of an ML-DSA-44 ring carrier** on an honest input:
`member.a_hat` (`55`) and `member.t1` (`56`) the spectra of the signer's carrier row (`specE`),
`member.mu` (`57`) the bits of the signer's `μ`, the index bits (`58`) the bits of the signer's
position, the quotient's digits the digits of the honest quotient (`quotN`); at the renamed value
of a held native value domain `H`'s core (`hValCore`), at the renamed value of a held emulated
value domain `A`'s (`aValE`); `0` elsewhere (the realization's values are generated,
`RealizedProgram.genCommitted`).

Running time: one `ExpandA` and four inverse NTTs of the signer's key, `20` transforms of length
`256`, `μ = H(tr ‖ M′)`, the relation's integers (`O(k l N²)` products of naturals), and the time of
`hValCore` and `aValE`. This running time is argued here, not proved in Lean. -/
-- spec-side
noncomputable def honestVal (y : RingIn msgLen) (v j : ℕ) : (interp (program.valueField v)).K :=
  if v = 55 then castElt (a := 0) (if j < 4096 then specE y (interp 0).K j else 0)
  else if v = 56 then castElt (a := 0) (if j < 1024 then specE y (interp 0).K (4096 + j) else 0)
  else if v = 57 then castElt (a := 0) ((muBitNat y.mu j : ℕ) : (interp 0).K)
  else if v = 58 then castElt (a := 0) ((y.w.idx / 2 ^ j % 2 : ℕ) : (interp 0).K)
  else if v ∈ (qD).ids then castElt (a := 0) (((qD).digit (quotN y j) v : ℕ) : (interp 0).K)
  else match hOf v with
    | some u => castElt (hValCore nat F0 FH y u j)
    | none => match aOf v with
      | some u => castElt (a := 0) (aValE y F0.K L u j)
      | none => 0

theorem member_ne {v : ℕ} (hv : v ∈ [55, 56, 57, 58] ++ (qD).ids) {u : ℕ} (hu : u ∈ hV) :
    σH.val u ≠ v := fun h => by
  have := MldsaCarrierHonest.member_none (program := program) v hv
  rw [← h, hOf_val u hu] at this
  cases this

theorem member_neA {v : ℕ} (hv : v ∈ [55, 56, 57, 58] ++ (qD).ids) {u : ℕ} (hu : u ∈ aValues L) :
    σA.val u ≠ v :=
  MldsaCarrierHonest.member_noneA (program := program) v hv u hu

/-- **A held native value's renamed value reads its core honest value.** -/
theorem honestVal_heldH (y : RingIn msgLen) {u : ℕ} (hu : u ∈ hV) (j : ℕ) :
    honestVal program F0 FH y (σH.val u) j = castElt (hValCore nat F0 FH y u j) := by
  have hm := fun v hv => member_ne (program := program) (v := v) hv hu
  unfold honestVal
  rw [if_neg (hm 55 (by simp)), if_neg (hm 56 (by simp)), if_neg (hm 57 (by simp)),
    if_neg (hm 58 (by simp)), if_neg (fun h => hm _ (List.mem_append_right _ h) rfl), hOf_val u hu]

/-- **A held emulated value's renamed value reads its domain `A` honest value.** -/
theorem honestVal_heldA (y : RingIn msgLen) {u : ℕ} (hu : u ∈ aValues L) (j : ℕ) :
    honestVal program F0 FH y (σA.val u) j = castElt (a := 0) (aValE y F0.K L u j) := by
  have hm := fun v hv => member_neA (program := program) (v := v) hv hu
  have huV := MldsaCarrierHonest.aVals (program := program) u (List.mem_append_left _ hu)
  unfold honestVal
  rw [if_neg (hm 55 (by simp)), if_neg (hm 56 (by simp)), if_neg (hm 57 (by simp)),
    if_neg (hm 58 (by simp)), if_neg (fun h => hm _ (List.mem_append_right _ h) rfl),
    hOf_valA u huV, aOf_val u huV]

/-- **The honest value of a member value or a quotient digit**, read in field `0`. -/
theorem honestVal_member (y : RingIn msgLen) (j : ℕ) :
    castElt (b := 0) (honestVal program F0 FH y 55 j) =
        (if j < 4096 then specE y (interp 0).K j else 0) ∧
      castElt (b := 0) (honestVal program F0 FH y 56 j) =
        (if j < 1024 then specE y (interp 0).K (4096 + j) else 0) ∧
      castElt (b := 0) (honestVal program F0 FH y 57 j) = ((muBitNat y.mu j : ℕ) : (interp 0).K) ∧
      castElt (b := 0) (honestVal program F0 FH y 58 j) =
        ((y.w.idx / 2 ^ j % 2 : ℕ) : (interp 0).K) ∧
      ∀ v ∈ (qD).ids, castElt (b := 0) (honestVal program F0 FH y v j) =
        (((qD).digit (quotN y j) v : ℕ) : (interp 0).K) := by
  have hc := MldsaCarrierHonest.member_cells (program := program)
  have hne : ∀ u ∈ [55, 56, 57, 58], ∀ v ∈ (qD).ids, u ≠ v := fun u hu v hv =>
    (List.nodup_append.1 (MldsaCarrierHonest.member_nodup (program := program))).2.2 u hu v hv
  refine ⟨?_, ?_, ?_, ?_, fun v hv => ?_⟩
  · unfold honestVal
    rw [if_pos rfl]
    exact castElt_castElt_of_eq (hc 55 (by simp)).2.symm _
  · unfold honestVal
    rw [if_neg (by decide), if_pos rfl]
    exact castElt_castElt_of_eq (hc 56 (by simp)).2.symm _
  · unfold honestVal
    rw [if_neg (by decide), if_neg (by decide), if_pos rfl]
    exact castElt_castElt_of_eq (hc 57 (by simp)).2.symm _
  · unfold honestVal
    rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_pos rfl]
    exact castElt_castElt_of_eq (hc 58 (by simp)).2.symm _
  · have hv' : v ∈ [55, 56, 57, 58] ++ (qD).ids := List.mem_append_right _ hv
    unfold honestVal
    rw [if_neg (fun h => hne 55 (by simp) v hv h.symm), if_neg (fun h => hne 56 (by simp) v hv h.symm),
      if_neg (fun h => hne 57 (by simp) v hv h.symm), if_neg (fun h => hne 58 (by simp) v hv h.symm),
      if_pos hv]
    exact castElt_castElt_of_eq (hc v hv').2.symm _

end Values

/-! ## The proofs of possession's view of the source environment -/

section Source

variable {program : RealizedProgram} [CarrierHEmbed program] [CarrierAEmbed program]
  [MldsaEAlgebra (CarrierAEmbed.emu program)] [MldsaCarrierHonest program]
  {F0 FH : FieldInterp} [RealizedProgram.PrimeCastField F0 pGold] [HField FH]

set_option hygiene false in
local notation "interp" => mldsaInterpOf F0 FH

set_option hygiene false in
local notation "nat" => CarrierHEmbed.nat program

set_option hygiene false in
local notation "emu" => CarrierAEmbed.emu program

set_option hygiene false in
local notation "L" => MldsaEAlgebra.layout (CarrierAEmbed.emu program)

variable [MldsaHHonest nat] [MldsaHShuffle nat] [MldsaHSelHonest nat] [MldsaHConsts nat FH]
  [MLDSA44.MldsaHNativeData FH]

variable (y : RingIn msgLen) (x : program.Valuation interp) (c : ∀ k, (program.layout interp).Ch k)
  (π : (program.layout interp).Pads)

set_option hygiene false in
local notation "E" => program.srcEnv interp x (honestVal program F0 FH y) c π

/-- **A held native committed value reads its core honest value** in the environment read as
the native program's. -/
theorem reader_heldH {u : ℕ} (hu : u ∈ hV) (hp : (nat).privCellB u = true) {j : ℕ}
    (hj : j < ((nat).value u).size) :
    (nat).reader (pullH E) u j = hValCore nat F0 FH y u j := by
  obtain ⟨-, -, hf, hsz, -⟩ := (CarrierHEmbed.embedding (program := program)).vals u hu
  rw [readerH_pull E hu j, reader_srcEnv_of_privCellB x _ c π
    (MldsaCarrierHonest.privCellH u hu hp) (by rw [hsz]; exact hj), honestVal_heldH y hu j]
  exact castElt_castElt_of_eq hf.symm _

/-- **A native committed value not held reads `0`** in the environment read as the native
program's. -/
theorem reader_unheldH {u : ℕ} (hu : u ∉ hV) (hk : ((nat).value u).kind = .priv) (j : ℕ) :
    (nat).reader (pullH E) u j = 0 := by
  rw [reader_of_priv _ hk]
  simp [pullH, pullEnv, hu]

variable (program F0 FH) in
/-- **The native program's honest valuation** at a ring input: the core's honest values on the
held values, `0` elsewhere. -/
-- spec-side
noncomputable def valNH (u j : ℕ) : (interp ((nat).valueField u)).K :=
  if u ∈ hV then hValCore nat F0 FH y u j else 0

/-- **The environment read as the native program's reads the native honest valuation** on its
committed values of domain `H`. -/
theorem readsCells_pullH : (nat).ReadsCells 1 (pullH E) (valNH program F0 FH y) := by
  intro u j hp _ hj
  unfold valNH
  by_cases hu : u ∈ hV
  · rw [if_pos hu]
    exact reader_heldH y x c π hu hp hj
  · rw [if_neg hu]
    exact reader_unheldH y x c π hu (kind_of_privCellB hp) j

/-- **The native honest valuation at the core's hash values is `hashValCore`.** -/
theorem valH_hash : ∀ v, coreHashB v = true →
    valNH program F0 FH y v = hashValCore (program := nat) (F0 := F0) (FH := FH) y v := by
  intro v hv
  obtain ⟨hw, -⟩ := MLDSA44.wordsOwner_checks
  have hmem : v ∈ hV ∧ MLDSA44.IsHashValue v := by
    rcases coreHashB_cases hv with rfl | rfl | ⟨p, hp, t, rfl⟩
    · exact ⟨(MldsaCarrierHonest.coreV (program := program)).1.1, by
        unfold MLDSA44.IsHashValue; simp⟩
    · exact ⟨(MldsaCarrierHonest.coreV (program := program)).1.2, by
        unfold MLDSA44.IsHashValue; simp⟩
    · refine ⟨(MldsaCarrierHonest.coreV (program := program)).2 p hp t, ?_⟩
      unfold MLDSA44.IsHashValue
      simp [hw p t]
  funext j
  unfold valNH hValCore
  rw [if_pos hmem.1, if_pos hmem.2]

/-- **The native honest valuation at a held value of SampleInBall** is `hValCore`. -/
theorem valH_core {v : ℕ} (hv : v ∈ [556, 557, 560, 561, 562, 563, 564, 565]) :
    valNH program F0 FH y v = hValCore nat F0 FH y v := by
  funext j
  unfold valNH
  rw [if_pos (MldsaCarrierHonest.selV (program := program) v hv)]

theorem valH_556 : ∀ n < 312, castElt (b := 1) (valNH program F0 FH y 556 n) = jFR (K := FH.K) y n := by
  intro n _
  obtain ⟨n7, -, -⟩ := MLDSA44.h_classes
  have h7 := (MldsaHSelHonest.sel_cells (program := nat)).2.2.2.2.2.2.2.2.2.2.1
  rw [valH_core y (by simp)]
  unfold hValCore
  rw [if_neg n7, if_pos rfl]
  exact castElt_castElt_of_eq h7.symm _

theorem valH_557 : ∀ w < 99, castElt (b := 1) (valNH program F0 FH y 557 w) =
    packWord (FH := FH) (lowFR (K := FH.K) y) w := by
  intro w _
  obtain ⟨-, n8, -⟩ := MLDSA44.h_classes
  have h8 := (MldsaHSelHonest.sel_cells (program := nat)).2.2.2.1
  rw [valH_core y (by simp)]
  unfold hValCore
  rw [if_neg n8, if_neg (by decide), if_pos rfl]
  exact castElt_castElt_of_eq h8.symm _

theorem valH_mem : ∀ v, v ∈ [560, 561, 562, 563, 564, 565] → ∀ n < ((nat).value v).size,
    castElt (b := 1) (valNH program F0 FH y v n) = memFR nat F0 FH y v n := by
  intro v hv n _
  obtain ⟨-, -, nm⟩ := MLDSA44.h_classes
  have hf := (MldsaHSelHonest.mem_cells (program := nat)).1 v hv
  have h7 : v ≠ 556 := by rintro rfl; simp at hv
  have h8 : v ≠ 557 := by rintro rfl; simp at hv
  rw [valH_core y (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hv ⊢; omega)]
  unfold hValCore
  rw [if_neg (nm v hv), if_neg h7, if_neg h8, if_pos hv]
  exact castElt_castElt_of_eq hf.2.symm _

/-- **Domain `H`'s core holds at the honest values**: carrier predicate `k − 25` for every native
core predicate `k` (`48 … 270`), by the renaming (`CarrierHEmbed.hPredCorr`, `holdsAt_pullEnv`) at
the native core's honest values (`GordieHowe.MLDSA44.Ring.Native.hPreds_core`). -/
theorem core_holds {k : ℕ} (h48 : 48 ≤ k) (h270 : k ≤ 270) :
    program.HoldsAt E (program.predicate (k - 25)).body :=
  (holdsAt_pullEnv (CarrierHEmbed.embedding (program := program)) E
    (CarrierHEmbed.hPredCorr k h48 h270).1).2
    (hPreds_core y (readsCells_pullH y x c π) (valH_hash y) (valH_556 y) (valH_557 y)
      (valH_mem y) h48 h270)

/-- **A held emulated committed value reads its domain `A` honest value** in the environment read
as the emulated program's. -/
theorem reader_heldA {u : ℕ} (hu : u ∈ aValues L) (hp : (emu).privCellB u = true)
    (hf0 : (emu).valueField u = 0) {j : ℕ} (hj : j < ((emu).value u).size) :
    rdA (pullA E) u j = aValE y F0.K L u j := by
  have huV := MldsaCarrierHonest.aVals (program := program) u (List.mem_append_left _ hu)
  obtain ⟨-, -, hf, hsz, -⟩ := (CarrierAEmbed.embedding (program := program)).vals u huV
  unfold rdA
  rw [evalE_leaf, readerA_pull E huV j, reader_srcEnv_of_privCellB x _ c π
    (MldsaCarrierHonest.privCellA u huV hp) (by rw [hsz]; exact hj), honestVal_heldA y hu j,
    castElt_castElt_eq, if_pos hf, castElt_castElt_of_eq (hf.trans hf0).symm]

variable [MLDSA44.MldsaHSample (MLDSA44.Emulated.MldsaEmbed.nat emu)]
  [MLDSA44.MldsaHConsts (MLDSA44.Emulated.MldsaEmbed.nat emu) FH]
  [MldsaHHonest (MLDSA44.Emulated.MldsaEmbed.nat emu)]
  [MldsaHSelHonest (MLDSA44.Emulated.MldsaEmbed.nat emu)] [MLDSA44.MldsaHNodes FH]
  [hE : MldsaEmulatedHonest emu F0 FH]

/-- **The environment read as the emulated program's reads domain `A`'s honest values.** -/
theorem readsAE_pullA : ReadsAE (pullA E) y where
  cells u hA j hj := by
    obtain ⟨hp, hf⟩ := MldsaEmulatedHonest.a_cells (program := emu) u hA
    exact reader_heldA y x c π hA hp hf hj
  bound u Ex hk hu j := by
    have huV := MldsaCarrierHonest.aVals (program := program) u (List.mem_append_right _ hu)
    have hb := MldsaCarrierHonest.boundExprs (program := program) u hu
    rw [hk] at hb
    simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, List.isEmpty_iff] at hb
    obtain ⟨⟨hop, hnodes⟩, hrefs⟩ := hb
    obtain ⟨-, hl', hf, -, -, -, hkc, -⟩ := (CarrierAEmbed.embedding (program := program)).vals u huV
    rw [hk] at hkc
    have hk' := kindCorr_bound hkc
    have key : (emu).reader (pullA E) u j =
        (emu).evalE ((emu).reader (pullA E)) ((emu).valueField u) Ex j := by
      rw [readerA_pull E huV j, reader_bindAsg_of_boundOk MldsaCarrierHonest.bound rfl hl' hk',
        evalE_rename (CarrierAEmbed.embedding (program := program)) E hop hnodes
          (by simp [hrefs])]
      exact castElt_evalE_of_eq hf
    have hf0 : (emu).valueField u = 0 := by
      have := MldsaEmulatedHonest.boundVals (program := emu) u hu
      exact this.2
    unfold rdA
    rw [evalE_leaf, key]
    exact castElt_evalE_of_eq hf0

/-- **Domain `A`'s gadgets hold at the honest values**: carrier predicate `predMapA k` for every
emulated predicate `k` of `aSource`, by the renaming (`CarrierAEmbed.aPredCorr`,
`holdsAt_pullEnv_body`) at domain `A`'s honest values (`aPredsE`). -/
theorem aSource_holds {k : ℕ} (hk : k ∈ aSource) :
    program.HoldsAt E (program.predicate (predMapA k)).body :=
  (holdsAt_pullEnv_body (CarrierAEmbed.embedding (program := program)) E
    (CarrierAEmbed.aPredCorr k ((by decide : ∀ k ∈ aSource, k ∈ aPreds) k hk)).1).2
    (aPredsE (readsAE_pullA y x c π) hk)

end Source

end GordieHowe.MLDSA44.Ring.Carrier
