-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweNative.Language.ProgramData
public import GordieHoweNative.Language.TableauNums

/-!
# GordieHowe: a domain's tableau check

The numbers of a tableau descriptor (`TableauDesc.nums`): a library tableau's from its key
(`TableauKey.nums`), a Johnson tableau's from its fields, with the mask test. `tableauFitB` is a
domain's two tableau tests at its descriptor's numbers, its field's point domain size and the plan.
The descriptor's certificate has these numbers (`TableauDesc.cert_nums`, Mathlib-side).
-/

@[expose] public section

namespace GordieHowe

open RealizedProgram

/-- **The numbers of a library tableau** (`TableauKey.cert`). -/
def TableauKey.nums : TableauKey → TableauNums
  | .gf128K265R2 => ⟨12, 63, 3722, 2, 63, true, 923, 94114354793⟩
  | .gf128K282R2 => ⟨12, 63, 3955, 2, 63, true, 982, 41166706213⟩
  | .gf128K300R2 => ⟨12, 63, 4203, 2, 63, true, 1044, 50940304454⟩
  | .gf256K339R2 => ⟨12, 128, 4746, 2, 128, true, 1179, 108518123392⟩
  | .fq20K271 => ⟨12, 127, 3799, 1, 127, true, 944, 23020764629⟩
  | .falconNativeROMA => ⟨5, 90, 2369, 2, 90, true, 758, 34023420758⟩
  | .falconRingNativeROMA => ⟨5, 89, 2105, 2, 89, true, 673, 51456804230⟩
  | .gold2K512R2 => ⟨5, 96, 3583, 2, 96, true, 1147, 101777974921⟩
  | .gold4K512 => ⟨6, 201, 4095, 1, 201, true, 1418, 1030262⟩
  | .gold4K512R2 => ⟨6, 175, 4095, 2, 175, true, 1257, 118174498727⟩
  | .gold4K1024 => ⟨6, 214, 8191, 1, 214, true, 2918, 1020592⟩

/-- **The numbers of a Johnson tableau**, with the mask test. -/
def JohnsonDesc.nums (j : JohnsonDesc) : TableauNums :=
  ⟨j.rate, j.nreq, j.blockEnc, j.nrep, j.r, true, j.agree, j.exceptions⟩

/-- **The numbers of a tableau descriptor.** -/
def TableauDesc.nums : TableauDesc → TableauNums
  | .library k => k.nums
  | .johnson j => j.nums

/-- **A domain's tableau tests at its numbers `t`**: the layout facts at its field's point domain
of size `q`, and the plan's Ligero numbers of domain `d` (`false` when the plan has no domain
`d`). -/
def tableauFitB (t : TableauNums) (q : Nat) (P : Export.Plan) (d : Nat) : Bool :=
  t.validB q && ((P.domainAt d).map fun pd => t.matchesB pd.ligero).getD false

end GordieHowe
