-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.Program.Transcript.Format
public import GordieHowe.ProofSystem.Program.Transcript.CircuitCodecs
public import GordieHowe.ProofSystem.Ligero.MaskRow.Masked

@[expose] public section

/-!
# Write codecs and challenge readers of Ligero with the prefix-row test

The codecs of every prover message (`SpecWrites`) and the readers of every challenge round
(`SpecReaders`) of Ligero at agreement threshold `A` with the prefix-row test on the committed cells
(`GordieHowe.Ligero.MaskRow.Setup`, either masking), as those of relatively packed Ligero
(`Ligero.Relative.Masked.Setup.writes`, `readers`, `commitWrites`, `commitReaders`, `leafCodec`,
`GordieHowe/ProofSystem/Program/Transcript/CircuitCodecs.lean`, `GordieHowe/ProofSystem/Program/Transcript/Format.lean`) without the batching phase:

* **the proof phase** (`writes`, `readers`): the constraint challenge, its point granted `g`
  stream bytes, the masked responses and the column query (`SpecWrites.ligeroListRadius`,
  `SpecReaders.listRadius`); the prefix-row test reads the opened columns only;
* **the commit rounds** (`commitWrites`, `commitReaders`): the low-degree challenge and response
  (`SpecWrites.ldtCommit`, `SpecReaders.ldtCommit`);
* **the leaves** (`leafCodec`): a tableau column with the two mask entries for untested masks
  (`colCodec`), the column's `R + 1` entries for the mask test;
* the counts (`nLeaves_commitProve`, `nc_commitProve`, `n_commitProve`, `card_queries`).
-/

namespace GordieHowe.Ligero.MaskRow.Setup

open GordieHowe.QROM GordieHowe.IOP GordieHowe.SPBCS SPBCS.Configurations

variable {K ι Q Lin : Type} [Field K] [Fintype K] [DecidableEq K] [Fintype ι] [Fintype Q]
  [Fintype Lin] {N R nQ nL np : ℕ} {C : GordieHowe.RSCode K N}
  {P : Tableau.Parameters (R := R) (nQ := nQ) C} {products : Routing.ProductLayout ι Q}
  {Ctx : Type} (rows : Ctx → Lin → AffineForm K ι) {fb B : ℕ}

omit [Fintype K] [DecidableEq K] [Fintype ι] [Fintype Q] [Fintype Lin] in
/-- At most `N` columns are queried. -/
theorem t_le : (S : Setup C P products Lin nL np) → S.t ≤ N
  | .listRadius S => S.t_le
  | .split S => S.t_le

/-- The tree has `N` leaves, the columns. -/
theorem nLeaves_commitProve (S : Setup C P products Lin nL np) :
    (S.commitProve rows).nLeaves = N := by
  cases S <;> rfl

/-- The commit phase has two rounds after the oracle message: the low-degree challenge and
response. -/
theorem nc_commitProve (S : Setup C P products Lin nL np) : (S.commitProve rows).nc = 2 := by
  cases S <;> rfl

/-- The proof phase has `3` rounds: the constraint challenge, the masked responses and the column
query. -/
theorem n_commitProve (S : Setup C P products Lin nL np) : (S.commitProve rows).n = 3 := by
  cases S <;> rfl

/-- **The verifier queries `t` leaves** at every challenge vector. -/
theorem card_queries (S : Setup C P products Lin nL np)
    (ch : (S.commitProve rows).spec.Challenges) : ((S.commitProve rows).queries ch).card = S.t := by
  cases S with
  | listRadius S => exact UntestedMask.card_queries S rows ch
  | split S => exact MaskTest.card_queries S rows ch

/-- **The codecs of the proof phase** of either masking: the proof phase of Ligero at agreement
threshold `A` (`SpecWrites.ligeroListRadius`: the masked responses). -/
def writes (S : Setup C P products Lin nL np) (FB : Codec.FieldBytes K fb)
    (hA : (9 + N * fb) + (9 + N * fb) ≤ B)
    (hR : (9 + (2 * C.k - 1) * fb) + (9 + (2 * C.k - 1) * fb) ≤ B) :
    SpecWrites (S.commitProve rows).spec B :=
  match S with
  | .listRadius _ => SpecWrites.ligeroListRadius FB hA hR
  | .split _ => SpecWrites.ligeroListRadius FB hA hR

/-- **The codecs of the commit rounds** of either masking: the low-degree responses, one array of
`nrep · k` field elements (`SpecWrites.ldtCommit`). -/
def commitWrites (S : Setup C P products Lin nL np) (FB : Codec.FieldBytes K fb)
    (hB : 9 + S.nrep * C.k * fb ≤ B) : SpecWrites (S.commitProve rows).commitRounds B :=
  match S with
  | .listRadius S => SpecWrites.ldtCommit FB R C.k S.nrep hB
  | .split S => SpecWrites.ldtCommit FB R C.k S.nrep hB

/-- **The leaf codec of a column of either masking**: a column of the encoded rows with the two
mask entries for untested masks (`colCodec`), the column's `nrep + R` entries as one array of
field elements for the mask test (the piece rows are tableau rows, `rowsColCodec`). -/
def leafCodec (S : Setup C P products Lin nL np) (FB : Codec.FieldBytes K fb) :
    Codec (S.commitProve rows).Leaf :=
  match S with
  | .listRadius S => colCodec FB R S.nrep
  | .split S => rowsColCodec FB R S.nrep

/-- A serialized column of either masking has at most the bytes of a column with two mask
entries. -/
theorem length_ser_leafCodec_le (S : Setup C P products Lin nL np) (FB : Codec.FieldBytes K fb)
    (c : (S.commitProve rows).Leaf) :
    ((S.leafCodec rows FB).ser c).length ≤ (9 + (S.nrep + R) * fb) + ((1 + fb) + (1 + fb)) := by
  cases S with
  | listRadius S => exact (length_ser_colCodec FB R S.nrep c).le
  | split S =>
    have h := length_ser_rowsColCodec FB R S.nrep c
    exact h.le.trans (Nat.le_add_right _ _)

/-- **The challenge readers of the proof phase** of either masking: the constraint challenge, its
point granted `g` stream bytes, and the column query (`SpecReaders.listRadius`). -/
def readers (S : Setup C P products Lin nL np) (r : CReader K) (g : ℕ) :
    SpecReaders (S.commitProve rows).spec :=
  match S with
  | .listRadius S => SpecReaders.listRadius r S.t_le g
  | .split S => SpecReaders.listRadius r S.t_le g

/-- **The loads of the proof phase's readers** satisfy `good` when the constraint challenge's
(`nL + nQ` elements) and the column query's do. -/
theorem readers_allLoads (S : Setup C P products Lin nL np) (r : CReader K) (g : ℕ)
    {good : Load → Prop} (hc : good ((CReader.pi nL r).prod (CReader.pi nQ r)).load)
    (hq : good (CReader.choose N S.t (t_le S)).load) : (S.readers rows r g).AllLoads good := by
  cases S with
  | listRadius S =>
    exact SpecReaders.dropMsg_allLoads _ (SpecReaders.twoStage_allLoads _ _ hc hq)
  | split S =>
    exact SpecReaders.dropMsg_allLoads _ (SpecReaders.twoStage_allLoads _ _ hc hq)

/-- **The challenge readers of the commit rounds** of either masking: the low-degree challenges,
`nrep · R` elements (`SpecReaders.ldtCommit`). -/
def commitReaders (S : Setup C P products Lin nL np) (r : CReader K) :
    SpecReaders (S.commitProve rows).commitRounds :=
  match S with
  | .listRadius S => SpecReaders.ldtCommit r R C.k S.nrep
  | .split S => SpecReaders.ldtCommit r R C.k S.nrep

/-- The load of the commit rounds' reader is that of `nrep · R` elements. -/
theorem commitReaders_allLoads (S : Setup C P products Lin nL np) (r : CReader K) :
    (S.commitReaders rows r).AllLoads (· ≤ r.load.nsmul (S.nrep * R)) := by
  cases S <;> exact SpecReaders.ldtCommit_allLoads r _ _ _

end GordieHowe.Ligero.MaskRow.Setup
