-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweNative.Language.ProgramData
public import GordieHoweNative.Language.TableauCheck
public import GordieHoweNative.ProofSystem.Program.FiguresCheck

/-!
# The figures part at program data

The field and tableau descriptors supply the numbers used by `FigCheck`. The part checks
batch validity, coverage of every packing mask query, split masking, and the figures. Batch
validity uses the structurally recursive product-cell counter so the kernel can evaluate it.
The compiled form shares one cells context across domains, batches and messages; soundness
transports the descriptor checks to the ready data using the checked packing descriptors.
-/

public section

namespace GordieHowe.ProgramData

open RealizedProgram Export Twin

variable (d : ProgramData)

/-- **A domain's numeric figures** at the program reader and the small descriptors. -/
@[expose] def figuresDomain [CellsReader] (i : Nat) : FigCheck.DomainFig where
  N := ForkReader.domainNums d.program i d.plan
    (d.fieldTable.packing.getD (d.fieldTable.domainField i) default)
  t := (d.tableauDesc i).nums
  fb := d.fieldTable.interp.fbN (d.fieldTable.domainField i)
  load := d.fieldTable.interp.loadN (d.fieldTable.domainField i)
  grant := d.fieldTable.interp.grantN (d.fieldTable.domainField i)
  grants := d.figures.grants.getD i {}
  q := d.fieldTable.interp.cardN (d.fieldTable.domainField i)
  Mx := nthOr d.figures.maxArray i
  Lmax := nthOr d.figures.maxRead i
  Lr := nthOr d.figures.restRead i

/-- **The numeric domain figures**, in field-table order. -/
@[expose] def figuresDomains [CellsReader] : List FigCheck.DomainFig :=
  (List.range d.fieldTable.domainFields.length).map (d.figuresDomain ·)

/-- **Every packing mask query used by the figures is covered.** -/
@[expose] def figuresMasksB : Bool :=
  (List.range d.fieldTable.domainFields.length).all fun i =>
    (d.fieldTable.packing.getD (d.fieldTable.domainField i) default).masksCoverB
      (d.program.planPacking d.plan i)

/-- **The figures check at a reader**, including batch validity and mask-query coverage. -/
@[expose] def figuresReaderB [r : CellsReader] : Bool :=
  okB (@CellsReader.batchesWith d.program r Shape.cellsK) && d.figuresMasksB &&
    @FigCheck.figuresB d.program (d.figuresDomains) r.toPReader d.plan.hash
      d.fieldTable.interp.loadN d.fieldTable.interp.cardN d.fieldTable.interp.fbN d.figures

/-- **The figures part in kernel mode**, with the program reader. -/
@[expose] def figuresPartB : Bool :=
  !d.figures.present || @figuresReaderB d (CellsReader.ofProgram d.program)

/-- **The figures part in compiled mode**, with the cells context built once. -/
@[expose] def figuresPartBC : Bool :=
  !d.figures.present || @figuresReaderB d (CellsReader.ofCtx d.program (CellsCtx.build d.program))

end GordieHowe.ProgramData
