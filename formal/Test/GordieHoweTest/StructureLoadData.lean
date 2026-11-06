-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.Realizations.Circuit.LoadNative

public section

/-! # Structure payload regression

The compiler fixture covers all gadget kinds and parts, routes and interval sources, all thirteen
record fields, a long keyed list, optional slots and a named index-map reference.
-/

namespace GordieHoweTest.StructureLoad
open GordieHowe GordieHowe.RealizedProgram

/-- The named index-map reference shared by the binary and literal fixtures. -/
@[expose] def idx0 : IndexMap := []

-- Loaded literal bodies are the interface under test.
@[expose] public section
load_program_ghc "ProgramCertData/Structure.ghc" "c802f0c69ac55cca"
end

namespace Literal
local notation "ℕ" => Nat
@[expose] def records : RealizedProgram.Structure where
  gadgets := [
    { kind := .selectRow, preds := [0, 1], values := [2, 3], params := [4, 5], parts := [.expr (.reindex idx0 (.leaf 3)), .kernel 0 1 2 3 4 5, .stream 2 none, .stream 2 (some 3), .kernelOf 4 5 6] },
    { kind := .spectralProduct, preds := [0, 1], values := [2, 3], params := [4, 5], parts := [] },
    { kind := .selectFirst, preds := [0, 1], values := [2, 3], params := [4, 5], parts := [] },
    { kind := .keccak, preds := [0, 1], values := [2, 3], params := [4, 5], parts := [] },
    { kind := .macSite, preds := [0, 1], values := [2, 3], params := [4, 5], parts := [] },
    { kind := .modField, preds := [0, 1], values := [2, 3], params := [4, 5], parts := [] },
    { kind := .modCommitted, preds := [0, 1], values := [2, 3], params := [4, 5], parts := [] },
    { kind := .modGrouped, preds := [0, 1], values := [2, 3], params := [4, 5], parts := [] },
    { kind := .modDigits, preds := [0, 1], values := [2, 3], params := [4, 5], parts := [] },
    { kind := .modOneDigit, preds := [0, 1], values := [2, 3], params := [4, 5], parts := [] },
    { kind := .lookupTwoSided, preds := [0, 1], values := [2, 3], params := [4, 5], parts := [] },
    { kind := .lookupDigits, preds := [0, 1], values := [2, 3], params := [4, 5], parts := [] },
    { kind := .packedTable, preds := [0, 1], values := [2, 3], params := [4, 5], parts := [] }]
  origins := [(0, ⟨1, 2⟩),
    (3, ⟨4, 5⟩)]
  messages := [(0, 1),
    (1, 2),
    (2, 3),
    (3, 4),
    (4, 5),
    (5, 6),
    (6, 7),
    (7, 8),
    (8, 9),
    (9, 10),
    (10, 11),
    (11, 12),
    (12, 13),
    (13, 14),
    (14, 15),
    (15, 16),
    (16, 17),
    (17, 18),
    (18, 19),
    (19, 20),
    (20, 21),
    (21, 22),
    (22, 23),
    (23, 24),
    (24, 25),
    (25, 26),
    (26, 27),
    (27, 28),
    (28, 29),
    (29, 30),
    (30, 31),
    (31, 32),
    (32, 33),
    (33, 34),
    (34, 35),
    (35, 36),
    (36, 37),
    (37, 38),
    (38, 39),
    (39, 40),
    (40, 41),
    (41, 42),
    (42, 43),
    (43, 44),
    (44, 45),
    (45, 46),
    (46, 47),
    (47, 48),
    (48, 49),
    (49, 50),
    (50, 51),
    (51, 52),
    (52, 53),
    (53, 54),
    (54, 55),
    (55, 56),
    (56, 57),
    (57, 58),
    (58, 59),
    (59, 60),
    (60, 61),
    (61, 62),
    (62, 63),
    (63, 64),
    (64, 65),
    (65, 66),
    (66, 67),
    (67, 68),
    (68, 69),
    (69, 70),
    (70, 71),
    (71, 72),
    (72, 73),
    (73, 74),
    (74, 75),
    (75, 76),
    (76, 77),
    (77, 78),
    (78, 79),
    (79, 80),
    (80, 81),
    (81, 82),
    (82, 83),
    (83, 84),
    (84, 85),
    (85, 86),
    (86, 87),
    (87, 88),
    (88, 89),
    (89, 90),
    (90, 91),
    (91, 92),
    (92, 93),
    (93, 94),
    (94, 95),
    (95, 96),
    (96, 97),
    (97, 98),
    (98, 99),
    (99, 100),
    (100, 101),
    (101, 102),
    (102, 103),
    (103, 104),
    (104, 105),
    (105, 106),
    (106, 107),
    (107, 108),
    (108, 109),
    (109, 110),
    (110, 111),
    (111, 112),
    (112, 113),
    (113, 114),
    (114, 115),
    (115, 116),
    (116, 117),
    (117, 118),
    (118, 119),
    (119, 120),
    (120, 121),
    (121, 122),
    (122, 123),
    (123, 124),
    (124, 125),
    (125, 126),
    (126, 127),
    (127, 128),
    (128, 129),
    (129, 130),
    (130, 131),
    (131, 132),
    (132, 133),
    (133, 134),
    (134, 135),
    (135, 136),
    (136, 137),
    (137, 138),
    (138, 139),
    (139, 140)]
  boundRecs := [(1, 2)]
  memberValues := [(3, 4)]
  routes := [(0, .affine false),
    (1, .affine true),
    (2, .quadratic),
    (3, .batch 1 2),
    (4, .gkr 3 4),
    (5, .realized 5 [6, 7]),
    (6, .realized 8 [])]
  logupHosts := [((1, 2), (3, 4))]
  macHosts := [(5, (6, 7))]
  chalValues := [(8, 9)]
  ivlSources := [(0, .const),
    (1, .opaqueBit),
    (2, .declared 0),
    (3, .shiftRange 1),
    (4, .range 2),
    (5, .quadRoot 3 4),
    (6, .rootSet [5, 6]),
    (7, .rootSet []),
    (8, .prime)]
  tableGadgets := [(1, 2)]
  macRequests := [(3, [4, 5, 6])]
  modRequests := [(7, [8, 9])]
end Literal

open Lean Elab Command in
run_cmd liftTermElabM do
  for (actualName, expectedName) in [(``records, ``Literal.records)] do
    let .defnInfo actual ← getConstInfo actualName | throwError "missing loaded payload"
    let .defnInfo expected ← getConstInfo expectedName | throwError "missing literal"
    unless actual.type == expected.type && actual.value == expected.value do
      throwError "loaded structures changed the literal type or value: {actualName}"

end GordieHoweTest.StructureLoad
