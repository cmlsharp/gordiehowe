-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.RealizedProgram.Shapes

public section

namespace GordieHoweTest.Shapes

open GordieHowe GordieHowe.RealizedProgram

/-- A constant and a private value exercise constant-shape rejection. -/
@[expose] def program : RealizedProgram where
  phases := 0
  fields := []
  domains := []
  values := [{ name := "constant", shape := [4], kind := .constant [38, 0, 38, 1], type := .field },
    { name := "private", shape := [4], kind := .priv, type := .field }]
  predicates := []

example : program.shapesB [.kindConstant 0 [38, 0, 38, 1]] = true := by decide +kernel
example : program.shapesB [.kindConstant 0 [38, 0, 39, 1]] = false := by decide +kernel
example : program.shapesB [.kindConstant 0 [38, 0, 38]] = false := by decide +kernel
example : program.shapesB [.kindConstant 1 [38, 0, 38, 1]] = false := by decide +kernel
example : program.shapesB [.kindConstant 2 [38, 0, 38, 1]] = false := by decide +kernel

example : program.shapesB [.phaseCount program.phases] = true := by decide +kernel
example : program.shapesB [.phaseCount (program.phases + 1)] = false := by decide +kernel
example : program.shapesB [.exprTable []] = true := by decide +kernel
example : program.shapesB [.exprTable [.leaf 0, .leaf 0, .leaf 0, .leaf 0]] = false := by
  decide +kernel
example : program.shapesB [.sourcePredicates 7 7] = false := by decide +kernel
/-- A program holds its own values under the identity renaming. -/
@[expose] def selfEmbedding : EmbedData where
  source := program
  vals := [0]
  refs := []
  chals := []
  V := [0]
  R := []

/-- The same part at a wrong image. -/
@[expose] def wrongEmbedding : EmbedData where
  source := program
  vals := [1]
  refs := []
  chals := []
  V := [0]
  R := []

example : program.shapesB [.embedding selfEmbedding] = true := by decide +kernel
example : program.shapesB [.embedding wrongEmbedding] = false := by decide +kernel

/-- The test program with one predicate, the default one, which reads value `0`. -/
@[expose] def defaultPredicateProgram : RealizedProgram :=
  { program with predicates := [default] }

/-- A part listing its first equality at the same predicate of the larger program. -/
@[expose] def equalEmbedding : EmbedData :=
  { selfEmbedding with source := defaultPredicateProgram, equals := [(0, 0)] }

/-- The same equality listed for a part with no predicate: index `0` is out of range in the
smaller program, whose `predicate 0` is still the default predicate. -/
@[expose] def outOfRangeEmbedding : EmbedData :=
  { selfEmbedding with equals := [(0, 0)] }

example : defaultPredicateProgram.shapesB [.embedding equalEmbedding] = true := by decide +kernel
example : defaultPredicateProgram.shapesB [.embedding outOfRangeEmbedding] = false := by
  decide +kernel


/-- An equality whose metadata must be checked separately from its body. -/
@[expose] def headerPredicate : Predicate where
  name := "padding"
  body := .equal 0 (.leaf 0) (.leaf 1) .affine
  reads := [.chal 0]
  degree := [(0, 1)]
  role := .source

@[expose] def headerProgram : RealizedProgram :=
  { program with predicates := [headerPredicate] }

example : headerProgram.shapesB
    [.equalHeader 0 ("padding", [.chal 0], [(0, 1)], .source, some .affine)] = true := by decide +kernel
example : headerProgram.shapesB
    [.equalHeader 0 ("wrong", [.chal 0], [(0, 1)], .source, some .affine)] = false := by decide +kernel
example : headerProgram.shapesB
    [.equalHeader 0 ("padding", [], [(0, 1)], .source, some .affine)] = false := by decide +kernel
example : headerProgram.shapesB
    [.equalHeader 0 ("padding", [.chal 0], [(0, 2)], .source, some .affine)] = false := by decide +kernel
example : headerProgram.shapesB
    [.equalHeader 0 ("padding", [.chal 0], [(0, 1)], .type 0, some .affine)] = false := by decide +kernel
example : headerProgram.shapesB
    [.equalHeader 0 ("padding", [.chal 0], [(0, 1)], .source, some .quadratic)] = false := by decide +kernel
example : headerProgram.shapesB
    [.equalHeader 0 ("padding", [.chal 0], [(0, 1)], .source, none)] = false := by decide +kernel
example : headerProgram.shapesB [.equalParts 0 0 (.leaf 1) (.leaf 0)] = false := by decide +kernel

/-- Small metadata for the test's first value. -/
@[expose] def valueHeader : ValueShape := ⟨0, 0, 4, 0, none, .none, .source⟩

example : program.shapesB [.valueHeader 0 valueHeader, .valueCount 2, .predicateCount 0] = true :=
  by decide +kernel
example : program.shapesB [.valueHeader 0 { valueHeader with domain := 1 }] = false := by decide +kernel
example : program.shapesB [.valueHeader 0 { valueHeader with field := 1 }] = false := by decide +kernel
example : program.shapesB [.valueHeader 0 { valueHeader with size := 5 }] = false := by decide +kernel
example : program.shapesB [.valueHeader 0 { valueHeader with phase := 1 }] = false := by decide +kernel
example : program.shapesB [.valueHeader 0 { valueHeader with node := some ⟨"wrong", 0⟩ }] = false :=
  by decide +kernel
example : program.shapesB [.valueHeader 0 { valueHeader with typeSource := .node }] = false :=
  by decide +kernel
example : program.shapesB [.valueHeader 0 { valueHeader with role := .realization 0 }] = false :=
  by decide +kernel
example : program.shapesB [.valueHeader 2 (program.valueShape 2)] = false := by decide +kernel
example : program.shapesB [.valueCount 3] = false := by decide +kernel
example : program.shapesB [.predicateCount 1] = false := by decide +kernel
example : program.shapesB [.exprCount 0, .domainCount 0, .challengeCount 0] = true := by decide +kernel
example : program.shapesB [.exprCount 1] = false := by decide +kernel
example : program.shapesB [.domainCount 1] = false := by decide +kernel
example : program.shapesB [.challengeCount 1] = false := by decide +kernel
example : headerProgram.shapesB [.predicateRole 0 .source] = true := by decide +kernel
example : headerProgram.shapesB [.predicateRole 0 (.type 0)] = false := by decide +kernel
example : headerProgram.shapesB [.predicateRole 1 .source] = false := by decide +kernel

example : program.shapesB [.statementChecks [], .statementRanges []] = true := by decide +kernel
example : program.shapesB [.statementChecks [⟨"missing", 0, 2, "falcon_key_canonical", [12289]⟩]] = false :=
  by decide +kernel
example : program.shapesB [.statementRanges [(0, 12289)]] = false := by decide +kernel

example : headerProgram.shapesB [.crossPredicates []] = true := by decide +kernel
example : headerProgram.shapesB [.crossPredicates [0]] = false := by decide +kernel

/-- Separated cross-field predicates exercise complete-summary rejection. -/
@[expose] def crossProgram : RealizedProgram :=
  { program with predicates := [
      { name := "first", body := .cross 0 (.leaf 0) 1 (.leaf 1) {} default },
      headerPredicate,
      { name := "last", body := .cross 1 (.leaf 1) 0 (.leaf 0) {} default }] }

example : crossProgram.shapesB [.crossPredicates [0, 2]] = true := by decide +kernel
example : crossProgram.shapesB [.crossPredicates [0]] = false := by decide +kernel
example : crossProgram.shapesB [.crossPredicates [0, 1]] = false := by decide +kernel
example : crossProgram.shapesB [.crossPredicates [0, 0, 2]] = false := by decide +kernel

/-- Packing-node metadata does not determine the declared type. -/
@[expose] def typedProgram : RealizedProgram :=
  { program with values := [
    { name := "field-at-node", shape := [1], kind := .priv, type := .field,
      node := some ⟨"GF(2^16)", 0⟩ },
    { name := "subfield", shape := [1], kind := .priv, type := .sub "GF(2^16)" },
    { name := "expression", shape := [1], kind := .pub (.expr (.leaf 0)), type := .bit }] }

example : typedProgram.shapesB [.valueType 0 .field, .valueType 1 (.sub "GF(2^16)"),
    .valueType 2 .bit, .kindExprEq 2 (.leaf 0)] = true := by decide +kernel
example : typedProgram.shapesB [.valueType 0 (.sub "GF(2^16)")] = false := by decide +kernel
example : typedProgram.shapesB [.valueType 1 (.sub "GF(2^8)")] = false := by decide +kernel
example : typedProgram.shapesB [.valueType 2 .field] = false := by decide +kernel
example : typedProgram.shapesB [.valueType 3 .field] = false := by decide +kernel
example : typedProgram.shapesB [.kindExprEq 2 (.leaf 1)] = false := by decide +kernel
example : typedProgram.shapesB [.kindExprEq 0 (.leaf 0)] = false := by decide +kernel
example : typedProgram.shapesB [.kindExprEq 3 (.leaf 0)] = false := by decide +kernel

/-- Source and realization challenges may have different sampler families. -/
@[expose] def challengeProgram : RealizedProgram :=
  { program with phases := 2, challenges := [
      { name := "gamma", field := 3, phase := 1, size := 2 },
      { name := "alpha", field := 4, phase := 2, sampler := .node "bit", role := .realization 0 },
      { name := "delta", field := 5, phase := 2 }] }

example : challengeProgram.shapesB [.challengeCount 3] = true := by decide +kernel
example : challengeProgram.shapesB [.challengeCount 2] = false := by decide +kernel

example : challengeProgram.shapesB [.sourceChallenges [0, 2], .fullChallenge 0 3 2,
    .fullChallenge 2 5 1] = true := by decide +kernel
example : challengeProgram.shapesB [.sourceChallenges [0]] = false := by decide +kernel
example : challengeProgram.shapesB [.sourceChallenges [0, 1, 2]] = false := by decide +kernel
example : challengeProgram.shapesB [.sourceChallenges [2, 0]] = false := by decide +kernel
example : challengeProgram.shapesB [.sourceChallenges [0, 0, 2]] = false := by decide +kernel
example : challengeProgram.shapesB [.fullChallenge 0 4 2] = false := by decide +kernel
example : challengeProgram.shapesB [.fullChallenge 0 3 1] = false := by decide +kernel
example : challengeProgram.shapesB [.fullChallenge 1 4 1] = false := by decide +kernel
example : challengeProgram.shapesB [.fullChallenge 3 0 1] = false := by decide +kernel

/-- Source ownership is checked for private cells, independently in each field. -/
@[expose] def privateProgram : RealizedProgram :=
  { program with domains := [{ name := "A", field := 1 }, { name := "H", field := 2 }], values := [
    { name := "source", shape := [1], type := .field, kind := .priv, domain := 0 },
    { name := "realized", shape := [1], type := .field, kind := .priv, domain := 1, role := .realization 0 },
    { name := "pad", shape := [1], type := .field, kind := .padCopy 0 "polynomialBits", domain := 0 }] }

example : privateProgram.shapesB [.privateFieldSources 1, .privateFieldSources 3,
    .kindPadCopy 2 0 "polynomialBits"] = true := by decide +kernel
example : privateProgram.shapesB [.privateFieldSources 2] = false := by decide +kernel
example : privateProgram.shapesB [.kindPadCopy 2 1 "polynomialBits"] = false := by decide +kernel
example : privateProgram.shapesB [.kindPadCopy 2 0 "wrong"] = false := by decide +kernel
example : privateProgram.shapesB [.kindPadCopy 0 0 "polynomialBits"] = false := by decide +kernel
example : privateProgram.shapesB [.kindPadCopy 3 0 "polynomialBits"] = false := by decide +kernel

/-! ## Families -/

/-- A family's ids are positions of each row. -/
example : headerProgram.shapesB [.family [[0], [0]] [.predicateRole 0 .source]] = true := by
  decide +kernel
/-- A row at which the template fails rejects the family. -/
example : headerProgram.shapesB [.family [[0], [1]] [.predicateRole 0 .source]] = false := by
  decide +kernel
/-- A position outside a row reads `0`. -/
example : (ShapeClaim.predicateRole 3 .source).atRow [7] matches .predicateRole 0 _ := rfl
/-- A family inside a template fails. -/
example : headerProgram.shapesB [.family [[0]] [.family [[0]] []]] = false := by decide +kernel
/-- An empty family holds vacuously. -/
example : headerProgram.shapesB [.family [] [.valueCount 99]] = true := by decide +kernel

end GordieHoweTest.Shapes
