// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// Application-declared frontend names and honest source roles. These records
// carry no runtime algorithm or certificate witness and enter no digest.
#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_SOURCE_METADATA_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_SOURCE_METADATA_H_

#include <cstddef>
#include <cstdint>
#include <memory>
#include <string>
#include <utility>
#include <vector>

namespace proofs::gordiehowe {

enum class SourceRole {
  kHashWord, kHashBit, kSelection, kAWitness,
  kRingSigma, kCarry, kStmtMember, kInput
};

// One repetition of a repeated gadget: the predicates, shared expressions and
// values whose shapes the family states, in the same order at every repetition.
struct ShapeFamilyRow {
  std::vector<std::string> predicates, exprs, values;
};

// A repeated gadget. The export groups its rows by shape and emits one checked
// family claim per group, in place of named facts for each repetition.
struct ShapeFamilyInput {
  std::string name;
  std::vector<ShapeFamilyRow> rows;
};

struct ValueShapeAlias {
  std::string name;
  size_t node;
};

// A derived handle or an expression DAG node. A weak identity does not alter
// Expr optimizations that inspect shared_ptr::use_count(). The compiled source
// retains live expressions; an alias whose expression expired is rejected.
struct ExprShapeAlias {
  std::string name;
  size_t derived = SIZE_MAX;
  std::weak_ptr<const void> expression;
};

// A structural expression name rooted at one named application value or
// predicate. Paths walk operands or explicitly enter a shared expression;
// no expression-arena or shared-pool index is part of this interface.
struct ShapeExprSelector {
  enum class Root { kValueDefinition, kPredicateLeft, kPredicateRight, kPredicateSet };
  enum class Edge { kFirst, kSecond, kThird, kShared, kArgument };
  struct Step {
    Edge edge;
    size_t argument = 0;
  };
  Root root = Root::kValueDefinition;
  std::string name;
  std::vector<Step> path;
};

struct SelectedShapeNode {
  std::string name;
  ShapeExprSelector selector;
};

// A part of another application's program that this program holds: the
// source program's configuration (at this program's profile), its
// predicates the part holds, by name, each the predicate of the same name
// here (runs of field equalities, by their first and last names, each a
// source predicate here; other bodies), the source's shared expressions the
// frontends read besides (by their coordinates in the source program), and
// the source's values this program holds under another name. The export
// computes the renaming, the part's values and shared expressions and the
// predicate pairs from the two programs (compiler/embedding.h); the
// embedding check reads both programs.
struct ProgramEmbeddingSpec {
  std::string name;
  std::string source_config;
  std::vector<std::pair<std::string, std::string>> equals;
  std::vector<std::string> bodies = {};
  std::vector<ShapeExprSelector> exprs = {};
  // (the source's name, the name here).
  std::vector<std::pair<std::string, std::string>> aliases = {};
};

// Shared by every profile of an application. Names resolve after compilation;
// an absent or ambiguous name is an export error, never a positional fallback.
// A configuration with no names takes the positional ShapeInputs instead.
struct NamedShapeInputs {
  std::vector<std::string> values, predicates, exprs, equal_headers;
  // Semantic value names anchor fields whose private cells must be source-owned.
  std::vector<std::string> private_field_sources;
  // Inclusive runs of predicates, by their first and last names, that must all
  // be valid source predicates.
  std::vector<std::pair<std::string, std::string>> source_predicate_ranges = {};
  std::vector<ProgramEmbeddingSpec> embeddings = {};
  // When set, a checked table of the program's shared expressions up to and
  // including this named expression.
  std::string expr_table_end = {};
  // Whether the frontends read the program's number of challenge phases.
  bool phase_count = false;
  std::vector<ShapeFamilyInput> families = {};
};

// A predicate's stable source meaning disambiguates a source declaration
// from a realization that deliberately retains the same printed name.
struct PredicateShapeSelector {
  enum class Role { kSource, kRealization, kType };
  enum class Body { kEqual, kMem, kMod, kCross };
  std::string name;
  Role role;
  Body body;
};

struct PredicateShapeAlias {
  std::string name;
  PredicateShapeSelector selector;
};

struct SourceRoleDecl {
  size_t node;
  SourceRole role;
  // Semantic witness component, not a realized-program index.
  size_t slot;
};

struct NamedSourceRoleDecl {
  std::string name;
  SourceRole role;
  size_t slot;
};

struct SourceMetadata {
  NamedShapeInputs shapes;
  std::vector<ValueShapeAlias> values;
  std::vector<ExprShapeAlias> exprs;
  std::vector<SelectedShapeNode> selected_exprs;
  std::vector<SelectedShapeNode> selected_values;
  std::vector<PredicateShapeAlias> predicates;
  std::vector<SourceRoleDecl> roles;
  std::vector<NamedSourceRoleDecl> named_roles;
};

}  // namespace proofs::gordiehowe
#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_SOURCE_METADATA_H_
