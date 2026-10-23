// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: the test side of a compiled relation. RelationSystem holds a
// relation and its system and gives the compiled system and the
// assignments of statement and witness values; each application's *System
// derives from it and adds the conversion of its example values (keys,
// messages, signatures) into those values.

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_SHARED_SYSTEM_TESTING_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_SHARED_SYSTEM_TESTING_H_

#include <memory>
#include <utility>

#include "gordiehowe/relation.h"

namespace proofs::gordiehowe::examples {

// The relation REL over statements ST and witnesses W, compiled into a
// system of type SYS (CS, the relation's own).
template <class SysT, class St, class W>
struct RelationSystem {
  using Sys = SysT;
  using Assignment = typename Sys::Assignment;
  using Compiled = typename Sys::Compiled;

  Relation<St, W> rel;
  Sys &cs;

  explicit RelationSystem(Relation<St, W> r)
      : rel(std::move(r)), cs(rel.template typed<Sys>().system()) {}

  // The relation's compiled system: the relation compiles once.
  std::shared_ptr<const Compiled> compile() const {
    return rel.template typed<Sys>().compiled_ptr();
  }
  const Compiled &compiled() const {
    return rel.template typed<Sys>().compiled();
  }
  Assignment statement(const St &st) const {
    return rel.template typed<Sys>().statement(st);
  }
  Assignment witness(const W &w) const {
    return rel.template typed<Sys>().witness(w);
  }
};

}  // namespace proofs::gordiehowe::examples

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_SHARED_SYSTEM_TESTING_H_
