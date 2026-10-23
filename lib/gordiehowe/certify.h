// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: certificates for inequalities on gadget parameters.
//
// A gadget whose soundness lemma holds under conditions on its parameters
// (public constants such as a digit base or a batch width) states them
// with a certify note. Each is checked when the gadget is declared: a failure is a
// CompileError naming the condition and both sides' values. A condition
// that holds is recorded as a constant node of the system with no
// coordinates, named
//   certify:<name> [<lhs> = <value> <op> <rhs> = <value>]
// so it enters the system digest and the compile report's node list.
//
//   s.note("certify", "norm.column",
//          term("(Wc + 2)(B - 1)", (p.Wc + 2) * (p.B - 1)) < term("q", q), A);
//
// note is a member of the system and its scopes (system.h); A supplies the
// field of the constant node.

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_CERTIFY_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_CERTIFY_H_

#include <string>
#include <utility>

#include "gordiehowe/core.h"

namespace proofs::gordiehowe {

// One side of a condition: its formula in the gadget's symbols and its value.
struct CertTerm {
  std::string text;
  Bound value;
};
inline CertTerm term(std::string text, Bound value) {
  return CertTerm{std::move(text), value};
}

// A condition on two terms: lhs < rhs, lhs <= rhs or lhs == rhs.
struct Condition {
  CertTerm lhs, rhs;
  std::string op;
  bool holds;
  std::string text() const {
    return lhs.text + " = " + bound_str(lhs.value) + " " + op + " " + rhs.text +
           " = " + bound_str(rhs.value);
  }
};
inline Condition operator<(CertTerm a, CertTerm b) {
  const bool h = a.value < b.value;
  return Condition{std::move(a), std::move(b), "<", h};
}
inline Condition operator<=(CertTerm a, CertTerm b) {
  const bool h = a.value <= b.value;
  return Condition{std::move(a), std::move(b), "<=", h};
}
inline Condition operator==(CertTerm a, CertTerm b) {
  const bool h = a.value == b.value;
  return Condition{std::move(a), std::move(b), "==", h};
}

}  // namespace proofs::gordiehowe

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_CERTIFY_H_
