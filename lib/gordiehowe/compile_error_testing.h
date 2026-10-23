// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0
//
// GordieHowe tests: the message of the CompileError a build or a compile
// throws, "" when it throws none.
//   error_of(BUILD)        BUILD()
//   compile_error(CS, P)   CS lowered under the profile P and compiled
//                          (compile(System &, CompileProfile))
//   core_error(CS)         CS compiled without lowering
//                          (compile(const System &))

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILE_ERROR_TESTING_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILE_ERROR_TESTING_H_

#include <string>

#include "gordiehowe/system.h"

namespace proofs::gordiehowe {

template <class Build>
std::string error_of(Build &&build) {
  try {
    build();
  } catch (const CompileError &e) {
    return e.what();
  }
  return "";
}

template <class S>
std::string compile_error(S &cs, const CompileProfile &p = {}) {
  return error_of([&] { compile(cs, p); });
}

template <class S>
std::string core_error(const S &cs) {
  return error_of([&] { compile(cs); });
}

}  // namespace proofs::gordiehowe

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILE_ERROR_TESTING_H_
