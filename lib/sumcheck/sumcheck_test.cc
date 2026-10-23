// Copyright 2026 Google LLC.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
// Modified 2026 by Chad Sharp and Paul Grubbs: tests for constant coefficients and full-field binary evaluation; transcripts take an explicit seed

#include <algorithm>
#include <cstdint>
#include <cstdlib>
#include <memory>
#include <utility>
#include <vector>

#include "algebra/bogorng.h"
#include "algebra/fp.h"
#include "arrays/affine.h"
#include "arrays/dense.h"
#include "gf2k/gf2_128.h"
#include "random/transcript.h"
#include "sumcheck/circuit.h"
#include "sumcheck/equad.h"
#include "sumcheck/prover.h"
#include "sumcheck/quad.h"
#include "sumcheck/quad_builder.h"
#include "sumcheck/verifier.h"
#include "gtest/gtest.h"

namespace proofs {
namespace {
using Field = Fp<4>;
static const Field F(
    "11579208923731619542357098500868790785326998466564056403945758400790883467"
    "1663");
using Elt = typename Field::Elt;

Bogorng<Field> rng(&F);
using index_t = Quad<Field>::index_t;
using ecorner = EQuad<Field>::ecorner;
using quad_corner_t = Quad<Field>::quad_corner_t;

/* From https://eprint.iacr.org/2015/1060.pdf Algorithm 7: Complete,
   projective point addition for prime order j-invariant 0 short
   Weierstrass curves E/Fq : y^2 = x^3 + b.

   X3 = (X1 Y2 + X2 Y1)(Y1 Y2 - 3b Z1 Z2) - 3b(Y1 Z2 + Y2 Z1)(X1 Z2 + X2 Z1)
   Y3 = (Y1 Y2 + 3b Z1 Z2)(Y1 Y2 - 3b Z1 Z2) + 9b X1 X2 (X1 Z2 + X2 Z1)
   Z3 = (Y1 Z2 + Y2 Z1)(Y1 Y2 + 3b Z1 Z2) + 3 X1 X2(X1 Y2 + X2 Y1)
*/

constexpr uint64_t b = 7;
Elt kone = F.one(), k3 = F.of_scalar(3), k3b = F.of_scalar(3 * b),
    k9b = F.of_scalar(9 * b);

void addE(Elt* X3, Elt* Y3, Elt* Z3, const Elt& X1, const Elt& Y1,
          const Elt& Z1, const Elt& X2, const Elt& Y2, const Elt& Z2) {
  // after common-subexpression elimination:
  Elt t0 = F.mulf(X2, Y1);
  Elt t1 = F.mulf(X1, Y2);
  Elt t2 = F.addf(t1, t0);
  Elt t3 = F.mulf(Y1, Y2);
  Elt t4 = F.mulf(Z1, Z2);
  Elt t5 = F.mulf(Y1, Z2);
  Elt t6 = F.mulf(Y2, Z1);
  Elt t7 = F.addf(t5, t6);
  Elt t8 = F.mulf(X1, Z2);
  Elt t9 = F.mulf(X2, Z1);
  Elt t10 = F.addf(t8, t9);
  Elt t11 = F.mulf(X1, X2);
  Elt t12 = F.mulf(k3b, t4);
  Elt t13 = F.addf(t3, t12);
  Elt t14 = F.subf(t3, t12);

  *X3 = F.subf(F.mulf(t2, t14), F.mulf(k3b, F.mulf(t7, t10)));
  *Y3 = F.addf(F.mulf(t13, t14), F.mulf(k9b, F.mulf(t11, t10)));
  *Z3 = F.addf(F.mulf(t7, t13), F.mulf(k3, F.mulf(t11, t2)));
}

/* Rewrite as quadratic forms in two layers:

L2:
   t0 = (Y1 Y2 + 3b Z1 Z2)
   t1 = (X1 Y2 + X2 Y1)
   t2 = (Y1 Y2 - 3b Z1 Z2)
   t3 = (Y1 Z2 + Y2 Z1)
   t4 = (X1 Z2 + X2 Z1)
   t5 = X1 X2

L1:
   X3 = t1 t2 - 3b t3 t4
   Y3 = t0 t2 + 9b t5 t4
   Z3 = t3 t0 + 3 t5 t1
*/

// input wires
enum { wX1, wY1, wZ1, wX2, wY2, wZ2 };

// t[i] implicitly i

// output wires
enum {
  wX3,
  wY3,
  wZ3,
};

struct testquad {
  Elt coef;
  size_t g, l, r;
};

std::unique_ptr<Quad<Field>> sparse_of_testquad(size_t n,
                                                const struct testquad* q) {
  auto S = std::make_unique<EQuad<Field>>(n);

  for (size_t i = 0; i < n; i++) {
    auto l = q[i].l, r = q[i].r;

    // canonicalize to l <= r
    if (l > r) {
      std::swap(l, r);
    }

    S->ec_[i] = ecorner{.g = quad_corner_t(q[i].g),
                        .h = {quad_corner_t(r), quad_corner_t(l)},
                        .v = q[i].coef};
  }

  S->canonicalize(F);
  return QuadBuilder<Field>::compress(S.get(), F);
}

#define NELEM(x) (sizeof(x) / sizeof(x[0]))

std::unique_ptr<Quad<Field>> addE_quad0() {
  testquad Q[] = {
      // X3 = t1 t2 - 3b t3 t4
      {kone, wX3, 1, 2},
      {F.negf(k3b), wX3, 3, 4},

      // Y3 = t0 t2 + 9b t5 t4
      {kone, wY3, 0, 2},
      {k9b, wY3, 5, 4},

      // Z3 = t3 t0 + 3 t5 t1
      {kone, wZ3, 3, 0},
      {k3, wZ3, 5, 1},
  };
  return sparse_of_testquad(NELEM(Q), Q);
}

std::unique_ptr<Quad<Field>> addE_quad1() {
  testquad Q[] = {
      // t0 = (Y1 Y2 + 3b Z1 Z2)
      {kone, 0, wY1, wY2},
      {k3b, 0, wZ1, wZ2},

      // t1 = (X1 Y2 + X2 Y1)
      {kone, 1, wX1, wY2},
      {kone, 1, wX2, wY1},

      // t2 = (Y1 Y2 - 3b Z1 Z2)
      {kone, 2, wY1, wY2},
      {F.negf(k3b), 2, wZ1, wZ2},

      // t3 = (Y1 Z2 + Y2 Z1)
      {kone, 3, wY1, wZ2},
      {kone, 3, wY2, wZ1},

      // t4 = (X1 Z2 + X2 Z1)
      {kone, 4, wX1, wZ2},
      {kone, 4, wX2, wZ1},

      // t5 = X1 X2
      {kone, 5, wX1, wX2},
  };
  return sparse_of_testquad(NELEM(Q), Q);
}

std::unique_ptr<Circuit<Field>> addE_circuit(size_t logc, corner_t nc) {
  std::unique_ptr<Circuit<Field>> c = std::make_unique<Circuit<Field>>();
  *c = Circuit<Field>{
      .nv = 3,  // outputs
      .logv = 2,
      .nc = nc,
      .logc = logc,
      .nl = 2,
  };
  c->l.push_back(Layer<Field>{.nw = 6, .logw = 3, .quad = addE_quad0()});
  c->l.push_back(Layer<Field>{.nw = 6, .logw = 3, .quad = addE_quad1()});

  return c;
}

TEST(Sumcheck, EvalCircuit) {
  size_t logc = 8;
  corner_t nc = 209;
  auto CIRCUIT = addE_circuit(logc, nc);
  auto W = std::make_unique<Dense<Field>>(nc, 6);
  for (corner_t i = 0; i < W->n0_ * W->n1_; ++i) {
    W->v_[i] = rng.next();
  }
  Prover<Field>::inputs in;
  Prover<Field> prover(F);
  auto Wclone = W->clone();
  const Dense<Field>* Wsave = &*Wclone;
  auto V = prover.eval_circuit(&in, CIRCUIT.get(), std::move(Wclone), F);

  EXPECT_EQ(Wclone.get(), nullptr);  // moved to in(nl-1)
  EXPECT_EQ(in[1].get(), Wsave);

  for (corner_t i = 0; i < nc; ++i) {
    Elt Xw, Yw, Zw;
    addE(&Xw, &Yw, &Zw, (W->v_[i + nc * 0]), (W->v_[i + nc * 1]),
         (W->v_[i + nc * 2]), (W->v_[i + nc * 3]), (W->v_[i + nc * 4]),
         (W->v_[i + nc * 5]));

    Elt X3 = V->v_[i + nc * 0], Y3 = (V->v_[i + nc * 1]),
        Z3 = (V->v_[i + nc * 2]);
    EXPECT_EQ(X3, Xw);
    EXPECT_EQ(Y3, Yw);
    EXPECT_EQ(Z3, Zw);
  }

  // create a proof for the side-effect of invoking the constructor/destructor
  // to detect memory leaks
  Proof<Field> P(CIRCUIT->nl);
}

template <class FF>
void check_constant_coefficient_evaluation(const FF& field) {
  using EC = typename EQuad<FF>::ecorner;
  EQuad<FF> expanded(3);
  expanded.ec_[0] = EC{.g = 0, .h = {0, 1}, .v = field.one()};
  expanded.ec_[1] = EC{.g = 0, .h = {1, 2}, .v = field.of_scalar(7)};
  // A zero coefficient represents an assertion, not an omitted term.
  expanded.ec_[2] = EC{.g = 0, .h = {3, 4}, .v = field.zero()};
  Circuit<FF> circuit{};
  circuit.nl = 1;
  circuit.nc = 3;
  circuit.logc = 2;
  circuit.nv = 1;
  circuit.logv = 0;
  circuit.ninputs = 5;
  circuit.l.push_back(Layer<FF>{.nw = 5, .logw = 3,
      .quad = QuadBuilder<FF>::compress(&expanded, field)});
  auto witness = std::make_unique<Dense<FF>>(3, 5);
  for (size_t copy = 0; copy < 3; ++copy) {
    for (size_t wire = 0; wire < 5; ++wire)
      witness->v_[wire * 3 + copy] = field.of_scalar(2 + wire + copy);
    witness->v_[3 * 3 + copy] = field.zero();
  }
  Prover<FF> prover(field);
  typename Prover<FF>::inputs inputs;
  auto output = prover.eval_circuit(&inputs, &circuit, witness->clone(), field);
  ASSERT_NE(output, nullptr);
  circuit.set_optimizations(OptimizationOptions::optimized());
  auto optimized = prover.eval_circuit(&inputs, &circuit, witness->clone(), field);
  ASSERT_NE(optimized, nullptr);
  for (size_t copy = 0; copy < 3; ++copy) {
    auto expected = field.addf(
        field.mulf(witness->v_[copy], witness->v_[3 + copy]),
        field.mulf(field.of_scalar(7),
                   field.mulf(witness->v_[3 + copy], witness->v_[6 + copy])));
    EXPECT_EQ(output->v_[copy], expected);
    EXPECT_EQ(optimized->v_[copy], expected);
  }
  witness->v_[9] = field.one();
  witness->v_[12] = field.one();
  EXPECT_EQ(prover.eval_circuit(&inputs, &circuit, std::move(witness), field), nullptr);
}

TEST(Sumcheck, ConstantCoefficientsPrime) {
  check_constant_coefficient_evaluation(F);
}

TEST(Sumcheck, ConstantCoefficientsBinary) {
  const GF2_128<> field;
  check_constant_coefficient_evaluation(field);
}

TEST(Sumcheck, BinaryEvaluationFullField) {
  const GF2_128<> field;
  using FF = GF2_128<>;
  using EC = EQuad<FF>::ecorner;
  Bogorng<FF> random(&field);
  constexpr size_t copies = 3, wires = 17, outputs = 7, terms = 257;
  EQuad<FF> expanded(terms);
  using Q = Quad<FF>::quad_corner_t;
  for (size_t i = 0; i < terms; ++i) {
    expanded.ec_[i] = EC{.g = Q(i % outputs),
        .h = {Q((i * 3) % wires), Q((i * 11) % wires)},
        .v = (i % 3 == 0) ? field.one() : random.nonzero()};
  }
  Circuit<FF> circuit{};
  circuit.nl = 1;
  circuit.nc = copies;
  circuit.logc = 2;
  circuit.nv = outputs;
  circuit.logv = 3;
  circuit.ninputs = wires;
  circuit.l.push_back(Layer<FF>{.nw = wires, .logw = 5,
      .quad = QuadBuilder<FF>::compress(&expanded, field)});
  auto witness = std::make_unique<Dense<FF>>(copies, wires);
  for (auto& value : witness->v_) value = random.next();
  std::vector<FF::Elt> expected(copies * outputs, field.zero());
  for (const auto& ec : expanded.ec_) {
    for (size_t c = 0; c < copies; ++c) {
      auto value = field.mulf(ec.v, field.mulf(
          witness->v_[copies * ec.h[0] + c],
          witness->v_[copies * ec.h[1] + c]));
      field.add(expected[copies * ec.g + c], value);
    }
  }
  Prover<FF> prover(field);
  for (auto options : {OptimizationOptions::baseline(),
                       OptimizationOptions::optimized()}) {
    circuit.set_optimizations(options);
    Prover<FF>::inputs inputs;
    auto result = prover.eval_circuit(&inputs, &circuit, witness->clone(), field);
    ASSERT_NE(result, nullptr);
    EXPECT_EQ(result->v_, expected);
  }
}

// New enums and functions for Zero Output test
enum { wZ_X1, wZ_Y1, wZ_Z1, wZ_X2, wZ_Y2, wZ_Z2, wZ_X3, wZ_Y3, wZ_Z3, wZ_ONE };

std::unique_ptr<Quad<Field>> addE_zero_quad0() {
  testquad Q[] = {
      // X3_check = t1 t2 - 3b t3 t4 - X3 * ONE
      {kone, 0, 1, 2},
      {F.negf(k3b), 0, 3, 4},
      {F.negf(kone), 0, 6, 9},

      // Y3_check = t0 t2 + 9b t5 t4 - Y3 * ONE
      {kone, 1, 0, 2},
      {k9b, 1, 5, 4},
      {F.negf(kone), 1, 7, 9},

      // Z3_check = t3 t0 + 3 t5 t1 - Z3 * ONE
      {kone, 2, 3, 0},
      {k3, 2, 5, 1},
      {F.negf(kone), 2, 8, 9},
  };
  return sparse_of_testquad(NELEM(Q), Q);
}

std::unique_ptr<Quad<Field>> addE_zero_quad1() {
  testquad Q[] = {
      // t0 = (Y1 Y2 + 3b Z1 Z2)
      {kone, 0, wZ_Y1, wZ_Y2},
      {k3b, 0, wZ_Z1, wZ_Z2},

      // t1 = (X1 Y2 + X2 Y1)
      {kone, 1, wZ_X1, wZ_Y2},
      {kone, 1, wZ_X2, wZ_Y1},

      // t2 = (Y1 Y2 - 3b Z1 Z2)
      {kone, 2, wZ_Y1, wZ_Y2},
      {F.negf(k3b), 2, wZ_Z1, wZ_Z2},

      // t3 = (Y1 Z2 + Y2 Z1)
      {kone, 3, wZ_Y1, wZ_Z2},
      {kone, 3, wZ_Y2, wZ_Z1},

      // t4 = (X1 Z2 + X2 Z1)
      {kone, 4, wZ_X1, wZ_Z2},
      {kone, 4, wZ_X2, wZ_Z1},

      // t5 = X1 X2
      {kone, 5, wZ_X1, wZ_X2},

      // pass through X3, Y3, Z3, ONE
      {kone, 6, wZ_X3, wZ_ONE},
      {kone, 7, wZ_Y3, wZ_ONE},
      {kone, 8, wZ_Z3, wZ_ONE},
      {kone, 9, wZ_ONE, wZ_ONE},
  };
  return sparse_of_testquad(NELEM(Q), Q);
}

std::unique_ptr<Circuit<Field>> addE_zero_circuit(size_t logc, corner_t nc) {
  std::unique_ptr<Circuit<Field>> c = std::make_unique<Circuit<Field>>();
  *c = Circuit<Field>{
      .nv = 3,  // outputs
      .logv = 2,
      .nc = nc,
      .logc = logc,
      .nl = 2,
  };
  c->l.push_back(Layer<Field>{.nw = 10, .logw = 4, .quad = addE_zero_quad0()});
  c->l.push_back(Layer<Field>{.nw = 10, .logw = 4, .quad = addE_zero_quad1()});

  return c;
}

TEST(Sumcheck, ZeroOutput) {
  size_t logc = 4;
  corner_t nc = 10;
  auto CIRCUIT = addE_zero_circuit(logc, nc);
  auto Wprover = std::make_unique<Dense<Field>>(nc, 10);

  for (corner_t i = 0; i < nc; ++i) {
    // Generate random p0 and p1
    Elt X1 = rng.next(), Y1 = rng.next(), Z1 = rng.next();
    Elt X2 = rng.next(), Y2 = rng.next(), Z2 = rng.next();

    Wprover->v_[i + nc * wZ_X1] = X1;
    Wprover->v_[i + nc * wZ_Y1] = Y1;
    Wprover->v_[i + nc * wZ_Z1] = Z1;
    Wprover->v_[i + nc * wZ_X2] = X2;
    Wprover->v_[i + nc * wZ_Y2] = Y2;
    Wprover->v_[i + nc * wZ_Z2] = Z2;

    // Compute p2 = addE(p0, p1)
    Elt X3, Y3, Z3;
    addE(&X3, &Y3, &Z3, X1, Y1, Z1, X2, Y2, Z2);

    Wprover->v_[i + nc * wZ_X3] = X3;
    Wprover->v_[i + nc * wZ_Y3] = Y3;
    Wprover->v_[i + nc * wZ_Z3] = Z3;

    // Force wONE to be 1
    Wprover->v_[i + nc * wZ_ONE] = F.one();
  }

  auto Wverifier = Wprover->clone();

  Proof<Field> proof(CIRCUIT->nl);
  Prover<Field>::inputs in;
  Prover<Field> prover(F);
  auto V = prover.eval_circuit(&in, CIRCUIT.get(), std::move(Wprover), F);

  // Verify that outputs are zero
  for (corner_t i = 0; i < nc * 3; ++i) {
    EXPECT_EQ(V->v_[i], F.zero());
  }

  Transcript tsp((uint8_t*)"test", 4, Transcript::Seed{});
  prover.prove(&proof, nullptr, CIRCUIT.get(), in, tsp);

  const char* why;
  Transcript tsv((uint8_t*)"test", 4, Transcript::Seed{});
  bool ok = Verifier<Field>::verify(&why, CIRCUIT.get(), &proof,
                                    std::move(Wverifier), tsv, F);
  EXPECT_EQ(ok, true);
  EXPECT_EQ(why, "ok");
}

TEST(Sumcheck, Limits) {
  size_t logc = 4;
  corner_t nc = 10;
  auto CIRCUIT = addE_zero_circuit(logc, nc);
  auto Wprover = std::make_unique<Dense<Field>>(nc, 10);
  for (corner_t i = 0; i < nc; ++i) {
    Wprover->v_[i + nc * wZ_ONE] = F.one();
  }
  auto Wverifier = Wprover->clone();
  Proof<Field> proof(CIRCUIT->nl);

  Transcript tsv((uint8_t*)"test", 4, Transcript::Seed{});
  const char* why;

  // Verify failure for too many layers
  CIRCUIT->nl = Circuit<Field>::kMaxLayers + 1;
  EXPECT_FALSE(Verifier<Field>::verify(&why, CIRCUIT.get(), &proof,
                                       Wverifier->clone(), tsv, F));
  EXPECT_STREQ(why, "too many layers");
  CIRCUIT->nl = 2;  // Restore

  CIRCUIT->nc = Circuit<Field>::kMaxCopies + 1;
  EXPECT_FALSE(Verifier<Field>::verify(&why, CIRCUIT.get(), &proof,
                                       Wverifier->clone(), tsv, F));
  EXPECT_STREQ(why, "too many copies");
  CIRCUIT->nc = nc;  // Restore

  CIRCUIT->nv = Circuit<Field>::kMaxOutputs + 1;
  EXPECT_FALSE(Verifier<Field>::verify(&why, CIRCUIT.get(), &proof,
                                       Wverifier->clone(), tsv, F));
  EXPECT_STREQ(why, "too many outputs");
  CIRCUIT->nv = 3;  // Restore
}

}  // namespace
}  // namespace proofs
