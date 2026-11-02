// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// The translation-validation certificate (gkr_certificate.h,
// QuadCircuit::take_certificate) on small circuits: each certificate
// describes its circuit (GkrCertificate::mismatch: the inputs are the first
// nodes, every layer is the circuit's, per gate the same multiset of terms,
// each last-layer assertion's wire carries its operand), and one with a
// changed constant index or a moved last-layer wire does not. The
// last-layer assertions the compiler turns into outputs are listed with
// their wires (the certificate's `cert.sched` outputs). With
// GH_GKR_CERT_TEST_DIR set, the certificates are kept there as text and as
// GHC files (the Lean test data, formal/Test/GordieHoweTest/
// GKRCertificate.lean, and the loader's cross-check).

#include <stddef.h>

#include <algorithm>
#include <cstdlib>
#include <fstream>
#include <functional>
#include <memory>
#include <string>
#include <vector>

#include "algebra/fp.h"
#include "circuits/compiler/compiler.h"
#include "circuits/compiler/gkr_certificate.h"
#include "gordiehowe/compiler/ghc.h"
#include "gordiehowe/compiler/ghc_gkr.h"
#include "sumcheck/circuit.h"
#include "gtest/gtest.h"

namespace proofs {
namespace {
typedef Fp<1> Field;
const Field F("18446744073709551557");

using Build = std::function<void(QuadCircuit<Field>&)>;
using Cert = GkrCertificate<Field>;

// The GHC file of CERT with no node table and no entries (ghc_gkr.h's
// sections of `cert`): circuit 0 over F.
std::vector<uint8_t> ghc(const Cert& cert) {
  namespace ghc = gordiehowe::ghc;
  ghc::GkrCore k;
  ghc::gkr_core(k, cert, F);
  const uint64_t p = 18446744073709551557ull;
  std::vector<uint8_t> b(Field::kBytes);
  for (int i = 0; i < 8; ++i) b[i] = uint8_t(p >> (8 * i));
  k.chr = b;
  k.prime = b;
  F.to_bytes_field(b.data(), F.mone());
  k.neg1 = b;
  F.to_bytes_field(b.data(), F.invertf(F.two()));
  k.half = b;
  ghc::File f(ghc::gkr_schema());
  ghc::write_gkr(f, "cert", k, ghc::GkrTable{});
  return f.bytes();
}

// Compiles BUILD, checks that its certificate describes the circuit and that
// one with a changed constant index does not, and writes it.
void export_cert(const std::string& name, const Build& build) {
  const char* d = std::getenv("GH_GKR_CERT_TEST_DIR");
  const std::string dir = d != nullptr && *d ? d : ::testing::TempDir();
  QuadCircuit<Field> q(F);
  build(q);
  auto c = q.mkcircuit(1);
  auto cert = q.take_certificate();
  EXPECT_EQ(cert->mismatch(*c, F), "") << name;
  std::ofstream(dir + "/" + name + ".cert") << cert->text(F);
  {
    const std::vector<uint8_t> b = ghc(*cert);
    std::ofstream(dir + "/" + name + ".ghc", std::ios::binary)
        .write(reinterpret_cast<const char*>(b.data()), std::streamsize(b.size()));
  }
  // A last-layer assertion's wire moved to a wire not carrying its operand.
  if (!cert->last_asserts.empty()) {
    Cert m = *cert;
    const size_t last = m.wires.depths() - 1;
    const uint32_t g = m.last_asserts[0].first;
    m.last_asserts[0].first = g + 1 < m.wires.width(last) ? g + 1 : 0;
    if (m.last_asserts[0].first != g &&
        m.wires.op[m.wires.first_wire[last] + m.last_asserts[0].first] !=
            m.wires.op[m.wires.first_wire[last] + g])
      EXPECT_NE(m.mismatch(*c, F), "") << name;
  }
  ScheduleCert& p = cert->wires;
  for (size_t w = 0; w < p.op.size(); ++w)
    if (!p.copy[w] && p.term_begin[w] < p.term_begin[w + 1]) {
      uint32_t& ki = p.terms[3 * p.term_begin[w]];
      ki = ki == 0 ? 1 : 0;
      EXPECT_NE(cert->mismatch(*c, F), "") << name;
      return;
    }
}

TEST(CertExport, Add) {
  export_cert("add", [](QuadCircuit<Field>& Q) {
    size_t a = Q.input_wire(), b = Q.input_wire(), c = Q.input_wire();
    Q.assert0(Q.sub(Q.add(a, b), c));
  });
}

TEST(CertExport, Mul) {
  export_cert("mul", [](QuadCircuit<Field>& Q) {
    size_t a = Q.input_wire(), b = Q.input_wire(), c = Q.input_wire();
    Q.assert0(Q.sub(Q.mul(a, b), c));
  });
}

TEST(CertExport, Scale) {
  export_cert("scale", [](QuadCircuit<Field>& Q) {
    size_t a = Q.input_wire(), b = Q.input_wire();
    Q.assert0(Q.sub(Q.mul(F.of_scalar(3), a), b));
  });
}

// e is read three layers above its own: copy wires; ab - f is an
// assertion below the last layer.
TEST(CertExport, Copies) {
  export_cert("copies", [](QuadCircuit<Field>& Q) {
    size_t a = Q.input_wire(), b = Q.input_wire(), c = Q.input_wire();
    size_t d = Q.input_wire(), e = Q.input_wire(), f = Q.input_wire();
    size_t ab = Q.mul(a, b);
    Q.assert0(Q.sub(ab, f));
    size_t t = Q.mul(Q.mul(ab, c), d);
    Q.assert0(Q.sub(Q.mul(t, t), e));
  });
}

// mul(b, a) is a CSE hit on mul(a, b).
TEST(CertExport, Cse) {
  export_cert("cse", [](QuadCircuit<Field>& Q) {
    size_t a = Q.input_wire(), b = Q.input_wire(), c = Q.input_wire();
    size_t d = Q.input_wire();
    size_t m1 = Q.mul(a, b), m2 = Q.mul(b, a);
    Q.assert0(Q.sub(Q.mul(m1, c), Q.mul(m2, d)));
  });
}

// Two assertions at the deepest layer, both turned into outputs: the
// certificate lists each with the last-layer wire carrying its operand
// (the schedule's last-layer assertions, `cert.sched`), and both are asserted
// nodes.
TEST(CertExport, LastLayer) {
  auto build = [](QuadCircuit<Field>& Q) {
    size_t a = Q.input_wire(), b = Q.input_wire(), c = Q.input_wire();
    Q.assert0(Q.sub(Q.mul(a, b), c));
    Q.assert0(Q.sub(Q.mul(b, c), a));
  };
  export_cert("lastlayer", build);
  QuadCircuit<Field> q(F);
  build(q);
  auto c = q.mkcircuit(1);
  auto cert = q.take_certificate();
  ASSERT_EQ(cert->last_asserts.size(), 2u);
  const size_t last = cert->wires.depths() - 1;
  const std::vector<uint32_t> as = cert->asserted();
  for (const auto& [g, z] : cert->last_asserts) {
    ASSERT_LT(g, cert->wires.width(last));
    size_t at = 0;
    while (at < cert->node_id.size() && cert->node_id[at] != z) ++at;
    ASSERT_LT(at, cert->node_id.size());
    const uint32_t b = cert->node_term_begin[at];
    ASSERT_EQ(cert->node_term_begin[at + 1], b + 1);
    EXPECT_EQ(cert->node_terms[3 * b], 0u);
    EXPECT_EQ(cert->wires.op[cert->wires.first_wire[last] + g],
              cert->node_terms[3 * b + 2]);
    EXPECT_NE(std::find(as.begin(), as.end(), z), as.end());
  }
  // An assertion below the last layer is no last-layer assertion.
  QuadCircuit<Field> q2(F);
  {
    size_t a = q2.input_wire(), b = q2.input_wire(), d = q2.input_wire();
    size_t ab = q2.mul(a, b);
    q2.assert0(q2.sub(ab, d));
    q2.assert0(q2.sub(q2.mul(q2.mul(ab, ab), ab), d));
  }
  q2.mkcircuit(1);
  auto cert2 = q2.take_certificate();
  EXPECT_EQ(cert2->last_asserts.size(), 1u);
  EXPECT_EQ(cert2->asserted().size(), 2u);
}

// The extra nodes a GKR export names (and every node their terms read) are
// kept in the DAG, though not needed.
TEST(CertExport, ExtraNodes) {
  QuadCircuit<Field> q(F);
  size_t a = q.input_wire(), b = q.input_wire(), c = q.input_wire();
  // S = 3 a, absorbed by the sum: not needed.
  size_t s = q.mul(F.of_scalar(3), a);
  q.assert0(q.sub(q.add(s, b), c));
  q.mkcircuit(1);
  auto cert = q.take_certificate({s});
  EXPECT_NE(std::find(cert->node_id.begin(), cert->node_id.end(), uint32_t(s)),
            cert->node_id.end());
}

// The primitives' folding: a constant and a linear operand peeled by mul, a
// scale, a konst, sums of different depth (one addend by reference), a
// cancelling sum, an assertion through a linear chain, and the axpy and
// apy wrappers.
TEST(CertExport, Folds) {
  export_cert("folds", [](QuadCircuit<Field>& Q) {
    size_t a = Q.input_wire(), b = Q.input_wire(), c = Q.input_wire();
    size_t k3 = Q.konst(F.of_scalar(3));
    size_t s = Q.mul(k3, a);
    size_t l = Q.linear(F.of_scalar(5), b);
    size_t m = Q.mul(l, Q.mul(a, c));
    size_t ab = Q.mul(a, b);
    size_t deep = Q.mul(ab, Q.mul(ab, c));
    size_t sum = Q.add(deep, s);
    size_t z = Q.sub(Q.add(ab, c), c);
    size_t y = Q.axpy(Q.apy(m, F.of_scalar(7)), F.of_scalar(2), sum);
    Q.assert0(Q.sub(z, ab));
    Q.assert0(Q.mul(F.of_scalar(4), Q.sub(y, a)));
    Q.assert0(Q.linear(F.of_scalar(9), Q.sub(sum, b)));
  });
}

// Longfellow's compiler_test.cc circuits.
TEST(CertExport, OutputAnInput) {
  export_cert("output_an_input", [](QuadCircuit<Field>& Q) {
    size_t a = Q.input_wire(), b = Q.input_wire(), c = Q.input_wire();
    Q.output_wire(a, 0);
    Q.output_wire(Q.mul(b, c), 1);
  });
}

TEST(CertExport, AliasOfLinearAndCopyWire) {
  export_cert("alias_linear_copy", [](QuadCircuit<Field>& Q) {
    size_t a = Q.input_wire();
    Q.output_wire(a, 0);
    Q.output_wire(Q.linear(a), 1);
  });
}

TEST(CertExport, Assert0) {
  export_cert("assert0", [](QuadCircuit<Field>& Q) {
    size_t a = Q.input_wire(), b = Q.input_wire(), c = Q.input_wire();
    Q.assert0(Q.sub(Q.add(a, b), c));
  });
}

// canonicalization_test.cc: (a * b) * (c * d), with spurious unused nodes.
TEST(CertExport, Canonicalization) {
  export_cert("canonicalization", [](QuadCircuit<Field>& Q) {
    size_t a = Q.input_wire(), b = Q.input_wire(), c = Q.input_wire();
    size_t d = Q.input_wire();
    size_t cd = Q.mul(c, d);
    size_t ab = Q.mul(b, a);
    Q.add(a, b);
    Q.output_wire(Q.mul(ab, cd), 0);
  });
}

// canonicalization_test.cc's matrix powers, 2 x 2, four products.
TEST(CertExport, MatMul) {
  export_cert("matmul", [](QuadCircuit<Field>& Q) {
    constexpr size_t kN = 2;
    size_t A[kN][kN], B[kN][kN];
    for (size_t i = 0; i < kN; ++i)
      for (size_t j = 0; j < kN; ++j) {
        A[i][j] = Q.input_wire();
        B[i][j] = Q.input_wire();
      }
    for (size_t n = 0; n < 4; ++n) {
      size_t C[kN][kN];
      for (size_t i = 0; i < kN; ++i)
        for (size_t j = 0; j < kN; ++j) {
          size_t s = Q.mul(A[i][0], B[0][j]);
          for (size_t k = 1; k < kN; ++k) s = Q.add(s, Q.mul(A[i][k], B[k][j]));
          C[i][j] = s;
        }
      for (size_t i = 0; i < kN; ++i)
        for (size_t j = 0; j < kN; ++j) A[i][j] = C[i][j];
    }
    size_t nout = 0;
    for (size_t i = 0; i < kN; ++i)
      for (size_t j = 0; j < kN; ++j) Q.output_wire(A[i][j], nout++);
  });
}

// A size ladder for timing the checker: P products of N x N matrices, the
// result asserted equal to an input matrix (about P (N^3 + N^2) quad terms).
void ladder(const std::string& name, size_t kN, size_t P) {
  export_cert(name, [kN, P](QuadCircuit<Field>& Q) {
    std::vector<std::vector<size_t>> A(kN, std::vector<size_t>(kN)), B = A, Y = A;
    for (size_t i = 0; i < kN; ++i)
      for (size_t j = 0; j < kN; ++j) {
        A[i][j] = Q.input_wire();
        B[i][j] = Q.input_wire();
        Y[i][j] = Q.input_wire();
      }
    for (size_t n = 0; n < P; ++n) {
      auto C = A;
      for (size_t i = 0; i < kN; ++i)
        for (size_t j = 0; j < kN; ++j) {
          size_t s = Q.mul(A[i][0], B[0][j]);
          for (size_t k = 1; k < kN; ++k) s = Q.add(s, Q.mul(A[i][k], B[k][j]));
          C[i][j] = s;
        }
      A = C;
    }
    for (size_t i = 0; i < kN; ++i)
      for (size_t j = 0; j < kN; ++j) Q.assert0(Q.sub(A[i][j], Y[i][j]));
  });
}

TEST(CertExport, Ladder) {
  ladder("ladder1k", 6, 4);
  ladder("ladder5k", 10, 5);
  ladder("ladder20k", 16, 5);
  ladder("ladder44k", 20, 5);
}

}  // namespace
}  // namespace proofs
