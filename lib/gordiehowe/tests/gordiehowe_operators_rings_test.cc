// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe tests (gordiehowe_operators_test binary): DISABLED_Timings and
// DISABLED_MACConvTimings.

#include "ec/p256.h"
#include "gordiehowe/tests/gordiehowe_operators_test.h"

namespace proofs::gordiehowe {
namespace {

// --------------------------------------------------------------- timing --

template <class Fn>
double best_ms(Fn fn, int reps) {
  double best = 1e300;
  for (int r = 0; r < reps; ++r) {
    const auto t0 = std::chrono::steady_clock::now();
    fn();
    const auto t1 = std::chrono::steady_clock::now();
    best = std::min(best,
                    std::chrono::duration<double, std::milli>(t1 - t0).count());
  }
  return best;
}
template <class F>
void time_pair(const char *field_name, const char *what,
               const LinearOperator<F> &before, const LinearOperator<F> &after,
               int reps_before) {
  auto x = random_full<F>(after.cols()), y = random_full<F>(after.rows());
  std::vector<typename F::Elt> ox(after.rows()), oy(after.cols());
  const double ba = best_ms([&] { before.apply(x.data(), ox.data()); }, reps_before);
  const double bt =
      best_ms([&] { before.transpose_apply(y.data(), oy.data()); }, reps_before);
  const double aa = best_ms([&] { after.apply(x.data(), ox.data()); }, 7);
  const double at = best_ms([&] { after.transpose_apply(y.data(), oy.data()); }, 7);
  std::printf("%-16s %-24s apply %10.3f -> %8.3f ms   transpose %10.3f -> %8.3f ms\n",
              field_name, what, ba, aa, bt, at);
}

// The carriers' previous operator: emulated_ntt::Plan with a full-field
// spectrum.
template <class F>
class CarrierConvBefore final : public LinearOperator<F> {
  using Elt = typename F::Elt;

 public:
  CarrierConvBefore(const F &f, const std::vector<Elt> &h)
      : f_(f), n_(h.size()), plan_(f, h.size()), s_(h), st_(h.size()) {
    plan_.transform(s_, false);
    st_[0] = h[0];
    for (size_t i = 1; i < n_; ++i) st_[i] = f.negf(h[n_ - i]);
    plan_.transform(st_, false);
  }
  size_t rows() const override { return n_; }
  size_t cols() const override { return n_; }
  void apply(const Elt *x, Elt *y) const override { mul(s_, x, y); }
  void transpose_apply(const Elt *y, Elt *x) const override { mul(st_, y, x); }

 private:
  void mul(const std::vector<Elt> &s, const Elt *x, Elt *y) const {
    std::vector<Elt> a(x, x + n_);
    plan_.transform(a, false);
    for (size_t k = 0; k < n_; ++k) a[k] = f_.mulf(a[k], s[k]);
    plan_.transform(a, true);
    std::copy(a.begin(), a.end(), y);
  }
  const F &f_;
  size_t n_;
  emulated_ntt::Plan<F> plan_;
  std::vector<Elt> s_, st_;
};

template <class F>
void time_field(const char *name) {
  const F &f = field<F>();
  const size_t n = ring_n<F>();
  const auto h = lift<F>(random_mod(n, modulus<F>(), 15));
  if constexpr (kCarrier<F>) {
    time_pair<F>(name, "NegacyclicConv", CarrierConvBefore<F>(f, h),
                 ops::NegacyclicConvOperator<F>(f, h), 7);
  } else {
    time_pair<F>(name, "NegacyclicConv", ops::NegacyclicConvReference<F>(f, h),
                 ops::NegacyclicConvOperator<F>(f, h), 2);
  }
  if constexpr (!kCarrier<F> && !kFalconField<F>) {
    const auto a = lift<F>(random_mod(kK * kL * n, kMLDSAQ, 16));
    time_pair<F>(name, "PolyMatVec 4x4",
                 ops::PolyMatVecOperator<F>(f, kK, kL, n, a,
                                            ops::Form::kCoefficients, nullptr),
                 ops::PolyMatVecOperator<F>(f, kK, kL, n, a, ops::Form::kNtt,
                                            scheme_ntt<F>(n)),
                 1);
  }
}

// MACConv per chunk (its window K): construction, apply and
// transpose_apply, at the MAC sizes of the programs (nch up to the
// post-quantum mDL's 920 chunks of 128 bits).
template <class F, class MF>
void time_mac(const F &f, const char *name, size_t nch) {
  MF mf;
  SecureRandomEngine rng;
  std::vector<typename MF::Elt> r(nch);
  for (auto &v : r) v = rng.elt(mf);
  std::vector<typename F::Elt> x(nch * MF::kBits), y(MF::kBits),
      ox(MF::kBits), oy(nch * MF::kBits);
  for (auto &v : x) v = rng.elt(f);
  for (auto &v : y) v = rng.elt(f);
  std::unique_ptr<ops::MACConvOperator<F, MF>> op;
  const double make = best_ms(
      [&] { op = std::make_unique<ops::MACConvOperator<F, MF>>(f, mf, r); }, 3);
  const double a = best_ms([&] { op->apply(x.data(), ox.data()); }, 5);
  const double t =
      best_ms([&] { op->transpose_apply(y.data(), oy.data()); }, 5);
  std::printf("%-14s w=%3zu nch=%4zu K=%zu make %9.4f  apply %9.4f  "
              "transpose %9.4f ms  (per chunk: %7.2f %7.2f %7.2f us)\n",
              name, MF::kBits, nch, op->window(), make, a, t,
              1e3 * make / nch, 1e3 * a / nch, 1e3 * t / nch);
}
TEST(GordieHoweOperators, DISABLED_MACConvTimings) {
  for (size_t nch : {2, 6, 16, 52, 64, 920}) {
    time_mac<Fp256Base, GF2_128<>>(p256_base, "Fp256Base", nch);
    time_mac<Fp24_6, GF2_128<>>(field<Fp24_6>(), "Fp24_6", nch);
    time_mac<Fp14_9, GF2_128<>>(field<Fp14_9>(), "Fp14_9", nch);
    time_mac<Fp64G2, GF2_128<>>(field<Fp64G2>(), "Fp64G2", nch);
  }
  for (size_t nch : {3, 26, 32, 460}) {
    time_mac<Fp256Base, GF2_256<>>(p256_base, "Fp256Base", nch);
    time_mac<MlDsaField11, GF2_256<>>(field<MlDsaField11>(), "MlDsaField11",
                                      nch);
    time_mac<FalconField18, GF2_256<>>(field<FalconField18>(), "FalconField18",
                                       nch);
    time_mac<Fp64G4, GF2_256<>>(field<Fp64G4>(), "Fp64G4", nch);
  }
}

TEST(GordieHoweOperators, DISABLED_Timings) {
  time_field<Fp64G2>("Fp64G2");
  time_field<Fp64G4>("Fp64G4");
  time_field<Fp14_9>("Fp14_9");
  time_field<FalconField18>("FalconField18");
  time_field<FalconField19>("FalconField19");
  time_field<FalconField20>("FalconField20");
  time_field<FalconField24>("FalconField24");
  time_field<Fp24_6>("Fp24_6");
  time_field<MlDsaField11>("MlDsaField11");
  time_field<MlDsaField12>("MlDsaField12");
}

}  // namespace
}  // namespace proofs::gordiehowe
