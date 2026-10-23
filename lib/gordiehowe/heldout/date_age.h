// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// Held-out program: an age predicate over a parsed date.
//
// The witness is a birth date as ten ASCII bytes "YYYY-MM-DD"; the
// statement is today's date and a minimum age (year, month, day, age). The
// relation parses the date and proves it well formed and old enough:
//   - each of the eight digit characters is a row (character, digit) of the
//     public table of the ten ASCII digits, and both separators are '-';
//   - the year lies in [1900, 2100) and the month in [1, 12];
//   - the day lies in [1, last(month)], last(month) read from a public
//     table of (month, last day) rows (February has 29);
//   - YYYYMMDD <= (year - age) MMDD of today, as a range check of the
//     difference.
// One Goldilocks^2 domain holds everything; every value lies in F_p.

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_HELDOUT_DATE_AGE_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_HELDOUT_DATE_AGE_H_

#include <array>
#include <cstddef>
#include <cstdint>
#include <string>
#include <utility>
#include <vector>

#include "gordiehowe/heldout/heldout_env.h"

namespace proofs::gordiehowe::heldout::date_age {

template <template <class> class F>
struct Statement {
  // Today's year, month and day, and the minimum age.
  F<std::array<uint16_t, 4>> today;
};
template <template <class> class F>
struct Witness {
  // "YYYY-MM-DD".
  F<std::array<uint8_t, 10>> birth;
};

// The positions of the digits in "YYYY-MM-DD", and of the separators.
inline const std::vector<size_t> kDigitAt = {0, 1, 2, 3, 5, 6, 8, 9};
inline const std::vector<size_t> kSeparatorAt = {4, 7};
inline constexpr uint64_t kLastDay[12] = {31, 29, 31, 30, 31, 30,
                                          31, 31, 30, 31, 30, 31};

inline auto relation() {
  return compile<Statement, Witness>(
      compile_profile("date-age"),
      [](GoldSys &cs, Statement<In> st, Witness<In> w) {
        auto &A = cs.domain(gold_profile(), "A");
        const GF &f = A.field();
        const auto chars = A.priv(Subfield<>{}, w.birth);
        const auto today = st.today.values(A);
        // Each digit's value, computed from its character.
        const auto digits = A.priv(
            Subfield<>{}, "digits", Shape{8}, depends_on(chars),
            [](const std::vector<uint64_t> &c) {
              std::vector<uint64_t> d;
              for (size_t at : kDigitAt) d.push_back(c[at] - '0');
              return d;
            });
        // The ASCII digits: rows (character, digit).
        std::vector<GF::Elt> ascii;
        for (uint64_t k = 0; k < 10; ++k) {
          ascii.push_back(f.of_scalar('0' + k));
          ascii.push_back(f.of_scalar(k));
        }
        const auto ascii_rows =
            A.constant("ascii_digits", ascii).reshape({10, 2});
        const auto digit_records = chars.reindex(kDigitAt)
                                       .reshape({8, 1})
                                       .concat(digits.reshape({8, 1}), 1);
        assert_in(digit_records, in_table(cs, "ascii", ascii_rows),
                  "digit_chars");
        assert_zero(chars.reindex(kSeparatorAt) - uint64_t('-'),
                    "separators");
        // from_digits reads the least significant digit first.
        const auto year = digits.slice(0, 4).reverse(0).from_digits(10);
        const auto month = digits.slice(4, 6).reverse(0).from_digits(10);
        const auto day = digits.slice(6, 8).reverse(0).from_digits(10);
        assert_range(year - 1900, 200, "year");
        assert_range(month - 1, 12, "month");
        // The month's last day, and the row (month, last day).
        const auto last = A.priv(Subfield<>{}, "last_day", Shape{1},
                                 depends_on(digits),
                                 [](const std::vector<uint64_t> &d) {
                                   const uint64_t m = 10 * d[4] + d[5];
                                   return std::vector<uint64_t>{
                                       kLastDay[(m - 1) % 12]};
                                 });
        std::vector<GF::Elt> months;
        for (uint64_t m = 1; m <= 12; ++m) {
          months.push_back(f.of_scalar(m));
          months.push_back(f.of_scalar(kLastDay[m - 1]));
        }
        const auto month_rows =
            A.constant("month_lengths", months).reshape({12, 2});
        assert_in(as_expr(month).concat(last),
                  in_table(cs, "months", month_rows), "month_length");
        assert_range(day - 1, 31, "day");
        assert_range(last - day, 31, "day_in_month");
        // Born on or before today's date, AGE years earlier.
        const auto born = 10000 * year + 100 * month + day;
        const auto cutoff = 10000 * (today.slice(0, 1) - today.slice(3, 4)) +
                            100 * today.slice(1, 2) + today.slice(2, 3);
        assert_range(cutoff - born, 1 << 24, "old_enough");
      },
      "heldout-date-age");
}

struct Instance {
  Statement<Value> statement;
  Witness<Value> witness;
};
// BIRTH ("YYYY-MM-DD") against TODAY's year, month, day and the minimum
// AGE.
inline Instance instance(const std::string &birth, uint16_t year,
                         uint16_t month, uint16_t day, uint16_t age) {
  Instance in;
  for (size_t i = 0; i < 10; ++i) in.witness.birth[i] = uint8_t(birth.at(i));
  in.statement.today = {year, month, day, age};
  return in;
}

}  // namespace proofs::gordiehowe::heldout::date_age

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_HELDOUT_DATE_AGE_H_
