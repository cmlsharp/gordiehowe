// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: the realized program (realized_program.h) as bytes, the
// compile cache's entry. write_program and read_program are inverse:
// read_program(write_program(p)) is p, field for field, and a malformed
// input reads as none (no partial program).

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_REALIZED_PROGRAM_IO_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_REALIZED_PROGRAM_IO_H_

#include <algorithm>
#include <array>
#include <cstddef>
#include <cstdint>
#include <map>
#include <optional>
#include <tuple>
#include <string>
#include <utility>
#include <vector>

#include "gordiehowe/compiler/realized_program.h"

namespace proofs::gordiehowe::ir {

namespace io_internal {

// The bytes' writer: integers as LEB128 varints (seven bits a byte, the
// high bit set on every byte but the last), length-prefixed strings and
// lists.
struct W {
  std::vector<uint8_t> b;
  void u(uint64_t x) {
    while (x >= 0x80) {
      b.push_back(uint8_t(x) | 0x80);
      x >>= 7;
    }
    b.push_back(uint8_t(x));
  }
  void s(const std::string &x) {
    u(x.size());
    b.insert(b.end(), x.begin(), x.end());
  }
  void bytes(const std::vector<uint8_t> &x) {
    u(x.size());
    b.insert(b.end(), x.begin(), x.end());
  }
  template <class T, class Fn>
  void list(const std::vector<T> &v, Fn fn) {
    u(v.size());
    for (const auto &x : v) fn(*this, x);
  }
  void ids(const std::vector<Id> &v) {
    list(v, [](W &w, Id x) { w.u(x); });
  }
  void sizes(const std::vector<size_t> &v) {
    list(v, [](W &w, size_t x) { w.u(x); });
  }
  void strs(const std::vector<std::string> &v) {
    list(v, [](W &w, const std::string &x) { w.s(x); });
  }
};

// The reader: fails (ok = false) instead of reading past the end, and
// bounds every count by the bytes left.
struct R {
  const std::vector<uint8_t> &b;
  size_t at = 0;
  bool ok = true;
  uint64_t u() {
    uint64_t x = 0;
    for (unsigned shift = 0; shift < 64; shift += 7) {
      if (at >= b.size()) {
        ok = false;
        return 0;
      }
      const uint8_t c = b[at++];
      x |= uint64_t(c & 0x7f) << shift;
      if ((c & 0x80) == 0) return x;
    }
    ok = false;
    return 0;
  }
  Id id() { return Id(u()); }
  size_t z() { return size_t(u()); }
  bool flag() { return u() != 0; }
  // A count of items of at least MIN bytes each.
  size_t count(size_t min = 1) {
    const uint64_t n = u();
    if (!ok || n > (b.size() - at) / std::max<size_t>(min, 1)) {
      ok = false;
      return 0;
    }
    return size_t(n);
  }
  std::string s() {
    const size_t n = count();
    if (!ok) return {};
    std::string x(b.begin() + long(at), b.begin() + long(at + n));
    at += n;
    return x;
  }
  std::vector<uint8_t> bytes() {
    const size_t n = count();
    if (!ok) return {};
    std::vector<uint8_t> x(b.begin() + long(at), b.begin() + long(at + n));
    at += n;
    return x;
  }
  template <class T, class Fn>
  void list(std::vector<T> &v, Fn fn, size_t min = 1) {
    const size_t n = count(min);
    v.clear();
    v.reserve(n);
    for (size_t i = 0; ok && i < n; ++i) {
      T x{};
      fn(*this, x);
      v.push_back(std::move(x));
    }
  }
  void ids(std::vector<Id> &v) {
    list(v, [](R &r, Id &x) { x = r.id(); });
  }
  void sizes(std::vector<size_t> &v) {
    list(v, [](R &r, size_t &x) { x = r.z(); });
  }
  void strs(std::vector<std::string> &v) {
    list(v, [](R &r, std::string &x) { x = r.s(); });
  }
  template <class E>
  E e(uint64_t last) {
    const uint64_t x = u();
    if (x > last) ok = false;
    return E(x);
  }
};

inline void put(W &w, const Space &x) {
  w.u(x.full);
  w.s(x.node);
}
inline void get(R &r, Space &x) {
  x.full = r.flag();
  x.node = r.s();
}
inline void put(W &w, const Target &x) {
  w.u(x.kind);
  w.u(x.id);
}
inline void get(R &r, Target &x) {
  x.kind = r.e<Target::Kind>(Target::kRealized);
  x.id = r.id();
}
inline void put(W &w, const Read &x) {
  w.u(x.kind);
  w.u(x.id);
}
inline void get(R &r, Read &x) {
  x.kind = r.e<Read::Kind>(Read::kPad);
  x.id = r.id();
}
inline void put_degree(W &w, const std::vector<std::pair<Id, size_t>> &d) {
  w.list(d, [](W &w2, const std::pair<Id, size_t> &x) {
    w2.u(x.first);
    w2.u(x.second);
  });
}
inline void get_degree(R &r, std::vector<std::pair<Id, size_t>> &d) {
  r.list(d, [](R &r2, std::pair<Id, size_t> &x) {
    x.first = r2.id();
    x.second = r2.z();
  }, 1);
}
inline void put(W &w, const RealRef &x) {
  w.u(x.kind);
  w.u(x.a);
  w.u(x.b);
  w.s(x.name);
}
inline void get(R &r, RealRef &x) {
  x.kind = r.e<RealRef::Kind>(RealRef::kUnmodeled);
  x.a = r.id();
  x.b = r.id();
  x.name = r.s();
}

inline void put(W &w, const Expr &x) {
  w.u(x.op);
  w.u(uint64_t(x.logic));
  w.u(x.x);
  w.u(x.a);
  w.u(x.b);
  w.u(x.c);
  w.ids(x.args);
  w.u(x.n);
}
inline void get(R &r, Expr &x) {
  x.op = r.e<Expr::Op>(Expr::kLogic);
  x.logic = r.e<LogicOp>(uint64_t(LogicOp::kAll));
  x.x = r.u();
  x.a = r.id();
  x.b = r.id();
  x.c = r.id();
  r.ids(x.args);
  x.n = r.z();
}

inline void put(W &w, const NamedOp &x) {
  w.u(x.kind);
  w.u(x.value);
  w.sizes(x.nats);
  w.s(x.elt);
  w.u(x.ntt_form);
  w.u(x.natural_order);
  w.sizes(x.taps);
  w.u(x.inner);
}
inline void get(R &r, NamedOp &x) {
  x.kind = r.e<NamedOp::Kind>(NamedOp::kBatched);
  x.value = r.id();
  r.sizes(x.nats);
  x.elt = r.s();
  x.ntt_form = r.flag();
  x.natural_order = r.flag();
  r.sizes(x.taps);
  x.inner = r.id();
}

inline void put(W &w, const Value &x) {
  w.s(x.name);
  w.u(x.domain);
  w.u(x.field);
  w.sizes(x.shape);
  w.u(x.kind);
  w.u(uint64_t(x.type));
  w.s(x.sub);
  w.u(x.phase);
  w.s(x.node);
  w.u(uint64_t(x.type_source));
  w.u(x.type_pred);
  w.list(x.reads, [](W &w2, const Read &y) { put(w2, y); });
  put(w, x.pad_space);
  put_degree(w, x.degree);
  w.s(x.bound);
  w.u(x.owner);
  w.s(x.opaque);
  w.ids(x.args);
  w.u(x.expr);
  w.strs(x.entries);
  w.u(x.ref);
  w.u(x.select);
  w.u(x.cnode);
  w.ids(x.sources);
  w.s(x.unmodeled);
}
inline void get(R &r, Value &x) {
  x.name = r.s();
  x.domain = r.id();
  x.field = r.id();
  r.sizes(x.shape);
  x.kind = r.e<Value::Kind>(Value::kBound);
  x.type = r.e<VType>(uint64_t(VType::kField));
  x.sub = r.s();
  x.phase = r.z();
  x.node = r.s();
  x.type_source = r.e<Value::TypeSource>(uint64_t(Value::TypeSource::kPred));
  x.type_pred = r.id();
  r.list(x.reads, [](R &r2, Read &y) { get(r2, y); }, 1);
  get(r, x.pad_space);
  get_degree(r, x.degree);
  x.bound = r.s();
  x.owner = r.id();
  x.opaque = r.s();
  r.ids(x.args);
  x.expr = r.id();
  r.strs(x.entries);
  x.ref = r.id();
  x.select = r.id();
  x.cnode = r.id();
  r.ids(x.sources);
  x.unmodeled = r.s();
}

inline void put(W &w, const Predicate &x) {
  w.s(x.name);
  w.u(x.body);
  w.u(x.domain);
  w.u(x.dy);
  w.u(x.lhs);
  w.u(x.rhs);
  put(w, x.target);
  w.s(x.range);
  w.u(x.set);
  // in
  w.u(x.in.implied);
  w.s(x.in.lo);
  w.s(x.in.hi);
  const LookupRealization &l = x.in.lookup;
  w.u(l.table);
  w.u(l.group);
  w.u(uint64_t(l.kind));
  w.u(l.digits);
  w.s(l.base);
  w.ids(l.digit_values);
  w.ids(l.second);
  w.ids(l.needles);
  w.s(l.honest);
  w.s(l.max);
  // mod
  w.s(x.q);
  const ModRealization &m = x.mod;
  w.u(uint64_t(m.form));
  w.u(m.has_interval);
  w.s(m.lhs_lo);
  w.s(m.lhs_hi);
  w.s(m.rhs_lo);
  w.s(m.rhs_hi);
  w.s(m.quotient_lo);
  w.s(m.qmax);
  w.u(m.quotient);
  w.ids(m.digits);
  w.s(m.radix);
  w.ids(m.ranges);
  w.list(m.bounds, [](W &w2, const std::array<Nat, 3> &y) {
    for (const auto &z : y) w2.s(z);
  });
  w.u(m.grouped.has_value());
  if (m.grouped) {
    const GroupedMod &g = *m.grouped;
    w.s(g.base);
    w.u(g.digit_count);
    w.list(g.groups, [](W &w2, const std::pair<size_t, size_t> &y) {
      w2.u(y.first);
      w2.u(y.second);
    });
    w.s(g.group_bound);
    w.u(g.group_digits);
    w.u(g.residues);
    w.u(g.accumulators);
  }
  w.u(m.target.has_value());
  if (m.target) put(w, *m.target);
  w.s(m.span);
  // cross
  w.u(x.width);
  const MacRealization &c = x.mac;
  w.u(c.mac_field);
  w.u(c.key);
  w.u(c.blind);
  w.u(c.blind_x);
  w.u(c.tag);
  w.u(c.h_predicate);
  w.u(c.chunks);
  w.u(c.width);
  w.ids(c.accumulators);
  w.ids(c.quotient_digits);
  w.list(x.reads, [](W &w2, const Read &y) { put(w2, y); });
  put_degree(w, x.degree);
  w.u(uint64_t(x.role));
  w.u(x.owner);
  w.ids(x.values);
  w.u(x.needles);
  w.u(x.size);
  w.u(x.origin.kind);
  w.u(x.origin.domain);
  w.u(x.origin.index);
  w.s(x.unmodeled);
}
inline void get(R &r, Predicate &x) {
  x.name = r.s();
  x.body = r.e<Predicate::Body>(Predicate::kCross);
  x.domain = r.id();
  x.dy = r.id();
  x.lhs = r.id();
  x.rhs = r.id();
  get(r, x.target);
  x.range = r.s();
  x.set = r.id();
  x.in.implied = r.flag();
  x.in.lo = r.s();
  x.in.hi = r.s();
  LookupRealization &l = x.in.lookup;
  l.table = r.id();
  l.group = r.id();
  l.kind = r.e<LookupKind>(uint64_t(LookupKind::kComplement));
  l.digits = r.z();
  l.base = r.s();
  r.ids(l.digit_values);
  r.ids(l.second);
  r.ids(l.needles);
  l.honest = r.s();
  l.max = r.s();
  x.q = r.s();
  ModRealization &m = x.mod;
  m.form = r.e<ModForm>(uint64_t(ModForm::kInteger));
  m.has_interval = r.flag();
  m.lhs_lo = r.s();
  m.lhs_hi = r.s();
  m.rhs_lo = r.s();
  m.rhs_hi = r.s();
  m.quotient_lo = r.s();
  m.qmax = r.s();
  m.quotient = r.id();
  r.ids(m.digits);
  m.radix = r.s();
  r.ids(m.ranges);
  r.list(m.bounds, [](R &r2, std::array<Nat, 3> &y) {
    for (auto &z : y) z = r2.s();
  }, 1);
  if (r.flag()) {
    GroupedMod g;
    g.base = r.s();
    g.digit_count = r.z();
    r.list(g.groups, [](R &r2, std::pair<size_t, size_t> &y) {
      y.first = r2.z();
      y.second = r2.z();
    }, 1);
    g.group_bound = r.s();
    g.group_digits = r.id();
    g.residues = r.id();
    g.accumulators = r.id();
    m.grouped = std::move(g);
  }
  if (r.flag()) {
    Target t;
    get(r, t);
    m.target = t;
  }
  m.span = r.s();
  x.width = r.z();
  MacRealization &c = x.mac;
  c.mac_field = r.id();
  c.key = r.id();
  c.blind = r.id();
  c.blind_x = r.id();
  c.tag = r.id();
  c.h_predicate = r.id();
  c.chunks = r.z();
  c.width = r.z();
  r.ids(c.accumulators);
  r.ids(c.quotient_digits);
  r.list(x.reads, [](R &r2, Read &y) { get(r2, y); }, 1);
  get_degree(r, x.degree);
  x.role = r.e<Predicate::Role>(uint64_t(Predicate::Role::kType));
  x.owner = r.id();
  r.ids(x.values);
  x.needles = r.z();
  x.size = r.z();
  x.origin.kind = r.e<Origin::Kind>(Origin::kCross);
  x.origin.domain = r.id();
  x.origin.index = r.u();
  x.unmodeled = r.s();
}

// The index maps' storage form: each map a sequence of items (base, shape)
// over one shape table shared by all maps. A shape is an arithmetic run
// (step, count), or a family: a head of items, with bases relative to the
// first, repeated `times` times, copy t shifted by t * delta. The writer
// finds the runs, then repeatedly folds the shortest periodic block of
// items (at most kMapPeriod items) into a family; a head's shapes precede
// the family in the table.
inline constexpr size_t kMapPeriod = 64;
inline uint64_t zig(long long s) {
  return s < 0 ? (uint64_t(-(s + 1)) << 1) | 1 : uint64_t(s) << 1;
}
inline long long unzig(uint64_t z) {
  return (z & 1) ? -(long long)(z >> 1) - 1 : (long long)(z >> 1);
}
struct MapShape {
  bool family = false;
  long long step = 0;
  uint64_t count = 0;
  std::vector<std::pair<long long, size_t>> head;
  uint64_t times = 0;
  long long delta = 0;
  // The number of entries the shape expands to, and its nesting depth.
  uint64_t size = 0;
  size_t depth = 0;
  bool operator<(const MapShape &o) const {
    return std::tie(family, step, count, head, times, delta) <
           std::tie(o.family, o.step, o.count, o.head, o.times, o.delta);
  }
};
using MapItems = std::vector<std::pair<long long, size_t>>;

inline void put_index_maps(W &w, const std::vector<std::vector<size_t>> &maps) {
  std::vector<MapShape> shapes;
  std::map<MapShape, size_t> index;
  auto intern = [&](MapShape s) {
    auto it = index.find(s);
    if (it != index.end()) return it->second;
    shapes.push_back(s);
    return index[std::move(s)] = shapes.size() - 1;
  };
  std::vector<MapItems> seqs;
  for (const auto &m : maps) {
    MapItems seq;
    for (size_t i = 0; i < m.size();) {
      const long long step =
          i + 1 < m.size() ? (long long)m[i + 1] - (long long)m[i] : 0;
      size_t j = i + 1;
      while (j < m.size() && (long long)m[j] - (long long)m[j - 1] == step) ++j;
      MapShape run;
      run.step = step;
      run.count = j - i;
      seq.push_back({(long long)m[i], intern(run)});
      i = j;
    }
    for (bool folded = true; folded;) {
      folded = false;
      MapItems out;
      for (size_t i = 0; i < seq.size();) {
        size_t k = 1, t = 0;
        for (; k <= std::min(kMapPeriod, (seq.size() - i) / 2); ++k) {
          if (seq[i + k].second != seq[i].second) continue;
          const long long d = seq[i + k].first - seq[i].first;
          for (t = 1; i + (t + 1) * k <= seq.size(); ++t) {
            bool same = true;
            for (size_t q = 0; q < k && same; ++q)
              same = seq[i + t * k + q].second == seq[i + q].second &&
                     seq[i + t * k + q].first - seq[i + q].first ==
                         d * (long long)t;
            if (!same) break;
          }
          if (t >= 2) break;
        }
        if (t < 2) {
          out.push_back(seq[i]);
          ++i;
          continue;
        }
        MapShape fam;
        fam.family = true;
        fam.times = t;
        fam.delta = seq[i + k].first - seq[i].first;
        for (size_t q = 0; q < k; ++q)
          fam.head.push_back({seq[i + q].first - seq[i].first, seq[i + q].second});
        out.push_back({seq[i].first, intern(std::move(fam))});
        i += k * t;
        folded = true;
      }
      seq.swap(out);
    }
    seqs.push_back(std::move(seq));
  }
  w.list(shapes, [](W &w2, const MapShape &s) {
    w2.u(s.family);
    if (!s.family) {
      w2.u(zig(s.step));
      w2.u(s.count);
      return;
    }
    w2.list(s.head, [](W &w3, const std::pair<long long, size_t> &h) {
      w3.u(zig(h.first));
      w3.u(h.second);
    });
    w2.u(s.times);
    w2.u(zig(s.delta));
  });
  w.list(seqs, [](W &w2, const MapItems &seq) {
    w2.list(seq, [](W &w3, const std::pair<long long, size_t> &x) {
      w3.u(zig(x.first));
      w3.u(x.second);
    });
  });
}

// Reads the maps; a head naming a shape at or after its family, a family
// nested more than 64 deep, or a map of more than 2^34 entries, is
// malformed.
inline void get_index_maps(R &r, std::vector<std::vector<size_t>> &maps) {
  constexpr uint64_t kMax = uint64_t(1) << 34;
  std::vector<MapShape> shapes;
  r.list(shapes, [](R &r2, MapShape &s) {
    s.family = r2.flag();
    if (!s.family) {
      s.step = unzig(r2.u());
      s.count = r2.u();
      return;
    }
    r2.list(s.head, [](R &r3, std::pair<long long, size_t> &h) {
      h.first = unzig(r3.u());
      h.second = r3.z();
    }, 2);
    s.times = r2.u();
    s.delta = unzig(r2.u());
  }, 2);
  for (size_t k = 0; r.ok && k < shapes.size(); ++k) {
    MapShape &s = shapes[k];
    if (!s.family) {
      s.size = s.count;
    } else {
      uint64_t h = 0;
      for (const auto &x : s.head) {
        if (x.second >= k) r.ok = false;
        if (!r.ok) break;
        h += shapes[x.second].size;
        s.depth = std::max(s.depth, shapes[x.second].depth + 1);
        if (h > kMax || s.depth > 64) r.ok = false;
      }
      if (r.ok && s.times > 0 && h > kMax / s.times) r.ok = false;
      s.size = h * s.times;
    }
    if (s.size > kMax) r.ok = false;
  }
  if (!r.ok) return;
  std::vector<MapItems> seqs;
  r.list(seqs, [](R &r2, MapItems &seq) {
    r2.list(seq, [](R &r3, std::pair<long long, size_t> &x) {
      x.first = unzig(r3.u());
      x.second = r3.z();
    }, 2);
  });
  if (!r.ok) return;
  struct Expand {
    const std::vector<MapShape> &shapes;
    std::vector<size_t> &out;
    void operator()(long long base, size_t k) const {
      const MapShape &s = shapes[k];
      if (!s.family) {
        for (uint64_t c = 0; c < s.count; ++c)
          out.push_back(size_t(base + s.step * (long long)c));
        return;
      }
      for (uint64_t t = 0; t < s.times; ++t)
        for (const auto &h : s.head)
          (*this)(base + s.delta * (long long)t + h.first, h.second);
    }
  };
  maps.assign(seqs.size(), {});
  for (size_t m = 0; r.ok && m < seqs.size(); ++m) {
    uint64_t n = 0;
    for (const auto &x : seqs[m]) {
      if (x.second >= shapes.size() || shapes[x.second].size > kMax - n) {
        r.ok = false;
        break;
      }
      n += shapes[x.second].size;
    }
    if (!r.ok) break;
    maps[m].reserve(size_t(n));
    const Expand expand{shapes, maps[m]};
    for (const auto &x : seqs[m]) expand(x.first, x.second);
  }
}

}  // namespace io_internal

// The format's tag and version; bumped when the layout changes.
inline constexpr uint64_t kProgramFormat = 7;

inline std::vector<uint8_t> write_program(const Program &p) {
  using namespace io_internal;
  W w;
  w.s("gordiehowe-realized-program");
  w.u(kProgramFormat);
  w.u(p.phases);
  w.u(p.msg_len);
  w.u(p.ctx_len);
  w.list(p.checks, [](W &w2, const MemberCheck &c) {
    w2.s(c.member);
    w2.u(c.offset);
    w2.u(c.bytes);
    w2.s(c.check);
    w2.list(c.args, [](W &w3, uint64_t a) { w3.u(a); });
  });
  w.list(p.fields, [](W &w2, const FieldDecl &f) {
    w2.s(f.name);
    w2.s(f.characteristic);
    w2.u(f.degree);
  });
  w.list(p.domains, [](W &w2, const DomainDecl &d) {
    w2.s(d.name);
    w2.u(d.field);
  });
  w.list(p.values, [](W &w2, const Value &v) { put(w2, v); });
  w.ids(p.exprs);
  w.list(p.predicates, [](W &w2, const Predicate &q) { put(w2, q); });
  w.list(p.tables, [](W &w2, const Table &t) {
    w2.s(t.name);
    w2.u(t.domain);
    w2.s(t.size);
    w2.u(t.rows_expr);
    w2.u(t.alpha);
    w2.list(t.groups, [](W &w3, const TableGroup &g) {
      w3.u(g.capacity);
      w3.u(g.static_mult);
      w3.u(g.late_mult);
      w3.u(g.merged);
      w3.list(g.members, [](W &w4, const std::array<size_t, 4> &m) {
        for (size_t x : m) w4.u(x);
      });
    });
  });
  w.list(p.challenges, [](W &w2, const Challenge &c) {
    w2.s(c.name);
    w2.u(c.field);
    w2.u(c.phase);
    w2.u(c.size);
    w2.u(uint64_t(c.sampler));
    w2.s(c.node);
    w2.s(c.tmax);
    w2.u(uint64_t(c.role));
    w2.u(c.owner);
  });
  w.list(p.messages, [](W &w2, const Message &m) {
    w2.u(m.value);
    w2.u(m.domain);
    w2.u(m.field);
    w2.u(m.phase);
    w2.u(m.size);
    put(w2, m.space);
    w2.u(m.subfield_message);
    w2.s(m.pad);
  });
  w.list(p.batches, [](W &w2, const Batch &b) {
    w2.s(b.name);
    w2.u(b.domain);
    w2.u(b.bit_operands);
    w2.u(b.degree);
    w2.u(b.instances);
    w2.u(b.width);
    w2.u(b.rounds);
    w2.u(b.pads);
    w2.u(b.bit_sumcheck);
    w2.u(b.char2);
    w2.ids(b.parts);
  });
  w.list(p.circuits, [](W &w2, const Circuit &c) {
    w2.s(c.name);
    w2.u(c.domain);
    w2.ids(c.predicates);
    w2.list(c.entries, [](W &w3, const CircuitEntry &e) {
      w3.u(e.kind);
      w3.u(e.id);
      put(w3, e.real);
    });
    w2.list(c.inputs, [](W &w3, const InputBlock &b) {
      w3.u(b.kind);
      w3.u(b.value);
      put(w3, b.real);
      w3.u(b.at);
      w3.u(b.n);
      w3.s(b.name);
    });
    for (size_t x : {c.public_inputs, c.input_count, c.layers, c.wires, c.terms})
      w2.u(x);
  });
  w.list(p.realization_circuits, [](W &w2, const std::pair<RealRef, Id> &x) {
    put(w2, x.first);
    w2.u(x.second);
  });
  w.list(p.convs, [](W &w2, const SpectralConv &c) {
    for (uint64_t x : {uint64_t(c.source), uint64_t(c.read), uint64_t(c.products),
                       uint64_t(c.blocks), uint64_t(c.left), uint64_t(c.right),
                       uint64_t(c.length)})
      w2.u(x);
    w2.s(c.root);
  });
  w.list(p.realizations, [](W &w2, const DomainRealization &d) {
    w2.bytes(d.decisions);
    w2.bytes(d.circuit);
  });
  w.strs(p.unmodeled);
  w.list(p.nodes, [](W &w2, const Expr &x) { put(w2, x); });
  put_index_maps(w, p.index_maps);
  w.strs(p.index_map_forms);
  w.list(p.coefs, [](W &w2, const Coef &c) {
    w2.u(c.is_const);
    w2.s(c.c);
    w2.u(c.v);
    w2.u(c.i);
  });
  w.list(p.ops, [](W &w2, const NamedOp &o) { put(w2, o); });
  w.list(p.linears, [](W &w2, const LinearRows &rows) {
    w2.list(rows, [](W &w3, const std::vector<std::pair<size_t, Id>> &row) {
      w3.list(row, [](W &w4, const std::pair<size_t, Id> &e) {
        w4.u(e.first);
        w4.u(e.second);
      });
    });
  });
  return std::move(w.b);
}

inline std::optional<Program> read_program(const std::vector<uint8_t> &b) {
  using namespace io_internal;
  R r{b};
  Program p;
  if (r.s() != "gordiehowe-realized-program" || r.u() != kProgramFormat)
    return std::nullopt;
  p.phases = r.z();
  p.msg_len = r.z();
  p.ctx_len = r.z();
  r.list(p.checks, [](R &r2, MemberCheck &c) {
    c.member = r2.s();
    c.offset = r2.z();
    c.bytes = r2.z();
    c.check = r2.s();
    r2.list(c.args, [](R &r3, uint64_t &a) { a = r3.u(); });
  });
  r.list(p.fields, [](R &r2, FieldDecl &f) {
    f.name = r2.s();
    f.characteristic = r2.s();
    f.degree = r2.z();
  });
  r.list(p.domains, [](R &r2, DomainDecl &d) {
    d.name = r2.s();
    d.field = r2.id();
  });
  r.list(p.values, [](R &r2, Value &v) { get(r2, v); });
  r.ids(p.exprs);
  r.list(p.predicates, [](R &r2, Predicate &q) { get(r2, q); });
  r.list(p.tables, [](R &r2, Table &t) {
    t.name = r2.s();
    t.domain = r2.id();
    t.size = r2.s();
    t.rows_expr = r2.id();
    t.alpha = r2.id();
    r2.list(t.groups, [](R &r3, TableGroup &g) {
      g.capacity = r3.z();
      g.static_mult = r3.id();
      g.late_mult = r3.id();
      g.merged = r3.flag();
      r3.list(g.members, [](R &r4, std::array<size_t, 4> &m) {
        for (size_t &x : m) x = r4.z();
      }, 1);
    });
  });
  r.list(p.challenges, [](R &r2, Challenge &c) {
    c.name = r2.s();
    c.field = r2.id();
    c.phase = r2.z();
    c.size = r2.z();
    c.sampler = r2.e<Challenge::Sampler>(uint64_t(Challenge::Sampler::kMinusRange));
    c.node = r2.s();
    c.tmax = r2.s();
    c.role = r2.e<Challenge::Role>(uint64_t(Challenge::Role::kUnmodeled));
    c.owner = r2.id();
  });
  r.list(p.messages, [](R &r2, Message &m) {
    m.value = r2.id();
    m.domain = r2.id();
    m.field = r2.id();
    m.phase = r2.z();
    m.size = r2.z();
    get(r2, m.space);
    m.subfield_message = r2.flag();
    m.pad = r2.s();
  });
  r.list(p.batches, [](R &r2, Batch &x) {
    x.name = r2.s();
    x.domain = r2.id();
    x.bit_operands = r2.flag();
    x.degree = r2.z();
    x.instances = r2.z();
    x.width = r2.z();
    x.rounds = r2.z();
    x.pads = r2.z();
    x.bit_sumcheck = r2.flag();
    x.char2 = r2.flag();
    r2.ids(x.parts);
  });
  r.list(p.circuits, [](R &r2, Circuit &c) {
    c.name = r2.s();
    c.domain = r2.id();
    r2.ids(c.predicates);
    r2.list(c.entries, [](R &r3, CircuitEntry &e) {
      e.kind = r3.e<CircuitEntry::Kind>(CircuitEntry::kRealization);
      e.id = r3.z();
      get(r3, e.real);
    });
    r2.list(c.inputs, [](R &r3, InputBlock &x) {
      x.kind = r3.e<InputBlock::Kind>(InputBlock::kFiller);
      x.value = r3.id();
      get(r3, x.real);
      x.at = r3.z();
      x.n = r3.z();
      x.name = r3.s();
    });
    c.public_inputs = r2.z();
    c.input_count = r2.z();
    c.layers = r2.z();
    c.wires = r2.z();
    c.terms = r2.z();
  });
  r.list(p.realization_circuits, [](R &r2, std::pair<RealRef, Id> &x) {
    get(r2, x.first);
    x.second = r2.id();
  });
  r.list(p.convs, [](R &r2, SpectralConv &c) {
    c.source = r2.id();
    c.read = r2.id();
    c.products = r2.id();
    c.blocks = r2.z();
    c.left = r2.z();
    c.right = r2.z();
    c.length = r2.z();
    c.root = r2.s();
  });
  r.list(p.realizations, [](R &r2, DomainRealization &d) {
    d.decisions = r2.bytes();
    d.circuit = r2.bytes();
  });
  r.strs(p.unmodeled);
  r.list(p.nodes, [](R &r2, Expr &x) { get(r2, x); }, 1);
  get_index_maps(r, p.index_maps);
  r.strs(p.index_map_forms);
  r.list(p.coefs, [](R &r2, Coef &c) {
    c.is_const = r2.flag();
    c.c = r2.s();
    c.v = r2.id();
    c.i = r2.z();
  });
  r.list(p.ops, [](R &r2, NamedOp &o) { get(r2, o); });
  r.list(p.linears, [](R &r2, LinearRows &rows) {
    r2.list(rows, [](R &r3, std::vector<std::pair<size_t, Id>> &row) {
      r3.list(row, [](R &r4, std::pair<size_t, Id> &e) {
        e.first = r4.z();
        e.second = r4.id();
      }, 1);
    });
  });
  if (!r.ok || r.at != b.size()) return std::nullopt;
  return p;
}

}  // namespace proofs::gordiehowe::ir

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_REALIZED_PROGRAM_IO_H_
