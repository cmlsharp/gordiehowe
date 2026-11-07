// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// The GHC writer: the compiler's data for the Lean formalization as `.ghc`
// files (version 3), which formal/GordieHoweNative/Ghc.lean reads (the
// container) and decodes by type (Lean's `Ghc.Decode`, derived per type).
//
// A file is the magic "GHC", the version byte 3, its sections, and the end
// marker (an empty name). A section is its name (the Lean definition it
// becomes, relative to the loading namespace), its Lean type (Ty), its flags
// (kCompile: the definition gets compiled code; kSpine: the value is in
// spine form; kReader: native mode reads it at run time; no other bit), its
// value's byte count and its value. A value is written by its Lean type: a
// natural as LEB128 (least significant group first, minimal: the readers
// reject a multi-byte natural whose last group is zero), an integer zigzag, a
// Bool as 0/1, a string as its byte count then its UTF-8 bytes, an Option
// as 0, or 1 then the value, a List as its count then its items, a
// structure (Prod included) as its fields in order, any other inductive as
// its constructor index then its fields, and an IndexMap as the number j of
// the program's idx<j>. In spine form every position carries a tag first:
// 0 a plain value, 1 the index of an earlier section of the same type, 2
// the constructor (index, unless a structure; a list's count) with each
// field again in spine form.
//
// The writer checks every section's value against a Schema, the Lean types
// mirrored (their constructors and field types): Schema::walk reads a value
// as the Lean decoder does, so a section is written only if Lean's decoder
// of its type reads it whole. read() and show() are the reader of the same
// format (the tests' round trip, and a text rendering of any file).

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_GHC_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_GHC_H_

#include <cstddef>
#include <cstdint>
#include <functional>
#include <map>
#include <set>
#include <stdexcept>
#include <string>
#include <utility>
#include <vector>

namespace proofs::gordiehowe::ghc {

// A malformed file or value, an unknown type, or a section the schema
// rejects.
struct Error : std::runtime_error {
  using std::runtime_error::runtime_error;
};

// ---------------------------------------------------------------- bytes --

// The encodings of the primitive values.
class Bytes {
 public:
  std::vector<uint8_t> out;

  void nat(uint64_t x) {
    do {
      uint8_t b = uint8_t(x & 0x7f);
      x >>= 7;
      if (x != 0) b |= 0x80;
      out.push_back(b);
    } while (x != 0);
  }
  // The natural of little-endian bytes B.
  void nat_le(const uint8_t *b, size_t n) {
    size_t bits = 0;
    for (size_t i = n; i-- > 0;)
      if (b[i] != 0) {
        bits = 8 * i;
        for (uint8_t v = b[i]; v != 0; v >>= 1) ++bits;
        break;
      }
    const size_t groups = bits == 0 ? 1 : (bits + 6) / 7;
    for (size_t g = 0; g < groups; ++g) {
      uint8_t c = 0;
      for (size_t j = 0; j < 7; ++j) {
        const size_t at = 7 * g + j;
        if (at < bits && ((b[at / 8] >> (at % 8)) & 1)) c |= uint8_t(1u << j);
      }
      if (g + 1 < groups) c |= 0x80;
      out.push_back(c);
    }
  }
  void nat_le(const std::vector<uint8_t> &b) { nat_le(b.data(), b.size()); }
  void integer(int64_t x) {
    nat(x >= 0 ? uint64_t(x) * 2 : uint64_t(-(x + 1)) * 2 + 1);
  }
  void boolean(bool b) { nat(b ? 1 : 0); }
  void string(const std::string &s) {
    nat(s.size());
    out.insert(out.end(), s.begin(), s.end());
  }
  void bytes(const std::vector<uint8_t> &b) { out.insert(out.end(), b.begin(), b.end()); }
  void bytes(const Bytes &b) { bytes(b.out); }
  // A constructor's index (an inductive that is not a structure).
  void ctor(uint64_t i) { nat(i); }
  // Spine-form tags: a plain value follows, an earlier section's index, or
  // the constructor form.
  void plain() { nat(0); }
  void ref(uint64_t section) {
    nat(1);
    nat(section);
  }
  void inline_() { nat(2); }
};

// FNV-1a 64 of B (the hash in a load_ghc line).
inline uint64_t fnv1a(const std::vector<uint8_t> &b) {
  uint64_t h = 0xcbf29ce484222325ull;
  for (uint8_t c : b) {
    h ^= c;
    h *= 0x100000001b3ull;
  }
  return h;
}

// A natural built by OR-ing values in at bit offsets (Lean's x ||| (v <<<
// at)): the packed chunks of the certificates.
class BitPack {
 public:
  void put(size_t at, uint64_t v) {
    for (size_t i = 0; v != 0; ++i, v >>= 1)
      if (v & 1) set(at + i);
  }
  // V given as little-endian bytes.
  void put(size_t at, const std::vector<uint8_t> &v) {
    for (size_t i = 0; i < 8 * v.size(); ++i)
      if ((v[i / 8] >> (i % 8)) & 1) set(at + i);
  }
  void write(Bytes &o) const { o.nat_le(b_.empty() ? std::vector<uint8_t>{0} : b_); }

 private:
  void set(size_t i) {
    if (b_.size() <= i / 8) b_.resize(i / 8 + 1, 0);
    b_[i / 8] |= uint8_t(1u << (i % 8));
  }
  std::vector<uint8_t> b_;
};

// The bit length of little-endian bytes (0 for zero).
inline size_t bit_length(const std::vector<uint8_t> &b) {
  for (size_t i = b.size(); i-- > 0;)
    if (b[i] != 0) {
      size_t n = 8 * i;
      for (uint8_t v = b[i]; v != 0; v >>= 1) ++n;
      return n;
    }
  return 0;
}

// ----------------------------------------------------------------- types --

// A Lean type: a constant's full name applied to arguments (the file writes
// it curried: 0 then a name, or 1 then a function and its argument). In a
// schema's field types, "#i" is the type's parameter i.
struct Ty {
  std::string name;
  std::vector<Ty> args;

  bool operator==(const Ty &o) const { return name == o.name && args == o.args; }
  bool operator!=(const Ty &o) const { return !(*this == o); }

  void encode(Bytes &o) const {
    for (size_t i = args.size(); i-- > 0;) o.nat(1);
    o.nat(0);
    o.string(name);
    for (const Ty &a : args) a.encode(o);
  }
  std::string text() const {
    std::string s = name;
    for (const Ty &a : args) s += " " + (a.args.empty() ? a.text() : "(" + a.text() + ")");
    return s;
  }
  // Parses "F A (G B)": names separated by spaces, parentheses grouping.
  static Ty parse(const std::string &s) {
    size_t i = 0;
    Ty t = parse_app(s, i);
    skip_ws(s, i);
    if (i != s.size()) throw Error("type text: trailing characters in " + s);
    return t;
  }
  Ty subst(const std::vector<Ty> &ps) const {
    if (!name.empty() && name[0] == '#') {
      const size_t k = std::stoul(name.substr(1));
      if (k >= ps.size()) throw Error("type text: no parameter " + name);
      return ps[k];
    }
    Ty t{name, {}};
    for (const Ty &a : args) t.args.push_back(a.subst(ps));
    return t;
  }

 private:
  static void skip_ws(const std::string &s, size_t &i) {
    while (i < s.size() && s[i] == ' ') ++i;
  }
  static Ty parse_atom(const std::string &s, size_t &i) {
    skip_ws(s, i);
    if (i < s.size() && s[i] == '(') {
      ++i;
      Ty t = parse_app(s, i);
      skip_ws(s, i);
      if (i >= s.size() || s[i] != ')') throw Error("type text: unbalanced " + s);
      ++i;
      return t;
    }
    size_t j = i;
    while (j < s.size() && s[j] != ' ' && s[j] != '(' && s[j] != ')') ++j;
    if (j == i) throw Error("type text: expected a name in " + s);
    Ty t{s.substr(i, j - i), {}};
    i = j;
    return t;
  }
  static Ty parse_app(const std::string &s, size_t &i) {
    Ty t = parse_atom(s, i);
    for (;;) {
      skip_ws(s, i);
      if (i >= s.size() || s[i] == ')') return t;
      t.args.push_back(parse_atom(s, i));
    }
  }
};

inline Ty ty(const std::string &s) { return Ty::parse(s); }

// ---------------------------------------------------------------- schema --

// The Lean types a file's values may have: the primitives, and each
// registered inductive's constructors (their names and field types, "#i"
// the type's parameter i, and a structure's field names), in Lean's order.
class Schema {
 public:
  struct Ctor {
    std::string name;
    std::vector<Ty> fields;
    // A structure's field names (empty where not given).
    std::vector<std::string> names;
  };
  struct Type {
    size_t params = 0;
    bool structure = false;
    std::vector<Ctor> ctors;
  };

  Schema() {
    for (const char *p : {"Nat", "Int", "Bool", "String", "GordieHowe.RealizedProgram.IndexMap"})
      prims_[p] = 0;
    prims_["List"] = 1;
    prims_["Option"] = 1;
    structure("Prod", 2, {"fst : #0", "snd : #1"});
  }

  // A structure: one constructor, its fields in order, each "name : type"
  // or a type alone.
  void structure(const std::string &name, size_t params, const std::vector<std::string> &fields) {
    Type t{params, true, {{"mk", {}, {}}}};
    for (const auto &f : fields) {
      const size_t colon = f.find(" : ");
      t.ctors[0].names.push_back(colon == std::string::npos ? "" : f.substr(0, colon));
      t.ctors[0].fields.push_back(Ty::parse(colon == std::string::npos ? f : f.substr(colon + 3)));
    }
    add(name, std::move(t));
  }
  // An inductive: its constructors, each a name and its fields' types.
  void inductive(const std::string &name, size_t params,
                 const std::vector<std::pair<std::string, std::vector<std::string>>> &ctors) {
    Type t{params, false, {}};
    for (const auto &[c, fs] : ctors) {
      Ctor k{c, {}, {}};
      for (const auto &f : fs) k.fields.push_back(Ty::parse(f));
      t.ctors.push_back(std::move(k));
    }
    add(name, std::move(t));
  }

  // Whether every constant of T is a known type at its arity.
  bool knows(const Ty &t) const {
    size_t arity;
    if (auto p = prims_.find(t.name); p != prims_.end())
      arity = p->second;
    else if (auto u = types_.find(t.name); u != types_.end())
      arity = u->second.params;
    else
      return false;
    if (t.args.size() != arity) return false;
    for (const Ty &a : t.args)
      if (!knows(a)) return false;
    return true;
  }

  // A cursor over a value's bytes, the earlier sections' types (the
  // references a spine-form value may make), and an optional rendering.
  struct Cursor {
    const uint8_t *b;
    size_t n, pos;
    const std::vector<Ty> *earlier = nullptr;
    std::string *text = nullptr;
  };

  // Reads one value of type T at C (in spine form when SPINE), as Lean's
  // decoder does, appending its rendering to C.text if set.
  void walk(const Ty &t, Cursor &c, bool spine) const {
    if (spine) {
      const uint64_t tag = nat(c);
      if (tag == 0) return walk(t, c, false);
      if (tag == 1) {
        const uint64_t j = nat(c);
        if (c.earlier == nullptr || j >= c.earlier->size())
          throw Error("a reference to section " + std::to_string(j) + ", not an earlier one");
        if ((*c.earlier)[j] != t)
          throw Error("a reference to section " + std::to_string(j) + " of type " +
                      (*c.earlier)[j].text() + ", not " + t.text());
        emit(c, "@" + std::to_string(j));
        return;
      }
      if (tag != 2) throw Error("spine tag " + std::to_string(tag));
    }
    walk_ctor(t, c, spine);
  }

  // The registered types as text, sorted by name, Lean's Prod aside: per
  // type a line "structure NAME (params P)" or "inductive NAME (params P)",
  // then a structure's fields, one "  name : type" line each ("_" for a
  // field given without a name), or an inductive's constructors, one
  // "  | name field-type..." line each (a type with arguments
  // parenthesized). formal/scripts/GhcSchema.lean prints the Lean types of
  // formal/GordieHoweNative/Data.lean the same way.
  std::string dump() const {
    std::string o;
    for (const auto &[name, t] : types_) {
      if (name == "Prod") continue;
      o += (t.structure ? "structure " : "inductive ") + name + " (params " +
           std::to_string(t.params) + ")\n";
      for (const Ctor &c : t.ctors) {
        if (t.structure) {
          for (size_t i = 0; i < c.fields.size(); ++i)
            o += "  " + (c.names[i].empty() ? std::string("_") : c.names[i]) + " : " +
                 c.fields[i].text() + "\n";
          continue;
        }
        o += "  | " + c.name;
        for (const Ty &f : c.fields) o += " " + (f.args.empty() ? f.text() : "(" + f.text() + ")");
        o += "\n";
      }
    }
    return o;
  }

  // The end of the plain value of type T at POS in B.
  size_t skip(const Ty &t, const std::vector<uint8_t> &b, size_t pos) const {
    Cursor c{b.data(), b.size(), pos};
    walk(t, c, false);
    return c.pos;
  }

 private:
  void add(const std::string &name, Type t) {
    if (prims_.count(name) || types_.count(name)) throw Error("schema: " + name + " twice");
    types_[name] = std::move(t);
  }


 public:
  // The LEB128 groups of a natural of any size at C, which must be minimal
  // (a multi-byte natural's last group nonzero).
  static std::vector<uint8_t> groups(Cursor &c) {
    const size_t start = c.pos;
    std::vector<uint8_t> g;
    for (;;) {
      if (c.pos >= c.n) throw Error("unexpected end of data at byte " + std::to_string(c.pos));
      const uint8_t v = c.b[c.pos++];
      g.push_back(v & 0x7f);
      if ((v & 0x80) == 0) break;
    }
    if (g.size() > 1 && g.back() == 0)
      throw Error("a natural at byte " + std::to_string(start) + " is not minimally encoded");
    return g;
  }
  // A natural below 2^64 at C (a tag, a count, a length): a minimal LEB128
  // natural of more bits is rejected, not truncated.
  static uint64_t nat(Cursor &c) {
    const size_t start = c.pos;
    const std::vector<uint8_t> g = groups(c);
    if (g.size() > 10 || (g.size() == 10 && g.back() > 1))
      throw Error("a natural at byte " + std::to_string(start) + " exceeds 64 bits");
    uint64_t x = 0;
    for (size_t i = 0; i < g.size(); ++i) x |= uint64_t(g[i]) << (7 * i);
    return x;
  }

 private:
  // A natural of any size, rendered in hex when it exceeds 64 bits.
  static void big(Cursor &c) {
    const size_t start = c.pos;
    const std::vector<uint8_t> groups = Schema::groups(c);
    if (c.text == nullptr) return;
    if (groups.size() <= 9) {
      Cursor d{c.b, c.n, start};
      *c.text += std::to_string(nat(d));
      return;
    }
    std::vector<uint8_t> bits;
    for (uint8_t g : groups)
      for (int j = 0; j < 7; ++j) bits.push_back((g >> j) & 1);
    std::string hex;
    for (size_t i = 0; i < bits.size(); i += 4) {
      int d = 0;
      for (int j = 0; j < 4 && i + j < bits.size(); ++j) d |= bits[i + j] << j;
      hex.insert(hex.begin(), "0123456789abcdef"[d]);
    }
    while (hex.size() > 1 && hex[0] == '0') hex.erase(hex.begin());
    *c.text += "0x" + hex;
  }
  static void emit(Cursor &c, const std::string &s) {
    if (c.text != nullptr) *c.text += s;
  }

  void walk_ctor(const Ty &t, Cursor &c, bool spine) const {
    if (auto p = prims_.find(t.name); p != prims_.end()) {
      if (t.args.size() != p->second) throw Error("type " + t.text() + ": wrong arity");
      if (t.name == "List") {
        const uint64_t n = nat(c);
        emit(c, "[");
        for (uint64_t i = 0; i < n; ++i) {
          if (i) emit(c, ", ");
          walk(t.args[0], c, spine);
        }
        emit(c, "]");
        return;
      }
      if (t.name == "Option") {
        const uint64_t k = nat(c);
        if (k == 0) return emit(c, "none");
        if (k != 1) throw Error("Option: no constructor " + std::to_string(k));
        emit(c, "(some ");
        walk(t.args[0], c, spine);
        return emit(c, ")");
      }
      if (spine) throw Error(t.text() + ": no constructor form");
      if (t.name == "Nat") return big(c);
      if (t.name == "Int") {
        Cursor d = c;
        groups(c);
        if (c.text == nullptr) return;
        if (c.pos - d.pos > 9) return big(d);
        const uint64_t z = nat(d);
        *c.text += (z & 1) ? "-" + std::to_string(z / 2 + 1) : std::to_string(z / 2);
        return;
      }
      if (t.name == "Bool") {
        const uint64_t k = nat(c);
        if (k > 1) throw Error("Bool: no constructor " + std::to_string(k));
        return emit(c, k ? "true" : "false");
      }
      if (t.name == "String") {
        const uint64_t n = nat(c);
        if (n > c.n - c.pos) throw Error("unexpected end of data in a string");
        emit(c, "\"" + std::string(reinterpret_cast<const char *>(c.b + c.pos), n) + "\"");
        c.pos += n;
        return;
      }
      // IndexMap
      return emit(c, "idx" + std::to_string(nat(c)));
    }
    auto u = types_.find(t.name);
    if (u == types_.end()) throw Error("unknown type " + t.name);
    const Type &ty = u->second;
    if (t.args.size() != ty.params) throw Error("type " + t.text() + ": wrong arity");
    size_t k = 0;
    if (!ty.structure) {
      k = nat(c);
      if (k >= ty.ctors.size())
        throw Error(t.name + ": no constructor " + std::to_string(k));
    }
    const Ctor &ct = ty.ctors[k];
    if (ty.structure)
      emit(c, "⟨");
    else
      emit(c, ct.fields.empty() ? "." + ct.name : "(." + ct.name);
    for (size_t i = 0; i < ct.fields.size(); ++i) {
      emit(c, ty.structure ? (i ? ", " : "") : " ");
      walk(ct.fields[i].subst(t.args), c, spine);
    }
    if (ty.structure)
      emit(c, "⟩");
    else if (!ct.fields.empty())
      emit(c, ")");
  }

  std::map<std::string, size_t> prims_;
  std::map<std::string, Type> types_;
};

// ----------------------------------------------------------------- files --

enum Flags : uint64_t { kCompile = 1, kSpine = 2, kReader = 4 };
// The flag bits a section may set; the writer and the reader reject any
// other.
inline constexpr uint64_t kKnownFlags = kCompile | kSpine | kReader;

// A file's section: name, type, flags, value.
struct Section {
  std::string name;
  Ty type;
  uint64_t flags = 0;
  std::vector<uint8_t> value;
};

// A file being written: its sections in order, each checked against the
// schema when added.
class File {
 public:
  explicit File(const Schema &s) : schema_(s) {}

  // Adds the section NAME : TYPE with VALUE (in spine form when FLAGS has
  // kSpine; its references name earlier sections); returns its index.
  size_t section(const std::string &name, const Ty &type, uint64_t flags, const Bytes &value) {
    if (name.empty()) throw Error("a section with no name");
    if (names_.count(name)) throw Error("section " + name + ": a second one");
    if (!schema_.knows(type)) throw Error("section " + name + ": unknown type " + type.text());
    if (flags & ~kKnownFlags)
      throw Error("section " + name + ": unknown flags " + std::to_string(flags));
    try {
      check(schema_, type, flags, value.out, types_);
    } catch (const Error &e) {
      throw Error("section " + name + ": " + e.what());
    }
    names_.insert(name);
    secs_.push_back({name, type, flags, value.out});
    types_.push_back(type);
    return secs_.size() - 1;
  }
  const std::vector<Section> &sections() const { return secs_; }

  std::vector<uint8_t> bytes() const {
    Bytes o;
    o.out = {0x47, 0x48, 0x43, 0x03};
    for (const Section &s : secs_) {
      o.string(s.name);
      s.type.encode(o);
      o.nat(s.flags);
      o.nat(s.value.size());
      o.bytes(s.value);
    }
    o.string("");
    return o.out;
  }

  // Whether VALUE is one whole value of TYPE (spine form by FLAGS), its
  // references to the sections of types EARLIER.
  static void check(const Schema &schema, const Ty &type, uint64_t flags,
                    const std::vector<uint8_t> &value, const std::vector<Ty> &earlier,
                    std::string *text = nullptr) {
    Schema::Cursor c{value.data(), value.size(), 0, &earlier, text};
    schema.walk(type, c, (flags & kSpine) != 0);
    if (c.pos != value.size()) throw Error("trailing bytes");
  }

 private:
  const Schema &schema_;
  std::vector<Section> secs_;
  std::vector<Ty> types_;
  std::set<std::string> names_;
};

// The sections of a file's bytes, each value checked against the schema.
inline std::vector<Section> read(const std::vector<uint8_t> &b, const Schema &schema) {
  if (b.size() < 4 || b[0] != 0x47 || b[1] != 0x48 || b[2] != 0x43 || b[3] != 3)
    throw Error("not a GHC version 3 file");
  Schema::Cursor c{b.data(), b.size(), 4};
  auto nat = [&]() { return Schema::nat(c); };
  auto string = [&]() {
    const uint64_t n = nat();
    if (n > c.n - c.pos) throw Error("unexpected end of data in a section name");
    std::string s(reinterpret_cast<const char *>(c.b + c.pos), n);
    c.pos += n;
    return s;
  };
  std::function<Ty()> type = [&]() -> Ty {
    const uint64_t k = nat();
    if (k == 0) return Ty{string(), {}};
    if (k != 1) throw Error("a type: no constructor " + std::to_string(k));
    Ty f = type();
    f.args.push_back(type());
    return f;
  };
  std::vector<Section> out;
  std::vector<Ty> types;
  std::set<std::string> names;
  for (;;) {
    std::string name = string();
    if (name.empty()) break;
    if (!names.insert(name).second) throw Error("section " + name + ": a second one");
    Section s{name, type(), 0, {}};
    s.flags = nat();
    if (s.flags & ~kKnownFlags)
      throw Error("section " + name + ": unknown flags " + std::to_string(s.flags));
    const uint64_t len = nat();
    if (len > c.n - c.pos) throw Error("section " + name + ": length past the end");
    s.value.assign(b.begin() + c.pos, b.begin() + c.pos + len);
    c.pos += len;
    if (!schema.knows(s.type)) throw Error("section " + name + ": unknown type " + s.type.text());
    try {
      File::check(schema, s.type, s.flags, s.value, types);
    } catch (const Error &e) {
      throw Error("section " + name + ": " + e.what());
    }
    types.push_back(s.type);
    out.push_back(std::move(s));
  }
  if (c.pos != b.size()) throw Error("bytes after the end marker");
  return out;
}

// A file as text: per section its name, type, flags and value.
inline std::string show(const std::vector<uint8_t> &b, const Schema &schema) {
  const std::vector<Section> secs = read(b, schema);
  std::string o;
  std::vector<Ty> types;
  for (size_t j = 0; j < secs.size(); ++j) {
    const Section &s = secs[j];
    o += "@" + std::to_string(j) + " " + s.name + " : " + s.type.text();
    if (s.flags & kCompile) o += " [compile]";
    if (s.flags & kSpine) o += " [spine]";
    if (s.flags & kReader) o += " [reader]";
    o += " :=\n  ";
    File::check(schema, s.type, s.flags, s.value, types, &o);
    o += "\n";
    types.push_back(s.type);
  }
  return o;
}

}  // namespace proofs::gordiehowe::ghc

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_GHC_H_
