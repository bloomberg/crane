#ifndef INCLUDED_GUARD_COMPARE_LABEL_COLLISION
#define INCLUDED_GUARD_COMPARE_LABEL_COLLISION

#include <memory>
#include <utility>
#include <variant>
#include <vector>

struct Nat {
  // TYPES
  struct O {};

  struct S {
    std::shared_ptr<Nat> a0;
  };

  using variant_t = std::variant<O, S>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  Nat() {}

  explicit Nat(O _v) : v_(_v) {}

  explicit Nat(S _v) : v_(std::move(_v)) {}

  static Nat o() { return Nat(O{}); }

  static Nat s(Nat a0) { return Nat(S{std::make_shared<Nat>(std::move(a0))}); }

  // MANIPULATORS
  ~Nat() {
    std::vector<std::shared_ptr<Nat>> _stack = {};
    auto _drain = [&](variant_t &_v) {
      if (auto *_alt = std::get_if<S>(&_v)) {
        if (_alt->a0) {
          _stack.push_back(std::move(_alt->a0));
        }
      }
    };
    _drain(v_mut());
    while (!_stack.empty()) {
      auto _cur = std::move(_stack.back());
      _stack.pop_back();
      if (_cur.use_count() == 1) {
        _drain(_cur->v_mut());
      }
    }
  }

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};
enum class Comparison { EQ, LT, GT };

template <typename X> struct Compare {
  // TYPES
  struct LT {};

  struct EQ {};

  struct GT {};

  using variant_t = std::variant<LT, EQ, GT>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  Compare() {}

  explicit Compare(LT _v) : v_(_v) {}

  explicit Compare(EQ _v) : v_(_v) {}

  explicit Compare(GT _v) : v_(_v) {}

  static Compare<X> lt() { return Compare(LT{}); }

  static Compare<X> eq() { return Compare(EQ{}); }

  static Compare<X> gt() { return Compare(GT{}); }

  // MANIPULATORS
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

/// Reproduces the documented `Crane Guard Compare` Label-keying bug (see
/// docs/scan/117-guard-compare-directives-are-keyed-by-final-label-and-can-affect-unrelated-functions.md).
///
/// `guard_compare_table` in src/table.ml is keyed by `Label.t`
/// (`KerName.label`, i.e. just the trailing identifier, dropping the module
/// path), not by full `GlobRef.t`. Two constants named compare in
/// unrelated modules therefore collide in the table: registering a guard
/// for one silently guards the other too, even though it is never named in
/// any Crane Guard Compare directive.
///
/// This matters because the guard's generated fast path is hardcoded to
/// return Datatypes::Comparison::EQ;, which only type-checks when the
/// target's return type really is the plain extraction-primitive
/// comparison type -- the shape ordinary Fixpoint-recursive comparators
/// have (e.g. OK.compare below, or `re_compare` in a real grammar's
/// lexer). UsualOrderedType-module-style comparators (used throughout
/// FSet/FMap-backed structures, e.g. `SllSubparserAsUOT`/`CacheKeyAsUOT` in
/// parse-a-lot's `SLLPrediction.v`) instead return the dependent
/// OrderedType.Compare lt eq x y sig -- a different C++ type. Ordered.t
/// below mimics that shape.
///
/// Expected (buggy) result: extracting this file and compiling the
/// generated C++ FAILS -- not because of anything wrong with Ordered.compare
/// itself, but because the Label collision injects an ill-typed
/// Datatypes::Comparison::EQ fast path into it, purely as a side effect of
/// guarding the unrelated OK.compare. A fix that keys `guard_compare_table`
/// by full GlobRef.t instead of Label.t should make this file extract
/// and compile cleanly (with the guard applied only to OK.compare).
struct OK {
  /// An ordinary structural comparator returning the plain extraction
  /// primitive comparison -- the only shape `Crane Guard Compare`'s
  /// codegen actually supports. Guarding this one is fine: physical
  /// identity of the two arguments trivially implies structural equality
  /// for pure/immutable values.
  static Comparison compare(const Nat &x, const Nat &y);
};

struct Ordered {
  /// Unrelated type and module -- never mentioned in the Crane Guard
  /// Compare directive below. Its compare happens to share the trailing
  /// label "compare" with OK.compare, which is all the Label-keyed table
  /// looks at. Mimics the real UsualOrderedType-module shape used by
  /// parse-a-lot's SLL prediction cache/set comparators.
  enum class T { A, B };

  template <typename T1> static T1 t_rect(T1 f, T1 f0, T t0) {
    switch (t0) {
    case T::A: {
      return f;
    }
    case T::B: {
      return f0;
    }
    default:
      std::unreachable();
    }
  }

  template <typename T1> static T1 t_rec(T1 f, T1 f0, T t0) {
    switch (t0) {
    case T::A: {
      return f;
    }
    case T::B: {
      return f0;
    }
    default:
      std::unreachable();
    }
  }

  /// An ordinary structural comparator returning the plain extraction
  /// primitive comparison -- the only shape `Crane Guard Compare`'s
  /// codegen actually supports. Guarding this one is fine: physical
  /// identity of the two arguments trivially implies structural equality
  /// for pure/immutable values.
  static Compare<T> compare(T x, T y);
};

#endif // INCLUDED_GUARD_COMPARE_LABEL_COLLISION
