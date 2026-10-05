#ifndef INCLUDED_GUARD_COMPARE_LABEL_COLLISION
#define INCLUDED_GUARD_COMPARE_LABEL_COLLISION

#include <atomic>
#include <memory>
#include <utility>
#include <variant>

struct Nat;
enum class Comparison;
template <typename X> struct Compare;

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
    auto _next = [&](variant_t &_v) -> std::shared_ptr<Nat> {
      if (auto *_alt = std::get_if<S>(&_v)) {
        if (_alt->a0 && _alt->a0.use_count() == 1) {
          std::atomic_thread_fence(std::memory_order_acquire);
          return std::move(_alt->a0);
        }
      }
      return nullptr;
    };
    std::shared_ptr<Nat> _cur = _next(v_mut());
    while (_cur) {
      _cur = _next(_cur->v_mut());
    }
  }

  Nat(const Nat &) = default;
  Nat &operator=(const Nat &) = default;
  Nat(Nat &&) = default;
  Nat &operator=(Nat &&) = default;

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

  static Compare<X> lt() { return Compare<X>(LT{}); }

  static Compare<X> eq() { return Compare<X>(EQ{}); }

  static Compare<X> gt() { return Compare<X>(GT{}); }

  // MANIPULATORS
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

/// Regression test for the `Crane Guard Compare` Label-keying bug (see
/// docs/scan/117-guard-compare-directives-are-keyed-by-final-label-and-can-affect-unrelated-functions.md).
///
/// `guard_compare_table` in src/table.ml used to be keyed by `Label.t`
/// (`KerName.label`, i.e. just the trailing identifier, dropping the module
/// path), so two constants named compare in unrelated modules would
/// collide in the table: registering a guard for one would silently guard
/// the other too, even though it was never named in any Crane Guard
/// Compare directive. It is now keyed by full GlobRef.t (via Refmap',
/// matching the customs table's convention), so only the exact constant
/// named in a directive is affected.
///
/// OK.compare is an ordinary Fixpoint-recursive comparator returning the
/// plain extraction-primitive comparison type -- the shape Crane Guard
/// Compare's codegen supports. Ordered.compare mimics a
/// UsualOrderedType-module-style comparator (used throughout FSet/FMap-
/// backed structures, e.g. `SllSubparserAsUOT`/`CacheKeyAsUOT` in
/// parse-a-lot's `SLLPrediction.v`), returning the dependent
/// OrderedType.Compare lt eq x y sig -- a different C++ type. Only
/// OK.compare is guarded below; Ordered.compare must extract and compile
/// unaffected.
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
    return t_rect<T1>(std::move(f), std::move(f0), t0);
  }

  /// An ordinary structural comparator returning the plain extraction
  /// primitive comparison -- the only shape `Crane Guard Compare`'s
  /// codegen actually supports. Guarding this one is fine: physical
  /// identity of the two arguments trivially implies structural equality
  /// for pure/immutable values.
  static Compare<T> compare(T x, T y);
};

#endif // INCLUDED_GUARD_COMPARE_LABEL_COLLISION
