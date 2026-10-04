#ifndef INCLUDED_HKT_CURRIED_PURE_ARITY
#define INCLUDED_HKT_CURRIED_PURE_ARITY

#include "fn.h"
#include "obj.h"
#include <atomic>
#include <concepts>
#include <memory>
#include <optional>
#include <utility>
#include <variant>

struct Nat;

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

/// A curried two-argument lambda passed to pure is typed as an uncurried
/// std::function, so the partially-applied ap no longer matches:
///
/// pure<ApOpt, std::function<Nat(Nat, Nat)>>(
/// (const auto &x, const auto &) { return x; })
///
/// should be std::function<std::function<Nat(Nat)>(Nat)>.
///
/// error: no matching function for call to 'ap'
template <typename I>
concept Apply = requires {
  typename I::template F<crane::obj>;
  {
    I::template pure<crane::obj>(std::declval<crane::obj>())
  } -> std::convertible_to<typename I::template F<crane::obj>>;
  {
    I::template ap<crane::obj, crane::obj>(
        std::declval<
            typename I::template F<crane::fn<crane::obj(crane::obj)>>>(),
        std::declval<typename I::template F<crane::obj>>())
  } -> std::convertible_to<typename I::template F<crane::obj>>;
};

struct HktCurriedPureArity {
  template <Apply _tcI0, typename T2>
  static typename _tcI0::template F<T2> pure(const T2 &x) {
    return _tcI0::template pure<T2>(x);
  }

  template <Apply _tcI0, typename T2, typename T3>
  static typename _tcI0::template F<T3>
  ap(typename _tcI0::template F<crane::fn<T3(T2)>> x,
     typename _tcI0::template F<T2> x0) {
    return _tcI0::template ap<T2, T3>(std::move(x), std::move(x0));
  }

  struct ApOpt {
    template <typename CraneA0> using F = std::optional<CraneA0>;

    template <typename CraneA0> static std::optional<CraneA0> pure(CraneA0 x) {
      return std::make_optional<CraneA0>(x);
    }

    template <typename CraneA0, typename CraneA1>
    static std::optional<CraneA1>
    ap(std::optional<crane::fn<CraneA1(CraneA0)>> f, std::optional<CraneA0> o) {
      if (f.has_value()) {
        const crane::fn<CraneA1(CraneA0)> &g = *f;
        if (o.has_value()) {
          const CraneA0 &x = *o;
          return std::make_optional<CraneA1>(g(x));
        } else {
          return std::optional<CraneA1>();
        }
      } else {
        return std::optional<CraneA1>();
      }
    }
  };

  static_assert(Apply<ApOpt>);
  static std::optional<Nat> run(const std::optional<Nat> &a,
                                const std::optional<Nat> &b);
};

#endif // INCLUDED_HKT_CURRIED_PURE_ARITY
