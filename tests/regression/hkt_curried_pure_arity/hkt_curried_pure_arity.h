#ifndef INCLUDED_HKT_CURRIED_PURE_ARITY
#define INCLUDED_HKT_CURRIED_PURE_ARITY

#include "small_vector.h"
#include <any>
#include <atomic>
#include <concepts>
#include <functional>
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
    crane::small_vector<std::shared_ptr<Nat>> _stack = {};
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
        std::atomic_thread_fence(std::memory_order_acquire);
        _drain(_cur->v_mut());
      }
    }
  }

  Nat(const Nat &) = default;
  Nat &operator=(const Nat &) = default;
  Nat(Nat &&) noexcept = default;
  Nat &operator=(Nat &&) noexcept = default;

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
  typename I::template F<std::any>;
  {
    I::template pure<std::any>(std::declval<std::any>())
  } -> std::convertible_to<typename I::template F<std::any>>;
  {
    I::template ap<std::any, std::any>(
        std::declval<
            typename I::template F<std::function<std::any(std::any)>>>(),
        std::declval<typename I::template F<std::any>>())
  } -> std::convertible_to<typename I::template F<std::any>>;
};

struct HktCurriedPureArity {
  template <Apply _tcI0, typename T2>
  static typename _tcI0::template F<T2> pure(const T2 &x) {
    return _tcI0::template pure<T2>(x);
  }

  template <Apply _tcI0, typename T2, typename T3>
  static typename _tcI0::template F<T3>
  ap(typename _tcI0::template F<std::function<T3(T2)>> x,
     typename _tcI0::template F<T2> x0) {
    return _tcI0::template ap<T2, T3>(x, x0);
  }

  struct ApOpt {
    template <typename _A0> using F = std::optional<_A0>;

    template <typename _A0> static std::optional<_A0> pure(_A0 x) {
      return std::make_optional<_A0>(x);
    }

    template <typename _A0, typename _A1>
    static std::optional<_A1> ap(std::optional<std::function<_A1(_A0)>> f,
                                 std::optional<_A0> o) {
      if (f.has_value()) {
        const std::function<_A1(_A0)> &g = *f;
        if (o.has_value()) {
          const _A0 &x = *o;
          return std::make_optional<_A1>(g(x));
        } else {
          return std::optional<_A1>();
        }
      } else {
        return std::optional<_A1>();
      }
    }
  };

  static_assert(Apply<ApOpt>);
  static std::optional<Nat> run(const std::optional<Nat> &a,
                                const std::optional<Nat> &b);
};

#endif // INCLUDED_HKT_CURRIED_PURE_ARITY
