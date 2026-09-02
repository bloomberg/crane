#ifndef INCLUDED_HKT_LAMBDA_PARAM_CARRIER
#define INCLUDED_HKT_LAMBDA_PARAM_CARRIER

#include "small_vector.h"
#include <any>
#include <atomic>
#include <concepts>
#include <functional>
#include <memory>
#include <optional>
#include <type_traits>
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

/// In a generic function over a Monad M, the class variable M leaks into
/// the parameter type of an inner lambda instead of the method's own element
/// type:
///
/// return bind<_tcI0>(m, =(const T2 &x) mutable {
/// return bind<_tcI0>(f(x), (M y) { return ret<_tcI0>(y); });
/// });
///
/// error: unknown type name 'M'   (should be T2)
template <typename I>
concept Monad = requires {
  typename I::template M<std::any>;
  {
    I::template ret<std::any>(std::declval<std::any>())
  } -> std::convertible_to<typename I::template M<std::any>>;
  {
    I::template bind<std::any, std::any>(
        std::declval<typename I::template M<std::any>>(),
        std::declval<
            std::function<typename I::template M<std::any>(std::any)>>())
  } -> std::convertible_to<typename I::template M<std::any>>;
};

struct HktLambdaParamCarrier {
  template <Monad _tcI0, typename T2>
  static typename _tcI0::template M<T2> ret(const T2 &x) {
    return _tcI0::template ret<T2>(x);
  }

  template <Monad _tcI0, typename T2, typename T3, typename F1>
    requires std::is_invocable_r_v<typename _tcI0::template M<T3>, F1 &, T2 &>
  static typename _tcI0::template M<T3> bind(typename _tcI0::template M<T2> x,
                                             F1 &&x0) {
    return _tcI0::template bind<T2, T3>(x, x0);
  }

  struct OptM {
    template <typename _A0> using M = std::optional<_A0>;

    template <typename _A0> static std::optional<_A0> ret(_A0 x) {
      return std::make_optional<_A0>(x);
    }

    template <typename _A0, typename _A1>
    static std::optional<_A1> bind(std::optional<_A0> m,
                                   std::function<std::optional<_A1>(_A0)> f) {
      if (m.has_value()) {
        const _A0 &x = *m;
        return f(x);
      } else {
        return std::optional<_A1>();
      }
    }
  };

  static_assert(Monad<OptM>);

  template <Monad _tcI0, typename T2, typename F1>
    requires std::is_invocable_r_v<typename _tcI0::template M<T2>, F1 &, T2 &>
  static typename _tcI0::template M<T2> twice(typename _tcI0::template M<T2> m,
                                              F1 &&f) {
    return bind<_tcI0, T2, T2>(m, [=](const T2 &x) mutable {
      return bind<_tcI0, T2, T2>(f(x), [](M y) { return ret<_tcI0, T2>(y); });
    });
  }

  static std::optional<Nat> run(const std::optional<Nat> &o);
};

#endif // INCLUDED_HKT_LAMBDA_PARAM_CARRIER
