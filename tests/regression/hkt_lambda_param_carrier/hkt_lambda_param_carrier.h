#ifndef INCLUDED_HKT_LAMBDA_PARAM_CARRIER
#define INCLUDED_HKT_LAMBDA_PARAM_CARRIER

#include "fn.h"
#include "obj.h"
#include <atomic>
#include <concepts>
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
  typename I::template M<crane::obj>;
  {
    I::template ret<crane::obj>(std::declval<crane::obj>())
  } -> std::convertible_to<typename I::template M<crane::obj>>;
  {
    I::template bind<crane::obj, crane::obj>(
        std::declval<typename I::template M<crane::obj>>(),
        std::declval<
            crane::fn<typename I::template M<crane::obj>(crane::obj)>>())
  } -> std::convertible_to<typename I::template M<crane::obj>>;
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
    return _tcI0::template bind<T2, T3>(std::move(x), x0);
  }

  struct OptM {
    template <typename CraneA0> using M = std::optional<CraneA0>;

    template <typename CraneA0> static std::optional<CraneA0> ret(CraneA0 x) {
      return std::make_optional<CraneA0>(x);
    }

    template <typename CraneA0, typename CraneA1>
    static std::optional<CraneA1>
    bind(std::optional<CraneA0> m,
         crane::fn<std::optional<CraneA1>(CraneA0)> f) {
      if (m.has_value()) {
        const CraneA0 &x = *m;
        return f(x);
      } else {
        return std::optional<CraneA1>();
      }
    }
  };

  static_assert(Monad<OptM>);

  template <Monad _tcI0, typename T2, typename F1>
    requires std::is_invocable_r_v<typename _tcI0::template M<T2>, F1 &, T2 &>
  static typename _tcI0::template M<T2> twice(typename _tcI0::template M<T2> m,
                                              F1 &&f) {
    return bind<_tcI0, T2, T2>(std::move(m), [=](const T2 &x) {
      return bind<_tcI0, T2, T2>(f(x),
                                 [](const T2 &y) { return ret<_tcI0, T2>(y); });
    });
  }

  static std::optional<Nat> run(const std::optional<Nat> &o);
};

#endif // INCLUDED_HKT_LAMBDA_PARAM_CARRIER
