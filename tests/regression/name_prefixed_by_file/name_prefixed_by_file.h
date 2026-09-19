#ifndef INCLUDED_NAME_PREFIXED_BY_FILE
#define INCLUDED_NAME_PREFIXED_BY_FILE

#include "crane_fn.h"
#include "small_vector.h"
#include <any>
#include <atomic>
#include <concepts>
#include <functional>
#include <memory>
#include <optional>
#include <stdexcept>
#include <type_traits>
#include <utility>
#include <variant>

struct EOU_monad;
struct Nat;
template <typename X> struct EOU;

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

template <typename I>
concept Monad = requires {
  typename I::template m<std::any>;
  {
    I::template ret<std::any>(std::declval<std::any>())
  } -> std::convertible_to<typename I::template m<std::any>>;
  {
    I::template bind<std::any, std::any>(
        std::declval<typename I::template m<std::any>>(),
        std::declval<
            std::function<typename I::template m<std::any>(std::any)>>())
  } -> std::convertible_to<typename I::template m<std::any>>;
};

struct Monad0 {
  template <Monad _tcI0, typename T2>
  static typename _tcI0::template m<T2> ret(const T2 &x);
  template <Monad _tcI0, typename T2, typename T3, typename F1>
    requires std::is_invocable_r_v<typename _tcI0::template m<T3>, F1 &, T2 &>
  static typename _tcI0::template m<T3> bind(typename _tcI0::template m<T2> x,
                                             F1 &&x0);
};

template <typename X> struct EOU {
  // TYPES
  struct Raise_error {
    Nat s;
  };

  struct Raise_ret {
    X x;
  };

  using variant_t = std::variant<Raise_error, Raise_ret>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  EOU() {}

  explicit EOU(Raise_error _v) : v_(std::move(_v)) {}

  explicit EOU(Raise_ret _v) : v_(std::move(_v)) {}

  template <typename _U> EOU(const EOU<_U> &_other) {
    if (std::holds_alternative<typename EOU<_U>::Raise_error>(_other.v())) {
      const auto &[s] = std::get<typename EOU<_U>::Raise_error>(_other.v());
      this->v_ = Raise_error{s};
    } else {
      const auto &[x] = std::get<typename EOU<_U>::Raise_ret>(_other.v());
      this->v_ = Raise_ret{[&]() -> X {
        if constexpr (std::is_same_v<_U, std::any>) {
          return crane_any_cast<X>(x);
        } else {
          if constexpr (std::is_constructible_v<X, const _U &>) {
            return X(x);
          } else {
            throw std::logic_error("unreachable: inactive constructor field at "
                                   "this instantiation");
          }
        }
      }()};
    }
  }

  static EOU<X> raise_error(Nat s) { return EOU<X>(Raise_error{std::move(s)}); }

  static EOU<X> raise_ret(X x) { return EOU<X>(Raise_ret{std::move(x)}); }

  // MANIPULATORS
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

struct EOU0 {
  template <typename T1>
  static EOU<T1> option_ub(Nat s, const std::optional<T1> &x);
};

struct EOU_monad {
  template <typename _A0> using m = EOU<_A0>;

  template <typename _A0> static EOU<_A0> ret(_A0 x) {
    return EOU<_A0>::raise_ret(std::move(x));
  }

  template <typename _A0, typename _A1>
  static EOU<_A1> bind(EOU<_A0> c, std::function<EOU<_A1>(_A0)> k) {
    if (std::holds_alternative<typename EOU<_A0>::Raise_error>(c.v())) {
      const auto &[s0] = std::get<typename EOU<_A0>::Raise_error>(c.v());
      return EOU<_A1>::raise_error(s0);
    } else {
      const auto &[x0] = std::get<typename EOU<_A0>::Raise_ret>(c.v());
      return k(x0);
    }
  }
};

static_assert(Monad<EOU_monad>);

struct NamePrefixedByFile {
  static EOU<Nat> use(Nat n);
};

template <Monad _tcI0, typename T2>
typename _tcI0::template m<T2> Monad0::ret(const T2 &x) {
  return _tcI0::template ret<T2>(x);
}

template <Monad _tcI0, typename T2, typename T3, typename F1>
  requires std::is_invocable_r_v<typename _tcI0::template m<T3>, F1 &, T2 &>
typename _tcI0::template m<T3> Monad0::bind(typename _tcI0::template m<T2> x,
                                            F1 &&x0) {
  return _tcI0::template bind<T2, T3>(std::move(x), x0);
}

template <typename T1>
EOU<T1> EOU0::option_ub(Nat s, const std::optional<T1> &x) {
  if (x.has_value()) {
    const T1 &v = *x;
    return EOU<T1>::raise_ret(v);
  } else {
    return EOU<T1>::raise_error(std::move(s));
  }
}

#endif // INCLUDED_NAME_PREFIXED_BY_FILE
