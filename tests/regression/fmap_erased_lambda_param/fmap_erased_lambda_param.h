#ifndef INCLUDED_FMAP_ERASED_LAMBDA_PARAM
#define INCLUDED_FMAP_ERASED_LAMBDA_PARAM

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

struct Nat;
template <typename A, typename B> struct Sum;
enum class Exc;
struct Dv;
struct Monad_option;

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

template <typename A, typename B> struct Sum {
  // TYPES
  struct Inl {
    A a0;
  };

  struct Inr {
    B a0;
  };

  using variant_t = std::variant<Inl, Inr>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  Sum() {}

  explicit Sum(Inl _v) : v_(std::move(_v)) {}

  explicit Sum(Inr _v) : v_(std::move(_v)) {}

  template <typename _U0, typename _U1> Sum(const Sum<_U0, _U1> &_other) {
    if (std::holds_alternative<typename Sum<_U0, _U1>::Inl>(_other.v())) {
      const auto &[a0] = std::get<typename Sum<_U0, _U1>::Inl>(_other.v());
      this->v_ = Inl{[&]() -> A {
        if constexpr (crane_convertible<A, const _U0 &>) {
          return crane_convert<A>(a0);
        } else {
          throw std::logic_error(
              "unreachable: inactive constructor field at this instantiation");
        }
      }()};
    } else {
      const auto &[a0] = std::get<typename Sum<_U0, _U1>::Inr>(_other.v());
      this->v_ = Inr{[&]() -> B {
        if constexpr (crane_convertible<B, const _U1 &>) {
          return crane_convert<B>(a0);
        } else {
          throw std::logic_error(
              "unreachable: inactive constructor field at this instantiation");
        }
      }()};
    }
  }

  static Sum<A, B> inl(A a0) { return Sum<A, B>(Inl{std::move(a0)}); }

  static Sum<A, B> inr(B a0) { return Sum<A, B>(Inr{std::move(a0)}); }

  // MANIPULATORS
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

template <typename I>
concept Functor = requires {
  typename I::template F<std::any>;
  {
    I::template fmap<std::any, std::any>(
        std::declval<std::function<std::any(std::any)>>(),
        std::declval<typename I::template F<std::any>>())
  } -> std::convertible_to<typename I::template F<std::any>>;
};

struct Functor0 {
  template <Functor _tcI0, typename T2, typename T3, typename F0>
    requires std::is_invocable_r_v<T3, F0 &, T2 &>
  static typename _tcI0::template F<T3> fmap(F0 &&x,
                                             typename _tcI0::template F<T2> x0);
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
enum class Exc { OOPS };

struct Dv {
  // DATA
  Nat n;

  // ACCESSORS
  Dv clone() const { return {n}; }

  // CREATORS
  static Dv DV_(Nat n) { return {std::move(n)}; }
};

template <Monad _tcI0> struct Functor_Monad {
  template <typename _A0> using m = typename _tcI0::template m<_A0>;
  template <typename _A0> using F = typename _tcI0::template m<_A0>;

  template <typename _A0, typename _A1>
  static typename _tcI0::template m<_A1>
  fmap(std::function<_A1(_A0)> f, typename _tcI0::template m<_A0> x) {
    return Monad0::template bind<_tcI0, _A0, _A1>(
        std::move(x), [=](const _A0 &a) mutable {
          return Monad0::template ret<_tcI0, _A1>(f(a));
        });
  }
};

struct Monad_option {
  template <typename _A0> using m = std::optional<_A0>;

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

static_assert(Monad<Monad_option>);

template <Monad _tcI0>
typename _tcI0::template m<Sum<Exc, Dv>>
raise_right(typename _tcI0::template m<Dv> m) {
  return Functor0::template fmap<Functor_Monad<_tcI0>, Dv, Sum<Exc, Dv>>(
      [](Dv x) { return Sum<Exc, Dv>::inr(x); }, std::move(m));
}

struct FmapErasedLambdaParam {
  static std::optional<Sum<Exc, Dv>> go(Nat n);
};

template <Functor _tcI0, typename T2, typename T3, typename F0>
  requires std::is_invocable_r_v<T3, F0 &, T2 &>
typename _tcI0::template F<T3>
Functor0::fmap(F0 &&x, typename _tcI0::template F<T2> x0) {
  return _tcI0::template fmap<T2, T3>(x, std::move(x0));
}

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

#endif // INCLUDED_FMAP_ERASED_LAMBDA_PARAM
