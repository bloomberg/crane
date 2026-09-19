#ifndef INCLUDED_HK_CLASS_ARG_NUMBERING
#define INCLUDED_HK_CLASS_ARG_NUMBERING

#include "crane_fn.h"
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

struct Monad_option;
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

template <typename I>
concept Functor = requires {
  typename I::template F<std::any>;
  {
    I::fmap(std::declval<std::function<std::any(std::any)>>(),
            std::declval<typename I::template F<std::any>>())
  } -> std::convertible_to<typename I::template F<std::any>>;
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
  template <Monad _tcI0, typename T2, typename T3, typename F0>
    requires std::is_invocable_r_v<T3, F0 &, T2 &>
  static typename _tcI0::template m<T3> liftM(F0 &&f,
                                              typename _tcI0::template m<T2> x);
};

template <Monad _tcI0> struct Functor_Monad {
  template <typename _A0> using m = typename _tcI0::template m<_A0>;
  template <typename _A0> using F = typename _tcI0::template m<_A0>;

  static typename _tcI0::template m<std::any>
  fmap(std::function<std::any(std::any)> a0,
       typename _tcI0::template m<std::any> a1) {
    return Monad0::template liftM<_tcI0>(std::move(a0), std::move(a1));
  }
};

struct Monad_option {
  template <typename _A0> using m = std::optional<_A0>;

  template <typename _A0> static std::optional<_A0> ret(_A0 x) {
    return std::make_optional<_A0>(x);
  }

  template <typename _A0, typename _A1>
  static std::optional<_A1> bind(std::optional<_A0> c1,
                                 std::function<std::optional<_A1>(_A0)> c2) {
    if (c1.has_value()) {
      const _A0 &v = *c1;
      return c2(v);
    } else {
      return std::optional<_A1>();
    }
  }
};

static_assert(Monad<Monad_option>);
template <template <typename> class m>
using Iter =
    std::function<m<std::any>(std::function<m<std::any>(std::any)>, std::any)>;

template <template <typename> class T1, typename T2, typename F1>
T1<T2> iter(Iter<T1> iter0, F1 &&x, const T2 &x0) {
  return crane_container_cast<T1<T2>>(
      iter0(crane_erase_fn<T1<std::any>>(x), x0));
}

template <Functor _tcI0, Monad _tcI1, typename T2, typename F1>
  requires std::is_invocable_r_v<typename _tcI0::template F<T2>, F1 &, T2 &>
typename _tcI0::template F<T2> run(Iter<_tcI0::template F> x0_, F1 &&x1_,
                                   const T2 &x2_) {
  return iter<_tcI0::template F, T2>(std::move(x0_), x1_, x2_);
}

template <typename F0>
std::optional<std::any> Iter_option(F0 &&f, std::any x0_) {
  return f(x0_);
}

struct HkClassArgNumbering {
  static std::optional<Nat> use(const Nat &n);
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

template <Monad _tcI0, typename T2, typename T3, typename F0>
  requires std::is_invocable_r_v<T3, F0 &, T2 &>
typename _tcI0::template m<T3> Monad0::liftM(F0 &&f,
                                             typename _tcI0::template m<T2> x) {
  return Monad0::template bind<_tcI0, T2, T3>(
      std::move(x), [=](const T2 &x0) mutable {
        return Monad0::template ret<_tcI0, T3>(f(x0));
      });
}

#endif // INCLUDED_HK_CLASS_ARG_NUMBERING
