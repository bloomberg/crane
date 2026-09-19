#ifndef INCLUDED_HANDLER_CASE_HAS_NO_NAME
#define INCLUDED_HANDLER_CASE_HAS_NO_NAME

#include "crane_fn.h"
#include "small_vector.h"
#include <any>
#include <atomic>
#include <concepts>
#include <crane_itree.h>
#include <functional>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

struct Nat;
template <typename A, typename B> struct Sum;
enum class AE;
enum class BE;

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
        if constexpr (std::is_same_v<_U0, std::any>) {
          return crane_any_cast<A>(a0);
        } else {
          return A(a0);
        }
      }()};
    } else {
      const auto &[a0] = std::get<typename Sum<_U0, _U1>::Inr>(_other.v());
      this->v_ = Inr{[&]() -> B {
        if constexpr (std::is_same_v<_U1, std::any>) {
          return crane_any_cast<B>(a0);
        } else {
          return B(a0);
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
    I::bind(std::declval<typename I::template m<std::any>>(),
            std::declval<
                std::function<typename I::template m<std::any>(std::any)>>())
  } -> std::convertible_to<typename I::template m<std::any>>;
};
template <template <typename> class m>
using MonadIter = std::function<m<std::any>(
    std::function<m<Sum<std::any, std::any>>(std::any)>, std::any)>;

struct Basics {
  template <typename T2, typename T3, typename F1>
  static std::invoke_result_t<F1 &, T3 &> iter(MonadIter<T1> monadIter, F1 &&x,
                                               const T3 &x0);
};

struct Handler {
  template <typename T1, typename T2, typename T3 = void, typename T4,
            typename F0, typename F1, typename _P0, typename _P1>
  static std::shared_ptr<ITree<T4>> case_(F0 &&f, F1 &&g,
                                          const Sum1<_P0, _P1, T4> &ab) {
    if (std::holds_alternative<
            typename Sum1<T1<std::any>, T2<std::any>, T4>::Inl1>(ab.v())) {
      const auto &[a0] =
          std::get<typename Sum1<T1<std::any>, T2<std::any>, T4>::Inl1>(ab.v());
      return f(a0);
    } else {
      const auto &[a0] =
          std::get<typename Sum1<T1<std::any>, T2<std::any>, T4>::Inr1>(ab.v());
      return g(a0);
    }
  }
};
template <template <typename> class e, typename f = void>
using Handler = std::function<std::shared_ptr<ITree<std::any>>(e<std::any>)>;
const<std::any, Handler<std::any, std::any>>
    Case_sum1_Handler = std::any_cast << std::any,
    Handler < std::any,
    std::any >>>
        ([=]<typename _X>(
             const std::function<std::shared_ptr<ITree<_X>>(_X)> &x) mutable {
          return [=](Sum1<T1<_X>, T2<_X>, T4> _x0) mutable
                     -> std::shared_ptr<ITree<T4>> {
            return Handler::case_(x, x0, _x0);
          };
        });

struct Interp {
  template <Monad _tcI0, Functor _tcI1, template <typename> class T1,
            typename T3, typename F1>
  static typename _tcI0::template m<T3> interp(MonadIter<_tcI0::template m> iM,
                                               F1 &&h0,
                                               std::shared_ptr<ITree<T3>> x0_);
};
enum class AE { A0 };
enum class BE { B0 };
template <typename x = void> using Eff = Sum1<AE, BE, x>;
std::shared_ptr<ITree<std::any>> e_trigger(AE e);
std::shared_ptr<ITree<std::any>> b_trigger(BE e);
std::shared_ptr<ITree<std::any>> h(Sum1<AE, BE, std::any, std::any> x);

struct HandlerCaseHasNoName {
  static std::shared_ptr<ITree<Nat>> use(Nat n);
};

template <Functor _tcI0, typename T2, typename T3, typename F0>
  requires std::is_invocable_r_v<T3, F0 &, T2 &>
typename _tcI0::template F<T3>
Functor0::fmap(F0 &&x, typename _tcI0::template F<T2> x0) {
  return _tcI0::template fmap<T2, T3>(x, std::move(x0));
}

template <typename T2, typename T3, typename F1>
std::invoke_result_t<F1 &, T3 &> Basics::iter(MonadIter<T1> monadIter, F1 &&x,
                                              const T3 &x0) {
  return monadIter(crane_erase_fn<T1<std::any, Sum<std::any, std::any>>>(x),
                   x0);
}

template <Monad _tcI0, Functor _tcI1, template <typename> class T1, typename T3,
          typename F1>
typename _tcI0::template m<T3> Interp::interp(MonadIter<_tcI0::template m> iM,
                                              F1 &&h0,
                                              std::shared_ptr<ITree<T3>> x0_) {
  return Basics::template iter<typename _tcI0::m, T3,
                               std::shared_ptr<ITree<T3>>>(
      std::move(iM),
      [=](const auto &t) mutable {
        auto _cs = t->observe();
        if (std::holds_alternative<typename ITree<T3>::Ret>(_cs)) {
          const auto &_itf = *std::get_if<typename ITree<T3>::Ret>(&_cs);
          auto r = _itf.value;
          return _tcI0::template ret<Sum<std::shared_ptr<ITree<T3>>, T3>>(
              Sum<std::shared_ptr<ITree<std::any>>, T3>::inr(r));
        } else if (std::holds_alternative<typename ITree<T3>::Tau>(_cs)) {
          const auto &_itf = *std::get_if<typename ITree<T3>::Tau>(&_cs);
          auto t0 = _itf.next;
          return _tcI0::template ret<Sum<std::shared_ptr<ITree<T3>>, T3>>(
              Sum<std::shared_ptr<ITree<T3>>, std::any>::inl(t0));
        } else {
          const auto &_itf = *std::get_if<typename ITree<T3>::Vis>(&_cs);
          auto e = _itf.effect;
          auto k = _itf.cont;
          return Functor0::template fmap<_tcI1>(
              [=](const auto &x) mutable {
                return Sum<std::shared_ptr<ITree<T3>>, T3>::inl(k(x));
              },
              h0(e));
        }
      },
      std::move(x0_));
}

#endif // INCLUDED_HANDLER_CASE_HAS_NO_NAME
