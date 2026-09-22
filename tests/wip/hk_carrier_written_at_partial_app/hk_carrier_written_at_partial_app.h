#ifndef INCLUDED_HK_CARRIER_WRITTEN_AT_PARTIAL_APP
#define INCLUDED_HK_CARRIER_WRITTEN_AT_PARTIAL_APP

#include "crane_fn.h"
#include "small_vector.h"
#include <any>
#include <atomic>
#include <functional>
#include <memory>
#include <stdexcept>
#include <type_traits>
#include <utility>
#include <variant>

struct Nat;
template <typename A> struct List;
template <typename T> struct Exp0;
template <typename T> struct Phi;

template <template <typename> class _F0> struct _crane_carrier_tch {
  template <typename _CraneTcArg>
  using c = std::function<Exp0<_CraneTcArg>(Exp0<_F0>)>;
};

struct HkCarrierWrittenAtPartialApp {
  static Nat bump(Nat n);
  static Phi<Nat> on_phi(const Phi<Nat> &p);
};

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

template <typename A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    A a;
    std::shared_ptr<List<A>> l;
  };

  using variant_t = std::variant<Nil, Cons>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  List() {}

  explicit List(Nil _v) : v_(_v) {}

  explicit List(Cons _v) : v_(std::move(_v)) {}

  template <typename _U> List(const List<_U> &_other) {
    if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
      this->v_ = Nil{};
    } else {
      const auto &[a, l] = std::get<typename List<_U>::Cons>(_other.v());
      this->v_ =
          Cons{[&]() -> A {
                 if constexpr (crane_convertible<A, const _U &>) {
                   return crane_convert<A>(a);
                 } else {
                   throw std::logic_error("unreachable: inactive constructor "
                                          "field at this instantiation");
                 }
               }(),
               (l ? std::make_shared<List<A>>(crane_convert<List<A>>(*l))
                  : nullptr)};
    }
  }

  static List<A> nil() { return List<A>(Nil{}); }

  static List<A> cons(A a, List<A> l) {
    return List<A>(Cons{std::move(a), std::make_shared<List<A>>(std::move(l))});
  }

  // MANIPULATORS
  ~List() {
    crane::small_vector<std::shared_ptr<List<A>>> _stack = {};
    auto _drain = [&](variant_t &_v) {
      if (auto *_alt = std::get_if<Cons>(&_v)) {
        if (_alt->l) {
          _stack.push_back(std::move(_alt->l));
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

  List(const List &) = default;
  List &operator=(const List &) = default;
  List(List &&) noexcept = default;
  List &operator=(List &&) noexcept = default;

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, A &>
  List<T1> map(F0 &&f) const {
    std::shared_ptr<List<T1>> _head{};
    std::shared_ptr<List<T1>> *_write = &_head;
    const List<A> *_loop_self = this;
    while (true) {
      auto &&_sv = *_loop_self;
      if (std::holds_alternative<typename List<A>::Nil>(_sv.v())) {
        *_write = std::make_shared<List<T1>>(List<T1>::nil());
        break;
      } else {
        const auto &[a0, a1] = std::get<typename List<A>::Cons>(_sv.v());
        auto _cell =
            std::make_shared<List<T1>>(typename List<T1>::Cons(f(a0), nullptr));
        *_write = std::move(_cell);
        _write = &std::get<typename List<T1>::Cons>((*_write)->v_mut()).l;
        _loop_self = crane_raw(a1);
        continue;
      }
    }
    return std::move(*_head);
  }
};
template <template <typename> class t>
using TFunctor =
    std::function<t<std::any>(std::function<std::any(std::any)>, t<std::any>)>;

template <template <typename> class T1, typename T2, typename F1,
          typename T3 = std::invoke_result_t<F1 &, T2 &>>
T1<T3> tfmap(std::type_identity_t<TFunctor<T1>> tFunctor, F1 &&x, T1<T2> x0) {
  return crane_container_cast<T1<T3>>(
      tFunctor(crane_erase_fn(x), crane_convert<T1<std::any>>(std::move(x0))));
}

template <typename T> struct Exp0 {
  // TYPES
  struct Var {
    T t;
  };

  struct Lit {
    Nat n;
  };

  using variant_t = std::variant<Var, Lit>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  Exp0() {}

  explicit Exp0(Var _v) : v_(std::move(_v)) {}

  explicit Exp0(Lit _v) : v_(std::move(_v)) {}

  template <typename _U> Exp0(const Exp0<_U> &_other) {
    if (std::holds_alternative<typename Exp0<_U>::Var>(_other.v())) {
      const auto &[t] = std::get<typename Exp0<_U>::Var>(_other.v());
      this->v_ = Var{[&]() -> T {
        if constexpr (crane_convertible<T, const _U &>) {
          return crane_convert<T>(t);
        } else {
          throw std::logic_error(
              "unreachable: inactive constructor field at this instantiation");
        }
      }()};
    } else {
      const auto &[n] = std::get<typename Exp0<_U>::Lit>(_other.v());
      this->v_ = Lit{n};
    }
  }

  static Exp0<T> var(T t) { return Exp0<T>(Var{std::move(t)}); }

  static Exp0<T> lit(Nat n) { return Exp0<T>(Lit{std::move(n)}); }

  // MANIPULATORS
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

  template <typename F0> Exp0<std::any> TFunctor_exp(F0 &&f) const {
    if (std::holds_alternative<typename Exp0<std::any>::Var>(this->v())) {
      const auto &[t0] = std::get<typename Exp0<std::any>::Var>(this->v());
      return Exp0<std::any>::var(crane_call_erased(f, t0));
    } else {
      const auto &[n0] = std::get<typename Exp0<std::any>::Lit>(this->v());
      return Exp0<std::any>::lit(n0);
    }
  }
};

template <typename T> struct Phi {
  // DATA
  List<Exp0<T>> es;

  // ACCESSORS
  Phi<T> clone() const { return {es}; }

  template <typename _U> operator Phi<_U>() const {
    return {crane_convert<List<Exp0<_U>>>(es)};
  }

  // CREATORS
  static Phi<T> phi0(List<Exp0<T>> es) { return {std::move(es)}; }
};

Phi<std::any> TFunctor_phi(std::type_identity_t<TFunctor<Exp0>> h,
                           std::function<std::any(std::any)> f,
                           const Phi<std::any> &p);

#endif // INCLUDED_HK_CARRIER_WRITTEN_AT_PARTIAL_APP
