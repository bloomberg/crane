#ifndef INCLUDED_HK_CARRIER_WRITTEN_AT_PARTIAL_APP
#define INCLUDED_HK_CARRIER_WRITTEN_AT_PARTIAL_APP

#include "crane_fn.h"
#include "fn.h"
#include "obj.h"
#include <any>
#include <atomic>
#include <memory>
#include <stdexcept>
#include <type_traits>
#include <utility>
#include <variant>

struct Nat;
template <typename A> struct List;
template <typename T> struct Exp0;
template <typename T> struct Phi;

struct HkCarrierWrittenAtPartialApp {
  static Nat bump(const Nat &n);
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

  template <typename _U>
  List(const List<_U> &_other)
      : v_([&]() -> variant_t {
          if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
            return Nil{};
          } else {
            const auto &[a, l] = std::get<typename List<_U>::Cons>(_other.v());
            return Cons{
                [&]() -> A {
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
        }()) {}

  static List<A> nil() { return List<A>(Nil{}); }

  static List<A> cons(A a, List<A> l) {
    return List<A>(Cons{std::move(a), std::make_shared<List<A>>(std::move(l))});
  }

  // MANIPULATORS
  ~List() {
    auto _next = [&](variant_t &_v) -> std::shared_ptr<List<A>> {
      if (auto *_alt = std::get_if<Cons>(&_v)) {
        if (_alt->l && _alt->l.use_count() == 1) {
          std::atomic_thread_fence(std::memory_order_acquire);
          return std::move(_alt->l);
        }
      }
      return nullptr;
    };
    std::shared_ptr<List<A>> _cur = _next(v_mut());
    while (_cur) {
      _cur = _next(_cur->v_mut());
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

template <typename t>
using TFunctor = crane::fn<t(crane::fn<crane::obj(crane::obj)>, t)>;

template <typename T1, typename T2, typename T3, typename F1>
crane::rebind_t<T1, T3> tfmap(std::type_identity_t<TFunctor<T1>> tFunctor,
                              F1 &&x, crane::rebind_t<T1, T2> x0) {
  return crane_container_cast<crane::rebind_t<T1, T3>>(
      tFunctor(crane_erase_fn(x), crane_convert<T1>(std::move(x0))));
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

  template <typename _U>
  Exp0(const Exp0<_U> &_other)
      : v_([&]() -> variant_t {
          if (std::holds_alternative<typename Exp0<_U>::Var>(_other.v())) {
            const auto &[t] = std::get<typename Exp0<_U>::Var>(_other.v());
            return Var{[&]() -> T {
              if constexpr (crane_convertible<T, const _U &>) {
                return crane_convert<T>(t);
              } else {
                throw std::logic_error("unreachable: inactive constructor "
                                       "field at this instantiation");
              }
            }()};
          } else {
            const auto &[n] = std::get<typename Exp0<_U>::Lit>(_other.v());
            return Lit{n};
          }
        }()) {}

  static Exp0<T> var(T t) { return Exp0<T>(Var{std::move(t)}); }

  static Exp0<T> lit(Nat n) { return Exp0<T>(Lit{std::move(n)}); }

  // MANIPULATORS
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

  template <typename F0> Exp0<crane::obj> TFunctor_exp(F0 &&f) const {
    if (std::holds_alternative<typename Exp0<crane::obj>::Var>(this->v())) {
      const auto &[t0] = std::get<typename Exp0<crane::obj>::Var>(this->v());
      return Exp0<crane::obj>::var(crane_call_erased(f, t0));
    } else {
      const auto &[n0] = std::get<typename Exp0<crane::obj>::Lit>(this->v());
      return Exp0<crane::obj>::lit(n0);
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

Phi<crane::obj> TFunctor_phi(TFunctor<Exp0<crane::obj>> h,
                             crane::fn<crane::obj(crane::obj)> f,
                             const Phi<crane::obj> &p);

#endif // INCLUDED_HK_CARRIER_WRITTEN_AT_PARTIAL_APP
