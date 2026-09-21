#ifndef INCLUDED_PAIR_FIELD_CONV_CTOR
#define INCLUDED_PAIR_FIELD_CONV_CTOR

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
struct Dt;
template <typename T> struct Exp0;
template <typename T> struct Ann;

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
                 if constexpr (std::is_same_v<_U, std::any>) {
                   return crane_any_cast<A>(a);
                 } else {
                   if constexpr (std::is_constructible_v<A, const _U &>) {
                     return A(a);
                   } else {
                     throw std::logic_error("unreachable: inactive constructor "
                                            "field at this instantiation");
                   }
                 }
               }(),
               (l ? std::make_shared<List<A>>(*l) : nullptr)};
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
template <template <typename> class f>
using TFunctor =
    std::function<f<std::any>(std::function<std::any(std::any)>, f<std::any>)>;

template <template <typename> class T1, typename T2, typename F1,
          typename T3 = std::invoke_result_t<F1 &, T2 &>>
T1<T3> tfmap(std::type_identity_t<TFunctor<T1>> tFunctor, F1 &&x, T1<T2> x0) {
  return crane_container_cast<T1<T3>>(
      tFunctor(crane_erase_fn(x), std::move(x0)));
}

struct Dt {
  // TYPES
  struct DI {
    Nat a0;
  };

  struct DP {};

  using variant_t = std::variant<DI, DP>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  Dt() {}

  explicit Dt(DI _v) : v_(std::move(_v)) {}

  explicit Dt(DP _v) : v_(_v) {}

  static Dt di(Nat a0) { return Dt(DI{std::move(a0)}); }

  static Dt dp() { return Dt(DP{}); }

  // MANIPULATORS
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

template <typename T> struct Exp0 {
  // TYPES
  struct EV {
    T a0;
  };

  struct EN {};

  using variant_t = std::variant<EV, EN>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  Exp0() {}

  explicit Exp0(EV _v) : v_(std::move(_v)) {}

  explicit Exp0(EN _v) : v_(_v) {}

  template <typename _U> Exp0(const Exp0<_U> &_other) {
    if (std::holds_alternative<typename Exp0<_U>::EV>(_other.v())) {
      const auto &[a0] = std::get<typename Exp0<_U>::EV>(_other.v());
      this->v_ = EV{[&]() -> T {
        if constexpr (std::is_same_v<_U, std::any>) {
          return crane_any_cast<T>(a0);
        } else {
          if constexpr (std::is_constructible_v<T, const _U &>) {
            return T(a0);
          } else {
            throw std::logic_error("unreachable: inactive constructor field at "
                                   "this instantiation");
          }
        }
      }()};
    } else {
      this->v_ = EN{};
    }
  }

  static Exp0<T> ev(T a0) { return Exp0<T>(EV{std::move(a0)}); }

  static Exp0<T> en() { return Exp0<T>(EN{}); }

  // MANIPULATORS
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

  template <typename F0> Exp0<std::any> TFunctor_exp(F0 &&f) const {
    if (std::holds_alternative<typename Exp0<std::any>::EV>(this->v())) {
      const auto &[a0] = std::get<typename Exp0<std::any>::EV>(this->v());
      return Exp0<std::any>::ev(crane_call_erased(f, a0));
    } else {
      return Exp0<std::any>::en();
    }
  }
};

template <typename t> using texp = std::pair<t, Exp0<t>>;

/// The two field kinds, side by side: a Crane container that converts, and a
/// std::pair that does not.
template <typename T> struct Ann {
  // TYPES
  struct ANN_metadata {
    List<T> a0;
  };

  struct ANN_prefix {
    texp<T> a0;
  };

  using variant_t = std::variant<ANN_metadata, ANN_prefix>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  Ann() {}

  explicit Ann(ANN_metadata _v) : v_(std::move(_v)) {}

  explicit Ann(ANN_prefix _v) : v_(std::move(_v)) {}

  template <typename _U> Ann(const Ann<_U> &_other) {
    if (std::holds_alternative<typename Ann<_U>::ANN_metadata>(_other.v())) {
      const auto &[a0] = std::get<typename Ann<_U>::ANN_metadata>(_other.v());
      this->v_ = ANN_metadata{crane_convert<List<T>>(a0)};
    } else {
      const auto &[a0] = std::get<typename Ann<_U>::ANN_prefix>(_other.v());
      this->v_ = ANN_prefix{crane_convert<texp<T>>(a0)};
    }
  }

  static Ann<T> ann_metadata(List<T> a0) {
    return Ann<T>(ANN_metadata{std::move(a0)});
  }

  static Ann<T> ann_prefix(texp<T> a0) {
    return Ann<T>(ANN_prefix{std::move(a0)});
  }

  // MANIPULATORS
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

Ann<std::any> TFunctor_ann(std::function<std::any(std::any)> f,
                           const Ann<std::any> &a);
Ann<Dt> run(const Ann<Nat> &a);

#endif // INCLUDED_PAIR_FIELD_CONV_CTOR
