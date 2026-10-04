#ifndef INCLUDED_PAIR_FIELD_CONV_CTOR
#define INCLUDED_PAIR_FIELD_CONV_CTOR

#include "crane_fn.h"
#include "fn.h"
#include "obj.h"
#include <atomic>
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

  template <typename CraneU>
  List(const List<CraneU> &_other)
      : v_([&]() -> variant_t {
          if (std::holds_alternative<typename List<CraneU>::Nil>(_other.v())) {
            return Nil{};
          } else {
            const auto &[a, l] =
                std::get<typename List<CraneU>::Cons>(_other.v());
            return Cons{
                [&]() -> A {
                  if constexpr (crane_convertible<A, const CraneU &>) {
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
  List(List &&) = default;
  List &operator=(List &&) = default;

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, const A &>
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

template <typename f>
using TFunctor = crane::fn<f(crane::fn<crane::obj(crane::obj)>, f)>;

template <typename T1, typename T2, typename T3, typename F1>
crane::rebind_t<T1, T3> tfmap(std::type_identity_t<TFunctor<T1>> tFunctor,
                              F1 &&x, crane::rebind_t<T1, T2> x0) {
  return crane_container_cast<crane::rebind_t<T1, T3>>(
      tFunctor(crane_erase_fn(x), crane_convert<T1>(std::move(x0))));
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

  template <typename CraneU>
  Exp0(const Exp0<CraneU> &_other)
      : v_([&]() -> variant_t {
          if (std::holds_alternative<typename Exp0<CraneU>::EV>(_other.v())) {
            const auto &[a0] = std::get<typename Exp0<CraneU>::EV>(_other.v());
            return EV{[&]() -> T {
              if constexpr (crane_convertible<T, const CraneU &>) {
                return crane_convert<T>(a0);
              } else {
                throw std::logic_error("unreachable: inactive constructor "
                                       "field at this instantiation");
              }
            }()};
          } else {
            return EN{};
          }
        }()) {}

  static Exp0<T> ev(T a0) { return Exp0<T>(EV{std::move(a0)}); }

  static Exp0<T> en() { return Exp0<T>(EN{}); }

  // MANIPULATORS
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

  template <typename F0> Exp0<crane::obj> TFunctor_exp(F0 &&f) const {
    if (std::holds_alternative<typename Exp0<crane::obj>::EV>(this->v())) {
      const auto &[a0] = std::get<typename Exp0<crane::obj>::EV>(this->v());
      return Exp0<crane::obj>::ev(crane_call_erased(f, a0));
    } else {
      return Exp0<crane::obj>::en();
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

  template <typename CraneU>
  Ann(const Ann<CraneU> &_other)
      : v_([&]() -> variant_t {
          if (std::holds_alternative<typename Ann<CraneU>::ANN_metadata>(
                  _other.v())) {
            const auto &[a0] =
                std::get<typename Ann<CraneU>::ANN_metadata>(_other.v());
            return ANN_metadata{crane_convert<List<T>>(a0)};
          } else {
            const auto &[a0] =
                std::get<typename Ann<CraneU>::ANN_prefix>(_other.v());
            return ANN_prefix{crane_convert<texp<T>>(a0)};
          }
        }()) {}

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

Ann<crane::obj> TFunctor_ann(crane::fn<crane::obj(crane::obj)> f,
                             const Ann<crane::obj> &a);

Ann<Dt> run(const Ann<Nat> &a);

#endif // INCLUDED_PAIR_FIELD_CONV_CTOR
