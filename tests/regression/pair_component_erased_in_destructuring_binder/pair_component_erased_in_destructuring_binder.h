#ifndef INCLUDED_PAIR_COMPONENT_ERASED_IN_DESTRUCTURING_BINDER
#define INCLUDED_PAIR_COMPONENT_ERASED_IN_DESTRUCTURING_BINDER

#include "crane_fn.h"
#include "fn.h"
#include "obj.h"
#include <any>
#include <atomic>
#include <concepts>
#include <crane_itree.h>
#include <memory>
#include <stdexcept>
#include <utility>
#include <variant>

struct Nat;
template <typename A> struct List;
template <typename A> struct EOU;
struct EOU_monad;
template <typename I>
concept Monad = requires {
  typename I::template m<crane::obj>;
  {
    I::template ret<crane::obj>(std::declval<crane::obj>())
  } -> std::convertible_to<typename I::template m<crane::obj>>;
  {
    I::template bind<crane::obj, crane::obj>(
        std::declval<typename I::template m<crane::obj>>(),
        std::declval<
            crane::fn<typename I::template m<crane::obj>(crane::obj)>>())
  } -> std::convertible_to<typename I::template m<crane::obj>>;
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
};

template <typename A> struct EOU {
  // TYPES
  struct Ok {
    A a0;
  };

  struct Err {
    Nat a0;
  };

  using variant_t = std::variant<Ok, Err>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  EOU() {}

  explicit EOU(Ok _v) : v_(std::move(_v)) {}

  explicit EOU(Err _v) : v_(std::move(_v)) {}

  template <typename _U>
  EOU(const EOU<_U> &_other)
      : v_([&]() -> variant_t {
          if (std::holds_alternative<typename EOU<_U>::Ok>(_other.v())) {
            const auto &[a0] = std::get<typename EOU<_U>::Ok>(_other.v());
            return Ok{[&]() -> A {
              if constexpr (crane_convertible<A, const _U &>) {
                return crane_convert<A>(a0);
              } else {
                throw std::logic_error("unreachable: inactive constructor "
                                       "field at this instantiation");
              }
            }()};
          } else {
            const auto &[a0] = std::get<typename EOU<_U>::Err>(_other.v());
            return Err{a0};
          }
        }()) {}

  static EOU<A> ok(A a0) { return EOU<A>(Ok{std::move(a0)}); }

  static EOU<A> err(Nat a0) { return EOU<A>(Err{std::move(a0)}); }

  // MANIPULATORS
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

struct EOU_monad {
  template <typename _A0> using m = EOU<_A0>;

  template <typename _A0> static EOU<_A0> ret(_A0 a) {
    return EOU<_A0>::ok(std::move(a));
  }

  template <typename _A0, typename _A1>
  static EOU<_A1> bind(EOU<_A0> m, crane::fn<EOU<_A1>(_A0)> k) {
    if (std::holds_alternative<typename EOU<_A0>::Ok>(m.v())) {
      const auto &[a0] = std::get<typename EOU<_A0>::Ok>(m.v());
      return k(a0);
    } else {
      const auto &[a0] = std::get<typename EOU<_A0>::Err>(m.v());
      return EOU<_A1>::err(a0);
    }
  }
};

static_assert(Monad<EOU_monad>);

template <typename T1, typename T2>
EOU<std::pair<List<std::pair<T1, T2>>, List<T2>>> combine(const List<T2> &l) {
  return EOU_monad::template ret<std::pair<List<std::pair<T1, T2>>, List<T2>>>(
      std::make_pair(List<std::pair<T1, T2>>::nil(), l));
}

template <typename T1, typename T2>
EOU<std::pair<List<std::pair<T1, T2>>, List<T2>>> go(const T1 &a, const T2 &b,
                                                     const List<T2> &l) {
  return EOU_monad::template bind<std::pair<List<std::pair<T1, T2>>, List<T2>>,
                                  std::pair<List<std::pair<T1, T2>>, List<T2>>>(
      combine<T1, T2>(l), [=](std::pair<List<std::pair<T1, T2>>, List<T2>> x) {
        const auto &[p, vargs] = x;
        return EOU_monad::template ret<
            std::pair<List<std::pair<T1, T2>>, List<T2>>>(std::make_pair(
            List<std::pair<T1, T2>>::cons(std::make_pair(a, b), p), vargs));
      });
}

struct PairComponentErasedInDestructuringBinder {
  static inline const EOU<std::pair<List<std::pair<Nat, Nat>>, List<Nat>>> run =
      go<Nat, Nat>(
          Nat::s(Nat::o()), Nat::s(Nat::s(Nat::o())),
          List<Nat>::cons(Nat::s(Nat::s(Nat::s(Nat::o()))), List<Nat>::nil()));
};

#endif // INCLUDED_PAIR_COMPONENT_ERASED_IN_DESTRUCTURING_BINDER
