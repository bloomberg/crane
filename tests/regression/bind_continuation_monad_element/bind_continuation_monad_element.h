#ifndef INCLUDED_BIND_CONTINUATION_MONAD_ELEMENT
#define INCLUDED_BIND_CONTINUATION_MONAD_ELEMENT

#include "crane_fn.h"
#include "fn.h"
#include "obj.h"
#include <atomic>
#include <concepts>
#include <memory>
#include <stdexcept>
#include <type_traits>
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
        std::declval<crane::fn<typename I::template m<crane::obj>(crane::obj)>>())
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

  static Nat s(crane::shared_child_slot<Nat> a0) { return Nat(S{a0.take()}); }

  // MANIPULATORS
  ~Nat() {
    // Release the children this node alone owns in a loop, not recursively, so
    // a deep value cannot overflow the stack.
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

  bool even() const {
    // Loop replaces the tail recursion: each recursive call updates the loop
    // variables.
    const Nat *_loop_self = this;
    while (true) {
      auto &&_sv = *_loop_self;
      if (std::holds_alternative<typename Nat::O>(_sv.v())) {
        return true;
      } else {
        const auto &[a0] = std::get<typename Nat::S>(_sv.v());
        auto &&_sv0 = *a0;
        if (std::holds_alternative<typename Nat::O>(_sv0.v())) {
          return false;
        } else {
          const auto &[a00] = std::get<typename Nat::S>(_sv0.v());
          _loop_self = crane_raw(a00);
        }
      }
    }
  }
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

  static List<A> cons(A a, crane::shared_child_slot<List<A>> l) {
    return List<A>(Cons{std::move(a), l.take()});
  }

  // MANIPULATORS
  ~List() {
    // Release the children this node alone owns in a loop, not recursively, so
    // a deep value cannot overflow the stack.
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

  List<A> rev_append(List<A> l_) const {
    // Loop replaces the tail recursion: each recursive call updates the loop
    // variables.
    const List<A> *_loop_self = this;
    List<A> _loop_l_ = std::move(l_);
    while (true) {
      auto &&_sv = *_loop_self;
      if (std::holds_alternative<typename List<A>::Nil>(_sv.v())) {
        return _loop_l_;
      } else {
        const auto &[a0, a1] = std::get<typename List<A>::Cons>(_sv.v());
        _loop_self = crane_raw(a1);
        _loop_l_ = List<A>::cons(a0, std::move(_loop_l_));
      }
    }
  }
};

struct Monad0 {
  template <Monad _tcI0, typename T2>
  static typename _tcI0::template m<T2> ret(const T2 &x);
  template <Monad _tcI0, typename T2, typename T3, typename F1>
  static typename _tcI0::template m<T3> bind(typename _tcI0::template m<T2> x,
                                             F1 &&x0);
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

  template <typename CraneU>
  EOU(const EOU<CraneU> &_other)
      : v_([&]() -> variant_t {
          if (std::holds_alternative<typename EOU<CraneU>::Ok>(_other.v())) {
            const auto &[a0] = std::get<typename EOU<CraneU>::Ok>(_other.v());
            return Ok{[&]() -> A {
              if constexpr (crane_convertible<A, const CraneU &>) {
                return crane_convert<A>(a0);
              } else {
                throw std::logic_error("unreachable: inactive constructor "
                                       "field at this instantiation");
              }
            }()};
          } else {
            const auto &[a0] = std::get<typename EOU<CraneU>::Err>(_other.v());
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
  template <typename CraneA0> using m = EOU<CraneA0>;

  template <typename CraneA0> static EOU<CraneA0> ret(CraneA0 a) {
    return EOU<CraneA0>::ok(std::move(a));
  }

  template <typename CraneA0, typename CraneA1>
  static EOU<CraneA1> bind(EOU<CraneA0> m, crane::fn<EOU<CraneA1>(CraneA0)> k) {
    if (std::holds_alternative<typename EOU<CraneA0>::Ok>(m.v_mut())) {
      auto &[a0] = std::get<typename EOU<CraneA0>::Ok>(m.v_mut());
      return k(std::move(a0));
    } else {
      auto &[a0] = std::get<typename EOU<CraneA0>::Err>(m.v_mut());
      return EOU<CraneA1>::err(std::move(a0));
    }
  }
};

static_assert(Monad<EOU_monad>);

struct BindContinuationMonadElement {
  template <Monad _tcI0, typename T2, typename T3, typename F0>
    requires std::is_invocable_r_v<typename _tcI0::template m<T3>, const F0 &,
                                   T2 &&>
  static typename _tcI0::template m<List<T3>> map_monad_acc(F0 &&f,
                                                            const List<T2> &l) {
    auto loop_impl =
        [=](auto &_self_loop, List<T3> acc,
            List<T2> l0)
             -> typename _tcI0::template m<List<T3>> {
          if (std::holds_alternative<typename List<T2>::Nil>(l0.v_mut())) {
            return _tcI0::template ret<List<T3>>(
                acc.rev_append(List<T3>::nil()));
          } else {
            auto &[a0, a1] = std::get<typename List<T2>::Cons>(l0.v_mut());
            const List<T2> &a1_value = *a1;
            return _tcI0::template bind<T3, List<T3>>(
                f(std::move(a0)), [=, acc = std::move(acc)](const T3 &b) {
                  return _self_loop(_self_loop, List<T3>::cons(b, acc),
                                    a1_value);
                });
          }
        };
    auto loop =
        [=, loop_impl = std::move(loop_impl)](List<T3> acc,
                                              List<T2> l0)
             -> typename _tcI0::template m<List<T3>> {
          return loop_impl(loop_impl, std::move(acc), std::move(l0));
        };
    return loop(List<T3>::nil(), l);
  }

  static inline const EOU<List<bool>> run = map_monad_acc<EOU_monad, Nat, bool>(
      [](const Nat &n) { return EOU<bool>::ok(n.even()); },
      List<Nat>::cons(
          Nat::s(Nat::o()),
          List<Nat>::cons(Nat::s(Nat::s(Nat::o())), List<Nat>::nil())));
};

template <Monad _tcI0, typename T2>
typename _tcI0::template m<T2> Monad0::ret(const T2 &x) {
  return _tcI0::template ret<T2>(x);
}

template <Monad _tcI0, typename T2, typename T3, typename F1>
typename _tcI0::template m<T3> Monad0::bind(typename _tcI0::template m<T2> x,
                                            F1 &&x0) {
  return _tcI0::template bind<T2, T3>(std::move(x), x0);
}

#endif // INCLUDED_BIND_CONTINUATION_MONAD_ELEMENT
