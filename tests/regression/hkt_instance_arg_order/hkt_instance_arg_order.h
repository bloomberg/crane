#ifndef INCLUDED_HKT_INSTANCE_ARG_ORDER
#define INCLUDED_HKT_INSTANCE_ARG_ORDER

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
template <typename A> struct List;

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

/// Two instance arguments in one signature.  The declaration binds them in the
/// order the binders appear, but the call site passes them in the order the
/// constraints were discovered, so the outer and inner functors are swapped.

template <typename I>
concept Fn = requires {
  typename I::template F<std::any>;
  {
    I::template fm<std::any, std::any>(
        std::declval<std::function<std::any(std::any)>>(),
        std::declval<typename I::template F<std::any>>())
  } -> std::convertible_to<typename I::template F<std::any>>;
};

struct HktInstanceArgOrder {
  template <Fn _tcI0, typename T2, typename T3, typename F0>
    requires std::is_invocable_r_v<T3, F0 &, T2 &>
  static typename _tcI0::template F<T3> fm(F0 &&x,
                                           typename _tcI0::template F<T2> x0) {
    return _tcI0::template fm<T2, T3>(x, std::move(x0));
  }

  struct optf {
    template <typename _A0> using F = std::optional<_A0>;

    template <typename _A0, typename _A1>
    static std::optional<_A1> fm(std::function<_A1(_A0)> f,
                                 std::optional<_A0> o) {
      if (o.has_value()) {
        const _A0 &x = *o;
        return std::make_optional<_A1>(f(x));
      } else {
        return std::optional<_A1>();
      }
    }
  };

  static_assert(Fn<optf>);

  struct lstf {
    template <typename _A0> using F = List<_A0>;

    template <typename _A0, typename _A1>
    static List<_A1> fm(std::function<_A1(_A0)> a0, List<_A0> a1) {
      return a1.template map<_A1>(std::move(a0));
    }
  };

  static_assert(Fn<lstf>);

  template <Fn _tcI0, Fn _tcI1, typename T3, typename T4, typename F0>
    requires std::is_invocable_r_v<T4, F0 &, T3 &>
  static typename _tcI1::template F<typename _tcI0::template F<T4>>
  compose_map(F0 &&f,
              typename _tcI1::template F<typename _tcI0::template F<T3>> x) {
    return fm<_tcI1, typename _tcI0::template F<T3>,
              typename _tcI0::template F<T4>>(
        [=](typename _tcI0::template F<T3> _x0) mutable ->
        typename _tcI0::template F<T4> { return fm<_tcI0, T3, T4>(f, _x0); },
        std::move(x));
  }

  static inline const std::optional<List<Nat>> ex =
      compose_map<lstf, optf, Nat, Nat>(
          [](Nat x) { return Nat::s(x); },
          std::make_optional<List<Nat>>(
              List<Nat>::cons(Nat::s(Nat::o()), List<Nat>::nil())));
};

#endif // INCLUDED_HKT_INSTANCE_ARG_ORDER
