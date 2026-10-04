#ifndef INCLUDED_HKT_INSTANCE_ARG_ORDER
#define INCLUDED_HKT_INSTANCE_ARG_ORDER

#include "crane_fn.h"
#include "fn.h"
#include "obj.h"
#include <atomic>
#include <concepts>
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

/// Two instance arguments in one signature.  The declaration binds them in the
/// order the binders appear, but the call site passes them in the order the
/// constraints were discovered, so the outer and inner functors are swapped.

template <typename I>
concept Fn = requires {
  typename I::template F<crane::obj>;
  {
    I::template fm<crane::obj, crane::obj>(
        std::declval<crane::fn<crane::obj(crane::obj)>>(),
        std::declval<typename I::template F<crane::obj>>())
  } -> std::convertible_to<typename I::template F<crane::obj>>;
};

struct HktInstanceArgOrder {
  template <Fn _tcI0, typename T2, typename T3, typename F0>
  static typename _tcI0::template F<T3> fm(F0 &&x,
                                           typename _tcI0::template F<T2> x0) {
    return _tcI0::template fm<T2, T3>(x, std::move(x0));
  }

  struct optf {
    template <typename CraneA0> using F = std::optional<CraneA0>;

    template <typename CraneA0, typename CraneA1>
    static std::optional<CraneA1> fm(crane::fn<CraneA1(CraneA0)> f,
                                     std::optional<CraneA0> o) {
      if (o.has_value()) {
        const CraneA0 &x = *o;
        return std::make_optional<CraneA1>(f(x));
      } else {
        return std::optional<CraneA1>();
      }
    }
  };

  static_assert(Fn<optf>);

  struct lstf {
    template <typename CraneA0> using F = List<CraneA0>;

    template <typename CraneA0, typename CraneA1>
    static List<CraneA1> fm(crane::fn<CraneA1(CraneA0)> a0, List<CraneA0> a1) {
      return a1.template map<CraneA1>(std::move(a0));
    }
  };

  static_assert(Fn<lstf>);

  template <Fn _tcI0, Fn _tcI1, typename T3, typename T4, typename F0>
  static typename _tcI1::template F<typename _tcI0::template F<T4>>
  compose_map(F0 &&f,
              typename _tcI1::template F<typename _tcI0::template F<T3>> x) {
    return fm<_tcI1, typename _tcI0::template F<T3>,
              typename _tcI0::template F<T4>>(
        [=](typename _tcI0::template F<T3> _x0) ->
        typename _tcI0::template F<T4> { return fm<_tcI0, T3, T4>(f, _x0); },
        std::move(x));
  }

  static inline const std::optional<List<Nat>> ex =
      compose_map<lstf, optf, Nat, Nat>(
          [](const Nat &x) { return Nat::s(x); },
          std::make_optional<List<Nat>>(
              List<Nat>::cons(Nat::s(Nat::o()), List<Nat>::nil())));
};

#endif // INCLUDED_HKT_INSTANCE_ARG_ORDER
