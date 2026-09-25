#ifndef INCLUDED_INNER_FIX_CODOMAIN_FROM_CLASS
#define INCLUDED_INNER_FIX_CODOMAIN_FROM_CLASS

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
template <typename X> struct EOU;
struct EOU_monad;

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
};

template <typename
I>concept IPtr = requires {
  typename I::iptr;
} && (requires {
  { I::zero_iptr() } -> std::convertible_to<typename I::iptr>;
} || requires {
  { I::zero_iptr } -> std::convertible_to<typename I::iptr>;
});
using iptr = std::any;
template <typename
I>concept Ptr = requires {
  typename I::ptr;
} && (requires {
  { I::zero_ptr() } -> std::convertible_to<typename I::ptr>;
} || requires {
  { I::zero_ptr } -> std::convertible_to<typename I::ptr>;
});
using ptr = std::any;
/// Both fields are themselves instances, as Params is in Vellvm.
///
/// {b An earlier version of this comment said IPTR "is the one Crane writes;
/// it is the last field, and that is worth keeping in view".}  That was
/// speculation about the Vellvm artifact, not a measurement of this test, and
/// read as a measurement it contradicts the filler rule.  It is wrong twice
/// over.  This test emits {e no} bare typename _tcI0::IPTR at all --- all 29
/// occurrences of each field here are legitimate ::iptr and ::ptr
/// projections --- because its inner fix is {e lifted}, so the hole escapes
/// as an undeducible template parameter instead of being filled.  There is
/// nothing to fill and so nothing to be positional about.  And in Vellvm's own
/// Params, IPTR is the {e first} field, not the last.
///
/// The filler, where one exists, is the first Type-valued or instance field of
/// the enclosing class in declaration order; see
/// tests/wip/bind_continuation_binder_from_class_field.
template <typename I>
concept Params = requires {
  typename I::PTR;
  typename I::IPTR;
};
/// A monad class, as Vellvm reaches ret through ExtLib's.
template <typename I>
concept MyMonad = requires {
  typename I::template M<std::any>;
  {
    I::template mret<std::any>(std::declval<std::any>())
  } -> std::convertible_to<typename I::template M<std::any>>;
  {
    I::template mbind<std::any, std::any>(
        std::declval<typename I::template M<std::any>>(),
        std::declval<
            std::function<typename I::template M<std::any>(std::any)>>())
  } -> std::convertible_to<typename I::template M<std::any>>;
};

template <MyMonad _tcI0, typename T2>
typename _tcI0::template M<T2> mret(const T2 &x) {
  return _tcI0::template mret<T2>(x);
}

template <MyMonad _tcI0, typename T2, typename T3, typename F1>
  requires std::is_invocable_r_v<typename _tcI0::template M<T3>, F1 &, T2 &>
typename _tcI0::template M<T3> mbind(typename _tcI0::template M<T2> x,
                                     F1 &&x0) {
  return _tcI0::template mbind<T2, T3>(std::move(x), x0);
}

template <typename X> struct EOU {
  // TYPES
  struct Eou_err {};

  struct Eou_ret {
    X a0;
  };

  using variant_t = std::variant<Eou_err, Eou_ret>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  EOU() {}

  explicit EOU(Eou_err _v) : v_(_v) {}

  explicit EOU(Eou_ret _v) : v_(std::move(_v)) {}

  template <typename _U> EOU(const EOU<_U> &_other) {
    if (std::holds_alternative<typename EOU<_U>::Eou_err>(_other.v())) {
      this->v_ = Eou_err{};
    } else {
      const auto &[a0] = std::get<typename EOU<_U>::Eou_ret>(_other.v());
      this->v_ = Eou_ret{[&]() -> X {
        if constexpr (crane_convertible<X, const _U &>) {
          return crane_convert<X>(a0);
        } else {
          throw std::logic_error(
              "unreachable: inactive constructor field at this instantiation");
        }
      }()};
    }
  }

  static EOU<X> eou_err() { return EOU<X>(Eou_err{}); }

  static EOU<X> eou_ret(X a0) { return EOU<X>(Eou_ret{std::move(a0)}); }

  // MANIPULATORS
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

struct EOU_monad {
  template <typename _A0> using M = EOU<_A0>;

  template <typename _A0> static EOU<_A0> mret(_A0 x) {
    return EOU<_A0>::eou_ret(std::move(x));
  }

  template <typename _A0, typename _A1>
  static EOU<_A1> mbind(EOU<_A0> c, std::function<EOU<_A1>(_A0)> k) {
    if (std::holds_alternative<typename EOU<_A0>::Eou_err>(c.v())) {
      return EOU<_A1>::eou_err();
    } else {
      const auto &[a0] = std::get<typename EOU<_A0>::Eou_ret>(c.v());
      return k(a0);
    }
  }
};

static_assert(MyMonad<EOU_monad>);
template <typename ptr, typename iptr> using dv = std::pair<ptr, iptr>;

template <Params _tcI0> auto _collect_go_all(const std::optional<Nat> pad) {
  auto go_impl =
      [=](auto &_self_go, auto m,
          List<dv<typename _tcI0::PTR::ptr, typename _tcI0::IPTR::iptr>>
              ys) mutable
      -> EOU<List<dv<typename _tcI0::PTR::ptr, typename _tcI0::IPTR::iptr>>> {
    if (std::holds_alternative<typename List<
            dv<typename _tcI0::PTR::ptr, typename _tcI0::IPTR::iptr>>::Nil>(
            ys.v())) {
      return mret<
          EOU_monad,
          List<dv<typename _tcI0::PTR::ptr, typename _tcI0::IPTR::iptr>>>(
          List<
              dv<typename _tcI0::PTR::ptr, typename _tcI0::IPTR::iptr>>::nil());
    } else {
      const auto &[a0, a1] = std::get<typename List<
          dv<typename _tcI0::PTR::ptr, typename _tcI0::IPTR::iptr>>::Cons>(
          ys.v());
      const List<dv<typename _tcI0::PTR::ptr, typename _tcI0::IPTR::iptr>>
          &a1_value = *a1;
      return mbind<
          EOU_monad,
          List<dv<typename _tcI0::PTR::ptr, typename _tcI0::IPTR::iptr>>,
          List<dv<typename _tcI0::PTR::ptr, typename _tcI0::IPTR::iptr>>>(
          _self_go(_self_go, m, a1_value),
          [=](List<dv<typename _tcI0::PTR::ptr, typename _tcI0::IPTR::iptr>>
                  rest) mutable {
            if (pad.has_value()) {
              const Nat &_x = *pad;
              return mret<EOU_monad, List<dv<typename _tcI0::PTR::ptr,
                                             typename _tcI0::IPTR::iptr>>>(
                  List<dv<typename _tcI0::PTR::ptr,
                          typename _tcI0::IPTR::iptr>>::cons(a0, rest));
            } else {
              return mret<EOU_monad, List<dv<typename _tcI0::PTR::ptr,
                                             typename _tcI0::IPTR::iptr>>>(
                  rest);
            }
          });
    }
  };
  auto go = [=](auto m,
                List<dv<typename _tcI0::PTR::ptr, typename _tcI0::IPTR::iptr>>
                    ys) mutable
      -> EOU<List<dv<typename _tcI0::PTR::ptr, typename _tcI0::IPTR::iptr>>> {
    return go_impl(go_impl, m, ys);
  };
  return go;
}

template <Params _tcI0>
EOU<dv<typename _tcI0::PTR::ptr, typename _tcI0::IPTR::iptr>> collect(
    const Nat &n,
    const List<std::pair<typename _tcI0::PTR::ptr, typename _tcI0::IPTR::iptr>>
        &xs) {
  if (std::holds_alternative<typename List<std::pair<
          typename _tcI0::PTR::ptr, typename _tcI0::IPTR::iptr>>::Nil>(
          xs.v())) {
    return EOU<
        dv<typename _tcI0::PTR::ptr, typename _tcI0::IPTR::iptr>>::eou_err();
  } else {
    const auto &[a00, a10] = std::get<typename List<
        std::pair<typename _tcI0::PTR::ptr, typename _tcI0::IPTR::iptr>>::Cons>(
        xs.v());
    if (std::holds_alternative<typename Nat::O>(n.v())) {
      auto &&_sv2 = _collect_go_all<_tcI0>(std::optional<Nat>())(n, xs);
      if (std::holds_alternative<typename EOU<List<dv<
              typename _tcI0::PTR::ptr, typename _tcI0::IPTR::iptr>>>::Eou_err>(
              _sv2.v())) {
        return mret<EOU_monad,
                    dv<typename _tcI0::PTR::ptr, typename _tcI0::IPTR::iptr>>(
            a00);
      } else {
        const auto &[a02] = std::get<typename EOU<List<dv<
            typename _tcI0::PTR::ptr, typename _tcI0::IPTR::iptr>>>::Eou_ret>(
            _sv2.v());
        if (std::holds_alternative<typename List<
                dv<typename _tcI0::PTR::ptr, typename _tcI0::IPTR::iptr>>::Nil>(
                a02.v())) {
          return mret<EOU_monad,
                      dv<typename _tcI0::PTR::ptr, typename _tcI0::IPTR::iptr>>(
              a00);
        } else {
          const auto &[a03, a13] = std::get<typename List<
              dv<typename _tcI0::PTR::ptr, typename _tcI0::IPTR::iptr>>::Cons>(
              a02.v());
          return mret<EOU_monad,
                      dv<typename _tcI0::PTR::ptr, typename _tcI0::IPTR::iptr>>(
              a03);
        }
      }
    } else {
      const auto &[a01] = std::get<typename Nat::S>(n.v());
      return collect<_tcI0>(*a01, *a10);
    }
  }
}

struct InnerFixCodomainFromClass {
  template <Params _tcI0>
  static EOU<dv<typename _tcI0::PTR::ptr, typename _tcI0::IPTR::iptr>>
  use(std::pair<typename _tcI0::PTR::ptr, typename _tcI0::IPTR::iptr> x) {
    return collect<_tcI0>(
        Nat::o(),
        List<std::pair<typename _tcI0::PTR::ptr, typename _tcI0::IPTR::iptr>>::
            cons(std::move(x),
                 List<std::pair<typename _tcI0::PTR::ptr,
                                typename _tcI0::IPTR::iptr>>::nil()));
  }
};

#endif // INCLUDED_INNER_FIX_CODOMAIN_FROM_CLASS
