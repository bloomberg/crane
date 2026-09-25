#ifndef INCLUDED_LIFTED_INNER_FIX_DROPS_CLASS_PARAM
#define INCLUDED_LIFTED_INNER_FIX_DROPS_CLASS_PARAM

#include "crane_fn.h"
#include "small_vector.h"
#include <any>
#include <atomic>
#include <concepts>
#include <memory>
#include <optional>
#include <stdexcept>
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
template <typename I>
concept Params = requires {
  typename I::PTR;
  typename I::IPTR;
};
template <typename ptr, typename iptr> using dv = std::pair<ptr, iptr>;
/// The monad the inner fix returns into.
template <typename a> using EOU = std::optional<a>;

template <typename T1> EOU<T1> eou_ret(T1 a) {
  return std::make_optional<T1>(a);
}

/// The outer Fixpoint is what makes the inner one a let-bound fix
/// rather than a top-level definition.
template <Params _tcI0> auto _collect_go_all(const std::optional<Nat> pad) {
  auto go_impl =
      [=](auto &_self_go, auto m,
          List<dv<typename _tcI0::PTR::ptr, typename _tcI0::IPTR::iptr>>
              ys) mutable
      -> std::optional<
          List<dv<typename _tcI0::PTR::ptr, typename _tcI0::IPTR::iptr>>> {
    if (std::holds_alternative<typename List<
            dv<typename _tcI0::PTR::ptr, typename _tcI0::IPTR::iptr>>::Nil>(
            ys.v())) {
      return eou_ret<
          List<dv<typename _tcI0::PTR::ptr, typename _tcI0::IPTR::iptr>>>(
          List<
              dv<typename _tcI0::PTR::ptr, typename _tcI0::IPTR::iptr>>::nil());
    } else {
      const auto &[a0, a1] = std::get<typename List<
          dv<typename _tcI0::PTR::ptr, typename _tcI0::IPTR::iptr>>::Cons>(
          ys.v());
      auto _cs = _self_go(_self_go, m, *a1);
      if (_cs.has_value()) {
        const List<dv<typename _tcI0::PTR::ptr, typename _tcI0::IPTR::iptr>>
            &rest = *_cs;
        return eou_ret<
            List<dv<typename _tcI0::PTR::ptr, typename _tcI0::IPTR::iptr>>>(
            List<dv<typename _tcI0::PTR::ptr,
                    typename _tcI0::IPTR::iptr>>::cons(a0, rest));
      } else {
        if (pad.has_value()) {
          const Nat &_x = *pad;
          return std::optional<
              List<dv<typename _tcI0::PTR::ptr, typename _tcI0::IPTR::iptr>>>();
        } else {
          return std::optional<
              List<dv<typename _tcI0::PTR::ptr, typename _tcI0::IPTR::iptr>>>();
        }
      }
    }
  };
  auto go = [=](auto m,
                List<dv<typename _tcI0::PTR::ptr, typename _tcI0::IPTR::iptr>>
                    ys) mutable
      -> std::optional<
          List<dv<typename _tcI0::PTR::ptr, typename _tcI0::IPTR::iptr>>> {
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
    return std::optional<
        std::pair<typename _tcI0::PTR::ptr, typename _tcI0::IPTR::iptr>>();
  } else {
    const auto &[a00, a10] = std::get<typename List<
        std::pair<typename _tcI0::PTR::ptr, typename _tcI0::IPTR::iptr>>::Cons>(
        xs.v());
    if (std::holds_alternative<typename Nat::O>(n.v())) {
      auto _cs = _collect_go_all<_tcI0>(std::optional<Nat>())(n, xs);
      if (_cs.has_value()) {
        const List<dv<typename _tcI0::PTR::ptr, typename _tcI0::IPTR::iptr>>
            &l = *_cs;
        if (std::holds_alternative<typename List<
                dv<typename _tcI0::PTR::ptr, typename _tcI0::IPTR::iptr>>::Nil>(
                l.v())) {
          return eou_ret<
              dv<typename _tcI0::PTR::ptr, typename _tcI0::IPTR::iptr>>(a00);
        } else {
          const auto &[a02, a12] = std::get<typename List<
              dv<typename _tcI0::PTR::ptr, typename _tcI0::IPTR::iptr>>::Cons>(
              l.v());
          return eou_ret<
              dv<typename _tcI0::PTR::ptr, typename _tcI0::IPTR::iptr>>(a02);
        }
      } else {
        return eou_ret<
            dv<typename _tcI0::PTR::ptr, typename _tcI0::IPTR::iptr>>(a00);
      }
    } else {
      const auto &[a01] = std::get<typename Nat::S>(n.v());
      return collect<_tcI0>(*a01, *a10);
    }
  }
}

struct LiftedInnerFixDropsClassParam {
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

#endif // INCLUDED_LIFTED_INNER_FIX_DROPS_CLASS_PARAM
