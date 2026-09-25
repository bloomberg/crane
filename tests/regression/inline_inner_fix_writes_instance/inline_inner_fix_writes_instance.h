#ifndef INCLUDED_INLINE_INNER_FIX_WRITES_INSTANCE
#define INCLUDED_INLINE_INNER_FIX_WRITES_INSTANCE

#include "crane_fn.h"
#include "small_vector.h"
#include <any>
#include <atomic>
#include <concepts>
#include <functional>
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
/// The monad the inner fix returns into, a plain inductive as Vellvm's
/// EOU is --- the class-typed part of the return type is dv, not the
/// carrier.
template <typename a> using EOU = std::optional<a>;

template <typename T1> EOU<T1> eou_ret(T1 a) {
  return std::make_optional<T1>(a);
}

template <Params _tcI0>
EOU<dv<typename _tcI0::PTR::ptr, typename _tcI0::IPTR::iptr>> collect(
    const Nat &n,
    const List<std::pair<typename _tcI0::PTR::ptr, typename _tcI0::IPTR::iptr>>
        &xs) {
  std::function<std::optional<
      List<dv<typename _tcI0::PTR::ptr, typename _tcI0::IPTR::iptr>>>(
      std::optional<Nat>, Nat,
      List<dv<typename _tcI0::PTR::ptr, typename _tcI0::IPTR::iptr>>)>
      go_all = [](std::optional<Nat> pad, const Nat &x,
                  const List<dv<typename _tcI0::PTR::ptr,
                                typename _tcI0::IPTR::iptr>> &x0) {
        auto go_impl = [&](auto &_self_go, const Nat &m,
                           const List<dv<typename _tcI0::PTR::ptr,
                                         typename _tcI0::IPTR::iptr>> &ys)
            -> std::optional<List<
                dv<typename _tcI0::PTR::ptr, typename _tcI0::IPTR::iptr>>> {
          if (std::holds_alternative<typename List<dv<
                  typename _tcI0::PTR::ptr, typename _tcI0::IPTR::iptr>>::Nil>(
                  ys.v())) {
            return eou_ret<
                List<dv<typename _tcI0::PTR::ptr, typename _tcI0::IPTR::iptr>>>(
                List<dv<typename _tcI0::PTR::ptr,
                        typename _tcI0::IPTR::iptr>>::nil());
          } else {
            const auto &[a0, a1] =
                std::get<typename List<dv<typename _tcI0::PTR::ptr,
                                          typename _tcI0::IPTR::iptr>>::Cons>(
                    ys.v());
            auto _cs = collect<_tcI0>(m, *a1);
            if (_cs.has_value()) {
              const dv<typename _tcI0::PTR::ptr, typename _tcI0::IPTR::iptr>
                  &z = *_cs;
              auto _cs1 = _self_go(_self_go, m, *a1);
              if (_cs1.has_value()) {
                const List<dv<typename _tcI0::PTR::ptr,
                              typename _tcI0::IPTR::iptr>> &rest = *_cs1;
                return eou_ret<List<
                    dv<typename _tcI0::PTR::ptr, typename _tcI0::IPTR::iptr>>>(
                    List<dv<typename _tcI0::PTR::ptr,
                            typename _tcI0::IPTR::iptr>>::cons(z, rest));
              } else {
                if (pad.has_value()) {
                  const Nat &_x0 = *pad;
                  return std::optional<List<dv<typename _tcI0::PTR::ptr,
                                               typename _tcI0::IPTR::iptr>>>();
                } else {
                  return std::optional<List<dv<typename _tcI0::PTR::ptr,
                                               typename _tcI0::IPTR::iptr>>>();
                }
              }
            } else {
              return std::optional<List<
                  dv<typename _tcI0::PTR::ptr, typename _tcI0::IPTR::iptr>>>();
            }
          }
        };
        auto go = [&](const Nat &m,
                      const List<dv<typename _tcI0::PTR::ptr,
                                    typename _tcI0::IPTR::iptr>> &ys)
            -> std::optional<List<
                dv<typename _tcI0::PTR::ptr, typename _tcI0::IPTR::iptr>>> {
          return go_impl(go_impl, m, ys);
        };
        return go(x, x0);
      };
  if (std::holds_alternative<typename List<std::pair<
          typename _tcI0::PTR::ptr, typename _tcI0::IPTR::iptr>>::Nil>(
          xs.v())) {
    return std::optional<
        std::pair<typename _tcI0::PTR::ptr, typename _tcI0::IPTR::iptr>>();
  } else {
    const auto &[a0, a1] = std::get<typename List<
        std::pair<typename _tcI0::PTR::ptr, typename _tcI0::IPTR::iptr>>::Cons>(
        xs.v());
    if (std::holds_alternative<typename Nat::O>(n.v())) {
      auto _cs = go_all(std::optional<Nat>(), n, xs);
      if (_cs.has_value()) {
        const List<dv<typename _tcI0::PTR::ptr, typename _tcI0::IPTR::iptr>>
            &l = *_cs;
        if (std::holds_alternative<typename List<
                dv<typename _tcI0::PTR::ptr, typename _tcI0::IPTR::iptr>>::Nil>(
                l.v())) {
          return eou_ret<
              dv<typename _tcI0::PTR::ptr, typename _tcI0::IPTR::iptr>>(a0);
        } else {
          const auto &[a01, a11] = std::get<typename List<
              dv<typename _tcI0::PTR::ptr, typename _tcI0::IPTR::iptr>>::Cons>(
              l.v());
          return eou_ret<
              dv<typename _tcI0::PTR::ptr, typename _tcI0::IPTR::iptr>>(a01);
        }
      } else {
        return eou_ret<
            dv<typename _tcI0::PTR::ptr, typename _tcI0::IPTR::iptr>>(a0);
      }
    } else {
      const auto &[a00] = std::get<typename Nat::S>(n.v());
      return collect<_tcI0>(*a00, *a1);
    }
  }
}

struct InlineInnerFixWritesInstance {
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

#endif // INCLUDED_INLINE_INNER_FIX_WRITES_INSTANCE
