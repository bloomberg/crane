#pragma once

#include "crane_fn.h"
#include "fn.h"
#include "obj.h"
#include <atomic>
#include <concepts>
#include <crane_itree.h>
#include <memory>
#include <stdexcept>
#include <utility>
#include <variant>

struct Nat;
template <typename A, typename B> struct Sum;
template <typename ptr> struct CountE;
struct natParams;
using ptr = crane::obj;
template <typename I>
concept Params = requires {
  typename I::ptr;
} && (requires {
  {
    I::nullp()
  }
  -> std::convertible_to<typename I::ptr>;
} || requires {
  {
    I::nullp
  }
  -> std::convertible_to<typename I::ptr>;
});

struct MrecCtxWrappedInRet {
  static std::shared_ptr<ITree<Nat>> run();
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
};

template <typename A, typename B> struct Sum {
  // TYPES
  struct Inl {
    A a0;
  };

  struct Inr {
    B a0;
  };

  using variant_t = std::variant<Inl, Inr>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  Sum() {}

  explicit Sum(Inl _v) : v_(std::move(_v)) {}

  explicit Sum(Inr _v) : v_(std::move(_v)) {}

  template <typename CraneU0, typename CraneU1>
  Sum(const Sum<CraneU0, CraneU1> &_other)
      : v_([&]() -> variant_t {
          if (std::holds_alternative<typename Sum<CraneU0, CraneU1>::Inl>(
                  _other.v())) {
            const auto &[a0] =
                std::get<typename Sum<CraneU0, CraneU1>::Inl>(_other.v());
            return Inl{[&]() -> A {
              if constexpr (crane_convertible<A, const CraneU0 &>) {
                return crane_convert<A>(a0);
              } else {
                throw std::logic_error("unreachable: inactive constructor "
                                       "field at this instantiation");
              }
            }()};
          } else {
            const auto &[a0] =
                std::get<typename Sum<CraneU0, CraneU1>::Inr>(_other.v());
            return Inr{[&]() -> B {
              if constexpr (crane_convertible<B, const CraneU1 &>) {
                return crane_convert<B>(a0);
              } else {
                throw std::logic_error("unreachable: inactive constructor "
                                       "field at this instantiation");
              }
            }()};
          }
        }()) {}

  static Sum<A, B> inl(A a0) { return Sum<A, B>(Inl{std::move(a0)}); }

  static Sum<A, B> inr(B a0) { return Sum<A, B>(Inr{std::move(a0)}); }

  // MANIPULATORS
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

struct Recursion {
  template <typename T1, typename T3>
  static std::shared_ptr<ITree<T3>>
  interp_mrec(const std::type_identity_t<
      crane::fn<std::shared_ptr<ITree<crane::obj>>(T1)>> &ctx0,
              const std::shared_ptr<ITree<T3>> &x0_);
  template <typename T1, typename T3, typename F0>
  static std::shared_ptr<ITree<T3>> mrec(F0 &&ctx0, crane::rebind_t<T1, T3> d);
};

/// Carries a promoted type, so it is a class template, as Vellvm's
/// CallE is: named as a type argument it needs its promoted arguments.
template <typename ptr> struct CountE {
  // DATA
  Nat a0;
  ptr a1;

  // ACCESSORS
  CountE<ptr> clone() const { return {a0, a1}; }

  template <typename CraneU> operator CountE<CraneU>() const {
    return {a0, a1};
  }

  // CREATORS
  static CountE<ptr> count(Nat a0, ptr a1) {
    return {std::move(a0), std::move(a1)};
  }

  /// Takes a bool first; it is still made a member template of
  /// CountE, its receiver the event after the bool.
  template <Params _tcI0, typename T1>
  std::shared_ptr<ITree<T1>> ctx(bool) const;
};

template <Params _tcI0> std::shared_ptr<ITree<Nat>> run_mrec() {
  return Recursion::template mrec<CountE<typename _tcI0::ptr>, Nat>(
      []() {
        return [](CountE<typename _tcI0::ptr> _x0) -> std::shared_ptr<
            ITree<crane::obj>> {
          return _x0.template ctx<_tcI0, crane::obj>(false);
        };
      }(),
      CountE<typename _tcI0::ptr>::count(Nat::s(Nat::s(Nat::s(Nat::o()))),
                                         _tcI0::nullp()));
}

struct natParams {
  using ptr = Nat;

  static Nat nullp() { return Nat::o(); }
};

static_assert(Params<natParams>);

template <typename T1, typename T3>
std::shared_ptr<ITree<T3>>
Recursion::interp_mrec(const std::type_identity_t<
    crane::fn<std::shared_ptr<ITree<crane::obj>>(T1)>> &ctx0,
                       const std::shared_ptr<ITree<T3>> &x0_) {
  return itree_iter(
      [=, ctx0 = ctx0](const std::shared_ptr<ITree<T3>> &t) -> std::shared_ptr<
          ITree<Sum<std::shared_ptr<ITree<T3>>, T3>>> {
        auto _cs = t->observe();
        if (std::holds_alternative<typename ITree<T3>::Ret>(_cs)) {
          T3 r = std::get_if<typename ITree<T3>::Ret>(&_cs)->value;
          return itree_ret(
              Sum<std::shared_ptr<ITree<T3>>, T3>::inr(std::move(r)));
        } else if (std::holds_alternative<typename ITree<T3>::Tau>(_cs)) {
          auto t0 = std::get_if<typename ITree<T3>::Tau>(&_cs)->next;
          return itree_ret(
              Sum<std::shared_ptr<ITree<T3>>, T3>::inl(std::move(t0)));
        } else {
          auto e0 = crane_event_as<Sum1<T1, T2, crane::obj>>(
              std::get_if<typename ITree<T3>::Vis>(&_cs)->effect);
          auto k = std::get_if<typename ITree<T3>::Vis>(&_cs)->cont;
          if (std::holds_alternative<typename std::decay_t<decltype(e0)>::Inl1>(
                  e0.v())) {
            const auto &d =
                std::get<typename std::decay_t<decltype(e0)>::Inl1>(e0.v()).a0;
            return itree_ret(Sum<std::shared_ptr<ITree<T3>>, T3>::inl(
                itree_bind(ctx0(d), std::move(k))));
          } else {
            const auto &e =
                std::get<typename std::decay_t<decltype(e0)>::Inr1>(e0.v()).a0;
            return itree_vis(e, [=, k = std::move(k)](const auto &x) {
              return itree_ret(Sum<std::shared_ptr<ITree<T3>>, T3>::inl(
                  crane_call_erased(k, x)));
            });
          }
        }
      },
      x0_);
}

template <typename T1, typename T3, typename F0>
std::shared_ptr<ITree<T3>> Recursion::mrec(F0 &&ctx0,
                                           crane::rebind_t<T1, T3> d) {
  return Recursion::template interp_mrec<T1, T3>(ctx0, ctx0(std::move(d)));
} /// Takes a bool first; it is still made a member template of

/// CountE, its receiver the event after the bool.
template <typename ptr>
template <Params _tcI0, typename T1> std::shared_ptr<ITree<T1>>
CountE<ptr>::ctx(bool) const {
  const auto &[a0, a1] = *this;
  if (std::holds_alternative<typename Nat::O>(a0.v())) {
    return itree_ret(crane_convert<T1>(Nat::o()));
  } else {
    const auto &[a00] = std::get<typename Nat::S>(a0.v());
    return itree_trigger(sum1_inl(CountE<ptr>::count(*a00, a1)));
  }
}
