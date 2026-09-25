#ifndef INCLUDED_MREC_CTX_WRAPPED_IN_RET
#define INCLUDED_MREC_CTX_WRAPPED_IN_RET

#include "crane_fn.h"
#include "small_vector.h"
#include <any>
#include <atomic>
#include <crane_itree.h>
#include <memory>
#include <stdexcept>
#include <utility>
#include <variant>

struct Nat;
template <typename A, typename B> struct Sum;
struct CountE;

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

  template <typename _U0, typename _U1> Sum(const Sum<_U0, _U1> &_other) {
    if (std::holds_alternative<typename Sum<_U0, _U1>::Inl>(_other.v())) {
      const auto &[a0] = std::get<typename Sum<_U0, _U1>::Inl>(_other.v());
      this->v_ = Inl{[&]() -> A {
        if constexpr (crane_convertible<A, const _U0 &>) {
          return crane_convert<A>(a0);
        } else {
          throw std::logic_error(
              "unreachable: inactive constructor field at this instantiation");
        }
      }()};
    } else {
      const auto &[a0] = std::get<typename Sum<_U0, _U1>::Inr>(_other.v());
      this->v_ = Inr{[&]() -> B {
        if constexpr (crane_convertible<B, const _U1 &>) {
          return crane_convert<B>(a0);
        } else {
          throw std::logic_error(
              "unreachable: inactive constructor field at this instantiation");
        }
      }()};
    }
  }

  static Sum<A, B> inl(A a0) { return Sum<A, B>(Inl{std::move(a0)}); }

  static Sum<A, B> inr(B a0) { return Sum<A, B>(Inr{std::move(a0)}); }

  // MANIPULATORS
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

struct Recursion {
  template <typename T1 = void, typename T2 = void, typename T3, typename F0>
  static std::shared_ptr<ITree<T3>> interp_mrec(F0 &&ctx0,
                                                std::shared_ptr<ITree<T3>> x0_);
  template <typename T1 = void, typename T2 = void, typename T3, typename F0,
            typename _P0>
  static std::shared_ptr<ITree<T3>> mrec(F0 &&ctx0, _P0 d);
};

struct CountE {
  // DATA
  Nat a0;

  // ACCESSORS
  CountE clone() const { return {a0}; }

  // CREATORS
  static CountE count(Nat a0) { return {std::move(a0)}; }

  /// Takes a bool first, so it stays a function rather than becoming a
  /// member template of CountE -- that shape has a defect of its own
  /// (tests/wip/eta_handler_event_as_template).
  template <typename T1> std::shared_ptr<ITree<T1>> ctx(bool) const;
};

template <typename T1, typename T2, typename T3, typename F0>
std::shared_ptr<ITree<T3>>
Recursion::interp_mrec(F0 &&ctx0, std::shared_ptr<ITree<T3>> x0_) {
  return itree_iter(
      [=](const std::shared_ptr<ITree<T3>> &t) mutable {
        auto _cs = t->observe();
        if (std::holds_alternative<typename ITree<T3>::Ret>(_cs)) {
          const auto &_itf = *std::get_if<typename ITree<T3>::Ret>(&_cs);
          auto r = _itf.value;
          return itree_ret(Sum<std::shared_ptr<ITree<T3>>, T3>::inr(r));
        } else if (std::holds_alternative<typename ITree<T3>::Tau>(_cs)) {
          const auto &_itf = *std::get_if<typename ITree<T3>::Tau>(&_cs);
          auto t0 = _itf.next;
          return itree_ret(Sum<std::shared_ptr<ITree<T3>>, T3>::inl(t0));
        } else {
          const auto &_itf = *std::get_if<typename ITree<T3>::Vis>(&_cs);
          auto e0 = crane_event_as<Sum1<std::any, T2, std::any>>(_itf.effect);
          auto k = _itf.cont;
          if (std::holds_alternative<
                  typename Sum1<std::any, T2, std::any>::Inl1>(e0.v())) {
            const auto &[a0] =
                std::get<typename Sum1<std::any, T2, std::any>::Inl1>(e0.v());
            return itree_ret(Sum<std::shared_ptr<ITree<T3>>, T3>::inl(
                itree_bind(ctx0(a0), k)));
          } else {
            const auto &[a0] =
                std::get<typename Sum1<std::any, T2, std::any>::Inr1>(e0.v());
            return itree_vis(a0, [=](const auto &x) mutable {
              return itree_ret(Sum<std::shared_ptr<ITree<T3>>, T3>::inl(
                  crane_call_erased(k, x)));
            });
          }
        }
      },
      std::move(x0_));
}

template <typename T1, typename T2, typename T3, typename F0, typename _P0>
std::shared_ptr<ITree<T3>> Recursion::mrec(F0 &&ctx0, _P0 d) {
  return Recursion::template interp_mrec<std::any, T2, T3>(ctx0,
                                                           ctx0(std::move(d)));
}

/// Takes a bool first, so it stays a function rather than becoming a
/// member template of CountE -- that shape has a defect of its own
/// (tests/wip/eta_handler_event_as_template).
template <typename T1> std::shared_ptr<ITree<T1>> CountE::ctx(bool) const {
  const auto &[a0] = *this;
  if (std::holds_alternative<typename Nat::O>(a0.v())) {
    return itree_ret(Nat::o());
  } else {
    const auto &[a00] = std::get<typename Nat::S>(a0.v());
    return itree_trigger(sum1_inl(CountE::count(*a00)));
  }
}

#endif // INCLUDED_MREC_CTX_WRAPPED_IN_RET
