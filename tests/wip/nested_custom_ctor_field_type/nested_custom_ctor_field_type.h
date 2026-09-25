#ifndef INCLUDED_NESTED_CUSTOM_CTOR_FIELD_TYPE
#define INCLUDED_NESTED_CUSTOM_CTOR_FIELD_TYPE

#include "crane_fn.h"
#include "small_vector.h"
#include <any>
#include <atomic>
#include <concepts>
#include <crane_itree.h>
#include <memory>
#include <optional>
#include <stdexcept>
#include <utility>
#include <variant>

struct Nat;
template <typename A, typename B> struct Sum;
template <typename ptr> struct Dvalue;
enum class FailE;
struct natParams;
using ptr = std::any;
template <typename
I>concept Params = requires {
  typename I::ptr;
} && (requires {
  { I::nullp() } -> std::convertible_to<typename I::ptr>;
} || requires {
  { I::nullp } -> std::convertible_to<typename I::ptr>;
});

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

template <typename ptr> struct Dvalue {
  // TYPES
  struct DP {
    ptr a0;
  };

  struct DU {};

  using variant_t = std::variant<DP, DU>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  Dvalue() {}

  explicit Dvalue(DP _v) : v_(std::move(_v)) {}

  explicit Dvalue(DU _v) : v_(_v) {}

  template <typename _U> Dvalue(const Dvalue<_U> &_other) {
    if (std::holds_alternative<typename Dvalue<_U>::DP>(_other.v())) {
      const auto &[a0] = std::get<typename Dvalue<_U>::DP>(_other.v());
      this->v_ = DP{a0};
    } else {
      this->v_ = DU{};
    }
  }

  static Dvalue<ptr> dp(ptr a0) { return Dvalue<ptr>(DP{std::move(a0)}); }

  static Dvalue<ptr> du() { return Dvalue<ptr>(DU{}); }

  // MANIPULATORS
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

template <typename ptr> using exc = Dvalue<ptr>;
enum class FailE { FAIL };
template <typename r> using CFGtop = std::shared_ptr<ITree<r>>;

template <Params _tcI0, typename T1 = void>
std::optional<exc<typename _tcI0::ptr>> exc_of_event(FailE) {
  return std::optional<Dvalue<typename _tcI0::ptr>>();
}

template <Params _tcI0, typename T1>
CFGtop<Sum<exc<typename _tcI0::ptr>, T1>>
run_exc(const std::shared_ptr<ITree<T1>> &t) {
  return itree_iter(
      [](const std::shared_ptr<ITree<T1>> &u) {
        auto _cs = u->observe();
        if (std::holds_alternative<typename ITree<T1>::Ret>(_cs)) {
          const auto &_itf = *std::get_if<typename ITree<T1>::Ret>(&_cs);
          auto a = _itf.value;
          return itree_ret(
              Sum<std::shared_ptr<ITree<T1>>,
                  Sum<Dvalue<typename _tcI0::ptr>, T1>>::
                  inr(Sum<Dvalue<typename _tcI0::ptr>,
                          Sum<Dvalue<typename _tcI0::ptr>, T1>>::inr(a)));
        } else if (std::holds_alternative<typename ITree<T1>::Tau>(_cs)) {
          const auto &_itf = *std::get_if<typename ITree<T1>::Tau>(&_cs);
          auto u_ = _itf.next;
          return itree_ret(Sum<std::shared_ptr<ITree<T1>>,
                               Sum<Dvalue<typename _tcI0::ptr>, T1>>::inl(u_));
        } else {
          const auto &_itf = *std::get_if<typename ITree<T1>::Vis>(&_cs);
          auto e = crane_event_as<FailE>(_itf.effect);
          auto k = _itf.cont;
          auto _cs1 = exc_of_event<_tcI0, T1>(e);
          if (_cs1.has_value()) {
            const Dvalue<typename _tcI0::ptr> &x = *_cs1;
            return itree_ret(
                Sum<std::shared_ptr<ITree<T1>>,
                    Sum<Dvalue<typename _tcI0::ptr>, T1>>::
                    inr(Sum<Dvalue<typename _tcI0::ptr>,
                            Sum<Dvalue<typename _tcI0::ptr>, T1>>::inl(x)));
          } else {
            return itree_vis(e, [=](const auto &y) mutable {
              return itree_ret(Sum<std::shared_ptr<ITree<T1>>,
                                   Sum<Dvalue<typename _tcI0::ptr>,
                                       T1>>::inl(crane_call_erased(k, y)));
            });
          }
        }
      },
      t);
}

struct natParams {
  using ptr = Nat;

  static Nat nullp() { return Nat::o(); }
};

static_assert(Params<natParams>);

struct NestedCustomCtorFieldType {
  static std::shared_ptr<ITree<Sum<exc<typename natParams::ptr>, Nat>>> run();
};

#endif // INCLUDED_NESTED_CUSTOM_CTOR_FIELD_TYPE
