#ifndef INCLUDED_STATET_DICT_ARG_DROPPED
#define INCLUDED_STATET_DICT_ARG_DROPPED

#include "crane_fn.h"
#include "small_vector.h"
#include <any>
#include <atomic>
#include <concepts>
#include <crane_itree.h>
#include <functional>
#include <memory>
#include <utility>
#include <variant>

struct Nat;
template <typename S, typename m, typename t> struct stateT;
struct FailE;

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

template <typename I>
concept Monad = requires {
  typename I::template m<std::any>;
  {
    I::template ret<std::any>(std::declval<std::any>())
  } -> std::convertible_to<typename I::template m<std::any>>;
  {
    I::template bind<std::any, std::any>(
        std::declval<typename I::template m<std::any>>(),
        std::declval<
            std::function<typename I::template m<std::any>(std::any)>>())
  } -> std::convertible_to<typename I::template m<std::any>>;
};

template <typename S, typename m, typename t> struct stateT {
  std::function<m(S)> runStateT;
};

template <Monad _tcI0, typename T1> struct Monad_stateT {
  template <typename _A0> using m = typename _tcI0::template m<_A0>;

  template <typename _A0>
  static stateT<T1, typename _tcI0::template m<std::any>, _A0> ret(_A0 x) {
    return stateT<std::any, std::any, std::any>{[=](const auto &s) mutable {
      return itree_ret(std::make_pair(std::any(x), std::any(s)));
    }};
  }

  template <typename _A0, typename _A1>
  static stateT<T1, typename _tcI0::template m<std::any>, _A1>
  bind(stateT<T1, typename _tcI0::template m<std::any>, _A0> c1,
       std::function<stateT<T1, typename _tcI0::template m<std::any>, _A1>(_A0)>
           c2) {
    return stateT<std::any, std::any, std::any>{[=](const auto &s) mutable {
      return itree_bind(c1.runStateT(s), [=](const auto &vs) mutable {
        const auto &[v, s0] = std::any_cast<std::pair<std::any, std::any>>(vs);
        return crane_container_cast<
            typename _tcI0::template m<std::pair<_A1, T1>>>(
            crane_call_erased(c2, v).runStateT(s0));
      });
    }};
  }
};

struct FailE {
  // DATA
  std::monostate a0;

  // ACCESSORS
  FailE clone() const { return {a0}; }

  // CREATORS
  static FailE Throw_(std::monostate a0) { return {a0}; }
};

using env = Nat;

template <typename T1 = void>
stateT<env, std::shared_ptr<ITree<std::any>>, Nat> step(Nat n) {
  return stateT<Nat, std::shared_ptr<ITree<std::any>>, Nat>{
      [=](Nat s) mutable { return itree_ret(std::make_pair(n, s)); }};
}

template <typename T1 = void>
stateT<env, std::shared_ptr<ITree<std::any>>, Nat> twice(const Nat &n) {
  return Monad_stateT<Monad_itree<std::any>, env>::template bind<Nat, Nat>(
      step<std::any>(n), [](const Nat &a) {
        return Monad_stateT<Monad_itree<std::any>, env>::template bind<
            Nat, Nat>(step<std::any>(a), [](const auto &b) {
          return Monad_stateT<Monad_itree<std::any>, env>::template ret<Nat>(b);
        });
      });
}

struct StateTDictArgDropped {
  static std::shared_ptr<ITree<std::pair<Nat, env>>> use(const Nat &n);
};

#endif // INCLUDED_STATET_DICT_ARG_DROPPED
