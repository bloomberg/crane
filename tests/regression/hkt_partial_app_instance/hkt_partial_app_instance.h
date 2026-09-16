#ifndef INCLUDED_HKT_PARTIAL_APP_INSTANCE
#define INCLUDED_HKT_PARTIAL_APP_INSTANCE

#include "small_vector.h"
#include <any>
#include <atomic>
#include <concepts>
#include <functional>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

struct Nat;

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

/// An instance at a partially applied type constructor.  The instance's member
/// alias is emitted at the constructor's full arity
/// (template <typename _A0, typename _A1> using F = std::pair<_A0,_A1>) rather
/// than at the arity the class demands, so F<T> does not resolve.

template <typename I>
concept Fn = requires {
  typename I::template F<std::any>;
  {
    I::template fm<std::any, std::any>(
        std::declval<std::function<std::any(std::any)>>(),
        std::declval<typename I::template F<std::any>>())
  } -> std::convertible_to<typename I::template F<std::any>>;
};

struct HktPartialAppInstance {
  template <Fn _tcI0, typename T2, typename T3, typename F0>
    requires std::is_invocable_r_v<T3, F0 &, T2 &>
  static typename _tcI0::template F<T3> fm(F0 &&x,
                                           typename _tcI0::template F<T2> x0) {
    return _tcI0::template fm<T2, T3>(x, std::move(x0));
  }

  template <typename T1> struct pf {
    template <typename _A0> using F = std::pair<T1, _A0>;

    template <typename _A0, typename _A1>
    static std::pair<T1, _A1> fm(std::function<_A1(_A0)> f,
                                 std::pair<T1, _A0> p) {
      return std::make_pair(p.first, f(p.second));
    }
  };

  static inline const std::pair<bool, Nat> ex = fm<pf<bool>, Nat, Nat>(
      [](Nat x) { return Nat::s(x); }, std::make_pair(true, Nat::s(Nat::o())));
};

#endif // INCLUDED_HKT_PARTIAL_APP_INSTANCE
