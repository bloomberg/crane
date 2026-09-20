#ifndef INCLUDED_TUPLE
#define INCLUDED_TUPLE

#include "crane_fn.h"
#include "small_vector.h"
#include <any>
#include <atomic>
#include <memory>
#include <stdexcept>
#include <type_traits>
#include <utility>
#include <variant>

struct Nat;
template <typename A, typename B> struct Prod;

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

template <typename A, typename B> struct Prod {
  // DATA
  A a0;
  B a1;

  // ACCESSORS
  Prod<A, B> clone() const { return {a0, a1}; }

  template <typename _U0, typename _U1> operator Prod<_U0, _U1>() const {
    return {[&]() -> _U0 {
              if constexpr (std::is_same_v<A, std::any>) {
                return crane_any_cast<_U0>(a0);
              } else {
                if constexpr (std::is_constructible_v<_U0, const A &>) {
                  return _U0(a0);
                } else {
                  throw std::logic_error("unreachable: inactive constructor "
                                         "field at this instantiation");
                }
              }
            }(),
            [&]() -> _U1 {
              if constexpr (std::is_same_v<B, std::any>) {
                return crane_any_cast<_U1>(a1);
              } else {
                if constexpr (std::is_constructible_v<_U1, const B &>) {
                  return _U1(a1);
                } else {
                  throw std::logic_error("unreachable: inactive constructor "
                                         "field at this instantiation");
                }
              }
            }()};
  }

  // CREATORS
  static Prod<A, B> pair(A a0, B a1) { return {std::move(a0), std::move(a1)}; }
};

struct Tuple {
  template <typename a, typename b> using pair = Prod<a, b>;

  template <typename T1, typename T2>
  static Prod<T1, T2> make_pair(T1 a, T2 b) {
    return Prod<T1, T2>::pair(std::move(a), std::move(b));
  }

  template <typename T1, typename T2> static T1 fst(Prod<T1, T2> p) {
    auto &[a0, a1] = p;
    return a0;
  }

  template <typename T1, typename T2> static T2 snd(Prod<T1, T2> p) {
    auto &[a0, a1] = p;
    return a1;
  }

  template <typename T1, typename T2> static Prod<T2, T1> swap(Prod<T1, T2> p) {
    auto &[a0, a1] = p;
    return Prod<T2, T1>::pair(std::move(a1), std::move(a0));
  }

  static inline const Prod<Nat, Nat> test_pair =
      make_pair<Nat, Nat>(Nat::s(Nat::o()), Nat::s(Nat::s(Nat::o())));
  static inline const Nat test_fst = fst<Nat, Nat>(test_pair);
  static inline const Prod<Nat, Nat> test_swap = swap<Nat, Nat>(test_pair);
};

#endif // INCLUDED_TUPLE
