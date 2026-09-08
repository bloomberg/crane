#ifndef INCLUDED_VECTOR_CASES_DEDUCTION
#define INCLUDED_VECTOR_CASES_DEDUCTION

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
template <typename A> struct T;

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

template <typename A> struct T {
  // TYPES
  struct Nil {};

  struct Cons {
    A h;
    Nat n;
    std::shared_ptr<T<A>> a2;
  };

  using variant_t = std::variant<Nil, Cons>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  T() {}

  explicit T(Nil _v) : v_(_v) {}

  explicit T(Cons _v) : v_(std::move(_v)) {}

  template <typename _U> T(const T<_U> &_other) {
    if (std::holds_alternative<typename T<_U>::Nil>(_other.v())) {
      this->v_ = Nil{};
    } else {
      const auto &[h, n, a2] = std::get<typename T<_U>::Cons>(_other.v());
      this->v_ = Cons{[&]() -> A {
                        if constexpr (std::is_same_v<_U, std::any>) {
                          return crane_any_cast<A>(h);
                        } else {
                          return A(h);
                        }
                      }(),
                      n, (a2 ? std::make_shared<T<A>>(*a2) : nullptr)};
    }
  }

  static T<A> nil() { return T<A>(Nil{}); }

  static T<A> cons(A h, Nat n, T<A> a2) {
    return T<A>(Cons{std::move(h), std::move(n),
                     std::make_shared<T<A>>(std::move(a2))});
  }

  // MANIPULATORS
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

struct Vector {
  template <typename T1, typename T2, typename F0>
    requires std::is_invocable_r_v<T2, F0 &, T1 &, Nat &, T<T1> &>
  static T2 caseS(F0 &&h, const Nat &_x, const T<T1> &v);
  template <typename T1> static T1 hd(const Nat &n, T<T1> x0_);
};

struct VectorCasesDeduction {
  static inline const T<Nat> v3 =
      T<Nat>::cons(Nat::s(Nat::o()), Nat::s(Nat::s(Nat::o())),
                   T<Nat>::cons(Nat::s(Nat::s(Nat::o())), Nat::s(Nat::o()),
                                T<Nat>::cons(Nat::s(Nat::s(Nat::s(Nat::o()))),
                                             Nat::o(), T<Nat>::nil())));
  static Nat hd3(const T<Nat> &v);
  static inline const Nat test = hd3(v3);
};

template <typename T1, typename T2, typename F0>
  requires std::is_invocable_r_v<T2, F0 &, T1 &, Nat &, T<T1> &>
T2 Vector::caseS(F0 &&h, const Nat &, const T<T1> &v) {
  if (std::holds_alternative<typename T<T1>::Nil>(v.v())) {
    return std::any_cast<T2>(
        ([]() -> std::any { throw std::logic_error("unreachable"); })());
  } else {
    const auto &[h1, n, a2] = std::get<typename T<T1>::Cons>(v.v());
    return h(h1, n, *a2);
  }
}

template <typename T1> T1 Vector::hd(const Nat &n, T<T1> x0_) {
  return Vector::template caseS<T1, T1>(
      [](T1 h, const Nat &, const T<T1> &) { return h; }, n, std::move(x0_));
}

#endif // INCLUDED_VECTOR_CASES_DEDUCTION
