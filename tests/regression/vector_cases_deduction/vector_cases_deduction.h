#ifndef INCLUDED_VECTOR_CASES_DEDUCTION
#define INCLUDED_VECTOR_CASES_DEDUCTION

#include "crane_fn.h"
#include "obj.h"
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

  template <typename CraneU>
  T(const T<CraneU> &_other)
      : v_([&]() -> variant_t {
          if (std::holds_alternative<typename T<CraneU>::Nil>(_other.v())) {
            return Nil{};
          } else {
            const auto &[h, n, a2] =
                std::get<typename T<CraneU>::Cons>(_other.v());
            return Cons{[&]() -> A {
                          if constexpr (crane_convertible<A, const CraneU &>) {
                            return crane_convert<A>(h);
                          } else {
                            throw std::logic_error(
                                "unreachable: inactive constructor field at "
                                "this instantiation");
                          }
                        }(),
                        n,
                        (a2 ? std::make_shared<T<A>>(crane_convert<T<A>>(*a2))
                            : nullptr)};
          }
        }()) {}

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
    return crane_any_cast<T2>(
        ([]() -> crane::obj { throw std::logic_error("unreachable"); })());
  } else {
    const auto &[h1, n, a2] = std::get<typename T<T1>::Cons>(v.v());
    return h(h1, n, *a2);
  }
}

template <typename T1> T1 Vector::hd(const Nat &n, T<T1> x0_) {
  return Vector::template caseS<T1, T1>([](T1 h, Nat, T<T1>) { return h; }, n,
                                        std::move(x0_));
}

#endif // INCLUDED_VECTOR_CASES_DEDUCTION
