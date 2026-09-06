#ifndef INCLUDED_DEPENDENT_VECTOR_NTH
#define INCLUDED_DEPENDENT_VECTOR_NTH

#include "crane_fn.h"
#include "small_vector.h"
#include <any>
#include <atomic>
#include <memory>
#include <stdexcept>
#include <type_traits>
#include <utility>
#include <variant>

struct T;
template <typename A> struct T0;

struct T {
  // TYPES
  struct F1 {
    uint64_t n;
  };

  struct FS {
    uint64_t n;
    std::shared_ptr<T> a1;
  };

  using variant_t = std::variant<F1, FS>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  T() {}

  explicit T(F1 _v) : v_(std::move(_v)) {}

  explicit T(FS _v) : v_(std::move(_v)) {}

  static T f1(uint64_t n) { return T(F1{n}); }

  static T fs(uint64_t n, T a1) {
    return T(FS{n, std::make_shared<T>(std::move(a1))});
  }

  // MANIPULATORS
  ~T() {
    crane::small_vector<std::shared_ptr<T>> _stack = {};
    auto _drain = [&](variant_t &_v) {
      if (auto *_alt = std::get_if<FS>(&_v)) {
        if (_alt->a1) {
          _stack.push_back(std::move(_alt->a1));
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

  T(const T &) = default;
  T &operator=(const T &) = default;
  T(T &&) noexcept = default;
  T &operator=(T &&) noexcept = default;

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

template <typename A> struct T0 {
  // TYPES
  struct Nil {};

  struct Cons {
    A h;
    uint64_t n;
    std::shared_ptr<T0<A>> a2;
  };

  using variant_t = std::variant<Nil, Cons>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  T0() {}

  explicit T0(Nil _v) : v_(_v) {}

  explicit T0(Cons _v) : v_(std::move(_v)) {}

  template <typename _U> T0(const T0<_U> &_other) {
    if (std::holds_alternative<typename T0<_U>::Nil>(_other.v())) {
      this->v_ = Nil{};
    } else {
      const auto &[h, n, a2] = std::get<typename T0<_U>::Cons>(_other.v());
      this->v_ = Cons{[&]() -> A {
                        if constexpr (std::is_same_v<_U, std::any>) {
                          return crane_any_cast<A>(h);
                        } else {
                          return A(h);
                        }
                      }(),
                      n, (a2 ? std::make_shared<T0<A>>(*a2) : nullptr)};
    }
  }

  static T0<A> nil() { return T0<A>(Nil{}); }

  static T0<A> cons(A h, uint64_t n, T0<A> a2) {
    return T0<A>(Cons{std::move(h), n, std::make_shared<T0<A>>(std::move(a2))});
  }

  // MANIPULATORS
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

struct Vector {
  template <typename T1>
  static T1 nth(uint64_t _x, const T0<T1> &v0, const T &p);
  template <typename T1, typename T2, typename F0>
    requires std::is_invocable_r_v<T2, F0 &, T2 &, T1 &>
  static T2 fold_left(F0 &&f, T2 b, uint64_t _x, const T0<T1> &v0);
};

/// Vector.nth eliminates the vector under a motive Fin.t n -> A and then
/// applies the result to the index.  The generated match keeps the motive's
/// arrow as the lambda's declared return type, std::function<T1(T)>, while
/// each branch returns a T1 -- so the extra argument is consumed twice in
/// the type and once in the term.
struct DependentVectorNth {
  static inline const T0<uint64_t> v = T0<uint64_t>::cons(
      UINT64_C(1), UINT64_C(2),
      T0<uint64_t>::cons(
          UINT64_C(2), UINT64_C(1),
          T0<uint64_t>::cons(UINT64_C(3), UINT64_C(0), T0<uint64_t>::nil())));
  static inline const uint64_t run =
      (Vector::template nth<uint64_t>(UINT64_C(3), v,
                                      T::fs(UINT64_C(2), T::f1(UINT64_C(1)))) +
       Vector::template fold_left<uint64_t, uint64_t>(
           [](uint64_t _x0, uint64_t _x1) -> uint64_t { return (_x0 + _x1); },
           UINT64_C(0), UINT64_C(3), v));
};

template <typename T1> T1 Vector::nth(uint64_t, const T0<T1> &v0, const T &p) {
  return [=]() mutable {
    if (std::holds_alternative<typename T0<T1>::Nil>(v0.v())) {
      throw std::logic_error("absurd case");
    } else {
      const auto &[h, n, a2] = std::get<typename T0<T1>::Cons>(v0.v());
      if (std::holds_alternative<typename T::F1>(p.v())) {
        return h;
      } else {
        const auto &[n1, a10] = std::get<typename T::FS>(p.v());
        return Vector::template nth<T1>(((n1 + 1) ? (n1 + 1) - 1 : (n1 + 1)),
                                        *a2, *a10);
      }
    }
  }();
}

template <typename T1, typename T2, typename F0>
  requires std::is_invocable_r_v<T2, F0 &, T2 &, T1 &>
T2 Vector::fold_left(F0 &&f, T2 b, uint64_t, const T0<T1> &v0) {
  if (std::holds_alternative<typename T0<T1>::Nil>(v0.v())) {
    return b;
  } else {
    const auto &[h, n, a2] = std::get<typename T0<T1>::Cons>(v0.v());
    return Vector::template fold_left<T1, T2>(f, f(b, h), n, *a2);
  }
}

#endif // INCLUDED_DEPENDENT_VECTOR_NTH
