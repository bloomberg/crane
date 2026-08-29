#ifndef INCLUDED_GUARD_COMPARE_LABEL_COLLISION
#define INCLUDED_GUARD_COMPARE_LABEL_COLLISION

#include "small_vector.h"
#include <atomic>
#include <memory>
#include <utility>
#include <variant>

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
enum class Comparison { EQ, LT, GT };

template <typename X> struct Compare {
  // TYPES
  struct LT {};

  struct EQ {};

  struct GT {};

  using variant_t = std::variant<LT, EQ, GT>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  Compare() {}

  explicit Compare(LT _v) : v_(_v) {}

  explicit Compare(EQ _v) : v_(_v) {}

  explicit Compare(GT _v) : v_(_v) {}

  static Compare<X> lt() { return Compare<X>(LT{}); }

  static Compare<X> eq() { return Compare<X>(EQ{}); }

  static Compare<X> gt() { return Compare<X>(GT{}); }

  // MANIPULATORS
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

struct OK {
  static Comparison compare(const Nat &x, const Nat &y);
};

struct Ordered {
  enum class T { A, B };

  template <typename T1> static T1 t_rect(T1 f, T1 f0, T t0) {
    switch (t0) {
    case T::A: {
      return f;
    }
    case T::B: {
      return f0;
    }
    default:
      std::unreachable();
    }
  }

  template <typename T1> static T1 t_rec(T1 f, T1 f0, T t0) {
    switch (t0) {
    case T::A: {
      return f;
    }
    case T::B: {
      return f0;
    }
    default:
      std::unreachable();
    }
  }

  static Compare<T> compare(T x, T y);
};

#endif // INCLUDED_GUARD_COMPARE_LABEL_COLLISION
