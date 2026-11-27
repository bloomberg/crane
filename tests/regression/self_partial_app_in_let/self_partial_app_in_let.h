#pragma once

#include "crane_fn.h"
#include "fn.h"
#include <atomic>
#include <memory>
#include <utility>
#include <variant>

struct Nat;
struct Positive;

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

struct Positive {
  // TYPES
  struct XI {
    std::shared_ptr<Positive> a0;
  };

  struct XO {
    std::shared_ptr<Positive> a0;
  };

  struct XH {};

  using variant_t = std::variant<XI, XO, XH>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  Positive() {}

  explicit Positive(XI _v) : v_(std::move(_v)) {}

  explicit Positive(XO _v) : v_(std::move(_v)) {}

  explicit Positive(XH _v) : v_(_v) {}

  static Positive xi(crane::shared_child_slot<Positive> a0) {
    return Positive(XI{a0.take()});
  }

  static Positive xo(crane::shared_child_slot<Positive> a0) {
    return Positive(XO{a0.take()});
  }

  static Positive xh() { return Positive(XH{}); }

  // MANIPULATORS
  ~Positive() {
    // Release the children this node alone owns in a loop, not recursively, so
    // a deep value cannot overflow the stack.
    auto _next = [&](variant_t &_v) -> std::shared_ptr<Positive> {
      if (auto *_alt = std::get_if<XI>(&_v)) {
        if (_alt->a0 && _alt->a0.use_count() == 1) {
          std::atomic_thread_fence(std::memory_order_acquire);
          return std::move(_alt->a0);
        }
      }
      if (auto *_alt = std::get_if<XO>(&_v)) {
        if (_alt->a0 && _alt->a0.use_count() == 1) {
          std::atomic_thread_fence(std::memory_order_acquire);
          return std::move(_alt->a0);
        }
      }
      return nullptr;
    };
    std::shared_ptr<Positive> _cur = _next(v_mut());
    while (_cur) {
      _cur = _next(_cur->v_mut());
    }
  }

  Positive(const Positive &) = default;
  Positive &operator=(const Positive &) = default;
  Positive(Positive &&) = default;
  Positive &operator=(Positive &&) = default;

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

struct Pos {
  static Positive succ(const Positive &x);

  template <typename T1>
  static T1 peano_rect(T1 a,
                       std::type_identity_t<crane::fn<T1(Positive, T1)>> f,
                       const Positive &p) {
    auto _lc1_pa0 = f(Positive::xh(), a);
    crane::fn<T1(Positive)> f2 = [=](Positive _x0) -> T1 {
      return peano_rect<T1>(
          _lc1_pa0,
          [=, f = f](const Positive &p0,
                     const T1 &x) {
            return f(succ(Positive::xo(p0)), f(Positive::xo(p0), x));
          },
          _x0);
    };
    if (std::holds_alternative<typename Positive::XI>(p.v())) {
      const auto &[a0] = std::get<typename Positive::XI>(p.v());
      return f(Positive::xo(crane::shared_child(a0)), f2(*a0));
    } else if (std::holds_alternative<typename Positive::XO>(p.v())) {
      const auto &[a0] = std::get<typename Positive::XO>(p.v());
      return f2(*a0);
    } else {
      return a;
    }
  }
};

struct SelfPartialAppInLet {
  static inline const Nat run = Pos::template peano_rect<Nat>(
      Nat::o(),
      [](Positive, const Nat &n) { return Nat::s(n); },
      Positive::xi(Positive::xo(Positive::xh())));
};
