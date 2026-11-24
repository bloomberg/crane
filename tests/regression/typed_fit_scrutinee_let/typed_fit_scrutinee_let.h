#pragma once

#include "crane_fn.h"
#include <atomic>
#include <cstdint>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

struct Positive;
struct Z;

struct Nat {};

struct Pos {
  static Positive succ(const Positive &x);
  static Positive of_succ_nat(uint64_t n);
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

struct Z {
  // TYPES
  struct Z0 {};

  struct Zpos {
    Positive a0;
  };

  struct Zneg {
    Positive a0;
  };

  using variant_t = std::variant<Z0, Zpos, Zneg>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  Z() {}

  explicit Z(Z0 _v) : v_(_v) {}

  explicit Z(Zpos _v) : v_(std::move(_v)) {}

  explicit Z(Zneg _v) : v_(std::move(_v)) {}

  static Z z0() { return Z(Z0{}); }

  static Z zpos(Positive a0) { return Z(Zpos{std::move(a0)}); }

  static Z zneg(Positive a0) { return Z(Zneg{std::move(a0)}); }

  // MANIPULATORS
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

struct BinInt {
  static Z of_nat(uint64_t n);
};

struct TypedFitScrutineeLet {
  struct t3 {
    // TYPES
    struct A {};

    struct B {
      uint64_t n;
    };

    using variant_t = std::variant<A, B>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    t3() {}

    explicit t3(A _v) : v_(_v) {}

    explicit t3(B _v) : v_(std::move(_v)) {}

    static t3 a() { return t3(A{}); }

    static t3 b(uint64_t n) { return t3(B{n}); }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename F1>
    requires std::is_invocable_r_v<T1, F1 &, const uint64_t &>
  static T1 t3_rect(T1 f, F1 &&f0, const t3 &t) {
    if (std::holds_alternative<typename t3::A>(t.v())) {
      return f;
    } else {
      const auto &[n0] = std::get<typename t3::B>(t.v());
      return f0(n0);
    }
  }

  template <typename T1, typename F1>
  static T1 t3_rec(T1 f, F1 &&f0, const t3 &t) {
    return t3_rect<T1>(std::move(f), f0, t);
  }

  static uint64_t on_t3(bool b, uint64_t n);
  static uint64_t on_z(bool b, uint64_t n);
};
