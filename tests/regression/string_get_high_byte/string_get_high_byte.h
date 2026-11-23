#pragma once

#include "crane_fn.h"
#include "obj.h"
#include <atomic>
#include <crane_string.h>
#include <cstdint>
#include <memory>
#include <string>
#include <string_view>
#include <type_traits>
#include <utility>
#include <variant>

struct Positive;
struct Z;

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

struct Pos {
  static Positive pred_double(const Positive &x);

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, T1 &, T1> &&
             std::is_invocable_r_v<T1, F0 &, T1 &, T1 &>
  static T1 iter_op(F0 &&op, const Positive &p, T1 a) {
    if (std::holds_alternative<typename Positive::XI>(p.v())) {
      const auto &[a0] = std::get<typename Positive::XI>(p.v());
      return op(a, iter_op<T1>(op, *a0, op(a, a)));
    } else if (std::holds_alternative<typename Positive::XO>(p.v())) {
      const auto &[a0] = std::get<typename Positive::XO>(p.v());
      return iter_op<T1>(op, *a0, op(a, a));
    } else {
      return a;
    }
  }

  static uint64_t to_nat(const Positive &x);
};

struct BinInt {
  static uint64_t to_nat(const Z &z);
};

struct IntDef {
  static Z double_(const Z &x);
  static Z succ_double(const Z &x);
};

struct Uint63Axioms {
  static constexpr uint64_t size = UINT64_C(63);
  static bool is_zero(int64_t i);
  static bool is_even(int64_t i);
  static Z to_Z_rec(uint64_t n, int64_t i);
  static Z to_Z(int64_t x0_);
};

struct StringGetHighByte {
  static inline const std::string accented = "\303\251";
  static inline const uint64_t first_code = BinInt::to_nat(
      Uint63Axioms::to_Z(crane::string_get(accented, INT64_C(0))));
  static inline const bool high_above_low =
      crane::string_get(std::string_view("a"), INT64_C(0)) <
      crane::string_get(accented, INT64_C(0));
  /// A char63 is any int: one above 255 keeps its value.
  static inline const int64_t wide = crane::any_cast<int64_t>(
      static_cast<int64_t>(
          (static_cast<uint64_t>(crane::string_get(accented, INT64_C(0))) +
           static_cast<uint64_t>(INT64_C(100))) &
          0x7FFFFFFFFFFFFFFFULL));
  static inline const uint64_t wide_code =
      BinInt::to_nat(Uint63Axioms::to_Z(wide));
};
