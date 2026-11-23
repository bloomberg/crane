#pragma once

#include "crane_fn.h"
#include "obj.h"
#include "small_vector.h"
#include <atomic>
#include <crane_string.h>
#include <cstdint>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <string_view>
#include <type_traits>
#include <utility>
#include <variant>

template <typename A> struct List;
struct Positive;
struct Z;

template <typename A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    A a;
    std::shared_ptr<List<A>> l;
  };

  using variant_t = std::variant<Nil, Cons>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  List() {}

  explicit List(Nil _v) : v_(_v) {}

  explicit List(Cons _v) : v_(std::move(_v)) {}

  template <typename CraneU>
  List(const List<CraneU> &_other)
      : v_([&]() -> variant_t {
          if (std::holds_alternative<typename List<CraneU>::Nil>(_other.v())) {
            return Nil{};
          } else {
            const auto &[a, l] =
                std::get<typename List<CraneU>::Cons>(_other.v());
            return Cons{
                [&]() -> A {
                  if constexpr (crane_convertible<A, const CraneU &>) {
                    return crane_convert<A>(a);
                  } else {
                    throw std::logic_error("unreachable: inactive constructor "
                                           "field at this instantiation");
                  }
                }(),
                (l ? std::make_shared<List<A>>(crane_convert<List<A>>(*l))
                   : nullptr)};
          }
        }()) {}

  static List<A> nil() { return List<A>(Nil{}); }

  static List<A> cons(A a, crane::shared_child_slot<List<A>> l) {
    return List<A>(Cons{std::move(a), l.take()});
  }

  // MANIPULATORS
  ~List() {
    // Release the children this node alone owns in a loop, not recursively, so
    // a deep value cannot overflow the stack.
    auto _next = [&](variant_t &_v) -> std::shared_ptr<List<A>> {
      if (auto *_alt = std::get_if<Cons>(&_v)) {
        if (_alt->l && _alt->l.use_count() == 1) {
          std::atomic_thread_fence(std::memory_order_acquire);
          return std::move(_alt->l);
        }
      }
      return nullptr;
    };
    std::shared_ptr<List<A>> _cur = _next(v_mut());
    while (_cur) {
      _cur = _next(_cur->v_mut());
    }
  }

  List(const List &) = default;
  List &operator=(const List &) = default;
  List(List &&) = default;
  List &operator=(List &&) = default;

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
  static Positive succ(const Positive &x);
  static Positive pred_double(const Positive &x);

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, T1 &, T1 &> &&
             std::is_invocable_r_v<T1, F0 &, T1 &&, T1 &&>
  static T1 iter_op(F0 &&op, const Positive &p, T1 a) {
    // Explicit stack replaces the non-tail recursion of iter_op: _call frames
    // are pending calls, _after frames resume a caller.
    struct _call {
      T1 a;
      const Positive *p;
    };

    struct _after_iter_op_in_XI {
      T1 a;
    };

    using _frame = std::variant<_call, _after_iter_op_in_XI>;
    T1 _result{};
    crane::small_vector<_frame> _stack;
    _stack.emplace_back(_call{std::move(a), &p});
    while (!_stack.empty()) {
      _frame &_popped = _stack.back();
      if (std::holds_alternative<_call>(_popped)) {
        auto _f = std::move(std::get<_call>(_popped));
        _stack.pop_back();
        auto a = std::move(_f.a);
        const Positive &p = *_f.p;
        if (std::holds_alternative<typename Positive::XI>(p.v())) {
          const auto &[a0] = std::get<typename Positive::XI>(p.v());
          _stack.emplace_back(_after_iter_op_in_XI{a});
          _stack.emplace_back(_call{op(a, a), crane_raw(a0)});
        } else if (std::holds_alternative<typename Positive::XO>(p.v())) {
          const auto &[a0] = std::get<typename Positive::XO>(p.v());
          _stack.emplace_back(_call{op(a, a), crane_raw(a0)});
        } else {
          _result = std::move(a);
        }
      } else {
        auto _f = std::move(std::get<_after_iter_op_in_XI>(_popped));
        _stack.pop_back();
        auto a = std::move(_f.a);
        _result = op(std::move(a), std::move(_result));
      }
    }
    return _result;
  }

  static uint64_t to_nat(const Positive &x);
  static Positive of_succ_nat(uint64_t n);
};

struct BinInt {
  static uint64_t to_nat(const Z &z);
  static Z of_nat(uint64_t n);
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
  static int64_t of_pos_rec(uint64_t n, const Positive &p);
  static int64_t of_pos(const Positive &x0_);
  static int64_t of_Z(const Z &z);
};

struct LoopifyStringViewDangling {
  static uint64_t i2n(int64_t i);
  static int64_t n2i(uint64_t n);
  static uint64_t drop_each(const List<bool> &l, std::string_view s);
  static inline const uint64_t result = drop_each(
      List<bool>::cons(true, List<bool>::cons(true, List<bool>::nil())),
      crane::string_capped(std::string("abcdefghijklmnopqrstuvwxyz") +
                           std::string("0123456789")));
};
