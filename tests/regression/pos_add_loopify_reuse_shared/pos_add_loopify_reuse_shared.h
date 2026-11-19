#pragma once

#include "crane_fn.h"
#include "crane_variant.h"
#include "shared_block.h"
#include "shared_variant.h"
#include "small_vector.h"
#include <atomic>
#include <cstdint>
#include <optional>
#include <type_traits>
#include <utility>

struct Positive;
struct N;

struct Positive {
  // TYPES
  struct XI {
    crane::shared_box<Positive> a0;
  };

  struct XO {
    crane::shared_box<Positive> a0;
  };

  struct XH {};

  using variant_t = crane::shared_variant<XI, XO, XH>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  Positive() {}

  explicit Positive(XI _v) : v_(std::move(_v)) {}

  explicit Positive(XO _v) : v_(std::move(_v)) {}

  explicit Positive(XH _v) : v_(_v) {}

  static Positive xi(Positive a0) {
    return Positive(XI{crane::shared_box<Positive>::make(std::move(a0))});
  }

  static Positive xi_crane_reuse(Positive _tok, Positive a0) {
    auto _alt = XI{crane::shared_box<Positive>::make(std::move(a0))};
    if (_tok.v_.try_reuse(std::move(_alt))) {
      return _tok;
    }
    return Positive(XI{std::move(_alt)});
  }

  static Positive xo(Positive a0) {
    return Positive(XO{crane::shared_box<Positive>::make(std::move(a0))});
  }

  static Positive xo_crane_reuse(Positive _tok, Positive a0) {
    auto _alt = XO{crane::shared_box<Positive>::make(std::move(a0))};
    if (_tok.v_.try_reuse(std::move(_alt))) {
      return _tok;
    }
    return Positive(XO{std::move(_alt)});
  }

  static Positive xh() { return Positive(XH{}); }

  // MANIPULATORS
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

struct N {
  // TYPES
  struct N0 {};

  struct Npos {
    Positive a0;
  };

  using variant_t = crane::shared_variant<N0, Npos>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  N() {}

  explicit N(N0 _v) : v_(_v) {}

  explicit N(Npos _v) : v_(std::move(_v)) {}

  static N n0() { return N(N0{}); }

  static N npos(Positive a0) { return N(Npos{std::move(a0)}); }

  static N npos_crane_reuse(N _tok, Positive a0) {
    auto _alt = Npos{std::move(a0)};
    if (_tok.v_.try_reuse(std::move(_alt))) {
      return _tok;
    }
    return N(Npos{std::move(_alt)});
  }

  // MANIPULATORS
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

struct Coq_Pos {
  static Positive succ(const Positive &x);
  static Positive add(const Positive &x, const Positive &y);
  static Positive add_carry(const Positive &x, const Positive &y);

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, T1 &, T1 &> &&
             std::is_invocable_r_v<T1, F0 &, T1 &&, T1 &&>
  static T1 iter_op(F0 &&op, const Positive &p, T1 a0) {
    // Explicit stack replaces the non-tail recursion of iter_op: _call frames
    // are pending calls, _after frames resume a caller.
    struct _call {
      T1 a0;
      const Positive *p;
    };

    struct _after_iter_op_in_XI {
      T1 a0;
    };

    using _frame = std::variant<_call, _after_iter_op_in_XI>;
    T1 _result{};
    crane::small_vector<_frame> _stack;
    _stack.emplace_back(_call{std::move(a0), &p});
    while (!_stack.empty()) {
      _frame &_popped = _stack.back();
      if (crane::holds_alternative<_call>(_popped)) {
        auto _f = std::move(crane::get<_call>(_popped));
        _stack.pop_back();
        auto a0 = std::move(_f.a0);
        const Positive &p = *_f.p;
        if (crane::holds_alternative<typename Positive::XI>(p.v())) {
          const auto &[a1] = crane::get<typename Positive::XI>(p.v());
          _stack.emplace_back(_after_iter_op_in_XI{a0});
          _stack.emplace_back(_call{op(a0, a0), crane_raw(a1)});
        } else if (crane::holds_alternative<typename Positive::XO>(p.v())) {
          const auto &[a1] = crane::get<typename Positive::XO>(p.v());
          _stack.emplace_back(_call{op(a0, a0), crane_raw(a1)});
        } else {
          _result = std::move(a0);
        }
      } else {
        auto _f = std::move(crane::get<_after_iter_op_in_XI>(_popped));
        _stack.pop_back();
        auto a0 = std::move(_f.a0);
        _result = op(std::move(a0), std::move(_result));
      }
    }
    return _result;
  }

  static uint64_t to_nat(const Positive &x);
};

struct Pos {
  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, T1 &, T1 &> &&
             std::is_invocable_r_v<T1, F0 &, T1 &&, T1 &&>
  static T1 iter_op(F0 &&op, const Positive &p, T1 a0) {
    // Explicit stack replaces the non-tail recursion of iter_op: _call frames
    // are pending calls, _after frames resume a caller.
    struct _call {
      T1 a0;
      const Positive *p;
    };

    struct _after_iter_op_in_XI {
      T1 a0;
    };

    using _frame = std::variant<_call, _after_iter_op_in_XI>;
    T1 _result{};
    crane::small_vector<_frame> _stack;
    _stack.emplace_back(_call{std::move(a0), &p});
    while (!_stack.empty()) {
      _frame &_popped = _stack.back();
      if (crane::holds_alternative<_call>(_popped)) {
        auto _f = std::move(crane::get<_call>(_popped));
        _stack.pop_back();
        auto a0 = std::move(_f.a0);
        const Positive &p = *_f.p;
        if (crane::holds_alternative<typename Positive::XI>(p.v())) {
          const auto &[a1] = crane::get<typename Positive::XI>(p.v());
          _stack.emplace_back(_after_iter_op_in_XI{a0});
          _stack.emplace_back(_call{op(a0, a0), crane_raw(a1)});
        } else if (crane::holds_alternative<typename Positive::XO>(p.v())) {
          const auto &[a1] = crane::get<typename Positive::XO>(p.v());
          _stack.emplace_back(_call{op(a0, a0), crane_raw(a1)});
        } else {
          _result = std::move(a0);
        }
      } else {
        auto _f = std::move(crane::get<_after_iter_op_in_XI>(_popped));
        _stack.pop_back();
        auto a0 = std::move(_f.a0);
        _result = op(std::move(a0), std::move(_result));
      }
    }
    return _result;
  }

  static uint64_t to_nat(const Positive &x);
};

struct BinNat {
  static N add(N n, N m);
  static uint64_t to_nat(const N &a0);
};

/// Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
/// testing of Crane: a generated program, shrunk by ephyra and reduced by hand.
///
/// Wrong value, no diagnostic.  With Loopify, Reuse and SharedVariant all on
/// (any two are fine), Stdlib's Pos.add 9 19 is 20 in C++ instead of
/// 28 (so N.add 9 19 too, without any N mapping); Pos.add 1 1,
/// Pos.add 3 1, Pos.succ 7 are right.  The mutually recursive
/// Pos.add/Pos.add_carry run as explicit-stack frames reusing their
/// matched cells in place.  No sanitizer report.
struct PosAddLoopifyReuseShared {
  static inline const uint64_t a = Coq_Pos::to_nat(Coq_Pos::add(
      Positive::xi(Positive::xo(Positive::xo(Positive::xh()))),
      Positive::xi(Positive::xi(Positive::xo(Positive::xo(Positive::xh()))))));
  static inline const uint64_t b = BinNat::to_nat(BinNat::add(
      N::npos(Positive::xi(Positive::xo(Positive::xo(Positive::xh())))),
      N::npos(Positive::xi(
          Positive::xi(Positive::xo(Positive::xo(Positive::xh())))))));
  static inline const uint64_t c =
      Coq_Pos::to_nat(Coq_Pos::add(Positive::xh(), Positive::xh()));
};
