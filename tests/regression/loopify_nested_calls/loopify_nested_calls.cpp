#include "loopify_nested_calls.h"

/// Shape 1: a let-bound compound expression computed after the recursive
/// call.  The generated continuation frame is pushed with a variable
/// (here) that is only declared and computed later, inside the
/// continuation branch: C++ compile error.
uint64_t sum_signum(uint64_t n) { /// CraneEnter: captures varying parameters
                                  /// for each recursive call.

  struct CraneEnter {
    uint64_t n;
  };

  /// CraneCont_n_: saves [n_], resumes after recursive call, then processes
  /// rest.
  struct CraneCont_n_ {
    uint64_t n_;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont_n_>;
  uint64_t _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{n});
  /// Loopified sum_signum: CraneEnter -> CraneCont_n_.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      uint64_t n = _f.n;
      if (n <= 0) {
        _result = UINT64_C(0);
      } else {
        uint64_t n_ = n - 1;
        _stack.emplace_back(CraneCont_n_{n_});
        _stack.emplace_back(CraneEnter{n_});
      }
    } else {
      auto _f = std::move(std::get<CraneCont_n_>(_frame));
      uint64_t n_ = _f.n_;
      uint64_t rest = std::move(_result);
      uint64_t here;
      if (n_ == UINT64_C(0)) {
        here = UINT64_C(0);
      } else {
        here = UINT64_C(1);
      }
      _result = (rest + here);
    }
  }
  return _result;
}

/// Shape 2: a recursive call under a conditional inside a let.  The
/// generated continuation branch assigns to a variable (rest) declared in
/// a different scope, and the consumer of rest runs before the recursive
/// frame is processed: C++ compile error, and wrong scheduling besides.
///
/// down_let n computes n-1; n-2; ...; 0: for example,
/// down_let 3 = [2; 1; 0].
List<uint64_t> down_let(uint64_t n) { /// CraneEnter: captures varying
                                      /// parameters for each recursive call.

  struct CraneEnter {
    uint64_t n;
  };

  /// CraneCont1: saves [n_], resumes after recursive call, then processes rest.
  struct CraneCont1 {
    uint64_t n_;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont1>;
  List<uint64_t> _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{n});
  /// Loopified down_let: CraneEnter -> CraneCont1.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      uint64_t n = _f.n;
      if (n <= 0) {
        _result = List<uint64_t>::nil();
      } else {
        uint64_t n_ = n - 1;
        List<uint64_t> rest;
        if (n_ == UINT64_C(0)) {
          rest = List<uint64_t>::nil();
          {
            _result = List<uint64_t>::cons(n_, std::move(rest));
          }
        } else {
          _stack.emplace_back(CraneCont1{n_});
          _stack.emplace_back(CraneEnter{n_});
        }
      }
    } else {
      auto _f = std::move(std::get<CraneCont1>(_frame));
      uint64_t n_ = _f.n_;
      auto rest = std::move(_result);
      _result = List<uint64_t>::cons(n_, std::move(rest));
    }
  }
  return _result;
}

/// Shape 3: the same function as shape 2 with the let inlined, so the
/// recursive call sits under a conditional inside a constructor argument.
/// This one compiles, but the generated loop drops the cons entirely:
/// down_inline 3 equals [2; 1; 0] in Rocq, yet extracts to code that
/// returns .  Plain cons n' (down_inline n') with the recursive call
/// directly in argument position is handled correctly.
List<uint64_t> down_inline(uint64_t n) { /// CraneEnter: captures varying
                                         /// parameters for each recursive call.

  struct CraneEnter {
    uint64_t n;
  };

  /// CraneCont1: saves [n_], resumes after recursive call, then processes rest.
  struct CraneCont1 {
    uint64_t n_;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont1>;
  List<uint64_t> _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{n});
  /// Loopified down_inline: CraneEnter -> CraneCont1.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      uint64_t n = _f.n;
      if (n <= 0) {
        _result = List<uint64_t>::nil();
      } else {
        uint64_t n_ = n - 1;
        List<uint64_t> _tmp1;
        if (n_ == UINT64_C(0)) {
          _tmp1 = List<uint64_t>::nil();
          {
            _result = List<uint64_t>::cons(n_, std::move(_tmp1));
          }
        } else {
          _stack.emplace_back(CraneCont1{n_});
          _stack.emplace_back(CraneEnter{n_});
        }
      }
    } else {
      auto _f = std::move(std::get<CraneCont1>(_frame));
      uint64_t n_ = _f.n_;
      _result = List<uint64_t>::cons(n_, std::move(_result));
    }
  }
  return _result;
}
