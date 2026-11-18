#include "loopify_rematch_frame_binder.h"

/// Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
/// testing of Crane: a generated program, shrunk by ephyra and reduced by hand.
///
/// Under Loopify, a non-tail recursive function that re-matches its own
/// argument inside the recursive branch (match n with O => [] | S _ => h m
/// end ++ h m) builds a continuation frame from _x, a name only declared as
/// a member of that frame: "use of undeclared identifier '_x'".
List<bool> LoopifyRematchFrameBinder::h(uint64_t n) {
  // Explicit stack replaces the non-tail recursion of h: _call frames are
  // pending calls, _after frames resume a caller.
  struct _call {
    uint64_t n;
  };

  struct _after_h_in_O {
    List<bool> _tmp2;
  };

  struct _after_h_in_S {
    uint64_t m;
  };

  struct _after_h_in_S_2 {
    crane::obj _x;
  };

  using _frame =
      std::variant<_call, _after_h_in_O, _after_h_in_S, _after_h_in_S_2>;
  List<bool> _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{n});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      uint64_t n = _f.n;
      if (n <= 0) {
        _result = List<bool>::nil();
      } else {
        uint64_t m = n - 1;
        List<bool> _tmp2;
        if (n <= 0) {
          _tmp2 = List<bool>::nil();
          {
            _stack.emplace_back(_after_h_in_O{std::move(_tmp2)});
            _stack.emplace_back(_call{m});
          }
        } else {
          uint64_t _x = n - 1;
          _stack.emplace_back(_after_h_in_S{m});
          _stack.emplace_back(_call{m});
        }
      }
    } else if (std::holds_alternative<_after_h_in_O>(_popped)) {
      auto _f = std::move(std::get<_after_h_in_O>(_popped));
      _stack.pop_back();
      _result = _f._tmp2.app(std::move(_result));
    } else if (std::holds_alternative<_after_h_in_S>(_popped)) {
      auto _f = std::move(std::get<_after_h_in_S>(_popped));
      _stack.pop_back();
      uint64_t m = _f.m;
      auto _tmp2 = std::move(_result);
      _stack.emplace_back(_after_h_in_S_2{std::move(_x)});
      _stack.emplace_back(_call{m});
    } else {
      auto _f = std::move(std::get<_after_h_in_S_2>(_popped));
      _stack.pop_back();
      crane::obj _x = std::move(_f._x);
      _result = _tmp2.app(std::move(_result));
    }
  }
  return _result;
}
