#include "stmonad.h"

uint64_t fibFun(uint64_t n) { /// _Enter: captures varying parameters for each
                              /// recursive call.

  struct _Enter {
    uint64_t n;
  };

  /// _After_m: saves [m0], dispatches next recursive call.
  struct _After_m {
    uint64_t m0;
  };

  /// _Combine_m: receives partial results, combines with _result from final
  /// call.
  struct _Combine_m {
    uint64_t _result;
  };

  using _Frame = std::variant<_Enter, _After_m, _Combine_m>;
  uint64_t _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{n});
  /// Loopified fibFun: _Enter -> _After_m -> _Combine_m.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      uint64_t n = _f.n;
      if (n <= 0) {
        _result = UINT64_C(0);
      } else {
        uint64_t m0 = n - 1;
        if (m0 <= 0) {
          _result = UINT64_C(1);
        } else {
          uint64_t m = m0 - 1;
          _stack.emplace_back(_After_m{m0});
          _stack.emplace_back(_Enter{m});
        }
      }
    } else if (std::holds_alternative<_After_m>(_frame)) {
      auto _f = std::move(std::get<_After_m>(_frame));
      _stack.emplace_back(_Combine_m{std::move(_result)});
      _stack.emplace_back(_Enter{_f.m0});
    } else {
      auto _f = std::move(std::get<_Combine_m>(_frame));
      _result = (std::move(_result) + std::move(_f._result));
    }
  }
  return _result;
}

List<uint64_t>
ListDef::seq(uint64_t start,
             uint64_t len) { /// _Enter: captures varying parameters for each
                             /// recursive call.

  struct _Enter {
    uint64_t len;
    uint64_t start;
  };

  /// _Resume_len0: saves [start], resumes after recursive call with _result.
  struct _Resume_len0 {
    uint64_t start;
  };

  using _Frame = std::variant<_Enter, _Resume_len0>;
  List<uint64_t> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{len, start});
  /// Loopified seq: _Enter -> _Resume_len0.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      uint64_t len = _f.len;
      uint64_t start = _f.start;
      if (len <= 0) {
        _result = List<uint64_t>::nil();
      } else {
        uint64_t len0 = len - 1;
        _stack.emplace_back(_Resume_len0{start});
        _stack.emplace_back(_Enter{len0, (start + 1)});
      }
    } else {
      auto _f = std::move(std::get<_Resume_len0>(_frame));
      _result = List<uint64_t>::cons(_f.start, std::move(_result));
    }
  }
  return _result;
}
