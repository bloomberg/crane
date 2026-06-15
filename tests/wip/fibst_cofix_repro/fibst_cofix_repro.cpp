#include "fibst_cofix_repro.h"

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
