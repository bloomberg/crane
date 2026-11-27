#include "loopify_partner_tail_and_invoked.h"

/// walk calls its partner step both as a tail call and as the operand
/// of an addition, and step calls walk back where its body runs.  Its
/// machine continues in step's body at the tail call and enters a copy of
/// step at the other, whose calls of walk are turns of the one machine:
/// no call between the two runs on the C++ stack, however deep.
uint64_t LoopifyPartnerTailAndInvoked::walk(uint64_t n) {
  // Explicit stack replaces the non-tail recursion of walk: _call frames are
  // pending calls, _after frames resume a caller.
  struct _call {
    uint64_t n;
  };

  struct _call_step_entry {
    uint64_t n0;
  };

  struct _after_step_entry_in_false {};

  struct _after_walk_in_S {};

  struct _after_walk_in_S_2 {};

  using _frame =
      std::variant<_call, _call_step_entry, _after_step_entry_in_false,
                   _after_walk_in_S, _after_walk_in_S_2>;
  uint64_t _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{n});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      uint64_t n = _f.n;
      if (n <= 0) {
        _result = UINT64_C(0);
      } else {
        uint64_t m = n - 1;
        if ((UINT64_C(2) ? m % UINT64_C(2) : m) == UINT64_C(0)) {
          if (m <= 0) {
            _result = UINT64_C(1);
          } else {
            uint64_t m0 = m - 1;
            _stack.emplace_back(_after_walk_in_S{});
            _stack.emplace_back(_call{m0});
          }
        } else {
          _stack.emplace_back(_after_step_entry_in_false{});
          _stack.emplace_back(_call_step_entry{m});
        }
      }
    } else if (std::holds_alternative<_call_step_entry>(_popped)) {
      auto _f = std::move(std::get<_call_step_entry>(_popped));
      _stack.pop_back();
      uint64_t n0 = _f.n0;
      if (n0 <= 0) {
        _result = UINT64_C(1);
      } else {
        uint64_t m = n0 - 1;
        _stack.emplace_back(_after_walk_in_S_2{});
        _stack.emplace_back(_call{m});
      }
    } else if (std::holds_alternative<_after_step_entry_in_false>(_popped)) {
      auto _f = std::move(std::get<_after_step_entry_in_false>(_popped));
      _stack.pop_back();
      _result = UINT64_C(1) + _result;
    } else if (std::holds_alternative<_after_walk_in_S>(_popped)) {
      auto _f = std::move(std::get<_after_walk_in_S>(_popped));
      _stack.pop_back();
      _result = (_result + 1);
    } else {
      auto _f = std::move(std::get<_after_walk_in_S_2>(_popped));
      _stack.pop_back();
      _result = (_result + 1);
    }
  }
  return _result;
}

uint64_t LoopifyPartnerTailAndInvoked::step(uint64_t n) {
  // Explicit stack replaces the non-tail recursion of step: _call frames are
  // pending calls, _after frames resume a caller.
  struct _call {
    uint64_t n;
  };

  struct _call_walk_entry {
    uint64_t n0;
  };

  struct _after_step_in_false {};

  struct _after_walk_entry_in_S {};

  using _frame = std::variant<_call, _call_walk_entry, _after_step_in_false,
                              _after_walk_entry_in_S>;
  uint64_t _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{n});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      uint64_t n = _f.n;
      if (n <= 0) {
        _result = UINT64_C(1);
      } else {
        uint64_t m = n - 1;
        _stack.emplace_back(_after_walk_entry_in_S{});
        _stack.emplace_back(_call_walk_entry{m});
      }
    } else if (std::holds_alternative<_call_walk_entry>(_popped)) {
      auto _f = std::move(std::get<_call_walk_entry>(_popped));
      _stack.pop_back();
      uint64_t n0 = _f.n0;
      if (n0 <= 0) {
        _result = UINT64_C(0);
      } else {
        uint64_t m = n0 - 1;
        if ((UINT64_C(2) ? m % UINT64_C(2) : m) == UINT64_C(0)) {
          _stack.emplace_back(_call{m});
        } else {
          _stack.emplace_back(_after_step_in_false{});
          _stack.emplace_back(_call{m});
        }
      }
    } else if (std::holds_alternative<_after_step_in_false>(_popped)) {
      auto _f = std::move(std::get<_after_step_in_false>(_popped));
      _stack.pop_back();
      _result = UINT64_C(1) + _result;
    } else {
      auto _f = std::move(std::get<_after_walk_entry_in_S>(_popped));
      _stack.pop_back();
      _result = (_result + 1);
    }
  }
  return _result;
}
