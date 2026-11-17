#include "loopify_reuse_cursor_reads_field.h"

uint64_t
LoopifyReuseCursorReadsField::len(const LoopifyReuseCursorReadsField::lst &l) {
  // Explicit stack replaces the non-tail recursion of len: _call frames are
  // pending calls, _after frames resume a caller.
  struct _call {
    const LoopifyReuseCursorReadsField::lst *l;
  };

  struct _after_len_in_Cons {};

  using _frame = std::variant<_call, _after_len_in_Cons>;
  uint64_t _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&l});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const LoopifyReuseCursorReadsField::lst &l = *_f.l;
      if (std::holds_alternative<
              typename LoopifyReuseCursorReadsField::lst::Nil>(l.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[_, a1] =
            std::get<typename LoopifyReuseCursorReadsField::lst::Cons>(l.v());
        _stack.emplace_back(_after_len_in_Cons{});
        _stack.emplace_back(_call{crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<_after_len_in_Cons>(_popped));
      _stack.pop_back();
      _result = (std::move(_result) + 1);
    }
  }
  return _result;
}

uint64_t
LoopifyReuseCursorReadsField::sum(const LoopifyReuseCursorReadsField::lst &l) {
  // Explicit stack replaces the non-tail recursion of sum: _call frames are
  // pending calls, _after frames resume a caller.
  struct _call {
    const LoopifyReuseCursorReadsField::lst *l;
  };

  struct _after_sum_in_Cons {
    uint64_t a0;
  };

  using _frame = std::variant<_call, _after_sum_in_Cons>;
  uint64_t _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&l});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const LoopifyReuseCursorReadsField::lst &l = *_f.l;
      if (std::holds_alternative<
              typename LoopifyReuseCursorReadsField::lst::Nil>(l.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] =
            std::get<typename LoopifyReuseCursorReadsField::lst::Cons>(l.v());
        _stack.emplace_back(_after_sum_in_Cons{a0});
        _stack.emplace_back(_call{crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<_after_sum_in_Cons>(_popped));
      _stack.pop_back();
      uint64_t a0 = _f.a0;
      _result = (a0 + std::move(_result));
    }
  }
  return _result;
}

LoopifyReuseCursorReadsField::lst
LoopifyReuseCursorReadsField::pairs(LoopifyReuseCursorReadsField::lst l) {
  // Builds the result front to back: _write points at the empty tail the next
  // cell fills. The input's cells are reused in place while uniquely owned.
  crane::rc<LoopifyReuseCursorReadsField::lst> _head{};
  crane::rc<LoopifyReuseCursorReadsField::lst> *_write = &_head;
  crane::rc<LoopifyReuseCursorReadsField::lst> _own =
      crane::rc<LoopifyReuseCursorReadsField::lst>();
  bool _uniq = true;
  const LoopifyReuseCursorReadsField::lst *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<typename LoopifyReuseCursorReadsField::lst::Nil>(
            _loop_l->v())) {
      *_write = crane::make_rc<LoopifyReuseCursorReadsField::lst>(lst::nil());
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename LoopifyReuseCursorReadsField::lst::Cons>(
              _loop_l->v());
      auto _read = (a0 + len(*a1));
      auto _rs = crane::reuse_step(_own, _uniq, a1);
      auto _cell = crane::make_rc_reusing_unchecked(
          std::move(_rs.token),
          typename LoopifyReuseCursorReadsField::lst::Cons(std::move(_read),
                                                           nullptr));
      *_write = std::move(_cell);
      _write =
          &std::get<typename LoopifyReuseCursorReadsField::lst::Cons>(
              (*_write)->v_mut())
              .a1;
      _own = std::move(_rs.next);
      _loop_l = _own.get();
      continue;
    }
  }
  return std::move(*_head);
}

LoopifyReuseCursorReadsField::lst
LoopifyReuseCursorReadsField::weigh(uint64_t acc,
                                    LoopifyReuseCursorReadsField::lst l) {
  // Builds the result front to back: _write points at the empty tail the next
  // cell fills. The input's cells are reused in place while uniquely owned.
  crane::rc<LoopifyReuseCursorReadsField::lst> _head{};
  crane::rc<LoopifyReuseCursorReadsField::lst> *_write = &_head;
  crane::rc<LoopifyReuseCursorReadsField::lst> _own =
      crane::rc<LoopifyReuseCursorReadsField::lst>();
  bool _uniq = true;
  const LoopifyReuseCursorReadsField::lst *_loop_l = &l;
  uint64_t _loop_acc = acc;
  while (true) {
    if (std::holds_alternative<typename LoopifyReuseCursorReadsField::lst::Nil>(
            _loop_l->v())) {
      *_write = crane::make_rc<LoopifyReuseCursorReadsField::lst>(lst::nil());
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename LoopifyReuseCursorReadsField::lst::Cons>(
              _loop_l->v());
      auto _read = len(*a1);
      auto _rs = crane::reuse_step(_own, _uniq, a1);
      auto _cell = crane::make_rc_reusing_unchecked(
          std::move(_rs.token),
          typename LoopifyReuseCursorReadsField::lst::Cons((a0 * _loop_acc),
                                                           nullptr));
      *_write = std::move(_cell);
      _write =
          &std::get<typename LoopifyReuseCursorReadsField::lst::Cons>(
              (*_write)->v_mut())
              .a1;
      _loop_acc = std::move(_read);
      _own = std::move(_rs.next);
      _loop_l = _own.get();
      continue;
    }
  }
  return std::move(*_head);
}
