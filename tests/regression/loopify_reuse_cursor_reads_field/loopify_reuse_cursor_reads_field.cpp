#include "loopify_reuse_cursor_reads_field.h"

uint64_t LoopifyReuseCursorReadsField::len(
    const LoopifyReuseCursorReadsField::lst
        &l) { /// CraneEnter: captures varying parameters for each recursive
              /// call.

  struct CraneEnter {
    const LoopifyReuseCursorReadsField::lst *l;
  };

  /// CraneCont_Cons: resumes after recursive call, then processes rest.
  struct CraneCont_Cons {};

  using CraneFrame = std::variant<CraneEnter, CraneCont_Cons>;
  uint64_t _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{&l});
  /// Loopified len: CraneEnter -> CraneCont_Cons.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      const LoopifyReuseCursorReadsField::lst &l = *_f.l;
      if (std::holds_alternative<
              typename LoopifyReuseCursorReadsField::lst::Nil>(l.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] =
            std::get<typename LoopifyReuseCursorReadsField::lst::Cons>(l.v());
        _stack.emplace_back(CraneCont_Cons{});
        _stack.emplace_back(CraneEnter{crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<CraneCont_Cons>(_frame));
      _result = (std::move(_result) + 1);
    }
  }
  return _result;
}

uint64_t LoopifyReuseCursorReadsField::sum(
    const LoopifyReuseCursorReadsField::lst
        &l) { /// CraneEnter: captures varying parameters for each recursive
              /// call.

  struct CraneEnter {
    const LoopifyReuseCursorReadsField::lst *l;
  };

  /// CraneCont_Cons: saves [a0], resumes after recursive call, then processes
  /// rest.
  struct CraneCont_Cons {
    uint64_t a0;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont_Cons>;
  uint64_t _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{&l});
  /// Loopified sum: CraneEnter -> CraneCont_Cons.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      const LoopifyReuseCursorReadsField::lst &l = *_f.l;
      if (std::holds_alternative<
              typename LoopifyReuseCursorReadsField::lst::Nil>(l.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] =
            std::get<typename LoopifyReuseCursorReadsField::lst::Cons>(l.v());
        _stack.emplace_back(CraneCont_Cons{a0});
        _stack.emplace_back(CraneEnter{crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<CraneCont_Cons>(_frame));
      uint64_t a0 = _f.a0;
      _result = (a0 + std::move(_result));
    }
  }
  return _result;
}

LoopifyReuseCursorReadsField::lst
LoopifyReuseCursorReadsField::pairs(LoopifyReuseCursorReadsField::lst l) {
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
      _write = &std::get<typename LoopifyReuseCursorReadsField::lst::Cons>(
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
      _write = &std::get<typename LoopifyReuseCursorReadsField::lst::Cons>(
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
