#include "loopify_reuse_cursor_turns.h"

uint64_t LoopifyReuseCursorTurns::sum(const LoopifyReuseCursorTurns::lst &l) {
  // Explicit stack replaces the non-tail recursion of sum: _call frames are
  // pending calls, _after frames resume a caller.
  struct _call {
    const LoopifyReuseCursorTurns::lst *l;
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
      const LoopifyReuseCursorTurns::lst &l = *_f.l;
      if (std::holds_alternative<typename LoopifyReuseCursorTurns::lst::Nil>(
              l.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] =
            std::get<typename LoopifyReuseCursorTurns::lst::Cons>(l.v());
        _stack.emplace_back(_after_sum_in_Cons{a0});
        _stack.emplace_back(_call{crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<_after_sum_in_Cons>(_popped));
      _stack.pop_back();
      uint64_t a0 = _f.a0;
      _result = (a0 + _result);
    }
  }
  return _result;
}

LoopifyReuseCursorTurns::lst
LoopifyReuseCursorTurns::keep_even(LoopifyReuseCursorTurns::lst l) {
  // Builds the result front to back: _write points at the empty tail the next
  // cell fills. The input's cells are reused in place while uniquely owned.
  crane::rc<LoopifyReuseCursorTurns::lst> _head{};
  crane::rc<LoopifyReuseCursorTurns::lst> *_write = &_head;
  crane::rc<LoopifyReuseCursorTurns::lst> _own =
      crane::rc<LoopifyReuseCursorTurns::lst>();
  bool _uniq = true;
  const LoopifyReuseCursorTurns::lst *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<typename LoopifyReuseCursorTurns::lst::Nil>(
            _loop_l->v())) {
      *_write = crane::make_rc<LoopifyReuseCursorTurns::lst>(lst::nil());
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename LoopifyReuseCursorTurns::lst::Cons>(_loop_l->v());
      if (Nat::even(a0)) {
        auto _rs = crane::reuse_step(_own, _uniq, a1);
        auto _cell = crane::make_rc_reusing_unchecked(
            std::move(_rs.token),
            typename LoopifyReuseCursorTurns::lst::Cons(a0, nullptr));
        *_write = std::move(_cell);
        _write =
            &std::get<typename LoopifyReuseCursorTurns::lst::Cons>(
                (*_write)->v_mut())
                .a1;
        _own = std::move(_rs.next);
        _loop_l = _own.get();
        continue;
      } else {
        auto _rs = crane::reuse_step(_own, _uniq, a1);
        _own = std::move(_rs.next);
        _loop_l = _own.get();
        continue;
      }
    }
  }
  return std::move(*_head);
}

LoopifyReuseCursorTurns::lst
LoopifyReuseCursorTurns::skip_sums(uint64_t seen,
                                   LoopifyReuseCursorTurns::lst l) {
  // Builds the result front to back: _write points at the empty tail the next
  // cell fills. The input's cells are reused in place while uniquely owned.
  crane::rc<LoopifyReuseCursorTurns::lst> _head{};
  crane::rc<LoopifyReuseCursorTurns::lst> *_write = &_head;
  crane::rc<LoopifyReuseCursorTurns::lst> _own =
      crane::rc<LoopifyReuseCursorTurns::lst>();
  bool _uniq = true;
  const LoopifyReuseCursorTurns::lst *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<typename LoopifyReuseCursorTurns::lst::Nil>(
            _loop_l->v())) {
      *_write = crane::make_rc<LoopifyReuseCursorTurns::lst>(lst::nil());
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename LoopifyReuseCursorTurns::lst::Cons>(_loop_l->v());
      if (Nat::even(a0)) {
        auto _rs = crane::reuse_step(_own, _uniq, a1);
        auto _cell = crane::make_rc_reusing_unchecked(
            std::move(_rs.token),
            typename LoopifyReuseCursorTurns::lst::Cons((a0 + seen), nullptr));
        *_write = std::move(_cell);
        _write =
            &std::get<typename LoopifyReuseCursorTurns::lst::Cons>(
                (*_write)->v_mut())
                .a1;
        _own = std::move(_rs.next);
        _loop_l = _own.get();
        continue;
      } else {
        auto _read = (seen + sum(*a1));
        auto _rs = crane::reuse_step(_own, _uniq, a1);
        seen = _read;
        _own = std::move(_rs.next);
        _loop_l = _own.get();
        continue;
      }
    }
  }
  return std::move(*_head);
}

LoopifyReuseCursorTurns::lst
LoopifyReuseCursorTurns::swap(LoopifyReuseCursorTurns::lst l) {
  // Builds the result front to back: _write points at the empty tail the next
  // cell fills.
  std::optional<LoopifyReuseCursorTurns::lst> _root{};
  crane::rc<LoopifyReuseCursorTurns::lst> *_write = nullptr;
  const LoopifyReuseCursorTurns::lst *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<typename LoopifyReuseCursorTurns::lst::Nil>(
            _loop_l->v())) {
      auto _value = lst::nil();
      (_write ? *(*_write = crane::make_rc<LoopifyReuseCursorTurns::lst>(
                      std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename LoopifyReuseCursorTurns::lst::Cons>(_loop_l->v());
      auto &&_sv0 = *a1;
      if (std::holds_alternative<typename LoopifyReuseCursorTurns::lst::Nil>(
              _sv0.v())) {
        auto _value = lst::cons(a0, lst::nil());
        (_write ? *(*_write = crane::make_rc<LoopifyReuseCursorTurns::lst>(
                        std::move(_value)))
                : _root.emplace(std::move(_value)));
        break;
      } else {
        const auto &[a00, a10] =
            std::get<typename LoopifyReuseCursorTurns::lst::Cons>(_sv0.v());
        auto _cell1 = crane::make_rc<LoopifyReuseCursorTurns::lst>(
            typename LoopifyReuseCursorTurns::lst::Cons(a0, nullptr));
        auto _cell =
            typename LoopifyReuseCursorTurns::lst::Cons(a00, std::move(_cell1));
        LoopifyReuseCursorTurns::lst &_node =
            (_write ? *(*_write = crane::make_rc<LoopifyReuseCursorTurns::lst>(
                            std::move(_cell)))
                    : _root.emplace(std::move(_cell)));
        _write =
            &std::get<typename LoopifyReuseCursorTurns::lst::Cons>(
                std::get<typename LoopifyReuseCursorTurns::lst::Cons>(
                    _node.v_mut())
                    .a1->v_mut())
                .a1;
        _loop_l = crane_raw(a10);
        continue;
      }
    }
  }
  return std::move(*_root);
}

LoopifyReuseCursorTurns::lst
LoopifyReuseCursorTurns::stutter(LoopifyReuseCursorTurns::lst l) {
  // Builds the result front to back: _write points at the empty tail the next
  // cell fills. The input's cells are reused in place while uniquely owned.
  crane::rc<LoopifyReuseCursorTurns::lst> _head{};
  crane::rc<LoopifyReuseCursorTurns::lst> *_write = &_head;
  crane::rc<LoopifyReuseCursorTurns::lst> _own =
      crane::rc<LoopifyReuseCursorTurns::lst>();
  bool _uniq = true;
  const LoopifyReuseCursorTurns::lst *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<typename LoopifyReuseCursorTurns::lst::Nil>(
            _loop_l->v())) {
      *_write = crane::make_rc<LoopifyReuseCursorTurns::lst>(lst::nil());
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename LoopifyReuseCursorTurns::lst::Cons>(_loop_l->v());
      auto _read = a0;
      auto _rs = crane::reuse_step(_own, _uniq, a1);
      auto _cell = crane::make_rc_reusing_unchecked(
          std::move(_rs.token),
          typename LoopifyReuseCursorTurns::lst::Cons((a0 + 1), nullptr));
      auto _cell1 = crane::make_rc<LoopifyReuseCursorTurns::lst>(
          typename LoopifyReuseCursorTurns::lst::Cons(std::move(_read),
                                                      nullptr));
      std::get<typename LoopifyReuseCursorTurns::lst::Cons>(_cell->v_mut()).a1 =
          std::move(_cell1);
      *_write = std::move(_cell);
      _write =
          &std::get<typename LoopifyReuseCursorTurns::lst::Cons>(
              std::get<typename LoopifyReuseCursorTurns::lst::Cons>(
                  (*_write)->v_mut())
                  .a1->v_mut())
              .a1;
      _own = std::move(_rs.next);
      _loop_l = _own.get();
      continue;
    }
  }
  return std::move(*_head);
}

LoopifyReuseCursorTurns::lst
LoopifyReuseCursorTurns::scale(uint64_t acc, LoopifyReuseCursorTurns::lst l) {
  // Builds the result front to back: _write points at the empty tail the next
  // cell fills. The input's cells are reused in place while uniquely owned.
  crane::rc<LoopifyReuseCursorTurns::lst> _head{};
  crane::rc<LoopifyReuseCursorTurns::lst> *_write = &_head;
  crane::rc<LoopifyReuseCursorTurns::lst> _own =
      crane::rc<LoopifyReuseCursorTurns::lst>();
  bool _uniq = true;
  const LoopifyReuseCursorTurns::lst *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<typename LoopifyReuseCursorTurns::lst::Nil>(
            _loop_l->v())) {
      *_write = crane::make_rc<LoopifyReuseCursorTurns::lst>(lst::nil());
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename LoopifyReuseCursorTurns::lst::Cons>(_loop_l->v());
      auto _read = (acc + a0);
      auto _rs = crane::reuse_step(_own, _uniq, a1);
      auto _cell = crane::make_rc_reusing_unchecked(
          std::move(_rs.token),
          typename LoopifyReuseCursorTurns::lst::Cons((a0 * acc), nullptr));
      *_write = std::move(_cell);
      _write =
          &std::get<typename LoopifyReuseCursorTurns::lst::Cons>(
              (*_write)->v_mut())
              .a1;
      acc = _read;
      _own = std::move(_rs.next);
      _loop_l = _own.get();
      continue;
    }
  }
  return std::move(*_head);
}

LoopifyReuseCursorTurns::lst
LoopifyReuseCursorTurns::suffix_sums(LoopifyReuseCursorTurns::lst l) {
  // Builds the result front to back: _write points at the empty tail the next
  // cell fills. The input's cells are reused in place while uniquely owned.
  crane::rc<LoopifyReuseCursorTurns::lst> _head{};
  crane::rc<LoopifyReuseCursorTurns::lst> *_write = &_head;
  crane::rc<LoopifyReuseCursorTurns::lst> _own =
      crane::rc<LoopifyReuseCursorTurns::lst>();
  bool _uniq = true;
  const LoopifyReuseCursorTurns::lst *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<typename LoopifyReuseCursorTurns::lst::Nil>(
            _loop_l->v())) {
      *_write = crane::make_rc<LoopifyReuseCursorTurns::lst>(lst::nil());
      break;
    } else {
      const auto &[_, a1] =
          std::get<typename LoopifyReuseCursorTurns::lst::Cons>(_loop_l->v());
      auto _read = sum(*_loop_l);
      auto _rs = crane::reuse_step(_own, _uniq, a1);
      auto _cell = crane::make_rc_reusing_unchecked(
          std::move(_rs.token),
          typename LoopifyReuseCursorTurns::lst::Cons(_read, nullptr));
      *_write = std::move(_cell);
      _write =
          &std::get<typename LoopifyReuseCursorTurns::lst::Cons>(
              (*_write)->v_mut())
              .a1;
      _own = std::move(_rs.next);
      _loop_l = _own.get();
      continue;
    }
  }
  return std::move(*_head);
}

bool Nat::even(uint64_t n) {
  // Loop replaces the tail recursion: each recursive call updates the loop
  // variables.
  while (true) {
    if (n <= 0) {
      return true;
    } else {
      uint64_t n0 = n - 1;
      if (n0 <= 0) {
        return false;
      } else {
        uint64_t n_ = n0 - 1;
        n = n_;
      }
    }
  }
}
