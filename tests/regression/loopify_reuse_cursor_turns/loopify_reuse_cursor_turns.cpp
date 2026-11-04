#include "loopify_reuse_cursor_turns.h"

uint64_t
LoopifyReuseCursorTurns::sum(const LoopifyReuseCursorTurns::lst
                                 &l) { /// CraneEnter: captures varying
                                       /// parameters for each recursive call.

  struct CraneEnter {
    const LoopifyReuseCursorTurns::lst *l;
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
      const LoopifyReuseCursorTurns::lst &l = *_f.l;
      if (std::holds_alternative<typename LoopifyReuseCursorTurns::lst::Nil>(
              l.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] =
            std::get<typename LoopifyReuseCursorTurns::lst::Cons>(l.v());
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

LoopifyReuseCursorTurns::lst
LoopifyReuseCursorTurns::keep_even(LoopifyReuseCursorTurns::lst l) {
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
        _write = &std::get<typename LoopifyReuseCursorTurns::lst::Cons>(
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
  crane::rc<LoopifyReuseCursorTurns::lst> _head{};
  crane::rc<LoopifyReuseCursorTurns::lst> *_write = &_head;
  crane::rc<LoopifyReuseCursorTurns::lst> _own =
      crane::rc<LoopifyReuseCursorTurns::lst>();
  bool _uniq = true;
  const LoopifyReuseCursorTurns::lst *_loop_l = &l;
  uint64_t _loop_seen = seen;
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
            std::move(_rs.token), typename LoopifyReuseCursorTurns::lst::Cons(
                                      (a0 + _loop_seen), nullptr));
        *_write = std::move(_cell);
        _write = &std::get<typename LoopifyReuseCursorTurns::lst::Cons>(
                      (*_write)->v_mut())
                      .a1;
        _own = std::move(_rs.next);
        _loop_l = _own.get();
        continue;
      } else {
        auto _read = (_loop_seen + sum(*a1));
        auto _rs = crane::reuse_step(_own, _uniq, a1);
        _loop_seen = std::move(_read);
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
        _write = &std::get<typename LoopifyReuseCursorTurns::lst::Cons>(
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
      _write = &std::get<typename LoopifyReuseCursorTurns::lst::Cons>(
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
  crane::rc<LoopifyReuseCursorTurns::lst> _head{};
  crane::rc<LoopifyReuseCursorTurns::lst> *_write = &_head;
  crane::rc<LoopifyReuseCursorTurns::lst> _own =
      crane::rc<LoopifyReuseCursorTurns::lst>();
  bool _uniq = true;
  const LoopifyReuseCursorTurns::lst *_loop_l = &l;
  uint64_t _loop_acc = acc;
  while (true) {
    if (std::holds_alternative<typename LoopifyReuseCursorTurns::lst::Nil>(
            _loop_l->v())) {
      *_write = crane::make_rc<LoopifyReuseCursorTurns::lst>(lst::nil());
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename LoopifyReuseCursorTurns::lst::Cons>(_loop_l->v());
      auto _read = (_loop_acc + a0);
      auto _rs = crane::reuse_step(_own, _uniq, a1);
      auto _cell = crane::make_rc_reusing_unchecked(
          std::move(_rs.token), typename LoopifyReuseCursorTurns::lst::Cons(
                                    (a0 * _loop_acc), nullptr));
      *_write = std::move(_cell);
      _write = &std::get<typename LoopifyReuseCursorTurns::lst::Cons>(
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

LoopifyReuseCursorTurns::lst
LoopifyReuseCursorTurns::suffix_sums(LoopifyReuseCursorTurns::lst l) {
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
      auto _read = sum(*_loop_l);
      auto _rs = crane::reuse_step(_own, _uniq, a1);
      auto _cell = crane::make_rc_reusing_unchecked(
          std::move(_rs.token), typename LoopifyReuseCursorTurns::lst::Cons(
                                    std::move(_read), nullptr));
      *_write = std::move(_cell);
      _write = &std::get<typename LoopifyReuseCursorTurns::lst::Cons>(
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
  uint64_t _loop_n = n;
  while (true) {
    if (_loop_n <= 0) {
      return true;
    } else {
      uint64_t n0 = _loop_n - 1;
      if (n0 <= 0) {
        return false;
      } else {
        uint64_t n_ = n0 - 1;
        _loop_n = n_;
      }
    }
  }
}
