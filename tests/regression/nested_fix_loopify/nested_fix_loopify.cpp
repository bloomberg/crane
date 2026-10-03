#include "nested_fix_loopify.h"

uint64_t NestedFixLoopify::outer(
    const NestedFixLoopify::lst
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const NestedFixLoopify::lst *l;
  };

  /// _Cont_Cons: saves [a0, a1], resumes after recursive call, then processes
  /// rest.
  struct _Cont_Cons {
    uint64_t a0;
    std::shared_ptr<NestedFixLoopify::lst> a1;
  };

  using _Frame = std::variant<_Enter, _Cont_Cons>;
  uint64_t _result{};
  crane::small_vector<_Frame> _stack;
  _stack.emplace_back(_Enter{&l});
  /// Loopified outer: _Enter -> _Cont_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const NestedFixLoopify::lst &l = *_f.l;
      if (std::holds_alternative<typename NestedFixLoopify::lst::Nil>(l.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] =
            std::get<typename NestedFixLoopify::lst::Cons>(l.v());
        _stack.emplace_back(_Cont_Cons{a0, a1});
        _stack.emplace_back(_Enter{crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<_Cont_Cons>(_frame));
      uint64_t a0 = _f.a0;
      std::shared_ptr<NestedFixLoopify::lst> a1 = std::move(_f.a1);
      _result = ([&]() {
        auto inner_impl = [&](auto &, const NestedFixLoopify::lst &m,
                              uint64_t a) -> uint64_t {
          uint64_t _loop_a = std::move(a);
          const NestedFixLoopify::lst *_loop_m = &m;
          while (true) {
            if (std::holds_alternative<typename NestedFixLoopify::lst::Nil>(
                    _loop_m->v())) {
              return _loop_a;
            } else {
              const auto &[a2, a3] =
                  std::get<typename NestedFixLoopify::lst::Cons>(_loop_m->v());
              _loop_a = (_loop_a + (a2 * a0));
              _loop_m = crane_raw(a3);
            }
          }
        };
        auto inner = [&](const NestedFixLoopify::lst &m,
                         uint64_t a) -> uint64_t {
          return inner_impl(inner_impl, m, a);
        };
        return inner(*a1, UINT64_C(0));
      }() + std::move(_result));
    }
  }
  return _result;
}

NestedFixLoopify::lst NestedFixLoopify::mk(uint64_t n) {
  std::shared_ptr<NestedFixLoopify::lst> _head{};
  std::shared_ptr<NestedFixLoopify::lst> *_write = &_head;
  uint64_t _loop_n = std::move(n);
  while (true) {
    if (_loop_n <= 0) {
      *_write = std::make_shared<NestedFixLoopify::lst>(lst::nil());
      break;
    } else {
      uint64_t m = _loop_n - 1;
      auto _cell = std::make_shared<NestedFixLoopify::lst>(
          typename NestedFixLoopify::lst::Cons(UINT64_C(2), nullptr));
      *_write = std::move(_cell);
      _write =
          &std::get<typename NestedFixLoopify::lst::Cons>((*_write)->v_mut())
               .a1;
      _loop_n = m;
      continue;
    }
  }
  return std::move(*_head);
}

uint64_t NestedFixLoopify::go(uint64_t n) { return outer(mk(n)); }
