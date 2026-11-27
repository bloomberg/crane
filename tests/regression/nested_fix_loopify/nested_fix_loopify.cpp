#include "nested_fix_loopify.h"

uint64_t NestedFixLoopify::outer(const NestedFixLoopify::lst &l) {
  // Explicit stack replaces the non-tail recursion of outer: _call frames are
  // pending calls, _after frames resume a caller.
  struct _call {
    const NestedFixLoopify::lst *l;
  };

  struct _after_outer_in_Cons {
    uint64_t a0;
    std::shared_ptr<NestedFixLoopify::lst> a1;
  };

  using _frame = std::variant<_call, _after_outer_in_Cons>;
  uint64_t _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&l});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const NestedFixLoopify::lst &l = *_f.l;
      if (std::holds_alternative<typename NestedFixLoopify::lst::Nil>(l.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] =
            std::get<typename NestedFixLoopify::lst::Cons>(l.v());
        _stack.emplace_back(_after_outer_in_Cons{a0, a1});
        _stack.emplace_back(_call{crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<_after_outer_in_Cons>(_popped));
      _stack.pop_back();
      uint64_t a0 = _f.a0;
      std::shared_ptr<NestedFixLoopify::lst> a1 = std::move(_f.a1);
      _result = ([&]() {
        auto inner =
            [&](const NestedFixLoopify::lst &m, uint64_t a) -> uint64_t {
              // Loop replaces the tail recursion: each recursive call updates
              // the loop variables.
              const NestedFixLoopify::lst *_loop_m = &m;
              while (true) {
                if (std::holds_alternative<typename NestedFixLoopify::lst::Nil>(
                        _loop_m->v())) {
                  return a;
                } else {
                  const auto &[a2, a3] =
                      std::get<typename NestedFixLoopify::lst::Cons>(
                          _loop_m->v());
                  a = (a + (a2 * a0));
                  _loop_m = crane_raw(a3);
                }
              }
            };
        return inner(*a1, UINT64_C(0));
      }() + _result);
    }
  }
  return _result;
}

NestedFixLoopify::lst NestedFixLoopify::mk(uint64_t n) {
  // Builds the result front to back: _write points at the empty tail the next
  // cell fills.
  std::optional<NestedFixLoopify::lst> _root{};
  std::shared_ptr<NestedFixLoopify::lst> *_write = nullptr;
  while (true) {
    if (n <= 0) {
      auto _value = lst::nil();
      (_write ? *(*_write = std::make_shared<NestedFixLoopify::lst>(
                      std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      uint64_t m = n - 1;
      auto _cell = typename NestedFixLoopify::lst::Cons(UINT64_C(2), nullptr);
      NestedFixLoopify::lst &_node =
          (_write ? *(*_write = std::make_shared<NestedFixLoopify::lst>(
                          std::move(_cell)))
                  : _root.emplace(std::move(_cell)));
      _write =
          &std::get<typename NestedFixLoopify::lst::Cons>(_node.v_mut()).a1;
      n = m;
      continue;
    }
  }
  return std::move(*_root);
}

uint64_t NestedFixLoopify::go(uint64_t n) { return outer(mk(n)); }
