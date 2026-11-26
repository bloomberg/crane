#include "loopify_shadow_from_reference.h"

uint64_t
LoopifyShadowFromReference::suml(const LoopifyShadowFromReference::lst &l) {
  // Explicit stack replaces the non-tail recursion of suml: _call frames are
  // pending calls, _after frames resume a caller.
  struct _call {
    const LoopifyShadowFromReference::lst *l;
  };

  struct _after_suml_in_Cons {
    uint64_t a0;
  };

  using _frame = std::variant<_call, _after_suml_in_Cons>;
  uint64_t _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&l});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const LoopifyShadowFromReference::lst &l = *_f.l;
      if (std::holds_alternative<typename LoopifyShadowFromReference::lst::Nil>(
              l.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] =
            std::get<typename LoopifyShadowFromReference::lst::Cons>(l.v());
        _stack.emplace_back(_after_suml_in_Cons{a0});
        _stack.emplace_back(_call{crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<_after_suml_in_Cons>(_popped));
      _stack.pop_back();
      uint64_t a0 = _f.a0;
      _result = (a0 + _result);
    }
  }
  return _result;
}

LoopifyShadowFromReference::lst
LoopifyShadowFromReference::g(LoopifyShadowFromReference::lst l) {
  // Builds the result front to back: _write points at the empty tail the next
  // cell fills. The input's cells are reused in place while uniquely owned.
  crane::rc<LoopifyShadowFromReference::lst> _head{};
  crane::rc<LoopifyShadowFromReference::lst> *_write = &_head;
  crane::rc<LoopifyShadowFromReference::lst> _own =
      crane::rc<LoopifyShadowFromReference::lst>();
  bool _uniq = true;
  const LoopifyShadowFromReference::lst *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<typename LoopifyShadowFromReference::lst::Nil>(
            _loop_l->v())) {
      *_write = crane::make_rc<LoopifyShadowFromReference::lst>(lst::nil());
      break;
    } else {
      const auto &[a0, a1] = std::get<
          typename LoopifyShadowFromReference::lst::Cons>(_loop_l->v());
      const LoopifyShadowFromReference::lst &a1_value = *a1;
      auto _read = twice([=, a1_value = a1_value](uint64_t y) {
        return suml(lst::cons(y, a1_value));
      },
                         a0);
      auto _rs = crane::reuse_step(_own, _uniq, a1);
      auto _cell = crane::make_rc_reusing_unchecked(
          std::move(_rs.token),
          typename LoopifyShadowFromReference::lst::Cons(_read, nullptr));
      *_write = std::move(_cell);
      _write =
          &std::get<typename LoopifyShadowFromReference::lst::Cons>(
              (*_write)->v_mut())
              .a1;
      _own = std::move(_rs.next);
      _loop_l = _own.get();
      continue;
    }
  }
  return std::move(*_head);
}

LoopifyShadowFromReference::lst LoopifyShadowFromReference::upto(uint64_t n) {
  // Builds the result front to back: _write points at the empty tail the next
  // cell fills.
  std::optional<LoopifyShadowFromReference::lst> _root{};
  crane::rc<LoopifyShadowFromReference::lst> *_write = nullptr;
  while (true) {
    if (n <= 0) {
      auto _value = lst::nil();
      (_write ? *(*_write = crane::make_rc<LoopifyShadowFromReference::lst>(
                      std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      uint64_t k = n - 1;
      auto _cell = typename LoopifyShadowFromReference::lst::Cons(n, nullptr);
      LoopifyShadowFromReference::lst &_node =
          (_write ? *(*_write = crane::make_rc<LoopifyShadowFromReference::lst>(
                          std::move(_cell)))
                  : _root.emplace(std::move(_cell)));
      _write =
          &std::get<typename LoopifyShadowFromReference::lst::Cons>(
              _node.v_mut())
              .a1;
      n = k;
      continue;
    }
  }
  return std::move(*_root);
}
