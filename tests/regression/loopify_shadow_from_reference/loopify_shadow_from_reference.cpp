#include "loopify_shadow_from_reference.h"

uint64_t LoopifyShadowFromReference::suml(
    const LoopifyShadowFromReference::lst
        &l) { /// CraneEnter: captures varying parameters for each recursive
              /// call.

  struct CraneEnter {
    const LoopifyShadowFromReference::lst *l;
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
  /// Loopified suml: CraneEnter -> CraneCont_Cons.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      const LoopifyShadowFromReference::lst &l = *_f.l;
      if (std::holds_alternative<typename LoopifyShadowFromReference::lst::Nil>(
              l.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] =
            std::get<typename LoopifyShadowFromReference::lst::Cons>(l.v());
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

LoopifyShadowFromReference::lst
LoopifyShadowFromReference::g(LoopifyShadowFromReference::lst l) {
  crane::rc<LoopifyShadowFromReference::lst> _head{};
  crane::rc<LoopifyShadowFromReference::lst> *_write = &_head;
  const LoopifyShadowFromReference::lst *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<typename LoopifyShadowFromReference::lst::Nil>(
            _loop_l->v())) {
      *_write = crane::make_rc<LoopifyShadowFromReference::lst>(lst::nil());
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename LoopifyShadowFromReference::lst::Cons>(
              _loop_l->v());
      const LoopifyShadowFromReference::lst &a1_value = *a1;
      auto _cell = crane::make_rc<LoopifyShadowFromReference::lst>(
          typename LoopifyShadowFromReference::lst::Cons(
              twice([=](uint64_t y) { return suml(lst::cons(y, a1_value)); },
                    a0),
              nullptr));
      *_write = std::move(_cell);
      _write = &std::get<typename LoopifyShadowFromReference::lst::Cons>(
                    (*_write)->v_mut())
                    .a1;
      _loop_l = &a1_value;
      continue;
    }
  }
  return std::move(*_head);
}

LoopifyShadowFromReference::lst LoopifyShadowFromReference::upto(uint64_t n) {
  crane::rc<LoopifyShadowFromReference::lst> _head{};
  crane::rc<LoopifyShadowFromReference::lst> *_write = &_head;
  uint64_t _loop_n = n;
  while (true) {
    if (_loop_n <= 0) {
      *_write = crane::make_rc<LoopifyShadowFromReference::lst>(lst::nil());
      break;
    } else {
      uint64_t k = _loop_n - 1;
      auto _cell = crane::make_rc<LoopifyShadowFromReference::lst>(
          typename LoopifyShadowFromReference::lst::Cons(_loop_n, nullptr));
      *_write = std::move(_cell);
      _write = &std::get<typename LoopifyShadowFromReference::lst::Cons>(
                    (*_write)->v_mut())
                    .a1;
      _loop_n = k;
      continue;
    }
  }
  return std::move(*_head);
}
