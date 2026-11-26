#include "loopify_moves_captured_closure.h"

uint64_t
LoopifyMovesCapturedClosure::sumw(uint64_t w,
                                  const LoopifyMovesCapturedClosure::tree &t) {
  crane::fn<uint64_t(uint64_t)> weigh = [=](uint64_t x) { return (x * w); };

  // Explicit stack replaces the non-tail recursion of go: _call frames are
  // pending calls, _after frames resume a caller.
  struct _call {
    const LoopifyMovesCapturedClosure::tree *t0;
  };

  struct _after_go_in_Node {
    uint64_t a1;
    const LoopifyMovesCapturedClosure::tree *a2;
  };

  struct _after_go_in_Node_2 {
    uint64_t a1;
    uint64_t _tmp2;
  };

  using _frame = std::variant<_call, _after_go_in_Node, _after_go_in_Node_2>;
  uint64_t _lc1_result{};
  crane::small_vector<_frame> _lc1_stack;
  _lc1_stack.emplace_back(_call{&t});
  while (!_lc1_stack.empty()) {
    _frame &_popped = _lc1_stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _lc1_stack.pop_back();
      const LoopifyMovesCapturedClosure::tree &t = *_f.t0;
      if (std::holds_alternative<
              typename LoopifyMovesCapturedClosure::tree::Leaf>(t.v())) {
        _lc1_result = UINT64_C(0);
      } else {
        const auto &[a0, a1, a2] =
            std::get<typename LoopifyMovesCapturedClosure::tree::Node>(t.v());
        _lc1_stack.emplace_back(_after_go_in_Node{a1, crane_raw(a2)});
        _lc1_stack.emplace_back(_call{crane_raw(a0)});
      }
    } else if (std::holds_alternative<_after_go_in_Node>(_popped)) {
      auto _f = std::move(std::get<_after_go_in_Node>(_popped));
      _lc1_stack.pop_back();
      uint64_t a1 = _f.a1;
      const LoopifyMovesCapturedClosure::tree &a2 = *_f.a2;
      _lc1_stack.emplace_back(_after_go_in_Node_2{a1, _lc1_result});
      _lc1_stack.emplace_back(_call{&a2});
    } else {
      auto _f = std::move(std::get<_after_go_in_Node_2>(_popped));
      _lc1_stack.pop_back();
      uint64_t a1 = _f.a1;
      _lc1_result = ((_f._tmp2 + weigh(a1)) + _lc1_result);
    }
  }
  return _lc1_result;
}

uint64_t LoopifyMovesCapturedClosure::sumw_list(uint64_t w,
                                                const List<uint64_t> &l) {
  crane::fn<uint64_t(uint64_t)> weigh = [=](uint64_t x) { return (x * w); };

  // Explicit stack replaces the non-tail recursion of go: _call frames are
  // pending calls, _after frames resume a caller.
  struct _call {
    const List<uint64_t> *l0;
  };

  struct _after_go_in_Cons {
    uint64_t a0;
  };

  using _frame = std::variant<_call, _after_go_in_Cons>;
  uint64_t _lc1_result{};
  crane::small_vector<_frame> _lc1_stack;
  _lc1_stack.emplace_back(_call{&l});
  while (!_lc1_stack.empty()) {
    _frame &_popped = _lc1_stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _lc1_stack.pop_back();
      const List<uint64_t> &l = *_f.l0;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
        _lc1_result = UINT64_C(0);
      } else {
        const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
        _lc1_stack.emplace_back(_after_go_in_Cons{a0});
        _lc1_stack.emplace_back(_call{crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<_after_go_in_Cons>(_popped));
      _lc1_stack.pop_back();
      uint64_t a0 = _f.a0;
      _lc1_result = (weigh(a0) + _lc1_result);
    }
  }
  return _lc1_result;
}

uint64_t LoopifyMovesCapturedClosure::sumw_acc(uint64_t w,
                                               const List<uint64_t> &l) {
  crane::fn<uint64_t(uint64_t)> weigh = [=](uint64_t x) { return (x * w); };
  uint64_t _lc1_acc = UINT64_C(0);
  // Loop replaces the tail recursion: each recursive call updates the loop
  // variables.
  uint64_t _lc1_loop_acc = _lc1_acc;
  const List<uint64_t> *_lc1_loop_l0 = &l;
  while (true) {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(_lc1_loop_l0->v())) {
      return _lc1_loop_acc;
    } else {
      const auto &[a0, a1] =
          std::get<typename List<uint64_t>::Cons>(_lc1_loop_l0->v());
      _lc1_loop_acc = (_lc1_loop_acc + weigh(a0));
      _lc1_loop_l0 = crane_raw(a1);
    }
  }
}
