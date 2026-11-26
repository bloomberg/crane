#include "loopify_accumulator_read_elsewhere.h"

/// A tail loop moves a parameter into its own next value only where that
/// value reads it for the last time in the turn
/// (Ownership_ir.continue_moves).
uint64_t LoopifyAccumulatorReadElsewhere::size(
    const LoopifyAccumulatorReadElsewhere::tree &t) {
  // Explicit stack replaces the non-tail recursion of size: _call frames are
  // pending calls, _after frames resume a caller.
  struct _call {
    const LoopifyAccumulatorReadElsewhere::tree *t;
  };

  struct _after_size_in_Node {
    const LoopifyAccumulatorReadElsewhere::tree *a2;
  };

  struct _after_size_in_Node_2 {
    uint64_t _tmp2;
  };

  using _frame =
      std::variant<_call, _after_size_in_Node, _after_size_in_Node_2>;
  uint64_t _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&t});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const LoopifyAccumulatorReadElsewhere::tree &t = *_f.t;
      if (std::holds_alternative<
              typename LoopifyAccumulatorReadElsewhere::tree::Leaf>(t.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, _, a2] =
            std::get<typename LoopifyAccumulatorReadElsewhere::tree::Node>(
                t.v());
        _stack.emplace_back(_after_size_in_Node{crane_raw(a2)});
        _stack.emplace_back(_call{crane_raw(a0)});
      }
    } else if (std::holds_alternative<_after_size_in_Node>(_popped)) {
      auto _f = std::move(std::get<_after_size_in_Node>(_popped));
      _stack.pop_back();
      const LoopifyAccumulatorReadElsewhere::tree &a2 = *_f.a2;
      _stack.emplace_back(_after_size_in_Node_2{_result});
      _stack.emplace_back(_call{&a2});
    } else {
      auto _f = std::move(std::get<_after_size_in_Node_2>(_popped));
      _stack.pop_back();
      _result = ((_f._tmp2 + UINT64_C(1)) + _result);
    }
  }
  return _result;
}

uint64_t LoopifyAccumulatorReadElsewhere::keys(
    const LoopifyAccumulatorReadElsewhere::tree &t) {
  // Explicit stack replaces the non-tail recursion of keys: _call frames are
  // pending calls, _after frames resume a caller.
  struct _call {
    const LoopifyAccumulatorReadElsewhere::tree *t;
  };

  struct _after_keys_in_Node {
    uint64_t a1;
    const LoopifyAccumulatorReadElsewhere::tree *a2;
  };

  struct _after_keys_in_Node_2 {
    uint64_t a1;
    uint64_t _tmp2;
  };

  using _frame =
      std::variant<_call, _after_keys_in_Node, _after_keys_in_Node_2>;
  uint64_t _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&t});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const LoopifyAccumulatorReadElsewhere::tree &t = *_f.t;
      if (std::holds_alternative<
              typename LoopifyAccumulatorReadElsewhere::tree::Leaf>(t.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1, a2] =
            std::get<typename LoopifyAccumulatorReadElsewhere::tree::Node>(
                t.v());
        _stack.emplace_back(_after_keys_in_Node{a1, crane_raw(a2)});
        _stack.emplace_back(_call{crane_raw(a0)});
      }
    } else if (std::holds_alternative<_after_keys_in_Node>(_popped)) {
      auto _f = std::move(std::get<_after_keys_in_Node>(_popped));
      _stack.pop_back();
      uint64_t a1 = _f.a1;
      const LoopifyAccumulatorReadElsewhere::tree &a2 = *_f.a2;
      _stack.emplace_back(_after_keys_in_Node_2{a1, _result});
      _stack.emplace_back(_call{&a2});
    } else {
      auto _f = std::move(std::get<_after_keys_in_Node_2>(_popped));
      _stack.pop_back();
      uint64_t a1 = _f.a1;
      _result = ((_f._tmp2 + a1) + _result);
    }
  }
  return _result;
}

/// Rebuilt around itself in a turn under a match on a nat, which is spelled
/// as an if: the one read is the turn's last, and is moved.
LoopifyAccumulatorReadElsewhere::tree LoopifyAccumulatorReadElsewhere::grow(
    uint64_t n, LoopifyAccumulatorReadElsewhere::tree acc) {
  // Loop replaces the tail recursion: each recursive call updates the loop
  // variables.
  LoopifyAccumulatorReadElsewhere::tree _loop_acc = std::move(acc);
  while (true) {
    if (n <= 0) {
      return _loop_acc;
    } else {
      uint64_t m = n - 1;
      _loop_acc = tree::node(std::move(_loop_acc), m, tree::leaf());
      n = m;
    }
  }
}

/// Read twice by its own next value and once more by the count's: no read
/// is the turn's last, and none is moved.
std::pair<uint64_t, LoopifyAccumulatorReadElsewhere::tree>
LoopifyAccumulatorReadElsewhere::grow_counted(
    uint64_t n, const LoopifyAccumulatorReadElsewhere::tree &acc,
    uint64_t count) {
  // Loop replaces the tail recursion: each recursive call updates the loop
  // variables.
  LoopifyAccumulatorReadElsewhere::tree _loop_acc = acc;
  while (true) {
    if (n <= 0) {
      return std::make_pair(count, _loop_acc);
    } else {
      uint64_t m = n - 1;
      LoopifyAccumulatorReadElsewhere::tree _next_acc =
          tree::node(_loop_acc, m, _loop_acc);
      count = (count + size(_loop_acc));
      n = m;
      _loop_acc = std::move(_next_acc);
    }
  }
}

/// Rebuilt around itself in a turn under a match on another parameter,
/// whose parts the same next value reads.
LoopifyAccumulatorReadElsewhere::tree LoopifyAccumulatorReadElsewhere::graft(
    const LoopifyAccumulatorReadElsewhere::tree &t,
    LoopifyAccumulatorReadElsewhere::tree acc) {
  // Loop replaces the tail recursion: each recursive call updates the loop
  // variables.
  LoopifyAccumulatorReadElsewhere::tree _loop_acc = std::move(acc);
  const LoopifyAccumulatorReadElsewhere::tree *_loop_t = &t;
  while (true) {
    if (std::holds_alternative<
            typename LoopifyAccumulatorReadElsewhere::tree::Leaf>(_loop_t->v())) {
      return _loop_acc;
    } else {
      const auto &[a0, a1, a2] =
          std::get<typename LoopifyAccumulatorReadElsewhere::tree::Node>(
              _loop_t->v());
      _loop_acc = tree::node(std::move(_loop_acc), a1, crane::shared_child(a0));
      _loop_t = crane_raw(a2);
    }
  }
}
