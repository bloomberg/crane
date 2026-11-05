#include "loopify_accumulator_read_elsewhere.h"

/// A tail loop moves a parameter into its own next value only where that
/// value reads it for the last time in the turn
/// (Ownership_plan.continue_moves).
uint64_t LoopifyAccumulatorReadElsewhere::size(
    const LoopifyAccumulatorReadElsewhere::tree
        &t) { /// CraneEnter: captures varying parameters for each recursive
              /// call.

  struct CraneEnter {
    const LoopifyAccumulatorReadElsewhere::tree *t;
  };

  /// CraneCont_Node: saves [a2], resumes after recursive call, then processes
  /// rest.
  struct CraneCont_Node {
    const LoopifyAccumulatorReadElsewhere::tree *a2;
  };

  /// CraneCont_Node_1: saves [_tmp2], resumes after recursive call, then
  /// processes rest.
  struct CraneCont_Node_1 {
    uint64_t _tmp2;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont_Node, CraneCont_Node_1>;
  uint64_t _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{&t});
  /// Loopified size: CraneEnter -> CraneCont_Node -> CraneCont_Node_1.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      const LoopifyAccumulatorReadElsewhere::tree &t = *_f.t;
      if (std::holds_alternative<
              typename LoopifyAccumulatorReadElsewhere::tree::Leaf>(t.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1, a2] =
            std::get<typename LoopifyAccumulatorReadElsewhere::tree::Node>(
                t.v());
        _stack.emplace_back(CraneCont_Node{crane_raw(a2)});
        _stack.emplace_back(CraneEnter{crane_raw(a0)});
      }
    } else if (std::holds_alternative<CraneCont_Node>(_frame)) {
      auto _f = std::move(std::get<CraneCont_Node>(_frame));
      const LoopifyAccumulatorReadElsewhere::tree &a2 = *_f.a2;
      _stack.emplace_back(CraneCont_Node_1{std::move(_result)});
      _stack.emplace_back(CraneEnter{&a2});
    } else {
      auto _f = std::move(std::get<CraneCont_Node_1>(_frame));
      _result = ((_f._tmp2 + UINT64_C(1)) + std::move(_result));
    }
  }
  return _result;
}

uint64_t LoopifyAccumulatorReadElsewhere::keys(
    const LoopifyAccumulatorReadElsewhere::tree
        &t) { /// CraneEnter: captures varying parameters for each recursive
              /// call.

  struct CraneEnter {
    const LoopifyAccumulatorReadElsewhere::tree *t;
  };

  /// CraneCont_Node: saves [a1, a2], resumes after recursive call, then
  /// processes rest.
  struct CraneCont_Node {
    uint64_t a1;
    const LoopifyAccumulatorReadElsewhere::tree *a2;
  };

  /// CraneCont_Node_1: saves [a1, _tmp2], resumes after recursive call, then
  /// processes rest.
  struct CraneCont_Node_1 {
    uint64_t a1;
    uint64_t _tmp2;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont_Node, CraneCont_Node_1>;
  uint64_t _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{&t});
  /// Loopified keys: CraneEnter -> CraneCont_Node -> CraneCont_Node_1.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      const LoopifyAccumulatorReadElsewhere::tree &t = *_f.t;
      if (std::holds_alternative<
              typename LoopifyAccumulatorReadElsewhere::tree::Leaf>(t.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1, a2] =
            std::get<typename LoopifyAccumulatorReadElsewhere::tree::Node>(
                t.v());
        _stack.emplace_back(CraneCont_Node{a1, crane_raw(a2)});
        _stack.emplace_back(CraneEnter{crane_raw(a0)});
      }
    } else if (std::holds_alternative<CraneCont_Node>(_frame)) {
      auto _f = std::move(std::get<CraneCont_Node>(_frame));
      uint64_t a1 = _f.a1;
      const LoopifyAccumulatorReadElsewhere::tree &a2 = *_f.a2;
      _stack.emplace_back(CraneCont_Node_1{a1, std::move(_result)});
      _stack.emplace_back(CraneEnter{&a2});
    } else {
      auto _f = std::move(std::get<CraneCont_Node_1>(_frame));
      uint64_t a1 = _f.a1;
      _result = ((_f._tmp2 + a1) + std::move(_result));
    }
  }
  return _result;
}

/// Rebuilt around itself in a turn under a match on a nat, which is spelled
/// as an if: the one read is the turn's last, and is moved.
LoopifyAccumulatorReadElsewhere::tree LoopifyAccumulatorReadElsewhere::grow(
    uint64_t n, LoopifyAccumulatorReadElsewhere::tree acc) {
  LoopifyAccumulatorReadElsewhere::tree _loop_acc = std::move(acc);
  uint64_t _loop_n = n;
  while (true) {
    if (_loop_n <= 0) {
      return _loop_acc;
    } else {
      uint64_t m = _loop_n - 1;
      _loop_acc = tree::node(std::move(_loop_acc), m, tree::leaf());
      _loop_n = m;
    }
  }
}

/// Read twice by its own next value and once more by the count's: no read
/// is the turn's last, and none is moved.
std::pair<uint64_t, LoopifyAccumulatorReadElsewhere::tree>
LoopifyAccumulatorReadElsewhere::grow_counted(
    uint64_t n, const LoopifyAccumulatorReadElsewhere::tree &acc,
    uint64_t count) {
  uint64_t _loop_count = count;
  LoopifyAccumulatorReadElsewhere::tree _loop_acc = acc;
  uint64_t _loop_n = n;
  while (true) {
    if (_loop_n <= 0) {
      return std::make_pair(_loop_count, _loop_acc);
    } else {
      uint64_t m = _loop_n - 1;
      LoopifyAccumulatorReadElsewhere::tree _next_acc =
          tree::node(_loop_acc, m, _loop_acc);
      _loop_count = (_loop_count + size(_loop_acc));
      _loop_n = m;
      _loop_acc = std::move(_next_acc);
    }
  }
}

/// Rebuilt around itself in a turn under a match on another parameter,
/// whose parts the same next value reads.
LoopifyAccumulatorReadElsewhere::tree LoopifyAccumulatorReadElsewhere::graft(
    const LoopifyAccumulatorReadElsewhere::tree &t,
    LoopifyAccumulatorReadElsewhere::tree acc) {
  LoopifyAccumulatorReadElsewhere::tree _loop_acc = std::move(acc);
  const LoopifyAccumulatorReadElsewhere::tree *_loop_t = &t;
  while (true) {
    if (std::holds_alternative<
            typename LoopifyAccumulatorReadElsewhere::tree::Leaf>(
            _loop_t->v())) {
      return _loop_acc;
    } else {
      const auto &[a0, a1, a2] =
          std::get<typename LoopifyAccumulatorReadElsewhere::tree::Node>(
              _loop_t->v());
      _loop_acc = tree::node(std::move(_loop_acc), a1, *a0);
      _loop_t = crane_raw(a2);
    }
  }
}
