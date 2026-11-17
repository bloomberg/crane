#include "reuse_loopified_helper.h"

/// Rebuilds the root's constructor: a candidate for reuse.
ReuseLoopifiedHelper::tree
ReuseLoopifiedHelper::bump_root(ReuseLoopifiedHelper::tree t) {
  // Reuse the matched cell in place when this is its only owner; otherwise
  // rebuild.
  if (t.v().index() == 1) {
    if (t.v().unique()) {
      ReuseLoopifiedHelper::tree l = std::move(
          *crane::get<typename ReuseLoopifiedHelper::tree::Node>(t.v_mut()).a0);
      uint64_t k = std::move(
          crane::get<typename ReuseLoopifiedHelper::tree::Node>(t.v_mut()).a1);
      ReuseLoopifiedHelper::tree r = std::move(
          *crane::get<typename ReuseLoopifiedHelper::tree::Node>(t.v_mut()).a2);
      return tree::node_crane_reuse(std::move(t), std::move(l),
                                    (std::move(k) + 1), std::move(r));
    } else {
      if (crane::holds_alternative<typename ReuseLoopifiedHelper::tree::Leaf>(
              t.v())) {
        return tree::leaf();
      } else {
        const auto &[a0, a1, a2] =
            crane::get<typename ReuseLoopifiedHelper::tree::Node>(t.v());
        return tree::node(*a0, (a1 + 1), *a2);
      }
    }
  } else {
    if (crane::holds_alternative<typename ReuseLoopifiedHelper::tree::Leaf>(
            t.v())) {
      return tree::leaf();
    } else {
      const auto &[a0, a1, a2] =
          crane::get<typename ReuseLoopifiedHelper::tree::Node>(t.v());
      return tree::node(*a0, (a1 + 1), *a2);
    }
  }
}

ReuseLoopifiedHelper::tree
ReuseLoopifiedHelper::insert(uint64_t x, const ReuseLoopifiedHelper::tree &t) {
  // Explicit stack replaces the non-tail recursion of insert: _call frames are
  // pending calls, _after frames resume a caller.
  struct _call {
    const ReuseLoopifiedHelper::tree *t;
  };

  struct _after_insert_in_true {
    uint64_t a1;
    crane::shared_box<ReuseLoopifiedHelper::tree> a2;
  };

  struct _after_insert_in_true_2 {
    crane::shared_box<ReuseLoopifiedHelper::tree> a0;
    uint64_t a1;
  };

  using _frame =
      std::variant<_call, _after_insert_in_true, _after_insert_in_true_2>;
  ReuseLoopifiedHelper::tree _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&t});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (crane::holds_alternative<_call>(_popped)) {
      auto _f = std::move(crane::get<_call>(_popped));
      _stack.pop_back();
      const ReuseLoopifiedHelper::tree &t = *_f.t;
      if (crane::holds_alternative<typename ReuseLoopifiedHelper::tree::Leaf>(
              t.v())) {
        _result = tree::node(tree::leaf(), x, tree::leaf());
      } else {
        const auto &[a0, a1, a2] =
            crane::get<typename ReuseLoopifiedHelper::tree::Node>(t.v());
        if (x < a1) {
          _stack.emplace_back(_after_insert_in_true{a1, a2});
          _stack.emplace_back(_call{crane_raw(a0)});
        } else {
          if (a1 < x) {
            _stack.emplace_back(_after_insert_in_true_2{a0, a1});
            _stack.emplace_back(_call{crane_raw(a2)});
          } else {
            _result = std::move(t);
          }
        }
      }
    } else if (crane::holds_alternative<_after_insert_in_true>(_popped)) {
      auto _f = std::move(crane::get<_after_insert_in_true>(_popped));
      _stack.pop_back();
      uint64_t a1 = _f.a1;
      crane::shared_box<ReuseLoopifiedHelper::tree> a2 = std::move(_f.a2);
      _result = tree::node(std::move(_result), a1, *a2);
    } else {
      auto _f = std::move(crane::get<_after_insert_in_true_2>(_popped));
      _stack.pop_back();
      crane::shared_box<ReuseLoopifiedHelper::tree> a0 = std::move(_f.a0);
      uint64_t a1 = _f.a1;
      _result = tree::node(*a0, a1, std::move(_result));
    }
  }
  return _result;
}

uint64_t ReuseLoopifiedHelper::sum(const ReuseLoopifiedHelper::tree &t) {
  // Explicit stack replaces the non-tail recursion of sum: _call frames are
  // pending calls, _after frames resume a caller.
  struct _call {
    const ReuseLoopifiedHelper::tree *t;
  };

  struct _after_sum_in_Node {
    uint64_t a1;
    const ReuseLoopifiedHelper::tree *a2;
  };

  struct _after_sum_in_Node_2 {
    uint64_t a1;
    uint64_t _tmp2;
  };

  using _frame = std::variant<_call, _after_sum_in_Node, _after_sum_in_Node_2>;
  uint64_t _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&t});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (crane::holds_alternative<_call>(_popped)) {
      auto _f = std::move(crane::get<_call>(_popped));
      _stack.pop_back();
      const ReuseLoopifiedHelper::tree &t = *_f.t;
      if (crane::holds_alternative<typename ReuseLoopifiedHelper::tree::Leaf>(
              t.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1, a2] =
            crane::get<typename ReuseLoopifiedHelper::tree::Node>(t.v());
        _stack.emplace_back(_after_sum_in_Node{a1, crane_raw(a2)});
        _stack.emplace_back(_call{crane_raw(a0)});
      }
    } else if (crane::holds_alternative<_after_sum_in_Node>(_popped)) {
      auto _f = std::move(crane::get<_after_sum_in_Node>(_popped));
      _stack.pop_back();
      uint64_t a1 = _f.a1;
      const ReuseLoopifiedHelper::tree &a2 = *_f.a2;
      _stack.emplace_back(_after_sum_in_Node_2{a1, std::move(_result)});
      _stack.emplace_back(_call{&a2});
    } else {
      auto _f = std::move(crane::get<_after_sum_in_Node_2>(_popped));
      _stack.pop_back();
      uint64_t a1 = _f.a1;
      _result = ((_f._tmp2 + a1) + std::move(_result));
    }
  }
  return _result;
}
