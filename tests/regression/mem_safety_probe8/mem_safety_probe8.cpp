#include "mem_safety_probe8.h"

/// TEST 1: Non-method tree traversal with double recursion.
/// dummy ensures tree is NOT the first arg (avoiding methodification).
/// tree is the second arg — should be owned if it doesn't escape.
uint64_t MemSafetyProbe8::tree_sum_ext(
    uint64_t _x,
    const MemSafetyProbe8::tree
        &t) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const MemSafetyProbe8::tree *t;
    uint64_t _x;
  };

  /// _After_Node: saves [a0, _s1, a1], dispatches next recursive call.
  struct _After_Node {
    const MemSafetyProbe8::tree *a0;
    decltype(UINT64_C(0)) _s1;
    uint64_t a1;
  };

  /// _Combine_Node: receives partial results, combines with _result from final
  /// call.
  struct _Combine_Node {
    uint64_t _result;
    uint64_t a1;
  };

  using _Frame = std::variant<_Enter, _After_Node, _Combine_Node>;
  uint64_t _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&t, _x});
  /// Loopified tree_sum_ext: _Enter -> _After_Node -> _Combine_Node.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const MemSafetyProbe8::tree &t = *_f.t;
      uint64_t _x = _f._x;
      if (std::holds_alternative<typename MemSafetyProbe8::tree::Leaf>(t.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1, a2] =
            std::get<typename MemSafetyProbe8::tree::Node>(t.v());
        _stack.emplace_back(_After_Node{a0.get(), UINT64_C(0), a1});
        _stack.emplace_back(_Enter{a2.get(), UINT64_C(0)});
      }
    } else if (std::holds_alternative<_After_Node>(_frame)) {
      auto _f = std::move(std::get<_After_Node>(_frame));
      _stack.emplace_back(_Combine_Node{_result, _f.a1});
      _stack.emplace_back(_Enter{_f.a0, _f._s1});
    } else {
      auto _f = std::move(std::get<_Combine_Node>(_frame));
      _result = ((_result + _f.a1) + _f._result);
    }
  }
  return _result;
}

/// TEST 2: Same but with a more complex computation to prevent
/// the optimizer from simplifying.
uint64_t MemSafetyProbe8::tree_weighted(
    uint64_t _x, const MemSafetyProbe8::tree &t,
    uint64_t depth) { /// _Enter: captures varying parameters for each recursive
                      /// call.

  struct _Enter {
    uint64_t depth;
    const MemSafetyProbe8::tree *t;
    uint64_t _x;
  };

  /// _After_Node: saves [_s0, a0, _s2, _s3], dispatches next recursive call.
  struct _After_Node {
    uint64_t _s0;
    const MemSafetyProbe8::tree *a0;
    decltype(UINT64_C(0)) _s2;
    uint64_t _s3;
  };

  /// _Combine_Node: receives partial results, combines with _result from final
  /// call.
  struct _Combine_Node {
    uint64_t _result;
    uint64_t _s1;
  };

  using _Frame = std::variant<_Enter, _After_Node, _Combine_Node>;
  uint64_t _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{depth, &t, _x});
  /// Loopified tree_weighted: _Enter -> _After_Node -> _Combine_Node.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      uint64_t depth = _f.depth;
      const MemSafetyProbe8::tree &t = *_f.t;
      uint64_t _x = _f._x;
      if (std::holds_alternative<typename MemSafetyProbe8::tree::Leaf>(t.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1, a2] =
            std::get<typename MemSafetyProbe8::tree::Node>(t.v());
        _stack.emplace_back(_After_Node{(UINT64_C(1) + depth), a0.get(),
                                        UINT64_C(0), (a1 * depth)});
        _stack.emplace_back(
            _Enter{(UINT64_C(1) + depth), a2.get(), UINT64_C(0)});
      }
    } else if (std::holds_alternative<_After_Node>(_frame)) {
      auto _f = std::move(std::get<_After_Node>(_frame));
      _stack.emplace_back(_Combine_Node{_result, _f._s3});
      _stack.emplace_back(_Enter{_f._s0, _f.a0, _f._s2});
    } else {
      auto _f = std::move(std::get<_Combine_Node>(_frame));
      _result = ((_result + _f._s1) + _f._result);
    }
  }
  return _result;
}

/// TEST 3: Deep tree traversal — more iterations, more frames.
MemSafetyProbe8::tree MemSafetyProbe8::make_left_spine(uint64_t n) {
  std::unique_ptr<MemSafetyProbe8::tree> _head{};
  std::unique_ptr<MemSafetyProbe8::tree> *_write = &_head;
  uint64_t _loop_n = std::move(n);
  while (true) {
    if (_loop_n <= 0) {
      *_write = std::make_unique<MemSafetyProbe8::tree>(tree::leaf());
      break;
    } else {
      uint64_t n_ = _loop_n - 1;
      auto _cell = std::make_unique<MemSafetyProbe8::tree>(typename tree::Node(
          nullptr, _loop_n,
          std::make_unique<MemSafetyProbe8::tree>(tree::leaf())));
      *_write = std::move(_cell);
      _write = &std::get<typename tree::Node>((*_write)->v_mut()).a0;
      _loop_n = n_;
      continue;
    }
  }
  return std::move(*_head);
}

/// TEST 4: Tree traversal where both recursive calls use
/// different subtrees — _After frame must hold one while
/// processing the other.
uint64_t MemSafetyProbe8::tree_collect(uint64_t,
                                       const MemSafetyProbe8::tree &t) {
  if (std::holds_alternative<typename MemSafetyProbe8::tree::Leaf>(t.v())) {
    return UINT64_C(0);
  } else {
    const auto &[a0, a1, a2] =
        std::get<typename MemSafetyProbe8::tree::Node>(t.v());
    uint64_t left = tree_collect(UINT64_C(0), *a0);
    uint64_t right = tree_collect(UINT64_C(0), *a2);
    return ((left + a1) + right);
  }
}

/// TEST 5: Tree function where the tree is consumed (not
/// used after recursive calls) — maximally owned.
uint64_t MemSafetyProbe8::tree_flatten(
    uint64_t _x,
    const MemSafetyProbe8::tree
        &t) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const MemSafetyProbe8::tree *t;
    uint64_t _x;
  };

  /// _After_Node: saves [a0, _s1, a1], dispatches next recursive call.
  struct _After_Node {
    const MemSafetyProbe8::tree *a0;
    decltype(UINT64_C(0)) _s1;
    uint64_t a1;
  };

  /// _Combine_Node: receives partial results, combines with _result from final
  /// call.
  struct _Combine_Node {
    uint64_t _result;
    uint64_t a1;
  };

  using _Frame = std::variant<_Enter, _After_Node, _Combine_Node>;
  uint64_t _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&t, _x});
  /// Loopified tree_flatten: _Enter -> _After_Node -> _Combine_Node.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const MemSafetyProbe8::tree &t = *_f.t;
      uint64_t _x = _f._x;
      if (std::holds_alternative<typename MemSafetyProbe8::tree::Leaf>(t.v())) {
        _result = UINT64_C(1);
      } else {
        const auto &[a0, a1, a2] =
            std::get<typename MemSafetyProbe8::tree::Node>(t.v());
        _stack.emplace_back(_After_Node{a0.get(), UINT64_C(0), a1});
        _stack.emplace_back(_Enter{a2.get(), UINT64_C(0)});
      }
    } else if (std::holds_alternative<_After_Node>(_frame)) {
      auto _f = std::move(std::get<_After_Node>(_frame));
      _stack.emplace_back(_Combine_Node{_result, _f.a1});
      _stack.emplace_back(_Enter{_f.a0, _f._s1});
    } else {
      auto _f = std::move(std::get<_Combine_Node>(_frame));
      _result = ((_result * _f.a1) * _f._result);
    }
  }
  return _result;
}

/// TEST 6: Pass tree as a higher-order function argument
/// to prevent methodification completely.
uint64_t MemSafetyProbe8::tree_size_via_fold(const MemSafetyProbe8::tree &t) {
  auto go_impl = [](auto &_self_go, uint64_t,
                    const MemSafetyProbe8::tree &t0) -> uint64_t {
    if (std::holds_alternative<typename MemSafetyProbe8::tree::Leaf>(t0.v())) {
      return UINT64_C(0);
    } else {
      const auto &[a0, a1, a2] =
          std::get<typename MemSafetyProbe8::tree::Node>(t0.v());
      return ((UINT64_C(1) + _self_go(_self_go, UINT64_C(0), *a0)) +
              _self_go(_self_go, UINT64_C(0), *a2));
    }
  };
  auto go = [&](uint64_t _x, const MemSafetyProbe8::tree &t0) -> uint64_t {
    return go_impl(go_impl, _x, t0);
  };
  return go(UINT64_C(0), t);
}
