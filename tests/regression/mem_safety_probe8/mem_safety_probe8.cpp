#include <mem_safety_probe8.h>

/// TEST 1: Non-method tree traversal with double recursion.
/// dummy ensures tree is NOT the first arg (avoiding methodification).
/// tree is the second arg — should be owned if it doesn't escape.
unsigned int MemSafetyProbe8::tree_sum_ext(
    const unsigned int _x,
    const MemSafetyProbe8::tree
        &t) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const MemSafetyProbe8::tree *t;
    unsigned int _x;
  };

  /// _After_Node: saves [d_a0, _s1, d_a1], dispatches next recursive call.
  struct _After_Node {
    const MemSafetyProbe8::tree *d_a0;
    decltype(0u) _s1;
    unsigned int d_a1;
  };

  /// _Combine_Node: receives partial results, combines with _result from final
  /// call.
  struct _Combine_Node {
    unsigned int _result;
    unsigned int d_a1;
  };

  using _Frame = std::variant<_Enter, _After_Node, _Combine_Node>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&t, _x});
  /// Loopified tree_sum_ext: _Enter -> _After_Node -> _Combine_Node.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const MemSafetyProbe8::tree &t = *(_f.t);
      const unsigned int _x = _f._x;
      if (std::holds_alternative<typename MemSafetyProbe8::tree::Leaf>(t.v())) {
        _result = 0u;
      } else {
        const auto &[d_a0, d_a1, d_a2] =
            std::get<typename MemSafetyProbe8::tree::Node>(t.v());
        _stack.emplace_back(_After_Node{d_a0.get(), 0u, d_a1});
        _stack.emplace_back(_Enter{d_a2.get(), 0u});
      }
    } else if (std::holds_alternative<_After_Node>(_frame)) {
      auto _f = std::move(std::get<_After_Node>(_frame));
      _stack.emplace_back(_Combine_Node{_result, _f.d_a1});
      _stack.emplace_back(_Enter{_f.d_a0, _f._s1});
    } else {
      auto _f = std::move(std::get<_Combine_Node>(_frame));
      _result = ((_result + _f.d_a1) + _f._result);
    }
  }
  return _result;
}

/// TEST 2: Same but with a more complex computation to prevent
/// the optimizer from simplifying.
unsigned int MemSafetyProbe8::tree_weighted(
    const unsigned int _x, const MemSafetyProbe8::tree &t,
    const unsigned int depth) { /// _Enter: captures varying parameters for each
                                /// recursive call.

  struct _Enter {
    unsigned int depth;
    const MemSafetyProbe8::tree *t;
    unsigned int _x;
  };

  /// _After_Node: saves [_s0, d_a0, _s2, _s3], dispatches next recursive call.
  struct _After_Node {
    unsigned int _s0;
    const MemSafetyProbe8::tree *d_a0;
    decltype(0u) _s2;
    unsigned int _s3;
  };

  /// _Combine_Node: receives partial results, combines with _result from final
  /// call.
  struct _Combine_Node {
    unsigned int _result;
    unsigned int _s1;
  };

  using _Frame = std::variant<_Enter, _After_Node, _Combine_Node>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{depth, &t, _x});
  /// Loopified tree_weighted: _Enter -> _After_Node -> _Combine_Node.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const unsigned int depth = _f.depth;
      const MemSafetyProbe8::tree &t = *(_f.t);
      const unsigned int _x = _f._x;
      if (std::holds_alternative<typename MemSafetyProbe8::tree::Leaf>(t.v())) {
        _result = 0u;
      } else {
        const auto &[d_a0, d_a1, d_a2] =
            std::get<typename MemSafetyProbe8::tree::Node>(t.v());
        _stack.emplace_back(
            _After_Node{(1u + depth), d_a0.get(), 0u, (d_a1 * depth)});
        _stack.emplace_back(_Enter{(1u + depth), d_a2.get(), 0u});
      }
    } else if (std::holds_alternative<_After_Node>(_frame)) {
      auto _f = std::move(std::get<_After_Node>(_frame));
      _stack.emplace_back(_Combine_Node{_result, _f._s3});
      _stack.emplace_back(_Enter{_f._s0, _f.d_a0, _f._s2});
    } else {
      auto _f = std::move(std::get<_Combine_Node>(_frame));
      _result = ((_result + _f._s1) + _f._result);
    }
  }
  return _result;
}

/// TEST 3: Deep tree traversal — more iterations, more frames.
MemSafetyProbe8::tree MemSafetyProbe8::make_left_spine(const unsigned int n) {
  std::unique_ptr<MemSafetyProbe8::tree> _head{};
  std::unique_ptr<MemSafetyProbe8::tree> *_write = &_head;
  unsigned int _loop_n = n;
  while (true) {
    if (_loop_n <= 0) {
      *(_write) = std::make_unique<MemSafetyProbe8::tree>(tree::leaf());
      break;
    } else {
      unsigned int n_ = _loop_n - 1;
      auto _cell = std::make_unique<MemSafetyProbe8::tree>(typename tree::Node(
          nullptr, _loop_n,
          std::make_unique<MemSafetyProbe8::tree>(tree::leaf())));
      *(_write) = std::move(_cell);
      _write = &std::get<typename tree::Node>((*_write)->v_mut()).d_a0;
      _loop_n = n_;
      continue;
    }
  }
  return std::move(*(_head));
}

/// TEST 4: Tree traversal where both recursive calls use
/// different subtrees — _After frame must hold one while
/// processing the other.
unsigned int MemSafetyProbe8::tree_collect(const unsigned int,
                                           const MemSafetyProbe8::tree &t) {
  if (std::holds_alternative<typename MemSafetyProbe8::tree::Leaf>(t.v())) {
    return 0u;
  } else {
    const auto &[d_a0, d_a1, d_a2] =
        std::get<typename MemSafetyProbe8::tree::Node>(t.v());
    unsigned int left = tree_collect(0u, *(d_a0));
    unsigned int right = tree_collect(0u, *(d_a2));
    return ((left + d_a1) + right);
  }
}

/// TEST 5: Tree function where the tree is consumed (not
/// used after recursive calls) — maximally owned.
unsigned int MemSafetyProbe8::tree_flatten(
    const unsigned int _x,
    const MemSafetyProbe8::tree
        &t) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const MemSafetyProbe8::tree *t;
    unsigned int _x;
  };

  /// _After_Node: saves [d_a0, _s1, d_a1], dispatches next recursive call.
  struct _After_Node {
    const MemSafetyProbe8::tree *d_a0;
    decltype(0u) _s1;
    unsigned int d_a1;
  };

  /// _Combine_Node: receives partial results, combines with _result from final
  /// call.
  struct _Combine_Node {
    unsigned int _result;
    unsigned int d_a1;
  };

  using _Frame = std::variant<_Enter, _After_Node, _Combine_Node>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&t, _x});
  /// Loopified tree_flatten: _Enter -> _After_Node -> _Combine_Node.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const MemSafetyProbe8::tree &t = *(_f.t);
      const unsigned int _x = _f._x;
      if (std::holds_alternative<typename MemSafetyProbe8::tree::Leaf>(t.v())) {
        _result = 1u;
      } else {
        const auto &[d_a0, d_a1, d_a2] =
            std::get<typename MemSafetyProbe8::tree::Node>(t.v());
        _stack.emplace_back(_After_Node{d_a0.get(), 0u, d_a1});
        _stack.emplace_back(_Enter{d_a2.get(), 0u});
      }
    } else if (std::holds_alternative<_After_Node>(_frame)) {
      auto _f = std::move(std::get<_After_Node>(_frame));
      _stack.emplace_back(_Combine_Node{_result, _f.d_a1});
      _stack.emplace_back(_Enter{_f.d_a0, _f._s1});
    } else {
      auto _f = std::move(std::get<_Combine_Node>(_frame));
      _result = ((_result * _f.d_a1) * _f._result);
    }
  }
  return _result;
}

/// TEST 6: Pass tree as a higher-order function argument
/// to prevent methodification completely.
unsigned int
MemSafetyProbe8::tree_size_via_fold(const MemSafetyProbe8::tree &t) {
  std::function<unsigned int(unsigned int, MemSafetyProbe8::tree)> go;
  go = [&](unsigned int _x, MemSafetyProbe8::tree t0) -> unsigned int {
    /// _Enter: captures varying parameters for each recursive call.
    struct _Enter {
      MemSafetyProbe8::tree t0;
      unsigned int _x;
    };
    /// _After_Node: saves [d_a0, _s1, _s2], dispatches next recursive call.
    struct _After_Node {
      MemSafetyProbe8::tree d_a0;
      decltype(0u) _s1;
      decltype(1u) _s2;
    };
    /// _Combine_Node: receives partial results, combines with _result from
    /// final call.
    struct _Combine_Node {
      unsigned int _result;
      decltype(1u) _s1;
    };
    using _Frame = std::variant<_Enter, _After_Node, _Combine_Node>;
    unsigned int _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{t0, _x});
    /// Loopified go: _Enter -> _After_Node -> _Combine_Node.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        MemSafetyProbe8::tree t0 = std::move(_f.t0);
        unsigned int _x = _f._x;
        if (std::holds_alternative<typename MemSafetyProbe8::tree::Leaf>(
                t0.v_mut())) {
          _result = 0u;
        } else {
          auto &[d_a0, d_a1, d_a2] =
              std::get<typename MemSafetyProbe8::tree::Node>(t0.v_mut());
          _stack.emplace_back(_After_Node{*(d_a0), 0u, 1u});
          _stack.emplace_back(_Enter{std::move(*(d_a2)), 0u});
        }
      } else if (std::holds_alternative<_After_Node>(_frame)) {
        auto _f = std::move(std::get<_After_Node>(_frame));
        _stack.emplace_back(_Combine_Node{_result, _f._s2});
        _stack.emplace_back(_Enter{std::move(_f.d_a0), _f._s1});
      } else {
        auto _f = std::move(std::get<_Combine_Node>(_frame));
        _result = ((_f._s1 + _result) + _f._result);
      }
    }
    return _result;
  };
  return go(0u, t);
}
