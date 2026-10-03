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

  /// _Cont_Node: saves [a1, a2], resumes after recursive call, then processes
  /// rest.
  struct _Cont_Node {
    uint64_t a1;
    const MemSafetyProbe8::tree *a2;
  };

  /// _Cont_Node_1: saves [_tmp2, a1], resumes after recursive call, then
  /// processes rest.
  struct _Cont_Node_1 {
    uint64_t _tmp2;
    uint64_t a1;
  };

  using _Frame = std::variant<_Enter, _Cont_Node, _Cont_Node_1>;
  uint64_t _result{};
  crane::small_vector<_Frame> _stack;
  _stack.emplace_back(_Enter{&t, _x});
  /// Loopified tree_sum_ext: _Enter -> _Cont_Node -> _Cont_Node_1.
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
        _stack.emplace_back(_Cont_Node{a1, crane_raw(a2)});
        _stack.emplace_back(_Enter{crane_raw(a0), UINT64_C(0)});
      }
    } else if (std::holds_alternative<_Cont_Node>(_frame)) {
      auto _f = std::move(std::get<_Cont_Node>(_frame));
      uint64_t a1 = _f.a1;
      const MemSafetyProbe8::tree &a2 = *_f.a2;
      _stack.emplace_back(_Cont_Node_1{std::move(_result), a1});
      _stack.emplace_back(_Enter{&a2, UINT64_C(0)});
    } else {
      auto _f = std::move(std::get<_Cont_Node_1>(_frame));
      uint64_t a1 = _f.a1;
      _result = ((_f._tmp2 + a1) + std::move(_result));
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

  /// _Cont_Node: saves [a1, a2, depth], resumes after recursive call, then
  /// processes rest.
  struct _Cont_Node {
    uint64_t a1;
    const MemSafetyProbe8::tree *a2;
    uint64_t depth;
  };

  /// _Cont_Node_1: saves [_tmp2, a1, depth], resumes after recursive call, then
  /// processes rest.
  struct _Cont_Node_1 {
    uint64_t _tmp2;
    uint64_t a1;
    uint64_t depth;
  };

  using _Frame = std::variant<_Enter, _Cont_Node, _Cont_Node_1>;
  uint64_t _result{};
  crane::small_vector<_Frame> _stack;
  _stack.emplace_back(_Enter{depth, &t, _x});
  /// Loopified tree_weighted: _Enter -> _Cont_Node -> _Cont_Node_1.
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
        _stack.emplace_back(_Cont_Node{a1, crane_raw(a2), depth});
        _stack.emplace_back(
            _Enter{(UINT64_C(1) + depth), crane_raw(a0), UINT64_C(0)});
      }
    } else if (std::holds_alternative<_Cont_Node>(_frame)) {
      auto _f = std::move(std::get<_Cont_Node>(_frame));
      uint64_t a1 = _f.a1;
      const MemSafetyProbe8::tree &a2 = *_f.a2;
      uint64_t depth = _f.depth;
      _stack.emplace_back(_Cont_Node_1{std::move(_result), a1, depth});
      _stack.emplace_back(_Enter{(UINT64_C(1) + depth), &a2, UINT64_C(0)});
    } else {
      auto _f = std::move(std::get<_Cont_Node_1>(_frame));
      uint64_t a1 = _f.a1;
      uint64_t depth = _f.depth;
      _result = ((_f._tmp2 + (a1 * depth)) + std::move(_result));
    }
  }
  return _result;
}

/// TEST 3: Deep tree traversal — more iterations, more frames.
MemSafetyProbe8::tree MemSafetyProbe8::make_left_spine(uint64_t n) {
  std::shared_ptr<MemSafetyProbe8::tree> _head{};
  std::shared_ptr<MemSafetyProbe8::tree> *_write = &_head;
  uint64_t _loop_n = std::move(n);
  while (true) {
    if (_loop_n <= 0) {
      *_write = std::make_shared<MemSafetyProbe8::tree>(tree::leaf());
      break;
    } else {
      uint64_t n_ = _loop_n - 1;
      auto _cell = std::make_shared<MemSafetyProbe8::tree>(
          typename MemSafetyProbe8::tree::Node(
              nullptr, _loop_n,
              std::make_shared<MemSafetyProbe8::tree>(tree::leaf())));
      *_write = std::move(_cell);
      _write =
          &std::get<typename MemSafetyProbe8::tree::Node>((*_write)->v_mut())
               .a0;
      _loop_n = n_;
      continue;
    }
  }
  return std::move(*_head);
}

/// TEST 4: Tree traversal where both recursive calls use
/// different subtrees — _After frame must hold one while
/// processing the other.
uint64_t MemSafetyProbe8::tree_collect(
    uint64_t _x,
    const MemSafetyProbe8::tree
        &t) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const MemSafetyProbe8::tree *t;
    uint64_t _x;
  };

  /// _Cont_Node: saves [a1, a2], resumes after recursive call, then processes
  /// rest.
  struct _Cont_Node {
    uint64_t a1;
    const MemSafetyProbe8::tree *a2;
  };

  /// _Cont_Node_1: saves [a1, left], resumes after recursive call, then
  /// processes rest.
  struct _Cont_Node_1 {
    uint64_t a1;
    uint64_t left;
  };

  using _Frame = std::variant<_Enter, _Cont_Node, _Cont_Node_1>;
  uint64_t _result{};
  crane::small_vector<_Frame> _stack;
  _stack.emplace_back(_Enter{&t, _x});
  /// Loopified tree_collect: _Enter -> _Cont_Node -> _Cont_Node_1.
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
        _stack.emplace_back(_Cont_Node{a1, crane_raw(a2)});
        _stack.emplace_back(_Enter{crane_raw(a0), UINT64_C(0)});
      }
    } else if (std::holds_alternative<_Cont_Node>(_frame)) {
      auto _f = std::move(std::get<_Cont_Node>(_frame));
      uint64_t a1 = _f.a1;
      const MemSafetyProbe8::tree &a2 = *_f.a2;
      uint64_t left = std::move(_result);
      _stack.emplace_back(_Cont_Node_1{a1, left});
      _stack.emplace_back(_Enter{&a2, UINT64_C(0)});
    } else {
      auto _f = std::move(std::get<_Cont_Node_1>(_frame));
      uint64_t a1 = _f.a1;
      uint64_t left = _f.left;
      uint64_t right = std::move(_result);
      _result = ((left + a1) + right);
    }
  }
  return _result;
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

  /// _Cont_Node: saves [a1, a2], resumes after recursive call, then processes
  /// rest.
  struct _Cont_Node {
    uint64_t a1;
    const MemSafetyProbe8::tree *a2;
  };

  /// _Cont_Node_1: saves [_tmp2, a1], resumes after recursive call, then
  /// processes rest.
  struct _Cont_Node_1 {
    uint64_t _tmp2;
    uint64_t a1;
  };

  using _Frame = std::variant<_Enter, _Cont_Node, _Cont_Node_1>;
  uint64_t _result{};
  crane::small_vector<_Frame> _stack;
  _stack.emplace_back(_Enter{&t, _x});
  /// Loopified tree_flatten: _Enter -> _Cont_Node -> _Cont_Node_1.
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
        _stack.emplace_back(_Cont_Node{a1, crane_raw(a2)});
        _stack.emplace_back(_Enter{crane_raw(a0), UINT64_C(0)});
      }
    } else if (std::holds_alternative<_Cont_Node>(_frame)) {
      auto _f = std::move(std::get<_Cont_Node>(_frame));
      uint64_t a1 = _f.a1;
      const MemSafetyProbe8::tree &a2 = *_f.a2;
      _stack.emplace_back(_Cont_Node_1{std::move(_result), a1});
      _stack.emplace_back(_Enter{&a2, UINT64_C(0)});
    } else {
      auto _f = std::move(std::get<_Cont_Node_1>(_frame));
      uint64_t a1 = _f.a1;
      _result = ((_f._tmp2 * a1) * std::move(_result));
    }
  }
  return _result;
}

/// TEST 6: Pass tree as a higher-order function argument
/// to prevent methodification completely.
uint64_t MemSafetyProbe8::tree_size_via_fold(const MemSafetyProbe8::tree &t) {
  auto go_impl = [&](auto &, uint64_t _x,
                     const MemSafetyProbe8::tree &t0) -> uint64_t {
    /// _Enter: captures varying parameters for each recursive call.
    struct _Enter {
      const MemSafetyProbe8::tree *t0;
      uint64_t _x;
    };
    /// _Cont_Node: saves [a2], resumes after recursive call, then processes
    /// rest.
    struct _Cont_Node {
      const MemSafetyProbe8::tree *a2;
    };
    /// _Cont_Node_1: saves [_tmp2], resumes after recursive call, then
    /// processes rest.
    struct _Cont_Node_1 {
      uint64_t _tmp2;
    };
    using _Frame = std::variant<_Enter, _Cont_Node, _Cont_Node_1>;
    uint64_t _result{};
    crane::small_vector<_Frame> _stack;
    _stack.emplace_back(_Enter{&t0, _x});
    /// Loopified go: _Enter -> _Cont_Node -> _Cont_Node_1.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const MemSafetyProbe8::tree &t0 = *_f.t0;
        uint64_t _x = _f._x;
        if (std::holds_alternative<typename MemSafetyProbe8::tree::Leaf>(
                t0.v())) {
          _result = UINT64_C(0);
        } else {
          const auto &[a0, a1, a2] =
              std::get<typename MemSafetyProbe8::tree::Node>(t0.v());
          _stack.emplace_back(_Cont_Node{crane_raw(a2)});
          _stack.emplace_back(_Enter{crane_raw(a0), UINT64_C(0)});
        }
      } else if (std::holds_alternative<_Cont_Node>(_frame)) {
        auto _f = std::move(std::get<_Cont_Node>(_frame));
        const MemSafetyProbe8::tree &a2 = *_f.a2;
        _stack.emplace_back(_Cont_Node_1{std::move(_result)});
        _stack.emplace_back(_Enter{&a2, UINT64_C(0)});
      } else {
        auto _f = std::move(std::get<_Cont_Node_1>(_frame));
        _result = ((UINT64_C(1) + _f._tmp2) + std::move(_result));
      }
    }
    return _result;
  };
  auto go = [&](uint64_t _x, const MemSafetyProbe8::tree &t0) -> uint64_t {
    return go_impl(go_impl, _x, t0);
  };
  return go(UINT64_C(0), t);
}
