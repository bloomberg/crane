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
    std::decay_t<decltype(UINT64_C(0))> _s1;
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
      _result = ((std::move(_result) + _f.a1) + std::move(_f._result));
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
    std::decay_t<decltype(UINT64_C(0))> _s2;
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
      _result = ((std::move(_result) + _f._s1) + std::move(_f._result));
    }
  }
  return _result;
}

/// TEST 3: Deep tree traversal — more iterations, more frames.
MemSafetyProbe8::tree MemSafetyProbe8::make_left_spine(
    uint64_t
        n) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    uint64_t n;
  };

  /// _Resume_n_: saves [_s0, n], resumes after recursive call with _result.
  struct _Resume_n_ {
    std::decay_t<decltype(tree::leaf())> _s0;
    uint64_t n;
  };

  using _Frame = std::variant<_Enter, _Resume_n_>;
  MemSafetyProbe8::tree _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{n});
  /// Loopified make_left_spine: _Enter -> _Resume_n_.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      uint64_t n = _f.n;
      if (n <= 0) {
        _result = tree::leaf();
      } else {
        uint64_t n_ = n - 1;
        _stack.emplace_back(_Resume_n_{tree::leaf(), n});
        _stack.emplace_back(_Enter{n_});
      }
    } else {
      auto _f = std::move(std::get<_Resume_n_>(_frame));
      _result = tree::node(_result, _f.n, _f._s0);
    }
  }
  return _result;
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
  std::vector<_Frame> _stack;
  _stack.reserve(8);
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
        _stack.emplace_back(_Cont_Node{a1, a2.get()});
        _stack.emplace_back(_Enter{a0.get(), UINT64_C(0)});
      }
    } else if (std::holds_alternative<_Cont_Node>(_frame)) {
      auto _f = std::move(std::get<_Cont_Node>(_frame));
      uint64_t a1 = _f.a1;
      const MemSafetyProbe8::tree &a2 = *_f.a2;
      uint64_t left = _result;
      _stack.emplace_back(_Cont_Node_1{a1, left});
      _stack.emplace_back(_Enter{&a2, UINT64_C(0)});
    } else {
      auto _f = std::move(std::get<_Cont_Node_1>(_frame));
      uint64_t a1 = _f.a1;
      uint64_t left = _f.left;
      uint64_t right = _result;
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

  /// _After_Node: saves [a0, _s1, a1], dispatches next recursive call.
  struct _After_Node {
    const MemSafetyProbe8::tree *a0;
    std::decay_t<decltype(UINT64_C(0))> _s1;
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
      _result = ((std::move(_result) * _f.a1) * std::move(_f._result));
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
