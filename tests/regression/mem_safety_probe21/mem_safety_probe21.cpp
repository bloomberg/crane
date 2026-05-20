#include "mem_safety_probe21.h"

uint64_t MemSafetyProbe21::tree_sum(
    const MemSafetyProbe21::tree
        &t) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const MemSafetyProbe21::tree *t;
  };

  /// _After_Node: saves [a0, a1], dispatches next recursive call.
  struct _After_Node {
    const MemSafetyProbe21::tree *a0;
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
  _stack.emplace_back(_Enter{&t});
  /// Loopified tree_sum: _Enter -> _After_Node -> _Combine_Node.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const MemSafetyProbe21::tree &t = *_f.t;
      if (std::holds_alternative<typename MemSafetyProbe21::tree::Leaf>(
              t.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1, a2] =
            std::get<typename MemSafetyProbe21::tree::Node>(t.v());
        _stack.emplace_back(_After_Node{a0.get(), a1});
        _stack.emplace_back(_Enter{a2.get()});
      }
    } else if (std::holds_alternative<_After_Node>(_frame)) {
      auto _f = std::move(std::get<_After_Node>(_frame));
      _stack.emplace_back(_Combine_Node{_result, _f.a1});
      _stack.emplace_back(_Enter{_f.a0});
    } else {
      auto _f = std::move(std::get<_Combine_Node>(_frame));
      _result = ((std::move(_result) + _f.a1) + std::move(_f._result));
    }
  }
  return _result;
}

/// TEST 1: Tail-recursive function where the recursive call takes
/// a constructed tree. The loopifier must store the new tree
/// somewhere that outlives the iteration.
uint64_t MemSafetyProbe21::grow_and_sum(MemSafetyProbe21::tree t, uint64_t n) {
  uint64_t _loop_n = std::move(n);
  MemSafetyProbe21::tree _loop_t = std::move(t);
  while (true) {
    if (_loop_n <= 0) {
      return tree_sum(std::move(_loop_t));
    } else {
      uint64_t n_ = _loop_n - 1;
      uint64_t _next_n = n_;
      _loop_t = tree::node(std::move(_loop_t), _loop_n, tree::leaf());
      _loop_n = _next_n;
    }
  }
}

/// TEST 2: Non-tail recursive with constructed tree argument.
/// The recursive call creates a new tree AND uses the original.
uint64_t MemSafetyProbe21::double_grow(
    MemSafetyProbe21::tree t,
    uint64_t
        n) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    uint64_t n;
    MemSafetyProbe21::tree t;
  };

  /// _Resume_n_: saves [t], resumes after recursive call with _result.
  struct _Resume_n_ {
    decltype(tree_sum(std::declval<MemSafetyProbe21::tree &>())) t;
  };

  using _Frame = std::variant<_Enter, _Resume_n_>;
  uint64_t _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{n, t});
  /// Loopified double_grow: _Enter -> _Resume_n_.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      uint64_t n = _f.n;
      MemSafetyProbe21::tree t = std::move(_f.t);
      if (n <= 0) {
        _result = tree_sum(std::move(t));
      } else {
        uint64_t n_ = n - 1;
        _stack.emplace_back(_Resume_n_{tree_sum(t)});
        _stack.emplace_back(
            _Enter{n_, tree::node(t, UINT64_C(0), tree::leaf())});
      }
    } else {
      auto _f = std::move(std::get<_Resume_n_>(_frame));
      _result = (_f.t + _result);
    }
  }
  return _result;
}

/// TEST 3: Two recursive calls, one with original tree, one with
/// constructed tree.
uint64_t MemSafetyProbe21::branch_grow(
    const MemSafetyProbe21::tree &t,
    uint64_t
        n) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    uint64_t n;
    MemSafetyProbe21::tree t;
  };

  /// _After_n_: saves [n_, t], dispatches next recursive call.
  struct _After_n_ {
    uint64_t n_;
    MemSafetyProbe21::tree t;
  };

  /// _Combine_n_: receives partial results, combines with _result from final
  /// call.
  struct _Combine_n_ {
    uint64_t _result;
  };

  using _Frame = std::variant<_Enter, _After_n_, _Combine_n_>;
  uint64_t _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{n, t});
  /// Loopified branch_grow: _Enter -> _After_n_ -> _Combine_n_.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      uint64_t n = _f.n;
      const MemSafetyProbe21::tree &t = _f.t;
      if (n <= 0) {
        _result = tree_sum(t);
      } else {
        uint64_t n_ = n - 1;
        _stack.emplace_back(_After_n_{n_, t});
        _stack.emplace_back(
            _Enter{n_, tree::node(tree::leaf(), n, tree::leaf())});
      }
    } else if (std::holds_alternative<_After_n_>(_frame)) {
      auto _f = std::move(std::get<_After_n_>(_frame));
      _stack.emplace_back(_Combine_n_{_result});
      _stack.emplace_back(_Enter{_f.n_, std::move(_f.t)});
    } else {
      auto _f = std::move(std::get<_Combine_n_>(_frame));
      _result = (std::move(_result) + std::move(_f._result));
    }
  }
  return _result;
}

/// TEST 4: Recursive call where the tree argument is built from
/// MULTIPLE constructor calls with the original tree embedded.
uint64_t MemSafetyProbe21::embed_grow(MemSafetyProbe21::tree t, uint64_t n) {
  uint64_t _loop_n = std::move(n);
  MemSafetyProbe21::tree _loop_t = std::move(t);
  while (true) {
    if (_loop_n <= 0) {
      return tree_sum(std::move(_loop_t));
    } else {
      uint64_t n_ = _loop_n - 1;
      uint64_t _next_n = n_;
      _loop_t =
          tree::node(tree::node(_loop_t, _loop_n, tree::leaf()), UINT64_C(0),
                     tree::node(tree::leaf(), _loop_n, _loop_t));
      _loop_n = _next_n;
    }
  }
}

/// TEST 5: Accumulator pattern with tree building.
MemSafetyProbe21::tree MemSafetyProbe21::accum_tree(MemSafetyProbe21::tree acc,
                                                    uint64_t n) {
  uint64_t _loop_n = std::move(n);
  MemSafetyProbe21::tree _loop_acc = std::move(acc);
  while (true) {
    if (_loop_n <= 0) {
      return _loop_acc;
    } else {
      uint64_t n_ = _loop_n - 1;
      uint64_t _next_n = n_;
      _loop_acc = tree::node(std::move(_loop_acc), _loop_n, tree::leaf());
      _loop_n = _next_n;
    }
  }
}

/// TEST 7: Mutually-referencing recursive call with tree
/// construction at each level.
uint64_t MemSafetyProbe21::weave(MemSafetyProbe21::tree t1,
                                 MemSafetyProbe21::tree t2, uint64_t n) {
  uint64_t _loop_n = std::move(n);
  MemSafetyProbe21::tree _loop_t2 = std::move(t2);
  MemSafetyProbe21::tree _loop_t1 = std::move(t1);
  while (true) {
    if (_loop_n <= 0) {
      return (tree_sum(std::move(_loop_t1)) + tree_sum(std::move(_loop_t2)));
    } else {
      uint64_t n_ = _loop_n - 1;
      uint64_t _next_n = n_;
      MemSafetyProbe21::tree _next_t2 =
          tree::node(std::move(_loop_t1), _loop_n, tree::leaf());
      MemSafetyProbe21::tree _next_t1 =
          tree::node(std::move(_loop_t2), _loop_n, tree::leaf());
      _loop_n = _next_n;
      _loop_t2 = std::move(_next_t2);
      _loop_t1 = std::move(_next_t1);
    }
  }
}

/// TEST 8: Deep nesting with tree_sum at each level before recursion.
uint64_t MemSafetyProbe21::sum_and_grow(
    MemSafetyProbe21::tree t,
    uint64_t
        n) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    uint64_t n;
    MemSafetyProbe21::tree t;
  };

  /// _Resume_n_: saves [s], resumes after recursive call with _result.
  struct _Resume_n_ {
    uint64_t s;
  };

  using _Frame = std::variant<_Enter, _Resume_n_>;
  uint64_t _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{n, t});
  /// Loopified sum_and_grow: _Enter -> _Resume_n_.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      uint64_t n = _f.n;
      MemSafetyProbe21::tree t = std::move(_f.t);
      if (n <= 0) {
        _result = tree_sum(std::move(t));
      } else {
        uint64_t n_ = n - 1;
        uint64_t s = tree_sum(t);
        _stack.emplace_back(_Resume_n_{s});
        _stack.emplace_back(
            _Enter{n_, tree::node(std::move(t), s, tree::leaf())});
      }
    } else {
      auto _f = std::move(std::get<_Resume_n_>(_frame));
      _result = (_f.s + _result);
    }
  }
  return _result;
}
