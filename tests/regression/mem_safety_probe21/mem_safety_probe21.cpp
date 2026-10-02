#include "mem_safety_probe21.h"

uint64_t MemSafetyProbe21::tree_sum(
    const MemSafetyProbe21::tree
        &t) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const MemSafetyProbe21::tree *t;
  };

  /// _Cont_Node: saves [a1, a2], resumes after recursive call, then processes
  /// rest.
  struct _Cont_Node {
    uint64_t a1;
    const MemSafetyProbe21::tree *a2;
  };

  /// _Cont_Node_1: saves [a1, r_], resumes after recursive call, then processes
  /// rest.
  struct _Cont_Node_1 {
    uint64_t a1;
    uint64_t r_;
  };

  using _Frame = std::variant<_Enter, _Cont_Node, _Cont_Node_1>;
  uint64_t _result{};
  crane::small_vector<_Frame> _stack;
  _stack.emplace_back(_Enter{&t});
  /// Loopified tree_sum: _Enter -> _Cont_Node -> _Cont_Node_1.
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
        _stack.emplace_back(_Cont_Node{a1, crane_raw(a2)});
        _stack.emplace_back(_Enter{crane_raw(a0)});
      }
    } else if (std::holds_alternative<_Cont_Node>(_frame)) {
      auto _f = std::move(std::get<_Cont_Node>(_frame));
      uint64_t a1 = _f.a1;
      const MemSafetyProbe21::tree &a2 = *_f.a2;
      uint64_t r_ = std::move(_result);
      _stack.emplace_back(_Cont_Node_1{a1, r_});
      _stack.emplace_back(_Enter{&a2});
    } else {
      auto _f = std::move(std::get<_Cont_Node_1>(_frame));
      uint64_t a1 = _f.a1;
      uint64_t r_ = _f.r_;
      uint64_t r_0 = std::move(_result);
      _result = ((r_ + a1) + r_0);
    }
  }
  return _result;
}

/// TEST 1: Tail-recursive function where the recursive call takes
/// a constructed tree. The loopifier must store the new tree
/// somewhere that outlives the iteration.
uint64_t MemSafetyProbe21::grow_and_sum(const MemSafetyProbe21::tree &t,
                                        uint64_t n) {
  uint64_t _loop_n = std::move(n);
  MemSafetyProbe21::tree _loop_t = t;
  while (true) {
    if (_loop_n <= 0) {
      return tree_sum(_loop_t);
    } else {
      uint64_t n_ = _loop_n - 1;
      uint64_t _next_n = n_;
      _loop_t = tree::node(_loop_t, _loop_n, tree::leaf());
      _loop_n = _next_n;
    }
  }
}

/// TEST 2: Non-tail recursive with constructed tree argument.
/// The recursive call creates a new tree AND uses the original.
uint64_t MemSafetyProbe21::double_grow(
    const MemSafetyProbe21::tree &t,
    uint64_t
        n) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    uint64_t n;
    MemSafetyProbe21::tree t;
  };

  /// _Cont_n_: saves [t], resumes after recursive call, then processes rest.
  struct _Cont_n_ {
    MemSafetyProbe21::tree t;
  };

  using _Frame = std::variant<_Enter, _Cont_n_>;
  uint64_t _result{};
  crane::small_vector<_Frame> _stack;
  _stack.emplace_back(_Enter{n, t});
  /// Loopified double_grow: _Enter -> _Cont_n_.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      uint64_t n = _f.n;
      const MemSafetyProbe21::tree &t = std::move(_f.t);
      if (n <= 0) {
        _result = tree_sum(t);
      } else {
        uint64_t n_ = n - 1;
        _stack.emplace_back(_Cont_n_{t});
        _stack.emplace_back(
            _Enter{n_, tree::node(t, UINT64_C(0), tree::leaf())});
      }
    } else {
      auto _f = std::move(std::get<_Cont_n_>(_frame));
      const MemSafetyProbe21::tree &t = std::move(_f.t);
      uint64_t r_ = std::move(_result);
      _result = (tree_sum(t) + r_);
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

  /// _Cont_n_: saves [n, n_], resumes after recursive call, then processes
  /// rest.
  struct _Cont_n_ {
    uint64_t n;
    uint64_t n_;
  };

  /// _Cont_n__1: saves [r_], resumes after recursive call, then processes rest.
  struct _Cont_n__1 {
    uint64_t r_;
  };

  using _Frame = std::variant<_Enter, _Cont_n_, _Cont_n__1>;
  uint64_t _result{};
  crane::small_vector<_Frame> _stack;
  _stack.emplace_back(_Enter{n, t});
  /// Loopified branch_grow: _Enter -> _Cont_n_ -> _Cont_n__1.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      uint64_t n = _f.n;
      const MemSafetyProbe21::tree &t = std::move(_f.t);
      if (n <= 0) {
        _result = tree_sum(t);
      } else {
        uint64_t n_ = n - 1;
        _stack.emplace_back(_Cont_n_{n, n_});
        _stack.emplace_back(_Enter{n_, t});
      }
    } else if (std::holds_alternative<_Cont_n_>(_frame)) {
      auto _f = std::move(std::get<_Cont_n_>(_frame));
      uint64_t n = _f.n;
      uint64_t n_ = _f.n_;
      uint64_t r_ = std::move(_result);
      _stack.emplace_back(_Cont_n__1{r_});
      _stack.emplace_back(
          _Enter{n_, tree::node(tree::leaf(), n, tree::leaf())});
    } else {
      auto _f = std::move(std::get<_Cont_n__1>(_frame));
      uint64_t r_ = _f.r_;
      uint64_t r_0 = std::move(_result);
      _result = (r_ + r_0);
    }
  }
  return _result;
}

/// TEST 4: Recursive call where the tree argument is built from
/// MULTIPLE constructor calls with the original tree embedded.
uint64_t MemSafetyProbe21::embed_grow(const MemSafetyProbe21::tree &t,
                                      uint64_t n) {
  uint64_t _loop_n = std::move(n);
  MemSafetyProbe21::tree _loop_t = t;
  while (true) {
    if (_loop_n <= 0) {
      return tree_sum(_loop_t);
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
uint64_t MemSafetyProbe21::weave(const MemSafetyProbe21::tree &t1,
                                 const MemSafetyProbe21::tree &t2, uint64_t n) {
  uint64_t _loop_n = std::move(n);
  MemSafetyProbe21::tree _loop_t2 = t2;
  MemSafetyProbe21::tree _loop_t1 = t1;
  while (true) {
    if (_loop_n <= 0) {
      return (tree_sum(_loop_t1) + tree_sum(_loop_t2));
    } else {
      uint64_t n_ = _loop_n - 1;
      uint64_t _next_n = n_;
      MemSafetyProbe21::tree _next_t2 =
          tree::node(_loop_t1, _loop_n, tree::leaf());
      MemSafetyProbe21::tree _next_t1 =
          tree::node(_loop_t2, _loop_n, tree::leaf());
      _loop_n = _next_n;
      _loop_t2 = std::move(_next_t2);
      _loop_t1 = std::move(_next_t1);
    }
  }
}

/// TEST 8: Deep nesting with tree_sum at each level before recursion.
uint64_t MemSafetyProbe21::sum_and_grow(
    const MemSafetyProbe21::tree &t,
    uint64_t
        n) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    uint64_t n;
    MemSafetyProbe21::tree t;
  };

  /// _Cont_n_: saves [s], resumes after recursive call, then processes rest.
  struct _Cont_n_ {
    uint64_t s;
  };

  using _Frame = std::variant<_Enter, _Cont_n_>;
  uint64_t _result{};
  crane::small_vector<_Frame> _stack;
  _stack.emplace_back(_Enter{n, t});
  /// Loopified sum_and_grow: _Enter -> _Cont_n_.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      uint64_t n = _f.n;
      const MemSafetyProbe21::tree &t = std::move(_f.t);
      if (n <= 0) {
        _result = tree_sum(t);
      } else {
        uint64_t n_ = n - 1;
        uint64_t s = tree_sum(t);
        _stack.emplace_back(_Cont_n_{s});
        _stack.emplace_back(_Enter{n_, tree::node(t, s, tree::leaf())});
      }
    } else {
      auto _f = std::move(std::get<_Cont_n_>(_frame));
      uint64_t s = _f.s;
      uint64_t r_ = std::move(_result);
      _result = (s + r_);
    }
  }
  return _result;
}
