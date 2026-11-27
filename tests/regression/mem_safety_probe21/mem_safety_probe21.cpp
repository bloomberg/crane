#include "mem_safety_probe21.h"

uint64_t MemSafetyProbe21::tree_sum(const MemSafetyProbe21::tree &t) {
  // Explicit stack replaces the non-tail recursion of tree_sum: _call frames
  // are pending calls, _after frames resume a caller.
  struct _call {
    const MemSafetyProbe21::tree *t;
  };

  struct _after_tree_sum_in_Node {
    uint64_t a1;
    const MemSafetyProbe21::tree *a2;
  };

  struct _after_tree_sum_in_Node_2 {
    uint64_t a1;
    uint64_t _tmp2;
  };

  using _frame =
      std::variant<_call, _after_tree_sum_in_Node, _after_tree_sum_in_Node_2>;
  uint64_t _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&t});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const MemSafetyProbe21::tree &t = *_f.t;
      if (std::holds_alternative<typename MemSafetyProbe21::tree::Leaf>(t.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1, a2] =
            std::get<typename MemSafetyProbe21::tree::Node>(t.v());
        _stack.emplace_back(_after_tree_sum_in_Node{a1, crane_raw(a2)});
        _stack.emplace_back(_call{crane_raw(a0)});
      }
    } else if (std::holds_alternative<_after_tree_sum_in_Node>(_popped)) {
      auto _f = std::move(std::get<_after_tree_sum_in_Node>(_popped));
      _stack.pop_back();
      uint64_t a1 = _f.a1;
      const MemSafetyProbe21::tree &a2 = *_f.a2;
      _stack.emplace_back(_after_tree_sum_in_Node_2{a1, _result});
      _stack.emplace_back(_call{&a2});
    } else {
      auto _f = std::move(std::get<_after_tree_sum_in_Node_2>(_popped));
      _stack.pop_back();
      uint64_t a1 = _f.a1;
      _result = _f._tmp2 + a1 + _result;
    }
  }
  return _result;
}

/// TEST 1: Tail-recursive function where the recursive call takes
/// a constructed tree. The loopifier must store the new tree
/// somewhere that outlives the iteration.
uint64_t MemSafetyProbe21::grow_and_sum(const MemSafetyProbe21::tree &t,
                                        uint64_t n) {
  // Loop replaces the tail recursion: each recursive call updates the loop
  // variables.
  MemSafetyProbe21::tree _loop_t = t;
  while (true) {
    if (n <= 0) {
      return tree_sum(_loop_t);
    } else {
      uint64_t n_ = n - 1;
      uint64_t _next_n = n_;
      _loop_t = tree::node(std::move(_loop_t), n, tree::leaf());
      n = _next_n;
    }
  }
}

/// TEST 2: Non-tail recursive with constructed tree argument.
/// The recursive call creates a new tree AND uses the original.
uint64_t MemSafetyProbe21::double_grow(const MemSafetyProbe21::tree &t,
                                       uint64_t n) {
  // Explicit stack replaces the non-tail recursion of double_grow: _call frames
  // are pending calls, _after frames resume a caller.
  struct _call {
    uint64_t n;
    MemSafetyProbe21::tree t;
  };

  struct _after_double_grow_in_S {
    MemSafetyProbe21::tree t;
  };

  using _frame = std::variant<_call, _after_double_grow_in_S>;
  uint64_t _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{n, t});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      uint64_t n = _f.n;
      MemSafetyProbe21::tree t = std::move(_f.t);
      if (n <= 0) {
        _result = tree_sum(std::move(t));
      } else {
        uint64_t n_ = n - 1;
        _stack.emplace_back(_after_double_grow_in_S{t});
        _stack.emplace_back(
            _call{n_, tree::node(std::move(t), UINT64_C(0), tree::leaf())});
      }
    } else {
      auto _f = std::move(std::get<_after_double_grow_in_S>(_popped));
      _stack.pop_back();
      MemSafetyProbe21::tree t = std::move(_f.t);
      _result = tree_sum(std::move(t)) + _result;
    }
  }
  return _result;
}

/// TEST 3: Two recursive calls, one with original tree, one with
/// constructed tree.
uint64_t MemSafetyProbe21::branch_grow(const MemSafetyProbe21::tree &t,
                                       uint64_t n) {
  // Explicit stack replaces the non-tail recursion of branch_grow: _call frames
  // are pending calls, _after frames resume a caller.
  struct _call {
    uint64_t n;
    MemSafetyProbe21::tree t;
  };

  struct _after_branch_grow_in_S {
    uint64_t n;
    uint64_t n_;
  };

  struct _after_branch_grow_in_S_2 {
    uint64_t _tmp2;
  };

  using _frame =
      std::variant<_call, _after_branch_grow_in_S, _after_branch_grow_in_S_2>;
  uint64_t _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{n, t});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      uint64_t n = _f.n;
      MemSafetyProbe21::tree t = std::move(_f.t);
      if (n <= 0) {
        _result = tree_sum(std::move(t));
      } else {
        uint64_t n_ = n - 1;
        _stack.emplace_back(_after_branch_grow_in_S{n, n_});
        _stack.emplace_back(_call{n_, std::move(t)});
      }
    } else if (std::holds_alternative<_after_branch_grow_in_S>(_popped)) {
      auto _f = std::move(std::get<_after_branch_grow_in_S>(_popped));
      _stack.pop_back();
      uint64_t n = _f.n;
      uint64_t n_ = _f.n_;
      _stack.emplace_back(_after_branch_grow_in_S_2{_result});
      _stack.emplace_back(_call{n_, tree::node(tree::leaf(), n, tree::leaf())});
    } else {
      auto _f = std::move(std::get<_after_branch_grow_in_S_2>(_popped));
      _stack.pop_back();
      _result = _f._tmp2 + _result;
    }
  }
  return _result;
}

/// TEST 4: Recursive call where the tree argument is built from
/// MULTIPLE constructor calls with the original tree embedded.
uint64_t MemSafetyProbe21::embed_grow(const MemSafetyProbe21::tree &t,
                                      uint64_t n) {
  // Loop replaces the tail recursion: each recursive call updates the loop
  // variables.
  MemSafetyProbe21::tree _loop_t = t;
  while (true) {
    if (n <= 0) {
      return tree_sum(_loop_t);
    } else {
      uint64_t n_ = n - 1;
      uint64_t _next_n = n_;
      _loop_t = tree::node(tree::node(_loop_t, n, tree::leaf()), UINT64_C(0),
                           tree::node(tree::leaf(), n, _loop_t));
      n = _next_n;
    }
  }
}

/// TEST 5: Accumulator pattern with tree building.
MemSafetyProbe21::tree MemSafetyProbe21::accum_tree(MemSafetyProbe21::tree acc,
                                                    uint64_t n) {
  // Loop replaces the tail recursion: each recursive call updates the loop
  // variables.
  MemSafetyProbe21::tree _loop_acc = std::move(acc);
  while (true) {
    if (n <= 0) {
      return _loop_acc;
    } else {
      uint64_t n_ = n - 1;
      uint64_t _next_n = n_;
      _loop_acc = tree::node(std::move(_loop_acc), n, tree::leaf());
      n = _next_n;
    }
  }
}

/// TEST 6: CPS-like pattern where the continuation builds a tree.
uint64_t MemSafetyProbe21::cps_sum(const MemSafetyProbe21::tree &t,
                                   const crane::fn<uint64_t(uint64_t)> &k) {
  // Loop replaces the tail recursion: each recursive call updates the loop
  // variables.
  crane::fn<uint64_t(uint64_t)> _loop_k = k;
  const MemSafetyProbe21::tree *_loop_t = &t;
  while (true) {
    if (std::holds_alternative<typename MemSafetyProbe21::tree::Leaf>(
            _loop_t->v())) {
      return _loop_k(UINT64_C(0));
    } else {
      const auto &[a0, a1, a2] =
          std::get<typename MemSafetyProbe21::tree::Node>(_loop_t->v());
      const MemSafetyProbe21::tree &a0_value = *a0;
      const MemSafetyProbe21::tree &a2_value = *a2;
      _loop_k = [=, a2_value = a2_value](uint64_t lsum) {
        return cps_sum(a2_value, [=, _loop_k = _loop_k](uint64_t rsum) {
          return _loop_k(lsum + a1 + rsum);
        });
      };
      _loop_t = &a0_value;
    }
  }
}

/// TEST 7: Mutually-referencing recursive call with tree
/// construction at each level.
uint64_t MemSafetyProbe21::weave(const MemSafetyProbe21::tree &t1,
                                 const MemSafetyProbe21::tree &t2, uint64_t n) {
  // Loop replaces the tail recursion: each recursive call updates the loop
  // variables.
  MemSafetyProbe21::tree _loop_t2 = t2;
  MemSafetyProbe21::tree _loop_t1 = t1;
  while (true) {
    if (n <= 0) {
      return tree_sum(_loop_t1) + tree_sum(_loop_t2);
    } else {
      uint64_t n_ = n - 1;
      uint64_t _next_n = n_;
      MemSafetyProbe21::tree _next_t2 = tree::node(_loop_t1, n, tree::leaf());
      MemSafetyProbe21::tree _next_t1 = tree::node(_loop_t2, n, tree::leaf());
      n = _next_n;
      _loop_t2 = std::move(_next_t2);
      _loop_t1 = std::move(_next_t1);
    }
  }
}

/// TEST 8: Deep nesting with tree_sum at each level before recursion.
uint64_t MemSafetyProbe21::sum_and_grow(const MemSafetyProbe21::tree &t,
                                        uint64_t n) {
  // Explicit stack replaces the non-tail recursion of sum_and_grow: _call
  // frames are pending calls, _after frames resume a caller.
  struct _call {
    uint64_t n;
    MemSafetyProbe21::tree t;
  };

  struct _after_sum_and_grow_in_S {
    uint64_t s;
  };

  using _frame = std::variant<_call, _after_sum_and_grow_in_S>;
  uint64_t _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{n, t});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      uint64_t n = _f.n;
      MemSafetyProbe21::tree t = std::move(_f.t);
      if (n <= 0) {
        _result = tree_sum(std::move(t));
      } else {
        uint64_t n_ = n - 1;
        uint64_t s = tree_sum(t);
        _stack.emplace_back(_after_sum_and_grow_in_S{s});
        _stack.emplace_back(
            _call{n_, tree::node(std::move(t), s, tree::leaf())});
      }
    } else {
      auto _f = std::move(std::get<_after_sum_and_grow_in_S>(_popped));
      _stack.pop_back();
      uint64_t s = _f.s;
      _result = s + _result;
    }
  }
  return _result;
}
