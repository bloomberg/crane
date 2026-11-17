#include "mem_safety_probe23.h"

uint64_t MemSafetyProbe23::tree_sum(const MemSafetyProbe23::tree &t) {
  // Explicit stack replaces the non-tail recursion of tree_sum: _call frames
  // are pending calls, _after frames resume a caller.
  struct _call {
    const MemSafetyProbe23::tree *t;
  };

  struct _after_tree_sum_in_Node {
    uint64_t a1;
    const MemSafetyProbe23::tree *a2;
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
    _frame _popped = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      const MemSafetyProbe23::tree &t = *_f.t;
      if (std::holds_alternative<typename MemSafetyProbe23::tree::Leaf>(t.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1, a2] =
            std::get<typename MemSafetyProbe23::tree::Node>(t.v());
        _stack.emplace_back(_after_tree_sum_in_Node{a1, crane_raw(a2)});
        _stack.emplace_back(_call{crane_raw(a0)});
      }
    } else if (std::holds_alternative<_after_tree_sum_in_Node>(_popped)) {
      auto _f = std::move(std::get<_after_tree_sum_in_Node>(_popped));
      uint64_t a1 = _f.a1;
      const MemSafetyProbe23::tree &a2 = *_f.a2;
      _stack.emplace_back(_after_tree_sum_in_Node_2{a1, std::move(_result)});
      _stack.emplace_back(_call{&a2});
    } else {
      auto _f = std::move(std::get<_after_tree_sum_in_Node_2>(_popped));
      uint64_t a1 = _f.a1;
      _result = ((_f._tmp2 + a1) + std::move(_result));
    }
  }
  return _result;
}

uint64_t MemSafetyProbe23::tree_size(const MemSafetyProbe23::tree &t) {
  // Explicit stack replaces the non-tail recursion of tree_size: _call frames
  // are pending calls, _after frames resume a caller.
  struct _call {
    const MemSafetyProbe23::tree *t;
  };

  struct _after_tree_size_in_Node {
    const MemSafetyProbe23::tree *a2;
  };

  struct _after_tree_size_in_Node_2 {
    uint64_t _tmp2;
  };

  using _frame =
      std::variant<_call, _after_tree_size_in_Node, _after_tree_size_in_Node_2>;
  uint64_t _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&t});
  while (!_stack.empty()) {
    _frame _popped = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      const MemSafetyProbe23::tree &t = *_f.t;
      if (std::holds_alternative<typename MemSafetyProbe23::tree::Leaf>(t.v())) {
        _result = UINT64_C(1);
      } else {
        const auto &[a0, _, a2] =
            std::get<typename MemSafetyProbe23::tree::Node>(t.v());
        _stack.emplace_back(_after_tree_size_in_Node{crane_raw(a2)});
        _stack.emplace_back(_call{crane_raw(a0)});
      }
    } else if (std::holds_alternative<_after_tree_size_in_Node>(_popped)) {
      auto _f = std::move(std::get<_after_tree_size_in_Node>(_popped));
      const MemSafetyProbe23::tree &a2 = *_f.a2;
      _stack.emplace_back(_after_tree_size_in_Node_2{std::move(_result)});
      _stack.emplace_back(_call{&a2});
    } else {
      auto _f = std::move(std::get<_after_tree_size_in_Node_2>(_popped));
      _result = ((UINT64_C(1) + _f._tmp2) + std::move(_result));
    }
  }
  return _result;
}

/// TEST 1: Return the ORIGINAL tree alongside recursive child processing.
/// t escapes because it is returned. Recursive calls on l and r (children).
/// Loopifier must handle: owned param + pointer-safe children.
std::pair<MemSafetyProbe23::tree, uint64_t>
MemSafetyProbe23::sum_with_original(const MemSafetyProbe23::tree &t) {
  // Explicit stack replaces the non-tail recursion of sum_with_original: _call
  // frames are pending calls, _after frames resume a caller.
  struct _call {
    const MemSafetyProbe23::tree *t;
  };

  struct _after_sum_with_original_in_Node {
    MemSafetyProbe23::tree t;
    uint64_t a1;
    const MemSafetyProbe23::tree *a2;
  };

  struct _after_sum_with_original_in_Node_2 {
    MemSafetyProbe23::tree t;
    uint64_t a1;
    std::pair<MemSafetyProbe23::tree, uint64_t> pl;
  };

  using _frame = std::variant<_call, _after_sum_with_original_in_Node,
                              _after_sum_with_original_in_Node_2>;
  std::pair<MemSafetyProbe23::tree, uint64_t> _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&t});
  while (!_stack.empty()) {
    _frame _popped = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      const MemSafetyProbe23::tree &t = *_f.t;
      if (std::holds_alternative<typename MemSafetyProbe23::tree::Leaf>(t.v())) {
        _result = std::make_pair(tree::leaf(), UINT64_C(0));
      } else {
        const auto &[a0, a1, a2] =
            std::get<typename MemSafetyProbe23::tree::Node>(t.v());
        _stack.emplace_back(
            _after_sum_with_original_in_Node{t, a1, crane_raw(a2)});
        _stack.emplace_back(_call{crane_raw(a0)});
      }
    } else if (
            std::holds_alternative<_after_sum_with_original_in_Node>(_popped)) {
      auto _f = std::move(std::get<_after_sum_with_original_in_Node>(_popped));
      const MemSafetyProbe23::tree &t = _f.t;
      uint64_t a1 = _f.a1;
      const MemSafetyProbe23::tree &a2 = *_f.a2;
      std::pair<MemSafetyProbe23::tree, uint64_t> pl = std::move(_result);
      _stack.emplace_back(
          _after_sum_with_original_in_Node_2{t, a1, std::move(pl)});
      _stack.emplace_back(_call{&a2});
    } else {
      auto _f =
          std::move(std::get<_after_sum_with_original_in_Node_2>(_popped));
      MemSafetyProbe23::tree t = std::move(_f.t);
      uint64_t a1 = _f.a1;
      std::pair<MemSafetyProbe23::tree, uint64_t> pl = std::move(_f.pl);
      std::pair<MemSafetyProbe23::tree, uint64_t> pr = std::move(_result);
      _result = std::make_pair(
          std::move(t), ((std::move(pl).second + a1) + std::move(pr).second));
    }
  }
  return _result;
}

/// TEST 2: Return a PAIR of the original tree and a transformed copy.
/// Forces tree to be owned; two recursive calls on children.
std::pair<MemSafetyProbe23::tree, MemSafetyProbe23::tree>
MemSafetyProbe23::dup_and_double(const MemSafetyProbe23::tree &t) {
  // Explicit stack replaces the non-tail recursion of dup_and_double: _call
  // frames are pending calls, _after frames resume a caller.
  struct _call {
    const MemSafetyProbe23::tree *t;
  };

  struct _after_dup_and_double_in_Node {
    MemSafetyProbe23::tree t;
    uint64_t a1;
    const MemSafetyProbe23::tree *a2;
  };

  struct _after_dup_and_double_in_Node_2 {
    MemSafetyProbe23::tree t;
    uint64_t a1;
    std::pair<MemSafetyProbe23::tree, MemSafetyProbe23::tree> pl;
  };

  using _frame = std::variant<_call, _after_dup_and_double_in_Node,
                              _after_dup_and_double_in_Node_2>;
  std::pair<MemSafetyProbe23::tree, MemSafetyProbe23::tree> _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&t});
  while (!_stack.empty()) {
    _frame _popped = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      const MemSafetyProbe23::tree &t = *_f.t;
      if (std::holds_alternative<typename MemSafetyProbe23::tree::Leaf>(t.v())) {
        _result = std::make_pair(tree::leaf(), tree::leaf());
      } else {
        const auto &[a0, a1, a2] =
            std::get<typename MemSafetyProbe23::tree::Node>(t.v());
        _stack.emplace_back(_after_dup_and_double_in_Node{t, a1,
                                                          crane_raw(a2)});
        _stack.emplace_back(_call{crane_raw(a0)});
      }
    } else if (std::holds_alternative<_after_dup_and_double_in_Node>(_popped)) {
      auto _f = std::move(std::get<_after_dup_and_double_in_Node>(_popped));
      const MemSafetyProbe23::tree &t = _f.t;
      uint64_t a1 = _f.a1;
      const MemSafetyProbe23::tree &a2 = *_f.a2;
      std::pair<MemSafetyProbe23::tree, MemSafetyProbe23::tree> pl =
          std::move(_result);
      _stack.emplace_back(_after_dup_and_double_in_Node_2{t, a1,
                                                          std::move(pl)});
      _stack.emplace_back(_call{&a2});
    } else {
      auto _f = std::move(std::get<_after_dup_and_double_in_Node_2>(_popped));
      MemSafetyProbe23::tree t = std::move(_f.t);
      uint64_t a1 = _f.a1;
      std::pair<MemSafetyProbe23::tree, MemSafetyProbe23::tree> pl =
          std::move(_f.pl);
      std::pair<MemSafetyProbe23::tree, MemSafetyProbe23::tree> pr =
          std::move(_result);
      _result = std::make_pair(
          std::move(t), tree::node(std::move(pl).second, (a1 * UINT64_C(2)),
                                   std::move(pr).second));
    }
  }
  return _result;
}

/// TEST 3: Store children in result alongside recursive processing.
/// l and r are extracted from match, BOTH used in result AND in
/// recursive calls. Tests whether children are correctly cloned when
/// they appear in both continuation and recursive positions.
std::pair<std::pair<MemSafetyProbe23::tree, MemSafetyProbe23::tree>, uint64_t>
MemSafetyProbe23::collect_children(const MemSafetyProbe23::tree &t) {
  // Explicit stack replaces the non-tail recursion of collect_children: _call
  // frames are pending calls, _after frames resume a caller.
  struct _call {
    const MemSafetyProbe23::tree *t;
  };

  struct _after_collect_children_in_Node {
    std::shared_ptr<MemSafetyProbe23::tree> a0;
    uint64_t a1;
    const MemSafetyProbe23::tree *a2;
  };

  struct _after_collect_children_in_Node_2 {
    std::shared_ptr<MemSafetyProbe23::tree> a0;
    uint64_t a1;
    const MemSafetyProbe23::tree *a2;
    std::pair<std::pair<MemSafetyProbe23::tree, MemSafetyProbe23::tree>,
              uint64_t> pl;
  };

  using _frame = std::variant<_call, _after_collect_children_in_Node,
                              _after_collect_children_in_Node_2>;
  std::pair<std::pair<MemSafetyProbe23::tree, MemSafetyProbe23::tree>,
            uint64_t> _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&t});
  while (!_stack.empty()) {
    _frame _popped = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      const MemSafetyProbe23::tree &t = *_f.t;
      if (std::holds_alternative<typename MemSafetyProbe23::tree::Leaf>(t.v())) {
        _result = std::make_pair(std::make_pair(tree::leaf(), tree::leaf()),
                                 UINT64_C(0));
      } else {
        const auto &[a0, a1, a2] =
            std::get<typename MemSafetyProbe23::tree::Node>(t.v());
        _stack.emplace_back(
            _after_collect_children_in_Node{a0, a1, crane_raw(a2)});
        _stack.emplace_back(_call{crane_raw(a0)});
      }
    } else if (std::holds_alternative<_after_collect_children_in_Node>(_popped)) {
      auto _f = std::move(std::get<_after_collect_children_in_Node>(_popped));
      std::shared_ptr<MemSafetyProbe23::tree> a0 = std::move(_f.a0);
      uint64_t a1 = _f.a1;
      const MemSafetyProbe23::tree &a2 = *_f.a2;
      std::pair<std::pair<MemSafetyProbe23::tree, MemSafetyProbe23::tree>,
                uint64_t> pl = std::move(_result);
      _stack.emplace_back(_after_collect_children_in_Node_2{std::move(a0), a1,
                                                            &a2,
                                                            std::move(pl)});
      _stack.emplace_back(_call{&a2});
    } else {
      auto _f = std::move(std::get<_after_collect_children_in_Node_2>(_popped));
      std::shared_ptr<MemSafetyProbe23::tree> a0 = std::move(_f.a0);
      uint64_t a1 = _f.a1;
      const MemSafetyProbe23::tree &a2 = *_f.a2;
      std::pair<std::pair<MemSafetyProbe23::tree, MemSafetyProbe23::tree>,
                uint64_t> pl = std::move(_f.pl);
      std::pair<std::pair<MemSafetyProbe23::tree, MemSafetyProbe23::tree>,
                uint64_t> pr = std::move(_result);
      uint64_t s = (([&]() -> uint64_t {
        auto [p, n] = std::move(pl);
        auto [_x, _x0] = std::move(p);
        return n;
      }() + a1) + [&]() -> uint64_t {
        auto [p, n] = std::move(pr);
        auto [_x, _x0] = std::move(p);
        return n;
      }());
      _result = std::make_pair(std::make_pair(*a0, a2), s);
    }
  }
  return _result;
}

/// TEST 4: Recursive function that rebuilds tree with an
/// ACCUMULATOR that captures the original tree. The accumulator
/// forces the tree to be owned. Two recursive calls on children.
std::pair<MemSafetyProbe23::tree, uint64_t>
MemSafetyProbe23::sum_with_acc(const MemSafetyProbe23::tree &t, uint64_t acc) {
  // Explicit stack replaces the non-tail recursion of sum_with_acc: _call
  // frames are pending calls, _after frames resume a caller.
  struct _call {
    uint64_t acc;
    const MemSafetyProbe23::tree *t;
  };

  struct _after_sum_with_acc_in_Node {
    uint64_t a1;
    const MemSafetyProbe23::tree *a2;
  };

  struct _after_sum_with_acc_in_Node_2 {
    uint64_t a1;
    std::pair<MemSafetyProbe23::tree, uint64_t> pl;
  };

  using _frame = std::variant<_call, _after_sum_with_acc_in_Node,
                              _after_sum_with_acc_in_Node_2>;
  std::pair<MemSafetyProbe23::tree, uint64_t> _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{acc, &t});
  while (!_stack.empty()) {
    _frame _popped = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      uint64_t acc = _f.acc;
      const MemSafetyProbe23::tree &t = *_f.t;
      if (std::holds_alternative<typename MemSafetyProbe23::tree::Leaf>(t.v())) {
        _result = std::make_pair(tree::leaf(), acc);
      } else {
        const auto &[a0, a1, a2] =
            std::get<typename MemSafetyProbe23::tree::Node>(t.v());
        _stack.emplace_back(_after_sum_with_acc_in_Node{a1, crane_raw(a2)});
        _stack.emplace_back(_call{(acc + a1), crane_raw(a0)});
      }
    } else if (std::holds_alternative<_after_sum_with_acc_in_Node>(_popped)) {
      auto _f = std::move(std::get<_after_sum_with_acc_in_Node>(_popped));
      uint64_t a1 = _f.a1;
      const MemSafetyProbe23::tree &a2 = *_f.a2;
      std::pair<MemSafetyProbe23::tree, uint64_t> pl = std::move(_result);
      _stack.emplace_back(_after_sum_with_acc_in_Node_2{a1, pl});
      _stack.emplace_back(_call{std::move(pl).second, &a2});
    } else {
      auto _f = std::move(std::get<_after_sum_with_acc_in_Node_2>(_popped));
      uint64_t a1 = _f.a1;
      std::pair<MemSafetyProbe23::tree, uint64_t> pl = std::move(_f.pl);
      std::pair<MemSafetyProbe23::tree, uint64_t> pr = std::move(_result);
      _result = std::make_pair(
          tree::node(std::move(pl).first, a1, std::move(pr).first),
          std::move(pr).second);
    }
  }
  return _result;
}

/// TEST 5: Function using tree_sum on children INSIDE the same
/// expression as recursive calls. Tests that child pointers remain
/// valid when other operations happen on the same tree.
std::pair<uint64_t, uint64_t>
MemSafetyProbe23::interleaved_ops(const MemSafetyProbe23::tree &t) {
  // Explicit stack replaces the non-tail recursion of interleaved_ops: _call
  // frames are pending calls, _after frames resume a caller.
  struct _call {
    const MemSafetyProbe23::tree *t;
  };

  struct _after_interleaved_ops_in_Node {
    uint64_t a1;
    const MemSafetyProbe23::tree *a2;
    uint64_t sl;
    uint64_t sr;
  };

  struct _after_interleaved_ops_in_Node_2 {
    uint64_t a1;
    uint64_t sl;
    uint64_t sr;
    std::pair<uint64_t, uint64_t> pl;
  };

  using _frame = std::variant<_call, _after_interleaved_ops_in_Node,
                              _after_interleaved_ops_in_Node_2>;
  std::pair<uint64_t, uint64_t> _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&t});
  while (!_stack.empty()) {
    _frame _popped = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      const MemSafetyProbe23::tree &t = *_f.t;
      if (std::holds_alternative<typename MemSafetyProbe23::tree::Leaf>(t.v())) {
        _result = std::make_pair(UINT64_C(0), UINT64_C(0));
      } else {
        const auto &[a0, a1, a2] =
            std::get<typename MemSafetyProbe23::tree::Node>(t.v());
        uint64_t sl = tree_sum(*a0);
        uint64_t sr = tree_sum(*a2);
        _stack.emplace_back(
            _after_interleaved_ops_in_Node{a1, crane_raw(a2), sl, sr});
        _stack.emplace_back(_call{crane_raw(a0)});
      }
    } else if (std::holds_alternative<_after_interleaved_ops_in_Node>(_popped)) {
      auto _f = std::move(std::get<_after_interleaved_ops_in_Node>(_popped));
      uint64_t a1 = _f.a1;
      const MemSafetyProbe23::tree &a2 = *_f.a2;
      uint64_t sl = _f.sl;
      uint64_t sr = _f.sr;
      std::pair<uint64_t, uint64_t> pl = std::move(_result);
      _stack.emplace_back(_after_interleaved_ops_in_Node_2{a1, sl, sr, pl});
      _stack.emplace_back(_call{&a2});
    } else {
      auto _f = std::move(std::get<_after_interleaved_ops_in_Node_2>(_popped));
      uint64_t a1 = _f.a1;
      uint64_t sl = _f.sl;
      uint64_t sr = _f.sr;
      std::pair<uint64_t, uint64_t> pl = _f.pl;
      std::pair<uint64_t, uint64_t> pr = std::move(_result);
      _result = std::make_pair(((sl + a1) + sr), ((pl.first + a1) + pr.first));
    }
  }
  return _result;
}

/// TEST 6: Nested tree type — tree of trees. Tests clone correctness
/// for deeply nested value types.
uint64_t
MemSafetyProbe23::flatten_tree_of_trees(const MemSafetyProbe23::tree &t,
                                        const MemSafetyProbe23::tree &inner) {
  // Explicit stack replaces the non-tail recursion of flatten_tree_of_trees:
  // _call frames are pending calls, _after frames resume a caller.
  struct _call {
    MemSafetyProbe23::tree inner;
    const MemSafetyProbe23::tree *t;
  };

  struct _after_flatten_tree_of_trees_in_Node {
    MemSafetyProbe23::tree inner;
    const MemSafetyProbe23::tree *a2;
  };

  struct _after_flatten_tree_of_trees_in_Node_2 {
    uint64_t _tmp2;
  };

  using _frame = std::variant<_call, _after_flatten_tree_of_trees_in_Node,
                              _after_flatten_tree_of_trees_in_Node_2>;
  uint64_t _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{inner, &t});
  while (!_stack.empty()) {
    _frame _popped = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      const MemSafetyProbe23::tree &inner = _f.inner;
      const MemSafetyProbe23::tree &t = *_f.t;
      if (std::holds_alternative<typename MemSafetyProbe23::tree::Leaf>(t.v())) {
        _result = tree_sum(inner);
      } else {
        const auto &[a0, a1, a2] =
            std::get<typename MemSafetyProbe23::tree::Node>(t.v());
        MemSafetyProbe23::tree new_inner = tree::node(inner, a1, tree::leaf());
        _stack.emplace_back(
            _after_flatten_tree_of_trees_in_Node{inner, crane_raw(a2)});
        _stack.emplace_back(_call{std::move(new_inner), crane_raw(a0)});
      }
    } else if (std::holds_alternative<_after_flatten_tree_of_trees_in_Node>(
                   _popped)) {
      auto _f =
          std::move(std::get<_after_flatten_tree_of_trees_in_Node>(_popped));
      MemSafetyProbe23::tree inner = std::move(_f.inner);
      const MemSafetyProbe23::tree &a2 = *_f.a2;
      _stack.emplace_back(
          _after_flatten_tree_of_trees_in_Node_2{std::move(_result)});
      _stack.emplace_back(_call{std::move(inner), &a2});
    } else {
      auto _f =
          std::move(std::get<_after_flatten_tree_of_trees_in_Node_2>(_popped));
      _result = (_f._tmp2 + std::move(_result));
    }
  }
  return _result;
}

/// TEST 7: Two recursive calls where one takes a CONSTRUCTED tree
/// with t embedded AND another takes a child of t.
/// Forces t to NOT be pointer-safe. The After frame saves
/// state for the child-based call.
uint64_t MemSafetyProbe23::mixed_recurse(const MemSafetyProbe23::tree &t,
                                         uint64_t n) {
  // Explicit stack replaces the non-tail recursion of mixed_recurse: _call
  // frames are pending calls, _after frames resume a caller.
  struct _call {
    uint64_t n;
    MemSafetyProbe23::tree t;
  };

  struct _after_mixed_recurse_in_Node {
    uint64_t n_;
    std::shared_ptr<MemSafetyProbe23::tree> a2;
  };

  struct _after_mixed_recurse_in_Node_2 {
    uint64_t _tmp2;
  };

  using _frame = std::variant<_call, _after_mixed_recurse_in_Node,
                              _after_mixed_recurse_in_Node_2>;
  uint64_t _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{n, t});
  while (!_stack.empty()) {
    _frame _popped = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      uint64_t n = _f.n;
      const MemSafetyProbe23::tree &t = _f.t;
      if (n <= 0) {
        _result = tree_sum(t);
      } else {
        uint64_t n_ = n - 1;
        if (std::holds_alternative<typename MemSafetyProbe23::tree::Leaf>(t.v())) {
          _result = UINT64_C(0);
        } else {
          const auto &[_, a1, a2] =
              std::get<typename MemSafetyProbe23::tree::Node>(t.v());
          _stack.emplace_back(_after_mixed_recurse_in_Node{n_, a2});
          _stack.emplace_back(_call{n_, tree::node(t, a1, tree::leaf())});
        }
      }
    } else if (std::holds_alternative<_after_mixed_recurse_in_Node>(_popped)) {
      auto _f = std::move(std::get<_after_mixed_recurse_in_Node>(_popped));
      uint64_t n_ = _f.n_;
      std::shared_ptr<MemSafetyProbe23::tree> a2 = std::move(_f.a2);
      _stack.emplace_back(_after_mixed_recurse_in_Node_2{std::move(_result)});
      _stack.emplace_back(_call{n_, *a2});
    } else {
      auto _f = std::move(std::get<_after_mixed_recurse_in_Node_2>(_popped));
      _result = (_f._tmp2 + std::move(_result));
    }
  }
  return _result;
}

/// TEST 8: Three-way split: function returns original tree AND
/// uses tree_size on children. Forces tree owned; exercises
/// the interplay between clone, move, and raw pointer in
/// continuation frames.
std::pair<MemSafetyProbe23::tree, uint64_t>
MemSafetyProbe23::annotate_sizes(const MemSafetyProbe23::tree &t) {
  // Explicit stack replaces the non-tail recursion of annotate_sizes: _call
  // frames are pending calls, _after frames resume a caller.
  struct _call {
    const MemSafetyProbe23::tree *t;
  };

  struct _after_annotate_sizes_in_Node {
    uint64_t a1;
    const MemSafetyProbe23::tree *a2;
    uint64_t sl;
    uint64_t sr;
  };

  struct _after_annotate_sizes_in_Node_2 {
    uint64_t a1;
    uint64_t sl;
    uint64_t sr;
    std::pair<MemSafetyProbe23::tree, uint64_t> pl;
  };

  using _frame = std::variant<_call, _after_annotate_sizes_in_Node,
                              _after_annotate_sizes_in_Node_2>;
  std::pair<MemSafetyProbe23::tree, uint64_t> _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&t});
  while (!_stack.empty()) {
    _frame _popped = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      const MemSafetyProbe23::tree &t = *_f.t;
      if (std::holds_alternative<typename MemSafetyProbe23::tree::Leaf>(t.v())) {
        _result = std::make_pair(tree::leaf(), UINT64_C(0));
      } else {
        const auto &[a0, a1, a2] =
            std::get<typename MemSafetyProbe23::tree::Node>(t.v());
        uint64_t sl = tree_size(*a0);
        uint64_t sr = tree_size(*a2);
        _stack.emplace_back(
            _after_annotate_sizes_in_Node{a1, crane_raw(a2), sl, sr});
        _stack.emplace_back(_call{crane_raw(a0)});
      }
    } else if (std::holds_alternative<_after_annotate_sizes_in_Node>(_popped)) {
      auto _f = std::move(std::get<_after_annotate_sizes_in_Node>(_popped));
      uint64_t a1 = _f.a1;
      const MemSafetyProbe23::tree &a2 = *_f.a2;
      uint64_t sl = _f.sl;
      uint64_t sr = _f.sr;
      std::pair<MemSafetyProbe23::tree, uint64_t> pl = std::move(_result);
      _stack.emplace_back(
          _after_annotate_sizes_in_Node_2{a1, sl, sr, std::move(pl)});
      _stack.emplace_back(_call{&a2});
    } else {
      auto _f = std::move(std::get<_after_annotate_sizes_in_Node_2>(_popped));
      uint64_t a1 = _f.a1;
      uint64_t sl = _f.sl;
      uint64_t sr = _f.sr;
      std::pair<MemSafetyProbe23::tree, uint64_t> pl = std::move(_f.pl);
      std::pair<MemSafetyProbe23::tree, uint64_t> pr = std::move(_result);
      _result = std::make_pair(
          tree::node(std::move(pl).first, ((a1 + sl) + sr),
                     std::move(pr).first),
          ((std::move(pl).second + std::move(pr).second) + UINT64_C(1)));
    }
  }
  return _result;
}
