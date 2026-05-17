#include "mem_safety_probe23.h"

unsigned int MemSafetyProbe23::tree_sum(
    const MemSafetyProbe23::tree
        &t) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const MemSafetyProbe23::tree *t;
  };

  /// _After_Node: saves [d_a0, d_a1], dispatches next recursive call.
  struct _After_Node {
    const MemSafetyProbe23::tree *d_a0;
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
  _stack.emplace_back(_Enter{&t});
  /// Loopified tree_sum: _Enter -> _After_Node -> _Combine_Node.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const MemSafetyProbe23::tree &t = *_f.t;
      if (std::holds_alternative<typename MemSafetyProbe23::tree::Leaf>(
              t.v())) {
        _result = 0u;
      } else {
        const auto &[d_a0, d_a1, d_a2] =
            std::get<typename MemSafetyProbe23::tree::Node>(t.v());
        _stack.emplace_back(_After_Node{d_a0.get(), d_a1});
        _stack.emplace_back(_Enter{d_a2.get()});
      }
    } else if (std::holds_alternative<_After_Node>(_frame)) {
      auto _f = std::move(std::get<_After_Node>(_frame));
      _stack.emplace_back(_Combine_Node{_result, _f.d_a1});
      _stack.emplace_back(_Enter{_f.d_a0});
    } else {
      auto _f = std::move(std::get<_Combine_Node>(_frame));
      _result = ((_result + _f.d_a1) + _f._result);
    }
  }
  return _result;
}

unsigned int MemSafetyProbe23::tree_size(
    const MemSafetyProbe23::tree
        &t) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const MemSafetyProbe23::tree *t;
  };

  /// _After_Node: saves [d_a0, _s1], dispatches next recursive call.
  struct _After_Node {
    const MemSafetyProbe23::tree *d_a0;
    decltype(1u) _s1;
  };

  /// _Combine_Node: receives partial results, combines with _result from final
  /// call.
  struct _Combine_Node {
    unsigned int _result;
    decltype(1u) _s1;
  };

  using _Frame = std::variant<_Enter, _After_Node, _Combine_Node>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&t});
  /// Loopified tree_size: _Enter -> _After_Node -> _Combine_Node.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const MemSafetyProbe23::tree &t = *_f.t;
      if (std::holds_alternative<typename MemSafetyProbe23::tree::Leaf>(
              t.v())) {
        _result = 1u;
      } else {
        const auto &[d_a0, d_a1, d_a2] =
            std::get<typename MemSafetyProbe23::tree::Node>(t.v());
        _stack.emplace_back(_After_Node{d_a0.get(), 1u});
        _stack.emplace_back(_Enter{d_a2.get()});
      }
    } else if (std::holds_alternative<_After_Node>(_frame)) {
      auto _f = std::move(std::get<_After_Node>(_frame));
      _stack.emplace_back(_Combine_Node{_result, _f._s1});
      _stack.emplace_back(_Enter{_f.d_a0});
    } else {
      auto _f = std::move(std::get<_Combine_Node>(_frame));
      _result = ((_f._s1 + _result) + _f._result);
    }
  }
  return _result;
}

/// TEST 1: Return the ORIGINAL tree alongside recursive child processing.
/// t escapes because it is returned. Recursive calls on l and r (children).
/// Loopifier must handle: owned param + pointer-safe children.
std::pair<MemSafetyProbe23::tree, unsigned int>
MemSafetyProbe23::sum_with_original(MemSafetyProbe23::tree t) {
  if (std::holds_alternative<typename MemSafetyProbe23::tree::Leaf>(
          t.v_mut())) {
    return std::make_pair(tree::leaf(), 0u);
  } else {
    auto &[d_a0, d_a1, d_a2] =
        std::get<typename MemSafetyProbe23::tree::Node>(t.v_mut());
    std::pair<MemSafetyProbe23::tree, unsigned int> pl =
        sum_with_original(*d_a0);
    std::pair<MemSafetyProbe23::tree, unsigned int> pr =
        sum_with_original(*d_a2);
    return std::make_pair(std::move(t), ((pl.second + d_a1) + pr.second));
  }
}

/// TEST 2: Return a PAIR of the original tree and a transformed copy.
/// Forces tree to be owned; two recursive calls on children.
std::pair<MemSafetyProbe23::tree, MemSafetyProbe23::tree>
MemSafetyProbe23::dup_and_double(MemSafetyProbe23::tree t) {
  if (std::holds_alternative<typename MemSafetyProbe23::tree::Leaf>(
          t.v_mut())) {
    return std::make_pair(tree::leaf(), tree::leaf());
  } else {
    auto &[d_a0, d_a1, d_a2] =
        std::get<typename MemSafetyProbe23::tree::Node>(t.v_mut());
    std::pair<MemSafetyProbe23::tree, MemSafetyProbe23::tree> pl =
        dup_and_double(*d_a0);
    std::pair<MemSafetyProbe23::tree, MemSafetyProbe23::tree> pr =
        dup_and_double(*d_a2);
    return std::make_pair(std::move(t),
                          tree::node(pl.second, (d_a1 * 2u), pr.second));
  }
}

/// TEST 3: Store children in result alongside recursive processing.
/// l and r are extracted from match, BOTH used in result AND in
/// recursive calls. Tests whether children are correctly cloned when
/// they appear in both continuation and recursive positions.
std::pair<std::pair<MemSafetyProbe23::tree, MemSafetyProbe23::tree>,
          unsigned int>
MemSafetyProbe23::collect_children(const MemSafetyProbe23::tree &t) {
  if (std::holds_alternative<typename MemSafetyProbe23::tree::Leaf>(t.v())) {
    return std::make_pair(std::make_pair(tree::leaf(), tree::leaf()), 0u);
  } else {
    const auto &[d_a0, d_a1, d_a2] =
        std::get<typename MemSafetyProbe23::tree::Node>(t.v());
    std::pair<std::pair<MemSafetyProbe23::tree, MemSafetyProbe23::tree>,
              unsigned int>
        pl = collect_children(*d_a0);
    std::pair<std::pair<MemSafetyProbe23::tree, MemSafetyProbe23::tree>,
              unsigned int>
        pr = collect_children(*d_a2);
    unsigned int s =
        (([&]() -> unsigned int {
           const std::pair<MemSafetyProbe23::tree, MemSafetyProbe23::tree> &p =
               pl.first;
           const unsigned int &n = pl.second;
           const MemSafetyProbe23::tree &_x = p.first;
           const MemSafetyProbe23::tree &_x0 = p.second;
           return n;
         }() + d_a1) +
             [&]() -> unsigned int {
          const std::pair<MemSafetyProbe23::tree, MemSafetyProbe23::tree> &p =
              pr.first;
          const unsigned int &n = pr.second;
          const MemSafetyProbe23::tree &_x = p.first;
          const MemSafetyProbe23::tree &_x0 = p.second;
          return n;
        }());
    return std::make_pair(std::make_pair(*d_a0, *d_a2), s);
  }
}

/// TEST 4: Recursive function that rebuilds tree with an
/// ACCUMULATOR that captures the original tree. The accumulator
/// forces the tree to be owned. Two recursive calls on children.
std::pair<MemSafetyProbe23::tree, unsigned int>
MemSafetyProbe23::sum_with_acc(const MemSafetyProbe23::tree &t,
                               unsigned int acc) {
  if (std::holds_alternative<typename MemSafetyProbe23::tree::Leaf>(t.v())) {
    return std::make_pair(tree::leaf(), acc);
  } else {
    const auto &[d_a0, d_a1, d_a2] =
        std::get<typename MemSafetyProbe23::tree::Node>(t.v());
    std::pair<MemSafetyProbe23::tree, unsigned int> pl =
        sum_with_acc(*d_a0, (acc + d_a1));
    std::pair<MemSafetyProbe23::tree, unsigned int> pr =
        sum_with_acc(*d_a2, pl.second);
    return std::make_pair(tree::node(pl.first, d_a1, pr.first), pr.second);
  }
}

/// TEST 5: Function using tree_sum on children INSIDE the same
/// expression as recursive calls. Tests that child pointers remain
/// valid when other operations happen on the same tree.
std::pair<unsigned int, unsigned int>
MemSafetyProbe23::interleaved_ops(const MemSafetyProbe23::tree &t) {
  if (std::holds_alternative<typename MemSafetyProbe23::tree::Leaf>(t.v())) {
    return std::make_pair(0u, 0u);
  } else {
    const auto &[d_a0, d_a1, d_a2] =
        std::get<typename MemSafetyProbe23::tree::Node>(t.v());
    unsigned int sl = tree_sum(*d_a0);
    unsigned int sr = tree_sum(*d_a2);
    std::pair<unsigned int, unsigned int> pl = interleaved_ops(*d_a0);
    std::pair<unsigned int, unsigned int> pr = interleaved_ops(*d_a2);
    return std::make_pair(((sl + d_a1) + sr), ((pl.first + d_a1) + pr.first));
  }
}

/// TEST 6: Nested tree type — tree of trees. Tests clone correctness
/// for deeply nested value types.
unsigned int MemSafetyProbe23::flatten_tree_of_trees(
    const MemSafetyProbe23::tree &t,
    MemSafetyProbe23::tree inner) { /// _Enter: captures varying parameters for
                                    /// each recursive call.

  struct _Enter {
    MemSafetyProbe23::tree inner;
    const MemSafetyProbe23::tree *t;
  };

  /// _After_Node: saves [new_inner, d_a0], dispatches next recursive call.
  struct _After_Node {
    MemSafetyProbe23::tree new_inner;
    const MemSafetyProbe23::tree *d_a0;
  };

  /// _Combine_Node: receives partial results, combines with _result from final
  /// call.
  struct _Combine_Node {
    unsigned int _result;
  };

  using _Frame = std::variant<_Enter, _After_Node, _Combine_Node>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{inner, &t});
  /// Loopified flatten_tree_of_trees: _Enter -> _After_Node -> _Combine_Node.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      MemSafetyProbe23::tree inner = std::move(_f.inner);
      const MemSafetyProbe23::tree &t = *_f.t;
      if (std::holds_alternative<typename MemSafetyProbe23::tree::Leaf>(
              t.v())) {
        _result = tree_sum(std::move(inner));
      } else {
        const auto &[d_a0, d_a1, d_a2] =
            std::get<typename MemSafetyProbe23::tree::Node>(t.v());
        MemSafetyProbe23::tree new_inner =
            tree::node(inner, d_a1, tree::leaf());
        _stack.emplace_back(_After_Node{std::move(new_inner), d_a0.get()});
        _stack.emplace_back(_Enter{std::move(inner), d_a2.get()});
      }
    } else if (std::holds_alternative<_After_Node>(_frame)) {
      auto _f = std::move(std::get<_After_Node>(_frame));
      _stack.emplace_back(_Combine_Node{_result});
      _stack.emplace_back(_Enter{std::move(_f.new_inner), _f.d_a0});
    } else {
      auto _f = std::move(std::get<_Combine_Node>(_frame));
      _result = (_result + _f._result);
    }
  }
  return _result;
}

/// TEST 7: Two recursive calls where one takes a CONSTRUCTED tree
/// with t embedded AND another takes a child of t.
/// Forces t to NOT be pointer-safe. The After frame saves
/// state for the child-based call.
unsigned int MemSafetyProbe23::mixed_recurse(
    MemSafetyProbe23::tree t,
    unsigned int
        n) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    unsigned int n;
    MemSafetyProbe23::tree t;
  };

  /// _After_Node: saves [n_, _s1], dispatches next recursive call.
  struct _After_Node {
    unsigned int n_;
    decltype(tree::node(std::declval<MemSafetyProbe23::tree &>(),
                        std::declval<unsigned int &>(), tree::leaf())) _s1;
  };

  /// _Combine_Node: receives partial results, combines with _result from final
  /// call.
  struct _Combine_Node {
    unsigned int _result;
  };

  using _Frame = std::variant<_Enter, _After_Node, _Combine_Node>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{n, t});
  /// Loopified mixed_recurse: _Enter -> _After_Node -> _Combine_Node.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      unsigned int n = _f.n;
      MemSafetyProbe23::tree t = std::move(_f.t);
      if (n <= 0) {
        _result = tree_sum(std::move(t));
      } else {
        unsigned int n_ = n - 1;
        if (std::holds_alternative<typename MemSafetyProbe23::tree::Leaf>(
                t.v_mut())) {
          _result = 0u;
        } else {
          auto &[d_a0, d_a1, d_a2] =
              std::get<typename MemSafetyProbe23::tree::Node>(t.v_mut());
          _stack.emplace_back(
              _After_Node{n_, tree::node(t, d_a1, tree::leaf())});
          _stack.emplace_back(_Enter{n_, std::move(*d_a2)});
        }
      }
    } else if (std::holds_alternative<_After_Node>(_frame)) {
      auto _f = std::move(std::get<_After_Node>(_frame));
      _stack.emplace_back(_Combine_Node{_result});
      _stack.emplace_back(_Enter{_f.n_, std::move(_f._s1)});
    } else {
      auto _f = std::move(std::get<_Combine_Node>(_frame));
      _result = (_result + _f._result);
    }
  }
  return _result;
}

/// TEST 8: Three-way split: function returns original tree AND
/// uses tree_size on children. Forces tree owned; exercises
/// the interplay between clone, move, and raw pointer in
/// continuation frames.
std::pair<MemSafetyProbe23::tree, unsigned int>
MemSafetyProbe23::annotate_sizes(const MemSafetyProbe23::tree &t) {
  if (std::holds_alternative<typename MemSafetyProbe23::tree::Leaf>(t.v())) {
    return std::make_pair(tree::leaf(), 0u);
  } else {
    const auto &[d_a0, d_a1, d_a2] =
        std::get<typename MemSafetyProbe23::tree::Node>(t.v());
    unsigned int sl = tree_size(*d_a0);
    unsigned int sr = tree_size(*d_a2);
    std::pair<MemSafetyProbe23::tree, unsigned int> pl = annotate_sizes(*d_a0);
    std::pair<MemSafetyProbe23::tree, unsigned int> pr = annotate_sizes(*d_a2);
    return std::make_pair(tree::node(pl.first, ((d_a1 + sl) + sr), pr.first),
                          ((pl.second + pr.second) + 1u));
  }
}
