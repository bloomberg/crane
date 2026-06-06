#include "mem_safety_probe23.h"

uint64_t MemSafetyProbe23::tree_sum(
    const MemSafetyProbe23::tree
        &t) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const MemSafetyProbe23::tree *t;
  };

  /// _After_Node: saves [a0, a1], dispatches next recursive call.
  struct _After_Node {
    const MemSafetyProbe23::tree *a0;
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
      const MemSafetyProbe23::tree &t = *_f.t;
      if (std::holds_alternative<typename MemSafetyProbe23::tree::Leaf>(
              t.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1, a2] =
            std::get<typename MemSafetyProbe23::tree::Node>(t.v());
        _stack.emplace_back(_After_Node{a0.get(), a1});
        _stack.emplace_back(_Enter{a2.get()});
      }
    } else if (std::holds_alternative<_After_Node>(_frame)) {
      auto _f = std::move(std::get<_After_Node>(_frame));
      _stack.emplace_back(_Combine_Node{std::move(_result), _f.a1});
      _stack.emplace_back(_Enter{_f.a0});
    } else {
      auto _f = std::move(std::get<_Combine_Node>(_frame));
      _result = ((std::move(_result) + _f.a1) + std::move(_f._result));
    }
  }
  return _result;
}

uint64_t MemSafetyProbe23::tree_size(
    const MemSafetyProbe23::tree
        &t) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const MemSafetyProbe23::tree *t;
  };

  /// _After_Node: saves [a0, _s1], dispatches next recursive call.
  struct _After_Node {
    const MemSafetyProbe23::tree *a0;
    std::decay_t<decltype(UINT64_C(1))> _s1;
  };

  /// _Combine_Node: receives partial results, combines with _result from final
  /// call.
  struct _Combine_Node {
    uint64_t _result;
    std::decay_t<decltype(UINT64_C(1))> _s1;
  };

  using _Frame = std::variant<_Enter, _After_Node, _Combine_Node>;
  uint64_t _result{};
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
        _result = UINT64_C(1);
      } else {
        const auto &[a0, a1, a2] =
            std::get<typename MemSafetyProbe23::tree::Node>(t.v());
        _stack.emplace_back(_After_Node{a0.get(), UINT64_C(1)});
        _stack.emplace_back(_Enter{a2.get()});
      }
    } else if (std::holds_alternative<_After_Node>(_frame)) {
      auto _f = std::move(std::get<_After_Node>(_frame));
      _stack.emplace_back(_Combine_Node{std::move(_result), _f._s1});
      _stack.emplace_back(_Enter{_f.a0});
    } else {
      auto _f = std::move(std::get<_Combine_Node>(_frame));
      _result = ((_f._s1 + std::move(_result)) + std::move(_f._result));
    }
  }
  return _result;
}

/// TEST 1: Return the ORIGINAL tree alongside recursive child processing.
/// t escapes because it is returned. Recursive calls on l and r (children).
/// Loopifier must handle: owned param + pointer-safe children.
std::pair<MemSafetyProbe23::tree, uint64_t> MemSafetyProbe23::sum_with_original(
    MemSafetyProbe23::tree
        t) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    MemSafetyProbe23::tree t;
  };

  /// _Cont_Node: saves [a1, a2, t], resumes after recursive call, then
  /// processes rest.
  struct _Cont_Node {
    uint64_t a1;
    std::shared_ptr<MemSafetyProbe23::tree> a2;
    MemSafetyProbe23::tree t;
  };

  /// _Cont_Node_1: saves [a1, pl, t], resumes after recursive call, then
  /// processes rest.
  struct _Cont_Node_1 {
    uint64_t a1;
    std::pair<MemSafetyProbe23::tree, uint64_t> pl;
    MemSafetyProbe23::tree t;
  };

  using _Frame = std::variant<_Enter, _Cont_Node, _Cont_Node_1>;
  std::pair<MemSafetyProbe23::tree, uint64_t> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{std::move(t)});
  /// Loopified sum_with_original: _Enter -> _Cont_Node -> _Cont_Node_1.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      MemSafetyProbe23::tree t = std::move(_f.t);
      if (std::holds_alternative<typename MemSafetyProbe23::tree::Leaf>(
              t.v_mut())) {
        _result = std::make_pair(tree::leaf(), UINT64_C(0));
      } else {
        auto &[a0, a1, a2] =
            std::get<typename MemSafetyProbe23::tree::Node>(t.v_mut());
        _stack.emplace_back(_Cont_Node{a1, a2, t});
        _stack.emplace_back(_Enter{*a0});
      }
    } else if (std::holds_alternative<_Cont_Node>(_frame)) {
      auto _f = std::move(std::get<_Cont_Node>(_frame));
      uint64_t a1 = _f.a1;
      std::shared_ptr<MemSafetyProbe23::tree> a2 = std::move(_f.a2);
      MemSafetyProbe23::tree t = std::move(_f.t);
      std::pair<MemSafetyProbe23::tree, uint64_t> pl = std::move(_result);
      _stack.emplace_back(_Cont_Node_1{a1, std::move(pl), std::move(t)});
      _stack.emplace_back(_Enter{*a2});
    } else {
      auto _f = std::move(std::get<_Cont_Node_1>(_frame));
      uint64_t a1 = _f.a1;
      std::pair<MemSafetyProbe23::tree, uint64_t> pl = std::move(_f.pl);
      MemSafetyProbe23::tree t = std::move(_f.t);
      std::pair<MemSafetyProbe23::tree, uint64_t> pr = std::move(_result);
      _result =
          std::make_pair(std::move(t), ((std::move(pl).second + std::move(a1)) +
                                        std::move(pr).second));
    }
  }
  return _result;
}

/// TEST 2: Return a PAIR of the original tree and a transformed copy.
/// Forces tree to be owned; two recursive calls on children.
std::pair<MemSafetyProbe23::tree, MemSafetyProbe23::tree>
MemSafetyProbe23::dup_and_double(
    MemSafetyProbe23::tree
        t) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    MemSafetyProbe23::tree t;
  };

  /// _Cont_Node: saves [a1, a2, t], resumes after recursive call, then
  /// processes rest.
  struct _Cont_Node {
    uint64_t a1;
    std::shared_ptr<MemSafetyProbe23::tree> a2;
    MemSafetyProbe23::tree t;
  };

  /// _Cont_Node_1: saves [a1, pl, t], resumes after recursive call, then
  /// processes rest.
  struct _Cont_Node_1 {
    uint64_t a1;
    std::pair<MemSafetyProbe23::tree, MemSafetyProbe23::tree> pl;
    MemSafetyProbe23::tree t;
  };

  using _Frame = std::variant<_Enter, _Cont_Node, _Cont_Node_1>;
  std::pair<MemSafetyProbe23::tree, MemSafetyProbe23::tree> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{std::move(t)});
  /// Loopified dup_and_double: _Enter -> _Cont_Node -> _Cont_Node_1.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      MemSafetyProbe23::tree t = std::move(_f.t);
      if (std::holds_alternative<typename MemSafetyProbe23::tree::Leaf>(
              t.v_mut())) {
        _result = std::make_pair(tree::leaf(), tree::leaf());
      } else {
        auto &[a0, a1, a2] =
            std::get<typename MemSafetyProbe23::tree::Node>(t.v_mut());
        _stack.emplace_back(_Cont_Node{a1, a2, t});
        _stack.emplace_back(_Enter{*a0});
      }
    } else if (std::holds_alternative<_Cont_Node>(_frame)) {
      auto _f = std::move(std::get<_Cont_Node>(_frame));
      uint64_t a1 = _f.a1;
      std::shared_ptr<MemSafetyProbe23::tree> a2 = std::move(_f.a2);
      MemSafetyProbe23::tree t = std::move(_f.t);
      std::pair<MemSafetyProbe23::tree, MemSafetyProbe23::tree> pl =
          std::move(_result);
      _stack.emplace_back(_Cont_Node_1{a1, std::move(pl), std::move(t)});
      _stack.emplace_back(_Enter{*a2});
    } else {
      auto _f = std::move(std::get<_Cont_Node_1>(_frame));
      uint64_t a1 = _f.a1;
      std::pair<MemSafetyProbe23::tree, MemSafetyProbe23::tree> pl =
          std::move(_f.pl);
      MemSafetyProbe23::tree t = std::move(_f.t);
      std::pair<MemSafetyProbe23::tree, MemSafetyProbe23::tree> pr =
          std::move(_result);
      _result =
          std::make_pair(std::move(t), tree::node(std::move(pl).second,
                                                  (std::move(a1) * UINT64_C(2)),
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
MemSafetyProbe23::collect_children(
    const MemSafetyProbe23::tree
        &t) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const MemSafetyProbe23::tree *t;
  };

  /// _Cont_Node: saves [a0, a1, a2], resumes after recursive call, then
  /// processes rest.
  struct _Cont_Node {
    std::shared_ptr<MemSafetyProbe23::tree> a0;
    uint64_t a1;
    const MemSafetyProbe23::tree *a2;
  };

  /// _Cont_Node_1: saves [a0, a1, a2, pl], resumes after recursive call, then
  /// processes rest.
  struct _Cont_Node_1 {
    std::shared_ptr<MemSafetyProbe23::tree> a0;
    uint64_t a1;
    const MemSafetyProbe23::tree *a2;
    std::pair<std::pair<MemSafetyProbe23::tree, MemSafetyProbe23::tree>,
              uint64_t>
        pl;
  };

  using _Frame = std::variant<_Enter, _Cont_Node, _Cont_Node_1>;
  std::pair<std::pair<MemSafetyProbe23::tree, MemSafetyProbe23::tree>, uint64_t>
      _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&t});
  /// Loopified collect_children: _Enter -> _Cont_Node -> _Cont_Node_1.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const MemSafetyProbe23::tree &t = *_f.t;
      if (std::holds_alternative<typename MemSafetyProbe23::tree::Leaf>(
              t.v())) {
        _result = std::make_pair(std::make_pair(tree::leaf(), tree::leaf()),
                                 UINT64_C(0));
      } else {
        const auto &[a0, a1, a2] =
            std::get<typename MemSafetyProbe23::tree::Node>(t.v());
        _stack.emplace_back(_Cont_Node{a0, a1, a2.get()});
        _stack.emplace_back(_Enter{a0.get()});
      }
    } else if (std::holds_alternative<_Cont_Node>(_frame)) {
      auto _f = std::move(std::get<_Cont_Node>(_frame));
      std::shared_ptr<MemSafetyProbe23::tree> a0 = std::move(_f.a0);
      uint64_t a1 = _f.a1;
      const MemSafetyProbe23::tree &a2 = *_f.a2;
      std::pair<std::pair<MemSafetyProbe23::tree, MemSafetyProbe23::tree>,
                uint64_t>
          pl = std::move(_result);
      _stack.emplace_back(_Cont_Node_1{std::move(a0), a1, &a2, std::move(pl)});
      _stack.emplace_back(_Enter{&a2});
    } else {
      auto _f = std::move(std::get<_Cont_Node_1>(_frame));
      std::shared_ptr<MemSafetyProbe23::tree> a0 = std::move(_f.a0);
      uint64_t a1 = _f.a1;
      const MemSafetyProbe23::tree &a2 = *_f.a2;
      std::pair<std::pair<MemSafetyProbe23::tree, MemSafetyProbe23::tree>,
                uint64_t>
          pl = std::move(_f.pl);
      std::pair<std::pair<MemSafetyProbe23::tree, MemSafetyProbe23::tree>,
                uint64_t>
          pr = std::move(_result);
      uint64_t s =
          (([&]() -> uint64_t {
             std::pair<MemSafetyProbe23::tree, MemSafetyProbe23::tree> p =
                 std::move(pl.first);
             uint64_t n = std::move(pl.second);
             MemSafetyProbe23::tree _x = std::move(p.first);
             MemSafetyProbe23::tree _x0 = std::move(p.second);
             return n;
           }() + a1) +
               [&]() -> uint64_t {
            std::pair<MemSafetyProbe23::tree, MemSafetyProbe23::tree> p =
                std::move(pr.first);
            uint64_t n = std::move(pr.second);
            MemSafetyProbe23::tree _x = std::move(p.first);
            MemSafetyProbe23::tree _x0 = std::move(p.second);
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
std::pair<MemSafetyProbe23::tree, uint64_t> MemSafetyProbe23::sum_with_acc(
    const MemSafetyProbe23::tree &t,
    uint64_t
        acc) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    uint64_t acc;
    const MemSafetyProbe23::tree *t;
  };

  /// _Cont_Node: saves [a1, a2], resumes after recursive call, then processes
  /// rest.
  struct _Cont_Node {
    uint64_t a1;
    const MemSafetyProbe23::tree *a2;
  };

  /// _Cont_Node_1: saves [a1, pl], resumes after recursive call, then processes
  /// rest.
  struct _Cont_Node_1 {
    uint64_t a1;
    std::pair<MemSafetyProbe23::tree, uint64_t> pl;
  };

  using _Frame = std::variant<_Enter, _Cont_Node, _Cont_Node_1>;
  std::pair<MemSafetyProbe23::tree, uint64_t> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{acc, &t});
  /// Loopified sum_with_acc: _Enter -> _Cont_Node -> _Cont_Node_1.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      uint64_t acc = _f.acc;
      const MemSafetyProbe23::tree &t = *_f.t;
      if (std::holds_alternative<typename MemSafetyProbe23::tree::Leaf>(
              t.v())) {
        _result = std::make_pair(tree::leaf(), acc);
      } else {
        const auto &[a0, a1, a2] =
            std::get<typename MemSafetyProbe23::tree::Node>(t.v());
        _stack.emplace_back(_Cont_Node{a1, a2.get()});
        _stack.emplace_back(_Enter{(acc + a1), a0.get()});
      }
    } else if (std::holds_alternative<_Cont_Node>(_frame)) {
      auto _f = std::move(std::get<_Cont_Node>(_frame));
      uint64_t a1 = _f.a1;
      const MemSafetyProbe23::tree &a2 = *_f.a2;
      std::pair<MemSafetyProbe23::tree, uint64_t> pl = std::move(_result);
      _stack.emplace_back(_Cont_Node_1{a1, std::move(pl)});
      _stack.emplace_back(_Enter{pl.second, &a2});
    } else {
      auto _f = std::move(std::get<_Cont_Node_1>(_frame));
      uint64_t a1 = _f.a1;
      std::pair<MemSafetyProbe23::tree, uint64_t> pl = std::move(_f.pl);
      std::pair<MemSafetyProbe23::tree, uint64_t> pr = std::move(_result);
      _result = std::make_pair(tree::node(std::move(pl).first, a1, pr.first),
                               pr.second);
    }
  }
  return _result;
}

/// TEST 5: Function using tree_sum on children INSIDE the same
/// expression as recursive calls. Tests that child pointers remain
/// valid when other operations happen on the same tree.
std::pair<uint64_t, uint64_t> MemSafetyProbe23::interleaved_ops(
    const MemSafetyProbe23::tree
        &t) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const MemSafetyProbe23::tree *t;
  };

  /// _Cont_Node: saves [a1, a2, sl, sr], resumes after recursive call, then
  /// processes rest.
  struct _Cont_Node {
    uint64_t a1;
    const MemSafetyProbe23::tree *a2;
    uint64_t sl;
    uint64_t sr;
  };

  /// _Cont_Node_1: saves [a1, pl, sl, sr], resumes after recursive call, then
  /// processes rest.
  struct _Cont_Node_1 {
    uint64_t a1;
    std::pair<uint64_t, uint64_t> pl;
    uint64_t sl;
    uint64_t sr;
  };

  using _Frame = std::variant<_Enter, _Cont_Node, _Cont_Node_1>;
  std::pair<uint64_t, uint64_t> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&t});
  /// Loopified interleaved_ops: _Enter -> _Cont_Node -> _Cont_Node_1.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const MemSafetyProbe23::tree &t = *_f.t;
      if (std::holds_alternative<typename MemSafetyProbe23::tree::Leaf>(
              t.v())) {
        _result = std::make_pair(UINT64_C(0), UINT64_C(0));
      } else {
        const auto &[a0, a1, a2] =
            std::get<typename MemSafetyProbe23::tree::Node>(t.v());
        uint64_t sl = tree_sum(*a0);
        uint64_t sr = tree_sum(*a2);
        _stack.emplace_back(_Cont_Node{a1, a2.get(), sl, sr});
        _stack.emplace_back(_Enter{a0.get()});
      }
    } else if (std::holds_alternative<_Cont_Node>(_frame)) {
      auto _f = std::move(std::get<_Cont_Node>(_frame));
      uint64_t a1 = _f.a1;
      const MemSafetyProbe23::tree &a2 = *_f.a2;
      uint64_t sl = _f.sl;
      uint64_t sr = _f.sr;
      std::pair<uint64_t, uint64_t> pl = std::move(_result);
      _stack.emplace_back(_Cont_Node_1{a1, pl, sl, sr});
      _stack.emplace_back(_Enter{&a2});
    } else {
      auto _f = std::move(std::get<_Cont_Node_1>(_frame));
      uint64_t a1 = _f.a1;
      std::pair<uint64_t, uint64_t> pl = std::move(_f.pl);
      uint64_t sl = _f.sl;
      uint64_t sr = _f.sr;
      std::pair<uint64_t, uint64_t> pr = std::move(_result);
      _result = std::make_pair(
          ((sl + a1) + sr), ((std::move(pl).first + a1) + std::move(pr).first));
    }
  }
  return _result;
}

/// TEST 6: Nested tree type — tree of trees. Tests clone correctness
/// for deeply nested value types.
uint64_t MemSafetyProbe23::flatten_tree_of_trees(
    const MemSafetyProbe23::tree &t,
    MemSafetyProbe23::tree inner) { /// _Enter: captures varying parameters for
                                    /// each recursive call.

  struct _Enter {
    MemSafetyProbe23::tree inner;
    const MemSafetyProbe23::tree *t;
  };

  /// _After_Node: saves [_s0, a0], dispatches next recursive call.
  struct _After_Node {
    MemSafetyProbe23::tree _s0;
    const MemSafetyProbe23::tree *a0;
  };

  /// _Combine_Node: receives partial results, combines with _result from final
  /// call.
  struct _Combine_Node {
    uint64_t _result;
  };

  using _Frame = std::variant<_Enter, _After_Node, _Combine_Node>;
  uint64_t _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{std::move(inner), &t});
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
        const auto &[a0, a1, a2] =
            std::get<typename MemSafetyProbe23::tree::Node>(t.v());
        MemSafetyProbe23::tree new_inner = tree::node(inner, a1, tree::leaf());
        _stack.emplace_back(
            _After_Node{std::move(std::move(new_inner)), a0.get()});
        _stack.emplace_back(_Enter{std::move(inner), a2.get()});
      }
    } else if (std::holds_alternative<_After_Node>(_frame)) {
      auto _f = std::move(std::get<_After_Node>(_frame));
      _stack.emplace_back(_Combine_Node{std::move(_result)});
      _stack.emplace_back(_Enter{std::move(_f._s0), _f.a0});
    } else {
      auto _f = std::move(std::get<_Combine_Node>(_frame));
      _result = (std::move(_result) + std::move(_f._result));
    }
  }
  return _result;
}

/// TEST 7: Two recursive calls where one takes a CONSTRUCTED tree
/// with t embedded AND another takes a child of t.
/// Forces t to NOT be pointer-safe. The After frame saves
/// state for the child-based call.
uint64_t MemSafetyProbe23::mixed_recurse(
    MemSafetyProbe23::tree t,
    uint64_t
        n) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    uint64_t n;
    MemSafetyProbe23::tree t;
  };

  /// _After_Node: saves [n_, _s1], dispatches next recursive call.
  struct _After_Node {
    uint64_t n_;
    std::decay_t<decltype(tree::node(std::declval<MemSafetyProbe23::tree &>(),
                                     std::move(std::declval<uint64_t &>()),
                                     tree::leaf()))>
        _s1;
  };

  /// _Combine_Node: receives partial results, combines with _result from final
  /// call.
  struct _Combine_Node {
    uint64_t _result;
  };

  using _Frame = std::variant<_Enter, _After_Node, _Combine_Node>;
  uint64_t _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{n, std::move(t)});
  /// Loopified mixed_recurse: _Enter -> _After_Node -> _Combine_Node.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      uint64_t n = _f.n;
      MemSafetyProbe23::tree t = std::move(_f.t);
      if (n <= 0) {
        _result = tree_sum(std::move(t));
      } else {
        uint64_t n_ = n - 1;
        if (std::holds_alternative<typename MemSafetyProbe23::tree::Leaf>(
                t.v_mut())) {
          _result = UINT64_C(0);
        } else {
          auto &[a0, a1, a2] =
              std::get<typename MemSafetyProbe23::tree::Node>(t.v_mut());
          _stack.emplace_back(
              _After_Node{n_, tree::node(t, std::move(a1), tree::leaf())});
          _stack.emplace_back(_Enter{n_, *a2});
        }
      }
    } else if (std::holds_alternative<_After_Node>(_frame)) {
      auto _f = std::move(std::get<_After_Node>(_frame));
      _stack.emplace_back(_Combine_Node{std::move(_result)});
      _stack.emplace_back(_Enter{_f.n_, std::move(_f._s1)});
    } else {
      auto _f = std::move(std::get<_Combine_Node>(_frame));
      _result = (std::move(_result) + std::move(_f._result));
    }
  }
  return _result;
}

/// TEST 8: Three-way split: function returns original tree AND
/// uses tree_size on children. Forces tree owned; exercises
/// the interplay between clone, move, and raw pointer in
/// continuation frames.
std::pair<MemSafetyProbe23::tree, uint64_t> MemSafetyProbe23::annotate_sizes(
    const MemSafetyProbe23::tree
        &t) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const MemSafetyProbe23::tree *t;
  };

  /// _Cont_Node: saves [a1, a2, sl, sr], resumes after recursive call, then
  /// processes rest.
  struct _Cont_Node {
    uint64_t a1;
    const MemSafetyProbe23::tree *a2;
    uint64_t sl;
    uint64_t sr;
  };

  /// _Cont_Node_1: saves [a1, pl, sl, sr], resumes after recursive call, then
  /// processes rest.
  struct _Cont_Node_1 {
    uint64_t a1;
    std::pair<MemSafetyProbe23::tree, uint64_t> pl;
    uint64_t sl;
    uint64_t sr;
  };

  using _Frame = std::variant<_Enter, _Cont_Node, _Cont_Node_1>;
  std::pair<MemSafetyProbe23::tree, uint64_t> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&t});
  /// Loopified annotate_sizes: _Enter -> _Cont_Node -> _Cont_Node_1.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const MemSafetyProbe23::tree &t = *_f.t;
      if (std::holds_alternative<typename MemSafetyProbe23::tree::Leaf>(
              t.v())) {
        _result = std::make_pair(tree::leaf(), UINT64_C(0));
      } else {
        const auto &[a0, a1, a2] =
            std::get<typename MemSafetyProbe23::tree::Node>(t.v());
        uint64_t sl = tree_size(*a0);
        uint64_t sr = tree_size(*a2);
        _stack.emplace_back(_Cont_Node{a1, a2.get(), sl, sr});
        _stack.emplace_back(_Enter{a0.get()});
      }
    } else if (std::holds_alternative<_Cont_Node>(_frame)) {
      auto _f = std::move(std::get<_Cont_Node>(_frame));
      uint64_t a1 = _f.a1;
      const MemSafetyProbe23::tree &a2 = *_f.a2;
      uint64_t sl = _f.sl;
      uint64_t sr = _f.sr;
      std::pair<MemSafetyProbe23::tree, uint64_t> pl = std::move(_result);
      _stack.emplace_back(_Cont_Node_1{a1, std::move(pl), sl, sr});
      _stack.emplace_back(_Enter{&a2});
    } else {
      auto _f = std::move(std::get<_Cont_Node_1>(_frame));
      uint64_t a1 = _f.a1;
      std::pair<MemSafetyProbe23::tree, uint64_t> pl = std::move(_f.pl);
      uint64_t sl = _f.sl;
      uint64_t sr = _f.sr;
      std::pair<MemSafetyProbe23::tree, uint64_t> pr = std::move(_result);
      _result = std::make_pair(tree::node(pl.first, ((a1 + sl) + sr), pr.first),
                               ((pl.second + pr.second) + UINT64_C(1)));
    }
  }
  return _result;
}
