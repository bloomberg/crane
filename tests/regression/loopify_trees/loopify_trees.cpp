#include "loopify_trees.h"

/// Consolidated UNIQUE tree algorithms - domain-specific tree operations.
uint64_t LoopifyTrees::tree_sum(
    const LoopifyTrees::tree<uint64_t>
        &t) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const LoopifyTrees::tree<uint64_t> *t;
  };

  /// _After_Node: saves [a0, a1], dispatches next recursive call.
  struct _After_Node {
    const LoopifyTrees::tree<uint64_t> *a0;
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
      const LoopifyTrees::tree<uint64_t> &t = *_f.t;
      if (std::holds_alternative<typename LoopifyTrees::tree<uint64_t>::Leaf>(
              t.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1, a2] =
            std::get<typename LoopifyTrees::tree<uint64_t>::Node>(t.v());
        _stack.emplace_back(_After_Node{a0.get(), a1});
        _stack.emplace_back(_Enter{a2.get()});
      }
    } else if (std::holds_alternative<_After_Node>(_frame)) {
      auto _f = std::move(std::get<_After_Node>(_frame));
      _stack.emplace_back(_Combine_Node{_result, _f.a1});
      _stack.emplace_back(_Enter{_f.a0});
    } else {
      auto _f = std::move(std::get<_Combine_Node>(_frame));
      _result = (_f.a1 + (_result + _f._result));
    }
  }
  return _result;
}

/// leaf_sum sums only leaf values.
uint64_t LoopifyTrees::leaf_sum(
    const LoopifyTrees::tree<uint64_t>
        &t) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const LoopifyTrees::tree<uint64_t> *t;
  };

  /// _After_Node: saves [a0], dispatches next recursive call.
  struct _After_Node {
    const LoopifyTrees::tree<uint64_t> *a0;
  };

  /// _After_Node_1: saves [a0], dispatches next recursive call.
  struct _After_Node_1 {
    const LoopifyTrees::tree<uint64_t> *a0;
  };

  /// _Combine_Node: receives partial results, combines with _result from final
  /// call.
  struct _Combine_Node {
    uint64_t _result;
  };

  /// _Combine_Node_1: receives partial results, combines with _result from
  /// final call.
  struct _Combine_Node_1 {
    uint64_t _result;
  };

  using _Frame = std::variant<_Enter, _After_Node, _After_Node_1, _Combine_Node,
                              _Combine_Node_1>;
  uint64_t _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&t});
  /// Loopified leaf_sum: _Enter -> _After_Node -> _After_Node_1 ->
  /// _Combine_Node -> _Combine_Node_1.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const LoopifyTrees::tree<uint64_t> &t = *_f.t;
      if (std::holds_alternative<typename LoopifyTrees::tree<uint64_t>::Leaf>(
              t.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1, a2] =
            std::get<typename LoopifyTrees::tree<uint64_t>::Node>(t.v());
        auto &&_sv = *a0;
        if (std::holds_alternative<typename LoopifyTrees::tree<uint64_t>::Leaf>(
                _sv.v())) {
          auto &&_sv = *a2;
          if (std::holds_alternative<
                  typename LoopifyTrees::tree<uint64_t>::Leaf>(_sv.v())) {
            _result = std::move(a1);
          } else {
            _stack.emplace_back(_After_Node{a0.get()});
            _stack.emplace_back(_Enter{a2.get()});
          }
        } else {
          _stack.emplace_back(_After_Node_1{a0.get()});
          _stack.emplace_back(_Enter{a2.get()});
        }
      }
    } else if (std::holds_alternative<_After_Node>(_frame)) {
      auto _f = std::move(std::get<_After_Node>(_frame));
      _stack.emplace_back(_Combine_Node{_result});
      _stack.emplace_back(_Enter{_f.a0});
    } else if (std::holds_alternative<_After_Node_1>(_frame)) {
      auto _f = std::move(std::get<_After_Node_1>(_frame));
      _stack.emplace_back(_Combine_Node_1{_result});
      _stack.emplace_back(_Enter{_f.a0});
    } else if (std::holds_alternative<_Combine_Node>(_frame)) {
      auto _f = std::move(std::get<_Combine_Node>(_frame));
      _result = (_result + _f._result);
    } else {
      auto _f = std::move(std::get<_Combine_Node_1>(_frame));
      _result = (_result + _f._result);
    }
  }
  return _result;
}

/// insert_bst BST insertion.
LoopifyTrees::tree<uint64_t> LoopifyTrees::insert_bst(
    uint64_t x,
    const LoopifyTrees::tree<uint64_t>
        &t) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const LoopifyTrees::tree<uint64_t> *t;
  };

  /// _Resume1: saves [a2, a1], resumes after recursive call with _result.
  struct _Resume1 {
    LoopifyTrees::tree<uint64_t> a2;
    uint64_t a1;
  };

  /// _Resume2: saves [a1, a0], resumes after recursive call with _result.
  struct _Resume2 {
    uint64_t a1;
    LoopifyTrees::tree<uint64_t> a0;
  };

  using _Frame = std::variant<_Enter, _Resume1, _Resume2>;
  LoopifyTrees::tree<uint64_t> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&t});
  /// Loopified insert_bst: _Enter -> _Resume1 -> _Resume2.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const LoopifyTrees::tree<uint64_t> &t = *_f.t;
      if (std::holds_alternative<typename LoopifyTrees::tree<uint64_t>::Leaf>(
              t.v())) {
        _result = tree<uint64_t>::node(tree<uint64_t>::leaf(), x,
                                       tree<uint64_t>::leaf());
      } else {
        const auto &[a0, a1, a2] =
            std::get<typename LoopifyTrees::tree<uint64_t>::Node>(t.v());
        if (x <= a1) {
          _stack.emplace_back(_Resume1{*a2, a1});
          _stack.emplace_back(_Enter{a0.get()});
        } else {
          _stack.emplace_back(_Resume2{a1, *a0});
          _stack.emplace_back(_Enter{a2.get()});
        }
      }
    } else if (std::holds_alternative<_Resume1>(_frame)) {
      auto _f = std::move(std::get<_Resume1>(_frame));
      _result = tree<uint64_t>::node(_result, _f.a1, _f.a2);
    } else {
      auto _f = std::move(std::get<_Resume2>(_frame));
      _result = tree<uint64_t>::node(_f.a0, _f.a1, _result);
    }
  }
  return _result;
}

/// count_paths t n counts root-to-leaf paths that sum to n.
uint64_t
LoopifyTrees::count_paths(const LoopifyTrees::tree<uint64_t> &t,
                          uint64_t n) { /// _Enter: captures varying parameters
                                        /// for each recursive call.

  struct _Enter {
    uint64_t n;
    const LoopifyTrees::tree<uint64_t> *t;
  };

  /// _After2: saves [_s0, a0], dispatches next recursive call.
  struct _After2 {
    decltype(UINT64_C(0)) _s0;
    const LoopifyTrees::tree<uint64_t> *a0;
  };

  /// _After4: saves [remaining, a0], dispatches next recursive call.
  struct _After4 {
    uint64_t remaining;
    const LoopifyTrees::tree<uint64_t> *a0;
  };

  /// _Combine1: receives partial results, combines with _result from final
  /// call.
  struct _Combine1 {
    uint64_t _result;
  };

  /// _Combine3: receives partial results, combines with _result from final
  /// call.
  struct _Combine3 {
    uint64_t _result;
  };

  using _Frame = std::variant<_Enter, _After2, _After4, _Combine1, _Combine3>;
  uint64_t _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{n, &t});
  /// Loopified count_paths: _Enter -> _After2 -> _After4 -> _Combine1 ->
  /// _Combine3.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      uint64_t n = _f.n;
      const LoopifyTrees::tree<uint64_t> &t = *_f.t;
      if (std::holds_alternative<typename LoopifyTrees::tree<uint64_t>::Leaf>(
              t.v())) {
        if (n == UINT64_C(0)) {
          _result = UINT64_C(1);
        } else {
          _result = UINT64_C(0);
        }
      } else {
        const auto &[a0, a1, a2] =
            std::get<typename LoopifyTrees::tree<uint64_t>::Node>(t.v());
        if (n <= a1) {
          if (n == a1) {
            _stack.emplace_back(_After2{UINT64_C(0), a0.get()});
            _stack.emplace_back(_Enter{UINT64_C(0), a2.get()});
          } else {
            _result = UINT64_C(0);
          }
        } else {
          uint64_t remaining = (((n - a1) > n ? 0 : (n - a1)));
          _stack.emplace_back(_After4{remaining, a0.get()});
          _stack.emplace_back(_Enter{remaining, a2.get()});
        }
      }
    } else if (std::holds_alternative<_After2>(_frame)) {
      auto _f = std::move(std::get<_After2>(_frame));
      _stack.emplace_back(_Combine1{_result});
      _stack.emplace_back(_Enter{_f._s0, _f.a0});
    } else if (std::holds_alternative<_After4>(_frame)) {
      auto _f = std::move(std::get<_After4>(_frame));
      _stack.emplace_back(_Combine3{_result});
      _stack.emplace_back(_Enter{_f.remaining, _f.a0});
    } else if (std::holds_alternative<_Combine1>(_frame)) {
      auto _f = std::move(std::get<_Combine1>(_frame));
      _result = (_result + _f._result);
    } else {
      auto _f = std::move(std::get<_Combine3>(_frame));
      _result = (_result + _f._result);
    }
  }
  return _result;
}

/// sum_of_max_branches sums maximum values along each path.
uint64_t
LoopifyTrees::sum_of_max_branches(const LoopifyTrees::tree<uint64_t> &t) {
  if (std::holds_alternative<typename LoopifyTrees::tree<uint64_t>::Leaf>(
          t.v())) {
    return UINT64_C(0);
  } else {
    const auto &[a0, a1, a2] =
        std::get<typename LoopifyTrees::tree<uint64_t>::Node>(t.v());
    uint64_t lsum = sum_of_max_branches(*a0);
    uint64_t rsum = sum_of_max_branches(*a2);
    return (a1 + (lsum <= rsum ? rsum : lsum));
  }
}

/// Helper: sum all values in a list of rose trees (processes both tree and
/// list levels in one recursive function to enable full loopification).
uint64_t LoopifyTrees::sum_rose_list_fuel(
    uint64_t fuel,
    const List<LoopifyTrees::rose>
        &cs) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<LoopifyTrees::rose> *cs;
    uint64_t fuel;
  };

  /// _After_RNode: saves [a10, f, a00], dispatches next recursive call.
  struct _After_RNode {
    const List<LoopifyTrees::rose> *a10;
    uint64_t f;
    uint64_t a00;
  };

  /// _Combine_RNode: receives partial results, combines with _result from final
  /// call.
  struct _Combine_RNode {
    uint64_t _result;
    uint64_t a00;
  };

  using _Frame = std::variant<_Enter, _After_RNode, _Combine_RNode>;
  uint64_t _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&cs, fuel});
  /// Loopified sum_rose_list_fuel: _Enter -> _After_RNode -> _Combine_RNode.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<LoopifyTrees::rose> &cs = *_f.cs;
      uint64_t fuel = _f.fuel;
      if (fuel <= 0) {
        _result = UINT64_C(0);
      } else {
        uint64_t f = fuel - 1;
        if (std::holds_alternative<typename List<LoopifyTrees::rose>::Nil>(
                cs.v())) {
          _result = UINT64_C(0);
        } else {
          const auto &[a0, a1] =
              std::get<typename List<LoopifyTrees::rose>::Cons>(cs.v());
          const auto &[a00, a10] =
              std::get<typename LoopifyTrees::rose::RNode>(a0.v());
          _stack.emplace_back(_After_RNode{a10.get(), f, a00});
          _stack.emplace_back(_Enter{a1.get(), f});
        }
      }
    } else if (std::holds_alternative<_After_RNode>(_frame)) {
      auto _f = std::move(std::get<_After_RNode>(_frame));
      _stack.emplace_back(_Combine_RNode{_result, _f.a00});
      _stack.emplace_back(_Enter{_f.a10, _f.f});
    } else {
      auto _f = std::move(std::get<_Combine_RNode>(_frame));
      _result = (_f.a00 + (_result + _f._result));
    }
  }
  return _result;
}

/// Helper: flatten a list of rose trees to a flat list of nats.
List<uint64_t> LoopifyTrees::flatten_rose_list_fuel(
    uint64_t fuel,
    const List<LoopifyTrees::rose>
        &cs) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<LoopifyTrees::rose> *cs;
    uint64_t fuel;
  };

  /// _After_RNode: saves [a10, f, a00], dispatches next recursive call.
  struct _After_RNode {
    const List<LoopifyTrees::rose> *a10;
    uint64_t f;
    uint64_t a00;
  };

  /// _Combine_RNode: receives partial results, combines with _result from final
  /// call.
  struct _Combine_RNode {
    List<uint64_t> _result;
    uint64_t a00;
  };

  using _Frame = std::variant<_Enter, _After_RNode, _Combine_RNode>;
  List<uint64_t> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&cs, fuel});
  /// Loopified flatten_rose_list_fuel: _Enter -> _After_RNode ->
  /// _Combine_RNode.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<LoopifyTrees::rose> &cs = *_f.cs;
      uint64_t fuel = _f.fuel;
      if (fuel <= 0) {
        _result = List<uint64_t>::nil();
      } else {
        uint64_t f = fuel - 1;
        if (std::holds_alternative<typename List<LoopifyTrees::rose>::Nil>(
                cs.v())) {
          _result = List<uint64_t>::nil();
        } else {
          const auto &[a0, a1] =
              std::get<typename List<LoopifyTrees::rose>::Cons>(cs.v());
          const auto &[a00, a10] =
              std::get<typename LoopifyTrees::rose::RNode>(a0.v());
          _stack.emplace_back(_After_RNode{a10.get(), f, a00});
          _stack.emplace_back(_Enter{a1.get(), f});
        }
      }
    } else if (std::holds_alternative<_After_RNode>(_frame)) {
      auto _f = std::move(std::get<_After_RNode>(_frame));
      _stack.emplace_back(_Combine_RNode{std::move(_result), _f.a00});
      _stack.emplace_back(_Enter{_f.a10, _f.f});
    } else {
      auto _f = std::move(std::get<_Combine_RNode>(_frame));
      _result = List<uint64_t>::cons(_f.a00, _result.app(_f._result));
    }
  }
  return _result;
}

/// Helper: compute maximum depth among a list of rose trees.
uint64_t
LoopifyTrees::depth_rose_list_fuel(uint64_t fuel,
                                   const List<LoopifyTrees::rose> &cs) {
  if (fuel <= 0) {
    return UINT64_C(0);
  } else {
    uint64_t f = fuel - 1;
    if (std::holds_alternative<typename List<LoopifyTrees::rose>::Nil>(
            cs.v())) {
      return UINT64_C(0);
    } else {
      const auto &[a0, a1] =
          std::get<typename List<LoopifyTrees::rose>::Cons>(cs.v());
      const auto &[a00, a10] =
          std::get<typename LoopifyTrees::rose::RNode>(a0.v());
      uint64_t d = (depth_rose_list_fuel(f, *a10) + 1);
      uint64_t rest_max = depth_rose_list_fuel(f, *a1);
      if (d <= rest_max) {
        return rest_max;
      } else {
        return d;
      }
    }
  }
}

/// tree_max t1 t2 element-wise maximum of two trees.
LoopifyTrees::tree<uint64_t> LoopifyTrees::tree_max(
    LoopifyTrees::tree<uint64_t> t1,
    LoopifyTrees::tree<uint64_t>
        t2) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    LoopifyTrees::tree<uint64_t> t2;
    LoopifyTrees::tree<uint64_t> t1;
  };

  /// _After_Node: saves [a00, a0, max_val], dispatches next recursive call.
  struct _After_Node {
    LoopifyTrees::tree<uint64_t> a00;
    LoopifyTrees::tree<uint64_t> a0;
    uint64_t max_val;
  };

  /// _Combine_Node: receives partial results, combines with _result from final
  /// call.
  struct _Combine_Node {
    LoopifyTrees::tree<uint64_t> _result;
    uint64_t max_val;
  };

  using _Frame = std::variant<_Enter, _After_Node, _Combine_Node>;
  LoopifyTrees::tree<uint64_t> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{t2, t1});
  /// Loopified tree_max: _Enter -> _After_Node -> _Combine_Node.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      LoopifyTrees::tree<uint64_t> t2 = std::move(_f.t2);
      LoopifyTrees::tree<uint64_t> t1 = std::move(_f.t1);
      if (std::holds_alternative<typename LoopifyTrees::tree<uint64_t>::Leaf>(
              t1.v_mut())) {
        if (std::holds_alternative<typename LoopifyTrees::tree<uint64_t>::Leaf>(
                t2.v_mut())) {
          _result = tree<uint64_t>::leaf();
        } else {
          _result = std::move(t2);
        }
      } else {
        auto &[a0, a1, a2] =
            std::get<typename LoopifyTrees::tree<uint64_t>::Node>(t1.v_mut());
        if (std::holds_alternative<typename LoopifyTrees::tree<uint64_t>::Leaf>(
                t2.v_mut())) {
          _result = std::move(t1);
        } else {
          auto &[a00, a10, a20] =
              std::get<typename LoopifyTrees::tree<uint64_t>::Node>(t2.v_mut());
          uint64_t max_val;
          if (a1 <= a10) {
            max_val = a10;
          } else {
            max_val = a1;
          }
          _stack.emplace_back(_After_Node{*a00, *a0, max_val});
          _stack.emplace_back(_Enter{std::move(*a20), std::move(*a2)});
        }
      }
    } else if (std::holds_alternative<_After_Node>(_frame)) {
      auto _f = std::move(std::get<_After_Node>(_frame));
      _stack.emplace_back(_Combine_Node{std::move(_result), _f.max_val});
      _stack.emplace_back(_Enter{std::move(_f.a00), std::move(_f.a0)});
    } else {
      auto _f = std::move(std::get<_Combine_Node>(_frame));
      _result = tree<uint64_t>::node(_result, _f.max_val, _f._result);
    }
  }
  return _result;
}

/// Helper: extract values from trees.
List<uint64_t> LoopifyTrees::extract_tree_values(
    const List<LoopifyTrees::tree<uint64_t>> &ts) {
  std::unique_ptr<List<uint64_t>> _head{};
  std::unique_ptr<List<uint64_t>> *_write = &_head;
  const List<LoopifyTrees::tree<uint64_t>> *_loop_ts = &ts;
  while (true) {
    if (std::holds_alternative<
            typename List<LoopifyTrees::tree<uint64_t>>::Nil>(_loop_ts->v())) {
      *_write = std::make_unique<List<uint64_t>>(List<uint64_t>::nil());
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename List<LoopifyTrees::tree<uint64_t>>::Cons>(
              _loop_ts->v());
      if (std::holds_alternative<typename LoopifyTrees::tree<uint64_t>::Leaf>(
              a0.v())) {
        _loop_ts = a1.get();
        continue;
      } else {
        const auto &[a00, a10, a20] =
            std::get<typename LoopifyTrees::tree<uint64_t>::Node>(a0.v());
        auto _cell = std::make_unique<List<uint64_t>>(
            typename List<uint64_t>::Cons(a10, nullptr));
        *_write = std::move(_cell);
        _write = &std::get<typename List<uint64_t>::Cons>((*_write)->v_mut()).l;
        _loop_ts = a1.get();
        continue;
      }
    }
  }
  return std::move(*_head);
}

/// Helper: extract children from trees.
List<LoopifyTrees::tree<uint64_t>> LoopifyTrees::extract_tree_children(
    const List<LoopifyTrees::tree<uint64_t>> &ts) {
  std::unique_ptr<List<LoopifyTrees::tree<uint64_t>>> _head{};
  std::unique_ptr<List<LoopifyTrees::tree<uint64_t>>> *_write = &_head;
  const List<LoopifyTrees::tree<uint64_t>> *_loop_ts = &ts;
  while (true) {
    if (std::holds_alternative<
            typename List<LoopifyTrees::tree<uint64_t>>::Nil>(_loop_ts->v())) {
      *_write = std::make_unique<List<LoopifyTrees::tree<uint64_t>>>(
          List<LoopifyTrees::tree<uint64_t>>::nil());
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename List<LoopifyTrees::tree<uint64_t>>::Cons>(
              _loop_ts->v());
      if (std::holds_alternative<typename LoopifyTrees::tree<uint64_t>::Leaf>(
              a0.v())) {
        _loop_ts = a1.get();
        continue;
      } else {
        const auto &[a00, a10, a20] =
            std::get<typename LoopifyTrees::tree<uint64_t>::Node>(a0.v());
        auto _cell = std::make_unique<List<LoopifyTrees::tree<uint64_t>>>(
            typename List<LoopifyTrees::tree<uint64_t>>::Cons(*a00, nullptr));
        auto _cell1 = std::make_unique<List<LoopifyTrees::tree<uint64_t>>>(
            typename List<LoopifyTrees::tree<uint64_t>>::Cons(*a20, nullptr));
        std::get<typename List<LoopifyTrees::tree<uint64_t>>::Cons>(
            _cell->v_mut())
            .l = std::move(_cell1);
        *_write = std::move(_cell);
        _write =
            &std::get<typename List<LoopifyTrees::tree<uint64_t>>::Cons>(
                 std::get<typename List<LoopifyTrees::tree<uint64_t>>::Cons>(
                     (*_write)->v_mut())
                     .l->v_mut())
                 .l;
        _loop_ts = a1.get();
        continue;
      }
    }
  }
  return std::move(*_head);
}

/// tree_levels t returns list of lists, one per level (breadth-first).
List<List<uint64_t>> LoopifyTrees::tree_levels_fuel(
    uint64_t fuel, const List<LoopifyTrees::tree<uint64_t>> &trees) {
  std::unique_ptr<List<List<uint64_t>>> _head{};
  std::unique_ptr<List<List<uint64_t>>> *_write = &_head;
  List<LoopifyTrees::tree<uint64_t>> _loop_trees = trees;
  uint64_t _loop_fuel = std::move(fuel);
  while (true) {
    if (_loop_fuel <= 0) {
      *_write =
          std::make_unique<List<List<uint64_t>>>(List<List<uint64_t>>::nil());
      break;
    } else {
      uint64_t f = _loop_fuel - 1;
      List<uint64_t> values = extract_tree_values(_loop_trees);
      if (std::holds_alternative<typename List<uint64_t>::Nil>(
              values.v_mut())) {
        *_write =
            std::make_unique<List<List<uint64_t>>>(List<List<uint64_t>>::nil());
        break;
      } else {
        List<LoopifyTrees::tree<uint64_t>> children =
            extract_tree_children(_loop_trees);
        auto _cell = std::make_unique<List<List<uint64_t>>>(
            typename List<List<uint64_t>>::Cons(values, nullptr));
        *_write = std::move(_cell);
        _write =
            &std::get<typename List<List<uint64_t>>::Cons>((*_write)->v_mut())
                 .l;
        _loop_trees = std::move(children);
        _loop_fuel = f;
        continue;
      }
    }
  }
  return std::move(*_head);
}

List<List<uint64_t>> LoopifyTrees::tree_levels(LoopifyTrees::tree<uint64_t> t) {
  return tree_levels_fuel(
      UINT64_C(100),
      List<LoopifyTrees::tree<uint64_t>>::cons(
          std::move(t), List<LoopifyTrees::tree<uint64_t>>::nil()));
}

/// count_nodes t returns tuple (node_count, sum_of_values).
std::pair<uint64_t, uint64_t>
LoopifyTrees::count_nodes(const LoopifyTrees::tree<uint64_t> &t) {
  if (std::holds_alternative<typename LoopifyTrees::tree<uint64_t>::Leaf>(
          t.v())) {
    return std::make_pair(UINT64_C(0), UINT64_C(0));
  } else {
    const auto &[a0, a1, a2] =
        std::get<typename LoopifyTrees::tree<uint64_t>::Node>(t.v());
    auto _cs = count_nodes(*a0);
    const uint64_t &lc = _cs.first;
    const uint64_t &ls = _cs.second;
    auto _cs1 = count_nodes(*a2);
    const uint64_t &rc = _cs1.first;
    const uint64_t &rs = _cs1.second;
    return std::make_pair(((lc + rc) + 1), (a1 + (ls + rs)));
  }
}

/// Helper: append two lists of lists.
List<List<uint64_t>>
LoopifyTrees::append_list_lists(const List<List<uint64_t>> &l1,
                                List<List<uint64_t>> l2) {
  std::unique_ptr<List<List<uint64_t>>> _head{};
  std::unique_ptr<List<List<uint64_t>>> *_write = &_head;
  List<List<uint64_t>> _loop_l2 = std::move(l2);
  const List<List<uint64_t>> *_loop_l1 = &l1;
  while (true) {
    if (std::holds_alternative<typename List<List<uint64_t>>::Nil>(
            _loop_l1->v())) {
      *_write = std::make_unique<List<List<uint64_t>>>(std::move(_loop_l2));
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename List<List<uint64_t>>::Cons>(_loop_l1->v());
      auto _cell = std::make_unique<List<List<uint64_t>>>(
          typename List<List<uint64_t>>::Cons(a0, nullptr));
      *_write = std::move(_cell);
      _write =
          &std::get<typename List<List<uint64_t>>::Cons>((*_write)->v_mut()).l;
      _loop_l1 = a1.get();
      continue;
    }
  }
  return std::move(*_head);
}

/// Helper: prepend value to all lists in a list of lists.
List<List<uint64_t>>
LoopifyTrees::map_cons_to_all(uint64_t x, const List<List<uint64_t>> &lsts) {
  std::unique_ptr<List<List<uint64_t>>> _head{};
  std::unique_ptr<List<List<uint64_t>>> *_write = &_head;
  const List<List<uint64_t>> *_loop_lsts = &lsts;
  while (true) {
    if (std::holds_alternative<typename List<List<uint64_t>>::Nil>(
            _loop_lsts->v())) {
      *_write =
          std::make_unique<List<List<uint64_t>>>(List<List<uint64_t>>::nil());
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename List<List<uint64_t>>::Cons>(_loop_lsts->v());
      auto _cell = std::make_unique<List<List<uint64_t>>>(
          typename List<List<uint64_t>>::Cons(List<uint64_t>::cons(x, a0),
                                              nullptr));
      *_write = std::move(_cell);
      _write =
          &std::get<typename List<List<uint64_t>>::Cons>((*_write)->v_mut()).l;
      _loop_lsts = a1.get();
      continue;
    }
  }
  return std::move(*_head);
}

/// paths t returns all root-to-leaf paths in tree.
List<List<uint64_t>> LoopifyTrees::paths(
    const LoopifyTrees::tree<uint64_t>
        &t) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const LoopifyTrees::tree<uint64_t> *t;
  };

  /// _After_Node: saves [a0, a1_0, a1_1], dispatches next recursive call.
  struct _After_Node {
    const LoopifyTrees::tree<uint64_t> *a0;
    uint64_t a1_0;
    uint64_t a1_1;
  };

  /// _Combine_Node: receives partial results, combines with _result from final
  /// call.
  struct _Combine_Node {
    List<List<uint64_t>> _result;
    uint64_t a1_0;
    uint64_t a1_1;
  };

  using _Frame = std::variant<_Enter, _After_Node, _Combine_Node>;
  List<List<uint64_t>> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&t});
  /// Loopified paths: _Enter -> _After_Node -> _Combine_Node.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const LoopifyTrees::tree<uint64_t> &t = *_f.t;
      if (std::holds_alternative<typename LoopifyTrees::tree<uint64_t>::Leaf>(
              t.v())) {
        _result = List<List<uint64_t>>::cons(List<uint64_t>::nil(),
                                             List<List<uint64_t>>::nil());
      } else {
        const auto &[a0, a1, a2] =
            std::get<typename LoopifyTrees::tree<uint64_t>::Node>(t.v());
        _stack.emplace_back(_After_Node{a0.get(), a1, a1});
        _stack.emplace_back(_Enter{a2.get()});
      }
    } else if (std::holds_alternative<_After_Node>(_frame)) {
      auto _f = std::move(std::get<_After_Node>(_frame));
      _stack.emplace_back(_Combine_Node{std::move(_result), _f.a1_0, _f.a1_1});
      _stack.emplace_back(_Enter{_f.a0});
    } else {
      auto _f = std::move(std::get<_Combine_Node>(_frame));
      _result = append_list_lists(map_cons_to_all(_f.a1_1, _result),
                                  map_cons_to_all(_f.a1_0, _f._result));
    }
  }
  return _result;
}

/// collect_sorted t collects and sorts all tree values.
List<uint64_t> LoopifyTrees::collect_unsorted(
    const LoopifyTrees::tree<uint64_t>
        &t) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const LoopifyTrees::tree<uint64_t> *t;
  };

  /// _After_Node: saves [a0, a1], dispatches next recursive call.
  struct _After_Node {
    const LoopifyTrees::tree<uint64_t> *a0;
    uint64_t a1;
  };

  /// _Combine_Node: receives partial results, combines with _result from final
  /// call.
  struct _Combine_Node {
    List<uint64_t> _result;
    uint64_t a1;
  };

  using _Frame = std::variant<_Enter, _After_Node, _Combine_Node>;
  List<uint64_t> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&t});
  /// Loopified collect_unsorted: _Enter -> _After_Node -> _Combine_Node.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const LoopifyTrees::tree<uint64_t> &t = *_f.t;
      if (std::holds_alternative<typename LoopifyTrees::tree<uint64_t>::Leaf>(
              t.v())) {
        _result = List<uint64_t>::nil();
      } else {
        const auto &[a0, a1, a2] =
            std::get<typename LoopifyTrees::tree<uint64_t>::Node>(t.v());
        _stack.emplace_back(_After_Node{a0.get(), a1});
        _stack.emplace_back(_Enter{a2.get()});
      }
    } else if (std::holds_alternative<_After_Node>(_frame)) {
      auto _f = std::move(std::get<_After_Node>(_frame));
      _stack.emplace_back(_Combine_Node{std::move(_result), _f.a1});
      _stack.emplace_back(_Enter{_f.a0});
    } else {
      auto _f = std::move(std::get<_Combine_Node>(_frame));
      _result = _result.app(List<uint64_t>::cons(_f.a1, _f._result));
    }
  }
  return _result;
}

/// Simple insertion sort for collect_sorted.
List<uint64_t> LoopifyTrees::insert_sorted(uint64_t x,
                                           const List<uint64_t> &l) {
  std::unique_ptr<List<uint64_t>> _head{};
  std::unique_ptr<List<uint64_t>> *_write = &_head;
  const List<uint64_t> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l->v())) {
      *_write = std::make_unique<List<uint64_t>>(
          List<uint64_t>::cons(x, List<uint64_t>::nil()));
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename List<uint64_t>::Cons>(_loop_l->v());
      if (x <= a0) {
        *_write = std::make_unique<List<uint64_t>>(
            List<uint64_t>::cons(x, List<uint64_t>::cons(a0, *a1)));
        break;
      } else {
        auto _cell = std::make_unique<List<uint64_t>>(
            typename List<uint64_t>::Cons(a0, nullptr));
        *_write = std::move(_cell);
        _write = &std::get<typename List<uint64_t>::Cons>((*_write)->v_mut()).l;
        _loop_l = a1.get();
        continue;
      }
    }
  }
  return std::move(*_head);
}

List<uint64_t> LoopifyTrees::sort_list(
    const List<uint64_t>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<uint64_t> *l;
  };

  /// _Resume_Cons: saves [a0], resumes after recursive call with _result.
  struct _Resume_Cons {
    uint64_t a0;
  };

  using _Frame = std::variant<_Enter, _Resume_Cons>;
  List<uint64_t> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l});
  /// Loopified sort_list: _Enter -> _Resume_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<uint64_t> &l = *_f.l;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
        _result = List<uint64_t>::nil();
      } else {
        const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
        _stack.emplace_back(_Resume_Cons{a0});
        _stack.emplace_back(_Enter{a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Resume_Cons>(_frame));
      _result = insert_sorted(_f.a0, _result);
    }
  }
  return _result;
}

List<uint64_t>
LoopifyTrees::collect_sorted(const LoopifyTrees::tree<uint64_t> &t) {
  return sort_list(collect_unsorted(t));
}

/// Helper: max of 4 values using nested max.
uint64_t LoopifyTrees::max4_impl(uint64_t a, uint64_t b, uint64_t c,
                                 uint64_t d) {
  if ((a <= b ? b : a) <= (c <= d ? d : c)) {
    if (c <= d) {
      return d;
    } else {
      return c;
    }
  } else {
    if (a <= b) {
      return b;
    } else {
      return a;
    }
  }
}

/// Helper: compute minimum of three values.
uint64_t LoopifyTrees::min3(uint64_t a, uint64_t b, uint64_t c) {
  if (a <= b) {
    if (a <= c) {
      return a;
    } else {
      return c;
    }
  } else {
    if (b <= c) {
      return b;
    } else {
      return c;
    }
  }
}

/// Helper: compute maximum of three values.
uint64_t LoopifyTrees::max3(uint64_t a, uint64_t b, uint64_t c) {
  if (b <= a) {
    if (c <= a) {
      return a;
    } else {
      return c;
    }
  } else {
    if (c <= b) {
      return b;
    } else {
      return c;
    }
  }
}

/// tree_min_max t finds minimum and maximum values in tree.
std::pair<uint64_t, uint64_t>
LoopifyTrees::tree_min_max(const LoopifyTrees::tree<uint64_t> &t) {
  if (std::holds_alternative<typename LoopifyTrees::tree<uint64_t>::Leaf>(
          t.v())) {
    return std::make_pair(UINT64_C(0), UINT64_C(0));
  } else {
    const auto &[a0, a1, a2] =
        std::get<typename LoopifyTrees::tree<uint64_t>::Node>(t.v());
    auto _cs = tree_min_max(*a0);
    const uint64_t &lmin = _cs.first;
    const uint64_t &lmax = _cs.second;
    auto _cs1 = tree_min_max(*a2);
    const uint64_t &rmin = _cs1.first;
    const uint64_t &rmax = _cs1.second;
    return std::make_pair(min3((lmin == UINT64_C(0) ? a1 : lmin),
                               (rmin == UINT64_C(0) ? a1 : rmin), a1),
                          max3(lmax, rmax, a1));
  }
}

/// all_paths_sum t sums all root-to-leaf path sums.
uint64_t LoopifyTrees::all_paths_sum(const LoopifyTrees::tree<uint64_t> &t) {
  auto sum_with_acc_impl =
      [](auto &_self_sum_with_acc, uint64_t acc,
         const LoopifyTrees::tree<uint64_t> &tree0) -> uint64_t {
    if (std::holds_alternative<typename LoopifyTrees::tree<uint64_t>::Leaf>(
            tree0.v())) {
      return acc;
    } else {
      const auto &[a0, a1, a2] =
          std::get<typename LoopifyTrees::tree<uint64_t>::Node>(tree0.v());
      uint64_t new_acc = (acc + a1);
      return (_self_sum_with_acc(_self_sum_with_acc, new_acc, *a0) +
              _self_sum_with_acc(_self_sum_with_acc, new_acc, *a2));
    }
  };
  auto sum_with_acc =
      [&](uint64_t acc, const LoopifyTrees::tree<uint64_t> &tree0) -> uint64_t {
    return sum_with_acc_impl(sum_with_acc_impl, acc, tree0);
  };
  return sum_with_acc(UINT64_C(0), t);
}

/// tree_contains x t checks if value exists in tree.
bool LoopifyTrees::tree_contains(
    uint64_t x,
    const LoopifyTrees::tree<uint64_t>
        &t) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const LoopifyTrees::tree<uint64_t> *t;
  };

  /// _After_Node: saves [a0, _s1], dispatches next recursive call.
  struct _After_Node {
    const LoopifyTrees::tree<uint64_t> *a0;
    decltype(std::declval<uint64_t &>() == std::declval<uint64_t &>()) _s1;
  };

  /// _Combine_Node: receives partial results, combines with _result from final
  /// call.
  struct _Combine_Node {
    bool _result;
    decltype(std::declval<uint64_t &>() == std::declval<uint64_t &>()) _s1;
  };

  using _Frame = std::variant<_Enter, _After_Node, _Combine_Node>;
  bool _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&t});
  /// Loopified tree_contains: _Enter -> _After_Node -> _Combine_Node.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const LoopifyTrees::tree<uint64_t> &t = *_f.t;
      if (std::holds_alternative<typename LoopifyTrees::tree<uint64_t>::Leaf>(
              t.v())) {
        _result = false;
      } else {
        const auto &[a0, a1, a2] =
            std::get<typename LoopifyTrees::tree<uint64_t>::Node>(t.v());
        _stack.emplace_back(_After_Node{a0.get(), x == a1});
        _stack.emplace_back(_Enter{a2.get()});
      }
    } else if (std::holds_alternative<_After_Node>(_frame)) {
      auto _f = std::move(std::get<_After_Node>(_frame));
      _stack.emplace_back(_Combine_Node{_result, _f._s1});
      _stack.emplace_back(_Enter{_f.a0});
    } else {
      auto _f = std::move(std::get<_Combine_Node>(_frame));
      _result = (_f._s1 || (_result || _f._result));
    }
  }
  return _result;
}
