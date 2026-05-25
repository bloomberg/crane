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
      _result = (_f.a1 + (std::move(_result) + std::move(_f._result)));
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
      _result = (std::move(_result) + std::move(_f._result));
    } else {
      auto _f = std::move(std::get<_Combine_Node_1>(_frame));
      _result = (std::move(_result) + std::move(_f._result));
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
    std::decay_t<decltype(UINT64_C(0))> _s0;
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
      _result = (std::move(_result) + std::move(_f._result));
    } else {
      auto _f = std::move(std::get<_Combine3>(_frame));
      _result = (std::move(_result) + std::move(_f._result));
    }
  }
  return _result;
}

/// sum_of_max_branches sums maximum values along each path.
uint64_t LoopifyTrees::sum_of_max_branches(
    const LoopifyTrees::tree<uint64_t>
        &t) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const LoopifyTrees::tree<uint64_t> *t;
  };

  /// _Cont_Node: saves [a1, a2], resumes after recursive call, then processes
  /// rest.
  struct _Cont_Node {
    uint64_t a1;
    const LoopifyTrees::tree<uint64_t> *a2;
  };

  /// _Cont_Node_1: saves [a1, lsum], resumes after recursive call, then
  /// processes rest.
  struct _Cont_Node_1 {
    uint64_t a1;
    uint64_t lsum;
  };

  using _Frame = std::variant<_Enter, _Cont_Node, _Cont_Node_1>;
  uint64_t _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&t});
  /// Loopified sum_of_max_branches: _Enter -> _Cont_Node -> _Cont_Node_1.
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
        _stack.emplace_back(_Cont_Node{a1, a2.get()});
        _stack.emplace_back(_Enter{a0.get()});
      }
    } else if (std::holds_alternative<_Cont_Node>(_frame)) {
      auto _f = std::move(std::get<_Cont_Node>(_frame));
      uint64_t a1 = _f.a1;
      const LoopifyTrees::tree<uint64_t> &a2 = *_f.a2;
      uint64_t lsum = _result;
      _stack.emplace_back(_Cont_Node_1{a1, lsum});
      _stack.emplace_back(_Enter{&a2});
    } else {
      auto _f = std::move(std::get<_Cont_Node_1>(_frame));
      uint64_t a1 = _f.a1;
      uint64_t lsum = _f.lsum;
      uint64_t rsum = _result;
      _result = (a1 + (lsum <= rsum ? rsum : lsum));
    }
  }
  return _result;
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
      _result = (_f.a00 + (std::move(_result) + std::move(_f._result)));
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
      _result = List<uint64_t>::cons(
          _f.a00, std::move(_result).app(std::move(_f._result)));
    }
  }
  return _result;
}

/// Helper: compute maximum depth among a list of rose trees.
uint64_t LoopifyTrees::depth_rose_list_fuel(
    uint64_t fuel,
    const List<LoopifyTrees::rose>
        &cs) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<LoopifyTrees::rose> *cs;
    uint64_t fuel;
  };

  /// _Cont_RNode: saves [a1, f], resumes after recursive call, then processes
  /// rest.
  struct _Cont_RNode {
    const List<LoopifyTrees::rose> *a1;
    uint64_t f;
  };

  /// _Cont_RNode_1: saves [d], resumes after recursive call, then processes
  /// rest.
  struct _Cont_RNode_1 {
    uint64_t d;
  };

  using _Frame = std::variant<_Enter, _Cont_RNode, _Cont_RNode_1>;
  uint64_t _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&cs, fuel});
  /// Loopified depth_rose_list_fuel: _Enter -> _Cont_RNode -> _Cont_RNode_1.
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
          _stack.emplace_back(_Cont_RNode{a1.get(), f});
          _stack.emplace_back(_Enter{a10.get(), f});
        }
      }
    } else if (std::holds_alternative<_Cont_RNode>(_frame)) {
      auto _f = std::move(std::get<_Cont_RNode>(_frame));
      const List<LoopifyTrees::rose> &a1 = *_f.a1;
      uint64_t f = _f.f;
      uint64_t d = (_result + 1);
      _stack.emplace_back(_Cont_RNode_1{d});
      _stack.emplace_back(_Enter{&a1, f});
    } else {
      auto _f = std::move(std::get<_Cont_RNode_1>(_frame));
      uint64_t d = _f.d;
      uint64_t rest_max = _result;
      if (d <= rest_max) {
        _result = std::move(rest_max);
      } else {
        _result = std::move(d);
      }
    }
  }
  return _result;
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
      _result = tree<uint64_t>::node(std::move(_result), _f.max_val,
                                     std::move(_f._result));
    }
  }
  return _result;
}

/// Helper: extract values from trees.
List<uint64_t> LoopifyTrees::extract_tree_values(
    const List<LoopifyTrees::tree<uint64_t>>
        &ts) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<LoopifyTrees::tree<uint64_t>> *ts;
  };

  /// _Resume_Node: saves [a10], resumes after recursive call with _result.
  struct _Resume_Node {
    uint64_t a10;
  };

  using _Frame = std::variant<_Enter, _Resume_Node>;
  List<uint64_t> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&ts});
  /// Loopified extract_tree_values: _Enter -> _Resume_Node.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<LoopifyTrees::tree<uint64_t>> &ts = *_f.ts;
      if (std::holds_alternative<
              typename List<LoopifyTrees::tree<uint64_t>>::Nil>(ts.v())) {
        _result = List<uint64_t>::nil();
      } else {
        const auto &[a0, a1] =
            std::get<typename List<LoopifyTrees::tree<uint64_t>>::Cons>(ts.v());
        if (std::holds_alternative<typename LoopifyTrees::tree<uint64_t>::Leaf>(
                a0.v())) {
          _stack.emplace_back(_Enter{a1.get()});
        } else {
          const auto &[a00, a10, a20] =
              std::get<typename LoopifyTrees::tree<uint64_t>::Node>(a0.v());
          _stack.emplace_back(_Resume_Node{a10});
          _stack.emplace_back(_Enter{a1.get()});
        }
      }
    } else {
      auto _f = std::move(std::get<_Resume_Node>(_frame));
      _result = List<uint64_t>::cons(_f.a10, _result);
    }
  }
  return _result;
}

/// Helper: extract children from trees.
List<LoopifyTrees::tree<uint64_t>> LoopifyTrees::extract_tree_children(
    const List<LoopifyTrees::tree<uint64_t>>
        &ts) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<LoopifyTrees::tree<uint64_t>> *ts;
  };

  /// _Resume_Node: saves [a00, a20], resumes after recursive call with _result.
  struct _Resume_Node {
    LoopifyTrees::tree<uint64_t> a00;
    LoopifyTrees::tree<uint64_t> a20;
  };

  using _Frame = std::variant<_Enter, _Resume_Node>;
  List<LoopifyTrees::tree<uint64_t>> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&ts});
  /// Loopified extract_tree_children: _Enter -> _Resume_Node.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<LoopifyTrees::tree<uint64_t>> &ts = *_f.ts;
      if (std::holds_alternative<
              typename List<LoopifyTrees::tree<uint64_t>>::Nil>(ts.v())) {
        _result = List<LoopifyTrees::tree<uint64_t>>::nil();
      } else {
        const auto &[a0, a1] =
            std::get<typename List<LoopifyTrees::tree<uint64_t>>::Cons>(ts.v());
        if (std::holds_alternative<typename LoopifyTrees::tree<uint64_t>::Leaf>(
                a0.v())) {
          _stack.emplace_back(_Enter{a1.get()});
        } else {
          const auto &[a00, a10, a20] =
              std::get<typename LoopifyTrees::tree<uint64_t>::Node>(a0.v());
          _stack.emplace_back(_Resume_Node{*a00, *a20});
          _stack.emplace_back(_Enter{a1.get()});
        }
      }
    } else {
      auto _f = std::move(std::get<_Resume_Node>(_frame));
      _result = List<LoopifyTrees::tree<uint64_t>>::cons(
          _f.a00, List<LoopifyTrees::tree<uint64_t>>::cons(_f.a20, _result));
    }
  }
  return _result;
}

/// tree_levels t returns list of lists, one per level (breadth-first).
List<List<uint64_t>> LoopifyTrees::tree_levels_fuel(
    uint64_t fuel,
    const List<LoopifyTrees::tree<uint64_t>>
        &trees) { /// _Enter: captures varying parameters for each recursive
                  /// call.

  struct _Enter {
    List<LoopifyTrees::tree<uint64_t>> trees;
    uint64_t fuel;
  };

  /// _Resume_Cons: saves [values], resumes after recursive call with _result.
  struct _Resume_Cons {
    List<uint64_t> values;
  };

  using _Frame = std::variant<_Enter, _Resume_Cons>;
  List<List<uint64_t>> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{trees, fuel});
  /// Loopified tree_levels_fuel: _Enter -> _Resume_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<LoopifyTrees::tree<uint64_t>> &trees = _f.trees;
      uint64_t fuel = _f.fuel;
      if (fuel <= 0) {
        _result = List<List<uint64_t>>::nil();
      } else {
        uint64_t f = fuel - 1;
        List<uint64_t> values = extract_tree_values(trees);
        if (std::holds_alternative<typename List<uint64_t>::Nil>(
                values.v_mut())) {
          _result = List<List<uint64_t>>::nil();
        } else {
          List<LoopifyTrees::tree<uint64_t>> children =
              extract_tree_children(trees);
          _stack.emplace_back(_Resume_Cons{values});
          _stack.emplace_back(_Enter{std::move(children), f});
        }
      }
    } else {
      auto _f = std::move(std::get<_Resume_Cons>(_frame));
      _result = List<List<uint64_t>>::cons(_f.values, _result);
    }
  }
  return _result;
}

List<List<uint64_t>> LoopifyTrees::tree_levels(LoopifyTrees::tree<uint64_t> t) {
  return tree_levels_fuel(
      UINT64_C(100),
      List<LoopifyTrees::tree<uint64_t>>::cons(
          std::move(t), List<LoopifyTrees::tree<uint64_t>>::nil()));
}

/// count_nodes t returns tuple (node_count, sum_of_values).
std::pair<uint64_t, uint64_t> LoopifyTrees::count_nodes(
    const LoopifyTrees::tree<uint64_t>
        &t) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const LoopifyTrees::tree<uint64_t> *t;
  };

  /// _Cont_Node: saves [a1, a2], resumes after recursive call, then processes
  /// rest.
  struct _Cont_Node {
    uint64_t a1;
    const LoopifyTrees::tree<uint64_t> *a2;
  };

  /// _Cont_lc: saves [a1, lc, ls], resumes after recursive call, then processes
  /// rest.
  struct _Cont_lc {
    uint64_t a1;
    uint64_t lc;
    uint64_t ls;
  };

  using _Frame = std::variant<_Enter, _Cont_Node, _Cont_lc>;
  std::pair<uint64_t, uint64_t> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&t});
  /// Loopified count_nodes: _Enter -> _Cont_Node -> _Cont_lc.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const LoopifyTrees::tree<uint64_t> &t = *_f.t;
      if (std::holds_alternative<typename LoopifyTrees::tree<uint64_t>::Leaf>(
              t.v())) {
        _result = std::make_pair(UINT64_C(0), UINT64_C(0));
      } else {
        const auto &[a0, a1, a2] =
            std::get<typename LoopifyTrees::tree<uint64_t>::Node>(t.v());
        _stack.emplace_back(_Cont_Node{a1, a2.get()});
        _stack.emplace_back(_Enter{a0.get()});
      }
    } else if (std::holds_alternative<_Cont_Node>(_frame)) {
      auto _f = std::move(std::get<_Cont_Node>(_frame));
      uint64_t a1 = _f.a1;
      const LoopifyTrees::tree<uint64_t> &a2 = *_f.a2;
      const uint64_t &lc = _result.first;
      const uint64_t &ls = _result.second;
      _stack.emplace_back(_Cont_lc{a1, lc, ls});
      _stack.emplace_back(_Enter{&a2});
    } else {
      auto _f = std::move(std::get<_Cont_lc>(_frame));
      uint64_t a1 = _f.a1;
      uint64_t lc = _f.lc;
      uint64_t ls = _f.ls;
      const uint64_t &rc = _result.first;
      const uint64_t &rs = _result.second;
      _result = std::make_pair(((lc + rc) + 1), (a1 + (ls + rs)));
    }
  }
  return _result;
}

/// Helper: append two lists of lists.
List<List<uint64_t>> LoopifyTrees::append_list_lists(
    const List<List<uint64_t>> &l1,
    List<List<uint64_t>>
        l2) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    List<List<uint64_t>> l2;
    const List<List<uint64_t>> *l1;
  };

  /// _Resume_Cons: saves [a0], resumes after recursive call with _result.
  struct _Resume_Cons {
    List<uint64_t> a0;
  };

  using _Frame = std::variant<_Enter, _Resume_Cons>;
  List<List<uint64_t>> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{l2, &l1});
  /// Loopified append_list_lists: _Enter -> _Resume_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      List<List<uint64_t>> l2 = std::move(_f.l2);
      const List<List<uint64_t>> &l1 = *_f.l1;
      if (std::holds_alternative<typename List<List<uint64_t>>::Nil>(l1.v())) {
        _result = std::move(l2);
      } else {
        const auto &[a0, a1] =
            std::get<typename List<List<uint64_t>>::Cons>(l1.v());
        _stack.emplace_back(_Resume_Cons{a0});
        _stack.emplace_back(_Enter{std::move(l2), a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Resume_Cons>(_frame));
      _result = List<List<uint64_t>>::cons(_f.a0, _result);
    }
  }
  return _result;
}

/// Helper: prepend value to all lists in a list of lists.
List<List<uint64_t>> LoopifyTrees::map_cons_to_all(
    uint64_t x,
    const List<List<uint64_t>> &
        lsts) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<List<uint64_t>> *lsts;
  };

  /// _Resume_Cons: saves [_s0], resumes after recursive call with _result.
  struct _Resume_Cons {
    std::decay_t<decltype(List<uint64_t>::cons(
        std::declval<uint64_t &>(), std::declval<List<uint64_t> &>()))>
        _s0;
  };

  using _Frame = std::variant<_Enter, _Resume_Cons>;
  List<List<uint64_t>> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&lsts});
  /// Loopified map_cons_to_all: _Enter -> _Resume_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<List<uint64_t>> &lsts = *_f.lsts;
      if (std::holds_alternative<typename List<List<uint64_t>>::Nil>(
              lsts.v())) {
        _result = List<List<uint64_t>>::nil();
      } else {
        const auto &[a0, a1] =
            std::get<typename List<List<uint64_t>>::Cons>(lsts.v());
        _stack.emplace_back(_Resume_Cons{List<uint64_t>::cons(x, a0)});
        _stack.emplace_back(_Enter{a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Resume_Cons>(_frame));
      _result = List<List<uint64_t>>::cons(_f._s0, _result);
    }
  }
  return _result;
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
      _result =
          append_list_lists(map_cons_to_all(_f.a1_1, std::move(_result)),
                            map_cons_to_all(_f.a1_0, std::move(_f._result)));
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
      _result = std::move(_result).app(
          List<uint64_t>::cons(_f.a1, std::move(_f._result)));
    }
  }
  return _result;
}

/// Simple insertion sort for collect_sorted.
List<uint64_t> LoopifyTrees::insert_sorted(
    uint64_t x,
    const List<uint64_t>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<uint64_t> *l;
  };

  /// _Resume1: saves [a0], resumes after recursive call with _result.
  struct _Resume1 {
    uint64_t a0;
  };

  using _Frame = std::variant<_Enter, _Resume1>;
  List<uint64_t> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l});
  /// Loopified insert_sorted: _Enter -> _Resume1.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<uint64_t> &l = *_f.l;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
        _result = List<uint64_t>::cons(x, List<uint64_t>::nil());
      } else {
        const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
        if (x <= a0) {
          _result = List<uint64_t>::cons(x, List<uint64_t>::cons(a0, *a1));
        } else {
          _stack.emplace_back(_Resume1{a0});
          _stack.emplace_back(_Enter{a1.get()});
        }
      }
    } else {
      auto _f = std::move(std::get<_Resume1>(_frame));
      _result = List<uint64_t>::cons(_f.a0, _result);
    }
  }
  return _result;
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
std::pair<uint64_t, uint64_t> LoopifyTrees::tree_min_max(
    const LoopifyTrees::tree<uint64_t>
        &t) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const LoopifyTrees::tree<uint64_t> *t;
  };

  /// _Cont_Node: saves [a1, a2], resumes after recursive call, then processes
  /// rest.
  struct _Cont_Node {
    uint64_t a1;
    const LoopifyTrees::tree<uint64_t> *a2;
  };

  /// _Cont_lmin: saves [a1, lmax, lmin], resumes after recursive call, then
  /// processes rest.
  struct _Cont_lmin {
    uint64_t a1;
    uint64_t lmax;
    uint64_t lmin;
  };

  using _Frame = std::variant<_Enter, _Cont_Node, _Cont_lmin>;
  std::pair<uint64_t, uint64_t> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&t});
  /// Loopified tree_min_max: _Enter -> _Cont_Node -> _Cont_lmin.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const LoopifyTrees::tree<uint64_t> &t = *_f.t;
      if (std::holds_alternative<typename LoopifyTrees::tree<uint64_t>::Leaf>(
              t.v())) {
        _result = std::make_pair(UINT64_C(0), UINT64_C(0));
      } else {
        const auto &[a0, a1, a2] =
            std::get<typename LoopifyTrees::tree<uint64_t>::Node>(t.v());
        _stack.emplace_back(_Cont_Node{a1, a2.get()});
        _stack.emplace_back(_Enter{a0.get()});
      }
    } else if (std::holds_alternative<_Cont_Node>(_frame)) {
      auto _f = std::move(std::get<_Cont_Node>(_frame));
      uint64_t a1 = _f.a1;
      const LoopifyTrees::tree<uint64_t> &a2 = *_f.a2;
      const uint64_t &lmin = _result.first;
      const uint64_t &lmax = _result.second;
      _stack.emplace_back(_Cont_lmin{a1, lmax, lmin});
      _stack.emplace_back(_Enter{&a2});
    } else {
      auto _f = std::move(std::get<_Cont_lmin>(_frame));
      uint64_t a1 = _f.a1;
      uint64_t lmax = _f.lmax;
      uint64_t lmin = _f.lmin;
      const uint64_t &rmin = _result.first;
      const uint64_t &rmax = _result.second;
      _result = std::make_pair(min3((lmin == UINT64_C(0) ? a1 : lmin),
                                    (rmin == UINT64_C(0) ? a1 : rmin), a1),
                               max3(lmax, rmax, a1));
    }
  }
  return _result;
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
    std::decay_t<decltype(std::declval<uint64_t &>() ==
                          std::declval<uint64_t &>())>
        _s1;
  };

  /// _Combine_Node: receives partial results, combines with _result from final
  /// call.
  struct _Combine_Node {
    bool _result;
    std::decay_t<decltype(std::declval<uint64_t &>() ==
                          std::declval<uint64_t &>())>
        _s1;
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
      _result = (_f._s1 || (std::move(_result) || std::move(_f._result)));
    }
  }
  return _result;
}
