#include "loopify_more_trees.h"

LoopifyMoreTrees::tree LoopifyMoreTrees::mirror(
    const LoopifyMoreTrees::tree
        &t) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const LoopifyMoreTrees::tree *t;
  };

  /// _After_Node: saves [a2, a1], dispatches next recursive call.
  struct _After_Node {
    const LoopifyMoreTrees::tree *a2;
    uint64_t a1;
  };

  /// _Combine_Node: receives partial results, combines with _result from final
  /// call.
  struct _Combine_Node {
    LoopifyMoreTrees::tree _result;
    uint64_t a1;
  };

  using _Frame = std::variant<_Enter, _After_Node, _Combine_Node>;
  LoopifyMoreTrees::tree _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&t});
  /// Loopified mirror: _Enter -> _After_Node -> _Combine_Node.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const LoopifyMoreTrees::tree &t = *_f.t;
      if (std::holds_alternative<typename LoopifyMoreTrees::tree::Leaf>(
              t.v())) {
        _result = tree::leaf();
      } else {
        const auto &[a0, a1, a2] =
            std::get<typename LoopifyMoreTrees::tree::Node>(t.v());
        _stack.emplace_back(_After_Node{a2.get(), a1});
        _stack.emplace_back(_Enter{a0.get()});
      }
    } else if (std::holds_alternative<_After_Node>(_frame)) {
      auto _f = std::move(std::get<_After_Node>(_frame));
      _stack.emplace_back(_Combine_Node{std::move(_result), _f.a1});
      _stack.emplace_back(_Enter{_f.a2});
    } else {
      auto _f = std::move(std::get<_Combine_Node>(_frame));
      _result = tree::node(_result, _f.a1, _f._result);
    }
  }
  return _result;
}

bool LoopifyMoreTrees::same_shape(
    const LoopifyMoreTrees::tree &t1,
    const LoopifyMoreTrees::tree
        &t2) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const LoopifyMoreTrees::tree *t2;
    const LoopifyMoreTrees::tree *t1;
  };

  /// _After_Node: saves [a00, a0], dispatches next recursive call.
  struct _After_Node {
    const LoopifyMoreTrees::tree *a00;
    const LoopifyMoreTrees::tree *a0;
  };

  /// _Combine_Node: receives partial results, combines with _result from final
  /// call.
  struct _Combine_Node {
    bool _result;
  };

  using _Frame = std::variant<_Enter, _After_Node, _Combine_Node>;
  bool _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&t2, &t1});
  /// Loopified same_shape: _Enter -> _After_Node -> _Combine_Node.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const LoopifyMoreTrees::tree &t2 = *_f.t2;
      const LoopifyMoreTrees::tree &t1 = *_f.t1;
      if (std::holds_alternative<typename LoopifyMoreTrees::tree::Leaf>(
              t1.v())) {
        if (std::holds_alternative<typename LoopifyMoreTrees::tree::Leaf>(
                t2.v())) {
          _result = true;
        } else {
          _result = false;
        }
      } else {
        const auto &[a0, a1, a2] =
            std::get<typename LoopifyMoreTrees::tree::Node>(t1.v());
        if (std::holds_alternative<typename LoopifyMoreTrees::tree::Leaf>(
                t2.v())) {
          _result = false;
        } else {
          const auto &[a00, a10, a20] =
              std::get<typename LoopifyMoreTrees::tree::Node>(t2.v());
          _stack.emplace_back(_After_Node{a00.get(), a0.get()});
          _stack.emplace_back(_Enter{a20.get(), a2.get()});
        }
      }
    } else if (std::holds_alternative<_After_Node>(_frame)) {
      auto _f = std::move(std::get<_After_Node>(_frame));
      _stack.emplace_back(_Combine_Node{_result});
      _stack.emplace_back(_Enter{_f.a00, _f.a0});
    } else {
      auto _f = std::move(std::get<_Combine_Node>(_frame));
      _result = (_result && _f._result);
    }
  }
  return _result;
}

List<uint64_t> LoopifyMoreTrees::tree_to_list(
    const LoopifyMoreTrees::tree
        &t) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const LoopifyMoreTrees::tree *t;
  };

  /// _After_Node: saves [a0, _s1], dispatches next recursive call.
  struct _After_Node {
    const LoopifyMoreTrees::tree *a0;
    decltype(List<uint64_t>::cons(std::declval<uint64_t &>(),
                                  List<uint64_t>::nil())) _s1;
  };

  /// _Combine_Node: receives partial results, combines with _result from final
  /// call.
  struct _Combine_Node {
    List<uint64_t> _result;
    decltype(List<uint64_t>::cons(std::declval<uint64_t &>(),
                                  List<uint64_t>::nil())) _s1;
  };

  using _Frame = std::variant<_Enter, _After_Node, _Combine_Node>;
  List<uint64_t> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&t});
  /// Loopified tree_to_list: _Enter -> _After_Node -> _Combine_Node.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const LoopifyMoreTrees::tree &t = *_f.t;
      if (std::holds_alternative<typename LoopifyMoreTrees::tree::Leaf>(
              t.v())) {
        _result = List<uint64_t>::nil();
      } else {
        const auto &[a0, a1, a2] =
            std::get<typename LoopifyMoreTrees::tree::Node>(t.v());
        _stack.emplace_back(_After_Node{
            a0.get(), List<uint64_t>::cons(a1, List<uint64_t>::nil())});
        _stack.emplace_back(_Enter{a2.get()});
      }
    } else if (std::holds_alternative<_After_Node>(_frame)) {
      auto _f = std::move(std::get<_After_Node>(_frame));
      _stack.emplace_back(_Combine_Node{std::move(_result), _f._s1});
      _stack.emplace_back(_Enter{_f.a0});
    } else {
      auto _f = std::move(std::get<_Combine_Node>(_frame));
      _result = _result.app(_f._s1.app(_f._result));
    }
  }
  return _result;
}

bool LoopifyMoreTrees::mirror_equal(const LoopifyMoreTrees::tree &t) {
  return same_shape(t, mirror(t));
}

uint64_t LoopifyMoreTrees::count_nodes(
    const LoopifyMoreTrees::tree
        &t) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const LoopifyMoreTrees::tree *t;
  };

  /// _After_Node: saves [a0, _s1], dispatches next recursive call.
  struct _After_Node {
    const LoopifyMoreTrees::tree *a0;
    decltype(UINT64_C(1)) _s1;
  };

  /// _Combine_Node: receives partial results, combines with _result from final
  /// call.
  struct _Combine_Node {
    uint64_t _result;
    decltype(UINT64_C(1)) _s1;
  };

  using _Frame = std::variant<_Enter, _After_Node, _Combine_Node>;
  uint64_t _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&t});
  /// Loopified count_nodes: _Enter -> _After_Node -> _Combine_Node.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const LoopifyMoreTrees::tree &t = *_f.t;
      if (std::holds_alternative<typename LoopifyMoreTrees::tree::Leaf>(
              t.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1, a2] =
            std::get<typename LoopifyMoreTrees::tree::Node>(t.v());
        _stack.emplace_back(_After_Node{a0.get(), UINT64_C(1)});
        _stack.emplace_back(_Enter{a2.get()});
      }
    } else if (std::holds_alternative<_After_Node>(_frame)) {
      auto _f = std::move(std::get<_After_Node>(_frame));
      _stack.emplace_back(_Combine_Node{_result, _f._s1});
      _stack.emplace_back(_Enter{_f.a0});
    } else {
      auto _f = std::move(std::get<_Combine_Node>(_frame));
      _result = ((_f._s1 + _result) + _f._result);
    }
  }
  return _result;
}

LoopifyMoreTrees::tree LoopifyMoreTrees::tree_max(
    LoopifyMoreTrees::tree t1,
    LoopifyMoreTrees::tree
        t2) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    LoopifyMoreTrees::tree t2;
    LoopifyMoreTrees::tree t1;
  };

  /// _After_Node: saves [a00, a0, _s2], dispatches next recursive call.
  struct _After_Node {
    LoopifyMoreTrees::tree a00;
    LoopifyMoreTrees::tree a0;
    decltype(std::max(std::move(std::declval<uint64_t &>()),
                      std::move(std::declval<uint64_t &>()))) _s2;
  };

  /// _Combine_Node: receives partial results, combines with _result from final
  /// call.
  struct _Combine_Node {
    LoopifyMoreTrees::tree _result;
    decltype(std::max(std::move(std::declval<uint64_t &>()),
                      std::move(std::declval<uint64_t &>()))) _s1;
  };

  using _Frame = std::variant<_Enter, _After_Node, _Combine_Node>;
  LoopifyMoreTrees::tree _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{t2, t1});
  /// Loopified tree_max: _Enter -> _After_Node -> _Combine_Node.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      LoopifyMoreTrees::tree t2 = std::move(_f.t2);
      LoopifyMoreTrees::tree t1 = std::move(_f.t1);
      if (std::holds_alternative<typename LoopifyMoreTrees::tree::Leaf>(
              t1.v_mut())) {
        _result = std::move(t2);
      } else {
        auto &[a0, a1, a2] =
            std::get<typename LoopifyMoreTrees::tree::Node>(t1.v_mut());
        if (std::holds_alternative<typename LoopifyMoreTrees::tree::Leaf>(
                t2.v_mut())) {
          _result = std::move(t1);
        } else {
          auto &[a00, a10, a20] =
              std::get<typename LoopifyMoreTrees::tree::Node>(t2.v_mut());
          _stack.emplace_back(
              _After_Node{*a00, *a0, std::max(std::move(a1), std::move(a10))});
          _stack.emplace_back(_Enter{std::move(*a20), std::move(*a2)});
        }
      }
    } else if (std::holds_alternative<_After_Node>(_frame)) {
      auto _f = std::move(std::get<_After_Node>(_frame));
      _stack.emplace_back(_Combine_Node{std::move(_result), _f._s2});
      _stack.emplace_back(_Enter{std::move(_f.a00), std::move(_f.a0)});
    } else {
      auto _f = std::move(std::get<_Combine_Node>(_frame));
      _result = tree::node(_result, _f._s1, _f._result);
    }
  }
  return _result;
}

uint64_t LoopifyMoreTrees::sum_of_max_branches(
    const LoopifyMoreTrees::tree
        &t) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const LoopifyMoreTrees::tree *t;
  };

  /// _After_Node: saves [a0, a1], dispatches next recursive call.
  struct _After_Node {
    const LoopifyMoreTrees::tree *a0;
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
  /// Loopified sum_of_max_branches: _Enter -> _After_Node -> _Combine_Node.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const LoopifyMoreTrees::tree &t = *_f.t;
      if (std::holds_alternative<typename LoopifyMoreTrees::tree::Leaf>(
              t.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1, a2] =
            std::get<typename LoopifyMoreTrees::tree::Node>(t.v());
        _stack.emplace_back(_After_Node{a0.get(), a1});
        _stack.emplace_back(_Enter{a2.get()});
      }
    } else if (std::holds_alternative<_After_Node>(_frame)) {
      auto _f = std::move(std::get<_After_Node>(_frame));
      _stack.emplace_back(_Combine_Node{_result, _f.a1});
      _stack.emplace_back(_Enter{_f.a0});
    } else {
      auto _f = std::move(std::get<_Combine_Node>(_frame));
      _result = (_f.a1 + std::max(_result, _f._result));
    }
  }
  return _result;
}

LoopifyMoreTrees::tree LoopifyMoreTrees::insert_bst(
    uint64_t x,
    const LoopifyMoreTrees::tree
        &t) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const LoopifyMoreTrees::tree *t;
  };

  /// _Resume1: saves [a2, a1], resumes after recursive call with _result.
  struct _Resume1 {
    LoopifyMoreTrees::tree a2;
    uint64_t a1;
  };

  /// _Resume2: saves [a1, a0], resumes after recursive call with _result.
  struct _Resume2 {
    uint64_t a1;
    LoopifyMoreTrees::tree a0;
  };

  using _Frame = std::variant<_Enter, _Resume1, _Resume2>;
  LoopifyMoreTrees::tree _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&t});
  /// Loopified insert_bst: _Enter -> _Resume1 -> _Resume2.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const LoopifyMoreTrees::tree &t = *_f.t;
      if (std::holds_alternative<typename LoopifyMoreTrees::tree::Leaf>(
              t.v())) {
        _result = tree::node(tree::leaf(), x, tree::leaf());
      } else {
        const auto &[a0, a1, a2] =
            std::get<typename LoopifyMoreTrees::tree::Node>(t.v());
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
      _result = tree::node(_result, _f.a1, _f.a2);
    } else {
      auto _f = std::move(std::get<_Resume2>(_frame));
      _result = tree::node(_f.a0, _f.a1, _result);
    }
  }
  return _result;
}

LoopifyMoreTrees::tree LoopifyMoreTrees::build_bst(
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
  LoopifyMoreTrees::tree _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l});
  /// Loopified build_bst: _Enter -> _Resume_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<uint64_t> &l = *_f.l;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
        _result = tree::leaf();
      } else {
        const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
        _stack.emplace_back(_Resume_Cons{a0});
        _stack.emplace_back(_Enter{a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Resume_Cons>(_frame));
      _result = insert_bst(_f.a0, _result);
    }
  }
  return _result;
}

List<uint64_t> LoopifyMoreTrees::append_lists(const List<uint64_t> &l1,
                                              List<uint64_t> l2) {
  std::unique_ptr<List<uint64_t>> _head{};
  std::unique_ptr<List<uint64_t>> *_write = &_head;
  List<uint64_t> _loop_l2 = std::move(l2);
  const List<uint64_t> *_loop_l1 = &l1;
  while (true) {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l1->v())) {
      *_write = std::make_unique<List<uint64_t>>(std::move(_loop_l2));
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename List<uint64_t>::Cons>(_loop_l1->v());
      auto _cell = std::make_unique<List<uint64_t>>(
          typename List<uint64_t>::Cons(a0, nullptr));
      *_write = std::move(_cell);
      _write = &std::get<typename List<uint64_t>::Cons>((*_write)->v_mut()).l;
      _loop_l1 = a1.get();
      continue;
    }
  }
  return std::move(*_head);
}

List<uint64_t> LoopifyMoreTrees::flatten(
    const List<List<uint64_t>>
        &ll) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<List<uint64_t>> *ll;
  };

  /// _Resume_Cons: saves [a0], resumes after recursive call with _result.
  struct _Resume_Cons {
    List<uint64_t> a0;
  };

  using _Frame = std::variant<_Enter, _Resume_Cons>;
  List<uint64_t> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&ll});
  /// Loopified flatten: _Enter -> _Resume_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<List<uint64_t>> &ll = *_f.ll;
      if (std::holds_alternative<typename List<List<uint64_t>>::Nil>(ll.v())) {
        _result = List<uint64_t>::nil();
      } else {
        const auto &[a0, a1] =
            std::get<typename List<List<uint64_t>>::Cons>(ll.v());
        _stack.emplace_back(_Resume_Cons{a0});
        _stack.emplace_back(_Enter{a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Resume_Cons>(_frame));
      _result = append_lists(_f.a0, _result);
    }
  }
  return _result;
}

List<List<uint64_t>>
LoopifyMoreTrees::map_tree_to_list(const List<LoopifyMoreTrees::tree> &lt) {
  std::unique_ptr<List<List<uint64_t>>> _head{};
  std::unique_ptr<List<List<uint64_t>>> *_write = &_head;
  const List<LoopifyMoreTrees::tree> *_loop_lt = &lt;
  while (true) {
    if (std::holds_alternative<typename List<LoopifyMoreTrees::tree>::Nil>(
            _loop_lt->v())) {
      *_write =
          std::make_unique<List<List<uint64_t>>>(List<List<uint64_t>>::nil());
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename List<LoopifyMoreTrees::tree>::Cons>(_loop_lt->v());
      auto _cell = std::make_unique<List<List<uint64_t>>>(
          typename List<List<uint64_t>>::Cons(tree_to_list(a0), nullptr));
      *_write = std::move(_cell);
      _write =
          &std::get<typename List<List<uint64_t>>::Cons>((*_write)->v_mut()).l;
      _loop_lt = a1.get();
      continue;
    }
  }
  return std::move(*_head);
}

List<LoopifyMoreTrees::tree>
LoopifyMoreTrees::tree_children(const LoopifyMoreTrees::tree &t) {
  if (std::holds_alternative<typename LoopifyMoreTrees::tree::Leaf>(t.v())) {
    return List<LoopifyMoreTrees::tree>::nil();
  } else {
    const auto &[a0, a1, a2] =
        std::get<typename LoopifyMoreTrees::tree::Node>(t.v());
    return List<LoopifyMoreTrees::tree>::cons(
        *a0, List<LoopifyMoreTrees::tree>::cons(
                 *a2, List<LoopifyMoreTrees::tree>::nil()));
  }
}

List<LoopifyMoreTrees::tree>
LoopifyMoreTrees::append_trees(const List<LoopifyMoreTrees::tree> &l1,
                               List<LoopifyMoreTrees::tree> l2) {
  std::unique_ptr<List<LoopifyMoreTrees::tree>> _head{};
  std::unique_ptr<List<LoopifyMoreTrees::tree>> *_write = &_head;
  List<LoopifyMoreTrees::tree> _loop_l2 = std::move(l2);
  const List<LoopifyMoreTrees::tree> *_loop_l1 = &l1;
  while (true) {
    if (std::holds_alternative<typename List<LoopifyMoreTrees::tree>::Nil>(
            _loop_l1->v())) {
      *_write =
          std::make_unique<List<LoopifyMoreTrees::tree>>(std::move(_loop_l2));
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename List<LoopifyMoreTrees::tree>::Cons>(_loop_l1->v());
      auto _cell = std::make_unique<List<LoopifyMoreTrees::tree>>(
          typename List<LoopifyMoreTrees::tree>::Cons(a0, nullptr));
      *_write = std::move(_cell);
      _write = &std::get<typename List<LoopifyMoreTrees::tree>::Cons>(
                    (*_write)->v_mut())
                    .l;
      _loop_l1 = a1.get();
      continue;
    }
  }
  return std::move(*_head);
}

List<LoopifyMoreTrees::tree> LoopifyMoreTrees::concat_map_children(
    const List<LoopifyMoreTrees::tree>
        &lt) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<LoopifyMoreTrees::tree> *lt;
  };

  /// _Resume_Cons: saves [a0], resumes after recursive call with _result.
  struct _Resume_Cons {
    decltype(tree_children(std::declval<LoopifyMoreTrees::tree &>())) a0;
  };

  using _Frame = std::variant<_Enter, _Resume_Cons>;
  List<LoopifyMoreTrees::tree> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&lt});
  /// Loopified concat_map_children: _Enter -> _Resume_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<LoopifyMoreTrees::tree> &lt = *_f.lt;
      if (std::holds_alternative<typename List<LoopifyMoreTrees::tree>::Nil>(
              lt.v())) {
        _result = List<LoopifyMoreTrees::tree>::nil();
      } else {
        const auto &[a0, a1] =
            std::get<typename List<LoopifyMoreTrees::tree>::Cons>(lt.v());
        _stack.emplace_back(_Resume_Cons{tree_children(a0)});
        _stack.emplace_back(_Enter{a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Resume_Cons>(_frame));
      _result = append_trees(_f.a0, _result);
    }
  }
  return _result;
}

List<List<uint64_t>>
LoopifyMoreTrees::tree_levels_fuel(uint64_t fuel,
                                   const List<LoopifyMoreTrees::tree> &level) {
  std::unique_ptr<List<List<uint64_t>>> _head{};
  std::unique_ptr<List<List<uint64_t>>> *_write = &_head;
  List<LoopifyMoreTrees::tree> _loop_level = level;
  uint64_t _loop_fuel = std::move(fuel);
  while (true) {
    if (_loop_fuel <= 0) {
      *_write =
          std::make_unique<List<List<uint64_t>>>(List<List<uint64_t>>::nil());
      break;
    } else {
      uint64_t fuel_ = _loop_fuel - 1;
      if (std::holds_alternative<typename List<LoopifyMoreTrees::tree>::Nil>(
              _loop_level.v())) {
        *_write =
            std::make_unique<List<List<uint64_t>>>(List<List<uint64_t>>::nil());
        break;
      } else {
        List<uint64_t> values = flatten(map_tree_to_list(_loop_level));
        List<LoopifyMoreTrees::tree> next = concat_map_children(_loop_level);
        auto _cell = std::make_unique<List<List<uint64_t>>>(
            typename List<List<uint64_t>>::Cons(std::move(values), nullptr));
        *_write = std::move(_cell);
        _write =
            &std::get<typename List<List<uint64_t>>::Cons>((*_write)->v_mut())
                 .l;
        _loop_level = std::move(next);
        _loop_fuel = fuel_;
        continue;
      }
    }
  }
  return std::move(*_head);
}

List<List<uint64_t>> LoopifyMoreTrees::tree_levels(LoopifyMoreTrees::tree t) {
  return tree_levels_fuel(
      UINT64_C(100), List<LoopifyMoreTrees::tree>::cons(
                         std::move(t), List<LoopifyMoreTrees::tree>::nil()));
}
