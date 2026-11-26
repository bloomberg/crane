#include "loopify_more_trees.h"

LoopifyMoreTrees::tree
LoopifyMoreTrees::mirror(const LoopifyMoreTrees::tree &t) {
  // Explicit stack replaces the non-tail recursion of mirror: _call frames are
  // pending calls, _after frames resume a caller.
  struct _call {
    const LoopifyMoreTrees::tree *t;
  };

  struct _after_mirror_in_Node {
    const LoopifyMoreTrees::tree *a0;
    uint64_t a1;
  };

  struct _after_mirror_in_Node_2 {
    uint64_t a1;
    LoopifyMoreTrees::tree _tmp2;
  };

  using _frame =
      std::variant<_call, _after_mirror_in_Node, _after_mirror_in_Node_2>;
  LoopifyMoreTrees::tree _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&t});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const LoopifyMoreTrees::tree &t = *_f.t;
      if (std::holds_alternative<typename LoopifyMoreTrees::tree::Leaf>(t.v())) {
        _result = tree::leaf();
      } else {
        const auto &[a0, a1, a2] =
            std::get<typename LoopifyMoreTrees::tree::Node>(t.v());
        _stack.emplace_back(_after_mirror_in_Node{crane_raw(a0), a1});
        _stack.emplace_back(_call{crane_raw(a2)});
      }
    } else if (std::holds_alternative<_after_mirror_in_Node>(_popped)) {
      auto _f = std::move(std::get<_after_mirror_in_Node>(_popped));
      _stack.pop_back();
      const LoopifyMoreTrees::tree &a0 = *_f.a0;
      uint64_t a1 = _f.a1;
      _stack.emplace_back(_after_mirror_in_Node_2{a1, std::move(_result)});
      _stack.emplace_back(_call{&a0});
    } else {
      auto _f = std::move(std::get<_after_mirror_in_Node_2>(_popped));
      _stack.pop_back();
      uint64_t a1 = _f.a1;
      _result = tree::node(std::move(_f._tmp2), a1, std::move(_result));
    }
  }
  return _result;
}

bool LoopifyMoreTrees::same_shape(const LoopifyMoreTrees::tree &t1,
                                  const LoopifyMoreTrees::tree &t2) {
  // Explicit stack replaces the non-tail recursion of same_shape: _call frames
  // are pending calls, _after frames resume a caller.
  struct _call {
    const LoopifyMoreTrees::tree *t2;
    const LoopifyMoreTrees::tree *t1;
  };

  struct _after_same_shape_in_Node {
    const LoopifyMoreTrees::tree *a2;
    const LoopifyMoreTrees::tree *a20;
  };

  struct _after_same_shape_in_Node_2 {
    bool _tmp2;
  };

  using _frame = std::variant<_call, _after_same_shape_in_Node,
                              _after_same_shape_in_Node_2>;
  bool _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&t2, &t1});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const LoopifyMoreTrees::tree &t2 = *_f.t2;
      const LoopifyMoreTrees::tree &t1 = *_f.t1;
      if (std::holds_alternative<typename LoopifyMoreTrees::tree::Leaf>(t1.v())) {
        if (std::holds_alternative<typename LoopifyMoreTrees::tree::Leaf>(
                t2.v())) {
          _result = true;
        } else {
          _result = false;
        }
      } else {
        const auto &[a0, _, a2] =
            std::get<typename LoopifyMoreTrees::tree::Node>(t1.v());
        if (std::holds_alternative<typename LoopifyMoreTrees::tree::Leaf>(
                t2.v())) {
          _result = false;
        } else {
          const auto &[a00, _, a20] =
              std::get<typename LoopifyMoreTrees::tree::Node>(t2.v());
          _stack.emplace_back(
              _after_same_shape_in_Node{crane_raw(a2), crane_raw(a20)});
          _stack.emplace_back(_call{crane_raw(a00), crane_raw(a0)});
        }
      }
    } else if (std::holds_alternative<_after_same_shape_in_Node>(_popped)) {
      auto _f = std::move(std::get<_after_same_shape_in_Node>(_popped));
      _stack.pop_back();
      const LoopifyMoreTrees::tree &a2 = *_f.a2;
      const LoopifyMoreTrees::tree &a20 = *_f.a20;
      _stack.emplace_back(_after_same_shape_in_Node_2{_result});
      _stack.emplace_back(_call{&a20, &a2});
    } else {
      auto _f = std::move(std::get<_after_same_shape_in_Node_2>(_popped));
      _stack.pop_back();
      _result = (_f._tmp2 && _result);
    }
  }
  return _result;
}

List<uint64_t> LoopifyMoreTrees::tree_to_list(const LoopifyMoreTrees::tree &t) {
  // Explicit stack replaces the non-tail recursion of tree_to_list: _call
  // frames are pending calls, _after frames resume a caller.
  struct _call {
    const LoopifyMoreTrees::tree *t;
  };

  struct _after_tree_to_list_in_Node {
    uint64_t a1;
    const LoopifyMoreTrees::tree *a2;
  };

  struct _after_tree_to_list_in_Node_2 {
    uint64_t a1;
    List<uint64_t> _tmp2;
  };

  using _frame = std::variant<_call, _after_tree_to_list_in_Node,
                              _after_tree_to_list_in_Node_2>;
  List<uint64_t> _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&t});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const LoopifyMoreTrees::tree &t = *_f.t;
      if (std::holds_alternative<typename LoopifyMoreTrees::tree::Leaf>(t.v())) {
        _result = List<uint64_t>::nil();
      } else {
        const auto &[a0, a1, a2] =
            std::get<typename LoopifyMoreTrees::tree::Node>(t.v());
        _stack.emplace_back(_after_tree_to_list_in_Node{a1, crane_raw(a2)});
        _stack.emplace_back(_call{crane_raw(a0)});
      }
    } else if (std::holds_alternative<_after_tree_to_list_in_Node>(_popped)) {
      auto _f = std::move(std::get<_after_tree_to_list_in_Node>(_popped));
      _stack.pop_back();
      uint64_t a1 = _f.a1;
      const LoopifyMoreTrees::tree &a2 = *_f.a2;
      _stack.emplace_back(_after_tree_to_list_in_Node_2{a1,
                                                        std::move(_result)});
      _stack.emplace_back(_call{&a2});
    } else {
      auto _f = std::move(std::get<_after_tree_to_list_in_Node_2>(_popped));
      _stack.pop_back();
      uint64_t a1 = _f.a1;
      _result =
          _f._tmp2.app(List<uint64_t>::cons(a1, List<uint64_t>::nil()).app(
              std::move(_result)));
    }
  }
  return _result;
}

bool LoopifyMoreTrees::mirror_equal(const LoopifyMoreTrees::tree &t) {
  return same_shape(t, mirror(t));
}

uint64_t LoopifyMoreTrees::count_nodes(const LoopifyMoreTrees::tree &t) {
  // Explicit stack replaces the non-tail recursion of count_nodes: _call frames
  // are pending calls, _after frames resume a caller.
  struct _call {
    const LoopifyMoreTrees::tree *t;
  };

  struct _after_count_nodes_in_Node {
    const LoopifyMoreTrees::tree *a2;
  };

  struct _after_count_nodes_in_Node_2 {
    uint64_t _tmp2;
  };

  using _frame = std::variant<_call, _after_count_nodes_in_Node,
                              _after_count_nodes_in_Node_2>;
  uint64_t _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&t});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const LoopifyMoreTrees::tree &t = *_f.t;
      if (std::holds_alternative<typename LoopifyMoreTrees::tree::Leaf>(t.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, _, a2] =
            std::get<typename LoopifyMoreTrees::tree::Node>(t.v());
        _stack.emplace_back(_after_count_nodes_in_Node{crane_raw(a2)});
        _stack.emplace_back(_call{crane_raw(a0)});
      }
    } else if (std::holds_alternative<_after_count_nodes_in_Node>(_popped)) {
      auto _f = std::move(std::get<_after_count_nodes_in_Node>(_popped));
      _stack.pop_back();
      const LoopifyMoreTrees::tree &a2 = *_f.a2;
      _stack.emplace_back(_after_count_nodes_in_Node_2{_result});
      _stack.emplace_back(_call{&a2});
    } else {
      auto _f = std::move(std::get<_after_count_nodes_in_Node_2>(_popped));
      _stack.pop_back();
      _result = ((UINT64_C(1) + _f._tmp2) + _result);
    }
  }
  return _result;
}

LoopifyMoreTrees::tree
LoopifyMoreTrees::tree_max(const LoopifyMoreTrees::tree &t1,
                           const LoopifyMoreTrees::tree &t2) {
  // Explicit stack replaces the non-tail recursion of tree_max: _call frames
  // are pending calls, _after frames resume a caller.
  struct _call {
    const LoopifyMoreTrees::tree *t2;
    const LoopifyMoreTrees::tree *t1;
  };

  struct _after_tree_max_in_Node {
    uint64_t a1;
    const LoopifyMoreTrees::tree *a2;
    uint64_t a10;
    const LoopifyMoreTrees::tree *a20;
  };

  struct _after_tree_max_in_Node_2 {
    uint64_t a1;
    uint64_t a10;
    LoopifyMoreTrees::tree _tmp2;
  };

  using _frame =
      std::variant<_call, _after_tree_max_in_Node, _after_tree_max_in_Node_2>;
  LoopifyMoreTrees::tree _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&t2, &t1});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const LoopifyMoreTrees::tree &t2 = *_f.t2;
      const LoopifyMoreTrees::tree &t1 = *_f.t1;
      if (std::holds_alternative<typename LoopifyMoreTrees::tree::Leaf>(t1.v())) {
        _result = std::move(t2);
      } else {
        const auto &[a0, a1, a2] =
            std::get<typename LoopifyMoreTrees::tree::Node>(t1.v());
        if (std::holds_alternative<typename LoopifyMoreTrees::tree::Leaf>(
                t2.v())) {
          _result = std::move(t1);
        } else {
          const auto &[a00, a10, a20] =
              std::get<typename LoopifyMoreTrees::tree::Node>(t2.v());
          _stack.emplace_back(
              _after_tree_max_in_Node{a1, crane_raw(a2), a10, crane_raw(a20)});
          _stack.emplace_back(_call{crane_raw(a00), crane_raw(a0)});
        }
      }
    } else if (std::holds_alternative<_after_tree_max_in_Node>(_popped)) {
      auto _f = std::move(std::get<_after_tree_max_in_Node>(_popped));
      _stack.pop_back();
      uint64_t a1 = _f.a1;
      const LoopifyMoreTrees::tree &a2 = *_f.a2;
      uint64_t a10 = _f.a10;
      const LoopifyMoreTrees::tree &a20 = *_f.a20;
      _stack.emplace_back(
          _after_tree_max_in_Node_2{a1, a10, std::move(_result)});
      _stack.emplace_back(_call{&a20, &a2});
    } else {
      auto _f = std::move(std::get<_after_tree_max_in_Node_2>(_popped));
      _stack.pop_back();
      uint64_t a1 = _f.a1;
      uint64_t a10 = _f.a10;
      _result = tree::node(std::move(_f._tmp2), std::max(a1, a10),
                           std::move(_result));
    }
  }
  return _result;
}

uint64_t
LoopifyMoreTrees::sum_of_max_branches(const LoopifyMoreTrees::tree &t) {
  // Explicit stack replaces the non-tail recursion of sum_of_max_branches:
  // _call frames are pending calls, _after frames resume a caller.
  struct _call {
    const LoopifyMoreTrees::tree *t;
  };

  struct _after_sum_of_max_branches_in_Node {
    uint64_t a1;
    const LoopifyMoreTrees::tree *a2;
  };

  struct _after_sum_of_max_branches_in_Node_2 {
    uint64_t a1;
    uint64_t _tmp2;
  };

  using _frame = std::variant<_call, _after_sum_of_max_branches_in_Node,
                              _after_sum_of_max_branches_in_Node_2>;
  uint64_t _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&t});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const LoopifyMoreTrees::tree &t = *_f.t;
      if (std::holds_alternative<typename LoopifyMoreTrees::tree::Leaf>(t.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1, a2] =
            std::get<typename LoopifyMoreTrees::tree::Node>(t.v());
        _stack.emplace_back(
            _after_sum_of_max_branches_in_Node{a1, crane_raw(a2)});
        _stack.emplace_back(_call{crane_raw(a0)});
      }
    } else if (
            std::holds_alternative<_after_sum_of_max_branches_in_Node>(_popped)) {
      auto _f =
          std::move(std::get<_after_sum_of_max_branches_in_Node>(_popped));
      _stack.pop_back();
      uint64_t a1 = _f.a1;
      const LoopifyMoreTrees::tree &a2 = *_f.a2;
      _stack.emplace_back(_after_sum_of_max_branches_in_Node_2{a1, _result});
      _stack.emplace_back(_call{&a2});
    } else {
      auto _f =
          std::move(std::get<_after_sum_of_max_branches_in_Node_2>(_popped));
      _stack.pop_back();
      uint64_t a1 = _f.a1;
      _result = (a1 + std::max(_f._tmp2, _result));
    }
  }
  return _result;
}

LoopifyMoreTrees::tree
LoopifyMoreTrees::insert_bst(uint64_t x, const LoopifyMoreTrees::tree &t) {
  // Explicit stack replaces the non-tail recursion of insert_bst: _call frames
  // are pending calls, _after frames resume a caller.
  struct _call {
    const LoopifyMoreTrees::tree *t;
  };

  struct _after_insert_bst_in_false {
    std::shared_ptr<LoopifyMoreTrees::tree> a0;
    uint64_t a1;
  };

  struct _after_insert_bst_in_true {
    uint64_t a1;
    std::shared_ptr<LoopifyMoreTrees::tree> a2;
  };

  using _frame = std::variant<_call, _after_insert_bst_in_false,
                              _after_insert_bst_in_true>;
  LoopifyMoreTrees::tree _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&t});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const LoopifyMoreTrees::tree &t = *_f.t;
      if (std::holds_alternative<typename LoopifyMoreTrees::tree::Leaf>(t.v())) {
        _result = tree::node(tree::leaf(), x, tree::leaf());
      } else {
        const auto &[a0, a1, a2] =
            std::get<typename LoopifyMoreTrees::tree::Node>(t.v());
        if (x <= a1) {
          _stack.emplace_back(_after_insert_bst_in_true{a1, a2});
          _stack.emplace_back(_call{crane_raw(a0)});
        } else {
          _stack.emplace_back(_after_insert_bst_in_false{a0, a1});
          _stack.emplace_back(_call{crane_raw(a2)});
        }
      }
    } else if (std::holds_alternative<_after_insert_bst_in_false>(_popped)) {
      auto _f = std::move(std::get<_after_insert_bst_in_false>(_popped));
      _stack.pop_back();
      std::shared_ptr<LoopifyMoreTrees::tree> a0 = std::move(_f.a0);
      uint64_t a1 = _f.a1;
      _result = tree::node(crane::shared_child(a0), a1, std::move(_result));
    } else {
      auto _f = std::move(std::get<_after_insert_bst_in_true>(_popped));
      _stack.pop_back();
      uint64_t a1 = _f.a1;
      std::shared_ptr<LoopifyMoreTrees::tree> a2 = std::move(_f.a2);
      _result = tree::node(std::move(_result), a1, crane::shared_child(a2));
    }
  }
  return _result;
}

LoopifyMoreTrees::tree LoopifyMoreTrees::build_bst(const List<uint64_t> &l) {
  // Explicit stack replaces the non-tail recursion of build_bst: _call frames
  // are pending calls, _after frames resume a caller.
  struct _call {
    const List<uint64_t> *l;
  };

  struct _after_build_bst_in_Cons {
    uint64_t a0;
  };

  using _frame = std::variant<_call, _after_build_bst_in_Cons>;
  LoopifyMoreTrees::tree _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&l});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const List<uint64_t> &l = *_f.l;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
        _result = tree::leaf();
      } else {
        const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
        _stack.emplace_back(_after_build_bst_in_Cons{a0});
        _stack.emplace_back(_call{crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<_after_build_bst_in_Cons>(_popped));
      _stack.pop_back();
      uint64_t a0 = _f.a0;
      _result = insert_bst(a0, std::move(_result));
    }
  }
  return _result;
}

List<uint64_t> LoopifyMoreTrees::append_lists(const List<uint64_t> &l1,
                                              List<uint64_t> l2) {
  // Builds the result front to back: _write points at the empty tail the next
  // cell fills.
  std::optional<List<uint64_t>> _root{};
  std::shared_ptr<List<uint64_t>> *_write = nullptr;
  const List<uint64_t> *_loop_l1 = &l1;
  while (true) {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l1->v())) {
      auto _value = std::move(l2);
      (_write ? *(*_write = std::make_shared<List<uint64_t>>(std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename List<uint64_t>::Cons>(_loop_l1->v());
      auto _cell = typename List<uint64_t>::Cons(a0, nullptr);
      List<uint64_t> &_node =
          (_write ? *(*_write =
                          std::make_shared<List<uint64_t>>(std::move(_cell)))
                  : _root.emplace(std::move(_cell)));
      _write = &std::get<typename List<uint64_t>::Cons>(_node.v_mut()).l;
      _loop_l1 = crane_raw(a1);
      continue;
    }
  }
  return std::move(*_root);
}

List<uint64_t> LoopifyMoreTrees::flatten(const List<List<uint64_t>> &ll) {
  // Explicit stack replaces the non-tail recursion of flatten: _call frames are
  // pending calls, _after frames resume a caller.
  struct _call {
    const List<List<uint64_t>> *ll;
  };

  struct _after_flatten_in_Cons {
    List<uint64_t> a0;
  };

  using _frame = std::variant<_call, _after_flatten_in_Cons>;
  List<uint64_t> _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&ll});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const List<List<uint64_t>> &ll = *_f.ll;
      if (std::holds_alternative<typename List<List<uint64_t>>::Nil>(ll.v())) {
        _result = List<uint64_t>::nil();
      } else {
        const auto &[a0, a1] =
            std::get<typename List<List<uint64_t>>::Cons>(ll.v());
        _stack.emplace_back(_after_flatten_in_Cons{a0});
        _stack.emplace_back(_call{crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<_after_flatten_in_Cons>(_popped));
      _stack.pop_back();
      List<uint64_t> a0 = std::move(_f.a0);
      _result = append_lists(std::move(a0), std::move(_result));
    }
  }
  return _result;
}

List<List<uint64_t>>
LoopifyMoreTrees::map_tree_to_list(const List<LoopifyMoreTrees::tree> &lt) {
  // Builds the result front to back: _write points at the empty tail the next
  // cell fills.
  std::optional<List<List<uint64_t>>> _root{};
  std::shared_ptr<List<List<uint64_t>>> *_write = nullptr;
  const List<LoopifyMoreTrees::tree> *_loop_lt = &lt;
  while (true) {
    if (std::holds_alternative<typename List<LoopifyMoreTrees::tree>::Nil>(
            _loop_lt->v())) {
      auto _value = List<List<uint64_t>>::nil();
      (_write ? *(*_write =
                      std::make_shared<List<List<uint64_t>>>(std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename List<LoopifyMoreTrees::tree>::Cons>(_loop_lt->v());
      auto _cell =
          typename List<List<uint64_t>>::Cons(tree_to_list(a0), nullptr);
      List<List<uint64_t>> &_node =
          (_write ? *(*_write = std::make_shared<List<List<uint64_t>>>(
                          std::move(_cell)))
                  : _root.emplace(std::move(_cell)));
      _write = &std::get<typename List<List<uint64_t>>::Cons>(_node.v_mut()).l;
      _loop_lt = crane_raw(a1);
      continue;
    }
  }
  return std::move(*_root);
}

List<LoopifyMoreTrees::tree>
LoopifyMoreTrees::tree_children(const LoopifyMoreTrees::tree &t) {
  if (std::holds_alternative<typename LoopifyMoreTrees::tree::Leaf>(t.v())) {
    return List<LoopifyMoreTrees::tree>::nil();
  } else {
    const auto &[a0, _, a2] =
        std::get<typename LoopifyMoreTrees::tree::Node>(t.v());
    return List<LoopifyMoreTrees::tree>::cons(
        *a0, List<LoopifyMoreTrees::tree>::cons(
                 *a2, List<LoopifyMoreTrees::tree>::nil()));
  }
}

List<LoopifyMoreTrees::tree>
LoopifyMoreTrees::append_trees(const List<LoopifyMoreTrees::tree> &l1,
                               List<LoopifyMoreTrees::tree> l2) {
  // Builds the result front to back: _write points at the empty tail the next
  // cell fills.
  std::optional<List<LoopifyMoreTrees::tree>> _root{};
  std::shared_ptr<List<LoopifyMoreTrees::tree>> *_write = nullptr;
  const List<LoopifyMoreTrees::tree> *_loop_l1 = &l1;
  while (true) {
    if (std::holds_alternative<typename List<LoopifyMoreTrees::tree>::Nil>(
            _loop_l1->v())) {
      auto _value = std::move(l2);
      (_write ? *(*_write = std::make_shared<List<LoopifyMoreTrees::tree>>(
                      std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename List<LoopifyMoreTrees::tree>::Cons>(_loop_l1->v());
      auto _cell = typename List<LoopifyMoreTrees::tree>::Cons(a0, nullptr);
      List<LoopifyMoreTrees::tree> &_node =
          (_write ? *(*_write = std::make_shared<List<LoopifyMoreTrees::tree>>(
                          std::move(_cell)))
                  : _root.emplace(std::move(_cell)));
      _write =
          &std::get<typename List<LoopifyMoreTrees::tree>::Cons>(_node.v_mut()).l;
      _loop_l1 = crane_raw(a1);
      continue;
    }
  }
  return std::move(*_root);
}

List<LoopifyMoreTrees::tree>
LoopifyMoreTrees::concat_map_children(const List<LoopifyMoreTrees::tree> &lt) {
  // Explicit stack replaces the non-tail recursion of concat_map_children:
  // _call frames are pending calls, _after frames resume a caller.
  struct _call {
    const List<LoopifyMoreTrees::tree> *lt;
  };

  struct _after_concat_map_children_in_Cons {
    LoopifyMoreTrees::tree a0;
  };

  using _frame = std::variant<_call, _after_concat_map_children_in_Cons>;
  List<LoopifyMoreTrees::tree> _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&lt});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const List<LoopifyMoreTrees::tree> &lt = *_f.lt;
      if (std::holds_alternative<typename List<LoopifyMoreTrees::tree>::Nil>(
              lt.v())) {
        _result = List<LoopifyMoreTrees::tree>::nil();
      } else {
        const auto &[a0, a1] =
            std::get<typename List<LoopifyMoreTrees::tree>::Cons>(lt.v());
        _stack.emplace_back(_after_concat_map_children_in_Cons{a0});
        _stack.emplace_back(_call{crane_raw(a1)});
      }
    } else {
      auto _f =
          std::move(std::get<_after_concat_map_children_in_Cons>(_popped));
      _stack.pop_back();
      LoopifyMoreTrees::tree a0 = std::move(_f.a0);
      _result = append_trees(tree_children(std::move(a0)), std::move(_result));
    }
  }
  return _result;
}

List<List<uint64_t>>
LoopifyMoreTrees::tree_levels_fuel(uint64_t fuel,
                                   const List<LoopifyMoreTrees::tree> &level) {
  // Builds the result front to back: _write points at the empty tail the next
  // cell fills.
  std::optional<List<List<uint64_t>>> _root{};
  std::shared_ptr<List<List<uint64_t>>> *_write = nullptr;
  List<LoopifyMoreTrees::tree> _loop_level = level;
  while (true) {
    if (fuel <= 0) {
      auto _value = List<List<uint64_t>>::nil();
      (_write ? *(*_write =
                      std::make_shared<List<List<uint64_t>>>(std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      uint64_t fuel_ = fuel - 1;
      if (std::holds_alternative<typename List<LoopifyMoreTrees::tree>::Nil>(
              _loop_level.v())) {
        auto _value = List<List<uint64_t>>::nil();
        (_write ? *(*_write = std::make_shared<List<List<uint64_t>>>(
                        std::move(_value)))
                : _root.emplace(std::move(_value)));
        break;
      } else {
        List<uint64_t> values = flatten(map_tree_to_list(_loop_level));
        List<LoopifyMoreTrees::tree> next = concat_map_children(_loop_level);
        auto _cell =
            typename List<List<uint64_t>>::Cons(std::move(values), nullptr);
        List<List<uint64_t>> &_node =
            (_write ? *(*_write = std::make_shared<List<List<uint64_t>>>(
                            std::move(_cell)))
                    : _root.emplace(std::move(_cell)));
        _write =
            &std::get<typename List<List<uint64_t>>::Cons>(_node.v_mut()).l;
        _loop_level = std::move(next);
        fuel = fuel_;
        continue;
      }
    }
  }
  return std::move(*_root);
}

List<List<uint64_t>>
LoopifyMoreTrees::tree_levels(const LoopifyMoreTrees::tree &t) {
  return tree_levels_fuel(UINT64_C(100),
                          List<LoopifyMoreTrees::tree>::cons(
                              t, List<LoopifyMoreTrees::tree>::nil()));
}
