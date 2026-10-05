#include "loopify_more_trees.h"

LoopifyMoreTrees::tree LoopifyMoreTrees::mirror(
    const LoopifyMoreTrees::tree &t) { /// CraneEnter: captures varying
                                       /// parameters for each recursive call.

  struct CraneEnter {
    const LoopifyMoreTrees::tree *t;
  };

  /// CraneCont_Node: saves [a0, a1], resumes after recursive call, then
  /// processes rest.
  struct CraneCont_Node {
    const LoopifyMoreTrees::tree *a0;
    uint64_t a1;
  };

  /// CraneCont_Node_1: saves [_tmp2, a1], resumes after recursive call, then
  /// processes rest.
  struct CraneCont_Node_1 {
    LoopifyMoreTrees::tree _tmp2;
    uint64_t a1;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont_Node, CraneCont_Node_1>;
  LoopifyMoreTrees::tree _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{&t});
  /// Loopified mirror: CraneEnter -> CraneCont_Node -> CraneCont_Node_1.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      const LoopifyMoreTrees::tree &t = *_f.t;
      if (std::holds_alternative<typename LoopifyMoreTrees::tree::Leaf>(
              t.v())) {
        _result = tree::leaf();
      } else {
        const auto &[a0, a1, a2] =
            std::get<typename LoopifyMoreTrees::tree::Node>(t.v());
        _stack.emplace_back(CraneCont_Node{crane_raw(a0), a1});
        _stack.emplace_back(CraneEnter{crane_raw(a2)});
      }
    } else if (std::holds_alternative<CraneCont_Node>(_frame)) {
      auto _f = std::move(std::get<CraneCont_Node>(_frame));
      const LoopifyMoreTrees::tree &a0 = *_f.a0;
      uint64_t a1 = _f.a1;
      _stack.emplace_back(CraneCont_Node_1{std::move(_result), a1});
      _stack.emplace_back(CraneEnter{&a0});
    } else {
      auto _f = std::move(std::get<CraneCont_Node_1>(_frame));
      uint64_t a1 = _f.a1;
      _result = tree::node(std::move(_f._tmp2), a1, std::move(_result));
    }
  }
  return _result;
}

bool LoopifyMoreTrees::same_shape(
    const LoopifyMoreTrees::tree &t1,
    const LoopifyMoreTrees::tree &t2) { /// CraneEnter: captures varying
                                        /// parameters for each recursive call.

  struct CraneEnter {
    const LoopifyMoreTrees::tree *t2;
    const LoopifyMoreTrees::tree *t1;
  };

  /// CraneCont_Node: saves [a2, a20], resumes after recursive call, then
  /// processes rest.
  struct CraneCont_Node {
    const LoopifyMoreTrees::tree *a2;
    const LoopifyMoreTrees::tree *a20;
  };

  /// CraneCont_Node_1: saves [_tmp2], resumes after recursive call, then
  /// processes rest.
  struct CraneCont_Node_1 {
    bool _tmp2;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont_Node, CraneCont_Node_1>;
  bool _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{&t2, &t1});
  /// Loopified same_shape: CraneEnter -> CraneCont_Node -> CraneCont_Node_1.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
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
          _stack.emplace_back(CraneCont_Node{crane_raw(a2), crane_raw(a20)});
          _stack.emplace_back(CraneEnter{crane_raw(a00), crane_raw(a0)});
        }
      }
    } else if (std::holds_alternative<CraneCont_Node>(_frame)) {
      auto _f = std::move(std::get<CraneCont_Node>(_frame));
      const LoopifyMoreTrees::tree &a2 = *_f.a2;
      const LoopifyMoreTrees::tree &a20 = *_f.a20;
      _stack.emplace_back(CraneCont_Node_1{std::move(_result)});
      _stack.emplace_back(CraneEnter{&a20, &a2});
    } else {
      auto _f = std::move(std::get<CraneCont_Node_1>(_frame));
      _result = (_f._tmp2 && std::move(_result));
    }
  }
  return _result;
}

List<uint64_t> LoopifyMoreTrees::tree_to_list(
    const LoopifyMoreTrees::tree &t) { /// CraneEnter: captures varying
                                       /// parameters for each recursive call.

  struct CraneEnter {
    const LoopifyMoreTrees::tree *t;
  };

  /// CraneCont_Node: saves [a1, a2], resumes after recursive call, then
  /// processes rest.
  struct CraneCont_Node {
    uint64_t a1;
    const LoopifyMoreTrees::tree *a2;
  };

  /// CraneCont_Node_1: saves [_tmp2, a1], resumes after recursive call, then
  /// processes rest.
  struct CraneCont_Node_1 {
    List<uint64_t> _tmp2;
    uint64_t a1;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont_Node, CraneCont_Node_1>;
  List<uint64_t> _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{&t});
  /// Loopified tree_to_list: CraneEnter -> CraneCont_Node -> CraneCont_Node_1.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      const LoopifyMoreTrees::tree &t = *_f.t;
      if (std::holds_alternative<typename LoopifyMoreTrees::tree::Leaf>(
              t.v())) {
        _result = List<uint64_t>::nil();
      } else {
        const auto &[a0, a1, a2] =
            std::get<typename LoopifyMoreTrees::tree::Node>(t.v());
        _stack.emplace_back(CraneCont_Node{a1, crane_raw(a2)});
        _stack.emplace_back(CraneEnter{crane_raw(a0)});
      }
    } else if (std::holds_alternative<CraneCont_Node>(_frame)) {
      auto _f = std::move(std::get<CraneCont_Node>(_frame));
      uint64_t a1 = _f.a1;
      const LoopifyMoreTrees::tree &a2 = *_f.a2;
      _stack.emplace_back(CraneCont_Node_1{std::move(_result), a1});
      _stack.emplace_back(CraneEnter{&a2});
    } else {
      auto _f = std::move(std::get<CraneCont_Node_1>(_frame));
      uint64_t a1 = _f.a1;
      _result = std::move(_f._tmp2).app(
          List<uint64_t>::cons(a1, List<uint64_t>::nil())
              .app(std::move(_result)));
    }
  }
  return _result;
}

bool LoopifyMoreTrees::mirror_equal(const LoopifyMoreTrees::tree &t) {
  return same_shape(t, mirror(t));
}

uint64_t LoopifyMoreTrees::count_nodes(
    const LoopifyMoreTrees::tree &t) { /// CraneEnter: captures varying
                                       /// parameters for each recursive call.

  struct CraneEnter {
    const LoopifyMoreTrees::tree *t;
  };

  /// CraneCont_Node: saves [a2], resumes after recursive call, then processes
  /// rest.
  struct CraneCont_Node {
    const LoopifyMoreTrees::tree *a2;
  };

  /// CraneCont_Node_1: saves [_tmp2], resumes after recursive call, then
  /// processes rest.
  struct CraneCont_Node_1 {
    uint64_t _tmp2;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont_Node, CraneCont_Node_1>;
  uint64_t _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{&t});
  /// Loopified count_nodes: CraneEnter -> CraneCont_Node -> CraneCont_Node_1.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      const LoopifyMoreTrees::tree &t = *_f.t;
      if (std::holds_alternative<typename LoopifyMoreTrees::tree::Leaf>(
              t.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1, a2] =
            std::get<typename LoopifyMoreTrees::tree::Node>(t.v());
        _stack.emplace_back(CraneCont_Node{crane_raw(a2)});
        _stack.emplace_back(CraneEnter{crane_raw(a0)});
      }
    } else if (std::holds_alternative<CraneCont_Node>(_frame)) {
      auto _f = std::move(std::get<CraneCont_Node>(_frame));
      const LoopifyMoreTrees::tree &a2 = *_f.a2;
      _stack.emplace_back(CraneCont_Node_1{std::move(_result)});
      _stack.emplace_back(CraneEnter{&a2});
    } else {
      auto _f = std::move(std::get<CraneCont_Node_1>(_frame));
      _result = ((UINT64_C(1) + _f._tmp2) + std::move(_result));
    }
  }
  return _result;
}

LoopifyMoreTrees::tree LoopifyMoreTrees::tree_max(
    LoopifyMoreTrees::tree t1,
    LoopifyMoreTrees::tree t2) { /// CraneEnter: captures varying parameters for
                                 /// each recursive call.

  struct CraneEnter {
    LoopifyMoreTrees::tree t2;
    LoopifyMoreTrees::tree t1;
  };

  /// CraneCont_Node: saves [a1, a10, a2, a20], resumes after recursive call,
  /// then processes rest.
  struct CraneCont_Node {
    uint64_t a1;
    uint64_t a10;
    std::shared_ptr<LoopifyMoreTrees::tree> a2;
    std::shared_ptr<LoopifyMoreTrees::tree> a20;
  };

  /// CraneCont_Node_1: saves [_tmp2, a1, a10], resumes after recursive call,
  /// then processes rest.
  struct CraneCont_Node_1 {
    LoopifyMoreTrees::tree _tmp2;
    uint64_t a1;
    uint64_t a10;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont_Node, CraneCont_Node_1>;
  LoopifyMoreTrees::tree _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{std::move(t2), std::move(t1)});
  /// Loopified tree_max: CraneEnter -> CraneCont_Node -> CraneCont_Node_1.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
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
          _stack.emplace_back(CraneCont_Node{a1, a10, a2, a20});
          _stack.emplace_back(CraneEnter{*a00, *a0});
        }
      }
    } else if (std::holds_alternative<CraneCont_Node>(_frame)) {
      auto _f = std::move(std::get<CraneCont_Node>(_frame));
      uint64_t a1 = _f.a1;
      uint64_t a10 = _f.a10;
      std::shared_ptr<LoopifyMoreTrees::tree> a2 = std::move(_f.a2);
      std::shared_ptr<LoopifyMoreTrees::tree> a20 = std::move(_f.a20);
      _stack.emplace_back(CraneCont_Node_1{std::move(_result), a1, a10});
      _stack.emplace_back(CraneEnter{*a20, *a2});
    } else {
      auto _f = std::move(std::get<CraneCont_Node_1>(_frame));
      uint64_t a1 = _f.a1;
      uint64_t a10 = _f.a10;
      _result = tree::node(std::move(_f._tmp2), std::max(a1, std::move(a10)),
                           std::move(_result));
    }
  }
  return _result;
}

uint64_t LoopifyMoreTrees::sum_of_max_branches(
    const LoopifyMoreTrees::tree &t) { /// CraneEnter: captures varying
                                       /// parameters for each recursive call.

  struct CraneEnter {
    const LoopifyMoreTrees::tree *t;
  };

  /// CraneCont_Node: saves [a1, a2], resumes after recursive call, then
  /// processes rest.
  struct CraneCont_Node {
    uint64_t a1;
    const LoopifyMoreTrees::tree *a2;
  };

  /// CraneCont_Node_1: saves [_tmp2, a1], resumes after recursive call, then
  /// processes rest.
  struct CraneCont_Node_1 {
    uint64_t _tmp2;
    uint64_t a1;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont_Node, CraneCont_Node_1>;
  uint64_t _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{&t});
  /// Loopified sum_of_max_branches: CraneEnter -> CraneCont_Node ->
  /// CraneCont_Node_1.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      const LoopifyMoreTrees::tree &t = *_f.t;
      if (std::holds_alternative<typename LoopifyMoreTrees::tree::Leaf>(
              t.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1, a2] =
            std::get<typename LoopifyMoreTrees::tree::Node>(t.v());
        _stack.emplace_back(CraneCont_Node{a1, crane_raw(a2)});
        _stack.emplace_back(CraneEnter{crane_raw(a0)});
      }
    } else if (std::holds_alternative<CraneCont_Node>(_frame)) {
      auto _f = std::move(std::get<CraneCont_Node>(_frame));
      uint64_t a1 = _f.a1;
      const LoopifyMoreTrees::tree &a2 = *_f.a2;
      _stack.emplace_back(CraneCont_Node_1{std::move(_result), a1});
      _stack.emplace_back(CraneEnter{&a2});
    } else {
      auto _f = std::move(std::get<CraneCont_Node_1>(_frame));
      uint64_t a1 = _f.a1;
      _result = (a1 + std::max(_f._tmp2, std::move(_result)));
    }
  }
  return _result;
}

LoopifyMoreTrees::tree LoopifyMoreTrees::insert_bst(
    uint64_t x,
    const LoopifyMoreTrees::tree &t) { /// CraneEnter: captures varying
                                       /// parameters for each recursive call.

  struct CraneEnter {
    const LoopifyMoreTrees::tree *t;
  };

  /// CraneCont1: saves [a1, a2], resumes after recursive call, then processes
  /// rest.
  struct CraneCont1 {
    uint64_t a1;
    std::shared_ptr<LoopifyMoreTrees::tree> a2;
  };

  /// CraneCont2: saves [a0, a1], resumes after recursive call, then processes
  /// rest.
  struct CraneCont2 {
    std::shared_ptr<LoopifyMoreTrees::tree> a0;
    uint64_t a1;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont1, CraneCont2>;
  LoopifyMoreTrees::tree _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{&t});
  /// Loopified insert_bst: CraneEnter -> CraneCont1 -> CraneCont2.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      const LoopifyMoreTrees::tree &t = *_f.t;
      if (std::holds_alternative<typename LoopifyMoreTrees::tree::Leaf>(
              t.v())) {
        _result = tree::node(tree::leaf(), x, tree::leaf());
      } else {
        const auto &[a0, a1, a2] =
            std::get<typename LoopifyMoreTrees::tree::Node>(t.v());
        if (x <= a1) {
          _stack.emplace_back(CraneCont1{a1, a2});
          _stack.emplace_back(CraneEnter{crane_raw(a0)});
        } else {
          _stack.emplace_back(CraneCont2{a0, a1});
          _stack.emplace_back(CraneEnter{crane_raw(a2)});
        }
      }
    } else if (std::holds_alternative<CraneCont1>(_frame)) {
      auto _f = std::move(std::get<CraneCont1>(_frame));
      uint64_t a1 = _f.a1;
      std::shared_ptr<LoopifyMoreTrees::tree> a2 = std::move(_f.a2);
      _result = tree::node(std::move(_result), a1, *a2);
    } else {
      auto _f = std::move(std::get<CraneCont2>(_frame));
      std::shared_ptr<LoopifyMoreTrees::tree> a0 = std::move(_f.a0);
      uint64_t a1 = _f.a1;
      _result = tree::node(*a0, a1, std::move(_result));
    }
  }
  return _result;
}

LoopifyMoreTrees::tree LoopifyMoreTrees::build_bst(
    const List<uint64_t> &l) { /// CraneEnter: captures varying parameters for
                               /// each recursive call.

  struct CraneEnter {
    const List<uint64_t> *l;
  };

  /// CraneCont_Cons: saves [a0], resumes after recursive call, then processes
  /// rest.
  struct CraneCont_Cons {
    uint64_t a0;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont_Cons>;
  LoopifyMoreTrees::tree _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{&l});
  /// Loopified build_bst: CraneEnter -> CraneCont_Cons.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      const List<uint64_t> &l = *_f.l;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
        _result = tree::leaf();
      } else {
        const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
        _stack.emplace_back(CraneCont_Cons{a0});
        _stack.emplace_back(CraneEnter{crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<CraneCont_Cons>(_frame));
      uint64_t a0 = _f.a0;
      _result = insert_bst(a0, std::move(_result));
    }
  }
  return _result;
}

List<uint64_t> LoopifyMoreTrees::append_lists(const List<uint64_t> &l1,
                                              List<uint64_t> l2) {
  std::optional<List<uint64_t>> _root{};
  std::shared_ptr<List<uint64_t>> *_write = nullptr;
  List<uint64_t> _loop_l2 = std::move(l2);
  const List<uint64_t> *_loop_l1 = &l1;
  while (true) {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l1->v())) {
      auto _value = std::move(_loop_l2);
      (_write ? *(*_write = std::make_shared<List<uint64_t>>(std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename List<uint64_t>::Cons>(_loop_l1->v());
      auto _cell = typename List<uint64_t>::Cons(a0, nullptr);
      List<uint64_t> &_node =
          (_write
               ? *(*_write = std::make_shared<List<uint64_t>>(std::move(_cell)))
               : _root.emplace(std::move(_cell)));
      _write = &std::get<typename List<uint64_t>::Cons>(_node.v_mut()).l;
      _loop_l1 = crane_raw(a1);
      continue;
    }
  }
  return std::move(*_root);
}

List<uint64_t> LoopifyMoreTrees::flatten(
    const List<List<uint64_t>> &ll) { /// CraneEnter: captures varying
                                      /// parameters for each recursive call.

  struct CraneEnter {
    const List<List<uint64_t>> *ll;
  };

  /// CraneCont_Cons: saves [a0], resumes after recursive call, then processes
  /// rest.
  struct CraneCont_Cons {
    List<uint64_t> a0;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont_Cons>;
  List<uint64_t> _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{&ll});
  /// Loopified flatten: CraneEnter -> CraneCont_Cons.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      const List<List<uint64_t>> &ll = *_f.ll;
      if (std::holds_alternative<typename List<List<uint64_t>>::Nil>(ll.v())) {
        _result = List<uint64_t>::nil();
      } else {
        const auto &[a0, a1] =
            std::get<typename List<List<uint64_t>>::Cons>(ll.v());
        _stack.emplace_back(CraneCont_Cons{a0});
        _stack.emplace_back(CraneEnter{crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<CraneCont_Cons>(_frame));
      List<uint64_t> a0 = std::move(_f.a0);
      _result = append_lists(a0, std::move(_result));
    }
  }
  return _result;
}

List<List<uint64_t>>
LoopifyMoreTrees::map_tree_to_list(const List<LoopifyMoreTrees::tree> &lt) {
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
  std::optional<List<LoopifyMoreTrees::tree>> _root{};
  std::shared_ptr<List<LoopifyMoreTrees::tree>> *_write = nullptr;
  List<LoopifyMoreTrees::tree> _loop_l2 = std::move(l2);
  const List<LoopifyMoreTrees::tree> *_loop_l1 = &l1;
  while (true) {
    if (std::holds_alternative<typename List<LoopifyMoreTrees::tree>::Nil>(
            _loop_l1->v())) {
      auto _value = std::move(_loop_l2);
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
          &std::get<typename List<LoopifyMoreTrees::tree>::Cons>(_node.v_mut())
               .l;
      _loop_l1 = crane_raw(a1);
      continue;
    }
  }
  return std::move(*_root);
}

List<LoopifyMoreTrees::tree> LoopifyMoreTrees::concat_map_children(
    const List<LoopifyMoreTrees::tree>
        &lt) { /// CraneEnter: captures varying parameters for each recursive
               /// call.

  struct CraneEnter {
    const List<LoopifyMoreTrees::tree> *lt;
  };

  /// CraneCont_Cons: saves [a0], resumes after recursive call, then processes
  /// rest.
  struct CraneCont_Cons {
    LoopifyMoreTrees::tree a0;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont_Cons>;
  List<LoopifyMoreTrees::tree> _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{&lt});
  /// Loopified concat_map_children: CraneEnter -> CraneCont_Cons.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      const List<LoopifyMoreTrees::tree> &lt = *_f.lt;
      if (std::holds_alternative<typename List<LoopifyMoreTrees::tree>::Nil>(
              lt.v())) {
        _result = List<LoopifyMoreTrees::tree>::nil();
      } else {
        const auto &[a0, a1] =
            std::get<typename List<LoopifyMoreTrees::tree>::Cons>(lt.v());
        _stack.emplace_back(CraneCont_Cons{a0});
        _stack.emplace_back(CraneEnter{crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<CraneCont_Cons>(_frame));
      LoopifyMoreTrees::tree a0 = std::move(_f.a0);
      _result = append_trees(tree_children(a0), std::move(_result));
    }
  }
  return _result;
}

List<List<uint64_t>>
LoopifyMoreTrees::tree_levels_fuel(uint64_t fuel,
                                   const List<LoopifyMoreTrees::tree> &level) {
  std::optional<List<List<uint64_t>>> _root{};
  std::shared_ptr<List<List<uint64_t>>> *_write = nullptr;
  List<LoopifyMoreTrees::tree> _loop_level = level;
  uint64_t _loop_fuel = fuel;
  while (true) {
    if (_loop_fuel <= 0) {
      auto _value = List<List<uint64_t>>::nil();
      (_write ? *(*_write =
                      std::make_shared<List<List<uint64_t>>>(std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      uint64_t fuel_ = _loop_fuel - 1;
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
        _loop_fuel = fuel_;
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
