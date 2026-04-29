#include <loopify_more_trees.h>

__attribute__((pure)) LoopifyMoreTrees::tree
LoopifyMoreTrees::mirror(const LoopifyMoreTrees::tree &t) {
  struct _Enter {
    const LoopifyMoreTrees::tree *t;
  };

  struct _Call1 {
    const LoopifyMoreTrees::tree *_s0;
    unsigned int _s1;
  };

  struct _Call2 {
    LoopifyMoreTrees::tree _s0;
    unsigned int _s1;
  };

  using _Frame = std::variant<_Enter, _Call1, _Call2>;
  LoopifyMoreTrees::tree _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{&t});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const LoopifyMoreTrees::tree &t = *(_f.t);
      if (std::holds_alternative<typename LoopifyMoreTrees::tree::Leaf>(
              t.v())) {
        _result = tree::leaf();
      } else {
        const auto &[d_a0, d_a1, d_a2] =
            std::get<typename LoopifyMoreTrees::tree::Node>(t.v());
        _stack.emplace_back(_Call1{d_a2.get(), d_a1});
        _stack.emplace_back(_Enter{d_a0.get()});
      }
    } else if (std::holds_alternative<_Call1>(_frame)) {
      auto _f = std::move(std::get<_Call1>(_frame));
      _stack.emplace_back(_Call2{_result, _f._s1});
      _stack.emplace_back(_Enter{_f._s0});
    } else {
      auto _f = std::move(std::get<_Call2>(_frame));
      _result = tree::node(_result, _f._s1, _f._s0);
    }
  }
  return _result;
}

__attribute__((pure)) bool
LoopifyMoreTrees::same_shape(const LoopifyMoreTrees::tree &t1,
                             const LoopifyMoreTrees::tree &t2) {
  struct _Enter {
    const LoopifyMoreTrees::tree *t2;
    const LoopifyMoreTrees::tree *t1;
  };

  struct _Call1 {
    const LoopifyMoreTrees::tree *_s0;
    const LoopifyMoreTrees::tree *_s1;
  };

  struct _Call2 {
    bool _s0;
  };

  using _Frame = std::variant<_Enter, _Call1, _Call2>;
  bool _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{&t2, &t1});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const LoopifyMoreTrees::tree &t2 = *(_f.t2);
      const LoopifyMoreTrees::tree &t1 = *(_f.t1);
      if (std::holds_alternative<typename LoopifyMoreTrees::tree::Leaf>(
              t1.v())) {
        if (std::holds_alternative<typename LoopifyMoreTrees::tree::Leaf>(
                t2.v())) {
          _result = true;
        } else {
          _result = false;
        }
      } else {
        const auto &[d_a0, d_a1, d_a2] =
            std::get<typename LoopifyMoreTrees::tree::Node>(t1.v());
        if (std::holds_alternative<typename LoopifyMoreTrees::tree::Leaf>(
                t2.v())) {
          _result = false;
        } else {
          const auto &[d_a00, d_a10, d_a20] =
              std::get<typename LoopifyMoreTrees::tree::Node>(t2.v());
          _stack.emplace_back(_Call1{d_a00.get(), d_a0.get()});
          _stack.emplace_back(_Enter{d_a20.get(), d_a2.get()});
        }
      }
    } else if (std::holds_alternative<_Call1>(_frame)) {
      auto _f = std::move(std::get<_Call1>(_frame));
      _stack.emplace_back(_Call2{_result});
      _stack.emplace_back(_Enter{_f._s0, _f._s1});
    } else {
      auto _f = std::move(std::get<_Call2>(_frame));
      _result = (_result && _f._s0);
    }
  }
  return _result;
}

__attribute__((pure)) List<unsigned int>
LoopifyMoreTrees::tree_to_list(const LoopifyMoreTrees::tree &t) {
  struct _Enter {
    const LoopifyMoreTrees::tree *t;
  };

  struct _Call1 {
    const LoopifyMoreTrees::tree *_s0;
    decltype(List<unsigned int>::cons(std::declval<unsigned int &>(),
                                      List<unsigned int>::nil())) _s1;
  };

  struct _Call2 {
    List<unsigned int> _s0;
    decltype(List<unsigned int>::cons(std::declval<unsigned int &>(),
                                      List<unsigned int>::nil())) _s1;
  };

  using _Frame = std::variant<_Enter, _Call1, _Call2>;
  List<unsigned int> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{&t});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const LoopifyMoreTrees::tree &t = *(_f.t);
      if (std::holds_alternative<typename LoopifyMoreTrees::tree::Leaf>(
              t.v())) {
        _result = List<unsigned int>::nil();
      } else {
        const auto &[d_a0, d_a1, d_a2] =
            std::get<typename LoopifyMoreTrees::tree::Node>(t.v());
        _stack.emplace_back(
            _Call1{d_a0.get(),
                   List<unsigned int>::cons(d_a1, List<unsigned int>::nil())});
        _stack.emplace_back(_Enter{d_a2.get()});
      }
    } else if (std::holds_alternative<_Call1>(_frame)) {
      auto _f = std::move(std::get<_Call1>(_frame));
      _stack.emplace_back(_Call2{_result, _f._s1});
      _stack.emplace_back(_Enter{_f._s0});
    } else {
      auto _f = std::move(std::get<_Call2>(_frame));
      _result = _result.app(_f._s1.app(_f._s0));
    }
  }
  return _result;
}

__attribute__((pure)) bool
LoopifyMoreTrees::mirror_equal(const LoopifyMoreTrees::tree &t) {
  return same_shape(t, mirror(t));
}

__attribute__((pure)) unsigned int
LoopifyMoreTrees::count_nodes(const LoopifyMoreTrees::tree &t) {
  struct _Enter {
    const LoopifyMoreTrees::tree *t;
  };

  struct _Call1 {
    const LoopifyMoreTrees::tree *_s0;
    decltype(1u) _s1;
  };

  struct _Call2 {
    unsigned int _s0;
    decltype(1u) _s1;
  };

  using _Frame = std::variant<_Enter, _Call1, _Call2>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{&t});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const LoopifyMoreTrees::tree &t = *(_f.t);
      if (std::holds_alternative<typename LoopifyMoreTrees::tree::Leaf>(
              t.v())) {
        _result = 0u;
      } else {
        const auto &[d_a0, d_a1, d_a2] =
            std::get<typename LoopifyMoreTrees::tree::Node>(t.v());
        _stack.emplace_back(_Call1{d_a0.get(), 1u});
        _stack.emplace_back(_Enter{d_a2.get()});
      }
    } else if (std::holds_alternative<_Call1>(_frame)) {
      auto _f = std::move(std::get<_Call1>(_frame));
      _stack.emplace_back(_Call2{_result, _f._s1});
      _stack.emplace_back(_Enter{_f._s0});
    } else {
      auto _f = std::move(std::get<_Call2>(_frame));
      _result = ((_f._s1 + _result) + _f._s0);
    }
  }
  return _result;
}

__attribute__((pure)) LoopifyMoreTrees::tree
LoopifyMoreTrees::tree_max(LoopifyMoreTrees::tree t1,
                           LoopifyMoreTrees::tree t2) {
  struct _Enter {
    LoopifyMoreTrees::tree t2;
    LoopifyMoreTrees::tree t1;
  };

  struct _Call1 {
    LoopifyMoreTrees::tree _s0;
    LoopifyMoreTrees::tree _s1;
    decltype(std::max(std::declval<unsigned int &>(),
                      std::declval<unsigned int &>())) _s2;
  };

  struct _Call2 {
    LoopifyMoreTrees::tree _s0;
    decltype(std::max(std::declval<unsigned int &>(),
                      std::declval<unsigned int &>())) _s1;
  };

  using _Frame = std::variant<_Enter, _Call1, _Call2>;
  LoopifyMoreTrees::tree _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{t2, t1});
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
        auto &[d_a0, d_a1, d_a2] =
            std::get<typename LoopifyMoreTrees::tree::Node>(t1.v_mut());
        if (std::holds_alternative<typename LoopifyMoreTrees::tree::Leaf>(
                t2.v_mut())) {
          _result = t1;
        } else {
          auto &[d_a00, d_a10, d_a20] =
              std::get<typename LoopifyMoreTrees::tree::Node>(t2.v_mut());
          _stack.emplace_back(_Call1{*(d_a00), *(d_a0), std::max(d_a1, d_a10)});
          _stack.emplace_back(_Enter{*(d_a20), *(d_a2)});
        }
      }
    } else if (std::holds_alternative<_Call1>(_frame)) {
      auto _f = std::move(std::get<_Call1>(_frame));
      _stack.emplace_back(_Call2{_result, _f._s2});
      _stack.emplace_back(_Enter{_f._s0, _f._s1});
    } else {
      auto _f = std::move(std::get<_Call2>(_frame));
      _result = tree::node(_result, _f._s1, _f._s0);
    }
  }
  return _result;
}

__attribute__((pure)) unsigned int
LoopifyMoreTrees::sum_of_max_branches(const LoopifyMoreTrees::tree &t) {
  struct _Enter {
    const LoopifyMoreTrees::tree *t;
  };

  struct _Call1 {
    const LoopifyMoreTrees::tree *_s0;
    unsigned int _s1;
  };

  struct _Call2 {
    unsigned int _s0;
    unsigned int _s1;
  };

  using _Frame = std::variant<_Enter, _Call1, _Call2>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{&t});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const LoopifyMoreTrees::tree &t = *(_f.t);
      if (std::holds_alternative<typename LoopifyMoreTrees::tree::Leaf>(
              t.v())) {
        _result = 0u;
      } else {
        const auto &[d_a0, d_a1, d_a2] =
            std::get<typename LoopifyMoreTrees::tree::Node>(t.v());
        _stack.emplace_back(_Call1{d_a0.get(), d_a1});
        _stack.emplace_back(_Enter{d_a2.get()});
      }
    } else if (std::holds_alternative<_Call1>(_frame)) {
      auto _f = std::move(std::get<_Call1>(_frame));
      _stack.emplace_back(_Call2{_result, _f._s1});
      _stack.emplace_back(_Enter{_f._s0});
    } else {
      auto _f = std::move(std::get<_Call2>(_frame));
      _result = (_f._s1 + std::max(_result, _f._s0));
    }
  }
  return _result;
}

__attribute__((pure)) LoopifyMoreTrees::tree
LoopifyMoreTrees::insert_bst(unsigned int x, const LoopifyMoreTrees::tree &t) {
  struct _Enter {
    const LoopifyMoreTrees::tree *t;
  };

  struct _Call1 {
    LoopifyMoreTrees::tree _s0;
    unsigned int _s1;
  };

  struct _Call2 {
    unsigned int _s0;
    LoopifyMoreTrees::tree _s1;
  };

  using _Frame = std::variant<_Enter, _Call1, _Call2>;
  LoopifyMoreTrees::tree _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{&t});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const LoopifyMoreTrees::tree &t = *(_f.t);
      if (std::holds_alternative<typename LoopifyMoreTrees::tree::Leaf>(
              t.v())) {
        _result = tree::node(tree::leaf(), x, tree::leaf());
      } else {
        const auto &[d_a0, d_a1, d_a2] =
            std::get<typename LoopifyMoreTrees::tree::Node>(t.v());
        if (x <= d_a1) {
          _stack.emplace_back(_Call1{*(d_a2), d_a1});
          _stack.emplace_back(_Enter{d_a0.get()});
        } else {
          _stack.emplace_back(_Call2{d_a1, *(d_a0)});
          _stack.emplace_back(_Enter{d_a2.get()});
        }
      }
    } else if (std::holds_alternative<_Call1>(_frame)) {
      auto _f = std::move(std::get<_Call1>(_frame));
      _result = tree::node(_result, _f._s1, _f._s0);
    } else {
      auto _f = std::move(std::get<_Call2>(_frame));
      _result = tree::node(_f._s1, _f._s0, _result);
    }
  }
  return _result;
}

__attribute__((pure)) LoopifyMoreTrees::tree
LoopifyMoreTrees::build_bst(const List<unsigned int> &l) {
  struct _Enter {
    const List<unsigned int> *l;
  };

  struct _Call1 {
    unsigned int _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  LoopifyMoreTrees::tree _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{&l});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<unsigned int> &l = *(_f.l);
      if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
        _result = tree::leaf();
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<unsigned int>::Cons>(l.v());
        _stack.emplace_back(_Call1{d_a0});
        _stack.emplace_back(_Enter{d_a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Call1>(_frame));
      _result = insert_bst(_f._s0, _result);
    }
  }
  return _result;
}

__attribute__((pure)) List<unsigned int>
LoopifyMoreTrees::append_lists(const List<unsigned int> &l1,
                               List<unsigned int> l2) {
  std::unique_ptr<List<unsigned int>> _head{};
  std::unique_ptr<List<unsigned int>> *_write = &_head;
  List<unsigned int> _loop_l2 = std::move(l2);
  const List<unsigned int> *_loop_l1 = &l1;
  while (true) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(
            _loop_l1->v())) {
      *(_write) = std::make_unique<List<unsigned int>>(std::move(_loop_l2));
      break;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<unsigned int>::Cons>(_loop_l1->v());
      auto _cell = std::make_unique<List<unsigned int>>(
          typename List<unsigned int>::Cons(d_a0, nullptr));
      *(_write) = std::move(_cell);
      _write =
          &std::get<typename List<unsigned int>::Cons>((*_write)->v_mut()).d_a1;
      List<unsigned int> _next_l2 = std::move(_loop_l2);
      const List<unsigned int> *_next_l1 = d_a1.get();
      _loop_l2 = std::move(_next_l2);
      _loop_l1 = _next_l1;
      continue;
    }
  }
  return std::move(*(_head));
}

__attribute__((pure)) List<unsigned int>
LoopifyMoreTrees::flatten(const List<List<unsigned int>> &ll) {
  struct _Enter {
    const List<List<unsigned int>> *ll;
  };

  struct _Call1 {
    List<unsigned int> _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  List<unsigned int> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{&ll});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<List<unsigned int>> &ll = *(_f.ll);
      if (std::holds_alternative<typename List<List<unsigned int>>::Nil>(
              ll.v())) {
        _result = List<unsigned int>::nil();
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<List<unsigned int>>::Cons>(ll.v());
        _stack.emplace_back(_Call1{d_a0});
        _stack.emplace_back(_Enter{d_a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Call1>(_frame));
      _result = append_lists(_f._s0, _result);
    }
  }
  return _result;
}

__attribute__((pure)) List<List<unsigned int>>
LoopifyMoreTrees::map_tree_to_list(const List<LoopifyMoreTrees::tree> &lt) {
  std::unique_ptr<List<List<unsigned int>>> _head{};
  std::unique_ptr<List<List<unsigned int>>> *_write = &_head;
  const List<LoopifyMoreTrees::tree> *_loop_lt = &lt;
  while (true) {
    if (std::holds_alternative<typename List<LoopifyMoreTrees::tree>::Nil>(
            _loop_lt->v())) {
      *(_write) = std::make_unique<List<List<unsigned int>>>(
          List<List<unsigned int>>::nil());
      break;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<LoopifyMoreTrees::tree>::Cons>(_loop_lt->v());
      auto _cell = std::make_unique<List<List<unsigned int>>>(
          typename List<List<unsigned int>>::Cons(tree_to_list(d_a0), nullptr));
      *(_write) = std::move(_cell);
      _write =
          &std::get<typename List<List<unsigned int>>::Cons>((*_write)->v_mut())
               .d_a1;
      _loop_lt = d_a1.get();
      continue;
    }
  }
  return std::move(*(_head));
}

__attribute__((pure)) List<LoopifyMoreTrees::tree>
LoopifyMoreTrees::tree_children(const LoopifyMoreTrees::tree &t) {
  if (std::holds_alternative<typename LoopifyMoreTrees::tree::Leaf>(t.v())) {
    return List<LoopifyMoreTrees::tree>::nil();
  } else {
    const auto &[d_a0, d_a1, d_a2] =
        std::get<typename LoopifyMoreTrees::tree::Node>(t.v());
    return List<LoopifyMoreTrees::tree>::cons(
        *(d_a0), List<LoopifyMoreTrees::tree>::cons(
                     *(d_a2), List<LoopifyMoreTrees::tree>::nil()));
  }
}

__attribute__((pure)) List<LoopifyMoreTrees::tree>
LoopifyMoreTrees::append_trees(const List<LoopifyMoreTrees::tree> &l1,
                               List<LoopifyMoreTrees::tree> l2) {
  std::unique_ptr<List<LoopifyMoreTrees::tree>> _head{};
  std::unique_ptr<List<LoopifyMoreTrees::tree>> *_write = &_head;
  List<LoopifyMoreTrees::tree> _loop_l2 = std::move(l2);
  const List<LoopifyMoreTrees::tree> *_loop_l1 = &l1;
  while (true) {
    if (std::holds_alternative<typename List<LoopifyMoreTrees::tree>::Nil>(
            _loop_l1->v())) {
      *(_write) =
          std::make_unique<List<LoopifyMoreTrees::tree>>(std::move(_loop_l2));
      break;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<LoopifyMoreTrees::tree>::Cons>(_loop_l1->v());
      auto _cell = std::make_unique<List<LoopifyMoreTrees::tree>>(
          typename List<LoopifyMoreTrees::tree>::Cons(d_a0, nullptr));
      *(_write) = std::move(_cell);
      _write = &std::get<typename List<LoopifyMoreTrees::tree>::Cons>(
                    (*_write)->v_mut())
                    .d_a1;
      List<LoopifyMoreTrees::tree> _next_l2 = std::move(_loop_l2);
      const List<LoopifyMoreTrees::tree> *_next_l1 = d_a1.get();
      _loop_l2 = std::move(_next_l2);
      _loop_l1 = _next_l1;
      continue;
    }
  }
  return std::move(*(_head));
}

__attribute__((pure)) List<LoopifyMoreTrees::tree>
LoopifyMoreTrees::concat_map_children(const List<LoopifyMoreTrees::tree> &lt) {
  struct _Enter {
    const List<LoopifyMoreTrees::tree> *lt;
  };

  struct _Call1 {
    decltype(tree_children(std::declval<LoopifyMoreTrees::tree &>())) _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  List<LoopifyMoreTrees::tree> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{&lt});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<LoopifyMoreTrees::tree> &lt = *(_f.lt);
      if (std::holds_alternative<typename List<LoopifyMoreTrees::tree>::Nil>(
              lt.v())) {
        _result = List<LoopifyMoreTrees::tree>::nil();
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<LoopifyMoreTrees::tree>::Cons>(lt.v());
        _stack.emplace_back(_Call1{tree_children(d_a0)});
        _stack.emplace_back(_Enter{d_a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Call1>(_frame));
      _result = append_trees(_f._s0, _result);
    }
  }
  return _result;
}

__attribute__((pure)) List<List<unsigned int>>
LoopifyMoreTrees::tree_levels_fuel(const unsigned int &fuel,
                                   const List<LoopifyMoreTrees::tree> &level) {
  std::unique_ptr<List<List<unsigned int>>> _head{};
  std::unique_ptr<List<List<unsigned int>>> *_write = &_head;
  List<LoopifyMoreTrees::tree> _loop_level = level;
  unsigned int _loop_fuel = fuel;
  while (true) {
    if (_loop_fuel <= 0) {
      *(_write) = std::make_unique<List<List<unsigned int>>>(
          List<List<unsigned int>>::nil());
      break;
    } else {
      unsigned int fuel_ = _loop_fuel - 1;
      if (std::holds_alternative<typename List<LoopifyMoreTrees::tree>::Nil>(
              _loop_level.v())) {
        *(_write) = std::make_unique<List<List<unsigned int>>>(
            List<List<unsigned int>>::nil());
        break;
      } else {
        List<unsigned int> values = flatten(map_tree_to_list(_loop_level));
        List<LoopifyMoreTrees::tree> next = concat_map_children(_loop_level);
        auto _cell = std::make_unique<List<List<unsigned int>>>(
            typename List<List<unsigned int>>::Cons(std::move(values),
                                                    nullptr));
        *(_write) = std::move(_cell);
        _write = &std::get<typename List<List<unsigned int>>::Cons>(
                      (*_write)->v_mut())
                      .d_a1;
        List<LoopifyMoreTrees::tree> _next_level = std::move(next);
        unsigned int _next_fuel = fuel_;
        _loop_level = std::move(_next_level);
        _loop_fuel = std::move(_next_fuel);
        continue;
      }
    }
  }
  return std::move(*(_head));
}

__attribute__((pure)) List<List<unsigned int>>
LoopifyMoreTrees::tree_levels(LoopifyMoreTrees::tree t) {
  return tree_levels_fuel(
      100u, List<LoopifyMoreTrees::tree>::cons(
                std::move(t), List<LoopifyMoreTrees::tree>::nil()));
}
