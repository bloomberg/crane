#include <loopify_more_trees.h>

#include <algorithm>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

std::shared_ptr<LoopifyMoreTrees::tree>
LoopifyMoreTrees::mirror(const std::shared_ptr<LoopifyMoreTrees::tree> &t) {
  struct _Enter {
    const std::shared_ptr<LoopifyMoreTrees::tree> t;
  };

  struct _Call1 {
    std::shared_ptr<LoopifyMoreTrees::tree> _s0;
    unsigned int _s1;
  };

  struct _Call2 {
    std::shared_ptr<LoopifyMoreTrees::tree> _s0;
    unsigned int _s1;
  };

  using _Frame = std::variant<_Enter, _Call1, _Call2>;
  std::shared_ptr<LoopifyMoreTrees::tree> _result{};
  std::vector<_Frame> _stack;
  _stack.emplace_back(_Enter{t});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      const auto &_f = std::get<_Enter>(_frame);
      const std::shared_ptr<LoopifyMoreTrees::tree> t = _f.t;
      if (std::holds_alternative<typename LoopifyMoreTrees::tree::Leaf>(
              t->v())) {
        _result = tree::leaf();
      } else {
        const auto &[d_a0, d_a1, d_a2] =
            std::get<typename LoopifyMoreTrees::tree::Node>(t->v());
        _stack.emplace_back(_Call1{d_a2, d_a1});
        _stack.emplace_back(_Enter{d_a0});
      }
    } else if (std::holds_alternative<_Call1>(_frame)) {
      const auto &_f = std::get<_Call1>(_frame);
      _stack.emplace_back(_Call2{_result, _f._s1});
      _stack.emplace_back(_Enter{_f._s0});
    } else {
      const auto &_f = std::get<_Call2>(_frame);
      _result = tree::node(_result, _f._s1, _f._s0);
    }
  }
  return _result;
}

__attribute__((pure)) bool LoopifyMoreTrees::same_shape(
    const std::shared_ptr<LoopifyMoreTrees::tree> &t1,
    const std::shared_ptr<LoopifyMoreTrees::tree> &t2) {
  struct _Enter {
    const std::shared_ptr<LoopifyMoreTrees::tree> t2;
    const std::shared_ptr<LoopifyMoreTrees::tree> t1;
  };

  struct _Call1 {
    std::shared_ptr<LoopifyMoreTrees::tree> _s0;
    std::shared_ptr<LoopifyMoreTrees::tree> _s1;
  };

  struct _Call2 {
    bool _s0;
  };

  using _Frame = std::variant<_Enter, _Call1, _Call2>;
  bool _result{};
  std::vector<_Frame> _stack;
  _stack.emplace_back(_Enter{t2, t1});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      const auto &_f = std::get<_Enter>(_frame);
      const std::shared_ptr<LoopifyMoreTrees::tree> t2 = _f.t2;
      const std::shared_ptr<LoopifyMoreTrees::tree> t1 = _f.t1;
      if (std::holds_alternative<typename LoopifyMoreTrees::tree::Leaf>(
              t1->v())) {
        if (std::holds_alternative<typename LoopifyMoreTrees::tree::Leaf>(
                t2->v())) {
          _result = true;
        } else {
          _result = false;
        }
      } else {
        const auto &[d_a0, d_a1, d_a2] =
            std::get<typename LoopifyMoreTrees::tree::Node>(t1->v());
        if (std::holds_alternative<typename LoopifyMoreTrees::tree::Leaf>(
                t2->v())) {
          _result = false;
        } else {
          const auto &[d_a00, d_a10, d_a20] =
              std::get<typename LoopifyMoreTrees::tree::Node>(t2->v());
          _stack.emplace_back(_Call1{d_a00, d_a0});
          _stack.emplace_back(_Enter{d_a20, d_a2});
        }
      }
    } else if (std::holds_alternative<_Call1>(_frame)) {
      const auto &_f = std::get<_Call1>(_frame);
      _stack.emplace_back(_Call2{_result});
      _stack.emplace_back(_Enter{_f._s0, _f._s1});
    } else {
      const auto &_f = std::get<_Call2>(_frame);
      _result = (_result && _f._s0);
    }
  }
  return _result;
}

std::shared_ptr<List<unsigned int>> LoopifyMoreTrees::tree_to_list(
    const std::shared_ptr<LoopifyMoreTrees::tree> &t) {
  struct _Enter {
    const std::shared_ptr<LoopifyMoreTrees::tree> t;
  };

  struct _Call1 {
    std::shared_ptr<LoopifyMoreTrees::tree> _s0;
    decltype(List<unsigned int>::cons(std::declval<unsigned int &>(),
                                      List<unsigned int>::nil())) _s1;
  };

  struct _Call2 {
    std::shared_ptr<List<unsigned int>> _s0;
    decltype(List<unsigned int>::cons(std::declval<unsigned int &>(),
                                      List<unsigned int>::nil())) _s1;
  };

  using _Frame = std::variant<_Enter, _Call1, _Call2>;
  std::shared_ptr<List<unsigned int>> _result{};
  std::vector<_Frame> _stack;
  _stack.emplace_back(_Enter{t});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      const auto &_f = std::get<_Enter>(_frame);
      const std::shared_ptr<LoopifyMoreTrees::tree> t = _f.t;
      if (std::holds_alternative<typename LoopifyMoreTrees::tree::Leaf>(
              t->v())) {
        _result = List<unsigned int>::nil();
      } else {
        const auto &[d_a0, d_a1, d_a2] =
            std::get<typename LoopifyMoreTrees::tree::Node>(t->v());
        _stack.emplace_back(_Call1{
            d_a0, List<unsigned int>::cons(d_a1, List<unsigned int>::nil())});
        _stack.emplace_back(_Enter{d_a2});
      }
    } else if (std::holds_alternative<_Call1>(_frame)) {
      const auto &_f = std::get<_Call1>(_frame);
      _stack.emplace_back(_Call2{_result, _f._s1});
      _stack.emplace_back(_Enter{_f._s0});
    } else {
      const auto &_f = std::get<_Call2>(_frame);
      _result = _result->app(_f._s1->app(_f._s0));
    }
  }
  return _result;
}

__attribute__((pure)) bool LoopifyMoreTrees::mirror_equal(
    const std::shared_ptr<LoopifyMoreTrees::tree> &t) {
  return same_shape(t, mirror(t));
}

__attribute__((pure)) unsigned int LoopifyMoreTrees::count_nodes(
    const std::shared_ptr<LoopifyMoreTrees::tree> &t) {
  struct _Enter {
    const std::shared_ptr<LoopifyMoreTrees::tree> t;
  };

  struct _Call1 {
    std::shared_ptr<LoopifyMoreTrees::tree> _s0;
    decltype(1u) _s1;
  };

  struct _Call2 {
    unsigned int _s0;
    decltype(1u) _s1;
  };

  using _Frame = std::variant<_Enter, _Call1, _Call2>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.emplace_back(_Enter{t});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      const auto &_f = std::get<_Enter>(_frame);
      const std::shared_ptr<LoopifyMoreTrees::tree> t = _f.t;
      if (std::holds_alternative<typename LoopifyMoreTrees::tree::Leaf>(
              t->v())) {
        _result = 0u;
      } else {
        const auto &[d_a0, d_a1, d_a2] =
            std::get<typename LoopifyMoreTrees::tree::Node>(t->v());
        _stack.emplace_back(_Call1{d_a0, 1u});
        _stack.emplace_back(_Enter{d_a2});
      }
    } else if (std::holds_alternative<_Call1>(_frame)) {
      const auto &_f = std::get<_Call1>(_frame);
      _stack.emplace_back(_Call2{_result, _f._s1});
      _stack.emplace_back(_Enter{_f._s0});
    } else {
      const auto &_f = std::get<_Call2>(_frame);
      _result = ((_f._s1 + _result) + _f._s0);
    }
  }
  return _result;
}

std::shared_ptr<LoopifyMoreTrees::tree>
LoopifyMoreTrees::tree_max(std::shared_ptr<LoopifyMoreTrees::tree> t1,
                           std::shared_ptr<LoopifyMoreTrees::tree> t2) {
  struct _Enter {
    std::shared_ptr<LoopifyMoreTrees::tree> t2;
    std::shared_ptr<LoopifyMoreTrees::tree> t1;
  };

  struct _Call1 {
    std::shared_ptr<LoopifyMoreTrees::tree> _s0;
    std::shared_ptr<LoopifyMoreTrees::tree> _s1;
    decltype(std::max(std::declval<unsigned int &>(),
                      std::declval<unsigned int &>())) _s2;
  };

  struct _Call2 {
    std::shared_ptr<LoopifyMoreTrees::tree> _s0;
    decltype(std::max(std::declval<unsigned int &>(),
                      std::declval<unsigned int &>())) _s1;
  };

  using _Frame = std::variant<_Enter, _Call1, _Call2>;
  std::shared_ptr<LoopifyMoreTrees::tree> _result{};
  std::vector<_Frame> _stack;
  _stack.emplace_back(_Enter{t2, t1});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      const auto &_f = std::get<_Enter>(_frame);
      std::shared_ptr<LoopifyMoreTrees::tree> t2 = _f.t2;
      std::shared_ptr<LoopifyMoreTrees::tree> t1 = _f.t1;
      if (std::holds_alternative<typename LoopifyMoreTrees::tree::Leaf>(
              t1->v())) {
        _result = std::move(t2);
      } else {
        const auto &[d_a0, d_a1, d_a2] =
            std::get<typename LoopifyMoreTrees::tree::Node>(t1->v());
        if (std::holds_alternative<typename LoopifyMoreTrees::tree::Node>(
                t2->v()) &&
            t2.use_count() == 1) {
          auto &_rf = std::get<1>(t2->v_mut());
          std::shared_ptr<LoopifyMoreTrees::tree> l2 = std::move(_rf.d_a0);
          unsigned int x2 = std::move(_rf.d_a1);
          std::shared_ptr<LoopifyMoreTrees::tree> r2 = std::move(_rf.d_a2);
          _rf.d_a0 = tree_max(d_a0, l2);
          _rf.d_a1 = std::max(std::move(d_a1), x2);
          _rf.d_a2 = tree_max(std::move(d_a2), r2);
          _result = t2;
        } else if (std::holds_alternative<
                       typename LoopifyMoreTrees::tree::Leaf>(t2->v())) {
          _result = std::move(t1);
        } else {
          const auto &[d_a00, d_a10, d_a20] =
              std::get<typename LoopifyMoreTrees::tree::Node>(t2->v());
          _stack.emplace_back(_Call1{d_a00, d_a0, std::max(d_a1, d_a10)});
          _stack.emplace_back(_Enter{d_a20, d_a2});
        }
      }
    } else if (std::holds_alternative<_Call1>(_frame)) {
      const auto &_f = std::get<_Call1>(_frame);
      _stack.emplace_back(_Call2{_result, _f._s2});
      _stack.emplace_back(_Enter{_f._s0, _f._s1});
    } else {
      const auto &_f = std::get<_Call2>(_frame);
      _result = tree::node(_result, _f._s1, _f._s0);
    }
  }
  return _result;
}

__attribute__((pure)) unsigned int LoopifyMoreTrees::sum_of_max_branches(
    const std::shared_ptr<LoopifyMoreTrees::tree> &t) {
  struct _Enter {
    const std::shared_ptr<LoopifyMoreTrees::tree> t;
  };

  struct _Call1 {
    std::shared_ptr<LoopifyMoreTrees::tree> _s0;
    unsigned int _s1;
  };

  struct _Call2 {
    unsigned int _s0;
    unsigned int _s1;
  };

  using _Frame = std::variant<_Enter, _Call1, _Call2>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.emplace_back(_Enter{t});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      const auto &_f = std::get<_Enter>(_frame);
      const std::shared_ptr<LoopifyMoreTrees::tree> t = _f.t;
      if (std::holds_alternative<typename LoopifyMoreTrees::tree::Leaf>(
              t->v())) {
        _result = 0u;
      } else {
        const auto &[d_a0, d_a1, d_a2] =
            std::get<typename LoopifyMoreTrees::tree::Node>(t->v());
        _stack.emplace_back(_Call1{d_a0, d_a1});
        _stack.emplace_back(_Enter{d_a2});
      }
    } else if (std::holds_alternative<_Call1>(_frame)) {
      const auto &_f = std::get<_Call1>(_frame);
      _stack.emplace_back(_Call2{_result, _f._s1});
      _stack.emplace_back(_Enter{_f._s0});
    } else {
      const auto &_f = std::get<_Call2>(_frame);
      _result = (_f._s1 + std::max(_result, _f._s0));
    }
  }
  return _result;
}

std::shared_ptr<LoopifyMoreTrees::tree>
LoopifyMoreTrees::insert_bst(const unsigned int x,
                             const std::shared_ptr<LoopifyMoreTrees::tree> &t) {
  struct _Enter {
    const std::shared_ptr<LoopifyMoreTrees::tree> t;
  };

  struct _Call1 {
    std::shared_ptr<LoopifyMoreTrees::tree> _s0;
    unsigned int _s1;
  };

  struct _Call2 {
    unsigned int _s0;
    std::shared_ptr<LoopifyMoreTrees::tree> _s1;
  };

  using _Frame = std::variant<_Enter, _Call1, _Call2>;
  std::shared_ptr<LoopifyMoreTrees::tree> _result{};
  std::vector<_Frame> _stack;
  _stack.emplace_back(_Enter{t});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      const auto &_f = std::get<_Enter>(_frame);
      const std::shared_ptr<LoopifyMoreTrees::tree> t = _f.t;
      if (std::holds_alternative<typename LoopifyMoreTrees::tree::Leaf>(
              t->v())) {
        _result = tree::node(tree::leaf(), x, tree::leaf());
      } else {
        const auto &[d_a0, d_a1, d_a2] =
            std::get<typename LoopifyMoreTrees::tree::Node>(t->v());
        if (x <= d_a1) {
          _stack.emplace_back(_Call1{d_a2, d_a1});
          _stack.emplace_back(_Enter{d_a0});
        } else {
          _stack.emplace_back(_Call2{d_a1, d_a0});
          _stack.emplace_back(_Enter{d_a2});
        }
      }
    } else if (std::holds_alternative<_Call1>(_frame)) {
      const auto &_f = std::get<_Call1>(_frame);
      _result = tree::node(_result, _f._s1, _f._s0);
    } else {
      const auto &_f = std::get<_Call2>(_frame);
      _result = tree::node(_f._s1, _f._s0, _result);
    }
  }
  return _result;
}

std::shared_ptr<LoopifyMoreTrees::tree>
LoopifyMoreTrees::build_bst(const std::shared_ptr<List<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<List<unsigned int>> l;
  };

  struct _Call1 {
    unsigned int _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::shared_ptr<LoopifyMoreTrees::tree> _result{};
  std::vector<_Frame> _stack;
  _stack.emplace_back(_Enter{l});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      const auto &_f = std::get<_Enter>(_frame);
      const std::shared_ptr<List<unsigned int>> l = _f.l;
      if (std::holds_alternative<typename List<unsigned int>::Nil>(l->v())) {
        _result = tree::leaf();
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<unsigned int>::Cons>(l->v());
        _stack.emplace_back(_Call1{d_a0});
        _stack.emplace_back(_Enter{d_a1});
      }
    } else {
      const auto &_f = std::get<_Call1>(_frame);
      _result = insert_bst(_f._s0, _result);
    }
  }
  return _result;
}

std::shared_ptr<List<unsigned int>>
LoopifyMoreTrees::append_lists(const std::shared_ptr<List<unsigned int>> &l1,
                               std::shared_ptr<List<unsigned int>> l2) {
  std::shared_ptr<List<unsigned int>> _head{};
  std::shared_ptr<List<unsigned int>> _last{};
  std::shared_ptr<List<unsigned int>> _loop_l1 = l1;
  bool _continue = true;
  while (_continue) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(
            _loop_l1->v())) {
      if (_last) {
        std::get<typename List<unsigned int>::Cons>(_last->v_mut()).d_a1 =
            std::move(l2);
      } else {
        _head = std::move(l2);
      }
      _continue = false;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<unsigned int>::Cons>(_loop_l1->v());
      auto _cell = List<unsigned int>::cons(d_a0, nullptr);
      if (_last) {
        std::get<typename List<unsigned int>::Cons>(_last->v_mut()).d_a1 =
            _cell;
      } else {
        _head = _cell;
      }
      _last = _cell;
      _loop_l1 = d_a1;
      continue;
    }
  }
  return _head;
}

std::shared_ptr<List<unsigned int>> LoopifyMoreTrees::flatten(
    const std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> &ll) {
  struct _Enter {
    const std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> ll;
  };

  struct _Call1 {
    std::shared_ptr<List<unsigned int>> _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::shared_ptr<List<unsigned int>> _result{};
  std::vector<_Frame> _stack;
  _stack.emplace_back(_Enter{ll});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      const auto &_f = std::get<_Enter>(_frame);
      const std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> ll =
          _f.ll;
      if (std::holds_alternative<
              typename List<std::shared_ptr<List<unsigned int>>>::Nil>(
              ll->v())) {
        _result = List<unsigned int>::nil();
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<std::shared_ptr<List<unsigned int>>>::Cons>(
                ll->v());
        _stack.emplace_back(_Call1{d_a0});
        _stack.emplace_back(_Enter{d_a1});
      }
    } else {
      const auto &_f = std::get<_Call1>(_frame);
      _result = append_lists(_f._s0, _result);
    }
  }
  return _result;
}

std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>
LoopifyMoreTrees::map_tree_to_list(
    const std::shared_ptr<List<std::shared_ptr<LoopifyMoreTrees::tree>>> &lt) {
  std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> _head{};
  std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> _last{};
  std::shared_ptr<List<std::shared_ptr<LoopifyMoreTrees::tree>>> _loop_lt = lt;
  bool _continue = true;
  while (_continue) {
    if (std::holds_alternative<
            typename List<std::shared_ptr<LoopifyMoreTrees::tree>>::Nil>(
            _loop_lt->v())) {
      if (_last) {
        std::get<typename List<std::shared_ptr<List<unsigned int>>>::Cons>(
            _last->v_mut())
            .d_a1 = List<std::shared_ptr<List<unsigned int>>>::nil();
      } else {
        _head = List<std::shared_ptr<List<unsigned int>>>::nil();
      }
      _continue = false;
    } else {
      const auto &[d_a0, d_a1] = std::get<
          typename List<std::shared_ptr<LoopifyMoreTrees::tree>>::Cons>(
          _loop_lt->v());
      auto _cell = List<std::shared_ptr<List<unsigned int>>>::cons(
          tree_to_list(d_a0), nullptr);
      if (_last) {
        std::get<typename List<std::shared_ptr<List<unsigned int>>>::Cons>(
            _last->v_mut())
            .d_a1 = _cell;
      } else {
        _head = _cell;
      }
      _last = _cell;
      _loop_lt = d_a1;
      continue;
    }
  }
  return _head;
}

std::shared_ptr<List<std::shared_ptr<LoopifyMoreTrees::tree>>>
LoopifyMoreTrees::tree_children(
    const std::shared_ptr<LoopifyMoreTrees::tree> &t) {
  if (std::holds_alternative<typename LoopifyMoreTrees::tree::Leaf>(t->v())) {
    return List<std::shared_ptr<LoopifyMoreTrees::tree>>::nil();
  } else {
    const auto &[d_a0, d_a1, d_a2] =
        std::get<typename LoopifyMoreTrees::tree::Node>(t->v());
    return List<std::shared_ptr<LoopifyMoreTrees::tree>>::cons(
        d_a0, List<std::shared_ptr<LoopifyMoreTrees::tree>>::cons(
                  d_a2, List<std::shared_ptr<LoopifyMoreTrees::tree>>::nil()));
  }
}

std::shared_ptr<List<std::shared_ptr<LoopifyMoreTrees::tree>>>
LoopifyMoreTrees::append_trees(
    const std::shared_ptr<List<std::shared_ptr<LoopifyMoreTrees::tree>>> &l1,
    std::shared_ptr<List<std::shared_ptr<LoopifyMoreTrees::tree>>> l2) {
  std::shared_ptr<List<std::shared_ptr<LoopifyMoreTrees::tree>>> _head{};
  std::shared_ptr<List<std::shared_ptr<LoopifyMoreTrees::tree>>> _last{};
  std::shared_ptr<List<std::shared_ptr<LoopifyMoreTrees::tree>>> _loop_l1 = l1;
  bool _continue = true;
  while (_continue) {
    if (std::holds_alternative<
            typename List<std::shared_ptr<LoopifyMoreTrees::tree>>::Nil>(
            _loop_l1->v())) {
      if (_last) {
        std::get<typename List<std::shared_ptr<LoopifyMoreTrees::tree>>::Cons>(
            _last->v_mut())
            .d_a1 = std::move(l2);
      } else {
        _head = std::move(l2);
      }
      _continue = false;
    } else {
      const auto &[d_a0, d_a1] = std::get<
          typename List<std::shared_ptr<LoopifyMoreTrees::tree>>::Cons>(
          _loop_l1->v());
      auto _cell =
          List<std::shared_ptr<LoopifyMoreTrees::tree>>::cons(d_a0, nullptr);
      if (_last) {
        std::get<typename List<std::shared_ptr<LoopifyMoreTrees::tree>>::Cons>(
            _last->v_mut())
            .d_a1 = _cell;
      } else {
        _head = _cell;
      }
      _last = _cell;
      _loop_l1 = d_a1;
      continue;
    }
  }
  return _head;
}

std::shared_ptr<List<std::shared_ptr<LoopifyMoreTrees::tree>>>
LoopifyMoreTrees::concat_map_children(
    const std::shared_ptr<List<std::shared_ptr<LoopifyMoreTrees::tree>>> &lt) {
  struct _Enter {
    const std::shared_ptr<List<std::shared_ptr<LoopifyMoreTrees::tree>>> lt;
  };

  struct _Call1 {
    decltype(tree_children(
        std::declval<std::shared_ptr<LoopifyMoreTrees::tree> &>())) _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::shared_ptr<List<std::shared_ptr<LoopifyMoreTrees::tree>>> _result{};
  std::vector<_Frame> _stack;
  _stack.emplace_back(_Enter{lt});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      const auto &_f = std::get<_Enter>(_frame);
      const std::shared_ptr<List<std::shared_ptr<LoopifyMoreTrees::tree>>> lt =
          _f.lt;
      if (std::holds_alternative<
              typename List<std::shared_ptr<LoopifyMoreTrees::tree>>::Nil>(
              lt->v())) {
        _result = List<std::shared_ptr<LoopifyMoreTrees::tree>>::nil();
      } else {
        const auto &[d_a0, d_a1] = std::get<
            typename List<std::shared_ptr<LoopifyMoreTrees::tree>>::Cons>(
            lt->v());
        _stack.emplace_back(_Call1{tree_children(d_a0)});
        _stack.emplace_back(_Enter{d_a1});
      }
    } else {
      const auto &_f = std::get<_Call1>(_frame);
      _result = append_trees(_f._s0, _result);
    }
  }
  return _result;
}

std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>
LoopifyMoreTrees::tree_levels_fuel(
    const unsigned int fuel,
    const std::shared_ptr<List<std::shared_ptr<LoopifyMoreTrees::tree>>>
        &level) {
  std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> _head{};
  std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> _last{};
  std::shared_ptr<List<std::shared_ptr<LoopifyMoreTrees::tree>>> _loop_level =
      level;
  unsigned int _loop_fuel = fuel;
  bool _continue = true;
  while (_continue) {
    if (_loop_fuel <= 0) {
      if (_last) {
        std::get<typename List<std::shared_ptr<List<unsigned int>>>::Cons>(
            _last->v_mut())
            .d_a1 = List<std::shared_ptr<List<unsigned int>>>::nil();
      } else {
        _head = List<std::shared_ptr<List<unsigned int>>>::nil();
      }
      _continue = false;
    } else {
      unsigned int fuel_ = _loop_fuel - 1;
      if (std::holds_alternative<
              typename List<std::shared_ptr<LoopifyMoreTrees::tree>>::Nil>(
              _loop_level->v())) {
        if (_last) {
          std::get<typename List<std::shared_ptr<List<unsigned int>>>::Cons>(
              _last->v_mut())
              .d_a1 = List<std::shared_ptr<List<unsigned int>>>::nil();
        } else {
          _head = List<std::shared_ptr<List<unsigned int>>>::nil();
        }
        _continue = false;
      } else {
        std::shared_ptr<List<unsigned int>> values =
            flatten(map_tree_to_list(_loop_level));
        std::shared_ptr<List<std::shared_ptr<LoopifyMoreTrees::tree>>> next =
            concat_map_children(_loop_level);
        auto _cell =
            List<std::shared_ptr<List<unsigned int>>>::cons(values, nullptr);
        if (_last) {
          std::get<typename List<std::shared_ptr<List<unsigned int>>>::Cons>(
              _last->v_mut())
              .d_a1 = _cell;
        } else {
          _head = _cell;
        }
        _last = _cell;
        std::shared_ptr<List<std::shared_ptr<LoopifyMoreTrees::tree>>>
            _next_level = next;
        unsigned int _next_fuel = fuel_;
        _loop_level = std::move(_next_level);
        _loop_fuel = std::move(_next_fuel);
        continue;
      }
    }
  }
  return _head;
}

std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>
LoopifyMoreTrees::tree_levels(std::shared_ptr<LoopifyMoreTrees::tree> t) {
  return tree_levels_fuel(
      100u, List<std::shared_ptr<LoopifyMoreTrees::tree>>::cons(
                t, List<std::shared_ptr<LoopifyMoreTrees::tree>>::nil()));
}
