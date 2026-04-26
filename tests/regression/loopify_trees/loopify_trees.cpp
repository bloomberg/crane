#include <loopify_trees.h>

#include <functional>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

/// Consolidated UNIQUE tree algorithms - domain-specific tree operations.
__attribute__((pure)) unsigned int
LoopifyTrees::tree_sum(const LoopifyTrees::tree<unsigned int> &t) {
  struct _Enter {
    const LoopifyTrees::tree<unsigned int> t;
  };

  struct _Call1 {
    LoopifyTrees::tree<unsigned int> _s0;
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
  _stack.emplace_back(_Enter{t});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const LoopifyTrees::tree<unsigned int> t = _f.t;
      if (std::holds_alternative<
              typename LoopifyTrees::tree<unsigned int>::Leaf>(t.v())) {
        _result = 0u;
      } else {
        const auto &[d_a0, d_a1, d_a2] =
            std::get<typename LoopifyTrees::tree<unsigned int>::Node>(t.v());
        _stack.emplace_back(_Call1{*(d_a0), d_a1});
        _stack.emplace_back(_Enter{*(d_a2)});
      }
    } else if (std::holds_alternative<_Call1>(_frame)) {
      auto _f = std::move(std::get<_Call1>(_frame));
      _stack.emplace_back(_Call2{_result, _f._s1});
      _stack.emplace_back(_Enter{_f._s0});
    } else {
      auto _f = std::move(std::get<_Call2>(_frame));
      _result = (_f._s1 + (_result + _f._s0));
    }
  }
  return _result;
}

/// leaf_sum sums only leaf values.
__attribute__((pure)) unsigned int
LoopifyTrees::leaf_sum(const LoopifyTrees::tree<unsigned int> &t) {
  struct _Enter {
    const LoopifyTrees::tree<unsigned int> t;
  };

  struct _Call1 {
    LoopifyTrees::tree<unsigned int> _s0;
  };

  struct _Call2 {
    unsigned int _s0;
  };

  struct _Call3 {
    LoopifyTrees::tree<unsigned int> _s0;
  };

  struct _Call4 {
    unsigned int _s0;
  };

  using _Frame = std::variant<_Enter, _Call1, _Call2, _Call3, _Call4>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{t});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const LoopifyTrees::tree<unsigned int> t = _f.t;
      if (std::holds_alternative<
              typename LoopifyTrees::tree<unsigned int>::Leaf>(t.v())) {
        _result = 0u;
      } else {
        const auto &[d_a0, d_a1, d_a2] =
            std::get<typename LoopifyTrees::tree<unsigned int>::Node>(t.v());
        auto &&_sv = *(d_a0);
        if (std::holds_alternative<
                typename LoopifyTrees::tree<unsigned int>::Leaf>(_sv.v())) {
          auto &&_sv = *(d_a2);
          if (std::holds_alternative<
                  typename LoopifyTrees::tree<unsigned int>::Leaf>(_sv.v())) {
            _result = d_a1;
          } else {
            _stack.emplace_back(_Call1{*(d_a0)});
            _stack.emplace_back(_Enter{*(d_a2)});
          }
        } else {
          _stack.emplace_back(_Call3{*(d_a0)});
          _stack.emplace_back(_Enter{*(d_a2)});
        }
      }
    } else if (std::holds_alternative<_Call1>(_frame)) {
      auto _f = std::move(std::get<_Call1>(_frame));
      _stack.emplace_back(_Call2{_result});
      _stack.emplace_back(_Enter{_f._s0});
    } else if (std::holds_alternative<_Call2>(_frame)) {
      auto _f = std::move(std::get<_Call2>(_frame));
      _result = (_result + _f._s0);
    } else if (std::holds_alternative<_Call3>(_frame)) {
      auto _f = std::move(std::get<_Call3>(_frame));
      _stack.emplace_back(_Call4{_result});
      _stack.emplace_back(_Enter{_f._s0});
    } else {
      auto _f = std::move(std::get<_Call4>(_frame));
      _result = (_result + _f._s0);
    }
  }
  return _result;
}

/// insert_bst BST insertion.
__attribute__((pure)) LoopifyTrees::tree<unsigned int>
LoopifyTrees::insert_bst(unsigned int x,
                         const LoopifyTrees::tree<unsigned int> &t) {
  struct _Enter {
    const LoopifyTrees::tree<unsigned int> t;
  };

  struct _Call1 {
    LoopifyTrees::tree<unsigned int> _s0;
    unsigned int _s1;
  };

  struct _Call2 {
    unsigned int _s0;
    LoopifyTrees::tree<unsigned int> _s1;
  };

  using _Frame = std::variant<_Enter, _Call1, _Call2>;
  LoopifyTrees::tree<unsigned int> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{t});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const LoopifyTrees::tree<unsigned int> t = _f.t;
      if (std::holds_alternative<
              typename LoopifyTrees::tree<unsigned int>::Leaf>(t.v())) {
        _result = tree<unsigned int>::node(tree<unsigned int>::leaf(), x,
                                           tree<unsigned int>::leaf());
      } else {
        const auto &[d_a0, d_a1, d_a2] =
            std::get<typename LoopifyTrees::tree<unsigned int>::Node>(t.v());
        if (x <= d_a1) {
          _stack.emplace_back(_Call1{*(d_a2), d_a1});
          _stack.emplace_back(_Enter{*(d_a0)});
        } else {
          _stack.emplace_back(_Call2{d_a1, *(d_a0)});
          _stack.emplace_back(_Enter{*(d_a2)});
        }
      }
    } else if (std::holds_alternative<_Call1>(_frame)) {
      auto _f = std::move(std::get<_Call1>(_frame));
      _result = tree<unsigned int>::node(_result, _f._s1, _f._s0);
    } else {
      auto _f = std::move(std::get<_Call2>(_frame));
      _result = tree<unsigned int>::node(_f._s1, _f._s0, _result);
    }
  }
  return _result;
}

/// count_paths t n counts root-to-leaf paths that sum to n.
__attribute__((pure)) unsigned int
LoopifyTrees::count_paths(const LoopifyTrees::tree<unsigned int> &t,
                          const unsigned int &n) {
  struct _Enter {
    const unsigned int n;
    const LoopifyTrees::tree<unsigned int> t;
  };

  struct _Call1 {
    decltype(0u) _s0;
    LoopifyTrees::tree<unsigned int> _s1;
  };

  struct _Call2 {
    unsigned int _s0;
  };

  struct _Call3 {
    unsigned int _s0;
    LoopifyTrees::tree<unsigned int> _s1;
  };

  struct _Call4 {
    unsigned int _s0;
  };

  using _Frame = std::variant<_Enter, _Call1, _Call2, _Call3, _Call4>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{n, t});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const unsigned int n = _f.n;
      const LoopifyTrees::tree<unsigned int> t = _f.t;
      if (std::holds_alternative<
              typename LoopifyTrees::tree<unsigned int>::Leaf>(t.v())) {
        if (n == 0u) {
          _result = 1u;
        } else {
          _result = 0u;
        }
      } else {
        const auto &[d_a0, d_a1, d_a2] =
            std::get<typename LoopifyTrees::tree<unsigned int>::Node>(t.v());
        if (n <= d_a1) {
          if (n == d_a1) {
            _stack.emplace_back(_Call1{0u, *(d_a0)});
            _stack.emplace_back(_Enter{0u, *(d_a2)});
          } else {
            _result = 0u;
          }
        } else {
          unsigned int remaining = (((n - d_a1) > n ? 0 : (n - d_a1)));
          _stack.emplace_back(_Call3{remaining, *(d_a0)});
          _stack.emplace_back(_Enter{remaining, *(d_a2)});
        }
      }
    } else if (std::holds_alternative<_Call1>(_frame)) {
      auto _f = std::move(std::get<_Call1>(_frame));
      _stack.emplace_back(_Call2{_result});
      _stack.emplace_back(_Enter{_f._s0, _f._s1});
    } else if (std::holds_alternative<_Call2>(_frame)) {
      auto _f = std::move(std::get<_Call2>(_frame));
      _result = (_result + _f._s0);
    } else if (std::holds_alternative<_Call3>(_frame)) {
      auto _f = std::move(std::get<_Call3>(_frame));
      _stack.emplace_back(_Call4{_result});
      _stack.emplace_back(_Enter{_f._s0, _f._s1});
    } else {
      auto _f = std::move(std::get<_Call4>(_frame));
      _result = (_result + _f._s0);
    }
  }
  return _result;
}

/// sum_of_max_branches sums maximum values along each path.
__attribute__((pure)) unsigned int
LoopifyTrees::sum_of_max_branches(const LoopifyTrees::tree<unsigned int> &t) {
  if (std::holds_alternative<typename LoopifyTrees::tree<unsigned int>::Leaf>(
          t.v())) {
    return 0u;
  } else {
    const auto &[d_a0, d_a1, d_a2] =
        std::get<typename LoopifyTrees::tree<unsigned int>::Node>(t.v());
    unsigned int lsum = sum_of_max_branches(*(d_a0));
    unsigned int rsum = sum_of_max_branches(*(d_a2));
    return (d_a1 + [&]() -> unsigned int {
      if (lsum <= rsum) {
        return rsum;
      } else {
        return lsum;
      }
    }());
  }
}

/// Helper: sum all values in a list of rose trees (processes both tree and
/// list levels in one recursive function to enable full loopification).
__attribute__((pure)) unsigned int
LoopifyTrees::sum_rose_list_fuel(const unsigned int &fuel,
                                 const List<LoopifyTrees::rose> &cs) {
  struct _Enter {
    const List<LoopifyTrees::rose> cs;
    const unsigned int fuel;
  };

  struct _Call1 {
    decltype(clone_as_value<List<LoopifyTrees::rose>>(
        std::declval<List<std::unique_ptr<LoopifyTrees::rose>> &>())) _s0;
    unsigned int _s1;
    unsigned int _s2;
  };

  struct _Call2 {
    unsigned int _s0;
    unsigned int _s1;
  };

  using _Frame = std::variant<_Enter, _Call1, _Call2>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{cs, fuel});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<LoopifyTrees::rose> cs = _f.cs;
      const unsigned int fuel = _f.fuel;
      if (fuel <= 0) {
        _result = 0u;
      } else {
        unsigned int f = fuel - 1;
        if (std::holds_alternative<typename List<LoopifyTrees::rose>::Nil>(
                cs.v())) {
          _result = 0u;
        } else {
          const auto &[d_a0, d_a1] =
              std::get<typename List<LoopifyTrees::rose>::Cons>(cs.v());
          const auto &[d_a00, d_a10] =
              std::get<typename LoopifyTrees::rose::RNode>(d_a0.v());
          _stack.emplace_back(_Call1{
              clone_as_value<List<LoopifyTrees::rose>>(d_a10), f, d_a00});
          _stack.emplace_back(_Enter{*(d_a1), f});
        }
      }
    } else if (std::holds_alternative<_Call1>(_frame)) {
      auto _f = std::move(std::get<_Call1>(_frame));
      _stack.emplace_back(_Call2{_result, _f._s2});
      _stack.emplace_back(_Enter{_f._s0, _f._s1});
    } else {
      auto _f = std::move(std::get<_Call2>(_frame));
      _result = (_f._s1 + (_result + _f._s0));
    }
  }
  return _result;
}

/// Helper: flatten a list of rose trees to a flat list of nats.
__attribute__((pure)) List<unsigned int>
LoopifyTrees::flatten_rose_list_fuel(const unsigned int &fuel,
                                     const List<LoopifyTrees::rose> &cs) {
  struct _Enter {
    const List<LoopifyTrees::rose> cs;
    const unsigned int fuel;
  };

  struct _Call1 {
    decltype(clone_as_value<List<LoopifyTrees::rose>>(
        std::declval<List<std::unique_ptr<LoopifyTrees::rose>> &>())) _s0;
    unsigned int _s1;
    unsigned int _s2;
  };

  struct _Call2 {
    List<unsigned int> _s0;
    unsigned int _s1;
  };

  using _Frame = std::variant<_Enter, _Call1, _Call2>;
  List<unsigned int> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{cs, fuel});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<LoopifyTrees::rose> cs = _f.cs;
      const unsigned int fuel = _f.fuel;
      if (fuel <= 0) {
        _result = List<unsigned int>::nil();
      } else {
        unsigned int f = fuel - 1;
        if (std::holds_alternative<typename List<LoopifyTrees::rose>::Nil>(
                cs.v())) {
          _result = List<unsigned int>::nil();
        } else {
          const auto &[d_a0, d_a1] =
              std::get<typename List<LoopifyTrees::rose>::Cons>(cs.v());
          const auto &[d_a00, d_a10] =
              std::get<typename LoopifyTrees::rose::RNode>(d_a0.v());
          _stack.emplace_back(_Call1{
              clone_as_value<List<LoopifyTrees::rose>>(d_a10), f, d_a00});
          _stack.emplace_back(_Enter{*(d_a1), f});
        }
      }
    } else if (std::holds_alternative<_Call1>(_frame)) {
      auto _f = std::move(std::get<_Call1>(_frame));
      _stack.emplace_back(_Call2{_result, _f._s2});
      _stack.emplace_back(_Enter{_f._s0, _f._s1});
    } else {
      auto _f = std::move(std::get<_Call2>(_frame));
      _result = List<unsigned int>::cons(_f._s1, _result.app(_f._s0));
    }
  }
  return _result;
}

/// Helper: compute maximum depth among a list of rose trees.
__attribute__((pure)) unsigned int
LoopifyTrees::depth_rose_list_fuel(const unsigned int &fuel,
                                   const List<LoopifyTrees::rose> &cs) {
  if (fuel <= 0) {
    return 0u;
  } else {
    unsigned int f = fuel - 1;
    if (std::holds_alternative<typename List<LoopifyTrees::rose>::Nil>(
            cs.v())) {
      return 0u;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<LoopifyTrees::rose>::Cons>(cs.v());
      const auto &[d_a00, d_a10] =
          std::get<typename LoopifyTrees::rose::RNode>(d_a0.v());
      unsigned int d =
          (depth_rose_list_fuel(
               f, clone_as_value<List<LoopifyTrees::rose>>(d_a10)) +
           1);
      unsigned int rest_max = depth_rose_list_fuel(f, *(d_a1));
      if (d <= rest_max) {
        return rest_max;
      } else {
        return d;
      }
    }
  }
}

/// tree_max t1 t2 element-wise maximum of two trees.
__attribute__((pure)) LoopifyTrees::tree<unsigned int>
LoopifyTrees::tree_max(LoopifyTrees::tree<unsigned int> t1,
                       LoopifyTrees::tree<unsigned int> t2) {
  struct _Enter {
    LoopifyTrees::tree<unsigned int> t2;
    LoopifyTrees::tree<unsigned int> t1;
  };

  struct _Call1 {
    LoopifyTrees::tree<unsigned int> _s0;
    LoopifyTrees::tree<unsigned int> _s1;
    unsigned int _s2;
  };

  struct _Call2 {
    LoopifyTrees::tree<unsigned int> _s0;
    unsigned int _s1;
  };

  using _Frame = std::variant<_Enter, _Call1, _Call2>;
  LoopifyTrees::tree<unsigned int> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{t2, t1});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      LoopifyTrees::tree<unsigned int> t2 = _f.t2;
      LoopifyTrees::tree<unsigned int> t1 = _f.t1;
      if (std::holds_alternative<
              typename LoopifyTrees::tree<unsigned int>::Leaf>(t1.v())) {
        if (std::holds_alternative<
                typename LoopifyTrees::tree<unsigned int>::Leaf>(t2.v())) {
          _result = tree<unsigned int>::leaf();
        } else {
          _result = t2;
        }
      } else {
        const auto &[d_a0, d_a1, d_a2] =
            std::get<typename LoopifyTrees::tree<unsigned int>::Node>(t1.v());
        if (std::holds_alternative<
                typename LoopifyTrees::tree<unsigned int>::Leaf>(t2.v())) {
          _result = t1;
        } else {
          const auto &[d_a00, d_a10, d_a20] =
              std::get<typename LoopifyTrees::tree<unsigned int>::Node>(t2.v());
          unsigned int max_val;
          if (d_a1 <= d_a10) {
            max_val = d_a10;
          } else {
            max_val = d_a1;
          }
          _stack.emplace_back(_Call1{*(d_a00), *(d_a0), max_val});
          _stack.emplace_back(_Enter{*(d_a20), *(d_a2)});
        }
      }
    } else if (std::holds_alternative<_Call1>(_frame)) {
      auto _f = std::move(std::get<_Call1>(_frame));
      _stack.emplace_back(_Call2{_result, _f._s2});
      _stack.emplace_back(_Enter{_f._s0, _f._s1});
    } else {
      auto _f = std::move(std::get<_Call2>(_frame));
      _result = tree<unsigned int>::node(_result, _f._s1, _f._s0);
    }
  }
  return _result;
}

/// Helper: extract values from trees.
__attribute__((pure)) List<unsigned int> LoopifyTrees::extract_tree_values(
    const List<LoopifyTrees::tree<unsigned int>> &ts) {
  std::unique_ptr<List<unsigned int>> _head{};
  std::unique_ptr<List<unsigned int>> *_write = &_head;
  List<LoopifyTrees::tree<unsigned int>> _loop_ts = ts;
  while (true) {
    if (std::holds_alternative<
            typename List<LoopifyTrees::tree<unsigned int>>::Nil>(
            _loop_ts.v())) {
      *(_write) =
          std::make_unique<List<unsigned int>>(List<unsigned int>::nil());
      break;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<LoopifyTrees::tree<unsigned int>>::Cons>(
              _loop_ts.v());
      if (std::holds_alternative<
              typename LoopifyTrees::tree<unsigned int>::Leaf>(d_a0.v())) {
        _loop_ts = *(d_a1);
        continue;
      } else {
        const auto &[d_a00, d_a10, d_a20] =
            std::get<typename LoopifyTrees::tree<unsigned int>::Node>(d_a0.v());
        auto _cell = std::make_unique<List<unsigned int>>(
            typename List<unsigned int>::Cons(d_a10, nullptr));
        *(_write) = std::move(_cell);
        _write =
            &std::get<typename List<unsigned int>::Cons>((*_write)->v_mut())
                 .d_a1;
        _loop_ts = *(d_a1);
        continue;
      }
    }
  }
  return std::move(*(_head));
}

/// Helper: extract children from trees.
__attribute__((pure)) List<LoopifyTrees::tree<unsigned int>>
LoopifyTrees::extract_tree_children(
    const List<LoopifyTrees::tree<unsigned int>> &ts) {
  std::unique_ptr<List<LoopifyTrees::tree<unsigned int>>> _head{};
  std::unique_ptr<List<LoopifyTrees::tree<unsigned int>>> *_write = &_head;
  List<LoopifyTrees::tree<unsigned int>> _loop_ts = ts;
  while (true) {
    if (std::holds_alternative<
            typename List<LoopifyTrees::tree<unsigned int>>::Nil>(
            _loop_ts.v())) {
      *(_write) = std::make_unique<List<LoopifyTrees::tree<unsigned int>>>(
          List<LoopifyTrees::tree<unsigned int>>::nil());
      break;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<LoopifyTrees::tree<unsigned int>>::Cons>(
              _loop_ts.v());
      if (std::holds_alternative<
              typename LoopifyTrees::tree<unsigned int>::Leaf>(d_a0.v())) {
        _loop_ts = *(d_a1);
        continue;
      } else {
        const auto &[d_a00, d_a10, d_a20] =
            std::get<typename LoopifyTrees::tree<unsigned int>::Node>(d_a0.v());
        auto _cell = std::make_unique<List<LoopifyTrees::tree<unsigned int>>>(
            typename List<LoopifyTrees::tree<unsigned int>>::Cons(*(d_a00),
                                                                  nullptr));
        auto _cell1 = std::make_unique<List<LoopifyTrees::tree<unsigned int>>>(
            typename List<LoopifyTrees::tree<unsigned int>>::Cons(*(d_a20),
                                                                  nullptr));
        std::get<typename List<LoopifyTrees::tree<unsigned int>>::Cons>(
            _cell->v_mut())
            .d_a1 = std::move(_cell1);
        *(_write) = std::move(_cell);
        _write =
            &std::get<typename List<LoopifyTrees::tree<unsigned int>>::Cons>(
                 std::get<
                     typename List<LoopifyTrees::tree<unsigned int>>::Cons>(
                     (*_write)->v_mut())
                     .d_a1->v_mut())
                 .d_a1;
        _loop_ts = *(d_a1);
        continue;
      }
    }
  }
  return std::move(*(_head));
}

/// tree_levels t returns list of lists, one per level (breadth-first).
__attribute__((pure)) List<List<unsigned int>> LoopifyTrees::tree_levels_fuel(
    const unsigned int &fuel,
    const List<LoopifyTrees::tree<unsigned int>> &trees) {
  std::unique_ptr<List<List<unsigned int>>> _head{};
  std::unique_ptr<List<List<unsigned int>>> *_write = &_head;
  List<LoopifyTrees::tree<unsigned int>> _loop_trees = trees;
  unsigned int _loop_fuel = fuel;
  while (true) {
    if (_loop_fuel <= 0) {
      *(_write) = std::make_unique<List<List<unsigned int>>>(
          List<List<unsigned int>>::nil());
      break;
    } else {
      unsigned int f = _loop_fuel - 1;
      List<unsigned int> values = extract_tree_values(_loop_trees);
      if (std::holds_alternative<typename List<unsigned int>::Nil>(
              values.v())) {
        *(_write) = std::make_unique<List<List<unsigned int>>>(
            List<List<unsigned int>>::nil());
        break;
      } else {
        List<LoopifyTrees::tree<unsigned int>> children =
            extract_tree_children(_loop_trees);
        auto _cell = std::make_unique<List<List<unsigned int>>>(
            typename List<List<unsigned int>>::Cons(values, nullptr));
        *(_write) = std::move(_cell);
        _write = &std::get<typename List<List<unsigned int>>::Cons>(
                      (*_write)->v_mut())
                      .d_a1;
        List<LoopifyTrees::tree<unsigned int>> _next_trees = children;
        unsigned int _next_fuel = f;
        _loop_trees = std::move(_next_trees);
        _loop_fuel = std::move(_next_fuel);
        continue;
      }
    }
  }
  return std::move(*(_head));
}

__attribute__((pure)) List<List<unsigned int>>
LoopifyTrees::tree_levels(LoopifyTrees::tree<unsigned int> t) {
  return tree_levels_fuel(
      100u, List<LoopifyTrees::tree<unsigned int>>::cons(
                t, List<LoopifyTrees::tree<unsigned int>>::nil()));
}

/// count_nodes t returns tuple (node_count, sum_of_values).
__attribute__((pure)) std::pair<unsigned int, unsigned int>
LoopifyTrees::count_nodes(const LoopifyTrees::tree<unsigned int> &t) {
  if (std::holds_alternative<typename LoopifyTrees::tree<unsigned int>::Leaf>(
          t.v())) {
    return std::make_pair(0u, 0u);
  } else {
    const auto &[d_a0, d_a1, d_a2] =
        std::get<typename LoopifyTrees::tree<unsigned int>::Node>(t.v());
    auto _cs = count_nodes(*(d_a0));
    const unsigned int &lc = _cs.first;
    const unsigned int &ls = _cs.second;
    auto _cs1 = count_nodes(*(d_a2));
    const unsigned int &rc = _cs1.first;
    const unsigned int &rs = _cs1.second;
    return std::make_pair(((lc + rc) + 1), (d_a1 + (ls + rs)));
  }
}

/// Helper: append two lists of lists.
__attribute__((pure)) List<List<unsigned int>>
LoopifyTrees::append_list_lists(const List<List<unsigned int>> &l1,
                                List<List<unsigned int>> l2) {
  std::unique_ptr<List<List<unsigned int>>> _head{};
  std::unique_ptr<List<List<unsigned int>>> *_write = &_head;
  List<List<unsigned int>> _loop_l1 = l1;
  while (true) {
    if (std::holds_alternative<typename List<List<unsigned int>>::Nil>(
            _loop_l1.v())) {
      *(_write) = std::make_unique<List<List<unsigned int>>>(l2);
      break;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<List<unsigned int>>::Cons>(_loop_l1.v());
      auto _cell = std::make_unique<List<List<unsigned int>>>(
          typename List<List<unsigned int>>::Cons(
              clone_as_value<List<unsigned int>>(d_a0), nullptr));
      *(_write) = std::move(_cell);
      _write =
          &std::get<typename List<List<unsigned int>>::Cons>((*_write)->v_mut())
               .d_a1;
      _loop_l1 = *(d_a1);
      continue;
    }
  }
  return std::move(*(_head));
}

/// Helper: prepend value to all lists in a list of lists.
__attribute__((pure)) List<List<unsigned int>>
LoopifyTrees::map_cons_to_all(unsigned int x,
                              const List<List<unsigned int>> &lsts) {
  std::unique_ptr<List<List<unsigned int>>> _head{};
  std::unique_ptr<List<List<unsigned int>>> *_write = &_head;
  List<List<unsigned int>> _loop_lsts = lsts;
  while (true) {
    if (std::holds_alternative<typename List<List<unsigned int>>::Nil>(
            _loop_lsts.v())) {
      *(_write) = std::make_unique<List<List<unsigned int>>>(
          List<List<unsigned int>>::nil());
      break;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<List<unsigned int>>::Cons>(_loop_lsts.v());
      auto _cell = std::make_unique<List<List<unsigned int>>>(
          typename List<List<unsigned int>>::Cons(
              List<unsigned int>::cons(
                  x, clone_as_value<List<unsigned int>>(d_a0)),
              nullptr));
      *(_write) = std::move(_cell);
      _write =
          &std::get<typename List<List<unsigned int>>::Cons>((*_write)->v_mut())
               .d_a1;
      _loop_lsts = *(d_a1);
      continue;
    }
  }
  return std::move(*(_head));
}

/// paths t returns all root-to-leaf paths in tree.
__attribute__((pure)) List<List<unsigned int>>
LoopifyTrees::paths(const LoopifyTrees::tree<unsigned int> &t) {
  struct _Enter {
    const LoopifyTrees::tree<unsigned int> t;
  };

  struct _Call1 {
    LoopifyTrees::tree<unsigned int> _s0;
    unsigned int _s1;
    unsigned int _s2;
  };

  struct _Call2 {
    List<List<unsigned int>> _s0;
    unsigned int _s1;
    unsigned int _s2;
  };

  using _Frame = std::variant<_Enter, _Call1, _Call2>;
  List<List<unsigned int>> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{t});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const LoopifyTrees::tree<unsigned int> t = _f.t;
      if (std::holds_alternative<
              typename LoopifyTrees::tree<unsigned int>::Leaf>(t.v())) {
        _result = List<List<unsigned int>>::cons(
            List<unsigned int>::nil(), List<List<unsigned int>>::nil());
      } else {
        const auto &[d_a0, d_a1, d_a2] =
            std::get<typename LoopifyTrees::tree<unsigned int>::Node>(t.v());
        _stack.emplace_back(_Call1{*(d_a0), d_a1, d_a1});
        _stack.emplace_back(_Enter{*(d_a2)});
      }
    } else if (std::holds_alternative<_Call1>(_frame)) {
      auto _f = std::move(std::get<_Call1>(_frame));
      _stack.emplace_back(_Call2{_result, _f._s1, _f._s2});
      _stack.emplace_back(_Enter{_f._s0});
    } else {
      auto _f = std::move(std::get<_Call2>(_frame));
      _result = append_list_lists(map_cons_to_all(_f._s2, _result),
                                  map_cons_to_all(_f._s1, _f._s0));
    }
  }
  return _result;
}

/// collect_sorted t collects and sorts all tree values.
__attribute__((pure)) List<unsigned int>
LoopifyTrees::collect_unsorted(const LoopifyTrees::tree<unsigned int> &t) {
  struct _Enter {
    const LoopifyTrees::tree<unsigned int> t;
  };

  struct _Call1 {
    LoopifyTrees::tree<unsigned int> _s0;
    unsigned int _s1;
  };

  struct _Call2 {
    List<unsigned int> _s0;
    unsigned int _s1;
  };

  using _Frame = std::variant<_Enter, _Call1, _Call2>;
  List<unsigned int> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{t});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const LoopifyTrees::tree<unsigned int> t = _f.t;
      if (std::holds_alternative<
              typename LoopifyTrees::tree<unsigned int>::Leaf>(t.v())) {
        _result = List<unsigned int>::nil();
      } else {
        const auto &[d_a0, d_a1, d_a2] =
            std::get<typename LoopifyTrees::tree<unsigned int>::Node>(t.v());
        _stack.emplace_back(_Call1{*(d_a0), d_a1});
        _stack.emplace_back(_Enter{*(d_a2)});
      }
    } else if (std::holds_alternative<_Call1>(_frame)) {
      auto _f = std::move(std::get<_Call1>(_frame));
      _stack.emplace_back(_Call2{_result, _f._s1});
      _stack.emplace_back(_Enter{_f._s0});
    } else {
      auto _f = std::move(std::get<_Call2>(_frame));
      _result = _result.app(List<unsigned int>::cons(_f._s1, _f._s0));
    }
  }
  return _result;
}

/// Simple insertion sort for collect_sorted.
__attribute__((pure)) List<unsigned int>
LoopifyTrees::insert_sorted(unsigned int x, const List<unsigned int> &l) {
  std::unique_ptr<List<unsigned int>> _head{};
  std::unique_ptr<List<unsigned int>> *_write = &_head;
  List<unsigned int> _loop_l = l;
  while (true) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(_loop_l.v())) {
      *(_write) = std::make_unique<List<unsigned int>>(
          List<unsigned int>::cons(x, List<unsigned int>::nil()));
      break;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<unsigned int>::Cons>(_loop_l.v());
      if (x <= d_a0) {
        *(_write) =
            std::make_unique<List<unsigned int>>(List<unsigned int>::cons(
                x, List<unsigned int>::cons(d_a0, *(d_a1))));
        break;
      } else {
        auto _cell = std::make_unique<List<unsigned int>>(
            typename List<unsigned int>::Cons(d_a0, nullptr));
        *(_write) = std::move(_cell);
        _write =
            &std::get<typename List<unsigned int>::Cons>((*_write)->v_mut())
                 .d_a1;
        _loop_l = *(d_a1);
        continue;
      }
    }
  }
  return std::move(*(_head));
}

__attribute__((pure)) List<unsigned int>
LoopifyTrees::sort_list(const List<unsigned int> &l) {
  struct _Enter {
    const List<unsigned int> l;
  };

  struct _Call1 {
    unsigned int _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  List<unsigned int> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{l});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<unsigned int> l = _f.l;
      if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
        _result = List<unsigned int>::nil();
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<unsigned int>::Cons>(l.v());
        _stack.emplace_back(_Call1{d_a0});
        _stack.emplace_back(_Enter{*(d_a1)});
      }
    } else {
      auto _f = std::move(std::get<_Call1>(_frame));
      _result = insert_sorted(_f._s0, _result);
    }
  }
  return _result;
}

__attribute__((pure)) List<unsigned int>
LoopifyTrees::collect_sorted(const LoopifyTrees::tree<unsigned int> &t) {
  return sort_list(collect_unsorted(t));
}

/// Helper: max of 4 values using nested max.
__attribute__((pure)) unsigned int LoopifyTrees::max4_impl(unsigned int a,
                                                           unsigned int b,
                                                           unsigned int c,
                                                           unsigned int d) {
  if ([&]() -> unsigned int {
        if (a <= b) {
          return b;
        } else {
          return a;
        }
      }() <= [&]() -> unsigned int {
        if (c <= d) {
          return d;
        } else {
          return c;
        }
      }()) {
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
__attribute__((pure)) unsigned int
LoopifyTrees::min3(unsigned int a, unsigned int b, unsigned int c) {
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
__attribute__((pure)) unsigned int
LoopifyTrees::max3(unsigned int a, unsigned int b, unsigned int c) {
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
__attribute__((pure)) std::pair<unsigned int, unsigned int>
LoopifyTrees::tree_min_max(const LoopifyTrees::tree<unsigned int> &t) {
  if (std::holds_alternative<typename LoopifyTrees::tree<unsigned int>::Leaf>(
          t.v())) {
    return std::make_pair(0u, 0u);
  } else {
    const auto &[d_a0, d_a1, d_a2] =
        std::get<typename LoopifyTrees::tree<unsigned int>::Node>(t.v());
    auto _cs = tree_min_max(*(d_a0));
    const unsigned int &lmin = _cs.first;
    const unsigned int &lmax = _cs.second;
    auto _cs1 = tree_min_max(*(d_a2));
    const unsigned int &rmin = _cs1.first;
    const unsigned int &rmax = _cs1.second;
    return std::make_pair(min3(
                              [&]() -> unsigned int {
                                if (lmin == 0u) {
                                  return d_a1;
                                } else {
                                  return lmin;
                                }
                              }(),
                              [&]() -> unsigned int {
                                if (rmin == 0u) {
                                  return d_a1;
                                } else {
                                  return rmin;
                                }
                              }(),
                              d_a1),
                          max3(lmax, rmax, d_a1));
  }
}

/// all_paths_sum t sums all root-to-leaf path sums.
__attribute__((pure)) unsigned int
LoopifyTrees::all_paths_sum(const LoopifyTrees::tree<unsigned int> &t) {
  std::function<unsigned int(unsigned int, LoopifyTrees::tree<unsigned int>)>
      sum_with_acc;
  sum_with_acc = [&](unsigned int acc,
                     LoopifyTrees::tree<unsigned int> tree0) -> unsigned int {
    struct _Enter {
      LoopifyTrees::tree<unsigned int> tree0;
      unsigned int acc;
    };
    struct _Call1 {
      LoopifyTrees::tree<unsigned int> _s0;
      unsigned int _s1;
    };
    struct _Call2 {
      unsigned int _s0;
    };
    using _Frame = std::variant<_Enter, _Call1, _Call2>;
    unsigned int _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(16);
    _stack.emplace_back(_Enter{tree0, acc});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        LoopifyTrees::tree<unsigned int> tree0 = _f.tree0;
        unsigned int acc = _f.acc;
        if (std::holds_alternative<
                typename LoopifyTrees::tree<unsigned int>::Leaf>(tree0.v())) {
          _result = acc;
        } else {
          const auto &[d_a0, d_a1, d_a2] =
              std::get<typename LoopifyTrees::tree<unsigned int>::Node>(
                  tree0.v());
          unsigned int new_acc = (acc + d_a1);
          _stack.emplace_back(_Call1{*(d_a0), new_acc});
          _stack.emplace_back(_Enter{*(d_a2), new_acc});
        }
      } else if (std::holds_alternative<_Call1>(_frame)) {
        auto _f = std::move(std::get<_Call1>(_frame));
        _stack.emplace_back(_Call2{_result});
        _stack.emplace_back(_Enter{_f._s0, _f._s1});
      } else {
        auto _f = std::move(std::get<_Call2>(_frame));
        _result = (_result + _f._s0);
      }
    }
    return _result;
  };
  return sum_with_acc(0u, t);
}

/// tree_contains x t checks if value exists in tree.
__attribute__((pure)) bool
LoopifyTrees::tree_contains(const unsigned int &x,
                            const LoopifyTrees::tree<unsigned int> &t) {
  struct _Enter {
    const LoopifyTrees::tree<unsigned int> t;
  };

  struct _Call1 {
    LoopifyTrees::tree<unsigned int> _s0;
    decltype(std::declval<const unsigned int &>() ==
             std::declval<unsigned int &>()) _s1;
  };

  struct _Call2 {
    bool _s0;
    decltype(std::declval<const unsigned int &>() ==
             std::declval<unsigned int &>()) _s1;
  };

  using _Frame = std::variant<_Enter, _Call1, _Call2>;
  bool _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{t});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const LoopifyTrees::tree<unsigned int> t = _f.t;
      if (std::holds_alternative<
              typename LoopifyTrees::tree<unsigned int>::Leaf>(t.v())) {
        _result = false;
      } else {
        const auto &[d_a0, d_a1, d_a2] =
            std::get<typename LoopifyTrees::tree<unsigned int>::Node>(t.v());
        _stack.emplace_back(_Call1{*(d_a0), x == d_a1});
        _stack.emplace_back(_Enter{*(d_a2)});
      }
    } else if (std::holds_alternative<_Call1>(_frame)) {
      auto _f = std::move(std::get<_Call1>(_frame));
      _stack.emplace_back(_Call2{_result, _f._s1});
      _stack.emplace_back(_Enter{_f._s0});
    } else {
      auto _f = std::move(std::get<_Call2>(_frame));
      _result = (_f._s1 || (_result || _f._s0));
    }
  }
  return _result;
}
