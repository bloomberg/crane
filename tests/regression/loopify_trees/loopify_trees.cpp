#include "loopify_trees.h"

/// Consolidated UNIQUE tree algorithms - domain-specific tree operations.
uint64_t LoopifyTrees::tree_sum(const LoopifyTrees::tree<uint64_t> &t) {
  // Explicit stack replaces the non-tail recursion of tree_sum: _call frames
  // are pending calls, _after frames resume a caller.
  struct _call {
    const LoopifyTrees::tree<uint64_t> *t;
  };

  struct _after_tree_sum_in_Node {
    uint64_t a1;
    const LoopifyTrees::tree<uint64_t> *a2;
  };

  struct _after_tree_sum_in_Node_2 {
    uint64_t a1;
    uint64_t _tmp2;
  };

  using _frame =
      std::variant<_call, _after_tree_sum_in_Node, _after_tree_sum_in_Node_2>;
  uint64_t _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&t});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const LoopifyTrees::tree<uint64_t> &t = *_f.t;
      if (std::holds_alternative<typename LoopifyTrees::tree<uint64_t>::Leaf>(
              t.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1, a2] =
            std::get<typename LoopifyTrees::tree<uint64_t>::Node>(t.v());
        _stack.emplace_back(_after_tree_sum_in_Node{a1, crane_raw(a2)});
        _stack.emplace_back(_call{crane_raw(a0)});
      }
    } else if (std::holds_alternative<_after_tree_sum_in_Node>(_popped)) {
      auto _f = std::move(std::get<_after_tree_sum_in_Node>(_popped));
      _stack.pop_back();
      uint64_t a1 = _f.a1;
      const LoopifyTrees::tree<uint64_t> &a2 = *_f.a2;
      _stack.emplace_back(_after_tree_sum_in_Node_2{a1, std::move(_result)});
      _stack.emplace_back(_call{&a2});
    } else {
      auto _f = std::move(std::get<_after_tree_sum_in_Node_2>(_popped));
      _stack.pop_back();
      uint64_t a1 = _f.a1;
      _result = (a1 + (_f._tmp2 + std::move(_result)));
    }
  }
  return _result;
}

/// leaf_sum sums only leaf values.
uint64_t LoopifyTrees::leaf_sum(const LoopifyTrees::tree<uint64_t> &t) {
  // Explicit stack replaces the non-tail recursion of leaf_sum: _call frames
  // are pending calls, _after frames resume a caller.
  struct _call {
    const LoopifyTrees::tree<uint64_t> *t;
  };

  struct _after_leaf_sum_in_Node {
    const LoopifyTrees::tree<uint64_t> *a2;
  };

  struct _after_leaf_sum_in_Node_2 {
    uint64_t _tmp2;
  };

  struct _after_leaf_sum_in_Node_3 {
    const LoopifyTrees::tree<uint64_t> *a2;
  };

  struct _after_leaf_sum_in_Node_4 {
    uint64_t _tmp4;
  };

  using _frame =
      std::variant<_call, _after_leaf_sum_in_Node, _after_leaf_sum_in_Node_2,
                   _after_leaf_sum_in_Node_3, _after_leaf_sum_in_Node_4>;
  uint64_t _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&t});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
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
            _stack.emplace_back(_after_leaf_sum_in_Node{crane_raw(a2)});
            _stack.emplace_back(_call{crane_raw(a0)});
          }
        } else {
          _stack.emplace_back(_after_leaf_sum_in_Node_3{crane_raw(a2)});
          _stack.emplace_back(_call{crane_raw(a0)});
        }
      }
    } else if (std::holds_alternative<_after_leaf_sum_in_Node>(_popped)) {
      auto _f = std::move(std::get<_after_leaf_sum_in_Node>(_popped));
      _stack.pop_back();
      const LoopifyTrees::tree<uint64_t> &a2 = *_f.a2;
      _stack.emplace_back(_after_leaf_sum_in_Node_2{std::move(_result)});
      _stack.emplace_back(_call{&a2});
    } else if (std::holds_alternative<_after_leaf_sum_in_Node_2>(_popped)) {
      auto _f = std::move(std::get<_after_leaf_sum_in_Node_2>(_popped));
      _stack.pop_back();
      _result = (_f._tmp2 + std::move(_result));
    } else if (std::holds_alternative<_after_leaf_sum_in_Node_3>(_popped)) {
      auto _f = std::move(std::get<_after_leaf_sum_in_Node_3>(_popped));
      _stack.pop_back();
      const LoopifyTrees::tree<uint64_t> &a2 = *_f.a2;
      _stack.emplace_back(_after_leaf_sum_in_Node_4{std::move(_result)});
      _stack.emplace_back(_call{&a2});
    } else {
      auto _f = std::move(std::get<_after_leaf_sum_in_Node_4>(_popped));
      _stack.pop_back();
      _result = (_f._tmp4 + std::move(_result));
    }
  }
  return _result;
}

/// insert_bst BST insertion.
LoopifyTrees::tree<uint64_t>
LoopifyTrees::insert_bst(uint64_t x, const LoopifyTrees::tree<uint64_t> &t) {
  // Explicit stack replaces the non-tail recursion of insert_bst: _call frames
  // are pending calls, _after frames resume a caller.
  struct _call {
    const LoopifyTrees::tree<uint64_t> *t;
  };

  struct _after_insert_bst_in_false {
    std::shared_ptr<LoopifyTrees::tree<uint64_t>> a0;
    uint64_t a1;
  };

  struct _after_insert_bst_in_true {
    uint64_t a1;
    std::shared_ptr<LoopifyTrees::tree<uint64_t>> a2;
  };

  using _frame = std::variant<_call, _after_insert_bst_in_false,
                              _after_insert_bst_in_true>;
  LoopifyTrees::tree<uint64_t> _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&t});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const LoopifyTrees::tree<uint64_t> &t = *_f.t;
      if (std::holds_alternative<typename LoopifyTrees::tree<uint64_t>::Leaf>(
              t.v())) {
        _result = tree<uint64_t>::node(tree<uint64_t>::leaf(), x,
                                       tree<uint64_t>::leaf());
      } else {
        const auto &[a0, a1, a2] =
            std::get<typename LoopifyTrees::tree<uint64_t>::Node>(t.v());
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
      std::shared_ptr<LoopifyTrees::tree<uint64_t>> a0 = std::move(_f.a0);
      uint64_t a1 = _f.a1;
      _result =
          tree<uint64_t>::node(crane::shared_child(a0), a1, std::move(_result));
    } else {
      auto _f = std::move(std::get<_after_insert_bst_in_true>(_popped));
      _stack.pop_back();
      uint64_t a1 = _f.a1;
      std::shared_ptr<LoopifyTrees::tree<uint64_t>> a2 = std::move(_f.a2);
      _result =
          tree<uint64_t>::node(std::move(_result), a1, crane::shared_child(a2));
    }
  }
  return _result;
}

/// count_paths t n counts root-to-leaf paths that sum to n.
uint64_t LoopifyTrees::count_paths(const LoopifyTrees::tree<uint64_t> &t,
                                   uint64_t n) {
  // Explicit stack replaces the non-tail recursion of count_paths: _call frames
  // are pending calls, _after frames resume a caller.
  struct _call {
    uint64_t n;
    const LoopifyTrees::tree<uint64_t> *t;
  };

  struct _after_count_paths_in_false {
    const LoopifyTrees::tree<uint64_t> *a2;
    uint64_t remaining;
  };

  struct _after_count_paths_in_false_2 {
    uint64_t _tmp4;
  };

  struct _after_count_paths_in_true {
    const LoopifyTrees::tree<uint64_t> *a2;
  };

  struct _after_count_paths_in_true_2 {
    uint64_t _tmp2;
  };

  using _frame = std::variant<
      _call, _after_count_paths_in_false, _after_count_paths_in_false_2,
      _after_count_paths_in_true, _after_count_paths_in_true_2>;
  uint64_t _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{n, &t});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
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
            _stack.emplace_back(_after_count_paths_in_true{crane_raw(a2)});
            _stack.emplace_back(_call{UINT64_C(0), crane_raw(a0)});
          } else {
            _result = UINT64_C(0);
          }
        } else {
          uint64_t remaining = (((n - a1) > n ? 0 : (n - a1)));
          _stack.emplace_back(
              _after_count_paths_in_false{crane_raw(a2), remaining});
          _stack.emplace_back(_call{remaining, crane_raw(a0)});
        }
      }
    } else if (std::holds_alternative<_after_count_paths_in_false>(_popped)) {
      auto _f = std::move(std::get<_after_count_paths_in_false>(_popped));
      _stack.pop_back();
      const LoopifyTrees::tree<uint64_t> &a2 = *_f.a2;
      uint64_t remaining = _f.remaining;
      _stack.emplace_back(_after_count_paths_in_false_2{std::move(_result)});
      _stack.emplace_back(_call{remaining, &a2});
    } else if (std::holds_alternative<_after_count_paths_in_false_2>(_popped)) {
      auto _f = std::move(std::get<_after_count_paths_in_false_2>(_popped));
      _stack.pop_back();
      _result = (_f._tmp4 + std::move(_result));
    } else if (std::holds_alternative<_after_count_paths_in_true>(_popped)) {
      auto _f = std::move(std::get<_after_count_paths_in_true>(_popped));
      _stack.pop_back();
      const LoopifyTrees::tree<uint64_t> &a2 = *_f.a2;
      _stack.emplace_back(_after_count_paths_in_true_2{std::move(_result)});
      _stack.emplace_back(_call{UINT64_C(0), &a2});
    } else {
      auto _f = std::move(std::get<_after_count_paths_in_true_2>(_popped));
      _stack.pop_back();
      _result = (_f._tmp2 + std::move(_result));
    }
  }
  return _result;
}

/// sum_of_max_branches sums maximum values along each path.
uint64_t
LoopifyTrees::sum_of_max_branches(const LoopifyTrees::tree<uint64_t> &t) {
  // Explicit stack replaces the non-tail recursion of sum_of_max_branches:
  // _call frames are pending calls, _after frames resume a caller.
  struct _call {
    const LoopifyTrees::tree<uint64_t> *t;
  };

  struct _after_sum_of_max_branches_in_Node {
    uint64_t a1;
    const LoopifyTrees::tree<uint64_t> *a2;
  };

  struct _after_sum_of_max_branches_in_Node_2 {
    uint64_t a1;
    uint64_t lsum;
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
      const LoopifyTrees::tree<uint64_t> &t = *_f.t;
      if (std::holds_alternative<typename LoopifyTrees::tree<uint64_t>::Leaf>(
              t.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1, a2] =
            std::get<typename LoopifyTrees::tree<uint64_t>::Node>(t.v());
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
      const LoopifyTrees::tree<uint64_t> &a2 = *_f.a2;
      uint64_t lsum = std::move(_result);
      _stack.emplace_back(_after_sum_of_max_branches_in_Node_2{a1, lsum});
      _stack.emplace_back(_call{&a2});
    } else {
      auto _f =
          std::move(std::get<_after_sum_of_max_branches_in_Node_2>(_popped));
      _stack.pop_back();
      uint64_t a1 = _f.a1;
      uint64_t lsum = _f.lsum;
      uint64_t rsum = std::move(_result);
      _result = (a1 + (lsum <= rsum ? rsum : lsum));
    }
  }
  return _result;
}

/// Helper: sum all values in a list of rose trees (processes both tree and
/// list levels in one recursive function to enable full loopification).
uint64_t LoopifyTrees::sum_rose_list_fuel(uint64_t fuel,
                                          const List<LoopifyTrees::rose> &cs) {
  // Explicit stack replaces the non-tail recursion of sum_rose_list_fuel: _call
  // frames are pending calls, _after frames resume a caller.
  struct _call {
    const List<LoopifyTrees::rose> *cs;
    uint64_t fuel;
  };

  struct _after_sum_rose_list_fuel_in_RNode {
    uint64_t f;
    const List<LoopifyTrees::rose> *a1;
    uint64_t a00;
  };

  struct _after_sum_rose_list_fuel_in_RNode_2 {
    uint64_t a00;
    uint64_t _tmp2;
  };

  using _frame = std::variant<_call, _after_sum_rose_list_fuel_in_RNode,
                              _after_sum_rose_list_fuel_in_RNode_2>;
  uint64_t _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&cs, fuel});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
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
          _stack.emplace_back(
              _after_sum_rose_list_fuel_in_RNode{f, crane_raw(a1), a00});
          _stack.emplace_back(_call{crane_raw(a10), f});
        }
      }
    } else if (
            std::holds_alternative<_after_sum_rose_list_fuel_in_RNode>(_popped)) {
      auto _f =
          std::move(std::get<_after_sum_rose_list_fuel_in_RNode>(_popped));
      _stack.pop_back();
      uint64_t f = _f.f;
      const List<LoopifyTrees::rose> &a1 = *_f.a1;
      uint64_t a00 = _f.a00;
      _stack.emplace_back(
          _after_sum_rose_list_fuel_in_RNode_2{a00, std::move(_result)});
      _stack.emplace_back(_call{&a1, f});
    } else {
      auto _f =
          std::move(std::get<_after_sum_rose_list_fuel_in_RNode_2>(_popped));
      _stack.pop_back();
      uint64_t a00 = _f.a00;
      _result = (a00 + (_f._tmp2 + std::move(_result)));
    }
  }
  return _result;
}

/// Helper: flatten a list of rose trees to a flat list of nats.
List<uint64_t>
LoopifyTrees::flatten_rose_list_fuel(uint64_t fuel,
                                     const List<LoopifyTrees::rose> &cs) {
  // Explicit stack replaces the non-tail recursion of flatten_rose_list_fuel:
  // _call frames are pending calls, _after frames resume a caller.
  struct _call {
    const List<LoopifyTrees::rose> *cs;
    uint64_t fuel;
  };

  struct _after_flatten_rose_list_fuel_in_RNode {
    uint64_t f;
    const List<LoopifyTrees::rose> *a1;
    uint64_t a00;
  };

  struct _after_flatten_rose_list_fuel_in_RNode_2 {
    uint64_t a00;
    List<uint64_t> _tmp2;
  };

  using _frame = std::variant<_call, _after_flatten_rose_list_fuel_in_RNode,
                              _after_flatten_rose_list_fuel_in_RNode_2>;
  List<uint64_t> _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&cs, fuel});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
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
          _stack.emplace_back(
              _after_flatten_rose_list_fuel_in_RNode{f, crane_raw(a1), a00});
          _stack.emplace_back(_call{crane_raw(a10), f});
        }
      }
    } else if (std::holds_alternative<_after_flatten_rose_list_fuel_in_RNode>(
                   _popped)) {
      auto _f =
          std::move(std::get<_after_flatten_rose_list_fuel_in_RNode>(_popped));
      _stack.pop_back();
      uint64_t f = _f.f;
      const List<LoopifyTrees::rose> &a1 = *_f.a1;
      uint64_t a00 = _f.a00;
      _stack.emplace_back(
          _after_flatten_rose_list_fuel_in_RNode_2{a00, std::move(_result)});
      _stack.emplace_back(_call{&a1, f});
    } else {
      auto _f = std::move(
          std::get<_after_flatten_rose_list_fuel_in_RNode_2>(_popped));
      _stack.pop_back();
      uint64_t a00 = _f.a00;
      _result = List<uint64_t>::cons(a00, _f._tmp2.app(std::move(_result)));
    }
  }
  return _result;
}

/// Helper: compute maximum depth among a list of rose trees.
uint64_t
LoopifyTrees::depth_rose_list_fuel(uint64_t fuel,
                                   const List<LoopifyTrees::rose> &cs) {
  // Explicit stack replaces the non-tail recursion of depth_rose_list_fuel:
  // _call frames are pending calls, _after frames resume a caller.
  struct _call {
    const List<LoopifyTrees::rose> *cs;
    uint64_t fuel;
  };

  struct _after_depth_rose_list_fuel_in_RNode {
    uint64_t f;
    const List<LoopifyTrees::rose> *a1;
  };

  struct _after_depth_rose_list_fuel_in_RNode_2 {
    uint64_t d;
  };

  using _frame = std::variant<_call, _after_depth_rose_list_fuel_in_RNode,
                              _after_depth_rose_list_fuel_in_RNode_2>;
  uint64_t _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&cs, fuel});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
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
          const auto &[_, a10] =
              std::get<typename LoopifyTrees::rose::RNode>(a0.v());
          _stack.emplace_back(
              _after_depth_rose_list_fuel_in_RNode{f, crane_raw(a1)});
          _stack.emplace_back(_call{crane_raw(a10), f});
        }
      }
    } else if (std::holds_alternative<_after_depth_rose_list_fuel_in_RNode>(
                   _popped)) {
      auto _f =
          std::move(std::get<_after_depth_rose_list_fuel_in_RNode>(_popped));
      _stack.pop_back();
      uint64_t f = _f.f;
      const List<LoopifyTrees::rose> &a1 = *_f.a1;
      uint64_t d = (std::move(_result) + 1);
      _stack.emplace_back(_after_depth_rose_list_fuel_in_RNode_2{d});
      _stack.emplace_back(_call{&a1, f});
    } else {
      auto _f =
          std::move(std::get<_after_depth_rose_list_fuel_in_RNode_2>(_popped));
      _stack.pop_back();
      uint64_t d = _f.d;
      uint64_t rest_max = std::move(_result);
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
LoopifyTrees::tree<uint64_t>
LoopifyTrees::tree_max(const LoopifyTrees::tree<uint64_t> &t1,
                       const LoopifyTrees::tree<uint64_t> &t2) {
  // Explicit stack replaces the non-tail recursion of tree_max: _call frames
  // are pending calls, _after frames resume a caller.
  struct _call {
    const LoopifyTrees::tree<uint64_t> *t2;
    const LoopifyTrees::tree<uint64_t> *t1;
  };

  struct _after_tree_max_in_Node {
    const LoopifyTrees::tree<uint64_t> *a2;
    const LoopifyTrees::tree<uint64_t> *a20;
    uint64_t max_val;
  };

  struct _after_tree_max_in_Node_2 {
    uint64_t max_val;
    LoopifyTrees::tree<uint64_t> _tmp2;
  };

  using _frame =
      std::variant<_call, _after_tree_max_in_Node, _after_tree_max_in_Node_2>;
  LoopifyTrees::tree<uint64_t> _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&t2, &t1});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const LoopifyTrees::tree<uint64_t> &t2 = *_f.t2;
      const LoopifyTrees::tree<uint64_t> &t1 = *_f.t1;
      if (std::holds_alternative<typename LoopifyTrees::tree<uint64_t>::Leaf>(
              t1.v())) {
        if (std::holds_alternative<typename LoopifyTrees::tree<uint64_t>::Leaf>(
                t2.v())) {
          _result = tree<uint64_t>::leaf();
        } else {
          _result = std::move(t2);
        }
      } else {
        const auto &[a0, a1, a2] =
            std::get<typename LoopifyTrees::tree<uint64_t>::Node>(t1.v());
        if (std::holds_alternative<typename LoopifyTrees::tree<uint64_t>::Leaf>(
                t2.v())) {
          _result = std::move(t1);
        } else {
          const auto &[a00, a10, a20] =
              std::get<typename LoopifyTrees::tree<uint64_t>::Node>(t2.v());
          uint64_t max_val;
          if (a1 <= a10) {
            max_val = a10;
          } else {
            max_val = a1;
          }
          _stack.emplace_back(
              _after_tree_max_in_Node{crane_raw(a2), crane_raw(a20), max_val});
          _stack.emplace_back(_call{crane_raw(a00), crane_raw(a0)});
        }
      }
    } else if (std::holds_alternative<_after_tree_max_in_Node>(_popped)) {
      auto _f = std::move(std::get<_after_tree_max_in_Node>(_popped));
      _stack.pop_back();
      const LoopifyTrees::tree<uint64_t> &a2 = *_f.a2;
      const LoopifyTrees::tree<uint64_t> &a20 = *_f.a20;
      uint64_t max_val = _f.max_val;
      _stack.emplace_back(
          _after_tree_max_in_Node_2{max_val, std::move(_result)});
      _stack.emplace_back(_call{&a20, &a2});
    } else {
      auto _f = std::move(std::get<_after_tree_max_in_Node_2>(_popped));
      _stack.pop_back();
      uint64_t max_val = _f.max_val;
      _result = tree<uint64_t>::node(std::move(_f._tmp2), max_val,
                                     std::move(_result));
    }
  }
  return _result;
}

/// Helper: extract values from trees.
List<uint64_t> LoopifyTrees::extract_tree_values(
    const List<LoopifyTrees::tree<uint64_t>> &ts) {
  // Builds the result front to back: _write points at the empty tail the next
  // cell fills.
  std::optional<List<uint64_t>> _root{};
  std::shared_ptr<List<uint64_t>> *_write = nullptr;
  const List<LoopifyTrees::tree<uint64_t>> *_loop_ts = &ts;
  while (true) {
    if (std::holds_alternative<typename List<LoopifyTrees::tree<uint64_t>>::Nil>(
            _loop_ts->v())) {
      auto _value = List<uint64_t>::nil();
      (_write ? *(*_write = std::make_shared<List<uint64_t>>(std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename List<LoopifyTrees::tree<uint64_t>>::Cons>(
              _loop_ts->v());
      if (std::holds_alternative<typename LoopifyTrees::tree<uint64_t>::Leaf>(
              a0.v())) {
        _loop_ts = crane_raw(a1);
        continue;
      } else {
        const auto &[_, a10, _] =
            std::get<typename LoopifyTrees::tree<uint64_t>::Node>(a0.v());
        auto _cell = typename List<uint64_t>::Cons(a10, nullptr);
        List<uint64_t> &_node =
            (_write ? *(*_write =
                            std::make_shared<List<uint64_t>>(std::move(_cell)))
                    : _root.emplace(std::move(_cell)));
        _write = &std::get<typename List<uint64_t>::Cons>(_node.v_mut()).l;
        _loop_ts = crane_raw(a1);
        continue;
      }
    }
  }
  return std::move(*_root);
}

/// Helper: extract children from trees.
List<LoopifyTrees::tree<uint64_t>> LoopifyTrees::extract_tree_children(
    const List<LoopifyTrees::tree<uint64_t>> &ts) {
  // Builds the result front to back: _write points at the empty tail the next
  // cell fills.
  std::optional<List<LoopifyTrees::tree<uint64_t>>> _root{};
  std::shared_ptr<List<LoopifyTrees::tree<uint64_t>>> *_write = nullptr;
  const List<LoopifyTrees::tree<uint64_t>> *_loop_ts = &ts;
  while (true) {
    if (std::holds_alternative<typename List<LoopifyTrees::tree<uint64_t>>::Nil>(
            _loop_ts->v())) {
      auto _value = List<LoopifyTrees::tree<uint64_t>>::nil();
      (
          _write ? *(*_write =
                         std::make_shared<List<LoopifyTrees::tree<uint64_t>>>(
                             std::move(_value)))
                 : _root.emplace(std::move(_value)));
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename List<LoopifyTrees::tree<uint64_t>>::Cons>(
              _loop_ts->v());
      if (std::holds_alternative<typename LoopifyTrees::tree<uint64_t>::Leaf>(
              a0.v())) {
        _loop_ts = crane_raw(a1);
        continue;
      } else {
        const auto &[a00, _, a20] =
            std::get<typename LoopifyTrees::tree<uint64_t>::Node>(a0.v());
        auto _cell1 = std::make_shared<List<LoopifyTrees::tree<uint64_t>>>(
            typename List<LoopifyTrees::tree<uint64_t>>::Cons(*a20, nullptr));
        auto _cell = typename List<LoopifyTrees::tree<uint64_t>>::Cons(
            *a00, std::move(_cell1));
        List<LoopifyTrees::tree<uint64_t>> &_node =
            (_write ? *(*_write = std::make_shared<
                            List<LoopifyTrees::tree<uint64_t>>>(
                            std::move(_cell)))
                    : _root.emplace(std::move(_cell)));
        _write =
            &std::get<typename List<LoopifyTrees::tree<uint64_t>>::Cons>(
                std::get<typename List<LoopifyTrees::tree<uint64_t>>::Cons>(
                    _node.v_mut())
                    .l->v_mut())
                .l;
        _loop_ts = crane_raw(a1);
        continue;
      }
    }
  }
  return std::move(*_root);
}

/// tree_levels t returns list of lists, one per level (breadth-first).
List<List<uint64_t>> LoopifyTrees::tree_levels_fuel(
    uint64_t fuel, const List<LoopifyTrees::tree<uint64_t>> &trees) {
  // Builds the result front to back: _write points at the empty tail the next
  // cell fills.
  std::optional<List<List<uint64_t>>> _root{};
  std::shared_ptr<List<List<uint64_t>>> *_write = nullptr;
  List<LoopifyTrees::tree<uint64_t>> _loop_trees = trees;
  uint64_t _loop_fuel = fuel;
  while (true) {
    if (_loop_fuel <= 0) {
      auto _value = List<List<uint64_t>>::nil();
      (_write ? *(*_write =
                      std::make_shared<List<List<uint64_t>>>(std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      uint64_t f = _loop_fuel - 1;
      List<uint64_t> values = extract_tree_values(_loop_trees);
      if (std::holds_alternative<typename List<uint64_t>::Nil>(values.v())) {
        auto _value = List<List<uint64_t>>::nil();
        (_write ? *(*_write = std::make_shared<List<List<uint64_t>>>(
                        std::move(_value)))
                : _root.emplace(std::move(_value)));
        break;
      } else {
        List<LoopifyTrees::tree<uint64_t>> children =
            extract_tree_children(_loop_trees);
        auto _cell = typename List<List<uint64_t>>::Cons(values, nullptr);
        List<List<uint64_t>> &_node =
            (_write ? *(*_write = std::make_shared<List<List<uint64_t>>>(
                            std::move(_cell)))
                    : _root.emplace(std::move(_cell)));
        _write =
            &std::get<typename List<List<uint64_t>>::Cons>(_node.v_mut()).l;
        _loop_trees = std::move(children);
        _loop_fuel = f;
        continue;
      }
    }
  }
  return std::move(*_root);
}

List<List<uint64_t>>
LoopifyTrees::tree_levels(const LoopifyTrees::tree<uint64_t> &t) {
  return tree_levels_fuel(UINT64_C(100),
                          List<LoopifyTrees::tree<uint64_t>>::cons(
                              t, List<LoopifyTrees::tree<uint64_t>>::nil()));
}

/// count_nodes t returns tuple (node_count, sum_of_values).
std::pair<uint64_t, uint64_t>
LoopifyTrees::count_nodes(const LoopifyTrees::tree<uint64_t> &t) {
  // Explicit stack replaces the non-tail recursion of count_nodes: _call frames
  // are pending calls, _after frames resume a caller.
  struct _call {
    const LoopifyTrees::tree<uint64_t> *t;
  };

  struct _after_count_nodes_in_Node {
    uint64_t a1;
    const LoopifyTrees::tree<uint64_t> *a2;
  };

  struct _after_count_nodes_in_pair {
    uint64_t a1;
    uint64_t lc;
    uint64_t ls;
  };

  using _frame = std::variant<_call, _after_count_nodes_in_Node,
                              _after_count_nodes_in_pair>;
  std::pair<uint64_t, uint64_t> _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&t});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const LoopifyTrees::tree<uint64_t> &t = *_f.t;
      if (std::holds_alternative<typename LoopifyTrees::tree<uint64_t>::Leaf>(
              t.v())) {
        _result = std::make_pair(UINT64_C(0), UINT64_C(0));
      } else {
        const auto &[a0, a1, a2] =
            std::get<typename LoopifyTrees::tree<uint64_t>::Node>(t.v());
        _stack.emplace_back(_after_count_nodes_in_Node{a1, crane_raw(a2)});
        _stack.emplace_back(_call{crane_raw(a0)});
      }
    } else if (std::holds_alternative<_after_count_nodes_in_Node>(_popped)) {
      auto _f = std::move(std::get<_after_count_nodes_in_Node>(_popped));
      _stack.pop_back();
      uint64_t a1 = _f.a1;
      const LoopifyTrees::tree<uint64_t> &a2 = *_f.a2;
      std::pair<uint64_t, uint64_t> _tmp2 = std::move(_result);
      const auto &[lc, ls] = _tmp2;
      _stack.emplace_back(_after_count_nodes_in_pair{a1, lc, ls});
      _stack.emplace_back(_call{&a2});
    } else {
      auto _f = std::move(std::get<_after_count_nodes_in_pair>(_popped));
      _stack.pop_back();
      uint64_t a1 = _f.a1;
      uint64_t lc = _f.lc;
      uint64_t ls = _f.ls;
      std::pair<uint64_t, uint64_t> _tmp1 = std::move(_result);
      const auto &[rc, rs] = _tmp1;
      _result = std::make_pair(((lc + rc) + 1), (a1 + (ls + rs)));
    }
  }
  return _result;
}

/// Helper: append two lists of lists.
List<List<uint64_t>>
LoopifyTrees::append_list_lists(const List<List<uint64_t>> &l1,
                                List<List<uint64_t>> l2) {
  // Builds the result front to back: _write points at the empty tail the next
  // cell fills.
  std::optional<List<List<uint64_t>>> _root{};
  std::shared_ptr<List<List<uint64_t>>> *_write = nullptr;
  const List<List<uint64_t>> *_loop_l1 = &l1;
  while (true) {
    if (std::holds_alternative<typename List<List<uint64_t>>::Nil>(
            _loop_l1->v())) {
      auto _value = std::move(l2);
      (_write ? *(*_write =
                      std::make_shared<List<List<uint64_t>>>(std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename List<List<uint64_t>>::Cons>(_loop_l1->v());
      auto _cell = typename List<List<uint64_t>>::Cons(a0, nullptr);
      List<List<uint64_t>> &_node =
          (_write ? *(*_write = std::make_shared<List<List<uint64_t>>>(
                          std::move(_cell)))
                  : _root.emplace(std::move(_cell)));
      _write = &std::get<typename List<List<uint64_t>>::Cons>(_node.v_mut()).l;
      _loop_l1 = crane_raw(a1);
      continue;
    }
  }
  return std::move(*_root);
}

/// Helper: prepend value to all lists in a list of lists.
List<List<uint64_t>>
LoopifyTrees::map_cons_to_all(uint64_t x, const List<List<uint64_t>> &lsts) {
  // Builds the result front to back: _write points at the empty tail the next
  // cell fills.
  std::optional<List<List<uint64_t>>> _root{};
  std::shared_ptr<List<List<uint64_t>>> *_write = nullptr;
  const List<List<uint64_t>> *_loop_lsts = &lsts;
  while (true) {
    if (std::holds_alternative<typename List<List<uint64_t>>::Nil>(
            _loop_lsts->v())) {
      auto _value = List<List<uint64_t>>::nil();
      (_write ? *(*_write =
                      std::make_shared<List<List<uint64_t>>>(std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename List<List<uint64_t>>::Cons>(_loop_lsts->v());
      auto _cell = typename List<List<uint64_t>>::Cons(
          List<uint64_t>::cons(x, a0), nullptr);
      List<List<uint64_t>> &_node =
          (_write ? *(*_write = std::make_shared<List<List<uint64_t>>>(
                          std::move(_cell)))
                  : _root.emplace(std::move(_cell)));
      _write = &std::get<typename List<List<uint64_t>>::Cons>(_node.v_mut()).l;
      _loop_lsts = crane_raw(a1);
      continue;
    }
  }
  return std::move(*_root);
}

/// paths t returns all root-to-leaf paths in tree.
List<List<uint64_t>>
LoopifyTrees::paths(const LoopifyTrees::tree<uint64_t> &t) {
  // Explicit stack replaces the non-tail recursion of paths: _call frames are
  // pending calls, _after frames resume a caller.
  struct _call {
    const LoopifyTrees::tree<uint64_t> *t;
  };

  struct _after_paths_in_Node {
    uint64_t a1;
    const LoopifyTrees::tree<uint64_t> *a2;
  };

  struct _after_paths_in_Node_2 {
    uint64_t a1;
    List<List<uint64_t>> _tmp2;
  };

  using _frame =
      std::variant<_call, _after_paths_in_Node, _after_paths_in_Node_2>;
  List<List<uint64_t>> _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&t});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const LoopifyTrees::tree<uint64_t> &t = *_f.t;
      if (std::holds_alternative<typename LoopifyTrees::tree<uint64_t>::Leaf>(
              t.v())) {
        _result = List<List<uint64_t>>::cons(List<uint64_t>::nil(),
                                             List<List<uint64_t>>::nil());
      } else {
        const auto &[a0, a1, a2] =
            std::get<typename LoopifyTrees::tree<uint64_t>::Node>(t.v());
        _stack.emplace_back(_after_paths_in_Node{a1, crane_raw(a2)});
        _stack.emplace_back(_call{crane_raw(a0)});
      }
    } else if (std::holds_alternative<_after_paths_in_Node>(_popped)) {
      auto _f = std::move(std::get<_after_paths_in_Node>(_popped));
      _stack.pop_back();
      uint64_t a1 = _f.a1;
      const LoopifyTrees::tree<uint64_t> &a2 = *_f.a2;
      _stack.emplace_back(_after_paths_in_Node_2{a1, std::move(_result)});
      _stack.emplace_back(_call{&a2});
    } else {
      auto _f = std::move(std::get<_after_paths_in_Node_2>(_popped));
      _stack.pop_back();
      uint64_t a1 = _f.a1;
      _result = append_list_lists(map_cons_to_all(a1, std::move(_f._tmp2)),
                                  map_cons_to_all(a1, std::move(_result)));
    }
  }
  return _result;
}

/// collect_sorted t collects and sorts all tree values.
List<uint64_t>
LoopifyTrees::collect_unsorted(const LoopifyTrees::tree<uint64_t> &t) {
  // Explicit stack replaces the non-tail recursion of collect_unsorted: _call
  // frames are pending calls, _after frames resume a caller.
  struct _call {
    const LoopifyTrees::tree<uint64_t> *t;
  };

  struct _after_collect_unsorted_in_Node {
    uint64_t a1;
    const LoopifyTrees::tree<uint64_t> *a2;
  };

  struct _after_collect_unsorted_in_Node_2 {
    uint64_t a1;
    List<uint64_t> _tmp2;
  };

  using _frame = std::variant<_call, _after_collect_unsorted_in_Node,
                              _after_collect_unsorted_in_Node_2>;
  List<uint64_t> _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&t});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const LoopifyTrees::tree<uint64_t> &t = *_f.t;
      if (std::holds_alternative<typename LoopifyTrees::tree<uint64_t>::Leaf>(
              t.v())) {
        _result = List<uint64_t>::nil();
      } else {
        const auto &[a0, a1, a2] =
            std::get<typename LoopifyTrees::tree<uint64_t>::Node>(t.v());
        _stack.emplace_back(_after_collect_unsorted_in_Node{a1, crane_raw(a2)});
        _stack.emplace_back(_call{crane_raw(a0)});
      }
    } else if (std::holds_alternative<_after_collect_unsorted_in_Node>(_popped)) {
      auto _f = std::move(std::get<_after_collect_unsorted_in_Node>(_popped));
      _stack.pop_back();
      uint64_t a1 = _f.a1;
      const LoopifyTrees::tree<uint64_t> &a2 = *_f.a2;
      _stack.emplace_back(
          _after_collect_unsorted_in_Node_2{a1, std::move(_result)});
      _stack.emplace_back(_call{&a2});
    } else {
      auto _f = std::move(std::get<_after_collect_unsorted_in_Node_2>(_popped));
      _stack.pop_back();
      uint64_t a1 = _f.a1;
      _result = _f._tmp2.app(List<uint64_t>::cons(a1, std::move(_result)));
    }
  }
  return _result;
}

/// Simple insertion sort for collect_sorted.
List<uint64_t> LoopifyTrees::insert_sorted(uint64_t x,
                                           const List<uint64_t> &l) {
  // Builds the result front to back: _write points at the empty tail the next
  // cell fills.
  std::optional<List<uint64_t>> _root{};
  std::shared_ptr<List<uint64_t>> *_write = nullptr;
  const List<uint64_t> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l->v())) {
      auto _value = List<uint64_t>::cons(x, List<uint64_t>::nil());
      (_write ? *(*_write = std::make_shared<List<uint64_t>>(std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename List<uint64_t>::Cons>(_loop_l->v());
      if (x <= a0) {
        auto _value = List<uint64_t>::cons(
            x, List<uint64_t>::cons(a0, crane::shared_child(a1)));
        (_write ? *(*_write =
                        std::make_shared<List<uint64_t>>(std::move(_value)))
                : _root.emplace(std::move(_value)));
        break;
      } else {
        auto _cell = typename List<uint64_t>::Cons(a0, nullptr);
        List<uint64_t> &_node =
            (_write ? *(*_write =
                            std::make_shared<List<uint64_t>>(std::move(_cell)))
                    : _root.emplace(std::move(_cell)));
        _write = &std::get<typename List<uint64_t>::Cons>(_node.v_mut()).l;
        _loop_l = crane_raw(a1);
        continue;
      }
    }
  }
  return std::move(*_root);
}

List<uint64_t> LoopifyTrees::sort_list(const List<uint64_t> &l) {
  // Explicit stack replaces the non-tail recursion of sort_list: _call frames
  // are pending calls, _after frames resume a caller.
  struct _call {
    const List<uint64_t> *l;
  };

  struct _after_sort_list_in_Cons {
    uint64_t a0;
  };

  using _frame = std::variant<_call, _after_sort_list_in_Cons>;
  List<uint64_t> _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&l});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const List<uint64_t> &l = *_f.l;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
        _result = List<uint64_t>::nil();
      } else {
        const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
        _stack.emplace_back(_after_sort_list_in_Cons{a0});
        _stack.emplace_back(_call{crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<_after_sort_list_in_Cons>(_popped));
      _stack.pop_back();
      uint64_t a0 = _f.a0;
      _result = insert_sorted(a0, std::move(_result));
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
  // Explicit stack replaces the non-tail recursion of tree_min_max: _call
  // frames are pending calls, _after frames resume a caller.
  struct _call {
    const LoopifyTrees::tree<uint64_t> *t;
  };

  struct _after_tree_min_max_in_Node {
    uint64_t a1;
    const LoopifyTrees::tree<uint64_t> *a2;
  };

  struct _after_tree_min_max_in_pair {
    uint64_t a1;
    uint64_t lmin;
    uint64_t lmax;
  };

  using _frame = std::variant<_call, _after_tree_min_max_in_Node,
                              _after_tree_min_max_in_pair>;
  std::pair<uint64_t, uint64_t> _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&t});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const LoopifyTrees::tree<uint64_t> &t = *_f.t;
      if (std::holds_alternative<typename LoopifyTrees::tree<uint64_t>::Leaf>(
              t.v())) {
        _result = std::make_pair(UINT64_C(0), UINT64_C(0));
      } else {
        const auto &[a0, a1, a2] =
            std::get<typename LoopifyTrees::tree<uint64_t>::Node>(t.v());
        _stack.emplace_back(_after_tree_min_max_in_Node{a1, crane_raw(a2)});
        _stack.emplace_back(_call{crane_raw(a0)});
      }
    } else if (std::holds_alternative<_after_tree_min_max_in_Node>(_popped)) {
      auto _f = std::move(std::get<_after_tree_min_max_in_Node>(_popped));
      _stack.pop_back();
      uint64_t a1 = _f.a1;
      const LoopifyTrees::tree<uint64_t> &a2 = *_f.a2;
      std::pair<uint64_t, uint64_t> _tmp2 = std::move(_result);
      const auto &[lmin, lmax] = _tmp2;
      _stack.emplace_back(_after_tree_min_max_in_pair{a1, lmin, lmax});
      _stack.emplace_back(_call{&a2});
    } else {
      auto _f = std::move(std::get<_after_tree_min_max_in_pair>(_popped));
      _stack.pop_back();
      uint64_t a1 = _f.a1;
      uint64_t lmin = _f.lmin;
      uint64_t lmax = _f.lmax;
      std::pair<uint64_t, uint64_t> _tmp1 = std::move(_result);
      const auto &[rmin, rmax] = _tmp1;
      _result = std::make_pair(min3((lmin == UINT64_C(0) ? a1 : lmin),
                                    (rmin == UINT64_C(0) ? a1 : rmin), a1),
                               max3(lmax, rmax, a1));
    }
  }
  return _result;
}

/// all_paths_sum t sums all root-to-leaf path sums.
uint64_t LoopifyTrees::all_paths_sum(const LoopifyTrees::tree<uint64_t> &t) {
  {
    uint64_t _lc1_acc = UINT64_C(0);
    const LoopifyTrees::tree<uint64_t> &_lc1_tree0 = t;

    // Explicit stack replaces the non-tail recursion of sum_with_acc: _call
    // frames are pending calls, _after frames resume a caller.
    struct _call {
      const LoopifyTrees::tree<uint64_t> *tree0;
      uint64_t acc;
    };

    struct _after_sum_with_acc_in_Node {
      const LoopifyTrees::tree<uint64_t> *a2;
      uint64_t new_acc;
    };

    struct _after_sum_with_acc_in_Node_2 {
      uint64_t _tmp2;
    };

    using _frame = std::variant<_call, _after_sum_with_acc_in_Node,
                                _after_sum_with_acc_in_Node_2>;
    uint64_t _lc1_result{};
    crane::small_vector<_frame> _lc1_stack;
    _lc1_stack.emplace_back(_call{&_lc1_tree0, _lc1_acc});
    while (!_lc1_stack.empty()) {
      _frame &_popped = _lc1_stack.back();
      if (std::holds_alternative<_call>(_popped)) {
        auto _f = std::move(std::get<_call>(_popped));
        _lc1_stack.pop_back();
        const LoopifyTrees::tree<uint64_t> &_lc1_tree0 = *_f.tree0;
        uint64_t _lc1_acc = _f.acc;
        if (std::holds_alternative<typename LoopifyTrees::tree<uint64_t>::Leaf>(
                _lc1_tree0.v())) {
          _lc1_result = std::move(_lc1_acc);
        } else {
          const auto &[a0, a1, a2] =
              std::get<typename LoopifyTrees::tree<uint64_t>::Node>(
                  _lc1_tree0.v());
          uint64_t new_acc = (_lc1_acc + a1);
          _lc1_stack.emplace_back(
              _after_sum_with_acc_in_Node{crane_raw(a2), new_acc});
          _lc1_stack.emplace_back(_call{crane_raw(a0), new_acc});
        }
      } else if (std::holds_alternative<_after_sum_with_acc_in_Node>(_popped)) {
        auto _f = std::move(std::get<_after_sum_with_acc_in_Node>(_popped));
        _lc1_stack.pop_back();
        const LoopifyTrees::tree<uint64_t> &a2 = *_f.a2;
        uint64_t new_acc = _f.new_acc;
        _lc1_stack.emplace_back(
            _after_sum_with_acc_in_Node_2{std::move(_lc1_result)});
        _lc1_stack.emplace_back(_call{&a2, new_acc});
      } else {
        auto _f = std::move(std::get<_after_sum_with_acc_in_Node_2>(_popped));
        _lc1_stack.pop_back();
        _lc1_result = (_f._tmp2 + std::move(_lc1_result));
      }
    }
    return _lc1_result;
  }
}

/// tree_contains x t checks if value exists in tree.
bool LoopifyTrees::tree_contains(uint64_t x,
                                 const LoopifyTrees::tree<uint64_t> &t) {
  // Explicit stack replaces the non-tail recursion of tree_contains: _call
  // frames are pending calls, _after frames resume a caller.
  struct _call {
    const LoopifyTrees::tree<uint64_t> *t;
  };

  struct _after_tree_contains_in_Node {
    uint64_t a1;
    const LoopifyTrees::tree<uint64_t> *a2;
  };

  struct _after_tree_contains_in_Node_2 {
    uint64_t a1;
    bool _tmp2;
  };

  using _frame = std::variant<_call, _after_tree_contains_in_Node,
                              _after_tree_contains_in_Node_2>;
  bool _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&t});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const LoopifyTrees::tree<uint64_t> &t = *_f.t;
      if (std::holds_alternative<typename LoopifyTrees::tree<uint64_t>::Leaf>(
              t.v())) {
        _result = false;
      } else {
        const auto &[a0, a1, a2] =
            std::get<typename LoopifyTrees::tree<uint64_t>::Node>(t.v());
        _stack.emplace_back(_after_tree_contains_in_Node{a1, crane_raw(a2)});
        _stack.emplace_back(_call{crane_raw(a0)});
      }
    } else if (std::holds_alternative<_after_tree_contains_in_Node>(_popped)) {
      auto _f = std::move(std::get<_after_tree_contains_in_Node>(_popped));
      _stack.pop_back();
      uint64_t a1 = _f.a1;
      const LoopifyTrees::tree<uint64_t> &a2 = *_f.a2;
      _stack.emplace_back(
          _after_tree_contains_in_Node_2{a1, std::move(_result)});
      _stack.emplace_back(_call{&a2});
    } else {
      auto _f = std::move(std::get<_after_tree_contains_in_Node_2>(_popped));
      _stack.pop_back();
      uint64_t a1 = _f.a1;
      _result = (x == a1 || (_f._tmp2 || std::move(_result)));
    }
  }
  return _result;
}
