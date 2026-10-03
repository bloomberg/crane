#include "loopify_trees.h"

/// Consolidated UNIQUE tree algorithms - domain-specific tree operations.
uint64_t LoopifyTrees::tree_sum(
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

  /// _Cont_Node_1: saves [a1, r_], resumes after recursive call, then processes
  /// rest.
  struct _Cont_Node_1 {
    uint64_t a1;
    uint64_t r_;
  };

  using _Frame = std::variant<_Enter, _Cont_Node, _Cont_Node_1>;
  uint64_t _result{};
  crane::small_vector<_Frame> _stack;
  _stack.emplace_back(_Enter{&t});
  /// Loopified tree_sum: _Enter -> _Cont_Node -> _Cont_Node_1.
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
        _stack.emplace_back(_Cont_Node{a1, crane_raw(a2)});
        _stack.emplace_back(_Enter{crane_raw(a0)});
      }
    } else if (std::holds_alternative<_Cont_Node>(_frame)) {
      auto _f = std::move(std::get<_Cont_Node>(_frame));
      uint64_t a1 = _f.a1;
      const LoopifyTrees::tree<uint64_t> &a2 = *_f.a2;
      uint64_t r_ = std::move(_result);
      _stack.emplace_back(_Cont_Node_1{a1, r_});
      _stack.emplace_back(_Enter{&a2});
    } else {
      auto _f = std::move(std::get<_Cont_Node_1>(_frame));
      uint64_t a1 = _f.a1;
      uint64_t r_ = _f.r_;
      uint64_t r_0 = std::move(_result);
      _result = (a1 + (r_ + r_0));
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

  /// _Cont_Node: saves [a2], resumes after recursive call, then processes rest.
  struct _Cont_Node {
    const LoopifyTrees::tree<uint64_t> *a2;
  };

  /// _Cont_Node_1: saves [r_], resumes after recursive call, then processes
  /// rest.
  struct _Cont_Node_1 {
    uint64_t r_;
  };

  /// _Cont_Node_2: saves [a2], resumes after recursive call, then processes
  /// rest.
  struct _Cont_Node_2 {
    const LoopifyTrees::tree<uint64_t> *a2;
  };

  /// _Cont_Node_3: saves [r_], resumes after recursive call, then processes
  /// rest.
  struct _Cont_Node_3 {
    uint64_t r_;
  };

  using _Frame = std::variant<_Enter, _Cont_Node, _Cont_Node_1, _Cont_Node_2,
                              _Cont_Node_3>;
  uint64_t _result{};
  crane::small_vector<_Frame> _stack;
  _stack.emplace_back(_Enter{&t});
  /// Loopified leaf_sum: _Enter -> _Cont_Node -> _Cont_Node_1 -> _Cont_Node_2
  /// -> _Cont_Node_3.
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
            _stack.emplace_back(_Cont_Node{crane_raw(a2)});
            _stack.emplace_back(_Enter{crane_raw(a0)});
          }
        } else {
          _stack.emplace_back(_Cont_Node_2{crane_raw(a2)});
          _stack.emplace_back(_Enter{crane_raw(a0)});
        }
      }
    } else if (std::holds_alternative<_Cont_Node>(_frame)) {
      auto _f = std::move(std::get<_Cont_Node>(_frame));
      const LoopifyTrees::tree<uint64_t> &a2 = *_f.a2;
      uint64_t r_ = std::move(_result);
      _stack.emplace_back(_Cont_Node_1{r_});
      _stack.emplace_back(_Enter{&a2});
    } else if (std::holds_alternative<_Cont_Node_1>(_frame)) {
      auto _f = std::move(std::get<_Cont_Node_1>(_frame));
      uint64_t r_ = _f.r_;
      uint64_t r_0 = std::move(_result);
      _result = (r_ + r_0);
    } else if (std::holds_alternative<_Cont_Node_2>(_frame)) {
      auto _f = std::move(std::get<_Cont_Node_2>(_frame));
      const LoopifyTrees::tree<uint64_t> &a2 = *_f.a2;
      uint64_t r_ = std::move(_result);
      _stack.emplace_back(_Cont_Node_3{r_});
      _stack.emplace_back(_Enter{&a2});
    } else {
      auto _f = std::move(std::get<_Cont_Node_3>(_frame));
      uint64_t r_ = _f.r_;
      uint64_t r_0 = std::move(_result);
      _result = (r_ + r_0);
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
  crane::small_vector<_Frame> _stack;
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
          _stack.emplace_back(_Enter{crane_raw(a0)});
        } else {
          _stack.emplace_back(_Resume2{a1, *a0});
          _stack.emplace_back(_Enter{crane_raw(a2)});
        }
      }
    } else if (std::holds_alternative<_Resume1>(_frame)) {
      auto _f = std::move(std::get<_Resume1>(_frame));
      _result =
          tree<uint64_t>::node(std::move(_result), _f.a1, std::move(_f.a2));
    } else {
      auto _f = std::move(std::get<_Resume2>(_frame));
      _result =
          tree<uint64_t>::node(std::move(_f.a0), _f.a1, std::move(_result));
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

  /// _Cont1: saves [a2], resumes after recursive call, then processes rest.
  struct _Cont1 {
    const LoopifyTrees::tree<uint64_t> *a2;
  };

  /// _Cont2: saves [r_], resumes after recursive call, then processes rest.
  struct _Cont2 {
    uint64_t r_;
  };

  /// _Cont3: saves [a2, remaining], resumes after recursive call, then
  /// processes rest.
  struct _Cont3 {
    const LoopifyTrees::tree<uint64_t> *a2;
    uint64_t remaining;
  };

  /// _Cont4: saves [r_], resumes after recursive call, then processes rest.
  struct _Cont4 {
    uint64_t r_;
  };

  using _Frame = std::variant<_Enter, _Cont1, _Cont2, _Cont3, _Cont4>;
  uint64_t _result{};
  crane::small_vector<_Frame> _stack;
  _stack.emplace_back(_Enter{n, &t});
  /// Loopified count_paths: _Enter -> _Cont1 -> _Cont2 -> _Cont3 -> _Cont4.
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
            _stack.emplace_back(_Cont1{crane_raw(a2)});
            _stack.emplace_back(_Enter{UINT64_C(0), crane_raw(a0)});
          } else {
            _result = UINT64_C(0);
          }
        } else {
          uint64_t remaining = (((n - a1) > n ? 0 : (n - a1)));
          _stack.emplace_back(_Cont3{crane_raw(a2), remaining});
          _stack.emplace_back(_Enter{remaining, crane_raw(a0)});
        }
      }
    } else if (std::holds_alternative<_Cont1>(_frame)) {
      auto _f = std::move(std::get<_Cont1>(_frame));
      const LoopifyTrees::tree<uint64_t> &a2 = *_f.a2;
      uint64_t r_ = std::move(_result);
      _stack.emplace_back(_Cont2{r_});
      _stack.emplace_back(_Enter{UINT64_C(0), &a2});
    } else if (std::holds_alternative<_Cont2>(_frame)) {
      auto _f = std::move(std::get<_Cont2>(_frame));
      uint64_t r_ = _f.r_;
      uint64_t r_0 = std::move(_result);
      _result = (r_ + r_0);
    } else if (std::holds_alternative<_Cont3>(_frame)) {
      auto _f = std::move(std::get<_Cont3>(_frame));
      const LoopifyTrees::tree<uint64_t> &a2 = *_f.a2;
      uint64_t remaining = _f.remaining;
      uint64_t r_ = std::move(_result);
      _stack.emplace_back(_Cont4{r_});
      _stack.emplace_back(_Enter{remaining, &a2});
    } else {
      auto _f = std::move(std::get<_Cont4>(_frame));
      uint64_t r_ = _f.r_;
      uint64_t r_0 = std::move(_result);
      _result = (r_ + r_0);
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
  crane::small_vector<_Frame> _stack;
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
        _stack.emplace_back(_Cont_Node{a1, crane_raw(a2)});
        _stack.emplace_back(_Enter{crane_raw(a0)});
      }
    } else if (std::holds_alternative<_Cont_Node>(_frame)) {
      auto _f = std::move(std::get<_Cont_Node>(_frame));
      uint64_t a1 = _f.a1;
      const LoopifyTrees::tree<uint64_t> &a2 = *_f.a2;
      uint64_t lsum = std::move(_result);
      _stack.emplace_back(_Cont_Node_1{a1, lsum});
      _stack.emplace_back(_Enter{&a2});
    } else {
      auto _f = std::move(std::get<_Cont_Node_1>(_frame));
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
uint64_t LoopifyTrees::sum_rose_list_fuel(
    uint64_t fuel,
    const List<LoopifyTrees::rose>
        &cs) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<LoopifyTrees::rose> *cs;
    uint64_t fuel;
  };

  /// _Cont_RNode: saves [a00, a1, f], resumes after recursive call, then
  /// processes rest.
  struct _Cont_RNode {
    uint64_t a00;
    const List<LoopifyTrees::rose> *a1;
    uint64_t f;
  };

  /// _Cont_RNode_1: saves [a00, r_], resumes after recursive call, then
  /// processes rest.
  struct _Cont_RNode_1 {
    uint64_t a00;
    uint64_t r_;
  };

  using _Frame = std::variant<_Enter, _Cont_RNode, _Cont_RNode_1>;
  uint64_t _result{};
  crane::small_vector<_Frame> _stack;
  _stack.emplace_back(_Enter{&cs, fuel});
  /// Loopified sum_rose_list_fuel: _Enter -> _Cont_RNode -> _Cont_RNode_1.
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
          _stack.emplace_back(_Cont_RNode{a00, crane_raw(a1), f});
          _stack.emplace_back(_Enter{crane_raw(a10), f});
        }
      }
    } else if (std::holds_alternative<_Cont_RNode>(_frame)) {
      auto _f = std::move(std::get<_Cont_RNode>(_frame));
      uint64_t a00 = _f.a00;
      const List<LoopifyTrees::rose> &a1 = *_f.a1;
      uint64_t f = _f.f;
      uint64_t r_ = std::move(_result);
      _stack.emplace_back(_Cont_RNode_1{a00, r_});
      _stack.emplace_back(_Enter{&a1, f});
    } else {
      auto _f = std::move(std::get<_Cont_RNode_1>(_frame));
      uint64_t a00 = _f.a00;
      uint64_t r_ = _f.r_;
      uint64_t r_0 = std::move(_result);
      _result = (a00 + (r_ + r_0));
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

  /// _Cont_RNode: saves [a00, a1, f], resumes after recursive call, then
  /// processes rest.
  struct _Cont_RNode {
    uint64_t a00;
    const List<LoopifyTrees::rose> *a1;
    uint64_t f;
  };

  /// _Cont_RNode_1: saves [a00, r_], resumes after recursive call, then
  /// processes rest.
  struct _Cont_RNode_1 {
    uint64_t a00;
    List<uint64_t> r_;
  };

  using _Frame = std::variant<_Enter, _Cont_RNode, _Cont_RNode_1>;
  List<uint64_t> _result{};
  crane::small_vector<_Frame> _stack;
  _stack.emplace_back(_Enter{&cs, fuel});
  /// Loopified flatten_rose_list_fuel: _Enter -> _Cont_RNode -> _Cont_RNode_1.
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
          _stack.emplace_back(_Cont_RNode{a00, crane_raw(a1), f});
          _stack.emplace_back(_Enter{crane_raw(a10), f});
        }
      }
    } else if (std::holds_alternative<_Cont_RNode>(_frame)) {
      auto _f = std::move(std::get<_Cont_RNode>(_frame));
      uint64_t a00 = _f.a00;
      const List<LoopifyTrees::rose> &a1 = *_f.a1;
      uint64_t f = _f.f;
      List<uint64_t> r_ = std::move(_result);
      _stack.emplace_back(_Cont_RNode_1{a00, std::move(r_)});
      _stack.emplace_back(_Enter{&a1, f});
    } else {
      auto _f = std::move(std::get<_Cont_RNode_1>(_frame));
      uint64_t a00 = _f.a00;
      List<uint64_t> r_ = std::move(_f.r_);
      List<uint64_t> r_0 = std::move(_result);
      _result = List<uint64_t>::cons(a00, std::move(r_).app(std::move(r_0)));
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
  crane::small_vector<_Frame> _stack;
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
          _stack.emplace_back(_Cont_RNode{crane_raw(a1), f});
          _stack.emplace_back(_Enter{crane_raw(a10), f});
        }
      }
    } else if (std::holds_alternative<_Cont_RNode>(_frame)) {
      auto _f = std::move(std::get<_Cont_RNode>(_frame));
      const List<LoopifyTrees::rose> &a1 = *_f.a1;
      uint64_t f = _f.f;
      uint64_t d = (std::move(_result) + 1);
      _stack.emplace_back(_Cont_RNode_1{d});
      _stack.emplace_back(_Enter{&a1, f});
    } else {
      auto _f = std::move(std::get<_Cont_RNode_1>(_frame));
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
LoopifyTrees::tree<uint64_t> LoopifyTrees::tree_max(
    LoopifyTrees::tree<uint64_t> t1,
    LoopifyTrees::tree<uint64_t>
        t2) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    LoopifyTrees::tree<uint64_t> t2;
    LoopifyTrees::tree<uint64_t> t1;
  };

  /// _Cont_Node: saves [a2, a20, max_val], resumes after recursive call, then
  /// processes rest.
  struct _Cont_Node {
    std::shared_ptr<LoopifyTrees::tree<uint64_t>> a2;
    std::shared_ptr<LoopifyTrees::tree<uint64_t>> a20;
    uint64_t max_val;
  };

  /// _Resume_Node: saves [max_val, r_], resumes after recursive call with
  /// _result.
  struct _Resume_Node {
    uint64_t max_val;
    LoopifyTrees::tree<uint64_t> r_;
  };

  using _Frame = std::variant<_Enter, _Cont_Node, _Resume_Node>;
  LoopifyTrees::tree<uint64_t> _result{};
  crane::small_vector<_Frame> _stack;
  _stack.emplace_back(_Enter{std::move(t2), std::move(t1)});
  /// Loopified tree_max: _Enter -> _Cont_Node -> _Resume_Node.
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
          _stack.emplace_back(_Cont_Node{a2, a20, max_val});
          _stack.emplace_back(_Enter{*a00, *a0});
        }
      }
    } else if (std::holds_alternative<_Cont_Node>(_frame)) {
      auto _f = std::move(std::get<_Cont_Node>(_frame));
      std::shared_ptr<LoopifyTrees::tree<uint64_t>> a2 = std::move(_f.a2);
      std::shared_ptr<LoopifyTrees::tree<uint64_t>> a20 = std::move(_f.a20);
      uint64_t max_val = _f.max_val;
      LoopifyTrees::tree<uint64_t> r_ = std::move(_result);
      _stack.emplace_back(_Resume_Node{max_val, std::move(r_)});
      _stack.emplace_back(_Enter{*a20, *a2});
    } else {
      auto _f = std::move(std::get<_Resume_Node>(_frame));
      _result = tree<uint64_t>::node(std::move(_f.r_), _f.max_val,
                                     std::move(_result));
    }
  }
  return _result;
}

/// Helper: extract values from trees.
List<uint64_t> LoopifyTrees::extract_tree_values(
    const List<LoopifyTrees::tree<uint64_t>> &ts) {
  std::shared_ptr<List<uint64_t>> _head{};
  std::shared_ptr<List<uint64_t>> *_write = &_head;
  const List<LoopifyTrees::tree<uint64_t>> *_loop_ts = &ts;
  while (true) {
    if (std::holds_alternative<
            typename List<LoopifyTrees::tree<uint64_t>>::Nil>(_loop_ts->v())) {
      *_write = std::make_shared<List<uint64_t>>(List<uint64_t>::nil());
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
        const auto &[a00, a10, a20] =
            std::get<typename LoopifyTrees::tree<uint64_t>::Node>(a0.v());
        auto _cell = std::make_shared<List<uint64_t>>(
            typename List<uint64_t>::Cons(a10, nullptr));
        *_write = std::move(_cell);
        _write = &std::get<typename List<uint64_t>::Cons>((*_write)->v_mut()).l;
        _loop_ts = crane_raw(a1);
        continue;
      }
    }
  }
  return std::move(*_head);
}

/// Helper: extract children from trees.
List<LoopifyTrees::tree<uint64_t>> LoopifyTrees::extract_tree_children(
    const List<LoopifyTrees::tree<uint64_t>> &ts) {
  std::shared_ptr<List<LoopifyTrees::tree<uint64_t>>> _head{};
  std::shared_ptr<List<LoopifyTrees::tree<uint64_t>>> *_write = &_head;
  const List<LoopifyTrees::tree<uint64_t>> *_loop_ts = &ts;
  while (true) {
    if (std::holds_alternative<
            typename List<LoopifyTrees::tree<uint64_t>>::Nil>(_loop_ts->v())) {
      *_write = std::make_shared<List<LoopifyTrees::tree<uint64_t>>>(
          List<LoopifyTrees::tree<uint64_t>>::nil());
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
        const auto &[a00, a10, a20] =
            std::get<typename LoopifyTrees::tree<uint64_t>::Node>(a0.v());
        auto _cell = std::make_shared<List<LoopifyTrees::tree<uint64_t>>>(
            typename List<LoopifyTrees::tree<uint64_t>>::Cons(*a00, nullptr));
        auto _cell1 = std::make_shared<List<LoopifyTrees::tree<uint64_t>>>(
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
        _loop_ts = crane_raw(a1);
        continue;
      }
    }
  }
  return std::move(*_head);
}

/// tree_levels t returns list of lists, one per level (breadth-first).
List<List<uint64_t>> LoopifyTrees::tree_levels_fuel(
    uint64_t fuel, const List<LoopifyTrees::tree<uint64_t>> &trees) {
  std::shared_ptr<List<List<uint64_t>>> _head{};
  std::shared_ptr<List<List<uint64_t>>> *_write = &_head;
  List<LoopifyTrees::tree<uint64_t>> _loop_trees = trees;
  uint64_t _loop_fuel = std::move(fuel);
  while (true) {
    if (_loop_fuel <= 0) {
      *_write =
          std::make_shared<List<List<uint64_t>>>(List<List<uint64_t>>::nil());
      break;
    } else {
      uint64_t f = _loop_fuel - 1;
      List<uint64_t> values = extract_tree_values(_loop_trees);
      if (std::holds_alternative<typename List<uint64_t>::Nil>(
              values.v_mut())) {
        *_write =
            std::make_shared<List<List<uint64_t>>>(List<List<uint64_t>>::nil());
        break;
      } else {
        List<LoopifyTrees::tree<uint64_t>> children =
            extract_tree_children(_loop_trees);
        auto _cell = std::make_shared<List<List<uint64_t>>>(
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

List<List<uint64_t>>
LoopifyTrees::tree_levels(const LoopifyTrees::tree<uint64_t> &t) {
  return tree_levels_fuel(UINT64_C(100),
                          List<LoopifyTrees::tree<uint64_t>>::cons(
                              t, List<LoopifyTrees::tree<uint64_t>>::nil()));
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
  crane::small_vector<_Frame> _stack;
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
        _stack.emplace_back(_Cont_Node{a1, crane_raw(a2)});
        _stack.emplace_back(_Enter{crane_raw(a0)});
      }
    } else if (std::holds_alternative<_Cont_Node>(_frame)) {
      auto _f = std::move(std::get<_Cont_Node>(_frame));
      uint64_t a1 = _f.a1;
      const LoopifyTrees::tree<uint64_t> &a2 = *_f.a2;
      std::pair<uint64_t, uint64_t> r_ = std::move(_result);
      auto [lc, ls] = std::move(r_);
      _stack.emplace_back(_Cont_lc{a1, lc, ls});
      _stack.emplace_back(_Enter{&a2});
    } else {
      auto _f = std::move(std::get<_Cont_lc>(_frame));
      uint64_t a1 = _f.a1;
      uint64_t lc = _f.lc;
      uint64_t ls = _f.ls;
      std::pair<uint64_t, uint64_t> r_0 = std::move(_result);
      auto [rc, rs] = std::move(r_0);
      _result = std::make_pair(((lc + rc) + 1), (a1 + (ls + rs)));
    }
  }
  return _result;
}

/// Helper: append two lists of lists.
List<List<uint64_t>>
LoopifyTrees::append_list_lists(const List<List<uint64_t>> &l1,
                                List<List<uint64_t>> l2) {
  std::shared_ptr<List<List<uint64_t>>> _head{};
  std::shared_ptr<List<List<uint64_t>>> *_write = &_head;
  List<List<uint64_t>> _loop_l2 = std::move(l2);
  const List<List<uint64_t>> *_loop_l1 = &l1;
  while (true) {
    if (std::holds_alternative<typename List<List<uint64_t>>::Nil>(
            _loop_l1->v())) {
      *_write = std::make_shared<List<List<uint64_t>>>(std::move(_loop_l2));
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename List<List<uint64_t>>::Cons>(_loop_l1->v());
      auto _cell = std::make_shared<List<List<uint64_t>>>(
          typename List<List<uint64_t>>::Cons(a0, nullptr));
      *_write = std::move(_cell);
      _write =
          &std::get<typename List<List<uint64_t>>::Cons>((*_write)->v_mut()).l;
      _loop_l1 = crane_raw(a1);
      continue;
    }
  }
  return std::move(*_head);
}

/// Helper: prepend value to all lists in a list of lists.
List<List<uint64_t>>
LoopifyTrees::map_cons_to_all(uint64_t x, const List<List<uint64_t>> &lsts) {
  std::shared_ptr<List<List<uint64_t>>> _head{};
  std::shared_ptr<List<List<uint64_t>>> *_write = &_head;
  const List<List<uint64_t>> *_loop_lsts = &lsts;
  while (true) {
    if (std::holds_alternative<typename List<List<uint64_t>>::Nil>(
            _loop_lsts->v())) {
      *_write =
          std::make_shared<List<List<uint64_t>>>(List<List<uint64_t>>::nil());
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename List<List<uint64_t>>::Cons>(_loop_lsts->v());
      auto _cell = std::make_shared<List<List<uint64_t>>>(
          typename List<List<uint64_t>>::Cons(List<uint64_t>::cons(x, a0),
                                              nullptr));
      *_write = std::move(_cell);
      _write =
          &std::get<typename List<List<uint64_t>>::Cons>((*_write)->v_mut()).l;
      _loop_lsts = crane_raw(a1);
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

  /// _Cont_Node: saves [a1, a2], resumes after recursive call, then processes
  /// rest.
  struct _Cont_Node {
    uint64_t a1;
    const LoopifyTrees::tree<uint64_t> *a2;
  };

  /// _Cont_Node_1: saves [a1, r_], resumes after recursive call, then processes
  /// rest.
  struct _Cont_Node_1 {
    uint64_t a1;
    List<List<uint64_t>> r_;
  };

  using _Frame = std::variant<_Enter, _Cont_Node, _Cont_Node_1>;
  List<List<uint64_t>> _result{};
  crane::small_vector<_Frame> _stack;
  _stack.emplace_back(_Enter{&t});
  /// Loopified paths: _Enter -> _Cont_Node -> _Cont_Node_1.
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
        _stack.emplace_back(_Cont_Node{a1, crane_raw(a2)});
        _stack.emplace_back(_Enter{crane_raw(a0)});
      }
    } else if (std::holds_alternative<_Cont_Node>(_frame)) {
      auto _f = std::move(std::get<_Cont_Node>(_frame));
      uint64_t a1 = _f.a1;
      const LoopifyTrees::tree<uint64_t> &a2 = *_f.a2;
      List<List<uint64_t>> r_ = std::move(_result);
      _stack.emplace_back(_Cont_Node_1{a1, std::move(r_)});
      _stack.emplace_back(_Enter{&a2});
    } else {
      auto _f = std::move(std::get<_Cont_Node_1>(_frame));
      uint64_t a1 = _f.a1;
      List<List<uint64_t>> r_ = std::move(_f.r_);
      List<List<uint64_t>> r_0 = std::move(_result);
      _result = append_list_lists(map_cons_to_all(a1, std::move(r_)),
                                  map_cons_to_all(a1, std::move(r_0)));
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

  /// _Cont_Node: saves [a1, a2], resumes after recursive call, then processes
  /// rest.
  struct _Cont_Node {
    uint64_t a1;
    const LoopifyTrees::tree<uint64_t> *a2;
  };

  /// _Cont_Node_1: saves [a1, r_], resumes after recursive call, then processes
  /// rest.
  struct _Cont_Node_1 {
    uint64_t a1;
    List<uint64_t> r_;
  };

  using _Frame = std::variant<_Enter, _Cont_Node, _Cont_Node_1>;
  List<uint64_t> _result{};
  crane::small_vector<_Frame> _stack;
  _stack.emplace_back(_Enter{&t});
  /// Loopified collect_unsorted: _Enter -> _Cont_Node -> _Cont_Node_1.
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
        _stack.emplace_back(_Cont_Node{a1, crane_raw(a2)});
        _stack.emplace_back(_Enter{crane_raw(a0)});
      }
    } else if (std::holds_alternative<_Cont_Node>(_frame)) {
      auto _f = std::move(std::get<_Cont_Node>(_frame));
      uint64_t a1 = _f.a1;
      const LoopifyTrees::tree<uint64_t> &a2 = *_f.a2;
      List<uint64_t> r_ = std::move(_result);
      _stack.emplace_back(_Cont_Node_1{a1, std::move(r_)});
      _stack.emplace_back(_Enter{&a2});
    } else {
      auto _f = std::move(std::get<_Cont_Node_1>(_frame));
      uint64_t a1 = _f.a1;
      List<uint64_t> r_ = std::move(_f.r_);
      List<uint64_t> r_0 = std::move(_result);
      _result = std::move(r_).app(List<uint64_t>::cons(a1, std::move(r_0)));
    }
  }
  return _result;
}

/// Simple insertion sort for collect_sorted.
List<uint64_t> LoopifyTrees::insert_sorted(uint64_t x,
                                           const List<uint64_t> &l) {
  std::shared_ptr<List<uint64_t>> _head{};
  std::shared_ptr<List<uint64_t>> *_write = &_head;
  const List<uint64_t> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l->v())) {
      *_write = std::make_shared<List<uint64_t>>(
          List<uint64_t>::cons(x, List<uint64_t>::nil()));
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename List<uint64_t>::Cons>(_loop_l->v());
      if (x <= a0) {
        *_write = std::make_shared<List<uint64_t>>(
            List<uint64_t>::cons(x, List<uint64_t>::cons(a0, *a1)));
        break;
      } else {
        auto _cell = std::make_shared<List<uint64_t>>(
            typename List<uint64_t>::Cons(a0, nullptr));
        *_write = std::move(_cell);
        _write = &std::get<typename List<uint64_t>::Cons>((*_write)->v_mut()).l;
        _loop_l = crane_raw(a1);
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

  /// _Cont_Cons: saves [a0], resumes after recursive call, then processes rest.
  struct _Cont_Cons {
    uint64_t a0;
  };

  using _Frame = std::variant<_Enter, _Cont_Cons>;
  List<uint64_t> _result{};
  crane::small_vector<_Frame> _stack;
  _stack.emplace_back(_Enter{&l});
  /// Loopified sort_list: _Enter -> _Cont_Cons.
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
        _stack.emplace_back(_Cont_Cons{a0});
        _stack.emplace_back(_Enter{crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<_Cont_Cons>(_frame));
      uint64_t a0 = _f.a0;
      List<uint64_t> r_ = std::move(_result);
      _result = insert_sorted(a0, std::move(r_));
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
  crane::small_vector<_Frame> _stack;
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
        _stack.emplace_back(_Cont_Node{a1, crane_raw(a2)});
        _stack.emplace_back(_Enter{crane_raw(a0)});
      }
    } else if (std::holds_alternative<_Cont_Node>(_frame)) {
      auto _f = std::move(std::get<_Cont_Node>(_frame));
      uint64_t a1 = _f.a1;
      const LoopifyTrees::tree<uint64_t> &a2 = *_f.a2;
      std::pair<uint64_t, uint64_t> r_ = std::move(_result);
      auto [lmin, lmax] = std::move(r_);
      _stack.emplace_back(_Cont_lmin{a1, lmax, lmin});
      _stack.emplace_back(_Enter{&a2});
    } else {
      auto _f = std::move(std::get<_Cont_lmin>(_frame));
      uint64_t a1 = _f.a1;
      uint64_t lmax = _f.lmax;
      uint64_t lmin = _f.lmin;
      std::pair<uint64_t, uint64_t> r_0 = std::move(_result);
      auto [rmin, rmax] = std::move(r_0);
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
      [&](auto &, uint64_t acc,
          const LoopifyTrees::tree<uint64_t> &tree0) -> uint64_t {
    /// _Enter: captures varying parameters for each recursive call.
    struct _Enter {
      const LoopifyTrees::tree<uint64_t> *tree0;
      uint64_t acc;
    };
    /// _Cont_Node: saves [a2, new_acc], resumes after recursive call, then
    /// processes rest.
    struct _Cont_Node {
      const LoopifyTrees::tree<uint64_t> *a2;
      uint64_t new_acc;
    };
    /// _Cont_Node_1: saves [r_], resumes after recursive call, then processes
    /// rest.
    struct _Cont_Node_1 {
      uint64_t r_;
    };
    using _Frame = std::variant<_Enter, _Cont_Node, _Cont_Node_1>;
    uint64_t _result{};
    crane::small_vector<_Frame> _stack;
    _stack.emplace_back(_Enter{&tree0, acc});
    /// Loopified sum_with_acc: _Enter -> _Cont_Node -> _Cont_Node_1.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const LoopifyTrees::tree<uint64_t> &tree0 = *_f.tree0;
        uint64_t acc = _f.acc;
        if (std::holds_alternative<typename LoopifyTrees::tree<uint64_t>::Leaf>(
                tree0.v())) {
          _result = std::move(acc);
        } else {
          const auto &[a0, a1, a2] =
              std::get<typename LoopifyTrees::tree<uint64_t>::Node>(tree0.v());
          uint64_t new_acc = (acc + a1);
          _stack.emplace_back(_Cont_Node{crane_raw(a2), new_acc});
          _stack.emplace_back(_Enter{crane_raw(a0), new_acc});
        }
      } else if (std::holds_alternative<_Cont_Node>(_frame)) {
        auto _f = std::move(std::get<_Cont_Node>(_frame));
        const LoopifyTrees::tree<uint64_t> &a2 = *_f.a2;
        uint64_t new_acc = _f.new_acc;
        uint64_t r_ = std::move(_result);
        _stack.emplace_back(_Cont_Node_1{r_});
        _stack.emplace_back(_Enter{&a2, new_acc});
      } else {
        auto _f = std::move(std::get<_Cont_Node_1>(_frame));
        uint64_t r_ = _f.r_;
        uint64_t r_0 = std::move(_result);
        _result = (r_ + r_0);
      }
    }
    return _result;
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

  /// _Cont_Node: saves [a1, a2], resumes after recursive call, then processes
  /// rest.
  struct _Cont_Node {
    uint64_t a1;
    const LoopifyTrees::tree<uint64_t> *a2;
  };

  /// _Cont_Node_1: saves [a1, r_], resumes after recursive call, then processes
  /// rest.
  struct _Cont_Node_1 {
    uint64_t a1;
    bool r_;
  };

  using _Frame = std::variant<_Enter, _Cont_Node, _Cont_Node_1>;
  bool _result{};
  crane::small_vector<_Frame> _stack;
  _stack.emplace_back(_Enter{&t});
  /// Loopified tree_contains: _Enter -> _Cont_Node -> _Cont_Node_1.
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
        _stack.emplace_back(_Cont_Node{a1, crane_raw(a2)});
        _stack.emplace_back(_Enter{crane_raw(a0)});
      }
    } else if (std::holds_alternative<_Cont_Node>(_frame)) {
      auto _f = std::move(std::get<_Cont_Node>(_frame));
      uint64_t a1 = _f.a1;
      const LoopifyTrees::tree<uint64_t> &a2 = *_f.a2;
      bool r_ = std::move(_result);
      _stack.emplace_back(_Cont_Node_1{a1, r_});
      _stack.emplace_back(_Enter{&a2});
    } else {
      auto _f = std::move(std::get<_Cont_Node_1>(_frame));
      uint64_t a1 = _f.a1;
      bool r_ = _f.r_;
      bool r_0 = std::move(_result);
      _result = (x == a1 || (r_ || r_0));
    }
  }
  return _result;
}
