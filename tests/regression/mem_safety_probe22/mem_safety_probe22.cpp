#include "mem_safety_probe22.h"

unsigned int MemSafetyProbe22::tree_sum(
    const MemSafetyProbe22::tree
        &t) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const MemSafetyProbe22::tree *t;
  };

  /// _After_Node: saves [d_a0, d_a1], dispatches next recursive call.
  struct _After_Node {
    const MemSafetyProbe22::tree *d_a0;
    unsigned int d_a1;
  };

  /// _Combine_Node: receives partial results, combines with _result from final
  /// call.
  struct _Combine_Node {
    unsigned int _result;
    unsigned int d_a1;
  };

  using _Frame = std::variant<_Enter, _After_Node, _Combine_Node>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&t});
  /// Loopified tree_sum: _Enter -> _After_Node -> _Combine_Node.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const MemSafetyProbe22::tree &t = *(_f.t);
      if (std::holds_alternative<typename MemSafetyProbe22::tree::Leaf>(
              t.v())) {
        _result = 0u;
      } else {
        const auto &[d_a0, d_a1, d_a2] =
            std::get<typename MemSafetyProbe22::tree::Node>(t.v());
        _stack.emplace_back(_After_Node{d_a0.get(), d_a1});
        _stack.emplace_back(_Enter{d_a2.get()});
      }
    } else if (std::holds_alternative<_After_Node>(_frame)) {
      auto _f = std::move(std::get<_After_Node>(_frame));
      _stack.emplace_back(_Combine_Node{_result, _f.d_a1});
      _stack.emplace_back(_Enter{_f.d_a0});
    } else {
      auto _f = std::move(std::get<_Combine_Node>(_frame));
      _result = ((_result + _f.d_a1) + _f._result);
    }
  }
  return _result;
}

/// TEST 1: Two recursive calls on CHILDREN, but the
/// function takes tree by value because it also returns/stores it.
std::pair<MemSafetyProbe22::tree, unsigned int>
MemSafetyProbe22::sum_and_rebuild(const MemSafetyProbe22::tree &t) {
  if (std::holds_alternative<typename MemSafetyProbe22::tree::Leaf>(t.v())) {
    return std::make_pair(tree::leaf(), 0u);
  } else {
    const auto &[d_a0, d_a1, d_a2] =
        std::get<typename MemSafetyProbe22::tree::Node>(t.v());
    std::pair<MemSafetyProbe22::tree, unsigned int> pl =
        sum_and_rebuild(*(d_a0));
    std::pair<MemSafetyProbe22::tree, unsigned int> pr =
        sum_and_rebuild(*(d_a2));
    return std::make_pair(tree::node(pl.first, d_a1, pr.first),
                          ((pl.second + d_a1) + pr.second));
  }
}

/// TEST 2: Function that recurses on children AND stores result
/// in constructor, forcing the tree to be owned.
MemSafetyProbe22::tree MemSafetyProbe22::double_tree(
    const MemSafetyProbe22::tree
        &t) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const MemSafetyProbe22::tree *t;
  };

  /// _After_Node: saves [d_a0, _s1], dispatches next recursive call.
  struct _After_Node {
    const MemSafetyProbe22::tree *d_a0;
    unsigned int _s1;
  };

  /// _Combine_Node: receives partial results, combines with _result from final
  /// call.
  struct _Combine_Node {
    MemSafetyProbe22::tree _result;
    unsigned int _s1;
  };

  using _Frame = std::variant<_Enter, _After_Node, _Combine_Node>;
  MemSafetyProbe22::tree _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&t});
  /// Loopified double_tree: _Enter -> _After_Node -> _Combine_Node.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const MemSafetyProbe22::tree &t = *(_f.t);
      if (std::holds_alternative<typename MemSafetyProbe22::tree::Leaf>(
              t.v())) {
        _result = tree::leaf();
      } else {
        const auto &[d_a0, d_a1, d_a2] =
            std::get<typename MemSafetyProbe22::tree::Node>(t.v());
        _stack.emplace_back(_After_Node{d_a0.get(), (d_a1 * 2u)});
        _stack.emplace_back(_Enter{d_a2.get()});
      }
    } else if (std::holds_alternative<_After_Node>(_frame)) {
      auto _f = std::move(std::get<_After_Node>(_frame));
      _stack.emplace_back(_Combine_Node{std::move(_result), _f._s1});
      _stack.emplace_back(_Enter{_f.d_a0});
    } else {
      auto _f = std::move(std::get<_Combine_Node>(_frame));
      _result = tree::node(_result, _f._s1, _f._result);
    }
  }
  return _result;
}

/// TEST 3: Two recursive calls with child + value in result.
unsigned int MemSafetyProbe22::weighted_sum(
    const MemSafetyProbe22::tree &t,
    const unsigned int
        w) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    unsigned int w;
    const MemSafetyProbe22::tree *t;
  };

  /// _After_Node: saves [_s0, d_a0, _s2], dispatches next recursive call.
  struct _After_Node {
    unsigned int _s0;
    const MemSafetyProbe22::tree *d_a0;
    unsigned int _s2;
  };

  /// _Combine_Node: receives partial results, combines with _result from final
  /// call.
  struct _Combine_Node {
    unsigned int _result;
    unsigned int _s1;
  };

  using _Frame = std::variant<_Enter, _After_Node, _Combine_Node>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{w, &t});
  /// Loopified weighted_sum: _Enter -> _After_Node -> _Combine_Node.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const unsigned int w = _f.w;
      const MemSafetyProbe22::tree &t = *(_f.t);
      if (std::holds_alternative<typename MemSafetyProbe22::tree::Leaf>(
              t.v())) {
        _result = 0u;
      } else {
        const auto &[d_a0, d_a1, d_a2] =
            std::get<typename MemSafetyProbe22::tree::Node>(t.v());
        _stack.emplace_back(_After_Node{(w + 1u), d_a0.get(), (d_a1 * w)});
        _stack.emplace_back(_Enter{(w + 1u), d_a2.get()});
      }
    } else if (std::holds_alternative<_After_Node>(_frame)) {
      auto _f = std::move(std::get<_After_Node>(_frame));
      _stack.emplace_back(_Combine_Node{_result, _f._s2});
      _stack.emplace_back(_Enter{_f._s0, _f.d_a0});
    } else {
      auto _f = std::move(std::get<_Combine_Node>(_frame));
      _result = ((_result + _f._s1) + _f._result);
    }
  }
  return _result;
}

/// TEST 4: Function with constructed-tree recursive calls.
unsigned int MemSafetyProbe22::split_sum(
    const MemSafetyProbe22::tree &t,
    const unsigned int
        n) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    unsigned int n;
    MemSafetyProbe22::tree t;
  };

  /// _After_Node: saves [n_, _s1], dispatches next recursive call.
  struct _After_Node {
    unsigned int n_;
    decltype(tree::node(
        *(std::declval<std::unique_ptr<MemSafetyProbe22::tree> &>()),
        (std::declval<unsigned int &>() + 1u), tree::leaf())) _s1;
  };

  /// _Combine_Node: receives partial results, combines with _result from final
  /// call.
  struct _Combine_Node {
    unsigned int _result;
  };

  using _Frame = std::variant<_Enter, _After_Node, _Combine_Node>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{n, t});
  /// Loopified split_sum: _Enter -> _After_Node -> _Combine_Node.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const unsigned int n = _f.n;
      const MemSafetyProbe22::tree &t = _f.t;
      if (n <= 0) {
        _result = tree_sum(t);
      } else {
        unsigned int n_ = n - 1;
        if (std::holds_alternative<typename MemSafetyProbe22::tree::Leaf>(
                t.v())) {
          _result = 0u;
        } else {
          const auto &[d_a0, d_a1, d_a2] =
              std::get<typename MemSafetyProbe22::tree::Node>(t.v());
          _stack.emplace_back(
              _After_Node{n_, tree::node(*(d_a0), (d_a1 + 1u), tree::leaf())});
          _stack.emplace_back(
              _Enter{n_, tree::node(tree::leaf(), (d_a1 + 1u), *(d_a2))});
        }
      }
    } else if (std::holds_alternative<_After_Node>(_frame)) {
      auto _f = std::move(std::get<_After_Node>(_frame));
      _stack.emplace_back(_Combine_Node{_result});
      _stack.emplace_back(_Enter{_f.n_, std::move(_f._s1)});
    } else {
      auto _f = std::move(std::get<_Combine_Node>(_frame));
      _result = (_result + _f._result);
    }
  }
  return _result;
}

/// TEST 6: Mirror tree (swap children). Two recursive calls.
MemSafetyProbe22::tree MemSafetyProbe22::mirror(
    const MemSafetyProbe22::tree
        &t) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const MemSafetyProbe22::tree *t;
  };

  /// _After_Node: saves [d_a2, d_a1], dispatches next recursive call.
  struct _After_Node {
    const MemSafetyProbe22::tree *d_a2;
    unsigned int d_a1;
  };

  /// _Combine_Node: receives partial results, combines with _result from final
  /// call.
  struct _Combine_Node {
    MemSafetyProbe22::tree _result;
    unsigned int d_a1;
  };

  using _Frame = std::variant<_Enter, _After_Node, _Combine_Node>;
  MemSafetyProbe22::tree _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&t});
  /// Loopified mirror: _Enter -> _After_Node -> _Combine_Node.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const MemSafetyProbe22::tree &t = *(_f.t);
      if (std::holds_alternative<typename MemSafetyProbe22::tree::Leaf>(
              t.v())) {
        _result = tree::leaf();
      } else {
        const auto &[d_a0, d_a1, d_a2] =
            std::get<typename MemSafetyProbe22::tree::Node>(t.v());
        _stack.emplace_back(_After_Node{d_a2.get(), d_a1});
        _stack.emplace_back(_Enter{d_a0.get()});
      }
    } else if (std::holds_alternative<_After_Node>(_frame)) {
      auto _f = std::move(std::get<_After_Node>(_frame));
      _stack.emplace_back(_Combine_Node{std::move(_result), _f.d_a1});
      _stack.emplace_back(_Enter{_f.d_a2});
    } else {
      auto _f = std::move(std::get<_Combine_Node>(_frame));
      _result = tree::node(_result, _f.d_a1, _f._result);
    }
  }
  return _result;
}

/// TEST 7: Insert into BST (non-pointer-safe because constructed tree
/// in recursive call).
MemSafetyProbe22::tree MemSafetyProbe22::insert(
    const MemSafetyProbe22::tree &t,
    const unsigned int
        x) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const MemSafetyProbe22::tree *t;
  };

  /// _Resume1: saves [d_a2, d_a1], resumes after recursive call with _result.
  struct _Resume1 {
    MemSafetyProbe22::tree d_a2;
    unsigned int d_a1;
  };

  /// _Resume2: saves [d_a1, d_a0], resumes after recursive call with _result.
  struct _Resume2 {
    unsigned int d_a1;
    MemSafetyProbe22::tree d_a0;
  };

  using _Frame = std::variant<_Enter, _Resume1, _Resume2>;
  MemSafetyProbe22::tree _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&t});
  /// Loopified insert: _Enter -> _Resume1 -> _Resume2.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const MemSafetyProbe22::tree &t = *(_f.t);
      if (std::holds_alternative<typename MemSafetyProbe22::tree::Leaf>(
              t.v())) {
        _result = tree::node(tree::leaf(), x, tree::leaf());
      } else {
        const auto &[d_a0, d_a1, d_a2] =
            std::get<typename MemSafetyProbe22::tree::Node>(t.v());
        if (x <= d_a1) {
          _stack.emplace_back(_Resume1{*(d_a2), d_a1});
          _stack.emplace_back(_Enter{d_a0.get()});
        } else {
          _stack.emplace_back(_Resume2{d_a1, *(d_a0)});
          _stack.emplace_back(_Enter{d_a2.get()});
        }
      }
    } else if (std::holds_alternative<_Resume1>(_frame)) {
      auto _f = std::move(std::get<_Resume1>(_frame));
      _result = tree::node(_result, _f.d_a1, _f.d_a2);
    } else {
      auto _f = std::move(std::get<_Resume2>(_frame));
      _result = tree::node(_f.d_a0, _f.d_a1, _result);
    }
  }
  return _result;
}

MemSafetyProbe22::tree
MemSafetyProbe22::insert_all(MemSafetyProbe22::tree t,
                             const List<unsigned int> &xs) {
  MemSafetyProbe22::tree _result;
  const List<unsigned int> *_loop_xs = &xs;
  MemSafetyProbe22::tree _loop_t = std::move(t);
  while (true) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(
            _loop_xs->v())) {
      _result = std::move(_loop_t);
      break;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<unsigned int>::Cons>(_loop_xs->v());
      _loop_xs = d_a1.get();
      _loop_t = insert(std::move(_loop_t), d_a0);
    }
  }
  return _result;
}

/// TEST 8: Deep tree transformation with two recursive calls.
MemSafetyProbe22::tree MemSafetyProbe22::label_depth(
    const MemSafetyProbe22::tree &t,
    const unsigned int
        d) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    unsigned int d;
    const MemSafetyProbe22::tree *t;
  };

  /// _After_Node: saves [_s0, d_a0, _s2], dispatches next recursive call.
  struct _After_Node {
    unsigned int _s0;
    const MemSafetyProbe22::tree *d_a0;
    unsigned int _s2;
  };

  /// _Combine_Node: receives partial results, combines with _result from final
  /// call.
  struct _Combine_Node {
    MemSafetyProbe22::tree _result;
    unsigned int _s1;
  };

  using _Frame = std::variant<_Enter, _After_Node, _Combine_Node>;
  MemSafetyProbe22::tree _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{d, &t});
  /// Loopified label_depth: _Enter -> _After_Node -> _Combine_Node.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const unsigned int d = _f.d;
      const MemSafetyProbe22::tree &t = *(_f.t);
      if (std::holds_alternative<typename MemSafetyProbe22::tree::Leaf>(
              t.v())) {
        _result = tree::leaf();
      } else {
        const auto &[d_a0, d_a1, d_a2] =
            std::get<typename MemSafetyProbe22::tree::Node>(t.v());
        _stack.emplace_back(_After_Node{(d + 1u), d_a0.get(), (d_a1 + d)});
        _stack.emplace_back(_Enter{(d + 1u), d_a2.get()});
      }
    } else if (std::holds_alternative<_After_Node>(_frame)) {
      auto _f = std::move(std::get<_After_Node>(_frame));
      _stack.emplace_back(_Combine_Node{std::move(_result), _f._s2});
      _stack.emplace_back(_Enter{_f._s0, _f.d_a0});
    } else {
      auto _f = std::move(std::get<_Combine_Node>(_frame));
      _result = tree::node(_result, _f._s1, _f._result);
    }
  }
  return _result;
}
