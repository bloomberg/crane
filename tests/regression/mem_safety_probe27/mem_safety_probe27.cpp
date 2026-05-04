#include <mem_safety_probe27.h>

unsigned int MemSafetyProbe27::tree_sum(
    const MemSafetyProbe27::tree
        &t) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const MemSafetyProbe27::tree *t;
  };

  /// _After_Node: saves [d_a0, d_a1], dispatches next recursive call.
  struct _After_Node {
    const MemSafetyProbe27::tree *d_a0;
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
      const MemSafetyProbe27::tree &t = *(_f.t);
      if (std::holds_alternative<typename MemSafetyProbe27::tree::Leaf>(
              t.v())) {
        _result = 0u;
      } else {
        const auto &[d_a0, d_a1, d_a2] =
            std::get<typename MemSafetyProbe27::tree::Node>(t.v());
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

unsigned int MemSafetyProbe27::tree_depth(
    const MemSafetyProbe27::tree
        &t) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const MemSafetyProbe27::tree *t;
  };

  /// _After_Node: saves [d_a0, _s1], dispatches next recursive call.
  struct _After_Node {
    const MemSafetyProbe27::tree *d_a0;
    decltype(1u) _s1;
  };

  /// _Combine_Node: receives partial results, combines with _result from final
  /// call.
  struct _Combine_Node {
    unsigned int _result;
    decltype(1u) _s1;
  };

  using _Frame = std::variant<_Enter, _After_Node, _Combine_Node>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&t});
  /// Loopified tree_depth: _Enter -> _After_Node -> _Combine_Node.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const MemSafetyProbe27::tree &t = *(_f.t);
      if (std::holds_alternative<typename MemSafetyProbe27::tree::Leaf>(
              t.v())) {
        _result = 0u;
      } else {
        const auto &[d_a0, d_a1, d_a2] =
            std::get<typename MemSafetyProbe27::tree::Node>(t.v());
        _stack.emplace_back(_After_Node{d_a0.get(), 1u});
        _stack.emplace_back(_Enter{d_a2.get()});
      }
    } else if (std::holds_alternative<_After_Node>(_frame)) {
      auto _f = std::move(std::get<_After_Node>(_frame));
      _stack.emplace_back(_Combine_Node{_result, _f._s1});
      _stack.emplace_back(_Enter{_f.d_a0});
    } else {
      auto _f = std::move(std::get<_Combine_Node>(_frame));
      _result = (_f._s1 + std::max(_result, _f._result));
    }
  }
  return _result;
}

/// TEST 1: Pair containing closure that captures whole tree.
/// No match on t — just direct capture. Tests whether Crane
/// creates a clone of t for the closure.
std::pair<std::function<unsigned int(unsigned int)>, unsigned int>
MemSafetyProbe27::pair_with_fn(MemSafetyProbe27::tree t) {
  return std::make_pair(
      [=](const unsigned int x) mutable { return (x + tree_sum(t)); },
      tree_sum(t));
}

/// TEST 2: if/else returning different closures in a pair.
/// After IIFE inlining, this becomes a top-level Sif.
/// return_captures_by_value may not process inner returns.
std::pair<std::function<unsigned int(unsigned int)>, unsigned int>
MemSafetyProbe27::cond_pair_fn(MemSafetyProbe27::tree t, const bool b) {
  if (b) {
    return std::make_pair(
        [=](const unsigned int x) mutable { return (x + tree_sum(t)); }, 1u);
  } else {
    return std::make_pair(
        [=](const unsigned int x) mutable { return (x + tree_depth(t)); }, 2u);
  }
}

/// TEST 3: Closure capturing TWO tree parameters.
std::pair<std::function<unsigned int(unsigned int)>, unsigned int>
MemSafetyProbe27::pair_two_trees(MemSafetyProbe27::tree t1,
                                 MemSafetyProbe27::tree t2) {
  return std::make_pair(
      [=](const unsigned int x) mutable {
        return ((x + tree_sum(t1)) + tree_sum(t2));
      },
      tree_sum(t1));
}

/// TEST 4: Closure stored in option (no match on tree).
std::optional<std::function<unsigned int(unsigned int)>>
MemSafetyProbe27::opt_tree_fn(MemSafetyProbe27::tree t, const bool b) {
  if (b) {
    return std::make_optional<std::function<unsigned int(unsigned int)>>(
        [=](const unsigned int x) mutable { return (x + tree_sum(t)); });
  } else {
    return std::optional<std::function<unsigned int(unsigned int)>>();
  }
}

/// TEST 5: Nested closures — inner captures tree, outer captures inner.
/// Tests that the inner closure correctly clones the tree.
std::pair<std::function<unsigned int(unsigned int)>, unsigned int>
MemSafetyProbe27::nested_closure_pair(MemSafetyProbe27::tree t) {
  std::function<unsigned int(unsigned int)> f =
      [=](const unsigned int x) mutable { return (x + tree_sum(t)); };
  return std::make_pair([=](const unsigned int x) mutable { return f(f(x)); },
                        tree_sum(std::move(t)));
}

/// TEST 6: Three closures stored in a triple, each using tree differently.
std::pair<std::pair<std::function<unsigned int(unsigned int)>,
                    std::function<unsigned int(unsigned int)>>,
          unsigned int>
MemSafetyProbe27::triple_fns(MemSafetyProbe27::tree t) {
  return std::make_pair(
      std::make_pair(
          [=](const unsigned int x) mutable { return (x + tree_sum(t)); },
          [=](const unsigned int x) mutable { return (x + tree_depth(t)); }),
      (tree_sum(t) + tree_depth(t)));
}

/// TEST 7: Closure and tree value stored together in a pair.
/// Tests whether the closure's capture and the tree return
/// are independent clones.
std::pair<std::function<unsigned int(unsigned int)>, MemSafetyProbe27::tree>
MemSafetyProbe27::fn_and_tree(MemSafetyProbe27::tree t) {
  return std::make_pair(
      [=](const unsigned int x) mutable { return (x + tree_sum(t)); }, t);
}

/// TEST 8: Closure captures tree, stored in option inside a pair.
/// Multiple levels of wrapping.
std::pair<std::optional<std::function<unsigned int(unsigned int)>>,
          unsigned int>
MemSafetyProbe27::wrapped_fn(MemSafetyProbe27::tree t, const bool b) {
  return std::make_pair(
      (b ? std::make_optional<std::function<unsigned int(unsigned int)>>(
               [=](const unsigned int x) mutable { return (x + tree_sum(t)); })
         : std::optional<std::function<unsigned int(unsigned int)>>()),
      tree_sum(t));
}
