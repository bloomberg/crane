#include "mem_safety_probe27.h"

uint64_t MemSafetyProbe27::tree_sum(
    const MemSafetyProbe27::tree
        &t) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const MemSafetyProbe27::tree *t;
  };

  /// _Cont_Node: saves [a1, a2], resumes after recursive call, then processes
  /// rest.
  struct _Cont_Node {
    uint64_t a1;
    const MemSafetyProbe27::tree *a2;
  };

  /// _Cont_Node_1: saves [_tmp2, a1], resumes after recursive call, then
  /// processes rest.
  struct _Cont_Node_1 {
    uint64_t _tmp2;
    uint64_t a1;
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
      const MemSafetyProbe27::tree &t = *_f.t;
      if (std::holds_alternative<typename MemSafetyProbe27::tree::Leaf>(
              t.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1, a2] =
            std::get<typename MemSafetyProbe27::tree::Node>(t.v());
        _stack.emplace_back(_Cont_Node{a1, crane_raw(a2)});
        _stack.emplace_back(_Enter{crane_raw(a0)});
      }
    } else if (std::holds_alternative<_Cont_Node>(_frame)) {
      auto _f = std::move(std::get<_Cont_Node>(_frame));
      uint64_t a1 = _f.a1;
      const MemSafetyProbe27::tree &a2 = *_f.a2;
      _stack.emplace_back(_Cont_Node_1{std::move(_result), a1});
      _stack.emplace_back(_Enter{&a2});
    } else {
      auto _f = std::move(std::get<_Cont_Node_1>(_frame));
      uint64_t a1 = _f.a1;
      _result = ((_f._tmp2 + a1) + std::move(_result));
    }
  }
  return _result;
}

uint64_t MemSafetyProbe27::tree_depth(
    const MemSafetyProbe27::tree
        &t) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const MemSafetyProbe27::tree *t;
  };

  /// _Cont_Node: saves [a2], resumes after recursive call, then processes rest.
  struct _Cont_Node {
    const MemSafetyProbe27::tree *a2;
  };

  /// _Cont_Node_1: saves [_tmp2], resumes after recursive call, then processes
  /// rest.
  struct _Cont_Node_1 {
    uint64_t _tmp2;
  };

  using _Frame = std::variant<_Enter, _Cont_Node, _Cont_Node_1>;
  uint64_t _result{};
  crane::small_vector<_Frame> _stack;
  _stack.emplace_back(_Enter{&t});
  /// Loopified tree_depth: _Enter -> _Cont_Node -> _Cont_Node_1.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const MemSafetyProbe27::tree &t = *_f.t;
      if (std::holds_alternative<typename MemSafetyProbe27::tree::Leaf>(
              t.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1, a2] =
            std::get<typename MemSafetyProbe27::tree::Node>(t.v());
        _stack.emplace_back(_Cont_Node{crane_raw(a2)});
        _stack.emplace_back(_Enter{crane_raw(a0)});
      }
    } else if (std::holds_alternative<_Cont_Node>(_frame)) {
      auto _f = std::move(std::get<_Cont_Node>(_frame));
      const MemSafetyProbe27::tree &a2 = *_f.a2;
      _stack.emplace_back(_Cont_Node_1{std::move(_result)});
      _stack.emplace_back(_Enter{&a2});
    } else {
      auto _f = std::move(std::get<_Cont_Node_1>(_frame));
      _result = (UINT64_C(1) + std::max(_f._tmp2, std::move(_result)));
    }
  }
  return _result;
}

/// TEST 1: Pair containing closure that captures whole tree.
/// No match on t — just direct capture. Tests whether Crane
/// creates a clone of t for the closure.
std::pair<crane::fn<uint64_t(uint64_t)>, uint64_t>
MemSafetyProbe27::pair_with_fn(MemSafetyProbe27::tree t) {
  return std::make_pair([=](uint64_t x) { return (x + tree_sum(t)); },
                        tree_sum(t));
}

/// TEST 2: if/else returning different closures in a pair.
/// After IIFE inlining, this becomes a top-level Sif.
/// return_captures_by_value may not process inner returns.
std::pair<crane::fn<uint64_t(uint64_t)>, uint64_t>
MemSafetyProbe27::cond_pair_fn(MemSafetyProbe27::tree t, bool b) {
  if (b) {
    return std::make_pair([=](uint64_t x) { return (x + tree_sum(t)); },
                          UINT64_C(1));
  } else {
    return std::make_pair([=](uint64_t x) { return (x + tree_depth(t)); },
                          UINT64_C(2));
  }
}

/// TEST 3: Closure capturing TWO tree parameters.
std::pair<crane::fn<uint64_t(uint64_t)>, uint64_t>
MemSafetyProbe27::pair_two_trees(MemSafetyProbe27::tree t1,
                                 MemSafetyProbe27::tree t2) {
  return std::make_pair(
      [=](uint64_t x) { return ((x + tree_sum(t1)) + tree_sum(t2)); },
      tree_sum(t1));
}

/// TEST 4: Closure stored in option (no match on tree).
std::optional<crane::fn<uint64_t(uint64_t)>>
MemSafetyProbe27::opt_tree_fn(MemSafetyProbe27::tree t, bool b) {
  if (b) {
    return std::make_optional<crane::fn<uint64_t(uint64_t)>>(
        [=](uint64_t x) { return (x + tree_sum(t)); });
  } else {
    return std::optional<crane::fn<uint64_t(uint64_t)>>();
  }
}

/// TEST 5: Nested closures — inner captures tree, outer captures inner.
/// Tests that the inner closure correctly clones the tree.
std::pair<crane::fn<uint64_t(uint64_t)>, uint64_t>
MemSafetyProbe27::nested_closure_pair(MemSafetyProbe27::tree t) {
  crane::fn<uint64_t(uint64_t)> f = [=](uint64_t x) {
    return (x + tree_sum(t));
  };
  return std::make_pair([=](uint64_t x) { return f(f(x)); },
                        tree_sum(std::move(t)));
}

/// TEST 6: Three closures stored in a triple, each using tree differently.
std::pair<
    std::pair<crane::fn<uint64_t(uint64_t)>, crane::fn<uint64_t(uint64_t)>>,
    uint64_t>
MemSafetyProbe27::triple_fns(MemSafetyProbe27::tree t) {
  return std::make_pair(
      std::make_pair([=](uint64_t x) { return (x + tree_sum(t)); },
                     [=](uint64_t x) { return (x + tree_depth(t)); }),
      (tree_sum(t) + tree_depth(t)));
}

/// TEST 7: Closure and tree value stored together in a pair.
/// Tests whether the closure's capture and the tree return
/// are independent clones.
std::pair<crane::fn<uint64_t(uint64_t)>, MemSafetyProbe27::tree>
MemSafetyProbe27::fn_and_tree(MemSafetyProbe27::tree t) {
  return std::make_pair([=](uint64_t x) { return (x + tree_sum(t)); }, t);
}

/// TEST 8: Closure captures tree, stored in option inside a pair.
/// Multiple levels of wrapping.
std::pair<std::optional<crane::fn<uint64_t(uint64_t)>>, uint64_t>
MemSafetyProbe27::wrapped_fn(MemSafetyProbe27::tree t, bool b) {
  return std::make_pair((b ? std::make_optional<crane::fn<uint64_t(uint64_t)>>(
                                 [=](uint64_t x) { return (x + tree_sum(t)); })
                           : std::optional<crane::fn<uint64_t(uint64_t)>>()),
                        tree_sum(t));
}
