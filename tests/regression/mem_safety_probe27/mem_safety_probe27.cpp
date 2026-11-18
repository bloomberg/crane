#include "mem_safety_probe27.h"

uint64_t MemSafetyProbe27::tree_sum(const MemSafetyProbe27::tree &t) {
  // Explicit stack replaces the non-tail recursion of tree_sum: _call frames
  // are pending calls, _after frames resume a caller.
  struct _call {
    const MemSafetyProbe27::tree *t;
  };

  struct _after_tree_sum_in_Node {
    uint64_t a1;
    const MemSafetyProbe27::tree *a2;
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
      const MemSafetyProbe27::tree &t = *_f.t;
      if (std::holds_alternative<typename MemSafetyProbe27::tree::Leaf>(t.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1, a2] =
            std::get<typename MemSafetyProbe27::tree::Node>(t.v());
        _stack.emplace_back(_after_tree_sum_in_Node{a1, crane_raw(a2)});
        _stack.emplace_back(_call{crane_raw(a0)});
      }
    } else if (std::holds_alternative<_after_tree_sum_in_Node>(_popped)) {
      auto _f = std::move(std::get<_after_tree_sum_in_Node>(_popped));
      _stack.pop_back();
      uint64_t a1 = _f.a1;
      const MemSafetyProbe27::tree &a2 = *_f.a2;
      _stack.emplace_back(_after_tree_sum_in_Node_2{a1, std::move(_result)});
      _stack.emplace_back(_call{&a2});
    } else {
      auto _f = std::move(std::get<_after_tree_sum_in_Node_2>(_popped));
      _stack.pop_back();
      uint64_t a1 = _f.a1;
      _result = ((_f._tmp2 + a1) + std::move(_result));
    }
  }
  return _result;
}

uint64_t MemSafetyProbe27::tree_depth(const MemSafetyProbe27::tree &t) {
  // Explicit stack replaces the non-tail recursion of tree_depth: _call frames
  // are pending calls, _after frames resume a caller.
  struct _call {
    const MemSafetyProbe27::tree *t;
  };

  struct _after_tree_depth_in_Node {
    const MemSafetyProbe27::tree *a2;
  };

  struct _after_tree_depth_in_Node_2 {
    uint64_t _tmp2;
  };

  using _frame = std::variant<_call, _after_tree_depth_in_Node,
                              _after_tree_depth_in_Node_2>;
  uint64_t _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&t});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const MemSafetyProbe27::tree &t = *_f.t;
      if (std::holds_alternative<typename MemSafetyProbe27::tree::Leaf>(t.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, _, a2] =
            std::get<typename MemSafetyProbe27::tree::Node>(t.v());
        _stack.emplace_back(_after_tree_depth_in_Node{crane_raw(a2)});
        _stack.emplace_back(_call{crane_raw(a0)});
      }
    } else if (std::holds_alternative<_after_tree_depth_in_Node>(_popped)) {
      auto _f = std::move(std::get<_after_tree_depth_in_Node>(_popped));
      _stack.pop_back();
      const MemSafetyProbe27::tree &a2 = *_f.a2;
      _stack.emplace_back(_after_tree_depth_in_Node_2{std::move(_result)});
      _stack.emplace_back(_call{&a2});
    } else {
      auto _f = std::move(std::get<_after_tree_depth_in_Node_2>(_popped));
      _stack.pop_back();
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
  return std::make_pair(
      crane::fn([=](uint64_t x) { return (x + tree_sum(t)); }), tree_sum(t));
}

/// TEST 2: if/else returning different closures in a pair.
/// After IIFE inlining, this becomes a top-level Sif.
/// return_captures_by_value may not process inner returns.
std::pair<crane::fn<uint64_t(uint64_t)>, uint64_t>
MemSafetyProbe27::cond_pair_fn(MemSafetyProbe27::tree t, bool b) {
  if (b) {
    return std::make_pair(crane::fn(
        [=, t = std::move(t)](uint64_t x) { return (x + tree_sum(t)); }),
                          UINT64_C(1));
  } else {
    return std::make_pair(crane::fn(
        [=, t = std::move(t)](uint64_t x) { return (x + tree_depth(t)); }),
                          UINT64_C(2));
  }
}

/// TEST 3: Closure capturing TWO tree parameters.
std::pair<crane::fn<uint64_t(uint64_t)>, uint64_t>
MemSafetyProbe27::pair_two_trees(MemSafetyProbe27::tree t1,
                                 MemSafetyProbe27::tree t2) {
  return std::make_pair(crane::fn([=, t2 = std::move(t2)](uint64_t x) {
    return ((x + tree_sum(t1)) + tree_sum(t2));
  }),
                        tree_sum(t1));
}

/// TEST 4: Closure stored in option (no match on tree).
std::optional<crane::fn<uint64_t(uint64_t)>>
MemSafetyProbe27::opt_tree_fn(MemSafetyProbe27::tree t, bool b) {
  if (b) {
    return std::make_optional<crane::fn<uint64_t(uint64_t)>>(crane::fn(
        [=, t = std::move(t)](uint64_t x) { return (x + tree_sum(t)); }));
  } else {
    return std::optional<crane::fn<uint64_t(uint64_t)>>();
  }
}

/// TEST 5: Nested closures — inner captures tree, outer captures inner.
/// Tests that the inner closure correctly clones the tree.
std::pair<crane::fn<uint64_t(uint64_t)>, uint64_t>
MemSafetyProbe27::nested_closure_pair(MemSafetyProbe27::tree t) {
  crane::fn<uint64_t(uint64_t)> f =
      [=](uint64_t x) { return (x + tree_sum(t)); };
  return std::make_pair(
      crane::fn([=, f = std::move(f)](uint64_t x) { return f(f(x)); }),
      tree_sum(std::move(t)));
}

/// TEST 6: Three closures stored in a triple, each using tree differently.
std::pair<
    std::pair<crane::fn<uint64_t(uint64_t)>, crane::fn<uint64_t(uint64_t)>>,
    uint64_t> MemSafetyProbe27::triple_fns(MemSafetyProbe27::tree t) {
  return std::make_pair(std::make_pair(
      crane::fn([=](uint64_t x) { return (x + tree_sum(t)); }),
      crane::fn([=](uint64_t x) { return (x + tree_depth(t)); })),
                        (tree_sum(t) + tree_depth(t)));
}

/// TEST 7: Closure and tree value stored together in a pair.
/// Tests whether the closure's capture and the tree return
/// are independent clones.
std::pair<crane::fn<uint64_t(uint64_t)>, MemSafetyProbe27::tree>
MemSafetyProbe27::fn_and_tree(MemSafetyProbe27::tree t) {
  return std::make_pair(
      crane::fn([=](uint64_t x) { return (x + tree_sum(t)); }), t);
}

/// TEST 8: Closure captures tree, stored in option inside a pair.
/// Multiple levels of wrapping.
std::pair<std::optional<crane::fn<uint64_t(uint64_t)>>, uint64_t>
MemSafetyProbe27::wrapped_fn(MemSafetyProbe27::tree t, bool b) {
  return std::make_pair(
      (b ? std::make_optional<crane::fn<uint64_t(uint64_t)>>(
               crane::fn([=](uint64_t x) { return (x + tree_sum(t)); }))
         : std::optional<crane::fn<uint64_t(uint64_t)>>()),
      tree_sum(t));
}
