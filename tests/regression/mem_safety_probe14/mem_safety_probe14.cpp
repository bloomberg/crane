#include "mem_safety_probe14.h"

uint64_t MemSafetyProbe14::sum_fns(
    const MemSafetyProbe14::mylist<crane::fn<uint64_t(uint64_t)>> &l) {
  // Explicit stack replaces the non-tail recursion of sum_fns: _call frames are
  // pending calls, _after frames resume a caller.
  struct _call {
    const MemSafetyProbe14::mylist<crane::fn<uint64_t(uint64_t)>> *l;
  };

  struct _after_sum_fns_in_Mycons {
    crane::fn<uint64_t(uint64_t)> a0;
  };

  using _frame = std::variant<_call, _after_sum_fns_in_Mycons>;
  uint64_t _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&l});
  while (!_stack.empty()) {
    _frame _popped = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      const MemSafetyProbe14::mylist<crane::fn<uint64_t(uint64_t)>> &l = *_f.l;
      if (std::holds_alternative<typename MemSafetyProbe14::mylist<
              crane::fn<uint64_t(uint64_t)>>::Mynil>(l.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] = std::get<typename MemSafetyProbe14::mylist<
            crane::fn<uint64_t(uint64_t)>>::Mycons>(l.v());
        _stack.emplace_back(_after_sum_fns_in_Mycons{a0});
        _stack.emplace_back(_call{crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<_after_sum_fns_in_Mycons>(_popped));
      crane::fn<uint64_t(uint64_t)> a0 = std::move(_f.a0);
      _result = (a0(UINT64_C(0)) + std::move(_result));
    }
  }
  return _result;
}

/// TEST 5: Closure captures tree, tree is pattern-matched
/// AFTER closure creation. The match destructures the tree.
/// The closure must still hold the original tree.
uint64_t MemSafetyProbe14::capture_then_match(MemSafetyProbe14::tree t) {
  crane::fn<uint64_t(uint64_t)> f =
      [=](uint64_t n) { return (t.tree_sum() + n); };
  if (std::holds_alternative<typename MemSafetyProbe14::tree::Leaf>(t.v_mut())) {
    return f(UINT64_C(0));
  } else {
    auto &[a0, a1, a2] =
        std::get<typename MemSafetyProbe14::tree::Node>(t.v_mut());
    return ((f(std::move(a1)) + a0->tree_sum()) + a2->tree_sum());
  }
}

MemSafetyProbe14::mylist<crane::fn<uint64_t(uint64_t)>>
MemSafetyProbe14::tree_level_fns(const MemSafetyProbe14::tree &t,
                                 uint64_t depth) {
  // Explicit stack replaces the non-tail recursion of tree_level_fns: _call
  // frames are pending calls, _after frames resume a caller.
  struct _call {
    uint64_t depth;
    const MemSafetyProbe14::tree *t;
  };

  struct _after_tree_level_fns_in_Node {
    uint64_t depth;
    std::shared_ptr<MemSafetyProbe14::tree> a0;
    uint64_t a1;
    const MemSafetyProbe14::tree *a2;
  };

  struct _after_tree_level_fns_in_Node_2 {
    uint64_t depth;
    std::shared_ptr<MemSafetyProbe14::tree> a0;
    uint64_t a1;
    const MemSafetyProbe14::tree *a2;
    MemSafetyProbe14::mylist<crane::fn<uint64_t(uint64_t)>> _tmp2;
  };

  using _frame = std::variant<_call, _after_tree_level_fns_in_Node,
                              _after_tree_level_fns_in_Node_2>;
  MemSafetyProbe14::mylist<crane::fn<uint64_t(uint64_t)>> _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{depth, &t});
  while (!_stack.empty()) {
    _frame _popped = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      uint64_t depth = _f.depth;
      const MemSafetyProbe14::tree &t = *_f.t;
      if (std::holds_alternative<typename MemSafetyProbe14::tree::Leaf>(t.v())) {
        _result = mylist<crane::fn<uint64_t(uint64_t)>>::mynil();
      } else {
        const auto &[a0, a1, a2] =
            std::get<typename MemSafetyProbe14::tree::Node>(t.v());
        const MemSafetyProbe14::tree &a0_value = *a0;
        const MemSafetyProbe14::tree &a2_value = *a2;
        _stack.emplace_back(
            _after_tree_level_fns_in_Node{depth, a0, a1, crane_raw(a2)});
        _stack.emplace_back(_call{(UINT64_C(1) + depth), crane_raw(a0)});
      }
    } else if (std::holds_alternative<_after_tree_level_fns_in_Node>(_popped)) {
      auto _f = std::move(std::get<_after_tree_level_fns_in_Node>(_popped));
      uint64_t depth = _f.depth;
      std::shared_ptr<MemSafetyProbe14::tree> a0 = std::move(_f.a0);
      uint64_t a1 = _f.a1;
      const MemSafetyProbe14::tree &a2 = *_f.a2;
      const MemSafetyProbe14::tree &a0_value = *a0;
      const MemSafetyProbe14::tree &a2_value = a2;
      _stack.emplace_back(_after_tree_level_fns_in_Node_2{
          depth, std::move(a0), a1, &a2, std::move(_result)});
      _stack.emplace_back(_call{(UINT64_C(1) + depth), &a2_value});
    } else {
      auto _f = std::move(std::get<_after_tree_level_fns_in_Node_2>(_popped));
      uint64_t depth = _f.depth;
      std::shared_ptr<MemSafetyProbe14::tree> a0 = std::move(_f.a0);
      uint64_t a1 = _f.a1;
      const MemSafetyProbe14::tree &a2 = *_f.a2;
      const MemSafetyProbe14::tree &a0_value = *a0;
      const MemSafetyProbe14::tree &a2_value = a2;
      _result = mylist<crane::fn<uint64_t(uint64_t)>>::mycons(
          [=](uint64_t n) { return (((depth * UINT64_C(100)) + a1) + n); },
          mylist<crane::fn<uint64_t(uint64_t)>>::mycons(
              [=](uint64_t n) {
                return ((a0_value.tree_sum() + a2_value.tree_sum()) + n);
              },
              _f._tmp2.mylist_append(std::move(_result))));
    }
  }
  return _result;
}

/// TEST 8: Large tree stress test. Many closures, deep recursion.
MemSafetyProbe14::tree MemSafetyProbe14::make_balanced(uint64_t n) {
  // Builds the result front to back: _write points at the empty tail the next
  // cell fills.
  std::optional<MemSafetyProbe14::tree> _root{};
  std::shared_ptr<MemSafetyProbe14::tree> *_write = nullptr;
  uint64_t _loop_n = n;
  while (true) {
    if (_loop_n <= 0) {
      auto _value = tree::leaf();
      (_write ? *(*_write = std::make_shared<MemSafetyProbe14::tree>(
                      std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      uint64_t n_ = _loop_n - 1;
      auto _cell = typename MemSafetyProbe14::tree::Node(
          nullptr, _loop_n,
          std::make_shared<MemSafetyProbe14::tree>(tree::leaf()));
      MemSafetyProbe14::tree &_node =
          (_write ? *(*_write = std::make_shared<MemSafetyProbe14::tree>(
                          std::move(_cell)))
                  : _root.emplace(std::move(_cell)));
      _write =
          &std::get<typename MemSafetyProbe14::tree::Node>(_node.v_mut()).a0;
      _loop_n = n_;
      continue;
    }
  }
  return std::move(*_root);
}

MemSafetyProbe14::mylist<crane::fn<uint64_t(uint64_t)>>
MemSafetyProbe14::collect_closures(const MemSafetyProbe14::tree &t) {
  // Explicit stack replaces the non-tail recursion of collect_closures: _call
  // frames are pending calls, _after frames resume a caller.
  struct _call {
    const MemSafetyProbe14::tree *t;
  };

  struct _after_collect_closures_in_Node {
    uint64_t a1;
    const MemSafetyProbe14::tree *a2;
  };

  struct _after_collect_closures_in_Node_2 {
    uint64_t a1;
    MemSafetyProbe14::mylist<crane::fn<uint64_t(uint64_t)>> _tmp2;
  };

  using _frame = std::variant<_call, _after_collect_closures_in_Node,
                              _after_collect_closures_in_Node_2>;
  MemSafetyProbe14::mylist<crane::fn<uint64_t(uint64_t)>> _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&t});
  while (!_stack.empty()) {
    _frame _popped = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      const MemSafetyProbe14::tree &t = *_f.t;
      if (std::holds_alternative<typename MemSafetyProbe14::tree::Leaf>(t.v())) {
        _result = mylist<crane::fn<uint64_t(uint64_t)>>::mynil();
      } else {
        const auto &[a0, a1, a2] =
            std::get<typename MemSafetyProbe14::tree::Node>(t.v());
        const MemSafetyProbe14::tree &a0_value = *a0;
        const MemSafetyProbe14::tree &a2_value = *a2;
        _stack.emplace_back(_after_collect_closures_in_Node{a1, crane_raw(a2)});
        _stack.emplace_back(_call{crane_raw(a0)});
      }
    } else if (std::holds_alternative<_after_collect_closures_in_Node>(_popped)) {
      auto _f = std::move(std::get<_after_collect_closures_in_Node>(_popped));
      uint64_t a1 = _f.a1;
      const MemSafetyProbe14::tree &a2 = *_f.a2;
      const MemSafetyProbe14::tree &a2_value = a2;
      _stack.emplace_back(
          _after_collect_closures_in_Node_2{a1, std::move(_result)});
      _stack.emplace_back(_call{&a2_value});
    } else {
      auto _f = std::move(std::get<_after_collect_closures_in_Node_2>(_popped));
      uint64_t a1 = _f.a1;
      _result = mylist<crane::fn<uint64_t(uint64_t)>>::mycons(
          [=](uint64_t n) { return (a1 + n); },
          _f._tmp2.mylist_append(std::move(_result)));
    }
  }
  return _result;
}
