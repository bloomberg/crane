#include "mem_safety_probe13.h"

uint64_t
MemSafetyProbe13::sum_list(const MemSafetyProbe13::mylist<uint64_t> &l) {
  // Explicit stack replaces the non-tail recursion of sum_list: _call frames
  // are pending calls, _after frames resume a caller.
  struct _call {
    const MemSafetyProbe13::mylist<uint64_t> *l;
  };

  struct _after_sum_list_in_Mycons {
    uint64_t a0;
  };

  using _frame = std::variant<_call, _after_sum_list_in_Mycons>;
  uint64_t _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&l});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const MemSafetyProbe13::mylist<uint64_t> &l = *_f.l;
      if (std::holds_alternative<
              typename MemSafetyProbe13::mylist<uint64_t>::Mynil>(l.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] = std::get<
            typename MemSafetyProbe13::mylist<uint64_t>::Mycons>(l.v());
        _stack.emplace_back(_after_sum_list_in_Mycons{a0});
        _stack.emplace_back(_call{crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<_after_sum_list_in_Mycons>(_popped));
      _stack.pop_back();
      uint64_t a0 = _f.a0;
      _result = (a0 + std::move(_result));
    }
  }
  return _result;
}

/// TEST 1: Double-recursion on tree where both subtrees
/// are used in closures AND in recursive calls.
/// Tests if the flatten optimization moves unique_ptr fields
/// that are also captured by closures.
std::pair<MemSafetyProbe13::mylist<uint64_t>,
          MemSafetyProbe13::mylist<crane::fn<uint64_t(uint64_t)>>>
MemSafetyProbe13::tree_vals_and_fns(const MemSafetyProbe13::tree &t) {
  // Explicit stack replaces the non-tail recursion of tree_vals_and_fns: _call
  // frames are pending calls, _after frames resume a caller.
  struct _call {
    const MemSafetyProbe13::tree *t;
  };

  struct _after_tree_vals_and_fns_in_Node {
    std::shared_ptr<MemSafetyProbe13::tree> a0;
    uint64_t a1;
    const MemSafetyProbe13::tree *a2;
  };

  struct _after_tree_vals_and_fns_in_pair {
    std::shared_ptr<MemSafetyProbe13::tree> a0;
    uint64_t a1;
    const MemSafetyProbe13::tree *a2;
    MemSafetyProbe13::mylist<uint64_t> lvals;
    MemSafetyProbe13::mylist<crane::fn<uint64_t(uint64_t)>> lfns;
  };

  using _frame = std::variant<_call, _after_tree_vals_and_fns_in_Node,
                              _after_tree_vals_and_fns_in_pair>;
  std::pair<MemSafetyProbe13::mylist<uint64_t>,
            MemSafetyProbe13::mylist<crane::fn<uint64_t(uint64_t)>>> _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&t});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const MemSafetyProbe13::tree &t = *_f.t;
      if (std::holds_alternative<typename MemSafetyProbe13::tree::Leaf>(t.v())) {
        _result =
            std::make_pair(mylist<uint64_t>::mynil(),
                           mylist<crane::fn<uint64_t(uint64_t)>>::mynil());
      } else {
        const auto &[a0, a1, a2] =
            std::get<typename MemSafetyProbe13::tree::Node>(t.v());
        const MemSafetyProbe13::tree &a0_value = *a0;
        const MemSafetyProbe13::tree &a2_value = *a2;
        _stack.emplace_back(
            _after_tree_vals_and_fns_in_Node{a0, a1, crane_raw(a2)});
        _stack.emplace_back(_call{crane_raw(a0)});
      }
    } else if (
            std::holds_alternative<_after_tree_vals_and_fns_in_Node>(_popped)) {
      auto _f = std::move(std::get<_after_tree_vals_and_fns_in_Node>(_popped));
      _stack.pop_back();
      std::shared_ptr<MemSafetyProbe13::tree> a0 = std::move(_f.a0);
      uint64_t a1 = _f.a1;
      const MemSafetyProbe13::tree &a2 = *_f.a2;
      const MemSafetyProbe13::tree &a0_value = *a0;
      const MemSafetyProbe13::tree &a2_value = a2;
      auto [lvals, lfns] = std::move(_result);
      _stack.emplace_back(_after_tree_vals_and_fns_in_pair{
          std::move(a0), a1, &a2, std::move(lvals), std::move(lfns)});
      _stack.emplace_back(_call{&a2_value});
    } else {
      auto _f = std::move(std::get<_after_tree_vals_and_fns_in_pair>(_popped));
      _stack.pop_back();
      std::shared_ptr<MemSafetyProbe13::tree> a0 = std::move(_f.a0);
      uint64_t a1 = _f.a1;
      const MemSafetyProbe13::tree &a2 = *_f.a2;
      MemSafetyProbe13::mylist<uint64_t> lvals = std::move(_f.lvals);
      MemSafetyProbe13::mylist<crane::fn<uint64_t(uint64_t)>> lfns =
          std::move(_f.lfns);
      const MemSafetyProbe13::tree &a0_value = *a0;
      const MemSafetyProbe13::tree &a2_value = a2;
      auto [rvals, rfns] = std::move(_result);
      crane::fn<uint64_t(uint64_t)> f =
          [=, a0_value = a0_value, a2_value = a2_value](uint64_t n) {
            return ((a0_value.tree_sum() + a2_value.tree_sum()) + n);
          };
      _result = std::make_pair(
          mylist<uint64_t>::mycons(a1, lvals.app(std::move(rvals))),
          mylist<crane::fn<uint64_t(uint64_t)>>::mycons(
              std::move(f), lfns.app(std::move(rfns))));
    }
  }
  return _result;
}

/// TEST 4: Deeply nested tree with closures at EVERY level.
/// Each closure captures values from its level AND from the parent.
/// Tests stack depth and closure lifetime with deep nesting.
MemSafetyProbe13::tree MemSafetyProbe13::make_deep(uint64_t n) {
  // Builds the result front to back: _write points at the empty tail the next
  // cell fills.
  std::optional<MemSafetyProbe13::tree> _root{};
  std::shared_ptr<MemSafetyProbe13::tree> *_write = nullptr;
  uint64_t _loop_n = n;
  while (true) {
    if (_loop_n <= 0) {
      auto _value = tree::leaf();
      (_write ? *(*_write = std::make_shared<MemSafetyProbe13::tree>(
                      std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      uint64_t n_ = _loop_n - 1;
      auto _cell = typename MemSafetyProbe13::tree::Node(
          nullptr, _loop_n,
          std::make_shared<MemSafetyProbe13::tree>(tree::leaf()));
      MemSafetyProbe13::tree &_node =
          (_write ? *(*_write = std::make_shared<MemSafetyProbe13::tree>(
                          std::move(_cell)))
                  : _root.emplace(std::move(_cell)));
      _write =
          &std::get<typename MemSafetyProbe13::tree::Node>(_node.v_mut()).a0;
      _loop_n = n_;
      continue;
    }
  }
  return std::move(*_root);
}

MemSafetyProbe13::mylist<crane::fn<uint64_t(uint64_t)>>
MemSafetyProbe13::depth_fns(const MemSafetyProbe13::tree &t,
                            uint64_t parent_val) {
  // Builds the result front to back: _write points at the empty tail the next
  // cell fills.
  std::optional<MemSafetyProbe13::mylist<crane::fn<uint64_t(uint64_t)>>> _root{};
  std::shared_ptr<MemSafetyProbe13::mylist<crane::fn<uint64_t(uint64_t)>>> *_write =
      nullptr;
  uint64_t _loop_parent_val = parent_val;
  const MemSafetyProbe13::tree *_loop_t = &t;
  while (true) {
    if (std::holds_alternative<typename MemSafetyProbe13::tree::Leaf>(
            _loop_t->v())) {
      auto _value = mylist<crane::fn<uint64_t(uint64_t)>>::mynil();
      (_write ? *(*_write = std::make_shared<
                      MemSafetyProbe13::mylist<crane::fn<uint64_t(uint64_t)>>>(
                      std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      const auto &[a0, a1, _] =
          std::get<typename MemSafetyProbe13::tree::Node>(_loop_t->v());
      const MemSafetyProbe13::tree &a0_value = *a0;
      crane::fn<uint64_t(uint64_t)> f =
          [=](uint64_t n) { return ((_loop_parent_val + a1) + n); };
      auto _cell = typename MemSafetyProbe13::mylist<
          crane::fn<uint64_t(uint64_t)>>::Mycons(std::move(f), nullptr);
      MemSafetyProbe13::mylist<crane::fn<uint64_t(uint64_t)>> &_node =
          (_write ? *(*_write = std::make_shared<MemSafetyProbe13::mylist<
                          crane::fn<uint64_t(uint64_t)>>>(std::move(_cell)))
                  : _root.emplace(std::move(_cell)));
      _write =
          &std::get<typename MemSafetyProbe13::mylist<
              crane::fn<uint64_t(uint64_t)>>::Mycons>(_node.v_mut()).a1;
      _loop_parent_val = a1;
      _loop_t = &a0_value;
      continue;
    }
  }
  return std::move(*_root);
}

MemSafetyProbe13::ftree
MemSafetyProbe13::tree_to_ftree(const MemSafetyProbe13::tree &t) {
  // Explicit stack replaces the non-tail recursion of tree_to_ftree: _call
  // frames are pending calls, _after frames resume a caller.
  struct _call {
    const MemSafetyProbe13::tree *t;
  };

  struct _after_tree_to_ftree_in_Node {
    uint64_t a1;
    const MemSafetyProbe13::tree *a2;
  };

  struct _after_tree_to_ftree_in_Node_2 {
    uint64_t a1;
    MemSafetyProbe13::ftree _tmp2;
  };

  using _frame = std::variant<_call, _after_tree_to_ftree_in_Node,
                              _after_tree_to_ftree_in_Node_2>;
  MemSafetyProbe13::ftree _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&t});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const MemSafetyProbe13::tree &t = *_f.t;
      if (std::holds_alternative<typename MemSafetyProbe13::tree::Leaf>(t.v())) {
        _result = ftree::fleaf();
      } else {
        const auto &[a0, a1, a2] =
            std::get<typename MemSafetyProbe13::tree::Node>(t.v());
        const MemSafetyProbe13::tree &a0_value = *a0;
        const MemSafetyProbe13::tree &a2_value = *a2;
        _stack.emplace_back(_after_tree_to_ftree_in_Node{a1, crane_raw(a2)});
        _stack.emplace_back(_call{crane_raw(a0)});
      }
    } else if (std::holds_alternative<_after_tree_to_ftree_in_Node>(_popped)) {
      auto _f = std::move(std::get<_after_tree_to_ftree_in_Node>(_popped));
      _stack.pop_back();
      uint64_t a1 = _f.a1;
      const MemSafetyProbe13::tree &a2 = *_f.a2;
      const MemSafetyProbe13::tree &a2_value = a2;
      _stack.emplace_back(
          _after_tree_to_ftree_in_Node_2{a1, std::move(_result)});
      _stack.emplace_back(_call{&a2_value});
    } else {
      auto _f = std::move(std::get<_after_tree_to_ftree_in_Node_2>(_popped));
      _stack.pop_back();
      uint64_t a1 = _f.a1;
      _result = ftree::fnode(std::move(_f._tmp2),
                             [=](uint64_t n) { return (a1 + n); },
                             std::move(_result));
    }
  }
  return _result;
}

/// TEST 6: Flatten a tree of lists into a single list,
/// where each list element is a closure.
MemSafetyProbe13::mylist<crane::fn<uint64_t(uint64_t)>>
MemSafetyProbe13::flatten_tree_fns(const MemSafetyProbe13::tree &t) {
  // Explicit stack replaces the non-tail recursion of flatten_tree_fns: _call
  // frames are pending calls, _after frames resume a caller.
  struct _call {
    const MemSafetyProbe13::tree *t;
  };

  struct _after_flatten_tree_fns_in_Node {
    uint64_t a1;
    const MemSafetyProbe13::tree *a2;
  };

  struct _after_flatten_tree_fns_in_Node_2 {
    uint64_t a1;
    MemSafetyProbe13::mylist<crane::fn<uint64_t(uint64_t)>> _tmp2;
  };

  using _frame = std::variant<_call, _after_flatten_tree_fns_in_Node,
                              _after_flatten_tree_fns_in_Node_2>;
  MemSafetyProbe13::mylist<crane::fn<uint64_t(uint64_t)>> _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&t});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const MemSafetyProbe13::tree &t = *_f.t;
      if (std::holds_alternative<typename MemSafetyProbe13::tree::Leaf>(t.v())) {
        _result = mylist<crane::fn<uint64_t(uint64_t)>>::mynil();
      } else {
        const auto &[a0, a1, a2] =
            std::get<typename MemSafetyProbe13::tree::Node>(t.v());
        const MemSafetyProbe13::tree &a0_value = *a0;
        const MemSafetyProbe13::tree &a2_value = *a2;
        _stack.emplace_back(_after_flatten_tree_fns_in_Node{a1, crane_raw(a2)});
        _stack.emplace_back(_call{crane_raw(a0)});
      }
    } else if (std::holds_alternative<_after_flatten_tree_fns_in_Node>(_popped)) {
      auto _f = std::move(std::get<_after_flatten_tree_fns_in_Node>(_popped));
      _stack.pop_back();
      uint64_t a1 = _f.a1;
      const MemSafetyProbe13::tree &a2 = *_f.a2;
      const MemSafetyProbe13::tree &a2_value = a2;
      _stack.emplace_back(
          _after_flatten_tree_fns_in_Node_2{a1, std::move(_result)});
      _stack.emplace_back(_call{&a2_value});
    } else {
      auto _f = std::move(std::get<_after_flatten_tree_fns_in_Node_2>(_popped));
      _stack.pop_back();
      uint64_t a1 = _f.a1;
      _result = _f._tmp2.app(mylist<crane::fn<uint64_t(uint64_t)>>::mycons(
          [=](uint64_t n) { return (a1 + n); }, std::move(_result)));
    }
  }
  return _result;
}
