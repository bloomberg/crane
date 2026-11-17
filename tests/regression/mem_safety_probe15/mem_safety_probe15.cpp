#include "mem_safety_probe15.h"

uint64_t
MemSafetyProbe15::sum_list(const MemSafetyProbe15::mylist<uint64_t> &l) {
  // Explicit stack replaces the non-tail recursion of sum_list: _call frames
  // are pending calls, _after frames resume a caller.
  struct _call {
    const MemSafetyProbe15::mylist<uint64_t> *l;
  };

  struct _after_sum_list_in_Mycons {
    uint64_t a0;
  };

  using _frame = std::variant<_call, _after_sum_list_in_Mycons>;
  uint64_t _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&l});
  while (!_stack.empty()) {
    _frame _popped = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      const MemSafetyProbe15::mylist<uint64_t> &l = *_f.l;
      if (std::holds_alternative<
              typename MemSafetyProbe15::mylist<uint64_t>::Mynil>(l.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] = std::get<
            typename MemSafetyProbe15::mylist<uint64_t>::Mycons>(l.v());
        _stack.emplace_back(_after_sum_list_in_Mycons{a0});
        _stack.emplace_back(_call{crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<_after_sum_list_in_Mycons>(_popped));
      uint64_t a0 = _f.a0;
      _result = (a0 + std::move(_result));
    }
  }
  return _result;
}

/// TEST 1: Tree flattening where left subtree is used AFTER
/// right subtree recursive call.
/// In loopified code, the Enter frame for the right subtree
/// may move the left subtree's pointer.
MemSafetyProbe15::mylist<uint64_t>
MemSafetyProbe15::flatten(const MemSafetyProbe15::tree &t) {
  // Explicit stack replaces the non-tail recursion of flatten: _call frames are
  // pending calls, _after frames resume a caller.
  struct _call {
    const MemSafetyProbe15::tree *t;
  };

  struct _after_flatten_in_Node {
    uint64_t a1;
    const MemSafetyProbe15::tree *a2;
  };

  struct _after_flatten_in_Node_2 {
    uint64_t a1;
    MemSafetyProbe15::mylist<uint64_t> _tmp2;
  };

  using _frame =
      std::variant<_call, _after_flatten_in_Node, _after_flatten_in_Node_2>;
  MemSafetyProbe15::mylist<uint64_t> _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&t});
  while (!_stack.empty()) {
    _frame _popped = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      const MemSafetyProbe15::tree &t = *_f.t;
      if (std::holds_alternative<typename MemSafetyProbe15::tree::Leaf>(t.v())) {
        _result = mylist<uint64_t>::mynil();
      } else {
        const auto &[a0, a1, a2] =
            std::get<typename MemSafetyProbe15::tree::Node>(t.v());
        _stack.emplace_back(_after_flatten_in_Node{a1, crane_raw(a2)});
        _stack.emplace_back(_call{crane_raw(a0)});
      }
    } else if (std::holds_alternative<_after_flatten_in_Node>(_popped)) {
      auto _f = std::move(std::get<_after_flatten_in_Node>(_popped));
      uint64_t a1 = _f.a1;
      const MemSafetyProbe15::tree &a2 = *_f.a2;
      _stack.emplace_back(_after_flatten_in_Node_2{a1, std::move(_result)});
      _stack.emplace_back(_call{&a2});
    } else {
      auto _f = std::move(std::get<_after_flatten_in_Node_2>(_popped));
      uint64_t a1 = _f.a1;
      _result =
          _f._tmp2.myapp(mylist<uint64_t>::mycons(a1, std::move(_result)));
    }
  }
  return _result;
}

/// TEST 2: Tree to list where each element is the sum of
/// its subtree. Uses both subtrees for computation AND recursion.
MemSafetyProbe15::mylist<uint64_t>
MemSafetyProbe15::subtree_sums(const MemSafetyProbe15::tree &t) {
  // Explicit stack replaces the non-tail recursion of subtree_sums: _call
  // frames are pending calls, _after frames resume a caller.
  struct _call {
    const MemSafetyProbe15::tree *t;
  };

  struct _after_subtree_sums_in_Node {
    std::shared_ptr<MemSafetyProbe15::tree> a0;
    uint64_t a1;
    const MemSafetyProbe15::tree *a2;
  };

  struct _after_subtree_sums_in_Node_2 {
    std::shared_ptr<MemSafetyProbe15::tree> a0;
    uint64_t a1;
    const MemSafetyProbe15::tree *a2;
    MemSafetyProbe15::mylist<uint64_t> _tmp2;
  };

  using _frame = std::variant<_call, _after_subtree_sums_in_Node,
                              _after_subtree_sums_in_Node_2>;
  MemSafetyProbe15::mylist<uint64_t> _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&t});
  while (!_stack.empty()) {
    _frame _popped = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      const MemSafetyProbe15::tree &t = *_f.t;
      if (std::holds_alternative<typename MemSafetyProbe15::tree::Leaf>(t.v())) {
        _result = mylist<uint64_t>::mynil();
      } else {
        const auto &[a0, a1, a2] =
            std::get<typename MemSafetyProbe15::tree::Node>(t.v());
        _stack.emplace_back(_after_subtree_sums_in_Node{a0, a1, crane_raw(a2)});
        _stack.emplace_back(_call{crane_raw(a0)});
      }
    } else if (std::holds_alternative<_after_subtree_sums_in_Node>(_popped)) {
      auto _f = std::move(std::get<_after_subtree_sums_in_Node>(_popped));
      std::shared_ptr<MemSafetyProbe15::tree> a0 = std::move(_f.a0);
      uint64_t a1 = _f.a1;
      const MemSafetyProbe15::tree &a2 = *_f.a2;
      _stack.emplace_back(_after_subtree_sums_in_Node_2{std::move(a0), a1, &a2,
                                                        std::move(_result)});
      _stack.emplace_back(_call{&a2});
    } else {
      auto _f = std::move(std::get<_after_subtree_sums_in_Node_2>(_popped));
      std::shared_ptr<MemSafetyProbe15::tree> a0 = std::move(_f.a0);
      uint64_t a1 = _f.a1;
      const MemSafetyProbe15::tree &a2 = *_f.a2;
      _result =
          mylist<uint64_t>::mycons(((a0->tree_sum() + a1) + a2.tree_sum()),
                                   _f._tmp2.myapp(std::move(_result)));
    }
  }
  return _result;
}

/// TEST 5: Deep left-spine tree.
/// Stresses the frame stack depth.
MemSafetyProbe15::tree MemSafetyProbe15::left_spine(uint64_t n) {
  // Builds the result front to back: _write points at the empty tail the next
  // cell fills.
  std::optional<MemSafetyProbe15::tree> _root{};
  std::shared_ptr<MemSafetyProbe15::tree> *_write = nullptr;
  uint64_t _loop_n = n;
  while (true) {
    if (_loop_n <= 0) {
      auto _value = tree::leaf();
      (_write ? *(*_write = std::make_shared<MemSafetyProbe15::tree>(
                      std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      uint64_t n_ = _loop_n - 1;
      auto _cell = typename MemSafetyProbe15::tree::Node(
          nullptr, _loop_n,
          std::make_shared<MemSafetyProbe15::tree>(tree::leaf()));
      MemSafetyProbe15::tree &_node =
          (_write ? *(*_write = std::make_shared<MemSafetyProbe15::tree>(
                          std::move(_cell)))
                  : _root.emplace(std::move(_cell)));
      _write =
          &std::get<typename MemSafetyProbe15::tree::Node>(_node.v_mut()).a0;
      _loop_n = n_;
      continue;
    }
  }
  return std::move(*_root);
}

/// TEST 9: Build a large tree and verify all values are preserved.
MemSafetyProbe15::tree MemSafetyProbe15::make_tree(uint64_t n) {
  // Explicit stack replaces the non-tail recursion of make_tree: _call frames
  // are pending calls, _after frames resume a caller.
  struct _call {
    uint64_t n;
  };

  struct _after_make_tree_in_S {
    uint64_t n;
    uint64_t n_;
  };

  struct _after_make_tree_in_S_2 {
    uint64_t n;
    MemSafetyProbe15::tree _tmp2;
  };

  using _frame =
      std::variant<_call, _after_make_tree_in_S, _after_make_tree_in_S_2>;
  MemSafetyProbe15::tree _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{n});
  while (!_stack.empty()) {
    _frame _popped = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      uint64_t n = _f.n;
      if (n <= 0) {
        _result = tree::leaf();
      } else {
        uint64_t n_ = n - 1;
        _stack.emplace_back(_after_make_tree_in_S{n, n_});
        _stack.emplace_back(_call{n_});
      }
    } else if (std::holds_alternative<_after_make_tree_in_S>(_popped)) {
      auto _f = std::move(std::get<_after_make_tree_in_S>(_popped));
      uint64_t n = _f.n;
      uint64_t n_ = _f.n_;
      _stack.emplace_back(_after_make_tree_in_S_2{n, std::move(_result)});
      _stack.emplace_back(_call{n_});
    } else {
      auto _f = std::move(std::get<_after_make_tree_in_S_2>(_popped));
      uint64_t n = _f.n;
      _result = tree::node(std::move(_f._tmp2), n, std::move(_result));
    }
  }
  return _result;
}
