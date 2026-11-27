#include "mem_safety_probe24.h"

uint64_t
MemSafetyProbe24::sum_list(const MemSafetyProbe24::mylist<uint64_t> &l) {
  // Explicit stack replaces the non-tail recursion of sum_list: _call frames
  // are pending calls, _after frames resume a caller.
  struct _call {
    const MemSafetyProbe24::mylist<uint64_t> *l;
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
      const MemSafetyProbe24::mylist<uint64_t> &l = *_f.l;
      if (std::holds_alternative<
              typename MemSafetyProbe24::mylist<uint64_t>::Mynil>(l.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] = std::get<
            typename MemSafetyProbe24::mylist<uint64_t>::Mycons>(l.v());
        _stack.emplace_back(_after_sum_list_in_Mycons{a0});
        _stack.emplace_back(_call{crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<_after_sum_list_in_Mycons>(_popped));
      _stack.pop_back();
      uint64_t a0 = _f.a0;
      _result = a0 + _result;
    }
  }
  return _result;
}

MemSafetyProbe24::mylist<uint64_t>
MemSafetyProbe24::tree_to_list(const MemSafetyProbe24::tree &t) {
  // Explicit stack replaces the non-tail recursion of tree_to_list: _call
  // frames are pending calls, _after frames resume a caller.
  struct _call {
    const MemSafetyProbe24::tree *t;
  };

  struct _after_tree_to_list_in_Node {
    uint64_t a1;
    const MemSafetyProbe24::tree *a2;
  };

  struct _after_tree_to_list_in_Node_2 {
    uint64_t a1;
    MemSafetyProbe24::mylist<uint64_t> _tmp2;
  };

  using _frame = std::variant<_call, _after_tree_to_list_in_Node,
                              _after_tree_to_list_in_Node_2>;
  MemSafetyProbe24::mylist<uint64_t> _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&t});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const MemSafetyProbe24::tree &t = *_f.t;
      if (std::holds_alternative<typename MemSafetyProbe24::tree::Leaf>(t.v())) {
        _result = mylist<uint64_t>::mynil();
      } else {
        const auto &[a0, a1, a2] =
            std::get<typename MemSafetyProbe24::tree::Node>(t.v());
        _stack.emplace_back(_after_tree_to_list_in_Node{a1, crane_raw(a2)});
        _stack.emplace_back(_call{crane_raw(a0)});
      }
    } else if (std::holds_alternative<_after_tree_to_list_in_Node>(_popped)) {
      auto _f = std::move(std::get<_after_tree_to_list_in_Node>(_popped));
      _stack.pop_back();
      uint64_t a1 = _f.a1;
      const MemSafetyProbe24::tree &a2 = *_f.a2;
      _stack.emplace_back(_after_tree_to_list_in_Node_2{a1,
                                                        std::move(_result)});
      _stack.emplace_back(_call{&a2});
    } else {
      auto _f = std::move(std::get<_after_tree_to_list_in_Node_2>(_popped));
      _stack.pop_back();
      uint64_t a1 = _f.a1;
      _result = _f._tmp2.app(mylist<uint64_t>::mycons(a1, std::move(_result)));
    }
  }
  return _result;
}

/// TEST 7: Build a tree from a list, using accumulated state.
/// Tests interaction between list recursion and tree construction.
MemSafetyProbe24::tree
MemSafetyProbe24::list_to_tree(const MemSafetyProbe24::mylist<uint64_t> &l,
                               MemSafetyProbe24::tree acc) {
  // Loop replaces the tail recursion: each recursive call updates the loop
  // variables.
  MemSafetyProbe24::tree _loop_acc = std::move(acc);
  const MemSafetyProbe24::mylist<uint64_t> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<
            typename MemSafetyProbe24::mylist<uint64_t>::Mynil>(_loop_l->v())) {
      return _loop_acc;
    } else {
      const auto &[a0, a1] =
          std::get<typename MemSafetyProbe24::mylist<uint64_t>::Mycons>(
              _loop_l->v());
      _loop_acc = tree::node(std::move(_loop_acc), a0, tree::leaf());
      _loop_l = crane_raw(a1);
    }
  }
}

/// TEST 8: Zip two trees, producing a list of pairs.
/// Both trees are destructured simultaneously.
MemSafetyProbe24::mylist<std::pair<uint64_t, uint64_t>>
MemSafetyProbe24::zip_trees(const MemSafetyProbe24::tree &t1,
                            const MemSafetyProbe24::tree &t2) {
  // Explicit stack replaces the non-tail recursion of zip_trees: _call frames
  // are pending calls, _after frames resume a caller.
  struct _call {
    const MemSafetyProbe24::tree *t2;
    const MemSafetyProbe24::tree *t1;
  };

  struct _after_zip_trees_in_Node {
    uint64_t a1;
    const MemSafetyProbe24::tree *a2;
    uint64_t a10;
    const MemSafetyProbe24::tree *a20;
  };

  struct _after_zip_trees_in_Node_2 {
    uint64_t a1;
    uint64_t a10;
    MemSafetyProbe24::mylist<std::pair<uint64_t, uint64_t>> _tmp2;
  };

  using _frame =
      std::variant<_call, _after_zip_trees_in_Node, _after_zip_trees_in_Node_2>;
  MemSafetyProbe24::mylist<std::pair<uint64_t, uint64_t>> _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&t2, &t1});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const MemSafetyProbe24::tree &t2 = *_f.t2;
      const MemSafetyProbe24::tree &t1 = *_f.t1;
      if (std::holds_alternative<typename MemSafetyProbe24::tree::Leaf>(t1.v())) {
        _result = mylist<std::pair<uint64_t, uint64_t>>::mynil();
      } else {
        const auto &[a0, a1, a2] =
            std::get<typename MemSafetyProbe24::tree::Node>(t1.v());
        if (std::holds_alternative<typename MemSafetyProbe24::tree::Leaf>(
                t2.v())) {
          _result = mylist<std::pair<uint64_t, uint64_t>>::mynil();
        } else {
          const auto &[a00, a10, a20] =
              std::get<typename MemSafetyProbe24::tree::Node>(t2.v());
          _stack.emplace_back(
              _after_zip_trees_in_Node{a1, crane_raw(a2), a10, crane_raw(a20)});
          _stack.emplace_back(_call{crane_raw(a00), crane_raw(a0)});
        }
      }
    } else if (std::holds_alternative<_after_zip_trees_in_Node>(_popped)) {
      auto _f = std::move(std::get<_after_zip_trees_in_Node>(_popped));
      _stack.pop_back();
      uint64_t a1 = _f.a1;
      const MemSafetyProbe24::tree &a2 = *_f.a2;
      uint64_t a10 = _f.a10;
      const MemSafetyProbe24::tree &a20 = *_f.a20;
      _stack.emplace_back(
          _after_zip_trees_in_Node_2{a1, a10, std::move(_result)});
      _stack.emplace_back(_call{&a20, &a2});
    } else {
      auto _f = std::move(std::get<_after_zip_trees_in_Node_2>(_popped));
      _stack.pop_back();
      uint64_t a1 = _f.a1;
      uint64_t a10 = _f.a10;
      _result = _f._tmp2.app(mylist<std::pair<uint64_t, uint64_t>>::mycons(
          std::make_pair(a1, a10), std::move(_result)));
    }
  }
  return _result;
}
