#include "mem_safety_probe28.h"

uint64_t MemSafetyProbe28::tree_sum(const MemSafetyProbe28::tree &t) {
  // Explicit stack replaces the non-tail recursion of tree_sum: _call frames
  // are pending calls, _after frames resume a caller.
  struct _call {
    const MemSafetyProbe28::tree *t;
  };

  struct _after_tree_sum_in_Node {
    uint64_t a1;
    const MemSafetyProbe28::tree *a2;
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
      const MemSafetyProbe28::tree &t = *_f.t;
      if (std::holds_alternative<typename MemSafetyProbe28::tree::Leaf>(t.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1, a2] =
            std::get<typename MemSafetyProbe28::tree::Node>(t.v());
        _stack.emplace_back(_after_tree_sum_in_Node{a1, crane_raw(a2)});
        _stack.emplace_back(_call{crane_raw(a0)});
      }
    } else if (std::holds_alternative<_after_tree_sum_in_Node>(_popped)) {
      auto _f = std::move(std::get<_after_tree_sum_in_Node>(_popped));
      _stack.pop_back();
      uint64_t a1 = _f.a1;
      const MemSafetyProbe28::tree &a2 = *_f.a2;
      _stack.emplace_back(_after_tree_sum_in_Node_2{a1, _result});
      _stack.emplace_back(_call{&a2});
    } else {
      auto _f = std::move(std::get<_after_tree_sum_in_Node_2>(_popped));
      _stack.pop_back();
      uint64_t a1 = _f.a1;
      _result = ((_f._tmp2 + a1) + _result);
    }
  }
  return _result;
}

uint64_t MemSafetyProbe28::tree_depth(const MemSafetyProbe28::tree &t) {
  // Explicit stack replaces the non-tail recursion of tree_depth: _call frames
  // are pending calls, _after frames resume a caller.
  struct _call {
    const MemSafetyProbe28::tree *t;
  };

  struct _after_tree_depth_in_Node {
    const MemSafetyProbe28::tree *a2;
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
      const MemSafetyProbe28::tree &t = *_f.t;
      if (std::holds_alternative<typename MemSafetyProbe28::tree::Leaf>(t.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, _, a2] =
            std::get<typename MemSafetyProbe28::tree::Node>(t.v());
        _stack.emplace_back(_after_tree_depth_in_Node{crane_raw(a2)});
        _stack.emplace_back(_call{crane_raw(a0)});
      }
    } else if (std::holds_alternative<_after_tree_depth_in_Node>(_popped)) {
      auto _f = std::move(std::get<_after_tree_depth_in_Node>(_popped));
      _stack.pop_back();
      const MemSafetyProbe28::tree &a2 = *_f.a2;
      _stack.emplace_back(_after_tree_depth_in_Node_2{_result});
      _stack.emplace_back(_call{&a2});
    } else {
      auto _f = std::move(std::get<_after_tree_depth_in_Node_2>(_popped));
      _stack.pop_back();
      _result = (UINT64_C(1) + std::max(_f._tmp2, _result));
    }
  }
  return _result;
}

/// TEST 1: zip_trees - Two tree params, t1 structural, t2 non-structural.
/// t2 is NOT pointer-safe because some calls pass Leaf (not CPPderef).
/// In the Node/Node branch, t2's children are used for recursion AND
/// tree_sum t2 uses the whole tree. If the optimization moves *(l2),
/// tree_sum t2 might see corrupted data.
uint64_t MemSafetyProbe28::zip_trees(const MemSafetyProbe28::tree &t1,
                                     const MemSafetyProbe28::tree &t2) {
  // Explicit stack replaces the non-tail recursion of zip_trees: _call frames
  // are pending calls, _after frames resume a caller.
  struct _call {
    MemSafetyProbe28::tree t2;
    const MemSafetyProbe28::tree *t1;
  };

  struct _after_zip_trees_in_Leaf {
    uint64_t a1;
    const MemSafetyProbe28::tree *a2;
  };

  struct _after_zip_trees_in_Leaf_2 {
    uint64_t a1;
    uint64_t _tmp2;
  };

  struct _after_zip_trees_in_Node {
    MemSafetyProbe28::tree t2;
    uint64_t a1;
    const MemSafetyProbe28::tree *a2;
    uint64_t a10;
    std::shared_ptr<MemSafetyProbe28::tree> a20;
  };

  struct _after_zip_trees_in_Node_2 {
    MemSafetyProbe28::tree t2;
    uint64_t a1;
    uint64_t a10;
    uint64_t _tmp4;
  };

  using _frame =
      std::variant<_call, _after_zip_trees_in_Leaf, _after_zip_trees_in_Leaf_2,
                   _after_zip_trees_in_Node, _after_zip_trees_in_Node_2>;
  uint64_t _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{t2, &t1});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      MemSafetyProbe28::tree t2 = std::move(_f.t2);
      const MemSafetyProbe28::tree &t1 = *_f.t1;
      if (std::holds_alternative<typename MemSafetyProbe28::tree::Leaf>(t1.v())) {
        _result = tree_sum(std::move(t2));
      } else {
        const auto &[a0, a1, a2] =
            std::get<typename MemSafetyProbe28::tree::Node>(t1.v());
        if (std::holds_alternative<typename MemSafetyProbe28::tree::Leaf>(
                t2.v())) {
          _stack.emplace_back(_after_zip_trees_in_Leaf{a1, crane_raw(a2)});
          _stack.emplace_back(_call{tree::leaf(), crane_raw(a0)});
        } else {
          const auto &[a00, a10, a20] =
              std::get<typename MemSafetyProbe28::tree::Node>(t2.v());
          _stack.emplace_back(
              _after_zip_trees_in_Node{t2, a1, crane_raw(a2), a10, a20});
          _stack.emplace_back(_call{*a00, crane_raw(a0)});
        }
      }
    } else if (std::holds_alternative<_after_zip_trees_in_Leaf>(_popped)) {
      auto _f = std::move(std::get<_after_zip_trees_in_Leaf>(_popped));
      _stack.pop_back();
      uint64_t a1 = _f.a1;
      const MemSafetyProbe28::tree &a2 = *_f.a2;
      _stack.emplace_back(_after_zip_trees_in_Leaf_2{a1, _result});
      _stack.emplace_back(_call{tree::leaf(), &a2});
    } else if (std::holds_alternative<_after_zip_trees_in_Leaf_2>(_popped)) {
      auto _f = std::move(std::get<_after_zip_trees_in_Leaf_2>(_popped));
      _stack.pop_back();
      uint64_t a1 = _f.a1;
      _result = ((a1 + _f._tmp2) + _result);
    } else if (std::holds_alternative<_after_zip_trees_in_Node>(_popped)) {
      auto _f = std::move(std::get<_after_zip_trees_in_Node>(_popped));
      _stack.pop_back();
      MemSafetyProbe28::tree t2 = std::move(_f.t2);
      uint64_t a1 = _f.a1;
      const MemSafetyProbe28::tree &a2 = *_f.a2;
      uint64_t a10 = _f.a10;
      std::shared_ptr<MemSafetyProbe28::tree> a20 = std::move(_f.a20);
      _stack.emplace_back(
          _after_zip_trees_in_Node_2{std::move(t2), a1, a10, _result});
      _stack.emplace_back(_call{*a20, &a2});
    } else {
      auto _f = std::move(std::get<_after_zip_trees_in_Node_2>(_popped));
      _stack.pop_back();
      MemSafetyProbe28::tree t2 = std::move(_f.t2);
      uint64_t a1 = _f.a1;
      uint64_t a10 = _f.a10;
      _result = ((((_f._tmp4 + a1) + a10) + _result) + tree_sum(std::move(t2)));
    }
  }
  return _result;
}

/// TEST 2: zip_depth - Similar but uses tree_depth on t2.
/// Tests a different tree traversal on the non-pointer-safe param.
uint64_t MemSafetyProbe28::zip_depth(const MemSafetyProbe28::tree &t1,
                                     const MemSafetyProbe28::tree &t2) {
  // Explicit stack replaces the non-tail recursion of zip_depth: _call frames
  // are pending calls, _after frames resume a caller.
  struct _call {
    MemSafetyProbe28::tree t2;
    const MemSafetyProbe28::tree *t1;
  };

  struct _after_zip_depth_in_Leaf {
    uint64_t a1;
    const MemSafetyProbe28::tree *a2;
  };

  struct _after_zip_depth_in_Leaf_2 {
    uint64_t a1;
    uint64_t _tmp2;
  };

  struct _after_zip_depth_in_Node {
    MemSafetyProbe28::tree t2;
    const MemSafetyProbe28::tree *a2;
    std::shared_ptr<MemSafetyProbe28::tree> a20;
  };

  struct _after_zip_depth_in_Node_2 {
    MemSafetyProbe28::tree t2;
    uint64_t _tmp4;
  };

  using _frame =
      std::variant<_call, _after_zip_depth_in_Leaf, _after_zip_depth_in_Leaf_2,
                   _after_zip_depth_in_Node, _after_zip_depth_in_Node_2>;
  uint64_t _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{t2, &t1});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      MemSafetyProbe28::tree t2 = std::move(_f.t2);
      const MemSafetyProbe28::tree &t1 = *_f.t1;
      if (std::holds_alternative<typename MemSafetyProbe28::tree::Leaf>(t1.v())) {
        _result = tree_depth(std::move(t2));
      } else {
        const auto &[a0, a1, a2] =
            std::get<typename MemSafetyProbe28::tree::Node>(t1.v());
        if (std::holds_alternative<typename MemSafetyProbe28::tree::Leaf>(
                t2.v())) {
          _stack.emplace_back(_after_zip_depth_in_Leaf{a1, crane_raw(a2)});
          _stack.emplace_back(_call{tree::leaf(), crane_raw(a0)});
        } else {
          const auto &[a00, _, a20] =
              std::get<typename MemSafetyProbe28::tree::Node>(t2.v());
          _stack.emplace_back(_after_zip_depth_in_Node{t2, crane_raw(a2), a20});
          _stack.emplace_back(_call{*a00, crane_raw(a0)});
        }
      }
    } else if (std::holds_alternative<_after_zip_depth_in_Leaf>(_popped)) {
      auto _f = std::move(std::get<_after_zip_depth_in_Leaf>(_popped));
      _stack.pop_back();
      uint64_t a1 = _f.a1;
      const MemSafetyProbe28::tree &a2 = *_f.a2;
      _stack.emplace_back(_after_zip_depth_in_Leaf_2{a1, _result});
      _stack.emplace_back(_call{tree::leaf(), &a2});
    } else if (std::holds_alternative<_after_zip_depth_in_Leaf_2>(_popped)) {
      auto _f = std::move(std::get<_after_zip_depth_in_Leaf_2>(_popped));
      _stack.pop_back();
      uint64_t a1 = _f.a1;
      _result = ((a1 + _f._tmp2) + _result);
    } else if (std::holds_alternative<_after_zip_depth_in_Node>(_popped)) {
      auto _f = std::move(std::get<_after_zip_depth_in_Node>(_popped));
      _stack.pop_back();
      MemSafetyProbe28::tree t2 = std::move(_f.t2);
      const MemSafetyProbe28::tree &a2 = *_f.a2;
      std::shared_ptr<MemSafetyProbe28::tree> a20 = std::move(_f.a20);
      _stack.emplace_back(_after_zip_depth_in_Node_2{std::move(t2), _result});
      _stack.emplace_back(_call{*a20, &a2});
    } else {
      auto _f = std::move(std::get<_after_zip_depth_in_Node_2>(_popped));
      _stack.pop_back();
      MemSafetyProbe28::tree t2 = std::move(_f.t2);
      _result = ((_f._tmp4 + tree_depth(std::move(t2))) + _result);
    }
  }
  return _result;
}

/// TEST 3: zip_and_build - Recurse and also construct using t2's children.
/// t2's left child is used for recursion AND returned as part of result.
uint64_t MemSafetyProbe28::zip_and_sum(const MemSafetyProbe28::tree &t1,
                                       const MemSafetyProbe28::tree &t2) {
  // Explicit stack replaces the non-tail recursion of zip_and_sum: _call frames
  // are pending calls, _after frames resume a caller.
  struct _call {
    MemSafetyProbe28::tree t2;
    const MemSafetyProbe28::tree *t1;
  };

  struct _after_zip_and_sum_in_Leaf {
    uint64_t a1;
    const MemSafetyProbe28::tree *a2;
  };

  struct _after_zip_and_sum_in_Leaf_2 {
    uint64_t a1;
    uint64_t _tmp2;
  };

  struct _after_zip_and_sum_in_Node {
    const MemSafetyProbe28::tree *a2;
    std::shared_ptr<MemSafetyProbe28::tree> a00;
    uint64_t a10;
    std::shared_ptr<MemSafetyProbe28::tree> a20;
  };

  struct _after_zip_and_sum_in_Node_2 {
    std::shared_ptr<MemSafetyProbe28::tree> a00;
    uint64_t a10;
    std::shared_ptr<MemSafetyProbe28::tree> a20;
    uint64_t _tmp4;
  };

  using _frame = std::variant<
      _call, _after_zip_and_sum_in_Leaf, _after_zip_and_sum_in_Leaf_2,
      _after_zip_and_sum_in_Node, _after_zip_and_sum_in_Node_2>;
  uint64_t _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{t2, &t1});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      MemSafetyProbe28::tree t2 = std::move(_f.t2);
      const MemSafetyProbe28::tree &t1 = *_f.t1;
      if (std::holds_alternative<typename MemSafetyProbe28::tree::Leaf>(t1.v())) {
        _result = tree_sum(std::move(t2));
      } else {
        const auto &[a0, a1, a2] =
            std::get<typename MemSafetyProbe28::tree::Node>(t1.v());
        if (std::holds_alternative<typename MemSafetyProbe28::tree::Leaf>(
                t2.v_mut())) {
          _stack.emplace_back(_after_zip_and_sum_in_Leaf{a1, crane_raw(a2)});
          _stack.emplace_back(_call{tree::leaf(), crane_raw(a0)});
        } else {
          auto &[a00, a10, a20] =
              std::get<typename MemSafetyProbe28::tree::Node>(t2.v_mut());
          _stack.emplace_back(
              _after_zip_and_sum_in_Node{crane_raw(a2), a00, a10, a20});
          _stack.emplace_back(_call{*a00, crane_raw(a0)});
        }
      }
    } else if (std::holds_alternative<_after_zip_and_sum_in_Leaf>(_popped)) {
      auto _f = std::move(std::get<_after_zip_and_sum_in_Leaf>(_popped));
      _stack.pop_back();
      uint64_t a1 = _f.a1;
      const MemSafetyProbe28::tree &a2 = *_f.a2;
      _stack.emplace_back(_after_zip_and_sum_in_Leaf_2{a1, _result});
      _stack.emplace_back(_call{tree::leaf(), &a2});
    } else if (std::holds_alternative<_after_zip_and_sum_in_Leaf_2>(_popped)) {
      auto _f = std::move(std::get<_after_zip_and_sum_in_Leaf_2>(_popped));
      _stack.pop_back();
      uint64_t a1 = _f.a1;
      _result = ((_f._tmp2 + a1) + _result);
    } else if (std::holds_alternative<_after_zip_and_sum_in_Node>(_popped)) {
      auto _f = std::move(std::get<_after_zip_and_sum_in_Node>(_popped));
      _stack.pop_back();
      const MemSafetyProbe28::tree &a2 = *_f.a2;
      std::shared_ptr<MemSafetyProbe28::tree> a00 = std::move(_f.a00);
      uint64_t a10 = _f.a10;
      std::shared_ptr<MemSafetyProbe28::tree> a20 = std::move(_f.a20);
      _stack.emplace_back(
          _after_zip_and_sum_in_Node_2{std::move(a00), a10, a20, _result});
      _stack.emplace_back(_call{*a20, &a2});
    } else {
      auto _f = std::move(std::get<_after_zip_and_sum_in_Node_2>(_popped));
      _stack.pop_back();
      std::shared_ptr<MemSafetyProbe28::tree> a00 = std::move(_f.a00);
      uint64_t a10 = _f.a10;
      std::shared_ptr<MemSafetyProbe28::tree> a20 = std::move(_f.a20);
      _result =
          ((((_f._tmp4 + a10) + _result) + tree_sum(*a00)) + tree_sum(*a20));
    }
  }
  return _result;
}

/// TEST 4: double_zip - Both t1 and t2 are trees, but t2 is used
/// in a different way for each call. Makes t2 non-pointer-safe.
uint64_t MemSafetyProbe28::double_zip(const MemSafetyProbe28::tree &t1,
                                      const MemSafetyProbe28::tree &t2) {
  // Explicit stack replaces the non-tail recursion of double_zip: _call frames
  // are pending calls, _after frames resume a caller.
  struct _call {
    const MemSafetyProbe28::tree *t2;
    const MemSafetyProbe28::tree *t1;
  };

  struct _after_double_zip_in_Leaf {
    const MemSafetyProbe28::tree *t2;
    uint64_t a1;
    const MemSafetyProbe28::tree *a2;
  };

  struct _after_double_zip_in_Leaf_2 {
    uint64_t a1;
    uint64_t _tmp2;
  };

  struct _after_double_zip_in_Node {
    MemSafetyProbe28::tree t2;
    const MemSafetyProbe28::tree *a2;
    uint64_t a10;
    const MemSafetyProbe28::tree *a20;
  };

  struct _after_double_zip_in_Node_2 {
    MemSafetyProbe28::tree t2;
    uint64_t a10;
    uint64_t _tmp4;
  };

  using _frame = std::variant<
      _call, _after_double_zip_in_Leaf, _after_double_zip_in_Leaf_2,
      _after_double_zip_in_Node, _after_double_zip_in_Node_2>;
  uint64_t _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&t2, &t1});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const MemSafetyProbe28::tree &t2 = *_f.t2;
      const MemSafetyProbe28::tree &t1 = *_f.t1;
      if (std::holds_alternative<typename MemSafetyProbe28::tree::Leaf>(t1.v())) {
        _result = tree_sum(t2);
      } else {
        const auto &[a0, a1, a2] =
            std::get<typename MemSafetyProbe28::tree::Node>(t1.v());
        if (std::holds_alternative<typename MemSafetyProbe28::tree::Leaf>(
                t2.v())) {
          _stack.emplace_back(_after_double_zip_in_Leaf{&t2, a1,
                                                        crane_raw(a2)});
          _stack.emplace_back(_call{&t2, crane_raw(a0)});
        } else {
          const auto &[a00, a10, a20] =
              std::get<typename MemSafetyProbe28::tree::Node>(t2.v());
          _stack.emplace_back(
              _after_double_zip_in_Node{t2, crane_raw(a2), a10,
                                        crane_raw(a20)});
          _stack.emplace_back(_call{crane_raw(a00), crane_raw(a0)});
        }
      }
    } else if (std::holds_alternative<_after_double_zip_in_Leaf>(_popped)) {
      auto _f = std::move(std::get<_after_double_zip_in_Leaf>(_popped));
      _stack.pop_back();
      const MemSafetyProbe28::tree &t2 = *_f.t2;
      uint64_t a1 = _f.a1;
      const MemSafetyProbe28::tree &a2 = *_f.a2;
      _stack.emplace_back(_after_double_zip_in_Leaf_2{a1, _result});
      _stack.emplace_back(_call{&t2, &a2});
    } else if (std::holds_alternative<_after_double_zip_in_Leaf_2>(_popped)) {
      auto _f = std::move(std::get<_after_double_zip_in_Leaf_2>(_popped));
      _stack.pop_back();
      uint64_t a1 = _f.a1;
      _result = ((_f._tmp2 + a1) + _result);
    } else if (std::holds_alternative<_after_double_zip_in_Node>(_popped)) {
      auto _f = std::move(std::get<_after_double_zip_in_Node>(_popped));
      _stack.pop_back();
      const MemSafetyProbe28::tree &t2 = _f.t2;
      const MemSafetyProbe28::tree &a2 = *_f.a2;
      uint64_t a10 = _f.a10;
      const MemSafetyProbe28::tree &a20 = *_f.a20;
      _stack.emplace_back(_after_double_zip_in_Node_2{t2, a10, _result});
      _stack.emplace_back(_call{&a20, &a2});
    } else {
      auto _f = std::move(std::get<_after_double_zip_in_Node_2>(_popped));
      _stack.pop_back();
      MemSafetyProbe28::tree t2 = std::move(_f.t2);
      uint64_t a10 = _f.a10;
      _result = (((_f._tmp4 + _result) + a10) + tree_sum(std::move(t2)));
    }
  }
  return _result;
}

/// TEST 5: zip with list accumulator. t2 is tree, acc is list.
/// t2 non-pointer-safe due to Leaf in some calls.
List<uint64_t> MemSafetyProbe28::zip_collect(const MemSafetyProbe28::tree &t1,
                                             const MemSafetyProbe28::tree &t2,
                                             List<uint64_t> acc) {
  // Explicit stack replaces the non-tail recursion of zip_collect: _call frames
  // are pending calls, _after frames resume a caller.
  struct _call {
    List<uint64_t> acc;
    MemSafetyProbe28::tree t2;
    const MemSafetyProbe28::tree *t1;
  };

  struct _after_zip_collect_in_Leaf {
    const MemSafetyProbe28::tree *a0;
    uint64_t a1;
  };

  struct _after_zip_collect_in_Node {
    const MemSafetyProbe28::tree *a0;
    uint64_t a1;
    std::shared_ptr<MemSafetyProbe28::tree> a00;
    uint64_t a10;
  };

  using _frame = std::variant<_call, _after_zip_collect_in_Leaf,
                              _after_zip_collect_in_Node>;
  List<uint64_t> _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{std::move(acc), t2, &t1});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      List<uint64_t> acc = std::move(_f.acc);
      const MemSafetyProbe28::tree &t2 = _f.t2;
      const MemSafetyProbe28::tree &t1 = *_f.t1;
      if (std::holds_alternative<typename MemSafetyProbe28::tree::Leaf>(t1.v())) {
        _result = std::move(acc);
      } else {
        const auto &[a0, a1, a2] =
            std::get<typename MemSafetyProbe28::tree::Node>(t1.v());
        if (std::holds_alternative<typename MemSafetyProbe28::tree::Leaf>(
                t2.v())) {
          _stack.emplace_back(_after_zip_collect_in_Leaf{crane_raw(a0), a1});
          _stack.emplace_back(
              _call{std::move(acc), tree::leaf(), crane_raw(a2)});
        } else {
          const auto &[a00, a10, a20] =
              std::get<typename MemSafetyProbe28::tree::Node>(t2.v());
          _stack.emplace_back(
              _after_zip_collect_in_Node{crane_raw(a0), a1, a00, a10});
          _stack.emplace_back(_call{std::move(acc), *a20, crane_raw(a2)});
        }
      }
    } else if (std::holds_alternative<_after_zip_collect_in_Leaf>(_popped)) {
      auto _f = std::move(std::get<_after_zip_collect_in_Leaf>(_popped));
      _stack.pop_back();
      const MemSafetyProbe28::tree &a0 = *_f.a0;
      uint64_t a1 = _f.a1;
      _stack.emplace_back(_call{List<uint64_t>::cons(a1, std::move(_result)),
                                tree::leaf(), &a0});
    } else {
      auto _f = std::move(std::get<_after_zip_collect_in_Node>(_popped));
      _stack.pop_back();
      const MemSafetyProbe28::tree &a0 = *_f.a0;
      uint64_t a1 = _f.a1;
      std::shared_ptr<MemSafetyProbe28::tree> a00 = std::move(_f.a00);
      uint64_t a10 = _f.a10;
      _stack.emplace_back(_call{List<uint64_t>::cons(
          a1, List<uint64_t>::cons(a10, std::move(_result))),
                                *a00, &a0});
    }
  }
  return _result;
}

uint64_t MemSafetyProbe28::list_sum(const List<uint64_t> &l) {
  // Explicit stack replaces the non-tail recursion of list_sum: _call frames
  // are pending calls, _after frames resume a caller.
  struct _call {
    const List<uint64_t> *l;
  };

  struct _after_list_sum_in_Cons {
    uint64_t a0;
  };

  using _frame = std::variant<_call, _after_list_sum_in_Cons>;
  uint64_t _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&l});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const List<uint64_t> &l = *_f.l;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
        _stack.emplace_back(_after_list_sum_in_Cons{a0});
        _stack.emplace_back(_call{crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<_after_list_sum_in_Cons>(_popped));
      _stack.pop_back();
      uint64_t a0 = _f.a0;
      _result = (a0 + _result);
    }
  }
  return _result;
}

/// TEST 6: Three-way recursion with non-pointer-safe second tree.
MemSafetyProbe28::tree
MemSafetyProbe28::merge_trees(const MemSafetyProbe28::tree &t1,
                              const MemSafetyProbe28::tree &t2) {
  // Explicit stack replaces the non-tail recursion of merge_trees: _call frames
  // are pending calls, _after frames resume a caller.
  struct _call {
    MemSafetyProbe28::tree t2;
    const MemSafetyProbe28::tree *t1;
  };

  struct _after_merge_trees_in_Leaf {
    uint64_t a1;
    const MemSafetyProbe28::tree *a2;
  };

  struct _after_merge_trees_in_Leaf_2 {
    uint64_t a1;
    MemSafetyProbe28::tree _tmp2;
  };

  struct _after_merge_trees_in_Node {
    uint64_t a1;
    const MemSafetyProbe28::tree *a2;
    uint64_t a10;
    std::shared_ptr<MemSafetyProbe28::tree> a20;
  };

  struct _after_merge_trees_in_Node_2 {
    uint64_t a1;
    uint64_t a10;
    MemSafetyProbe28::tree _tmp4;
  };

  using _frame = std::variant<
      _call, _after_merge_trees_in_Leaf, _after_merge_trees_in_Leaf_2,
      _after_merge_trees_in_Node, _after_merge_trees_in_Node_2>;
  MemSafetyProbe28::tree _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{t2, &t1});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      MemSafetyProbe28::tree t2 = std::move(_f.t2);
      const MemSafetyProbe28::tree &t1 = *_f.t1;
      if (std::holds_alternative<typename MemSafetyProbe28::tree::Leaf>(t1.v())) {
        _result = std::move(t2);
      } else {
        const auto &[a0, a1, a2] =
            std::get<typename MemSafetyProbe28::tree::Node>(t1.v());
        if (std::holds_alternative<typename MemSafetyProbe28::tree::Leaf>(
                t2.v_mut())) {
          _stack.emplace_back(_after_merge_trees_in_Leaf{a1, crane_raw(a2)});
          _stack.emplace_back(_call{tree::leaf(), crane_raw(a0)});
        } else {
          auto &[a00, a10, a20] =
              std::get<typename MemSafetyProbe28::tree::Node>(t2.v_mut());
          _stack.emplace_back(
              _after_merge_trees_in_Node{a1, crane_raw(a2), a10, a20});
          _stack.emplace_back(_call{*a00, crane_raw(a0)});
        }
      }
    } else if (std::holds_alternative<_after_merge_trees_in_Leaf>(_popped)) {
      auto _f = std::move(std::get<_after_merge_trees_in_Leaf>(_popped));
      _stack.pop_back();
      uint64_t a1 = _f.a1;
      const MemSafetyProbe28::tree &a2 = *_f.a2;
      _stack.emplace_back(_after_merge_trees_in_Leaf_2{a1, std::move(_result)});
      _stack.emplace_back(_call{tree::leaf(), &a2});
    } else if (std::holds_alternative<_after_merge_trees_in_Leaf_2>(_popped)) {
      auto _f = std::move(std::get<_after_merge_trees_in_Leaf_2>(_popped));
      _stack.pop_back();
      uint64_t a1 = _f.a1;
      _result = tree::node(std::move(_f._tmp2), a1, std::move(_result));
    } else if (std::holds_alternative<_after_merge_trees_in_Node>(_popped)) {
      auto _f = std::move(std::get<_after_merge_trees_in_Node>(_popped));
      _stack.pop_back();
      uint64_t a1 = _f.a1;
      const MemSafetyProbe28::tree &a2 = *_f.a2;
      uint64_t a10 = _f.a10;
      std::shared_ptr<MemSafetyProbe28::tree> a20 = std::move(_f.a20);
      _stack.emplace_back(
          _after_merge_trees_in_Node_2{a1, a10, std::move(_result)});
      _stack.emplace_back(_call{*a20, &a2});
    } else {
      auto _f = std::move(std::get<_after_merge_trees_in_Node_2>(_popped));
      _stack.pop_back();
      uint64_t a1 = _f.a1;
      uint64_t a10 = _f.a10;
      _result = tree::node(std::move(_f._tmp4), (a1 + a10), std::move(_result));
    }
  }
  return _result;
}

/// TEST 7: Deep trees to stress the optimization.
MemSafetyProbe28::tree MemSafetyProbe28::build_balanced(uint64_t n) {
  // Explicit stack replaces the non-tail recursion of build_balanced: _call
  // frames are pending calls, _after frames resume a caller.
  struct _call {
    uint64_t n;
  };

  struct _after_build_balanced_in_S {
    uint64_t n;
    uint64_t n_;
  };

  struct _after_build_balanced_in_S_2 {
    uint64_t n;
    MemSafetyProbe28::tree _tmp2;
  };

  using _frame = std::variant<_call, _after_build_balanced_in_S,
                              _after_build_balanced_in_S_2>;
  MemSafetyProbe28::tree _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{n});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      uint64_t n = _f.n;
      if (n <= 0) {
        _result = tree::leaf();
      } else {
        uint64_t n_ = n - 1;
        _stack.emplace_back(_after_build_balanced_in_S{n, n_});
        _stack.emplace_back(_call{n_});
      }
    } else if (std::holds_alternative<_after_build_balanced_in_S>(_popped)) {
      auto _f = std::move(std::get<_after_build_balanced_in_S>(_popped));
      _stack.pop_back();
      uint64_t n = _f.n;
      uint64_t n_ = _f.n_;
      _stack.emplace_back(_after_build_balanced_in_S_2{n, std::move(_result)});
      _stack.emplace_back(_call{n_});
    } else {
      auto _f = std::move(std::get<_after_build_balanced_in_S_2>(_popped));
      _stack.pop_back();
      uint64_t n = _f.n;
      _result = tree::node(std::move(_f._tmp2), n, std::move(_result));
    }
  }
  return _result;
}
