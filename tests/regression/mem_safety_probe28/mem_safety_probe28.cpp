#include "mem_safety_probe28.h"

uint64_t MemSafetyProbe28::tree_sum(
    const MemSafetyProbe28::tree
        &t) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const MemSafetyProbe28::tree *t;
  };

  /// _After_Node: saves [a0, a1], dispatches next recursive call.
  struct _After_Node {
    const MemSafetyProbe28::tree *a0;
    uint64_t a1;
  };

  /// _Combine_Node: receives partial results, combines with _result from final
  /// call.
  struct _Combine_Node {
    uint64_t _result;
    uint64_t a1;
  };

  using _Frame = std::variant<_Enter, _After_Node, _Combine_Node>;
  uint64_t _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&t});
  /// Loopified tree_sum: _Enter -> _After_Node -> _Combine_Node.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const MemSafetyProbe28::tree &t = *_f.t;
      if (std::holds_alternative<typename MemSafetyProbe28::tree::Leaf>(
              t.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1, a2] =
            std::get<typename MemSafetyProbe28::tree::Node>(t.v());
        _stack.emplace_back(_After_Node{a0.get(), a1});
        _stack.emplace_back(_Enter{a2.get()});
      }
    } else if (std::holds_alternative<_After_Node>(_frame)) {
      auto _f = std::move(std::get<_After_Node>(_frame));
      _stack.emplace_back(_Combine_Node{_result, _f.a1});
      _stack.emplace_back(_Enter{_f.a0});
    } else {
      auto _f = std::move(std::get<_Combine_Node>(_frame));
      _result = ((std::move(_result) + _f.a1) + std::move(_f._result));
    }
  }
  return _result;
}

uint64_t MemSafetyProbe28::tree_depth(
    const MemSafetyProbe28::tree
        &t) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const MemSafetyProbe28::tree *t;
  };

  /// _After_Node: saves [a0, _s1], dispatches next recursive call.
  struct _After_Node {
    const MemSafetyProbe28::tree *a0;
    decltype(UINT64_C(1)) _s1;
  };

  /// _Combine_Node: receives partial results, combines with _result from final
  /// call.
  struct _Combine_Node {
    uint64_t _result;
    decltype(UINT64_C(1)) _s1;
  };

  using _Frame = std::variant<_Enter, _After_Node, _Combine_Node>;
  uint64_t _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&t});
  /// Loopified tree_depth: _Enter -> _After_Node -> _Combine_Node.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const MemSafetyProbe28::tree &t = *_f.t;
      if (std::holds_alternative<typename MemSafetyProbe28::tree::Leaf>(
              t.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1, a2] =
            std::get<typename MemSafetyProbe28::tree::Node>(t.v());
        _stack.emplace_back(_After_Node{a0.get(), UINT64_C(1)});
        _stack.emplace_back(_Enter{a2.get()});
      }
    } else if (std::holds_alternative<_After_Node>(_frame)) {
      auto _f = std::move(std::get<_After_Node>(_frame));
      _stack.emplace_back(_Combine_Node{_result, _f._s1});
      _stack.emplace_back(_Enter{_f.a0});
    } else {
      auto _f = std::move(std::get<_Combine_Node>(_frame));
      _result = (_f._s1 + std::max(std::move(_result), std::move(_f._result)));
    }
  }
  return _result;
}

/// TEST 1: zip_trees - Two tree params, t1 structural, t2 non-structural.
/// t2 is NOT pointer-safe because some calls pass Leaf (not CPPderef).
/// In the Node/Node branch, t2's children are used for recursion AND
/// tree_sum t2 uses the whole tree. If the optimization moves *(l2),
/// tree_sum t2 might see corrupted data.
uint64_t MemSafetyProbe28::zip_trees(
    const MemSafetyProbe28::tree &t1,
    const MemSafetyProbe28::tree
        &t2) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    MemSafetyProbe28::tree t2;
    const MemSafetyProbe28::tree *t1;
  };

  /// _After_Leaf: saves [_s0, a0, a1], dispatches next recursive call.
  struct _After_Leaf {
    decltype(tree::leaf()) _s0;
    const MemSafetyProbe28::tree *a0;
    uint64_t a1;
  };

  /// _After_Node: saves [a00, a0, a10, a1, t2], dispatches next recursive call.
  struct _After_Node {
    MemSafetyProbe28::tree a00;
    const MemSafetyProbe28::tree *a0;
    uint64_t a10;
    uint64_t a1;
    decltype(tree_sum(std::declval<const MemSafetyProbe28::tree &>())) t2;
  };

  /// _Combine_Leaf: receives partial results, combines with _result from final
  /// call.
  struct _Combine_Leaf {
    uint64_t _result;
    uint64_t a1;
  };

  /// _Combine_Node: receives partial results, combines with _result from final
  /// call.
  struct _Combine_Node {
    uint64_t _result;
    uint64_t a10;
    uint64_t a1;
    decltype(tree_sum(std::declval<const MemSafetyProbe28::tree &>())) t2;
  };

  using _Frame = std::variant<_Enter, _After_Leaf, _After_Node, _Combine_Leaf,
                              _Combine_Node>;
  uint64_t _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{t2, &t1});
  /// Loopified zip_trees: _Enter -> _After_Leaf -> _After_Node -> _Combine_Leaf
  /// -> _Combine_Node.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const MemSafetyProbe28::tree &t2 = _f.t2;
      const MemSafetyProbe28::tree &t1 = *_f.t1;
      if (std::holds_alternative<typename MemSafetyProbe28::tree::Leaf>(
              t1.v())) {
        _result = tree_sum(t2);
      } else {
        const auto &[a0, a1, a2] =
            std::get<typename MemSafetyProbe28::tree::Node>(t1.v());
        if (std::holds_alternative<typename MemSafetyProbe28::tree::Leaf>(
                t2.v())) {
          _stack.emplace_back(_After_Leaf{tree::leaf(), a0.get(), a1});
          _stack.emplace_back(_Enter{tree::leaf(), a2.get()});
        } else {
          const auto &[a00, a10, a20] =
              std::get<typename MemSafetyProbe28::tree::Node>(t2.v());
          _stack.emplace_back(
              _After_Node{*a00, a0.get(), a10, a1, tree_sum(t2)});
          _stack.emplace_back(_Enter{std::move(*a20), a2.get()});
        }
      }
    } else if (std::holds_alternative<_After_Leaf>(_frame)) {
      auto _f = std::move(std::get<_After_Leaf>(_frame));
      _stack.emplace_back(_Combine_Leaf{_result, _f.a1});
      _stack.emplace_back(_Enter{std::move(_f._s0), _f.a0});
    } else if (std::holds_alternative<_After_Node>(_frame)) {
      auto _f = std::move(std::get<_After_Node>(_frame));
      _stack.emplace_back(_Combine_Node{_result, _f.a10, _f.a1, _f.t2});
      _stack.emplace_back(_Enter{std::move(_f.a00), _f.a0});
    } else if (std::holds_alternative<_Combine_Leaf>(_frame)) {
      auto _f = std::move(std::get<_Combine_Leaf>(_frame));
      _result = ((_f.a1 + std::move(_result)) + std::move(_f._result));
    } else {
      auto _f = std::move(std::get<_Combine_Node>(_frame));
      _result =
          ((((std::move(_result) + _f.a1) + _f.a10) + std::move(_f._result)) +
           _f.t2);
    }
  }
  return _result;
}

/// TEST 2: zip_depth - Similar but uses tree_depth on t2.
/// Tests a different tree traversal on the non-pointer-safe param.
uint64_t MemSafetyProbe28::zip_depth(
    const MemSafetyProbe28::tree &t1,
    const MemSafetyProbe28::tree
        &t2) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    MemSafetyProbe28::tree t2;
    const MemSafetyProbe28::tree *t1;
  };

  /// _After_Leaf: saves [_s0, a0, a1], dispatches next recursive call.
  struct _After_Leaf {
    decltype(tree::leaf()) _s0;
    const MemSafetyProbe28::tree *a0;
    uint64_t a1;
  };

  /// _After_Node: saves [a00, a0, t2], dispatches next recursive call.
  struct _After_Node {
    MemSafetyProbe28::tree a00;
    const MemSafetyProbe28::tree *a0;
    decltype(tree_depth(std::declval<const MemSafetyProbe28::tree &>())) t2;
  };

  /// _Combine_Leaf: receives partial results, combines with _result from final
  /// call.
  struct _Combine_Leaf {
    uint64_t _result;
    uint64_t a1;
  };

  /// _Combine_Node: receives partial results, combines with _result from final
  /// call.
  struct _Combine_Node {
    uint64_t _result;
    decltype(tree_depth(std::declval<const MemSafetyProbe28::tree &>())) t2;
  };

  using _Frame = std::variant<_Enter, _After_Leaf, _After_Node, _Combine_Leaf,
                              _Combine_Node>;
  uint64_t _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{t2, &t1});
  /// Loopified zip_depth: _Enter -> _After_Leaf -> _After_Node -> _Combine_Leaf
  /// -> _Combine_Node.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const MemSafetyProbe28::tree &t2 = _f.t2;
      const MemSafetyProbe28::tree &t1 = *_f.t1;
      if (std::holds_alternative<typename MemSafetyProbe28::tree::Leaf>(
              t1.v())) {
        _result = tree_depth(t2);
      } else {
        const auto &[a0, a1, a2] =
            std::get<typename MemSafetyProbe28::tree::Node>(t1.v());
        if (std::holds_alternative<typename MemSafetyProbe28::tree::Leaf>(
                t2.v())) {
          _stack.emplace_back(_After_Leaf{tree::leaf(), a0.get(), a1});
          _stack.emplace_back(_Enter{tree::leaf(), a2.get()});
        } else {
          const auto &[a00, a10, a20] =
              std::get<typename MemSafetyProbe28::tree::Node>(t2.v());
          _stack.emplace_back(_After_Node{*a00, a0.get(), tree_depth(t2)});
          _stack.emplace_back(_Enter{std::move(*a20), a2.get()});
        }
      }
    } else if (std::holds_alternative<_After_Leaf>(_frame)) {
      auto _f = std::move(std::get<_After_Leaf>(_frame));
      _stack.emplace_back(_Combine_Leaf{_result, _f.a1});
      _stack.emplace_back(_Enter{std::move(_f._s0), _f.a0});
    } else if (std::holds_alternative<_After_Node>(_frame)) {
      auto _f = std::move(std::get<_After_Node>(_frame));
      _stack.emplace_back(_Combine_Node{_result, _f.t2});
      _stack.emplace_back(_Enter{std::move(_f.a00), _f.a0});
    } else if (std::holds_alternative<_Combine_Leaf>(_frame)) {
      auto _f = std::move(std::get<_Combine_Leaf>(_frame));
      _result = ((_f.a1 + std::move(_result)) + std::move(_f._result));
    } else {
      auto _f = std::move(std::get<_Combine_Node>(_frame));
      _result = ((std::move(_result) + _f.t2) + std::move(_f._result));
    }
  }
  return _result;
}

/// TEST 3: zip_and_build - Recurse and also construct using t2's children.
/// t2's left child is used for recursion AND returned as part of result.
uint64_t MemSafetyProbe28::zip_and_sum(
    const MemSafetyProbe28::tree &t1,
    const MemSafetyProbe28::tree
        &t2) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    MemSafetyProbe28::tree t2;
    const MemSafetyProbe28::tree *t1;
  };

  /// _After_Leaf: saves [_s0, a0, a1], dispatches next recursive call.
  struct _After_Leaf {
    decltype(tree::leaf()) _s0;
    const MemSafetyProbe28::tree *a0;
    uint64_t a1;
  };

  /// _After_Node: saves [a00, a0, a10, _s3, _s4], dispatches next recursive
  /// call.
  struct _After_Node {
    MemSafetyProbe28::tree a00;
    const MemSafetyProbe28::tree *a0;
    uint64_t a10;
    decltype(tree_sum(
        *(std::declval<std::shared_ptr<MemSafetyProbe28::tree> &>()))) _s3;
    decltype(tree_sum(
        *(std::declval<std::shared_ptr<MemSafetyProbe28::tree> &>()))) _s4;
  };

  /// _Combine_Leaf: receives partial results, combines with _result from final
  /// call.
  struct _Combine_Leaf {
    uint64_t _result;
    uint64_t a1;
  };

  /// _Combine_Node: receives partial results, combines with _result from final
  /// call.
  struct _Combine_Node {
    uint64_t _result;
    uint64_t a10;
    decltype(tree_sum(
        *(std::declval<std::shared_ptr<MemSafetyProbe28::tree> &>()))) _s2;
    decltype(tree_sum(
        *(std::declval<std::shared_ptr<MemSafetyProbe28::tree> &>()))) _s3;
  };

  using _Frame = std::variant<_Enter, _After_Leaf, _After_Node, _Combine_Leaf,
                              _Combine_Node>;
  uint64_t _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{t2, &t1});
  /// Loopified zip_and_sum: _Enter -> _After_Leaf -> _After_Node ->
  /// _Combine_Leaf -> _Combine_Node.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const MemSafetyProbe28::tree &t2 = _f.t2;
      const MemSafetyProbe28::tree &t1 = *_f.t1;
      if (std::holds_alternative<typename MemSafetyProbe28::tree::Leaf>(
              t1.v())) {
        _result = tree_sum(t2);
      } else {
        const auto &[a0, a1, a2] =
            std::get<typename MemSafetyProbe28::tree::Node>(t1.v());
        if (std::holds_alternative<typename MemSafetyProbe28::tree::Leaf>(
                t2.v())) {
          _stack.emplace_back(_After_Leaf{tree::leaf(), a0.get(), a1});
          _stack.emplace_back(_Enter{tree::leaf(), a2.get()});
        } else {
          const auto &[a00, a10, a20] =
              std::get<typename MemSafetyProbe28::tree::Node>(t2.v());
          _stack.emplace_back(
              _After_Node{*a00, a0.get(), a10, tree_sum(*a00), tree_sum(*a20)});
          _stack.emplace_back(_Enter{std::move(*a20), a2.get()});
        }
      }
    } else if (std::holds_alternative<_After_Leaf>(_frame)) {
      auto _f = std::move(std::get<_After_Leaf>(_frame));
      _stack.emplace_back(_Combine_Leaf{_result, _f.a1});
      _stack.emplace_back(_Enter{std::move(_f._s0), _f.a0});
    } else if (std::holds_alternative<_After_Node>(_frame)) {
      auto _f = std::move(std::get<_After_Node>(_frame));
      _stack.emplace_back(_Combine_Node{_result, _f.a10, _f._s3, _f._s4});
      _stack.emplace_back(_Enter{std::move(_f.a00), _f.a0});
    } else if (std::holds_alternative<_Combine_Leaf>(_frame)) {
      auto _f = std::move(std::get<_Combine_Leaf>(_frame));
      _result = ((std::move(_result) + _f.a1) + std::move(_f._result));
    } else {
      auto _f = std::move(std::get<_Combine_Node>(_frame));
      _result =
          ((((std::move(_result) + _f.a10) + std::move(_f._result)) + _f._s2) +
           _f._s3);
    }
  }
  return _result;
}

/// TEST 4: double_zip - Both t1 and t2 are trees, but t2 is used
/// in a different way for each call. Makes t2 non-pointer-safe.
uint64_t MemSafetyProbe28::double_zip(
    const MemSafetyProbe28::tree &t1,
    const MemSafetyProbe28::tree
        &t2) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const MemSafetyProbe28::tree *t2;
    const MemSafetyProbe28::tree *t1;
  };

  /// _After_Leaf: saves [t2, a0, a1], dispatches next recursive call.
  struct _After_Leaf {
    const MemSafetyProbe28::tree *t2;
    const MemSafetyProbe28::tree *a0;
    uint64_t a1;
  };

  /// _After_Node: saves [a00, a0, a10, t2], dispatches next recursive call.
  struct _After_Node {
    const MemSafetyProbe28::tree *a00;
    const MemSafetyProbe28::tree *a0;
    uint64_t a10;
    decltype(tree_sum(std::declval<const MemSafetyProbe28::tree &>())) t2;
  };

  /// _Combine_Leaf: receives partial results, combines with _result from final
  /// call.
  struct _Combine_Leaf {
    uint64_t _result;
    uint64_t a1;
  };

  /// _Combine_Node: receives partial results, combines with _result from final
  /// call.
  struct _Combine_Node {
    uint64_t _result;
    uint64_t a10;
    decltype(tree_sum(std::declval<const MemSafetyProbe28::tree &>())) t2;
  };

  using _Frame = std::variant<_Enter, _After_Leaf, _After_Node, _Combine_Leaf,
                              _Combine_Node>;
  uint64_t _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&t2, &t1});
  /// Loopified double_zip: _Enter -> _After_Leaf -> _After_Node ->
  /// _Combine_Leaf -> _Combine_Node.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const MemSafetyProbe28::tree &t2 = *_f.t2;
      const MemSafetyProbe28::tree &t1 = *_f.t1;
      if (std::holds_alternative<typename MemSafetyProbe28::tree::Leaf>(
              t1.v())) {
        _result = tree_sum(t2);
      } else {
        const auto &[a0, a1, a2] =
            std::get<typename MemSafetyProbe28::tree::Node>(t1.v());
        if (std::holds_alternative<typename MemSafetyProbe28::tree::Leaf>(
                t2.v())) {
          _stack.emplace_back(_After_Leaf{&t2, a0.get(), a1});
          _stack.emplace_back(_Enter{&t2, a2.get()});
        } else {
          const auto &[a00, a10, a20] =
              std::get<typename MemSafetyProbe28::tree::Node>(t2.v());
          _stack.emplace_back(
              _After_Node{a00.get(), a0.get(), a10, tree_sum(t2)});
          _stack.emplace_back(_Enter{a20.get(), a2.get()});
        }
      }
    } else if (std::holds_alternative<_After_Leaf>(_frame)) {
      auto _f = std::move(std::get<_After_Leaf>(_frame));
      _stack.emplace_back(_Combine_Leaf{_result, _f.a1});
      _stack.emplace_back(_Enter{_f.t2, _f.a0});
    } else if (std::holds_alternative<_After_Node>(_frame)) {
      auto _f = std::move(std::get<_After_Node>(_frame));
      _stack.emplace_back(_Combine_Node{_result, _f.a10, _f.t2});
      _stack.emplace_back(_Enter{_f.a00, _f.a0});
    } else if (std::holds_alternative<_Combine_Leaf>(_frame)) {
      auto _f = std::move(std::get<_Combine_Leaf>(_frame));
      _result = ((std::move(_result) + _f.a1) + std::move(_f._result));
    } else {
      auto _f = std::move(std::get<_Combine_Node>(_frame));
      _result =
          (((std::move(_result) + std::move(_f._result)) + _f.a10) + _f.t2);
    }
  }
  return _result;
}

/// TEST 5: zip with list accumulator. t2 is tree, acc is list.
/// t2 non-pointer-safe due to Leaf in some calls.
List<uint64_t> MemSafetyProbe28::zip_collect(
    const MemSafetyProbe28::tree &t1, const MemSafetyProbe28::tree &t2,
    List<uint64_t>
        acc) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    List<uint64_t> acc;
    MemSafetyProbe28::tree t2;
    const MemSafetyProbe28::tree *t1;
  };

  /// _Resume_Leaf: saves [_s0, a0], resumes after recursive call with _result.
  struct _Resume_Leaf {
    decltype(tree::leaf()) _s0;
    const MemSafetyProbe28::tree *a0;
  };

  /// _Resume_Leaf_1: saves [a1], resumes after recursive call with _result.
  struct _Resume_Leaf_1 {
    uint64_t a1;
  };

  /// _Resume_Node: saves [a00, a0], resumes after recursive call with _result.
  struct _Resume_Node {
    MemSafetyProbe28::tree a00;
    const MemSafetyProbe28::tree *a0;
  };

  /// _Resume_Node_1: saves [a1, a10], resumes after recursive call with
  /// _result.
  struct _Resume_Node_1 {
    uint64_t a1;
    uint64_t a10;
  };

  using _Frame = std::variant<_Enter, _Resume_Leaf, _Resume_Leaf_1,
                              _Resume_Node, _Resume_Node_1>;
  List<uint64_t> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{acc, t2, &t1});
  /// Loopified zip_collect: _Enter -> _Resume_Leaf -> _Resume_Leaf_1 ->
  /// _Resume_Node -> _Resume_Node_1.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      List<uint64_t> acc = std::move(_f.acc);
      const MemSafetyProbe28::tree &t2 = _f.t2;
      const MemSafetyProbe28::tree &t1 = *_f.t1;
      if (std::holds_alternative<typename MemSafetyProbe28::tree::Leaf>(
              t1.v())) {
        _result = std::move(acc);
      } else {
        const auto &[a0, a1, a2] =
            std::get<typename MemSafetyProbe28::tree::Node>(t1.v());
        if (std::holds_alternative<typename MemSafetyProbe28::tree::Leaf>(
                t2.v())) {
          _stack.emplace_back(_Resume_Leaf{tree::leaf(), a0.get()});
          _stack.emplace_back(_Resume_Leaf_1{a1});
          _stack.emplace_back(_Enter{std::move(acc), tree::leaf(), a2.get()});
        } else {
          const auto &[a00, a10, a20] =
              std::get<typename MemSafetyProbe28::tree::Node>(t2.v());
          _stack.emplace_back(_Resume_Node{*a00, a0.get()});
          _stack.emplace_back(_Resume_Node_1{a1, a10});
          _stack.emplace_back(
              _Enter{std::move(acc), std::move(*a20), a2.get()});
        }
      }
    } else if (std::holds_alternative<_Resume_Leaf>(_frame)) {
      auto _f = std::move(std::get<_Resume_Leaf>(_frame));
      _stack.emplace_back(_Enter{std::move(_result), std::move(_f._s0), _f.a0});
    } else if (std::holds_alternative<_Resume_Leaf_1>(_frame)) {
      auto _f = std::move(std::get<_Resume_Leaf_1>(_frame));
      _result = List<uint64_t>::cons(_f.a1, _result);
    } else if (std::holds_alternative<_Resume_Node>(_frame)) {
      auto _f = std::move(std::get<_Resume_Node>(_frame));
      _stack.emplace_back(_Enter{std::move(_result), std::move(_f.a00), _f.a0});
    } else {
      auto _f = std::move(std::get<_Resume_Node_1>(_frame));
      _result =
          List<uint64_t>::cons(_f.a1, List<uint64_t>::cons(_f.a10, _result));
    }
  }
  return _result;
}

uint64_t MemSafetyProbe28::list_sum(
    const List<uint64_t>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<uint64_t> *l;
  };

  /// _Resume_Cons: saves [a0], resumes after recursive call with _result.
  struct _Resume_Cons {
    uint64_t a0;
  };

  using _Frame = std::variant<_Enter, _Resume_Cons>;
  uint64_t _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l});
  /// Loopified list_sum: _Enter -> _Resume_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<uint64_t> &l = *_f.l;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
        _stack.emplace_back(_Resume_Cons{a0});
        _stack.emplace_back(_Enter{a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Resume_Cons>(_frame));
      _result = (_f.a0 + _result);
    }
  }
  return _result;
}

/// TEST 6: Three-way recursion with non-pointer-safe second tree.
MemSafetyProbe28::tree MemSafetyProbe28::merge_trees(
    const MemSafetyProbe28::tree &t1,
    MemSafetyProbe28::tree
        t2) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    MemSafetyProbe28::tree t2;
    const MemSafetyProbe28::tree *t1;
  };

  /// _After_Leaf: saves [_s0, a0, a1], dispatches next recursive call.
  struct _After_Leaf {
    decltype(tree::leaf()) _s0;
    const MemSafetyProbe28::tree *a0;
    uint64_t a1;
  };

  /// _After_Node: saves [a00, a0, _s2], dispatches next recursive call.
  struct _After_Node {
    MemSafetyProbe28::tree a00;
    const MemSafetyProbe28::tree *a0;
    uint64_t _s2;
  };

  /// _Combine_Leaf: receives partial results, combines with _result from final
  /// call.
  struct _Combine_Leaf {
    MemSafetyProbe28::tree _result;
    uint64_t a1;
  };

  /// _Combine_Node: receives partial results, combines with _result from final
  /// call.
  struct _Combine_Node {
    MemSafetyProbe28::tree _result;
    uint64_t _s1;
  };

  using _Frame = std::variant<_Enter, _After_Leaf, _After_Node, _Combine_Leaf,
                              _Combine_Node>;
  MemSafetyProbe28::tree _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{t2, &t1});
  /// Loopified merge_trees: _Enter -> _After_Leaf -> _After_Node ->
  /// _Combine_Leaf -> _Combine_Node.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      MemSafetyProbe28::tree t2 = std::move(_f.t2);
      const MemSafetyProbe28::tree &t1 = *_f.t1;
      if (std::holds_alternative<typename MemSafetyProbe28::tree::Leaf>(
              t1.v())) {
        _result = std::move(t2);
      } else {
        const auto &[a0, a1, a2] =
            std::get<typename MemSafetyProbe28::tree::Node>(t1.v());
        if (std::holds_alternative<typename MemSafetyProbe28::tree::Leaf>(
                t2.v_mut())) {
          _stack.emplace_back(_After_Leaf{tree::leaf(), a0.get(), a1});
          _stack.emplace_back(_Enter{tree::leaf(), a2.get()});
        } else {
          auto &[a00, a10, a20] =
              std::get<typename MemSafetyProbe28::tree::Node>(t2.v_mut());
          _stack.emplace_back(
              _After_Node{*a00, a0.get(), (a1 + std::move(a10))});
          _stack.emplace_back(_Enter{std::move(*a20), a2.get()});
        }
      }
    } else if (std::holds_alternative<_After_Leaf>(_frame)) {
      auto _f = std::move(std::get<_After_Leaf>(_frame));
      _stack.emplace_back(_Combine_Leaf{std::move(_result), _f.a1});
      _stack.emplace_back(_Enter{std::move(_f._s0), _f.a0});
    } else if (std::holds_alternative<_After_Node>(_frame)) {
      auto _f = std::move(std::get<_After_Node>(_frame));
      _stack.emplace_back(_Combine_Node{std::move(_result), _f._s2});
      _stack.emplace_back(_Enter{std::move(_f.a00), _f.a0});
    } else if (std::holds_alternative<_Combine_Leaf>(_frame)) {
      auto _f = std::move(std::get<_Combine_Leaf>(_frame));
      _result = tree::node(std::move(_result), _f.a1, std::move(_f._result));
    } else {
      auto _f = std::move(std::get<_Combine_Node>(_frame));
      _result = tree::node(std::move(_result), _f._s1, std::move(_f._result));
    }
  }
  return _result;
}

/// TEST 7: Deep trees to stress the optimization.
MemSafetyProbe28::tree MemSafetyProbe28::build_balanced(
    uint64_t
        n) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    uint64_t n;
  };

  /// _After_n_: saves [n_, n], dispatches next recursive call.
  struct _After_n_ {
    uint64_t n_;
    uint64_t n;
  };

  /// _Combine_n_: receives partial results, combines with _result from final
  /// call.
  struct _Combine_n_ {
    MemSafetyProbe28::tree _result;
    uint64_t n;
  };

  using _Frame = std::variant<_Enter, _After_n_, _Combine_n_>;
  MemSafetyProbe28::tree _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{n});
  /// Loopified build_balanced: _Enter -> _After_n_ -> _Combine_n_.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      uint64_t n = _f.n;
      if (n <= 0) {
        _result = tree::leaf();
      } else {
        uint64_t n_ = n - 1;
        _stack.emplace_back(_After_n_{n_, n});
        _stack.emplace_back(_Enter{n_});
      }
    } else if (std::holds_alternative<_After_n_>(_frame)) {
      auto _f = std::move(std::get<_After_n_>(_frame));
      _stack.emplace_back(_Combine_n_{std::move(_result), _f.n});
      _stack.emplace_back(_Enter{_f.n_});
    } else {
      auto _f = std::move(std::get<_Combine_n_>(_frame));
      _result = tree::node(std::move(_result), _f.n, std::move(_f._result));
    }
  }
  return _result;
}
