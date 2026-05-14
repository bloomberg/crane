#include "mem_safety_probe28.h"

unsigned int MemSafetyProbe28::tree_sum(
    const MemSafetyProbe28::tree
        &t) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const MemSafetyProbe28::tree *t;
  };

  /// _After_Node: saves [d_a0, d_a1], dispatches next recursive call.
  struct _After_Node {
    const MemSafetyProbe28::tree *d_a0;
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
      const MemSafetyProbe28::tree &t = *(_f.t);
      if (std::holds_alternative<typename MemSafetyProbe28::tree::Leaf>(
              t.v())) {
        _result = 0u;
      } else {
        const auto &[d_a0, d_a1, d_a2] =
            std::get<typename MemSafetyProbe28::tree::Node>(t.v());
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

unsigned int MemSafetyProbe28::tree_depth(
    const MemSafetyProbe28::tree
        &t) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const MemSafetyProbe28::tree *t;
  };

  /// _After_Node: saves [d_a0, _s1], dispatches next recursive call.
  struct _After_Node {
    const MemSafetyProbe28::tree *d_a0;
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
      const MemSafetyProbe28::tree &t = *(_f.t);
      if (std::holds_alternative<typename MemSafetyProbe28::tree::Leaf>(
              t.v())) {
        _result = 0u;
      } else {
        const auto &[d_a0, d_a1, d_a2] =
            std::get<typename MemSafetyProbe28::tree::Node>(t.v());
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

/// TEST 1: zip_trees - Two tree params, t1 structural, t2 non-structural.
/// t2 is NOT pointer-safe because some calls pass Leaf (not CPPderef).
/// In the Node/Node branch, t2's children are used for recursion AND
/// tree_sum t2 uses the whole tree. If the optimization moves *(l2),
/// tree_sum t2 might see corrupted data.
unsigned int MemSafetyProbe28::zip_trees(
    const MemSafetyProbe28::tree &t1,
    const MemSafetyProbe28::tree
        &t2) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    MemSafetyProbe28::tree t2;
    const MemSafetyProbe28::tree *t1;
  };

  /// _After_Leaf: saves [_s0, d_a0, d_a1], dispatches next recursive call.
  struct _After_Leaf {
    decltype(tree::leaf()) _s0;
    const MemSafetyProbe28::tree *d_a0;
    unsigned int d_a1;
  };

  /// _After_Node: saves [d_a00, d_a0, d_a10, d_a1, t2], dispatches next
  /// recursive call.
  struct _After_Node {
    MemSafetyProbe28::tree d_a00;
    const MemSafetyProbe28::tree *d_a0;
    unsigned int d_a10;
    unsigned int d_a1;
    decltype(tree_sum(std::declval<const MemSafetyProbe28::tree &>())) t2;
  };

  /// _Combine_Leaf: receives partial results, combines with _result from final
  /// call.
  struct _Combine_Leaf {
    unsigned int _result;
    unsigned int d_a1;
  };

  /// _Combine_Node: receives partial results, combines with _result from final
  /// call.
  struct _Combine_Node {
    unsigned int _result;
    unsigned int d_a10;
    unsigned int d_a1;
    decltype(tree_sum(std::declval<const MemSafetyProbe28::tree &>())) t2;
  };

  using _Frame = std::variant<_Enter, _After_Leaf, _After_Node, _Combine_Leaf,
                              _Combine_Node>;
  unsigned int _result{};
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
      const MemSafetyProbe28::tree &t1 = *(_f.t1);
      if (std::holds_alternative<typename MemSafetyProbe28::tree::Leaf>(
              t1.v())) {
        _result = tree_sum(t2);
      } else {
        const auto &[d_a0, d_a1, d_a2] =
            std::get<typename MemSafetyProbe28::tree::Node>(t1.v());
        if (std::holds_alternative<typename MemSafetyProbe28::tree::Leaf>(
                t2.v())) {
          _stack.emplace_back(_After_Leaf{tree::leaf(), d_a0.get(), d_a1});
          _stack.emplace_back(_Enter{tree::leaf(), d_a2.get()});
        } else {
          const auto &[d_a00, d_a10, d_a20] =
              std::get<typename MemSafetyProbe28::tree::Node>(t2.v());
          _stack.emplace_back(
              _After_Node{*(d_a00), d_a0.get(), d_a10, d_a1, tree_sum(t2)});
          _stack.emplace_back(_Enter{std::move(*(d_a20)), d_a2.get()});
        }
      }
    } else if (std::holds_alternative<_After_Leaf>(_frame)) {
      auto _f = std::move(std::get<_After_Leaf>(_frame));
      _stack.emplace_back(_Combine_Leaf{_result, _f.d_a1});
      _stack.emplace_back(_Enter{std::move(_f._s0), _f.d_a0});
    } else if (std::holds_alternative<_After_Node>(_frame)) {
      auto _f = std::move(std::get<_After_Node>(_frame));
      _stack.emplace_back(_Combine_Node{_result, _f.d_a10, _f.d_a1, _f.t2});
      _stack.emplace_back(_Enter{std::move(_f.d_a00), _f.d_a0});
    } else if (std::holds_alternative<_Combine_Leaf>(_frame)) {
      auto _f = std::move(std::get<_Combine_Leaf>(_frame));
      _result = ((_f.d_a1 + _result) + _f._result);
    } else {
      auto _f = std::move(std::get<_Combine_Node>(_frame));
      _result = ((((_result + _f.d_a1) + _f.d_a10) + _f._result) + _f.t2);
    }
  }
  return _result;
}

/// TEST 2: zip_depth - Similar but uses tree_depth on t2.
/// Tests a different tree traversal on the non-pointer-safe param.
unsigned int MemSafetyProbe28::zip_depth(
    const MemSafetyProbe28::tree &t1,
    const MemSafetyProbe28::tree
        &t2) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    MemSafetyProbe28::tree t2;
    const MemSafetyProbe28::tree *t1;
  };

  /// _After_Leaf: saves [_s0, d_a0, d_a1], dispatches next recursive call.
  struct _After_Leaf {
    decltype(tree::leaf()) _s0;
    const MemSafetyProbe28::tree *d_a0;
    unsigned int d_a1;
  };

  /// _After_Node: saves [d_a00, d_a0, t2], dispatches next recursive call.
  struct _After_Node {
    MemSafetyProbe28::tree d_a00;
    const MemSafetyProbe28::tree *d_a0;
    decltype(tree_depth(std::declval<const MemSafetyProbe28::tree &>())) t2;
  };

  /// _Combine_Leaf: receives partial results, combines with _result from final
  /// call.
  struct _Combine_Leaf {
    unsigned int _result;
    unsigned int d_a1;
  };

  /// _Combine_Node: receives partial results, combines with _result from final
  /// call.
  struct _Combine_Node {
    unsigned int _result;
    decltype(tree_depth(std::declval<const MemSafetyProbe28::tree &>())) t2;
  };

  using _Frame = std::variant<_Enter, _After_Leaf, _After_Node, _Combine_Leaf,
                              _Combine_Node>;
  unsigned int _result{};
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
      const MemSafetyProbe28::tree &t1 = *(_f.t1);
      if (std::holds_alternative<typename MemSafetyProbe28::tree::Leaf>(
              t1.v())) {
        _result = tree_depth(t2);
      } else {
        const auto &[d_a0, d_a1, d_a2] =
            std::get<typename MemSafetyProbe28::tree::Node>(t1.v());
        if (std::holds_alternative<typename MemSafetyProbe28::tree::Leaf>(
                t2.v())) {
          _stack.emplace_back(_After_Leaf{tree::leaf(), d_a0.get(), d_a1});
          _stack.emplace_back(_Enter{tree::leaf(), d_a2.get()});
        } else {
          const auto &[d_a00, d_a10, d_a20] =
              std::get<typename MemSafetyProbe28::tree::Node>(t2.v());
          _stack.emplace_back(
              _After_Node{*(d_a00), d_a0.get(), tree_depth(t2)});
          _stack.emplace_back(_Enter{std::move(*(d_a20)), d_a2.get()});
        }
      }
    } else if (std::holds_alternative<_After_Leaf>(_frame)) {
      auto _f = std::move(std::get<_After_Leaf>(_frame));
      _stack.emplace_back(_Combine_Leaf{_result, _f.d_a1});
      _stack.emplace_back(_Enter{std::move(_f._s0), _f.d_a0});
    } else if (std::holds_alternative<_After_Node>(_frame)) {
      auto _f = std::move(std::get<_After_Node>(_frame));
      _stack.emplace_back(_Combine_Node{_result, _f.t2});
      _stack.emplace_back(_Enter{std::move(_f.d_a00), _f.d_a0});
    } else if (std::holds_alternative<_Combine_Leaf>(_frame)) {
      auto _f = std::move(std::get<_Combine_Leaf>(_frame));
      _result = ((_f.d_a1 + _result) + _f._result);
    } else {
      auto _f = std::move(std::get<_Combine_Node>(_frame));
      _result = ((_result + _f.t2) + _f._result);
    }
  }
  return _result;
}

/// TEST 3: zip_and_build - Recurse and also construct using t2's children.
/// t2's left child is used for recursion AND returned as part of result.
unsigned int MemSafetyProbe28::zip_and_sum(
    const MemSafetyProbe28::tree &t1,
    const MemSafetyProbe28::tree
        &t2) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    MemSafetyProbe28::tree t2;
    const MemSafetyProbe28::tree *t1;
  };

  /// _After_Leaf: saves [_s0, d_a0, d_a1], dispatches next recursive call.
  struct _After_Leaf {
    decltype(tree::leaf()) _s0;
    const MemSafetyProbe28::tree *d_a0;
    unsigned int d_a1;
  };

  /// _After_Node: saves [d_a00, d_a0, d_a10, _s3, _s4], dispatches next
  /// recursive call.
  struct _After_Node {
    MemSafetyProbe28::tree d_a00;
    const MemSafetyProbe28::tree *d_a0;
    unsigned int d_a10;
    decltype(tree_sum(
        *(std::declval<std::unique_ptr<MemSafetyProbe28::tree> &>()))) _s3;
    decltype(tree_sum(
        *(std::declval<std::unique_ptr<MemSafetyProbe28::tree> &>()))) _s4;
  };

  /// _Combine_Leaf: receives partial results, combines with _result from final
  /// call.
  struct _Combine_Leaf {
    unsigned int _result;
    unsigned int d_a1;
  };

  /// _Combine_Node: receives partial results, combines with _result from final
  /// call.
  struct _Combine_Node {
    unsigned int _result;
    unsigned int d_a10;
    decltype(tree_sum(
        *(std::declval<std::unique_ptr<MemSafetyProbe28::tree> &>()))) _s2;
    decltype(tree_sum(
        *(std::declval<std::unique_ptr<MemSafetyProbe28::tree> &>()))) _s3;
  };

  using _Frame = std::variant<_Enter, _After_Leaf, _After_Node, _Combine_Leaf,
                              _Combine_Node>;
  unsigned int _result{};
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
      const MemSafetyProbe28::tree &t1 = *(_f.t1);
      if (std::holds_alternative<typename MemSafetyProbe28::tree::Leaf>(
              t1.v())) {
        _result = tree_sum(t2);
      } else {
        const auto &[d_a0, d_a1, d_a2] =
            std::get<typename MemSafetyProbe28::tree::Node>(t1.v());
        if (std::holds_alternative<typename MemSafetyProbe28::tree::Leaf>(
                t2.v())) {
          _stack.emplace_back(_After_Leaf{tree::leaf(), d_a0.get(), d_a1});
          _stack.emplace_back(_Enter{tree::leaf(), d_a2.get()});
        } else {
          const auto &[d_a00, d_a10, d_a20] =
              std::get<typename MemSafetyProbe28::tree::Node>(t2.v());
          _stack.emplace_back(_After_Node{*(d_a00), d_a0.get(), d_a10,
                                          tree_sum(*(d_a00)),
                                          tree_sum(*(d_a20))});
          _stack.emplace_back(_Enter{std::move(*(d_a20)), d_a2.get()});
        }
      }
    } else if (std::holds_alternative<_After_Leaf>(_frame)) {
      auto _f = std::move(std::get<_After_Leaf>(_frame));
      _stack.emplace_back(_Combine_Leaf{_result, _f.d_a1});
      _stack.emplace_back(_Enter{std::move(_f._s0), _f.d_a0});
    } else if (std::holds_alternative<_After_Node>(_frame)) {
      auto _f = std::move(std::get<_After_Node>(_frame));
      _stack.emplace_back(_Combine_Node{_result, _f.d_a10, _f._s3, _f._s4});
      _stack.emplace_back(_Enter{std::move(_f.d_a00), _f.d_a0});
    } else if (std::holds_alternative<_Combine_Leaf>(_frame)) {
      auto _f = std::move(std::get<_Combine_Leaf>(_frame));
      _result = ((_result + _f.d_a1) + _f._result);
    } else {
      auto _f = std::move(std::get<_Combine_Node>(_frame));
      _result = ((((_result + _f.d_a10) + _f._result) + _f._s2) + _f._s3);
    }
  }
  return _result;
}

/// TEST 4: double_zip - Both t1 and t2 are trees, but t2 is used
/// in a different way for each call. Makes t2 non-pointer-safe.
unsigned int MemSafetyProbe28::double_zip(
    const MemSafetyProbe28::tree &t1,
    const MemSafetyProbe28::tree
        &t2) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const MemSafetyProbe28::tree *t2;
    const MemSafetyProbe28::tree *t1;
  };

  /// _After_Leaf: saves [t2, d_a0, d_a1], dispatches next recursive call.
  struct _After_Leaf {
    const MemSafetyProbe28::tree *t2;
    const MemSafetyProbe28::tree *d_a0;
    unsigned int d_a1;
  };

  /// _After_Node: saves [d_a00, d_a0, d_a10, t2], dispatches next recursive
  /// call.
  struct _After_Node {
    const MemSafetyProbe28::tree *d_a00;
    const MemSafetyProbe28::tree *d_a0;
    unsigned int d_a10;
    decltype(tree_sum(std::declval<const MemSafetyProbe28::tree &>())) t2;
  };

  /// _Combine_Leaf: receives partial results, combines with _result from final
  /// call.
  struct _Combine_Leaf {
    unsigned int _result;
    unsigned int d_a1;
  };

  /// _Combine_Node: receives partial results, combines with _result from final
  /// call.
  struct _Combine_Node {
    unsigned int _result;
    unsigned int d_a10;
    decltype(tree_sum(std::declval<const MemSafetyProbe28::tree &>())) t2;
  };

  using _Frame = std::variant<_Enter, _After_Leaf, _After_Node, _Combine_Leaf,
                              _Combine_Node>;
  unsigned int _result{};
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
      const MemSafetyProbe28::tree &t2 = *(_f.t2);
      const MemSafetyProbe28::tree &t1 = *(_f.t1);
      if (std::holds_alternative<typename MemSafetyProbe28::tree::Leaf>(
              t1.v())) {
        _result = tree_sum(t2);
      } else {
        const auto &[d_a0, d_a1, d_a2] =
            std::get<typename MemSafetyProbe28::tree::Node>(t1.v());
        if (std::holds_alternative<typename MemSafetyProbe28::tree::Leaf>(
                t2.v())) {
          _stack.emplace_back(_After_Leaf{&t2, d_a0.get(), d_a1});
          _stack.emplace_back(_Enter{&t2, d_a2.get()});
        } else {
          const auto &[d_a00, d_a10, d_a20] =
              std::get<typename MemSafetyProbe28::tree::Node>(t2.v());
          _stack.emplace_back(
              _After_Node{d_a00.get(), d_a0.get(), d_a10, tree_sum(t2)});
          _stack.emplace_back(_Enter{d_a20.get(), d_a2.get()});
        }
      }
    } else if (std::holds_alternative<_After_Leaf>(_frame)) {
      auto _f = std::move(std::get<_After_Leaf>(_frame));
      _stack.emplace_back(_Combine_Leaf{_result, _f.d_a1});
      _stack.emplace_back(_Enter{_f.t2, _f.d_a0});
    } else if (std::holds_alternative<_After_Node>(_frame)) {
      auto _f = std::move(std::get<_After_Node>(_frame));
      _stack.emplace_back(_Combine_Node{_result, _f.d_a10, _f.t2});
      _stack.emplace_back(_Enter{_f.d_a00, _f.d_a0});
    } else if (std::holds_alternative<_Combine_Leaf>(_frame)) {
      auto _f = std::move(std::get<_Combine_Leaf>(_frame));
      _result = ((_result + _f.d_a1) + _f._result);
    } else {
      auto _f = std::move(std::get<_Combine_Node>(_frame));
      _result = (((_result + _f._result) + _f.d_a10) + _f.t2);
    }
  }
  return _result;
}

/// TEST 5: zip with list accumulator. t2 is tree, acc is list.
/// t2 non-pointer-safe due to Leaf in some calls.
List<unsigned int> MemSafetyProbe28::zip_collect(
    const MemSafetyProbe28::tree &t1, const MemSafetyProbe28::tree &t2,
    List<unsigned int>
        acc) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    List<unsigned int> acc;
    MemSafetyProbe28::tree t2;
    const MemSafetyProbe28::tree *t1;
  };

  /// _Resume_Leaf: saves [_s0, d_a0], resumes after recursive call with
  /// _result.
  struct _Resume_Leaf {
    decltype(tree::leaf()) _s0;
    const MemSafetyProbe28::tree *d_a0;
  };

  /// _Resume_Leaf_1: saves [d_a1], resumes after recursive call with _result.
  struct _Resume_Leaf_1 {
    unsigned int d_a1;
  };

  /// _Resume_Node: saves [d_a00, d_a0], resumes after recursive call with
  /// _result.
  struct _Resume_Node {
    MemSafetyProbe28::tree d_a00;
    const MemSafetyProbe28::tree *d_a0;
  };

  /// _Resume_Node_1: saves [d_a1, d_a10], resumes after recursive call with
  /// _result.
  struct _Resume_Node_1 {
    unsigned int d_a1;
    unsigned int d_a10;
  };

  using _Frame = std::variant<_Enter, _Resume_Leaf, _Resume_Leaf_1,
                              _Resume_Node, _Resume_Node_1>;
  List<unsigned int> _result{};
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
      List<unsigned int> acc = std::move(_f.acc);
      const MemSafetyProbe28::tree &t2 = _f.t2;
      const MemSafetyProbe28::tree &t1 = *(_f.t1);
      if (std::holds_alternative<typename MemSafetyProbe28::tree::Leaf>(
              t1.v())) {
        _result = std::move(acc);
      } else {
        const auto &[d_a0, d_a1, d_a2] =
            std::get<typename MemSafetyProbe28::tree::Node>(t1.v());
        if (std::holds_alternative<typename MemSafetyProbe28::tree::Leaf>(
                t2.v())) {
          _stack.emplace_back(_Resume_Leaf{tree::leaf(), d_a0.get()});
          _stack.emplace_back(_Resume_Leaf_1{d_a1});
          _stack.emplace_back(_Enter{std::move(acc), tree::leaf(), d_a2.get()});
        } else {
          const auto &[d_a00, d_a10, d_a20] =
              std::get<typename MemSafetyProbe28::tree::Node>(t2.v());
          _stack.emplace_back(_Resume_Node{*(d_a00), d_a0.get()});
          _stack.emplace_back(_Resume_Node_1{d_a1, d_a10});
          _stack.emplace_back(
              _Enter{std::move(acc), std::move(*(d_a20)), d_a2.get()});
        }
      }
    } else if (std::holds_alternative<_Resume_Leaf>(_frame)) {
      auto _f = std::move(std::get<_Resume_Leaf>(_frame));
      _stack.emplace_back(
          _Enter{std::move(_result), std::move(_f._s0), _f.d_a0});
    } else if (std::holds_alternative<_Resume_Leaf_1>(_frame)) {
      auto _f = std::move(std::get<_Resume_Leaf_1>(_frame));
      _result = List<unsigned int>::cons(_f.d_a1, _result);
    } else if (std::holds_alternative<_Resume_Node>(_frame)) {
      auto _f = std::move(std::get<_Resume_Node>(_frame));
      _stack.emplace_back(
          _Enter{std::move(_result), std::move(_f.d_a00), _f.d_a0});
    } else {
      auto _f = std::move(std::get<_Resume_Node_1>(_frame));
      _result = List<unsigned int>::cons(
          _f.d_a1, List<unsigned int>::cons(_f.d_a10, _result));
    }
  }
  return _result;
}

unsigned int MemSafetyProbe28::list_sum(
    const List<unsigned int>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<unsigned int> *l;
  };

  /// _Resume_Cons: saves [d_a0], resumes after recursive call with _result.
  struct _Resume_Cons {
    unsigned int d_a0;
  };

  using _Frame = std::variant<_Enter, _Resume_Cons>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l});
  /// Loopified list_sum: _Enter -> _Resume_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<unsigned int> &l = *(_f.l);
      if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
        _result = 0u;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<unsigned int>::Cons>(l.v());
        _stack.emplace_back(_Resume_Cons{d_a0});
        _stack.emplace_back(_Enter{d_a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Resume_Cons>(_frame));
      _result = (_f.d_a0 + _result);
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

  /// _After_Leaf: saves [_s0, d_a0, d_a1], dispatches next recursive call.
  struct _After_Leaf {
    decltype(tree::leaf()) _s0;
    const MemSafetyProbe28::tree *d_a0;
    unsigned int d_a1;
  };

  /// _After_Node: saves [d_a00, d_a0, _s2], dispatches next recursive call.
  struct _After_Node {
    MemSafetyProbe28::tree d_a00;
    const MemSafetyProbe28::tree *d_a0;
    unsigned int _s2;
  };

  /// _Combine_Leaf: receives partial results, combines with _result from final
  /// call.
  struct _Combine_Leaf {
    MemSafetyProbe28::tree _result;
    unsigned int d_a1;
  };

  /// _Combine_Node: receives partial results, combines with _result from final
  /// call.
  struct _Combine_Node {
    MemSafetyProbe28::tree _result;
    unsigned int _s1;
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
      const MemSafetyProbe28::tree &t1 = *(_f.t1);
      if (std::holds_alternative<typename MemSafetyProbe28::tree::Leaf>(
              t1.v())) {
        _result = std::move(t2);
      } else {
        const auto &[d_a0, d_a1, d_a2] =
            std::get<typename MemSafetyProbe28::tree::Node>(t1.v());
        if (std::holds_alternative<typename MemSafetyProbe28::tree::Leaf>(
                t2.v_mut())) {
          _stack.emplace_back(_After_Leaf{tree::leaf(), d_a0.get(), d_a1});
          _stack.emplace_back(_Enter{tree::leaf(), d_a2.get()});
        } else {
          auto &[d_a00, d_a10, d_a20] =
              std::get<typename MemSafetyProbe28::tree::Node>(t2.v_mut());
          _stack.emplace_back(
              _After_Node{*(d_a00), d_a0.get(), (d_a1 + d_a10)});
          _stack.emplace_back(_Enter{std::move(*(d_a20)), d_a2.get()});
        }
      }
    } else if (std::holds_alternative<_After_Leaf>(_frame)) {
      auto _f = std::move(std::get<_After_Leaf>(_frame));
      _stack.emplace_back(_Combine_Leaf{std::move(_result), _f.d_a1});
      _stack.emplace_back(_Enter{std::move(_f._s0), _f.d_a0});
    } else if (std::holds_alternative<_After_Node>(_frame)) {
      auto _f = std::move(std::get<_After_Node>(_frame));
      _stack.emplace_back(_Combine_Node{std::move(_result), _f._s2});
      _stack.emplace_back(_Enter{std::move(_f.d_a00), _f.d_a0});
    } else if (std::holds_alternative<_Combine_Leaf>(_frame)) {
      auto _f = std::move(std::get<_Combine_Leaf>(_frame));
      _result = tree::node(_result, _f.d_a1, _f._result);
    } else {
      auto _f = std::move(std::get<_Combine_Node>(_frame));
      _result = tree::node(_result, _f._s1, _f._result);
    }
  }
  return _result;
}

/// TEST 7: Deep trees to stress the optimization.
MemSafetyProbe28::tree MemSafetyProbe28::build_balanced(
    const unsigned int
        n) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    unsigned int n;
  };

  /// _After_n_: saves [n_, n], dispatches next recursive call.
  struct _After_n_ {
    unsigned int n_;
    unsigned int n;
  };

  /// _Combine_n_: receives partial results, combines with _result from final
  /// call.
  struct _Combine_n_ {
    MemSafetyProbe28::tree _result;
    unsigned int n;
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
      const unsigned int n = _f.n;
      if (n <= 0) {
        _result = tree::leaf();
      } else {
        unsigned int n_ = n - 1;
        _stack.emplace_back(_After_n_{n_, n});
        _stack.emplace_back(_Enter{n_});
      }
    } else if (std::holds_alternative<_After_n_>(_frame)) {
      auto _f = std::move(std::get<_After_n_>(_frame));
      _stack.emplace_back(_Combine_n_{std::move(_result), _f.n});
      _stack.emplace_back(_Enter{_f.n_});
    } else {
      auto _f = std::move(std::get<_Combine_n_>(_frame));
      _result = tree::node(_result, _f.n, _f._result);
    }
  }
  return _result;
}
