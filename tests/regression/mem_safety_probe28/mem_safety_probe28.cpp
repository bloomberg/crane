#include "mem_safety_probe28.h"

uint64_t MemSafetyProbe28::tree_sum(
    const MemSafetyProbe28::tree
        &t) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const MemSafetyProbe28::tree *t;
  };

  /// _Cont_Node: saves [a1, a2], resumes after recursive call, then processes
  /// rest.
  struct _Cont_Node {
    uint64_t a1;
    const MemSafetyProbe28::tree *a2;
  };

  /// _Cont_Node_1: saves [a1, r_], resumes after recursive call, then processes
  /// rest.
  struct _Cont_Node_1 {
    uint64_t a1;
    uint64_t r_;
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
      const MemSafetyProbe28::tree &t = *_f.t;
      if (std::holds_alternative<typename MemSafetyProbe28::tree::Leaf>(
              t.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1, a2] =
            std::get<typename MemSafetyProbe28::tree::Node>(t.v());
        _stack.emplace_back(_Cont_Node{a1, crane_raw(a2)});
        _stack.emplace_back(_Enter{crane_raw(a0)});
      }
    } else if (std::holds_alternative<_Cont_Node>(_frame)) {
      auto _f = std::move(std::get<_Cont_Node>(_frame));
      uint64_t a1 = _f.a1;
      const MemSafetyProbe28::tree &a2 = *_f.a2;
      uint64_t r_ = std::move(_result);
      _stack.emplace_back(_Cont_Node_1{a1, r_});
      _stack.emplace_back(_Enter{&a2});
    } else {
      auto _f = std::move(std::get<_Cont_Node_1>(_frame));
      uint64_t a1 = _f.a1;
      uint64_t r_ = _f.r_;
      uint64_t r_0 = std::move(_result);
      _result = ((r_ + a1) + r_0);
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

  /// _Cont_Node: saves [a2], resumes after recursive call, then processes rest.
  struct _Cont_Node {
    const MemSafetyProbe28::tree *a2;
  };

  /// _Cont_Node_1: saves [r_], resumes after recursive call, then processes
  /// rest.
  struct _Cont_Node_1 {
    uint64_t r_;
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
      const MemSafetyProbe28::tree &t = *_f.t;
      if (std::holds_alternative<typename MemSafetyProbe28::tree::Leaf>(
              t.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1, a2] =
            std::get<typename MemSafetyProbe28::tree::Node>(t.v());
        _stack.emplace_back(_Cont_Node{crane_raw(a2)});
        _stack.emplace_back(_Enter{crane_raw(a0)});
      }
    } else if (std::holds_alternative<_Cont_Node>(_frame)) {
      auto _f = std::move(std::get<_Cont_Node>(_frame));
      const MemSafetyProbe28::tree &a2 = *_f.a2;
      uint64_t r_ = std::move(_result);
      _stack.emplace_back(_Cont_Node_1{r_});
      _stack.emplace_back(_Enter{&a2});
    } else {
      auto _f = std::move(std::get<_Cont_Node_1>(_frame));
      uint64_t r_ = _f.r_;
      uint64_t r_0 = std::move(_result);
      _result = (UINT64_C(1) + std::max(r_, r_0));
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

  /// _Cont_Leaf: saves [a1, a2], resumes after recursive call, then processes
  /// rest.
  struct _Cont_Leaf {
    uint64_t a1;
    const MemSafetyProbe28::tree *a2;
  };

  /// _Cont_Leaf_1: saves [a1, r_], resumes after recursive call, then processes
  /// rest.
  struct _Cont_Leaf_1 {
    uint64_t a1;
    uint64_t r_;
  };

  /// _Cont_Node: saves [a1, a10, a2, a20, t2], resumes after recursive call,
  /// then processes rest.
  struct _Cont_Node {
    uint64_t a1;
    uint64_t a10;
    const MemSafetyProbe28::tree *a2;
    std::shared_ptr<MemSafetyProbe28::tree> a20;
    MemSafetyProbe28::tree t2;
  };

  /// _Cont_Node_1: saves [a1, a10, r_, t2], resumes after recursive call, then
  /// processes rest.
  struct _Cont_Node_1 {
    uint64_t a1;
    uint64_t a10;
    uint64_t r_;
    MemSafetyProbe28::tree t2;
  };

  using _Frame =
      std::variant<_Enter, _Cont_Leaf, _Cont_Leaf_1, _Cont_Node, _Cont_Node_1>;
  uint64_t _result{};
  crane::small_vector<_Frame> _stack;
  _stack.emplace_back(_Enter{t2, &t1});
  /// Loopified zip_trees: _Enter -> _Cont_Leaf -> _Cont_Leaf_1 -> _Cont_Node ->
  /// _Cont_Node_1.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const MemSafetyProbe28::tree &t2 = std::move(_f.t2);
      const MemSafetyProbe28::tree &t1 = *_f.t1;
      if (std::holds_alternative<typename MemSafetyProbe28::tree::Leaf>(
              t1.v())) {
        _result = tree_sum(t2);
      } else {
        const auto &[a0, a1, a2] =
            std::get<typename MemSafetyProbe28::tree::Node>(t1.v());
        if (std::holds_alternative<typename MemSafetyProbe28::tree::Leaf>(
                t2.v())) {
          _stack.emplace_back(_Cont_Leaf{a1, crane_raw(a2)});
          _stack.emplace_back(_Enter{tree::leaf(), crane_raw(a0)});
        } else {
          const auto &[a00, a10, a20] =
              std::get<typename MemSafetyProbe28::tree::Node>(t2.v());
          _stack.emplace_back(_Cont_Node{a1, a10, crane_raw(a2), a20, t2});
          _stack.emplace_back(_Enter{*a00, crane_raw(a0)});
        }
      }
    } else if (std::holds_alternative<_Cont_Leaf>(_frame)) {
      auto _f = std::move(std::get<_Cont_Leaf>(_frame));
      uint64_t a1 = _f.a1;
      const MemSafetyProbe28::tree &a2 = *_f.a2;
      uint64_t r_ = std::move(_result);
      _stack.emplace_back(_Cont_Leaf_1{a1, r_});
      _stack.emplace_back(_Enter{tree::leaf(), &a2});
    } else if (std::holds_alternative<_Cont_Leaf_1>(_frame)) {
      auto _f = std::move(std::get<_Cont_Leaf_1>(_frame));
      uint64_t a1 = _f.a1;
      uint64_t r_ = _f.r_;
      uint64_t r_0 = std::move(_result);
      _result = ((a1 + r_) + r_0);
    } else if (std::holds_alternative<_Cont_Node>(_frame)) {
      auto _f = std::move(std::get<_Cont_Node>(_frame));
      uint64_t a1 = _f.a1;
      uint64_t a10 = _f.a10;
      const MemSafetyProbe28::tree &a2 = *_f.a2;
      std::shared_ptr<MemSafetyProbe28::tree> a20 = std::move(_f.a20);
      const MemSafetyProbe28::tree &t2 = std::move(_f.t2);
      uint64_t r_ = std::move(_result);
      _stack.emplace_back(_Cont_Node_1{a1, a10, r_, t2});
      _stack.emplace_back(_Enter{*a20, &a2});
    } else {
      auto _f = std::move(std::get<_Cont_Node_1>(_frame));
      uint64_t a1 = _f.a1;
      uint64_t a10 = _f.a10;
      uint64_t r_ = _f.r_;
      const MemSafetyProbe28::tree &t2 = std::move(_f.t2);
      uint64_t r_0 = std::move(_result);
      _result = ((((r_ + a1) + a10) + r_0) + tree_sum(t2));
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

  /// _Cont_Leaf: saves [a1, a2], resumes after recursive call, then processes
  /// rest.
  struct _Cont_Leaf {
    uint64_t a1;
    const MemSafetyProbe28::tree *a2;
  };

  /// _Cont_Leaf_1: saves [a1, r_], resumes after recursive call, then processes
  /// rest.
  struct _Cont_Leaf_1 {
    uint64_t a1;
    uint64_t r_;
  };

  /// _Cont_Node: saves [a2, a20, t2], resumes after recursive call, then
  /// processes rest.
  struct _Cont_Node {
    const MemSafetyProbe28::tree *a2;
    std::shared_ptr<MemSafetyProbe28::tree> a20;
    MemSafetyProbe28::tree t2;
  };

  /// _Cont_Node_1: saves [r_, t2], resumes after recursive call, then processes
  /// rest.
  struct _Cont_Node_1 {
    uint64_t r_;
    MemSafetyProbe28::tree t2;
  };

  using _Frame =
      std::variant<_Enter, _Cont_Leaf, _Cont_Leaf_1, _Cont_Node, _Cont_Node_1>;
  uint64_t _result{};
  crane::small_vector<_Frame> _stack;
  _stack.emplace_back(_Enter{t2, &t1});
  /// Loopified zip_depth: _Enter -> _Cont_Leaf -> _Cont_Leaf_1 -> _Cont_Node ->
  /// _Cont_Node_1.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const MemSafetyProbe28::tree &t2 = std::move(_f.t2);
      const MemSafetyProbe28::tree &t1 = *_f.t1;
      if (std::holds_alternative<typename MemSafetyProbe28::tree::Leaf>(
              t1.v())) {
        _result = tree_depth(t2);
      } else {
        const auto &[a0, a1, a2] =
            std::get<typename MemSafetyProbe28::tree::Node>(t1.v());
        if (std::holds_alternative<typename MemSafetyProbe28::tree::Leaf>(
                t2.v())) {
          _stack.emplace_back(_Cont_Leaf{a1, crane_raw(a2)});
          _stack.emplace_back(_Enter{tree::leaf(), crane_raw(a0)});
        } else {
          const auto &[a00, a10, a20] =
              std::get<typename MemSafetyProbe28::tree::Node>(t2.v());
          _stack.emplace_back(_Cont_Node{crane_raw(a2), a20, t2});
          _stack.emplace_back(_Enter{*a00, crane_raw(a0)});
        }
      }
    } else if (std::holds_alternative<_Cont_Leaf>(_frame)) {
      auto _f = std::move(std::get<_Cont_Leaf>(_frame));
      uint64_t a1 = _f.a1;
      const MemSafetyProbe28::tree &a2 = *_f.a2;
      uint64_t r_ = std::move(_result);
      _stack.emplace_back(_Cont_Leaf_1{a1, r_});
      _stack.emplace_back(_Enter{tree::leaf(), &a2});
    } else if (std::holds_alternative<_Cont_Leaf_1>(_frame)) {
      auto _f = std::move(std::get<_Cont_Leaf_1>(_frame));
      uint64_t a1 = _f.a1;
      uint64_t r_ = _f.r_;
      uint64_t r_0 = std::move(_result);
      _result = ((a1 + r_) + r_0);
    } else if (std::holds_alternative<_Cont_Node>(_frame)) {
      auto _f = std::move(std::get<_Cont_Node>(_frame));
      const MemSafetyProbe28::tree &a2 = *_f.a2;
      std::shared_ptr<MemSafetyProbe28::tree> a20 = std::move(_f.a20);
      const MemSafetyProbe28::tree &t2 = std::move(_f.t2);
      uint64_t r_ = std::move(_result);
      _stack.emplace_back(_Cont_Node_1{r_, t2});
      _stack.emplace_back(_Enter{*a20, &a2});
    } else {
      auto _f = std::move(std::get<_Cont_Node_1>(_frame));
      uint64_t r_ = _f.r_;
      const MemSafetyProbe28::tree &t2 = std::move(_f.t2);
      uint64_t r_0 = std::move(_result);
      _result = ((r_ + tree_depth(t2)) + r_0);
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

  /// _Cont_Leaf: saves [a1, a2], resumes after recursive call, then processes
  /// rest.
  struct _Cont_Leaf {
    uint64_t a1;
    const MemSafetyProbe28::tree *a2;
  };

  /// _Cont_Leaf_1: saves [a1, r_], resumes after recursive call, then processes
  /// rest.
  struct _Cont_Leaf_1 {
    uint64_t a1;
    uint64_t r_;
  };

  /// _Cont_Node: saves [a00, a10, a2, a20], resumes after recursive call, then
  /// processes rest.
  struct _Cont_Node {
    std::shared_ptr<MemSafetyProbe28::tree> a00;
    uint64_t a10;
    const MemSafetyProbe28::tree *a2;
    std::shared_ptr<MemSafetyProbe28::tree> a20;
  };

  /// _Cont_Node_1: saves [a00, a10, a20, r_], resumes after recursive call,
  /// then processes rest.
  struct _Cont_Node_1 {
    std::shared_ptr<MemSafetyProbe28::tree> a00;
    uint64_t a10;
    std::shared_ptr<MemSafetyProbe28::tree> a20;
    uint64_t r_;
  };

  using _Frame =
      std::variant<_Enter, _Cont_Leaf, _Cont_Leaf_1, _Cont_Node, _Cont_Node_1>;
  uint64_t _result{};
  crane::small_vector<_Frame> _stack;
  _stack.emplace_back(_Enter{t2, &t1});
  /// Loopified zip_and_sum: _Enter -> _Cont_Leaf -> _Cont_Leaf_1 -> _Cont_Node
  /// -> _Cont_Node_1.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const MemSafetyProbe28::tree &t2 = std::move(_f.t2);
      const MemSafetyProbe28::tree &t1 = *_f.t1;
      if (std::holds_alternative<typename MemSafetyProbe28::tree::Leaf>(
              t1.v())) {
        _result = tree_sum(t2);
      } else {
        const auto &[a0, a1, a2] =
            std::get<typename MemSafetyProbe28::tree::Node>(t1.v());
        if (std::holds_alternative<typename MemSafetyProbe28::tree::Leaf>(
                t2.v())) {
          _stack.emplace_back(_Cont_Leaf{a1, crane_raw(a2)});
          _stack.emplace_back(_Enter{tree::leaf(), crane_raw(a0)});
        } else {
          const auto &[a00, a10, a20] =
              std::get<typename MemSafetyProbe28::tree::Node>(t2.v());
          _stack.emplace_back(_Cont_Node{a00, a10, crane_raw(a2), a20});
          _stack.emplace_back(_Enter{*a00, crane_raw(a0)});
        }
      }
    } else if (std::holds_alternative<_Cont_Leaf>(_frame)) {
      auto _f = std::move(std::get<_Cont_Leaf>(_frame));
      uint64_t a1 = _f.a1;
      const MemSafetyProbe28::tree &a2 = *_f.a2;
      uint64_t r_ = std::move(_result);
      _stack.emplace_back(_Cont_Leaf_1{a1, r_});
      _stack.emplace_back(_Enter{tree::leaf(), &a2});
    } else if (std::holds_alternative<_Cont_Leaf_1>(_frame)) {
      auto _f = std::move(std::get<_Cont_Leaf_1>(_frame));
      uint64_t a1 = _f.a1;
      uint64_t r_ = _f.r_;
      uint64_t r_0 = std::move(_result);
      _result = ((r_ + a1) + r_0);
    } else if (std::holds_alternative<_Cont_Node>(_frame)) {
      auto _f = std::move(std::get<_Cont_Node>(_frame));
      std::shared_ptr<MemSafetyProbe28::tree> a00 = std::move(_f.a00);
      uint64_t a10 = _f.a10;
      const MemSafetyProbe28::tree &a2 = *_f.a2;
      std::shared_ptr<MemSafetyProbe28::tree> a20 = std::move(_f.a20);
      uint64_t r_ = std::move(_result);
      _stack.emplace_back(_Cont_Node_1{std::move(a00), a10, a20, r_});
      _stack.emplace_back(_Enter{*a20, &a2});
    } else {
      auto _f = std::move(std::get<_Cont_Node_1>(_frame));
      std::shared_ptr<MemSafetyProbe28::tree> a00 = std::move(_f.a00);
      uint64_t a10 = _f.a10;
      std::shared_ptr<MemSafetyProbe28::tree> a20 = std::move(_f.a20);
      uint64_t r_ = _f.r_;
      uint64_t r_0 = std::move(_result);
      _result = ((((r_ + a10) + r_0) + tree_sum(*a00)) + tree_sum(*a20));
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

  /// _Cont_Leaf: saves [a1, a2, t2], resumes after recursive call, then
  /// processes rest.
  struct _Cont_Leaf {
    uint64_t a1;
    const MemSafetyProbe28::tree *a2;
    const MemSafetyProbe28::tree *t2;
  };

  /// _Cont_Leaf_1: saves [a1, r_], resumes after recursive call, then processes
  /// rest.
  struct _Cont_Leaf_1 {
    uint64_t a1;
    uint64_t r_;
  };

  /// _Cont_Node: saves [a10, a2, a20, t2], resumes after recursive call, then
  /// processes rest.
  struct _Cont_Node {
    uint64_t a10;
    const MemSafetyProbe28::tree *a2;
    const MemSafetyProbe28::tree *a20;
    MemSafetyProbe28::tree t2;
  };

  /// _Cont_Node_1: saves [a10, r_, t2], resumes after recursive call, then
  /// processes rest.
  struct _Cont_Node_1 {
    uint64_t a10;
    uint64_t r_;
    MemSafetyProbe28::tree t2;
  };

  using _Frame =
      std::variant<_Enter, _Cont_Leaf, _Cont_Leaf_1, _Cont_Node, _Cont_Node_1>;
  uint64_t _result{};
  crane::small_vector<_Frame> _stack;
  _stack.emplace_back(_Enter{&t2, &t1});
  /// Loopified double_zip: _Enter -> _Cont_Leaf -> _Cont_Leaf_1 -> _Cont_Node
  /// -> _Cont_Node_1.
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
          _stack.emplace_back(_Cont_Leaf{a1, crane_raw(a2), &t2});
          _stack.emplace_back(_Enter{&t2, crane_raw(a0)});
        } else {
          const auto &[a00, a10, a20] =
              std::get<typename MemSafetyProbe28::tree::Node>(t2.v());
          _stack.emplace_back(
              _Cont_Node{a10, crane_raw(a2), crane_raw(a20), t2});
          _stack.emplace_back(_Enter{crane_raw(a00), crane_raw(a0)});
        }
      }
    } else if (std::holds_alternative<_Cont_Leaf>(_frame)) {
      auto _f = std::move(std::get<_Cont_Leaf>(_frame));
      uint64_t a1 = _f.a1;
      const MemSafetyProbe28::tree &a2 = *_f.a2;
      const MemSafetyProbe28::tree &t2 = *_f.t2;
      uint64_t r_ = std::move(_result);
      _stack.emplace_back(_Cont_Leaf_1{a1, r_});
      _stack.emplace_back(_Enter{&t2, &a2});
    } else if (std::holds_alternative<_Cont_Leaf_1>(_frame)) {
      auto _f = std::move(std::get<_Cont_Leaf_1>(_frame));
      uint64_t a1 = _f.a1;
      uint64_t r_ = _f.r_;
      uint64_t r_0 = std::move(_result);
      _result = ((r_ + a1) + r_0);
    } else if (std::holds_alternative<_Cont_Node>(_frame)) {
      auto _f = std::move(std::get<_Cont_Node>(_frame));
      uint64_t a10 = _f.a10;
      const MemSafetyProbe28::tree &a2 = *_f.a2;
      const MemSafetyProbe28::tree &a20 = *_f.a20;
      const MemSafetyProbe28::tree &t2 = std::move(_f.t2);
      uint64_t r_ = std::move(_result);
      _stack.emplace_back(_Cont_Node_1{a10, r_, t2});
      _stack.emplace_back(_Enter{&a20, &a2});
    } else {
      auto _f = std::move(std::get<_Cont_Node_1>(_frame));
      uint64_t a10 = _f.a10;
      uint64_t r_ = _f.r_;
      const MemSafetyProbe28::tree &t2 = std::move(_f.t2);
      uint64_t r_0 = std::move(_result);
      _result = (((r_ + r_0) + a10) + tree_sum(t2));
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

  /// _Cont_Leaf: saves [a0, a1], resumes after recursive call, then processes
  /// rest.
  struct _Cont_Leaf {
    const MemSafetyProbe28::tree *a0;
    uint64_t a1;
  };

  /// _Cont_Node: saves [a0, a00, a1, a10], resumes after recursive call, then
  /// processes rest.
  struct _Cont_Node {
    const MemSafetyProbe28::tree *a0;
    std::shared_ptr<MemSafetyProbe28::tree> a00;
    uint64_t a1;
    uint64_t a10;
  };

  using _Frame = std::variant<_Enter, _Cont_Leaf, _Cont_Node>;
  List<uint64_t> _result{};
  crane::small_vector<_Frame> _stack;
  _stack.emplace_back(_Enter{std::move(acc), t2, &t1});
  /// Loopified zip_collect: _Enter -> _Cont_Leaf -> _Cont_Node.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      List<uint64_t> acc = std::move(_f.acc);
      const MemSafetyProbe28::tree &t2 = std::move(_f.t2);
      const MemSafetyProbe28::tree &t1 = *_f.t1;
      if (std::holds_alternative<typename MemSafetyProbe28::tree::Leaf>(
              t1.v())) {
        _result = std::move(acc);
      } else {
        const auto &[a0, a1, a2] =
            std::get<typename MemSafetyProbe28::tree::Node>(t1.v());
        if (std::holds_alternative<typename MemSafetyProbe28::tree::Leaf>(
                t2.v())) {
          _stack.emplace_back(_Cont_Leaf{crane_raw(a0), a1});
          _stack.emplace_back(
              _Enter{std::move(acc), tree::leaf(), crane_raw(a2)});
        } else {
          const auto &[a00, a10, a20] =
              std::get<typename MemSafetyProbe28::tree::Node>(t2.v());
          _stack.emplace_back(_Cont_Node{crane_raw(a0), a00, a1, a10});
          _stack.emplace_back(_Enter{std::move(acc), *a20, crane_raw(a2)});
        }
      }
    } else if (std::holds_alternative<_Cont_Leaf>(_frame)) {
      auto _f = std::move(std::get<_Cont_Leaf>(_frame));
      const MemSafetyProbe28::tree &a0 = *_f.a0;
      uint64_t a1 = _f.a1;
      List<uint64_t> r_ = std::move(_result);
      _stack.emplace_back(
          _Enter{List<uint64_t>::cons(a1, std::move(r_)), tree::leaf(), &a0});
    } else {
      auto _f = std::move(std::get<_Cont_Node>(_frame));
      const MemSafetyProbe28::tree &a0 = *_f.a0;
      std::shared_ptr<MemSafetyProbe28::tree> a00 = std::move(_f.a00);
      uint64_t a1 = _f.a1;
      uint64_t a10 = _f.a10;
      List<uint64_t> r_ = std::move(_result);
      _stack.emplace_back(_Enter{
          List<uint64_t>::cons(a1, List<uint64_t>::cons(a10, std::move(r_))),
          *a00, &a0});
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

  /// _Cont_Cons: saves [a0], resumes after recursive call, then processes rest.
  struct _Cont_Cons {
    uint64_t a0;
  };

  using _Frame = std::variant<_Enter, _Cont_Cons>;
  uint64_t _result{};
  crane::small_vector<_Frame> _stack;
  _stack.emplace_back(_Enter{&l});
  /// Loopified list_sum: _Enter -> _Cont_Cons.
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
        _stack.emplace_back(_Cont_Cons{a0});
        _stack.emplace_back(_Enter{crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<_Cont_Cons>(_frame));
      uint64_t a0 = _f.a0;
      uint64_t r_ = std::move(_result);
      _result = (a0 + r_);
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

  /// _Cont_Leaf: saves [a1, a2], resumes after recursive call, then processes
  /// rest.
  struct _Cont_Leaf {
    uint64_t a1;
    const MemSafetyProbe28::tree *a2;
  };

  /// _Cont_Node: saves [a1, a10, a2, a20], resumes after recursive call, then
  /// processes rest.
  struct _Cont_Node {
    uint64_t a1;
    uint64_t a10;
    const MemSafetyProbe28::tree *a2;
    std::shared_ptr<MemSafetyProbe28::tree> a20;
  };

  /// _Resume_Leaf: saves [a1, r_], resumes after recursive call with _result.
  struct _Resume_Leaf {
    uint64_t a1;
    MemSafetyProbe28::tree r_;
  };

  /// _Resume_Node: saves [_s0, r_], resumes after recursive call with _result.
  struct _Resume_Node {
    uint64_t _s0;
    MemSafetyProbe28::tree r_;
  };

  using _Frame =
      std::variant<_Enter, _Cont_Leaf, _Cont_Node, _Resume_Leaf, _Resume_Node>;
  MemSafetyProbe28::tree _result{};
  crane::small_vector<_Frame> _stack;
  _stack.emplace_back(_Enter{std::move(t2), &t1});
  /// Loopified merge_trees: _Enter -> _Cont_Leaf -> _Cont_Node -> _Resume_Leaf
  /// -> _Resume_Node.
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
          _stack.emplace_back(_Cont_Leaf{a1, crane_raw(a2)});
          _stack.emplace_back(_Enter{tree::leaf(), crane_raw(a0)});
        } else {
          auto &[a00, a10, a20] =
              std::get<typename MemSafetyProbe28::tree::Node>(t2.v_mut());
          _stack.emplace_back(_Cont_Node{a1, a10, crane_raw(a2), a20});
          _stack.emplace_back(_Enter{*a00, crane_raw(a0)});
        }
      }
    } else if (std::holds_alternative<_Cont_Leaf>(_frame)) {
      auto _f = std::move(std::get<_Cont_Leaf>(_frame));
      uint64_t a1 = _f.a1;
      const MemSafetyProbe28::tree &a2 = *_f.a2;
      MemSafetyProbe28::tree r_ = std::move(_result);
      _stack.emplace_back(_Resume_Leaf{a1, std::move(r_)});
      _stack.emplace_back(_Enter{tree::leaf(), &a2});
    } else if (std::holds_alternative<_Cont_Node>(_frame)) {
      auto _f = std::move(std::get<_Cont_Node>(_frame));
      uint64_t a1 = _f.a1;
      uint64_t a10 = _f.a10;
      const MemSafetyProbe28::tree &a2 = *_f.a2;
      std::shared_ptr<MemSafetyProbe28::tree> a20 = std::move(_f.a20);
      MemSafetyProbe28::tree r_ = std::move(_result);
      _stack.emplace_back(_Resume_Node{(a1 + std::move(a10)), std::move(r_)});
      _stack.emplace_back(_Enter{*a20, &a2});
    } else if (std::holds_alternative<_Resume_Leaf>(_frame)) {
      auto _f = std::move(std::get<_Resume_Leaf>(_frame));
      _result = tree::node(std::move(_f.r_), _f.a1, std::move(_result));
    } else {
      auto _f = std::move(std::get<_Resume_Node>(_frame));
      _result = tree::node(std::move(_f.r_), _f._s0, std::move(_result));
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

  /// _Cont_n_: saves [n, n_], resumes after recursive call, then processes
  /// rest.
  struct _Cont_n_ {
    uint64_t n;
    uint64_t n_;
  };

  /// _Resume_n_: saves [n, r_], resumes after recursive call with _result.
  struct _Resume_n_ {
    uint64_t n;
    MemSafetyProbe28::tree r_;
  };

  using _Frame = std::variant<_Enter, _Cont_n_, _Resume_n_>;
  MemSafetyProbe28::tree _result{};
  crane::small_vector<_Frame> _stack;
  _stack.emplace_back(_Enter{n});
  /// Loopified build_balanced: _Enter -> _Cont_n_ -> _Resume_n_.
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
        _stack.emplace_back(_Cont_n_{n, n_});
        _stack.emplace_back(_Enter{n_});
      }
    } else if (std::holds_alternative<_Cont_n_>(_frame)) {
      auto _f = std::move(std::get<_Cont_n_>(_frame));
      uint64_t n = _f.n;
      uint64_t n_ = _f.n_;
      MemSafetyProbe28::tree r_ = std::move(_result);
      _stack.emplace_back(_Resume_n_{n, std::move(r_)});
      _stack.emplace_back(_Enter{n_});
    } else {
      auto _f = std::move(std::get<_Resume_n_>(_frame));
      _result = tree::node(std::move(_f.r_), _f.n, std::move(_result));
    }
  }
  return _result;
}
