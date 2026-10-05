#include "mem_safety_probe28.h"

uint64_t MemSafetyProbe28::tree_sum(
    const MemSafetyProbe28::tree &t) { /// CraneEnter: captures varying
                                       /// parameters for each recursive call.

  struct CraneEnter {
    const MemSafetyProbe28::tree *t;
  };

  /// CraneCont_Node: saves [a1, a2], resumes after recursive call, then
  /// processes rest.
  struct CraneCont_Node {
    uint64_t a1;
    const MemSafetyProbe28::tree *a2;
  };

  /// CraneCont_Node_1: saves [_tmp2, a1], resumes after recursive call, then
  /// processes rest.
  struct CraneCont_Node_1 {
    uint64_t _tmp2;
    uint64_t a1;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont_Node, CraneCont_Node_1>;
  uint64_t _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{&t});
  /// Loopified tree_sum: CraneEnter -> CraneCont_Node -> CraneCont_Node_1.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      const MemSafetyProbe28::tree &t = *_f.t;
      if (std::holds_alternative<typename MemSafetyProbe28::tree::Leaf>(
              t.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1, a2] =
            std::get<typename MemSafetyProbe28::tree::Node>(t.v());
        _stack.emplace_back(CraneCont_Node{a1, crane_raw(a2)});
        _stack.emplace_back(CraneEnter{crane_raw(a0)});
      }
    } else if (std::holds_alternative<CraneCont_Node>(_frame)) {
      auto _f = std::move(std::get<CraneCont_Node>(_frame));
      uint64_t a1 = _f.a1;
      const MemSafetyProbe28::tree &a2 = *_f.a2;
      _stack.emplace_back(CraneCont_Node_1{std::move(_result), a1});
      _stack.emplace_back(CraneEnter{&a2});
    } else {
      auto _f = std::move(std::get<CraneCont_Node_1>(_frame));
      uint64_t a1 = _f.a1;
      _result = ((_f._tmp2 + a1) + std::move(_result));
    }
  }
  return _result;
}

uint64_t MemSafetyProbe28::tree_depth(
    const MemSafetyProbe28::tree &t) { /// CraneEnter: captures varying
                                       /// parameters for each recursive call.

  struct CraneEnter {
    const MemSafetyProbe28::tree *t;
  };

  /// CraneCont_Node: saves [a2], resumes after recursive call, then processes
  /// rest.
  struct CraneCont_Node {
    const MemSafetyProbe28::tree *a2;
  };

  /// CraneCont_Node_1: saves [_tmp2], resumes after recursive call, then
  /// processes rest.
  struct CraneCont_Node_1 {
    uint64_t _tmp2;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont_Node, CraneCont_Node_1>;
  uint64_t _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{&t});
  /// Loopified tree_depth: CraneEnter -> CraneCont_Node -> CraneCont_Node_1.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      const MemSafetyProbe28::tree &t = *_f.t;
      if (std::holds_alternative<typename MemSafetyProbe28::tree::Leaf>(
              t.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1, a2] =
            std::get<typename MemSafetyProbe28::tree::Node>(t.v());
        _stack.emplace_back(CraneCont_Node{crane_raw(a2)});
        _stack.emplace_back(CraneEnter{crane_raw(a0)});
      }
    } else if (std::holds_alternative<CraneCont_Node>(_frame)) {
      auto _f = std::move(std::get<CraneCont_Node>(_frame));
      const MemSafetyProbe28::tree &a2 = *_f.a2;
      _stack.emplace_back(CraneCont_Node_1{std::move(_result)});
      _stack.emplace_back(CraneEnter{&a2});
    } else {
      auto _f = std::move(std::get<CraneCont_Node_1>(_frame));
      _result = (UINT64_C(1) + std::max(_f._tmp2, std::move(_result)));
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
    const MemSafetyProbe28::tree &t2) { /// CraneEnter: captures varying
                                        /// parameters for each recursive call.

  struct CraneEnter {
    MemSafetyProbe28::tree t2;
    const MemSafetyProbe28::tree *t1;
  };

  /// CraneCont_Leaf: saves [a1, a2], resumes after recursive call, then
  /// processes rest.
  struct CraneCont_Leaf {
    uint64_t a1;
    const MemSafetyProbe28::tree *a2;
  };

  /// CraneCont_Leaf_1: saves [_tmp2, a1], resumes after recursive call, then
  /// processes rest.
  struct CraneCont_Leaf_1 {
    uint64_t _tmp2;
    uint64_t a1;
  };

  /// CraneCont_Node: saves [a1, a10, a2, a20, t2], resumes after recursive
  /// call, then processes rest.
  struct CraneCont_Node {
    uint64_t a1;
    uint64_t a10;
    const MemSafetyProbe28::tree *a2;
    std::shared_ptr<MemSafetyProbe28::tree> a20;
    MemSafetyProbe28::tree t2;
  };

  /// CraneCont_Node_1: saves [_tmp4, a1, a10, t2], resumes after recursive
  /// call, then processes rest.
  struct CraneCont_Node_1 {
    uint64_t _tmp4;
    uint64_t a1;
    uint64_t a10;
    MemSafetyProbe28::tree t2;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont_Leaf, CraneCont_Leaf_1,
                                  CraneCont_Node, CraneCont_Node_1>;
  uint64_t _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{t2, &t1});
  /// Loopified zip_trees: CraneEnter -> CraneCont_Leaf -> CraneCont_Leaf_1 ->
  /// CraneCont_Node -> CraneCont_Node_1.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
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
          _stack.emplace_back(CraneCont_Leaf{a1, crane_raw(a2)});
          _stack.emplace_back(CraneEnter{tree::leaf(), crane_raw(a0)});
        } else {
          const auto &[a00, a10, a20] =
              std::get<typename MemSafetyProbe28::tree::Node>(t2.v());
          _stack.emplace_back(CraneCont_Node{a1, a10, crane_raw(a2), a20, t2});
          _stack.emplace_back(CraneEnter{*a00, crane_raw(a0)});
        }
      }
    } else if (std::holds_alternative<CraneCont_Leaf>(_frame)) {
      auto _f = std::move(std::get<CraneCont_Leaf>(_frame));
      uint64_t a1 = _f.a1;
      const MemSafetyProbe28::tree &a2 = *_f.a2;
      _stack.emplace_back(CraneCont_Leaf_1{std::move(_result), a1});
      _stack.emplace_back(CraneEnter{tree::leaf(), &a2});
    } else if (std::holds_alternative<CraneCont_Leaf_1>(_frame)) {
      auto _f = std::move(std::get<CraneCont_Leaf_1>(_frame));
      uint64_t a1 = _f.a1;
      _result = ((a1 + _f._tmp2) + std::move(_result));
    } else if (std::holds_alternative<CraneCont_Node>(_frame)) {
      auto _f = std::move(std::get<CraneCont_Node>(_frame));
      uint64_t a1 = _f.a1;
      uint64_t a10 = _f.a10;
      const MemSafetyProbe28::tree &a2 = *_f.a2;
      std::shared_ptr<MemSafetyProbe28::tree> a20 = std::move(_f.a20);
      const MemSafetyProbe28::tree &t2 = std::move(_f.t2);
      _stack.emplace_back(CraneCont_Node_1{std::move(_result), a1, a10, t2});
      _stack.emplace_back(CraneEnter{*a20, &a2});
    } else {
      auto _f = std::move(std::get<CraneCont_Node_1>(_frame));
      uint64_t a1 = _f.a1;
      uint64_t a10 = _f.a10;
      const MemSafetyProbe28::tree &t2 = std::move(_f.t2);
      _result = ((((_f._tmp4 + a1) + a10) + std::move(_result)) + tree_sum(t2));
    }
  }
  return _result;
}

/// TEST 2: zip_depth - Similar but uses tree_depth on t2.
/// Tests a different tree traversal on the non-pointer-safe param.
uint64_t MemSafetyProbe28::zip_depth(
    const MemSafetyProbe28::tree &t1,
    const MemSafetyProbe28::tree &t2) { /// CraneEnter: captures varying
                                        /// parameters for each recursive call.

  struct CraneEnter {
    MemSafetyProbe28::tree t2;
    const MemSafetyProbe28::tree *t1;
  };

  /// CraneCont_Leaf: saves [a1, a2], resumes after recursive call, then
  /// processes rest.
  struct CraneCont_Leaf {
    uint64_t a1;
    const MemSafetyProbe28::tree *a2;
  };

  /// CraneCont_Leaf_1: saves [_tmp2, a1], resumes after recursive call, then
  /// processes rest.
  struct CraneCont_Leaf_1 {
    uint64_t _tmp2;
    uint64_t a1;
  };

  /// CraneCont_Node: saves [a2, a20, t2], resumes after recursive call, then
  /// processes rest.
  struct CraneCont_Node {
    const MemSafetyProbe28::tree *a2;
    std::shared_ptr<MemSafetyProbe28::tree> a20;
    MemSafetyProbe28::tree t2;
  };

  /// CraneCont_Node_1: saves [_tmp4, t2], resumes after recursive call, then
  /// processes rest.
  struct CraneCont_Node_1 {
    uint64_t _tmp4;
    MemSafetyProbe28::tree t2;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont_Leaf, CraneCont_Leaf_1,
                                  CraneCont_Node, CraneCont_Node_1>;
  uint64_t _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{t2, &t1});
  /// Loopified zip_depth: CraneEnter -> CraneCont_Leaf -> CraneCont_Leaf_1 ->
  /// CraneCont_Node -> CraneCont_Node_1.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
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
          _stack.emplace_back(CraneCont_Leaf{a1, crane_raw(a2)});
          _stack.emplace_back(CraneEnter{tree::leaf(), crane_raw(a0)});
        } else {
          const auto &[a00, a10, a20] =
              std::get<typename MemSafetyProbe28::tree::Node>(t2.v());
          _stack.emplace_back(CraneCont_Node{crane_raw(a2), a20, t2});
          _stack.emplace_back(CraneEnter{*a00, crane_raw(a0)});
        }
      }
    } else if (std::holds_alternative<CraneCont_Leaf>(_frame)) {
      auto _f = std::move(std::get<CraneCont_Leaf>(_frame));
      uint64_t a1 = _f.a1;
      const MemSafetyProbe28::tree &a2 = *_f.a2;
      _stack.emplace_back(CraneCont_Leaf_1{std::move(_result), a1});
      _stack.emplace_back(CraneEnter{tree::leaf(), &a2});
    } else if (std::holds_alternative<CraneCont_Leaf_1>(_frame)) {
      auto _f = std::move(std::get<CraneCont_Leaf_1>(_frame));
      uint64_t a1 = _f.a1;
      _result = ((a1 + _f._tmp2) + std::move(_result));
    } else if (std::holds_alternative<CraneCont_Node>(_frame)) {
      auto _f = std::move(std::get<CraneCont_Node>(_frame));
      const MemSafetyProbe28::tree &a2 = *_f.a2;
      std::shared_ptr<MemSafetyProbe28::tree> a20 = std::move(_f.a20);
      const MemSafetyProbe28::tree &t2 = std::move(_f.t2);
      _stack.emplace_back(CraneCont_Node_1{std::move(_result), t2});
      _stack.emplace_back(CraneEnter{*a20, &a2});
    } else {
      auto _f = std::move(std::get<CraneCont_Node_1>(_frame));
      const MemSafetyProbe28::tree &t2 = std::move(_f.t2);
      _result = ((_f._tmp4 + tree_depth(t2)) + std::move(_result));
    }
  }
  return _result;
}

/// TEST 3: zip_and_build - Recurse and also construct using t2's children.
/// t2's left child is used for recursion AND returned as part of result.
uint64_t MemSafetyProbe28::zip_and_sum(
    const MemSafetyProbe28::tree &t1,
    const MemSafetyProbe28::tree &t2) { /// CraneEnter: captures varying
                                        /// parameters for each recursive call.

  struct CraneEnter {
    MemSafetyProbe28::tree t2;
    const MemSafetyProbe28::tree *t1;
  };

  /// CraneCont_Leaf: saves [a1, a2], resumes after recursive call, then
  /// processes rest.
  struct CraneCont_Leaf {
    uint64_t a1;
    const MemSafetyProbe28::tree *a2;
  };

  /// CraneCont_Leaf_1: saves [_tmp2, a1], resumes after recursive call, then
  /// processes rest.
  struct CraneCont_Leaf_1 {
    uint64_t _tmp2;
    uint64_t a1;
  };

  /// CraneCont_Node: saves [a00, a10, a2, a20], resumes after recursive call,
  /// then processes rest.
  struct CraneCont_Node {
    std::shared_ptr<MemSafetyProbe28::tree> a00;
    uint64_t a10;
    const MemSafetyProbe28::tree *a2;
    std::shared_ptr<MemSafetyProbe28::tree> a20;
  };

  /// CraneCont_Node_1: saves [_tmp4, a00, a10, a20], resumes after recursive
  /// call, then processes rest.
  struct CraneCont_Node_1 {
    uint64_t _tmp4;
    std::shared_ptr<MemSafetyProbe28::tree> a00;
    uint64_t a10;
    std::shared_ptr<MemSafetyProbe28::tree> a20;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont_Leaf, CraneCont_Leaf_1,
                                  CraneCont_Node, CraneCont_Node_1>;
  uint64_t _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{t2, &t1});
  /// Loopified zip_and_sum: CraneEnter -> CraneCont_Leaf -> CraneCont_Leaf_1 ->
  /// CraneCont_Node -> CraneCont_Node_1.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
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
          _stack.emplace_back(CraneCont_Leaf{a1, crane_raw(a2)});
          _stack.emplace_back(CraneEnter{tree::leaf(), crane_raw(a0)});
        } else {
          const auto &[a00, a10, a20] =
              std::get<typename MemSafetyProbe28::tree::Node>(t2.v());
          _stack.emplace_back(CraneCont_Node{a00, a10, crane_raw(a2), a20});
          _stack.emplace_back(CraneEnter{*a00, crane_raw(a0)});
        }
      }
    } else if (std::holds_alternative<CraneCont_Leaf>(_frame)) {
      auto _f = std::move(std::get<CraneCont_Leaf>(_frame));
      uint64_t a1 = _f.a1;
      const MemSafetyProbe28::tree &a2 = *_f.a2;
      _stack.emplace_back(CraneCont_Leaf_1{std::move(_result), a1});
      _stack.emplace_back(CraneEnter{tree::leaf(), &a2});
    } else if (std::holds_alternative<CraneCont_Leaf_1>(_frame)) {
      auto _f = std::move(std::get<CraneCont_Leaf_1>(_frame));
      uint64_t a1 = _f.a1;
      _result = ((_f._tmp2 + a1) + std::move(_result));
    } else if (std::holds_alternative<CraneCont_Node>(_frame)) {
      auto _f = std::move(std::get<CraneCont_Node>(_frame));
      std::shared_ptr<MemSafetyProbe28::tree> a00 = std::move(_f.a00);
      uint64_t a10 = _f.a10;
      const MemSafetyProbe28::tree &a2 = *_f.a2;
      std::shared_ptr<MemSafetyProbe28::tree> a20 = std::move(_f.a20);
      _stack.emplace_back(
          CraneCont_Node_1{std::move(_result), std::move(a00), a10, a20});
      _stack.emplace_back(CraneEnter{*a20, &a2});
    } else {
      auto _f = std::move(std::get<CraneCont_Node_1>(_frame));
      std::shared_ptr<MemSafetyProbe28::tree> a00 = std::move(_f.a00);
      uint64_t a10 = _f.a10;
      std::shared_ptr<MemSafetyProbe28::tree> a20 = std::move(_f.a20);
      _result = ((((_f._tmp4 + a10) + std::move(_result)) + tree_sum(*a00)) +
                 tree_sum(*a20));
    }
  }
  return _result;
}

/// TEST 4: double_zip - Both t1 and t2 are trees, but t2 is used
/// in a different way for each call. Makes t2 non-pointer-safe.
uint64_t MemSafetyProbe28::double_zip(
    const MemSafetyProbe28::tree &t1,
    const MemSafetyProbe28::tree &t2) { /// CraneEnter: captures varying
                                        /// parameters for each recursive call.

  struct CraneEnter {
    const MemSafetyProbe28::tree *t2;
    const MemSafetyProbe28::tree *t1;
  };

  /// CraneCont_Leaf: saves [a1, a2, t2], resumes after recursive call, then
  /// processes rest.
  struct CraneCont_Leaf {
    uint64_t a1;
    const MemSafetyProbe28::tree *a2;
    const MemSafetyProbe28::tree *t2;
  };

  /// CraneCont_Leaf_1: saves [_tmp2, a1], resumes after recursive call, then
  /// processes rest.
  struct CraneCont_Leaf_1 {
    uint64_t _tmp2;
    uint64_t a1;
  };

  /// CraneCont_Node: saves [a10, a2, a20, t2], resumes after recursive call,
  /// then processes rest.
  struct CraneCont_Node {
    uint64_t a10;
    const MemSafetyProbe28::tree *a2;
    const MemSafetyProbe28::tree *a20;
    MemSafetyProbe28::tree t2;
  };

  /// CraneCont_Node_1: saves [_tmp4, a10, t2], resumes after recursive call,
  /// then processes rest.
  struct CraneCont_Node_1 {
    uint64_t _tmp4;
    uint64_t a10;
    MemSafetyProbe28::tree t2;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont_Leaf, CraneCont_Leaf_1,
                                  CraneCont_Node, CraneCont_Node_1>;
  uint64_t _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{&t2, &t1});
  /// Loopified double_zip: CraneEnter -> CraneCont_Leaf -> CraneCont_Leaf_1 ->
  /// CraneCont_Node -> CraneCont_Node_1.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
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
          _stack.emplace_back(CraneCont_Leaf{a1, crane_raw(a2), &t2});
          _stack.emplace_back(CraneEnter{&t2, crane_raw(a0)});
        } else {
          const auto &[a00, a10, a20] =
              std::get<typename MemSafetyProbe28::tree::Node>(t2.v());
          _stack.emplace_back(
              CraneCont_Node{a10, crane_raw(a2), crane_raw(a20), t2});
          _stack.emplace_back(CraneEnter{crane_raw(a00), crane_raw(a0)});
        }
      }
    } else if (std::holds_alternative<CraneCont_Leaf>(_frame)) {
      auto _f = std::move(std::get<CraneCont_Leaf>(_frame));
      uint64_t a1 = _f.a1;
      const MemSafetyProbe28::tree &a2 = *_f.a2;
      const MemSafetyProbe28::tree &t2 = *_f.t2;
      _stack.emplace_back(CraneCont_Leaf_1{std::move(_result), a1});
      _stack.emplace_back(CraneEnter{&t2, &a2});
    } else if (std::holds_alternative<CraneCont_Leaf_1>(_frame)) {
      auto _f = std::move(std::get<CraneCont_Leaf_1>(_frame));
      uint64_t a1 = _f.a1;
      _result = ((_f._tmp2 + a1) + std::move(_result));
    } else if (std::holds_alternative<CraneCont_Node>(_frame)) {
      auto _f = std::move(std::get<CraneCont_Node>(_frame));
      uint64_t a10 = _f.a10;
      const MemSafetyProbe28::tree &a2 = *_f.a2;
      const MemSafetyProbe28::tree &a20 = *_f.a20;
      const MemSafetyProbe28::tree &t2 = std::move(_f.t2);
      _stack.emplace_back(CraneCont_Node_1{std::move(_result), a10, t2});
      _stack.emplace_back(CraneEnter{&a20, &a2});
    } else {
      auto _f = std::move(std::get<CraneCont_Node_1>(_frame));
      uint64_t a10 = _f.a10;
      const MemSafetyProbe28::tree &t2 = std::move(_f.t2);
      _result = (((_f._tmp4 + std::move(_result)) + a10) + tree_sum(t2));
    }
  }
  return _result;
}

/// TEST 5: zip with list accumulator. t2 is tree, acc is list.
/// t2 non-pointer-safe due to Leaf in some calls.
List<uint64_t> MemSafetyProbe28::zip_collect(
    const MemSafetyProbe28::tree &t1, const MemSafetyProbe28::tree &t2,
    List<uint64_t> acc) { /// CraneEnter: captures varying parameters for each
                          /// recursive call.

  struct CraneEnter {
    List<uint64_t> acc;
    MemSafetyProbe28::tree t2;
    const MemSafetyProbe28::tree *t1;
  };

  /// CraneCont_Leaf: saves [a0, a1], resumes after recursive call, then
  /// processes rest.
  struct CraneCont_Leaf {
    const MemSafetyProbe28::tree *a0;
    uint64_t a1;
  };

  /// CraneCont_Node: saves [a0, a00, a1, a10], resumes after recursive call,
  /// then processes rest.
  struct CraneCont_Node {
    const MemSafetyProbe28::tree *a0;
    std::shared_ptr<MemSafetyProbe28::tree> a00;
    uint64_t a1;
    uint64_t a10;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont_Leaf, CraneCont_Node>;
  List<uint64_t> _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{std::move(acc), t2, &t1});
  /// Loopified zip_collect: CraneEnter -> CraneCont_Leaf -> CraneCont_Node.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
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
          _stack.emplace_back(CraneCont_Leaf{crane_raw(a0), a1});
          _stack.emplace_back(
              CraneEnter{std::move(acc), tree::leaf(), crane_raw(a2)});
        } else {
          const auto &[a00, a10, a20] =
              std::get<typename MemSafetyProbe28::tree::Node>(t2.v());
          _stack.emplace_back(CraneCont_Node{crane_raw(a0), a00, a1, a10});
          _stack.emplace_back(CraneEnter{std::move(acc), *a20, crane_raw(a2)});
        }
      }
    } else if (std::holds_alternative<CraneCont_Leaf>(_frame)) {
      auto _f = std::move(std::get<CraneCont_Leaf>(_frame));
      const MemSafetyProbe28::tree &a0 = *_f.a0;
      uint64_t a1 = _f.a1;
      _stack.emplace_back(CraneEnter{
          List<uint64_t>::cons(a1, std::move(_result)), tree::leaf(), &a0});
    } else {
      auto _f = std::move(std::get<CraneCont_Node>(_frame));
      const MemSafetyProbe28::tree &a0 = *_f.a0;
      std::shared_ptr<MemSafetyProbe28::tree> a00 = std::move(_f.a00);
      uint64_t a1 = _f.a1;
      uint64_t a10 = _f.a10;
      _stack.emplace_back(
          CraneEnter{List<uint64_t>::cons(
                         a1, List<uint64_t>::cons(a10, std::move(_result))),
                     *a00, &a0});
    }
  }
  return _result;
}

uint64_t MemSafetyProbe28::list_sum(const List<uint64_t> &l) {
  {
    const List<uint64_t> &_lc1_l0 = l;
    uint64_t _lc1_acc = UINT64_C(0);
    uint64_t _lc1_loop_acc = std::move(_lc1_acc);
    const List<uint64_t> *_lc1_loop_l0 = &_lc1_l0;
    while (true) {
      if (std::holds_alternative<typename List<uint64_t>::Nil>(
              _lc1_loop_l0->v())) {
        return _lc1_loop_acc;
      } else {
        const auto &[a0, a1] =
            std::get<typename List<uint64_t>::Cons>(_lc1_loop_l0->v());
        _lc1_loop_acc = (_lc1_loop_acc + a0);
        _lc1_loop_l0 = crane_raw(a1);
      }
    }
  }
}

/// TEST 6: Three-way recursion with non-pointer-safe second tree.
MemSafetyProbe28::tree MemSafetyProbe28::merge_trees(
    const MemSafetyProbe28::tree &t1,
    MemSafetyProbe28::tree t2) { /// CraneEnter: captures varying parameters for
                                 /// each recursive call.

  struct CraneEnter {
    MemSafetyProbe28::tree t2;
    const MemSafetyProbe28::tree *t1;
  };

  /// CraneCont_Leaf: saves [a1, a2], resumes after recursive call, then
  /// processes rest.
  struct CraneCont_Leaf {
    uint64_t a1;
    const MemSafetyProbe28::tree *a2;
  };

  /// CraneCont_Leaf_1: saves [_tmp2, a1], resumes after recursive call, then
  /// processes rest.
  struct CraneCont_Leaf_1 {
    MemSafetyProbe28::tree _tmp2;
    uint64_t a1;
  };

  /// CraneCont_Node: saves [a1, a10, a2, a20], resumes after recursive call,
  /// then processes rest.
  struct CraneCont_Node {
    uint64_t a1;
    uint64_t a10;
    const MemSafetyProbe28::tree *a2;
    std::shared_ptr<MemSafetyProbe28::tree> a20;
  };

  /// CraneCont_Node_1: saves [_tmp4, a1, a10], resumes after recursive call,
  /// then processes rest.
  struct CraneCont_Node_1 {
    MemSafetyProbe28::tree _tmp4;
    uint64_t a1;
    uint64_t a10;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont_Leaf, CraneCont_Leaf_1,
                                  CraneCont_Node, CraneCont_Node_1>;
  MemSafetyProbe28::tree _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{std::move(t2), &t1});
  /// Loopified merge_trees: CraneEnter -> CraneCont_Leaf -> CraneCont_Leaf_1 ->
  /// CraneCont_Node -> CraneCont_Node_1.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
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
          _stack.emplace_back(CraneCont_Leaf{a1, crane_raw(a2)});
          _stack.emplace_back(CraneEnter{tree::leaf(), crane_raw(a0)});
        } else {
          auto &[a00, a10, a20] =
              std::get<typename MemSafetyProbe28::tree::Node>(t2.v_mut());
          _stack.emplace_back(CraneCont_Node{a1, a10, crane_raw(a2), a20});
          _stack.emplace_back(CraneEnter{*a00, crane_raw(a0)});
        }
      }
    } else if (std::holds_alternative<CraneCont_Leaf>(_frame)) {
      auto _f = std::move(std::get<CraneCont_Leaf>(_frame));
      uint64_t a1 = _f.a1;
      const MemSafetyProbe28::tree &a2 = *_f.a2;
      _stack.emplace_back(CraneCont_Leaf_1{std::move(_result), a1});
      _stack.emplace_back(CraneEnter{tree::leaf(), &a2});
    } else if (std::holds_alternative<CraneCont_Leaf_1>(_frame)) {
      auto _f = std::move(std::get<CraneCont_Leaf_1>(_frame));
      uint64_t a1 = _f.a1;
      _result = tree::node(std::move(_f._tmp2), a1, std::move(_result));
    } else if (std::holds_alternative<CraneCont_Node>(_frame)) {
      auto _f = std::move(std::get<CraneCont_Node>(_frame));
      uint64_t a1 = _f.a1;
      uint64_t a10 = _f.a10;
      const MemSafetyProbe28::tree &a2 = *_f.a2;
      std::shared_ptr<MemSafetyProbe28::tree> a20 = std::move(_f.a20);
      _stack.emplace_back(CraneCont_Node_1{std::move(_result), a1, a10});
      _stack.emplace_back(CraneEnter{*a20, &a2});
    } else {
      auto _f = std::move(std::get<CraneCont_Node_1>(_frame));
      uint64_t a1 = _f.a1;
      uint64_t a10 = _f.a10;
      _result = tree::node(std::move(_f._tmp4), (a1 + std::move(a10)),
                           std::move(_result));
    }
  }
  return _result;
}

/// TEST 7: Deep trees to stress the optimization.
MemSafetyProbe28::tree MemSafetyProbe28::build_balanced(
    uint64_t n) { /// CraneEnter: captures varying parameters for each recursive
                  /// call.

  struct CraneEnter {
    uint64_t n;
  };

  /// CraneCont_n_: saves [n, n_], resumes after recursive call, then processes
  /// rest.
  struct CraneCont_n_ {
    uint64_t n;
    uint64_t n_;
  };

  /// CraneCont_n__1: saves [_tmp2, n], resumes after recursive call, then
  /// processes rest.
  struct CraneCont_n__1 {
    MemSafetyProbe28::tree _tmp2;
    uint64_t n;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont_n_, CraneCont_n__1>;
  MemSafetyProbe28::tree _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{n});
  /// Loopified build_balanced: CraneEnter -> CraneCont_n_ -> CraneCont_n__1.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      uint64_t n = _f.n;
      if (n <= 0) {
        _result = tree::leaf();
      } else {
        uint64_t n_ = n - 1;
        _stack.emplace_back(CraneCont_n_{n, n_});
        _stack.emplace_back(CraneEnter{n_});
      }
    } else if (std::holds_alternative<CraneCont_n_>(_frame)) {
      auto _f = std::move(std::get<CraneCont_n_>(_frame));
      uint64_t n = _f.n;
      uint64_t n_ = _f.n_;
      _stack.emplace_back(CraneCont_n__1{std::move(_result), n});
      _stack.emplace_back(CraneEnter{n_});
    } else {
      auto _f = std::move(std::get<CraneCont_n__1>(_frame));
      uint64_t n = _f.n;
      _result = tree::node(std::move(_f._tmp2), n, std::move(_result));
    }
  }
  return _result;
}
