#include "mem_safety_probe23.h"

uint64_t MemSafetyProbe23::tree_sum(
    const MemSafetyProbe23::tree &t) { /// CraneEnter: captures varying
                                       /// parameters for each recursive call.

  struct CraneEnter {
    const MemSafetyProbe23::tree *t;
  };

  /// CraneCont_Node: saves [a1, a2], resumes after recursive call, then
  /// processes rest.
  struct CraneCont_Node {
    uint64_t a1;
    const MemSafetyProbe23::tree *a2;
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
      const MemSafetyProbe23::tree &t = *_f.t;
      if (std::holds_alternative<typename MemSafetyProbe23::tree::Leaf>(
              t.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1, a2] =
            std::get<typename MemSafetyProbe23::tree::Node>(t.v());
        _stack.emplace_back(CraneCont_Node{a1, crane_raw(a2)});
        _stack.emplace_back(CraneEnter{crane_raw(a0)});
      }
    } else if (std::holds_alternative<CraneCont_Node>(_frame)) {
      auto _f = std::move(std::get<CraneCont_Node>(_frame));
      uint64_t a1 = _f.a1;
      const MemSafetyProbe23::tree &a2 = *_f.a2;
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

uint64_t MemSafetyProbe23::tree_size(
    const MemSafetyProbe23::tree &t) { /// CraneEnter: captures varying
                                       /// parameters for each recursive call.

  struct CraneEnter {
    const MemSafetyProbe23::tree *t;
  };

  /// CraneCont_Node: saves [a2], resumes after recursive call, then processes
  /// rest.
  struct CraneCont_Node {
    const MemSafetyProbe23::tree *a2;
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
  /// Loopified tree_size: CraneEnter -> CraneCont_Node -> CraneCont_Node_1.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      const MemSafetyProbe23::tree &t = *_f.t;
      if (std::holds_alternative<typename MemSafetyProbe23::tree::Leaf>(
              t.v())) {
        _result = UINT64_C(1);
      } else {
        const auto &[a0, a1, a2] =
            std::get<typename MemSafetyProbe23::tree::Node>(t.v());
        _stack.emplace_back(CraneCont_Node{crane_raw(a2)});
        _stack.emplace_back(CraneEnter{crane_raw(a0)});
      }
    } else if (std::holds_alternative<CraneCont_Node>(_frame)) {
      auto _f = std::move(std::get<CraneCont_Node>(_frame));
      const MemSafetyProbe23::tree &a2 = *_f.a2;
      _stack.emplace_back(CraneCont_Node_1{std::move(_result)});
      _stack.emplace_back(CraneEnter{&a2});
    } else {
      auto _f = std::move(std::get<CraneCont_Node_1>(_frame));
      _result = ((UINT64_C(1) + _f._tmp2) + std::move(_result));
    }
  }
  return _result;
}

/// TEST 1: Return the ORIGINAL tree alongside recursive child processing.
/// t escapes because it is returned. Recursive calls on l and r (children).
/// Loopifier must handle: owned param + pointer-safe children.
std::pair<MemSafetyProbe23::tree, uint64_t> MemSafetyProbe23::sum_with_original(
    const MemSafetyProbe23::tree &t) { /// CraneEnter: captures varying
                                       /// parameters for each recursive call.

  struct CraneEnter {
    const MemSafetyProbe23::tree *t;
  };

  /// CraneCont_Node: saves [a1, a2, t], resumes after recursive call, then
  /// processes rest.
  struct CraneCont_Node {
    uint64_t a1;
    const MemSafetyProbe23::tree *a2;
    MemSafetyProbe23::tree t;
  };

  /// CraneCont_Node_1: saves [a1, pl, t], resumes after recursive call, then
  /// processes rest.
  struct CraneCont_Node_1 {
    uint64_t a1;
    std::pair<MemSafetyProbe23::tree, uint64_t> pl;
    MemSafetyProbe23::tree t;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont_Node, CraneCont_Node_1>;
  std::pair<MemSafetyProbe23::tree, uint64_t> _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{&t});
  /// Loopified sum_with_original: CraneEnter -> CraneCont_Node ->
  /// CraneCont_Node_1.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      const MemSafetyProbe23::tree &t = *_f.t;
      if (std::holds_alternative<typename MemSafetyProbe23::tree::Leaf>(
              t.v())) {
        _result = std::make_pair(tree::leaf(), UINT64_C(0));
      } else {
        const auto &[a0, a1, a2] =
            std::get<typename MemSafetyProbe23::tree::Node>(t.v());
        _stack.emplace_back(CraneCont_Node{a1, crane_raw(a2), t});
        _stack.emplace_back(CraneEnter{crane_raw(a0)});
      }
    } else if (std::holds_alternative<CraneCont_Node>(_frame)) {
      auto _f = std::move(std::get<CraneCont_Node>(_frame));
      uint64_t a1 = _f.a1;
      const MemSafetyProbe23::tree &a2 = *_f.a2;
      const MemSafetyProbe23::tree &t = std::move(_f.t);
      std::pair<MemSafetyProbe23::tree, uint64_t> pl = std::move(_result);
      _stack.emplace_back(CraneCont_Node_1{a1, std::move(pl), t});
      _stack.emplace_back(CraneEnter{&a2});
    } else {
      auto _f = std::move(std::get<CraneCont_Node_1>(_frame));
      uint64_t a1 = _f.a1;
      std::pair<MemSafetyProbe23::tree, uint64_t> pl = std::move(_f.pl);
      const MemSafetyProbe23::tree &t = std::move(_f.t);
      std::pair<MemSafetyProbe23::tree, uint64_t> pr = std::move(_result);
      _result = std::make_pair(
          t, ((std::move(pl).second + a1) + std::move(pr).second));
    }
  }
  return _result;
}

/// TEST 2: Return a PAIR of the original tree and a transformed copy.
/// Forces tree to be owned; two recursive calls on children.
std::pair<MemSafetyProbe23::tree, MemSafetyProbe23::tree>
MemSafetyProbe23::dup_and_double(
    const MemSafetyProbe23::tree &t) { /// CraneEnter: captures varying
                                       /// parameters for each recursive call.

  struct CraneEnter {
    const MemSafetyProbe23::tree *t;
  };

  /// CraneCont_Node: saves [a1, a2, t], resumes after recursive call, then
  /// processes rest.
  struct CraneCont_Node {
    uint64_t a1;
    const MemSafetyProbe23::tree *a2;
    MemSafetyProbe23::tree t;
  };

  /// CraneCont_Node_1: saves [a1, pl, t], resumes after recursive call, then
  /// processes rest.
  struct CraneCont_Node_1 {
    uint64_t a1;
    std::pair<MemSafetyProbe23::tree, MemSafetyProbe23::tree> pl;
    MemSafetyProbe23::tree t;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont_Node, CraneCont_Node_1>;
  std::pair<MemSafetyProbe23::tree, MemSafetyProbe23::tree> _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{&t});
  /// Loopified dup_and_double: CraneEnter -> CraneCont_Node ->
  /// CraneCont_Node_1.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      const MemSafetyProbe23::tree &t = *_f.t;
      if (std::holds_alternative<typename MemSafetyProbe23::tree::Leaf>(
              t.v())) {
        _result = std::make_pair(tree::leaf(), tree::leaf());
      } else {
        const auto &[a0, a1, a2] =
            std::get<typename MemSafetyProbe23::tree::Node>(t.v());
        _stack.emplace_back(CraneCont_Node{a1, crane_raw(a2), t});
        _stack.emplace_back(CraneEnter{crane_raw(a0)});
      }
    } else if (std::holds_alternative<CraneCont_Node>(_frame)) {
      auto _f = std::move(std::get<CraneCont_Node>(_frame));
      uint64_t a1 = _f.a1;
      const MemSafetyProbe23::tree &a2 = *_f.a2;
      const MemSafetyProbe23::tree &t = std::move(_f.t);
      std::pair<MemSafetyProbe23::tree, MemSafetyProbe23::tree> pl =
          std::move(_result);
      _stack.emplace_back(CraneCont_Node_1{a1, std::move(pl), t});
      _stack.emplace_back(CraneEnter{&a2});
    } else {
      auto _f = std::move(std::get<CraneCont_Node_1>(_frame));
      uint64_t a1 = _f.a1;
      std::pair<MemSafetyProbe23::tree, MemSafetyProbe23::tree> pl =
          std::move(_f.pl);
      const MemSafetyProbe23::tree &t = std::move(_f.t);
      std::pair<MemSafetyProbe23::tree, MemSafetyProbe23::tree> pr =
          std::move(_result);
      _result =
          std::make_pair(t, tree::node(std::move(pl).second, (a1 * UINT64_C(2)),
                                       std::move(pr).second));
    }
  }
  return _result;
}

/// TEST 3: Store children in result alongside recursive processing.
/// l and r are extracted from match, BOTH used in result AND in
/// recursive calls. Tests whether children are correctly cloned when
/// they appear in both continuation and recursive positions.
std::pair<std::pair<MemSafetyProbe23::tree, MemSafetyProbe23::tree>, uint64_t>
MemSafetyProbe23::collect_children(
    const MemSafetyProbe23::tree &t) { /// CraneEnter: captures varying
                                       /// parameters for each recursive call.

  struct CraneEnter {
    const MemSafetyProbe23::tree *t;
  };

  /// CraneCont_Node: saves [a0, a1, a2], resumes after recursive call, then
  /// processes rest.
  struct CraneCont_Node {
    std::shared_ptr<MemSafetyProbe23::tree> a0;
    uint64_t a1;
    const MemSafetyProbe23::tree *a2;
  };

  /// CraneCont_Node_1: saves [a0, a1, a2, pl], resumes after recursive call,
  /// then processes rest.
  struct CraneCont_Node_1 {
    std::shared_ptr<MemSafetyProbe23::tree> a0;
    uint64_t a1;
    const MemSafetyProbe23::tree *a2;
    std::pair<std::pair<MemSafetyProbe23::tree, MemSafetyProbe23::tree>,
              uint64_t>
        pl;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont_Node, CraneCont_Node_1>;
  std::pair<std::pair<MemSafetyProbe23::tree, MemSafetyProbe23::tree>, uint64_t>
      _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{&t});
  /// Loopified collect_children: CraneEnter -> CraneCont_Node ->
  /// CraneCont_Node_1.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      const MemSafetyProbe23::tree &t = *_f.t;
      if (std::holds_alternative<typename MemSafetyProbe23::tree::Leaf>(
              t.v())) {
        _result = std::make_pair(std::make_pair(tree::leaf(), tree::leaf()),
                                 UINT64_C(0));
      } else {
        const auto &[a0, a1, a2] =
            std::get<typename MemSafetyProbe23::tree::Node>(t.v());
        _stack.emplace_back(CraneCont_Node{a0, a1, crane_raw(a2)});
        _stack.emplace_back(CraneEnter{crane_raw(a0)});
      }
    } else if (std::holds_alternative<CraneCont_Node>(_frame)) {
      auto _f = std::move(std::get<CraneCont_Node>(_frame));
      std::shared_ptr<MemSafetyProbe23::tree> a0 = std::move(_f.a0);
      uint64_t a1 = _f.a1;
      const MemSafetyProbe23::tree &a2 = *_f.a2;
      std::pair<std::pair<MemSafetyProbe23::tree, MemSafetyProbe23::tree>,
                uint64_t>
          pl = std::move(_result);
      _stack.emplace_back(
          CraneCont_Node_1{std::move(a0), a1, &a2, std::move(pl)});
      _stack.emplace_back(CraneEnter{&a2});
    } else {
      auto _f = std::move(std::get<CraneCont_Node_1>(_frame));
      std::shared_ptr<MemSafetyProbe23::tree> a0 = std::move(_f.a0);
      uint64_t a1 = _f.a1;
      const MemSafetyProbe23::tree &a2 = *_f.a2;
      std::pair<std::pair<MemSafetyProbe23::tree, MemSafetyProbe23::tree>,
                uint64_t>
          pl = std::move(_f.pl);
      std::pair<std::pair<MemSafetyProbe23::tree, MemSafetyProbe23::tree>,
                uint64_t>
          pr = std::move(_result);
      uint64_t s = (([&]() -> uint64_t {
                      auto [p, n] = std::move(pl);
                      auto [_x, _x0] = std::move(p);
                      return n;
                    }() + a1) +
                        [&]() -> uint64_t {
        auto [p, n] = std::move(pr);
        auto [_x, _x0] = std::move(p);
        return n;
      }());
      _result = std::make_pair(std::make_pair(*a0, a2), s);
    }
  }
  return _result;
}

/// TEST 4: Recursive function that rebuilds tree with an
/// ACCUMULATOR that captures the original tree. The accumulator
/// forces the tree to be owned. Two recursive calls on children.
std::pair<MemSafetyProbe23::tree, uint64_t> MemSafetyProbe23::sum_with_acc(
    const MemSafetyProbe23::tree &t,
    uint64_t acc) { /// CraneEnter: captures varying parameters for each
                    /// recursive call.

  struct CraneEnter {
    uint64_t acc;
    const MemSafetyProbe23::tree *t;
  };

  /// CraneCont_Node: saves [a1, a2], resumes after recursive call, then
  /// processes rest.
  struct CraneCont_Node {
    uint64_t a1;
    const MemSafetyProbe23::tree *a2;
  };

  /// CraneCont_Node_1: saves [a1, pl], resumes after recursive call, then
  /// processes rest.
  struct CraneCont_Node_1 {
    uint64_t a1;
    std::pair<MemSafetyProbe23::tree, uint64_t> pl;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont_Node, CraneCont_Node_1>;
  std::pair<MemSafetyProbe23::tree, uint64_t> _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{acc, &t});
  /// Loopified sum_with_acc: CraneEnter -> CraneCont_Node -> CraneCont_Node_1.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      uint64_t acc = _f.acc;
      const MemSafetyProbe23::tree &t = *_f.t;
      if (std::holds_alternative<typename MemSafetyProbe23::tree::Leaf>(
              t.v())) {
        _result = std::make_pair(tree::leaf(), acc);
      } else {
        const auto &[a0, a1, a2] =
            std::get<typename MemSafetyProbe23::tree::Node>(t.v());
        _stack.emplace_back(CraneCont_Node{a1, crane_raw(a2)});
        _stack.emplace_back(CraneEnter{(acc + a1), crane_raw(a0)});
      }
    } else if (std::holds_alternative<CraneCont_Node>(_frame)) {
      auto _f = std::move(std::get<CraneCont_Node>(_frame));
      uint64_t a1 = _f.a1;
      const MemSafetyProbe23::tree &a2 = *_f.a2;
      std::pair<MemSafetyProbe23::tree, uint64_t> pl = std::move(_result);
      _stack.emplace_back(CraneCont_Node_1{a1, pl});
      _stack.emplace_back(CraneEnter{pl.second, &a2});
    } else {
      auto _f = std::move(std::get<CraneCont_Node_1>(_frame));
      uint64_t a1 = _f.a1;
      std::pair<MemSafetyProbe23::tree, uint64_t> pl = std::move(_f.pl);
      std::pair<MemSafetyProbe23::tree, uint64_t> pr = std::move(_result);
      _result = std::make_pair(tree::node(std::move(pl).first, a1, pr.first),
                               pr.second);
    }
  }
  return _result;
}

/// TEST 5: Function using tree_sum on children INSIDE the same
/// expression as recursive calls. Tests that child pointers remain
/// valid when other operations happen on the same tree.
std::pair<uint64_t, uint64_t> MemSafetyProbe23::interleaved_ops(
    const MemSafetyProbe23::tree &t) { /// CraneEnter: captures varying
                                       /// parameters for each recursive call.

  struct CraneEnter {
    const MemSafetyProbe23::tree *t;
  };

  /// CraneCont_Node: saves [a1, a2, sl, sr], resumes after recursive call, then
  /// processes rest.
  struct CraneCont_Node {
    uint64_t a1;
    const MemSafetyProbe23::tree *a2;
    uint64_t sl;
    uint64_t sr;
  };

  /// CraneCont_Node_1: saves [a1, pl, sl, sr], resumes after recursive call,
  /// then processes rest.
  struct CraneCont_Node_1 {
    uint64_t a1;
    std::pair<uint64_t, uint64_t> pl;
    uint64_t sl;
    uint64_t sr;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont_Node, CraneCont_Node_1>;
  std::pair<uint64_t, uint64_t> _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{&t});
  /// Loopified interleaved_ops: CraneEnter -> CraneCont_Node ->
  /// CraneCont_Node_1.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      const MemSafetyProbe23::tree &t = *_f.t;
      if (std::holds_alternative<typename MemSafetyProbe23::tree::Leaf>(
              t.v())) {
        _result = std::make_pair(UINT64_C(0), UINT64_C(0));
      } else {
        const auto &[a0, a1, a2] =
            std::get<typename MemSafetyProbe23::tree::Node>(t.v());
        uint64_t sl = tree_sum(*a0);
        uint64_t sr = tree_sum(*a2);
        _stack.emplace_back(CraneCont_Node{a1, crane_raw(a2), sl, sr});
        _stack.emplace_back(CraneEnter{crane_raw(a0)});
      }
    } else if (std::holds_alternative<CraneCont_Node>(_frame)) {
      auto _f = std::move(std::get<CraneCont_Node>(_frame));
      uint64_t a1 = _f.a1;
      const MemSafetyProbe23::tree &a2 = *_f.a2;
      uint64_t sl = _f.sl;
      uint64_t sr = _f.sr;
      std::pair<uint64_t, uint64_t> pl = std::move(_result);
      _stack.emplace_back(CraneCont_Node_1{a1, pl, sl, sr});
      _stack.emplace_back(CraneEnter{&a2});
    } else {
      auto _f = std::move(std::get<CraneCont_Node_1>(_frame));
      uint64_t a1 = _f.a1;
      std::pair<uint64_t, uint64_t> pl = _f.pl;
      uint64_t sl = _f.sl;
      uint64_t sr = _f.sr;
      std::pair<uint64_t, uint64_t> pr = std::move(_result);
      _result = std::make_pair(
          ((sl + a1) + sr), ((std::move(pl).first + a1) + std::move(pr).first));
    }
  }
  return _result;
}

/// TEST 6: Nested tree type — tree of trees. Tests clone correctness
/// for deeply nested value types.
uint64_t MemSafetyProbe23::flatten_tree_of_trees(
    const MemSafetyProbe23::tree &t,
    const MemSafetyProbe23::tree
        &inner) { /// CraneEnter: captures varying parameters for each recursive
                  /// call.

  struct CraneEnter {
    MemSafetyProbe23::tree inner;
    const MemSafetyProbe23::tree *t;
  };

  /// CraneCont_Node: saves [a2, inner], resumes after recursive call, then
  /// processes rest.
  struct CraneCont_Node {
    const MemSafetyProbe23::tree *a2;
    MemSafetyProbe23::tree inner;
  };

  /// CraneCont_Node_1: saves [_tmp2], resumes after recursive call, then
  /// processes rest.
  struct CraneCont_Node_1 {
    uint64_t _tmp2;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont_Node, CraneCont_Node_1>;
  uint64_t _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{inner, &t});
  /// Loopified flatten_tree_of_trees: CraneEnter -> CraneCont_Node ->
  /// CraneCont_Node_1.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      const MemSafetyProbe23::tree &inner = std::move(_f.inner);
      const MemSafetyProbe23::tree &t = *_f.t;
      if (std::holds_alternative<typename MemSafetyProbe23::tree::Leaf>(
              t.v())) {
        _result = tree_sum(inner);
      } else {
        const auto &[a0, a1, a2] =
            std::get<typename MemSafetyProbe23::tree::Node>(t.v());
        MemSafetyProbe23::tree new_inner = tree::node(inner, a1, tree::leaf());
        _stack.emplace_back(CraneCont_Node{crane_raw(a2), inner});
        _stack.emplace_back(CraneEnter{std::move(new_inner), crane_raw(a0)});
      }
    } else if (std::holds_alternative<CraneCont_Node>(_frame)) {
      auto _f = std::move(std::get<CraneCont_Node>(_frame));
      const MemSafetyProbe23::tree &a2 = *_f.a2;
      const MemSafetyProbe23::tree &inner = std::move(_f.inner);
      _stack.emplace_back(CraneCont_Node_1{std::move(_result)});
      _stack.emplace_back(CraneEnter{inner, &a2});
    } else {
      auto _f = std::move(std::get<CraneCont_Node_1>(_frame));
      _result = (_f._tmp2 + std::move(_result));
    }
  }
  return _result;
}

/// TEST 7: Two recursive calls where one takes a CONSTRUCTED tree
/// with t embedded AND another takes a child of t.
/// Forces t to NOT be pointer-safe. The After frame saves
/// state for the child-based call.
uint64_t MemSafetyProbe23::mixed_recurse(
    const MemSafetyProbe23::tree &t,
    uint64_t n) { /// CraneEnter: captures varying parameters for each recursive
                  /// call.

  struct CraneEnter {
    uint64_t n;
    MemSafetyProbe23::tree t;
  };

  /// CraneCont_Node: saves [a2, n_], resumes after recursive call, then
  /// processes rest.
  struct CraneCont_Node {
    std::shared_ptr<MemSafetyProbe23::tree> a2;
    uint64_t n_;
  };

  /// CraneCont_Node_1: saves [_tmp2], resumes after recursive call, then
  /// processes rest.
  struct CraneCont_Node_1 {
    uint64_t _tmp2;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont_Node, CraneCont_Node_1>;
  uint64_t _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{n, t});
  /// Loopified mixed_recurse: CraneEnter -> CraneCont_Node -> CraneCont_Node_1.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      uint64_t n = _f.n;
      const MemSafetyProbe23::tree &t = std::move(_f.t);
      if (n <= 0) {
        _result = tree_sum(t);
      } else {
        uint64_t n_ = n - 1;
        if (std::holds_alternative<typename MemSafetyProbe23::tree::Leaf>(
                t.v())) {
          _result = UINT64_C(0);
        } else {
          const auto &[a0, a1, a2] =
              std::get<typename MemSafetyProbe23::tree::Node>(t.v());
          _stack.emplace_back(CraneCont_Node{a2, n_});
          _stack.emplace_back(CraneEnter{n_, tree::node(t, a1, tree::leaf())});
        }
      }
    } else if (std::holds_alternative<CraneCont_Node>(_frame)) {
      auto _f = std::move(std::get<CraneCont_Node>(_frame));
      std::shared_ptr<MemSafetyProbe23::tree> a2 = std::move(_f.a2);
      uint64_t n_ = _f.n_;
      _stack.emplace_back(CraneCont_Node_1{std::move(_result)});
      _stack.emplace_back(CraneEnter{n_, *a2});
    } else {
      auto _f = std::move(std::get<CraneCont_Node_1>(_frame));
      _result = (_f._tmp2 + std::move(_result));
    }
  }
  return _result;
}

/// TEST 8: Three-way split: function returns original tree AND
/// uses tree_size on children. Forces tree owned; exercises
/// the interplay between clone, move, and raw pointer in
/// continuation frames.
std::pair<MemSafetyProbe23::tree, uint64_t> MemSafetyProbe23::annotate_sizes(
    const MemSafetyProbe23::tree &t) { /// CraneEnter: captures varying
                                       /// parameters for each recursive call.

  struct CraneEnter {
    const MemSafetyProbe23::tree *t;
  };

  /// CraneCont_Node: saves [a1, a2, sl, sr], resumes after recursive call, then
  /// processes rest.
  struct CraneCont_Node {
    uint64_t a1;
    const MemSafetyProbe23::tree *a2;
    uint64_t sl;
    uint64_t sr;
  };

  /// CraneCont_Node_1: saves [a1, pl, sl, sr], resumes after recursive call,
  /// then processes rest.
  struct CraneCont_Node_1 {
    uint64_t a1;
    std::pair<MemSafetyProbe23::tree, uint64_t> pl;
    uint64_t sl;
    uint64_t sr;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont_Node, CraneCont_Node_1>;
  std::pair<MemSafetyProbe23::tree, uint64_t> _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{&t});
  /// Loopified annotate_sizes: CraneEnter -> CraneCont_Node ->
  /// CraneCont_Node_1.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      const MemSafetyProbe23::tree &t = *_f.t;
      if (std::holds_alternative<typename MemSafetyProbe23::tree::Leaf>(
              t.v())) {
        _result = std::make_pair(tree::leaf(), UINT64_C(0));
      } else {
        const auto &[a0, a1, a2] =
            std::get<typename MemSafetyProbe23::tree::Node>(t.v());
        uint64_t sl = tree_size(*a0);
        uint64_t sr = tree_size(*a2);
        _stack.emplace_back(CraneCont_Node{a1, crane_raw(a2), sl, sr});
        _stack.emplace_back(CraneEnter{crane_raw(a0)});
      }
    } else if (std::holds_alternative<CraneCont_Node>(_frame)) {
      auto _f = std::move(std::get<CraneCont_Node>(_frame));
      uint64_t a1 = _f.a1;
      const MemSafetyProbe23::tree &a2 = *_f.a2;
      uint64_t sl = _f.sl;
      uint64_t sr = _f.sr;
      std::pair<MemSafetyProbe23::tree, uint64_t> pl = std::move(_result);
      _stack.emplace_back(CraneCont_Node_1{a1, std::move(pl), sl, sr});
      _stack.emplace_back(CraneEnter{&a2});
    } else {
      auto _f = std::move(std::get<CraneCont_Node_1>(_frame));
      uint64_t a1 = _f.a1;
      std::pair<MemSafetyProbe23::tree, uint64_t> pl = std::move(_f.pl);
      uint64_t sl = _f.sl;
      uint64_t sr = _f.sr;
      std::pair<MemSafetyProbe23::tree, uint64_t> pr = std::move(_result);
      _result = std::make_pair(tree::node(pl.first, ((a1 + sl) + sr), pr.first),
                               ((pl.second + pr.second) + UINT64_C(1)));
    }
  }
  return _result;
}
