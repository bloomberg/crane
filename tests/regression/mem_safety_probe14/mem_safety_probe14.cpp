#include "mem_safety_probe14.h"

uint64_t MemSafetyProbe14::sum_fns(
    const MemSafetyProbe14::mylist<crane::fn<uint64_t(uint64_t)>>
        &l) { /// CraneEnter: captures varying parameters for each recursive
              /// call.

  struct CraneEnter {
    const MemSafetyProbe14::mylist<crane::fn<uint64_t(uint64_t)>> *l;
  };

  /// CraneCont_Mycons: saves [a0], resumes after recursive call, then processes
  /// rest.
  struct CraneCont_Mycons {
    crane::fn<uint64_t(uint64_t)> a0;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont_Mycons>;
  uint64_t _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{&l});
  /// Loopified sum_fns: CraneEnter -> CraneCont_Mycons.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      const MemSafetyProbe14::mylist<crane::fn<uint64_t(uint64_t)>> &l = *_f.l;
      if (std::holds_alternative<typename MemSafetyProbe14::mylist<
              crane::fn<uint64_t(uint64_t)>>::Mynil>(l.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] = std::get<typename MemSafetyProbe14::mylist<
            crane::fn<uint64_t(uint64_t)>>::Mycons>(l.v());
        _stack.emplace_back(CraneCont_Mycons{a0});
        _stack.emplace_back(CraneEnter{crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<CraneCont_Mycons>(_frame));
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
  crane::fn<uint64_t(uint64_t)> f = [=](uint64_t n) {
    return (t.tree_sum() + n);
  };
  if (std::holds_alternative<typename MemSafetyProbe14::tree::Leaf>(
          t.v_mut())) {
    return f(UINT64_C(0));
  } else {
    auto &[a0, a1, a2] =
        std::get<typename MemSafetyProbe14::tree::Node>(t.v_mut());
    return ((f(std::move(a1)) + a0->tree_sum()) + a2->tree_sum());
  }
}

MemSafetyProbe14::mylist<crane::fn<uint64_t(uint64_t)>>
MemSafetyProbe14::tree_level_fns(
    const MemSafetyProbe14::tree &t,
    uint64_t depth) { /// CraneEnter: captures varying parameters for each
                      /// recursive call.

  struct CraneEnter {
    uint64_t depth;
    const MemSafetyProbe14::tree *t;
  };

  /// CraneCont_Node: saves [a1, depth, a0, a2], resumes after recursive call,
  /// then processes rest.
  struct CraneCont_Node {
    uint64_t a1;
    uint64_t depth;
    std::shared_ptr<MemSafetyProbe14::tree> a0;
    std::shared_ptr<MemSafetyProbe14::tree> a2;
  };

  /// CraneCont_Node_1: saves [_tmp2, a1, depth, a0, a2], resumes after
  /// recursive call, then processes rest.
  struct CraneCont_Node_1 {
    MemSafetyProbe14::mylist<crane::fn<uint64_t(uint64_t)>> _tmp2;
    uint64_t a1;
    uint64_t depth;
    std::shared_ptr<MemSafetyProbe14::tree> a0;
    std::shared_ptr<MemSafetyProbe14::tree> a2;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont_Node, CraneCont_Node_1>;
  MemSafetyProbe14::mylist<crane::fn<uint64_t(uint64_t)>> _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{depth, &t});
  /// Loopified tree_level_fns: CraneEnter -> CraneCont_Node ->
  /// CraneCont_Node_1.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      uint64_t depth = _f.depth;
      const MemSafetyProbe14::tree &t = *_f.t;
      if (std::holds_alternative<typename MemSafetyProbe14::tree::Leaf>(
              t.v())) {
        _result = mylist<crane::fn<uint64_t(uint64_t)>>::mynil();
      } else {
        const auto &[a0, a1, a2] =
            std::get<typename MemSafetyProbe14::tree::Node>(t.v());
        const MemSafetyProbe14::tree &a0_value = *a0;
        const MemSafetyProbe14::tree &a2_value = *a2;
        _stack.emplace_back(CraneCont_Node{a1, depth, a0, a2});
        _stack.emplace_back(CraneEnter{(UINT64_C(1) + depth), crane_raw(a0)});
      }
    } else if (std::holds_alternative<CraneCont_Node>(_frame)) {
      auto _f = std::move(std::get<CraneCont_Node>(_frame));
      uint64_t a1 = _f.a1;
      uint64_t depth = _f.depth;
      std::shared_ptr<MemSafetyProbe14::tree> a0 = std::move(_f.a0);
      std::shared_ptr<MemSafetyProbe14::tree> a2 = std::move(_f.a2);
      const MemSafetyProbe14::tree &a0_value = *a0;
      const MemSafetyProbe14::tree &a2_value = *a2;
      _stack.emplace_back(
          CraneCont_Node_1{std::move(_result), a1, depth, std::move(a0), a2});
      _stack.emplace_back(CraneEnter{(UINT64_C(1) + depth), crane_raw(a2)});
    } else {
      auto _f = std::move(std::get<CraneCont_Node_1>(_frame));
      uint64_t a1 = _f.a1;
      uint64_t depth = _f.depth;
      std::shared_ptr<MemSafetyProbe14::tree> a0 = std::move(_f.a0);
      std::shared_ptr<MemSafetyProbe14::tree> a2 = std::move(_f.a2);
      const MemSafetyProbe14::tree &a0_value = *a0;
      const MemSafetyProbe14::tree &a2_value = *a2;
      _result = mylist<crane::fn<uint64_t(uint64_t)>>::mycons(
          [=](uint64_t n) { return (((depth * UINT64_C(100)) + a1) + n); },
          mylist<crane::fn<uint64_t(uint64_t)>>::mycons(
              [=](uint64_t n) {
                return ((a0_value.tree_sum() + a2_value.tree_sum()) + n);
              },
              std::move(_f._tmp2).mylist_append(std::move(_result))));
    }
  }
  return _result;
}

/// TEST 8: Large tree stress test. Many closures, deep recursion.
MemSafetyProbe14::tree MemSafetyProbe14::make_balanced(uint64_t n) {
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
MemSafetyProbe14::collect_closures(
    const MemSafetyProbe14::tree &t) { /// CraneEnter: captures varying
                                       /// parameters for each recursive call.

  struct CraneEnter {
    const MemSafetyProbe14::tree *t;
  };

  /// CraneCont_Node: saves [a1, a2], resumes after recursive call, then
  /// processes rest.
  struct CraneCont_Node {
    uint64_t a1;
    std::shared_ptr<MemSafetyProbe14::tree> a2;
  };

  /// CraneCont_Node_1: saves [_tmp2, a1], resumes after recursive call, then
  /// processes rest.
  struct CraneCont_Node_1 {
    MemSafetyProbe14::mylist<crane::fn<uint64_t(uint64_t)>> _tmp2;
    uint64_t a1;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont_Node, CraneCont_Node_1>;
  MemSafetyProbe14::mylist<crane::fn<uint64_t(uint64_t)>> _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{&t});
  /// Loopified collect_closures: CraneEnter -> CraneCont_Node ->
  /// CraneCont_Node_1.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      const MemSafetyProbe14::tree &t = *_f.t;
      if (std::holds_alternative<typename MemSafetyProbe14::tree::Leaf>(
              t.v())) {
        _result = mylist<crane::fn<uint64_t(uint64_t)>>::mynil();
      } else {
        const auto &[a0, a1, a2] =
            std::get<typename MemSafetyProbe14::tree::Node>(t.v());
        const MemSafetyProbe14::tree &a0_value = *a0;
        const MemSafetyProbe14::tree &a2_value = *a2;
        _stack.emplace_back(CraneCont_Node{a1, a2});
        _stack.emplace_back(CraneEnter{crane_raw(a0)});
      }
    } else if (std::holds_alternative<CraneCont_Node>(_frame)) {
      auto _f = std::move(std::get<CraneCont_Node>(_frame));
      uint64_t a1 = _f.a1;
      std::shared_ptr<MemSafetyProbe14::tree> a2 = std::move(_f.a2);
      const MemSafetyProbe14::tree &a2_value = *a2;
      _stack.emplace_back(CraneCont_Node_1{std::move(_result), a1});
      _stack.emplace_back(CraneEnter{crane_raw(a2)});
    } else {
      auto _f = std::move(std::get<CraneCont_Node_1>(_frame));
      uint64_t a1 = _f.a1;
      _result = mylist<crane::fn<uint64_t(uint64_t)>>::mycons(
          [=](uint64_t n) { return (a1 + n); },
          std::move(_f._tmp2).mylist_append(std::move(_result)));
    }
  }
  return _result;
}
