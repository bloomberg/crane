#include "mem_safety_probe14.h"

uint64_t MemSafetyProbe14::sum_fns(
    const MemSafetyProbe14::mylist<crane::fn<uint64_t(uint64_t)>>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const MemSafetyProbe14::mylist<crane::fn<uint64_t(uint64_t)>> *l;
  };

  /// _Cont_Mycons: saves [a0], resumes after recursive call, then processes
  /// rest.
  struct _Cont_Mycons {
    crane::fn<uint64_t(uint64_t)> a0;
  };

  using _Frame = std::variant<_Enter, _Cont_Mycons>;
  uint64_t _result{};
  crane::small_vector<_Frame> _stack;
  _stack.emplace_back(_Enter{&l});
  /// Loopified sum_fns: _Enter -> _Cont_Mycons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const MemSafetyProbe14::mylist<crane::fn<uint64_t(uint64_t)>> &l = *_f.l;
      if (std::holds_alternative<typename MemSafetyProbe14::mylist<
              crane::fn<uint64_t(uint64_t)>>::Mynil>(l.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] = std::get<typename MemSafetyProbe14::mylist<
            crane::fn<uint64_t(uint64_t)>>::Mycons>(l.v());
        _stack.emplace_back(_Cont_Mycons{a0});
        _stack.emplace_back(_Enter{crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<_Cont_Mycons>(_frame));
      crane::fn<uint64_t(uint64_t)> a0 = std::move(_f.a0);
      uint64_t r_ = std::move(_result);
      _result = (a0(UINT64_C(0)) + r_);
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
    uint64_t depth) { /// _Enter: captures varying parameters for each recursive
                      /// call.

  struct _Enter {
    uint64_t depth;
    const MemSafetyProbe14::tree *t;
  };

  /// _Cont_Node: saves [a1, depth, a0, a2], resumes after recursive call, then
  /// processes rest.
  struct _Cont_Node {
    uint64_t a1;
    uint64_t depth;
    std::shared_ptr<MemSafetyProbe14::tree> a0;
    std::shared_ptr<MemSafetyProbe14::tree> a2;
  };

  /// _Cont_Node_1: saves [a1, depth, r_, a0, a2], resumes after recursive call,
  /// then processes rest.
  struct _Cont_Node_1 {
    uint64_t a1;
    uint64_t depth;
    MemSafetyProbe14::mylist<crane::fn<uint64_t(uint64_t)>> r_;
    std::shared_ptr<MemSafetyProbe14::tree> a0;
    std::shared_ptr<MemSafetyProbe14::tree> a2;
  };

  using _Frame = std::variant<_Enter, _Cont_Node, _Cont_Node_1>;
  MemSafetyProbe14::mylist<crane::fn<uint64_t(uint64_t)>> _result{};
  crane::small_vector<_Frame> _stack;
  _stack.emplace_back(_Enter{depth, &t});
  /// Loopified tree_level_fns: _Enter -> _Cont_Node -> _Cont_Node_1.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
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
        _stack.emplace_back(_Cont_Node{a1, depth, a0, a2});
        _stack.emplace_back(_Enter{(UINT64_C(1) + depth), crane_raw(a0)});
      }
    } else if (std::holds_alternative<_Cont_Node>(_frame)) {
      auto _f = std::move(std::get<_Cont_Node>(_frame));
      uint64_t a1 = _f.a1;
      uint64_t depth = _f.depth;
      std::shared_ptr<MemSafetyProbe14::tree> a0 = std::move(_f.a0);
      std::shared_ptr<MemSafetyProbe14::tree> a2 = std::move(_f.a2);
      MemSafetyProbe14::mylist<crane::fn<uint64_t(uint64_t)>> r_ =
          std::move(_result);
      const MemSafetyProbe14::tree &a0_value = *a0;
      const MemSafetyProbe14::tree &a2_value = *a2;
      _stack.emplace_back(
          _Cont_Node_1{a1, depth, std::move(r_), std::move(a0), a2});
      _stack.emplace_back(_Enter{(UINT64_C(1) + depth), crane_raw(a2)});
    } else {
      auto _f = std::move(std::get<_Cont_Node_1>(_frame));
      uint64_t a1 = _f.a1;
      uint64_t depth = _f.depth;
      MemSafetyProbe14::mylist<crane::fn<uint64_t(uint64_t)>> r_ =
          std::move(_f.r_);
      std::shared_ptr<MemSafetyProbe14::tree> a0 = std::move(_f.a0);
      std::shared_ptr<MemSafetyProbe14::tree> a2 = std::move(_f.a2);
      MemSafetyProbe14::mylist<crane::fn<uint64_t(uint64_t)>> r_0 =
          std::move(_result);
      const MemSafetyProbe14::tree &a0_value = *a0;
      const MemSafetyProbe14::tree &a2_value = *a2;
      _result = mylist<crane::fn<uint64_t(uint64_t)>>::mycons(
          [=](uint64_t n) { return (((depth * UINT64_C(100)) + a1) + n); },
          mylist<crane::fn<uint64_t(uint64_t)>>::mycons(
              [=](uint64_t n) {
                return ((a0_value.tree_sum() + a2_value.tree_sum()) + n);
              },
              std::move(r_).mylist_append(std::move(r_0))));
    }
  }
  return _result;
}

/// TEST 8: Large tree stress test. Many closures, deep recursion.
MemSafetyProbe14::tree MemSafetyProbe14::make_balanced(uint64_t n) {
  std::shared_ptr<MemSafetyProbe14::tree> _head{};
  std::shared_ptr<MemSafetyProbe14::tree> *_write = &_head;
  uint64_t _loop_n = std::move(n);
  while (true) {
    if (_loop_n <= 0) {
      *_write = std::make_shared<MemSafetyProbe14::tree>(tree::leaf());
      break;
    } else {
      uint64_t n_ = _loop_n - 1;
      auto _cell = std::make_shared<MemSafetyProbe14::tree>(
          typename MemSafetyProbe14::tree::Node(
              nullptr, _loop_n,
              std::make_shared<MemSafetyProbe14::tree>(tree::leaf())));
      *_write = std::move(_cell);
      _write =
          &std::get<typename MemSafetyProbe14::tree::Node>((*_write)->v_mut())
               .a0;
      _loop_n = n_;
      continue;
    }
  }
  return std::move(*_head);
}

MemSafetyProbe14::mylist<crane::fn<uint64_t(uint64_t)>>
MemSafetyProbe14::collect_closures(
    const MemSafetyProbe14::tree
        &t) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const MemSafetyProbe14::tree *t;
  };

  /// _Cont_Node: saves [a1, a2], resumes after recursive call, then processes
  /// rest.
  struct _Cont_Node {
    uint64_t a1;
    std::shared_ptr<MemSafetyProbe14::tree> a2;
  };

  /// _Cont_Node_1: saves [a1, r_], resumes after recursive call, then processes
  /// rest.
  struct _Cont_Node_1 {
    uint64_t a1;
    MemSafetyProbe14::mylist<crane::fn<uint64_t(uint64_t)>> r_;
  };

  using _Frame = std::variant<_Enter, _Cont_Node, _Cont_Node_1>;
  MemSafetyProbe14::mylist<crane::fn<uint64_t(uint64_t)>> _result{};
  crane::small_vector<_Frame> _stack;
  _stack.emplace_back(_Enter{&t});
  /// Loopified collect_closures: _Enter -> _Cont_Node -> _Cont_Node_1.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const MemSafetyProbe14::tree &t = *_f.t;
      if (std::holds_alternative<typename MemSafetyProbe14::tree::Leaf>(
              t.v())) {
        _result = mylist<crane::fn<uint64_t(uint64_t)>>::mynil();
      } else {
        const auto &[a0, a1, a2] =
            std::get<typename MemSafetyProbe14::tree::Node>(t.v());
        const MemSafetyProbe14::tree &a0_value = *a0;
        const MemSafetyProbe14::tree &a2_value = *a2;
        _stack.emplace_back(_Cont_Node{a1, a2});
        _stack.emplace_back(_Enter{crane_raw(a0)});
      }
    } else if (std::holds_alternative<_Cont_Node>(_frame)) {
      auto _f = std::move(std::get<_Cont_Node>(_frame));
      uint64_t a1 = _f.a1;
      std::shared_ptr<MemSafetyProbe14::tree> a2 = std::move(_f.a2);
      MemSafetyProbe14::mylist<crane::fn<uint64_t(uint64_t)>> r_ =
          std::move(_result);
      const MemSafetyProbe14::tree &a2_value = *a2;
      _stack.emplace_back(_Cont_Node_1{a1, std::move(r_)});
      _stack.emplace_back(_Enter{crane_raw(a2)});
    } else {
      auto _f = std::move(std::get<_Cont_Node_1>(_frame));
      uint64_t a1 = _f.a1;
      MemSafetyProbe14::mylist<crane::fn<uint64_t(uint64_t)>> r_ =
          std::move(_f.r_);
      MemSafetyProbe14::mylist<crane::fn<uint64_t(uint64_t)>> r_0 =
          std::move(_result);
      _result = mylist<crane::fn<uint64_t(uint64_t)>>::mycons(
          [=](uint64_t n) { return (a1 + n); },
          std::move(r_).mylist_append(std::move(r_0)));
    }
  }
  return _result;
}
