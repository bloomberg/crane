#include "mem_safety_probe13.h"

uint64_t MemSafetyProbe13::sum_list(
    const MemSafetyProbe13::mylist<uint64_t>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const MemSafetyProbe13::mylist<uint64_t> *l;
  };

  /// _Cont_Mycons: saves [a0], resumes after recursive call, then processes
  /// rest.
  struct _Cont_Mycons {
    uint64_t a0;
  };

  using _Frame = std::variant<_Enter, _Cont_Mycons>;
  uint64_t _result{};
  crane::small_vector<_Frame> _stack;
  _stack.emplace_back(_Enter{&l});
  /// Loopified sum_list: _Enter -> _Cont_Mycons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const MemSafetyProbe13::mylist<uint64_t> &l = *_f.l;
      if (std::holds_alternative<
              typename MemSafetyProbe13::mylist<uint64_t>::Mynil>(l.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] =
            std::get<typename MemSafetyProbe13::mylist<uint64_t>::Mycons>(
                l.v());
        _stack.emplace_back(_Cont_Mycons{a0});
        _stack.emplace_back(_Enter{crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<_Cont_Mycons>(_frame));
      uint64_t a0 = _f.a0;
      _result = (a0 + std::move(_result));
    }
  }
  return _result;
}

/// TEST 1: Double-recursion on tree where both subtrees
/// are used in closures AND in recursive calls.
/// Tests if the flatten optimization moves unique_ptr fields
/// that are also captured by closures.
std::pair<MemSafetyProbe13::mylist<uint64_t>,
          MemSafetyProbe13::mylist<crane::fn<uint64_t(uint64_t)>>>
MemSafetyProbe13::tree_vals_and_fns(
    const MemSafetyProbe13::tree
        &t) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const MemSafetyProbe13::tree *t;
  };

  /// _Cont_Node: saves [a1, a0, a2], resumes after recursive call, then
  /// processes rest.
  struct _Cont_Node {
    uint64_t a1;
    std::shared_ptr<MemSafetyProbe13::tree> a0;
    std::shared_ptr<MemSafetyProbe13::tree> a2;
  };

  /// _Cont_lvals: saves [a1, lfns, lvals, a0, a2], resumes after recursive
  /// call, then processes rest.
  struct _Cont_lvals {
    uint64_t a1;
    MemSafetyProbe13::mylist<crane::fn<uint64_t(uint64_t)>> lfns;
    MemSafetyProbe13::mylist<uint64_t> lvals;
    std::shared_ptr<MemSafetyProbe13::tree> a0;
    std::shared_ptr<MemSafetyProbe13::tree> a2;
  };

  using _Frame = std::variant<_Enter, _Cont_Node, _Cont_lvals>;
  std::pair<MemSafetyProbe13::mylist<uint64_t>,
            MemSafetyProbe13::mylist<crane::fn<uint64_t(uint64_t)>>>
      _result{};
  crane::small_vector<_Frame> _stack;
  _stack.emplace_back(_Enter{&t});
  /// Loopified tree_vals_and_fns: _Enter -> _Cont_Node -> _Cont_lvals.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const MemSafetyProbe13::tree &t = *_f.t;
      if (std::holds_alternative<typename MemSafetyProbe13::tree::Leaf>(
              t.v())) {
        _result =
            std::make_pair(mylist<uint64_t>::mynil(),
                           mylist<crane::fn<uint64_t(uint64_t)>>::mynil());
      } else {
        const auto &[a0, a1, a2] =
            std::get<typename MemSafetyProbe13::tree::Node>(t.v());
        const MemSafetyProbe13::tree &a0_value = *a0;
        const MemSafetyProbe13::tree &a2_value = *a2;
        _stack.emplace_back(_Cont_Node{a1, a0, a2});
        _stack.emplace_back(_Enter{crane_raw(a0)});
      }
    } else if (std::holds_alternative<_Cont_Node>(_frame)) {
      auto _f = std::move(std::get<_Cont_Node>(_frame));
      uint64_t a1 = _f.a1;
      std::shared_ptr<MemSafetyProbe13::tree> a0 = std::move(_f.a0);
      std::shared_ptr<MemSafetyProbe13::tree> a2 = std::move(_f.a2);
      const MemSafetyProbe13::tree &a0_value = *a0;
      const MemSafetyProbe13::tree &a2_value = *a2;
      auto [lvals, lfns] = std::move(_result);
      _stack.emplace_back(_Cont_lvals{a1, lfns, lvals, std::move(a0), a2});
      _stack.emplace_back(_Enter{crane_raw(a2)});
    } else {
      auto _f = std::move(std::get<_Cont_lvals>(_frame));
      uint64_t a1 = _f.a1;
      MemSafetyProbe13::mylist<crane::fn<uint64_t(uint64_t)>> lfns =
          std::move(_f.lfns);
      MemSafetyProbe13::mylist<uint64_t> lvals = std::move(_f.lvals);
      std::shared_ptr<MemSafetyProbe13::tree> a0 = std::move(_f.a0);
      std::shared_ptr<MemSafetyProbe13::tree> a2 = std::move(_f.a2);
      const MemSafetyProbe13::tree &a0_value = *a0;
      const MemSafetyProbe13::tree &a2_value = *a2;
      auto [rvals, rfns] = std::move(_result);
      crane::fn<uint64_t(uint64_t)> f = [=](uint64_t n) {
        return ((a0_value.tree_sum() + a2_value.tree_sum()) + n);
      };
      _result = std::make_pair(
          mylist<uint64_t>::mycons(a1, std::move(lvals).app(std::move(rvals))),
          mylist<crane::fn<uint64_t(uint64_t)>>::mycons(
              f, std::move(lfns).app(std::move(rfns))));
    }
  }
  return _result;
}

/// TEST 4: Deeply nested tree with closures at EVERY level.
/// Each closure captures values from its level AND from the parent.
/// Tests stack depth and closure lifetime with deep nesting.
MemSafetyProbe13::tree MemSafetyProbe13::make_deep(uint64_t n) {
  std::shared_ptr<MemSafetyProbe13::tree> _head{};
  std::shared_ptr<MemSafetyProbe13::tree> *_write = &_head;
  uint64_t _loop_n = std::move(n);
  while (true) {
    if (_loop_n <= 0) {
      *_write = std::make_shared<MemSafetyProbe13::tree>(tree::leaf());
      break;
    } else {
      uint64_t n_ = _loop_n - 1;
      auto _cell = std::make_shared<MemSafetyProbe13::tree>(
          typename MemSafetyProbe13::tree::Node(
              nullptr, _loop_n,
              std::make_shared<MemSafetyProbe13::tree>(tree::leaf())));
      *_write = std::move(_cell);
      _write =
          &std::get<typename MemSafetyProbe13::tree::Node>((*_write)->v_mut())
               .a0;
      _loop_n = n_;
      continue;
    }
  }
  return std::move(*_head);
}

MemSafetyProbe13::mylist<crane::fn<uint64_t(uint64_t)>>
MemSafetyProbe13::depth_fns(const MemSafetyProbe13::tree &t,
                            uint64_t parent_val) {
  std::shared_ptr<MemSafetyProbe13::mylist<crane::fn<uint64_t(uint64_t)>>>
      _head{};
  std::shared_ptr<MemSafetyProbe13::mylist<crane::fn<uint64_t(uint64_t)>>>
      *_write = &_head;
  uint64_t _loop_parent_val = std::move(parent_val);
  MemSafetyProbe13::tree _loop_t = t;
  while (true) {
    if (std::holds_alternative<typename MemSafetyProbe13::tree::Leaf>(
            _loop_t.v())) {
      *_write = std::make_shared<
          MemSafetyProbe13::mylist<crane::fn<uint64_t(uint64_t)>>>(
          mylist<crane::fn<uint64_t(uint64_t)>>::mynil());
      break;
    } else {
      const auto &[a0, a1, a2] =
          std::get<typename MemSafetyProbe13::tree::Node>(_loop_t.v());
      const MemSafetyProbe13::tree &a0_value = *a0;
      crane::fn<uint64_t(uint64_t)> f = [=](uint64_t n) {
        return ((_loop_parent_val + a1) + n);
      };
      auto _cell = std::make_shared<
          MemSafetyProbe13::mylist<crane::fn<uint64_t(uint64_t)>>>(
          typename MemSafetyProbe13::mylist<
              crane::fn<uint64_t(uint64_t)>>::Mycons(std::move(f), nullptr));
      *_write = std::move(_cell);
      _write = &std::get<typename MemSafetyProbe13::mylist<
          crane::fn<uint64_t(uint64_t)>>::Mycons>((*_write)->v_mut())
                    .a1;
      _loop_parent_val = a1;
      _loop_t = a0_value;
      continue;
    }
  }
  return std::move(*_head);
}

MemSafetyProbe13::ftree MemSafetyProbe13::tree_to_ftree(
    const MemSafetyProbe13::tree
        &t) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const MemSafetyProbe13::tree *t;
  };

  /// _Cont_Node: saves [a1, a2], resumes after recursive call, then processes
  /// rest.
  struct _Cont_Node {
    uint64_t a1;
    std::shared_ptr<MemSafetyProbe13::tree> a2;
  };

  /// _Cont_Node_1: saves [_tmp2, a1], resumes after recursive call, then
  /// processes rest.
  struct _Cont_Node_1 {
    MemSafetyProbe13::ftree _tmp2;
    uint64_t a1;
  };

  using _Frame = std::variant<_Enter, _Cont_Node, _Cont_Node_1>;
  MemSafetyProbe13::ftree _result{};
  crane::small_vector<_Frame> _stack;
  _stack.emplace_back(_Enter{&t});
  /// Loopified tree_to_ftree: _Enter -> _Cont_Node -> _Cont_Node_1.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const MemSafetyProbe13::tree &t = *_f.t;
      if (std::holds_alternative<typename MemSafetyProbe13::tree::Leaf>(
              t.v())) {
        _result = ftree::fleaf();
      } else {
        const auto &[a0, a1, a2] =
            std::get<typename MemSafetyProbe13::tree::Node>(t.v());
        const MemSafetyProbe13::tree &a0_value = *a0;
        const MemSafetyProbe13::tree &a2_value = *a2;
        _stack.emplace_back(_Cont_Node{a1, a2});
        _stack.emplace_back(_Enter{crane_raw(a0)});
      }
    } else if (std::holds_alternative<_Cont_Node>(_frame)) {
      auto _f = std::move(std::get<_Cont_Node>(_frame));
      uint64_t a1 = _f.a1;
      std::shared_ptr<MemSafetyProbe13::tree> a2 = std::move(_f.a2);
      const MemSafetyProbe13::tree &a2_value = *a2;
      _stack.emplace_back(_Cont_Node_1{std::move(_result), a1});
      _stack.emplace_back(_Enter{crane_raw(a2)});
    } else {
      auto _f = std::move(std::get<_Cont_Node_1>(_frame));
      uint64_t a1 = _f.a1;
      _result = ftree::fnode(
          std::move(_f._tmp2), [=](uint64_t n) { return (a1 + n); },
          std::move(_result));
    }
  }
  return _result;
}

/// TEST 6: Flatten a tree of lists into a single list,
/// where each list element is a closure.
MemSafetyProbe13::mylist<crane::fn<uint64_t(uint64_t)>>
MemSafetyProbe13::flatten_tree_fns(
    const MemSafetyProbe13::tree
        &t) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const MemSafetyProbe13::tree *t;
  };

  /// _Cont_Node: saves [a1, a2], resumes after recursive call, then processes
  /// rest.
  struct _Cont_Node {
    uint64_t a1;
    std::shared_ptr<MemSafetyProbe13::tree> a2;
  };

  /// _Cont_Node_1: saves [_tmp2, a1], resumes after recursive call, then
  /// processes rest.
  struct _Cont_Node_1 {
    MemSafetyProbe13::mylist<crane::fn<uint64_t(uint64_t)>> _tmp2;
    uint64_t a1;
  };

  using _Frame = std::variant<_Enter, _Cont_Node, _Cont_Node_1>;
  MemSafetyProbe13::mylist<crane::fn<uint64_t(uint64_t)>> _result{};
  crane::small_vector<_Frame> _stack;
  _stack.emplace_back(_Enter{&t});
  /// Loopified flatten_tree_fns: _Enter -> _Cont_Node -> _Cont_Node_1.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const MemSafetyProbe13::tree &t = *_f.t;
      if (std::holds_alternative<typename MemSafetyProbe13::tree::Leaf>(
              t.v())) {
        _result = mylist<crane::fn<uint64_t(uint64_t)>>::mynil();
      } else {
        const auto &[a0, a1, a2] =
            std::get<typename MemSafetyProbe13::tree::Node>(t.v());
        const MemSafetyProbe13::tree &a0_value = *a0;
        const MemSafetyProbe13::tree &a2_value = *a2;
        _stack.emplace_back(_Cont_Node{a1, a2});
        _stack.emplace_back(_Enter{crane_raw(a0)});
      }
    } else if (std::holds_alternative<_Cont_Node>(_frame)) {
      auto _f = std::move(std::get<_Cont_Node>(_frame));
      uint64_t a1 = _f.a1;
      std::shared_ptr<MemSafetyProbe13::tree> a2 = std::move(_f.a2);
      const MemSafetyProbe13::tree &a2_value = *a2;
      _stack.emplace_back(_Cont_Node_1{std::move(_result), a1});
      _stack.emplace_back(_Enter{crane_raw(a2)});
    } else {
      auto _f = std::move(std::get<_Cont_Node_1>(_frame));
      uint64_t a1 = _f.a1;
      _result =
          std::move(_f._tmp2).app(mylist<crane::fn<uint64_t(uint64_t)>>::mycons(
              [=](uint64_t n) { return (a1 + n); }, std::move(_result)));
    }
  }
  return _result;
}
