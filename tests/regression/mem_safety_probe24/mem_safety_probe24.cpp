#include "mem_safety_probe24.h"

uint64_t MemSafetyProbe24::sum_list(
    const MemSafetyProbe24::mylist<uint64_t>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const MemSafetyProbe24::mylist<uint64_t> *l;
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
      const MemSafetyProbe24::mylist<uint64_t> &l = *_f.l;
      if (std::holds_alternative<
              typename MemSafetyProbe24::mylist<uint64_t>::Mynil>(l.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] =
            std::get<typename MemSafetyProbe24::mylist<uint64_t>::Mycons>(
                l.v());
        _stack.emplace_back(_Cont_Mycons{a0});
        _stack.emplace_back(_Enter{crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<_Cont_Mycons>(_frame));
      uint64_t a0 = _f.a0;
      uint64_t r_ = std::move(_result);
      _result = (a0 + r_);
    }
  }
  return _result;
}

MemSafetyProbe24::mylist<uint64_t> MemSafetyProbe24::tree_to_list(
    const MemSafetyProbe24::tree
        &t) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const MemSafetyProbe24::tree *t;
  };

  /// _Cont_Node: saves [a1, a2], resumes after recursive call, then processes
  /// rest.
  struct _Cont_Node {
    uint64_t a1;
    const MemSafetyProbe24::tree *a2;
  };

  /// _Cont_Node_1: saves [a1, r_], resumes after recursive call, then processes
  /// rest.
  struct _Cont_Node_1 {
    uint64_t a1;
    MemSafetyProbe24::mylist<uint64_t> r_;
  };

  using _Frame = std::variant<_Enter, _Cont_Node, _Cont_Node_1>;
  MemSafetyProbe24::mylist<uint64_t> _result{};
  crane::small_vector<_Frame> _stack;
  _stack.emplace_back(_Enter{&t});
  /// Loopified tree_to_list: _Enter -> _Cont_Node -> _Cont_Node_1.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const MemSafetyProbe24::tree &t = *_f.t;
      if (std::holds_alternative<typename MemSafetyProbe24::tree::Leaf>(
              t.v())) {
        _result = mylist<uint64_t>::mynil();
      } else {
        const auto &[a0, a1, a2] =
            std::get<typename MemSafetyProbe24::tree::Node>(t.v());
        _stack.emplace_back(_Cont_Node{a1, crane_raw(a2)});
        _stack.emplace_back(_Enter{crane_raw(a0)});
      }
    } else if (std::holds_alternative<_Cont_Node>(_frame)) {
      auto _f = std::move(std::get<_Cont_Node>(_frame));
      uint64_t a1 = _f.a1;
      const MemSafetyProbe24::tree &a2 = *_f.a2;
      MemSafetyProbe24::mylist<uint64_t> r_ = std::move(_result);
      _stack.emplace_back(_Cont_Node_1{a1, std::move(r_)});
      _stack.emplace_back(_Enter{&a2});
    } else {
      auto _f = std::move(std::get<_Cont_Node_1>(_frame));
      uint64_t a1 = _f.a1;
      MemSafetyProbe24::mylist<uint64_t> r_ = std::move(_f.r_);
      MemSafetyProbe24::mylist<uint64_t> r_0 = std::move(_result);
      _result = std::move(r_).app(mylist<uint64_t>::mycons(a1, std::move(r_0)));
    }
  }
  return _result;
}

/// TEST 7: Build a tree from a list, using accumulated state.
/// Tests interaction between list recursion and tree construction.
MemSafetyProbe24::tree
MemSafetyProbe24::list_to_tree(const MemSafetyProbe24::mylist<uint64_t> &l,
                               MemSafetyProbe24::tree acc) {
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
MemSafetyProbe24::zip_trees(
    const MemSafetyProbe24::tree &t1,
    const MemSafetyProbe24::tree
        &t2) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const MemSafetyProbe24::tree *t2;
    const MemSafetyProbe24::tree *t1;
  };

  /// _Cont_Node: saves [a1, a10, a2, a20], resumes after recursive call, then
  /// processes rest.
  struct _Cont_Node {
    uint64_t a1;
    uint64_t a10;
    const MemSafetyProbe24::tree *a2;
    const MemSafetyProbe24::tree *a20;
  };

  /// _Cont_Node_1: saves [a1, a10, r_], resumes after recursive call, then
  /// processes rest.
  struct _Cont_Node_1 {
    uint64_t a1;
    uint64_t a10;
    MemSafetyProbe24::mylist<std::pair<uint64_t, uint64_t>> r_;
  };

  using _Frame = std::variant<_Enter, _Cont_Node, _Cont_Node_1>;
  MemSafetyProbe24::mylist<std::pair<uint64_t, uint64_t>> _result{};
  crane::small_vector<_Frame> _stack;
  _stack.emplace_back(_Enter{&t2, &t1});
  /// Loopified zip_trees: _Enter -> _Cont_Node -> _Cont_Node_1.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const MemSafetyProbe24::tree &t2 = *_f.t2;
      const MemSafetyProbe24::tree &t1 = *_f.t1;
      if (std::holds_alternative<typename MemSafetyProbe24::tree::Leaf>(
              t1.v())) {
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
              _Cont_Node{a1, a10, crane_raw(a2), crane_raw(a20)});
          _stack.emplace_back(_Enter{crane_raw(a00), crane_raw(a0)});
        }
      }
    } else if (std::holds_alternative<_Cont_Node>(_frame)) {
      auto _f = std::move(std::get<_Cont_Node>(_frame));
      uint64_t a1 = _f.a1;
      uint64_t a10 = _f.a10;
      const MemSafetyProbe24::tree &a2 = *_f.a2;
      const MemSafetyProbe24::tree &a20 = *_f.a20;
      MemSafetyProbe24::mylist<std::pair<uint64_t, uint64_t>> r_ =
          std::move(_result);
      _stack.emplace_back(_Cont_Node_1{a1, a10, std::move(r_)});
      _stack.emplace_back(_Enter{&a20, &a2});
    } else {
      auto _f = std::move(std::get<_Cont_Node_1>(_frame));
      uint64_t a1 = _f.a1;
      uint64_t a10 = _f.a10;
      MemSafetyProbe24::mylist<std::pair<uint64_t, uint64_t>> r_ =
          std::move(_f.r_);
      MemSafetyProbe24::mylist<std::pair<uint64_t, uint64_t>> r_0 =
          std::move(_result);
      _result = std::move(r_).app(mylist<std::pair<uint64_t, uint64_t>>::mycons(
          std::make_pair(a1, a10), std::move(r_0)));
    }
  }
  return _result;
}
