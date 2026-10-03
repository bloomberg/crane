#include "mem_safety_probe15.h"

uint64_t MemSafetyProbe15::sum_list(
    const MemSafetyProbe15::mylist<uint64_t>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const MemSafetyProbe15::mylist<uint64_t> *l;
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
      const MemSafetyProbe15::mylist<uint64_t> &l = *_f.l;
      if (std::holds_alternative<
              typename MemSafetyProbe15::mylist<uint64_t>::Mynil>(l.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] =
            std::get<typename MemSafetyProbe15::mylist<uint64_t>::Mycons>(
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

/// TEST 1: Tree flattening where left subtree is used AFTER
/// right subtree recursive call.
/// In loopified code, the Enter frame for the right subtree
/// may move the left subtree's pointer.
MemSafetyProbe15::mylist<uint64_t> MemSafetyProbe15::flatten(
    const MemSafetyProbe15::tree
        &t) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const MemSafetyProbe15::tree *t;
  };

  /// _Cont_Node: saves [a1, a2], resumes after recursive call, then processes
  /// rest.
  struct _Cont_Node {
    uint64_t a1;
    const MemSafetyProbe15::tree *a2;
  };

  /// _Cont_Node_1: saves [_tmp2, a1], resumes after recursive call, then
  /// processes rest.
  struct _Cont_Node_1 {
    MemSafetyProbe15::mylist<uint64_t> _tmp2;
    uint64_t a1;
  };

  using _Frame = std::variant<_Enter, _Cont_Node, _Cont_Node_1>;
  MemSafetyProbe15::mylist<uint64_t> _result{};
  crane::small_vector<_Frame> _stack;
  _stack.emplace_back(_Enter{&t});
  /// Loopified flatten: _Enter -> _Cont_Node -> _Cont_Node_1.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const MemSafetyProbe15::tree &t = *_f.t;
      if (std::holds_alternative<typename MemSafetyProbe15::tree::Leaf>(
              t.v())) {
        _result = mylist<uint64_t>::mynil();
      } else {
        const auto &[a0, a1, a2] =
            std::get<typename MemSafetyProbe15::tree::Node>(t.v());
        _stack.emplace_back(_Cont_Node{a1, crane_raw(a2)});
        _stack.emplace_back(_Enter{crane_raw(a0)});
      }
    } else if (std::holds_alternative<_Cont_Node>(_frame)) {
      auto _f = std::move(std::get<_Cont_Node>(_frame));
      uint64_t a1 = _f.a1;
      const MemSafetyProbe15::tree &a2 = *_f.a2;
      _stack.emplace_back(_Cont_Node_1{std::move(_result), a1});
      _stack.emplace_back(_Enter{&a2});
    } else {
      auto _f = std::move(std::get<_Cont_Node_1>(_frame));
      uint64_t a1 = _f.a1;
      _result = std::move(_f._tmp2).myapp(
          mylist<uint64_t>::mycons(a1, std::move(_result)));
    }
  }
  return _result;
}

/// TEST 2: Tree to list where each element is the sum of
/// its subtree. Uses both subtrees for computation AND recursion.
MemSafetyProbe15::mylist<uint64_t> MemSafetyProbe15::subtree_sums(
    const MemSafetyProbe15::tree
        &t) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const MemSafetyProbe15::tree *t;
  };

  /// _Cont_Node: saves [a0, a1, a2], resumes after recursive call, then
  /// processes rest.
  struct _Cont_Node {
    std::shared_ptr<MemSafetyProbe15::tree> a0;
    uint64_t a1;
    const MemSafetyProbe15::tree *a2;
  };

  /// _Cont_Node_1: saves [_tmp2, a0, a1, a2], resumes after recursive call,
  /// then processes rest.
  struct _Cont_Node_1 {
    MemSafetyProbe15::mylist<uint64_t> _tmp2;
    std::shared_ptr<MemSafetyProbe15::tree> a0;
    uint64_t a1;
    const MemSafetyProbe15::tree *a2;
  };

  using _Frame = std::variant<_Enter, _Cont_Node, _Cont_Node_1>;
  MemSafetyProbe15::mylist<uint64_t> _result{};
  crane::small_vector<_Frame> _stack;
  _stack.emplace_back(_Enter{&t});
  /// Loopified subtree_sums: _Enter -> _Cont_Node -> _Cont_Node_1.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const MemSafetyProbe15::tree &t = *_f.t;
      if (std::holds_alternative<typename MemSafetyProbe15::tree::Leaf>(
              t.v())) {
        _result = mylist<uint64_t>::mynil();
      } else {
        const auto &[a0, a1, a2] =
            std::get<typename MemSafetyProbe15::tree::Node>(t.v());
        _stack.emplace_back(_Cont_Node{a0, a1, crane_raw(a2)});
        _stack.emplace_back(_Enter{crane_raw(a0)});
      }
    } else if (std::holds_alternative<_Cont_Node>(_frame)) {
      auto _f = std::move(std::get<_Cont_Node>(_frame));
      std::shared_ptr<MemSafetyProbe15::tree> a0 = std::move(_f.a0);
      uint64_t a1 = _f.a1;
      const MemSafetyProbe15::tree &a2 = *_f.a2;
      _stack.emplace_back(
          _Cont_Node_1{std::move(_result), std::move(a0), a1, &a2});
      _stack.emplace_back(_Enter{&a2});
    } else {
      auto _f = std::move(std::get<_Cont_Node_1>(_frame));
      std::shared_ptr<MemSafetyProbe15::tree> a0 = std::move(_f.a0);
      uint64_t a1 = _f.a1;
      const MemSafetyProbe15::tree &a2 = *_f.a2;
      _result = mylist<uint64_t>::mycons(
          ((a0->tree_sum() + a1) + a2.tree_sum()),
          std::move(_f._tmp2).myapp(std::move(_result)));
    }
  }
  return _result;
}

/// TEST 5: Deep left-spine tree.
/// Stresses the frame stack depth.
MemSafetyProbe15::tree MemSafetyProbe15::left_spine(uint64_t n) {
  std::shared_ptr<MemSafetyProbe15::tree> _head{};
  std::shared_ptr<MemSafetyProbe15::tree> *_write = &_head;
  uint64_t _loop_n = std::move(n);
  while (true) {
    if (_loop_n <= 0) {
      *_write = std::make_shared<MemSafetyProbe15::tree>(tree::leaf());
      break;
    } else {
      uint64_t n_ = _loop_n - 1;
      auto _cell = std::make_shared<MemSafetyProbe15::tree>(
          typename MemSafetyProbe15::tree::Node(
              nullptr, _loop_n,
              std::make_shared<MemSafetyProbe15::tree>(tree::leaf())));
      *_write = std::move(_cell);
      _write =
          &std::get<typename MemSafetyProbe15::tree::Node>((*_write)->v_mut())
               .a0;
      _loop_n = n_;
      continue;
    }
  }
  return std::move(*_head);
}

/// TEST 9: Build a large tree and verify all values are preserved.
MemSafetyProbe15::tree MemSafetyProbe15::make_tree(
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

  /// _Resume_n_: saves [n, _tmp1], resumes after recursive call with _result.
  struct _Resume_n_ {
    uint64_t n;
    MemSafetyProbe15::tree _tmp1;
  };

  using _Frame = std::variant<_Enter, _Cont_n_, _Resume_n_>;
  MemSafetyProbe15::tree _result{};
  crane::small_vector<_Frame> _stack;
  _stack.emplace_back(_Enter{n});
  /// Loopified make_tree: _Enter -> _Cont_n_ -> _Resume_n_.
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
      _stack.emplace_back(_Resume_n_{n, std::move(_result)});
      _stack.emplace_back(_Enter{n_});
    } else {
      auto _f = std::move(std::get<_Resume_n_>(_frame));
      _result = tree::node(std::move(_f._tmp1), _f.n, std::move(_result));
    }
  }
  return _result;
}
