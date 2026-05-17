#include "mem_safety_probe17.h"

uint64_t MemSafetyProbe17::sum_list(
    const MemSafetyProbe17::mylist<uint64_t>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const MemSafetyProbe17::mylist<uint64_t> *l;
  };

  /// _Resume_Mycons: saves [a0], resumes after recursive call with _result.
  struct _Resume_Mycons {
    uint64_t a0;
  };

  using _Frame = std::variant<_Enter, _Resume_Mycons>;
  uint64_t _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l});
  /// Loopified sum_list: _Enter -> _Resume_Mycons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const MemSafetyProbe17::mylist<uint64_t> &l = *_f.l;
      if (std::holds_alternative<
              typename MemSafetyProbe17::mylist<uint64_t>::Mynil>(l.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] =
            std::get<typename MemSafetyProbe17::mylist<uint64_t>::Mycons>(
                l.v());
        _stack.emplace_back(_Resume_Mycons{a0});
        _stack.emplace_back(_Enter{a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Resume_Mycons>(_frame));
      _result = (_f.a0 + _result);
    }
  }
  return _result;
}

MemSafetyProbe17::mylist<uint64_t> MemSafetyProbe17::qtree_flatten(
    const MemSafetyProbe17::qtree
        &t) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const MemSafetyProbe17::qtree *t;
  };

  /// _After_QNode: saves [a3, a1, a0, a2], dispatches next recursive call.
  struct _After_QNode {
    const MemSafetyProbe17::qtree *a3;
    const MemSafetyProbe17::qtree *a1;
    const MemSafetyProbe17::qtree *a0;
    uint64_t a2;
  };

  /// _After_QNode_1: saves [_result, a1, a0, a2], dispatches next recursive
  /// call.
  struct _After_QNode_1 {
    MemSafetyProbe17::mylist<uint64_t> _result;
    const MemSafetyProbe17::qtree *a1;
    const MemSafetyProbe17::qtree *a0;
    uint64_t a2;
  };

  /// _After_QNode_2: saves [_result_0, _result_1, a0, a2], dispatches next
  /// recursive call.
  struct _After_QNode_2 {
    MemSafetyProbe17::mylist<uint64_t> _result_0;
    MemSafetyProbe17::mylist<uint64_t> _result_1;
    const MemSafetyProbe17::qtree *a0;
    uint64_t a2;
  };

  /// _Combine_QNode: receives partial results, combines with _result from final
  /// call.
  struct _Combine_QNode {
    MemSafetyProbe17::mylist<uint64_t> _result_0;
    MemSafetyProbe17::mylist<uint64_t> _result_1;
    MemSafetyProbe17::mylist<uint64_t> _result_2;
    uint64_t a2;
  };

  using _Frame = std::variant<_Enter, _After_QNode, _After_QNode_1,
                              _After_QNode_2, _Combine_QNode>;
  MemSafetyProbe17::mylist<uint64_t> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&t});
  /// Loopified qtree_flatten: _Enter -> _After_QNode -> _After_QNode_1 ->
  /// _After_QNode_2 -> _Combine_QNode.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const MemSafetyProbe17::qtree &t = *_f.t;
      if (std::holds_alternative<typename MemSafetyProbe17::qtree::QLeaf>(
              t.v())) {
        _result = mylist<uint64_t>::mynil();
      } else {
        const auto &[a0, a1, a2, a3, a4] =
            std::get<typename MemSafetyProbe17::qtree::QNode>(t.v());
        _stack.emplace_back(_After_QNode{a3.get(), a1.get(), a0.get(), a2});
        _stack.emplace_back(_Enter{a4.get()});
      }
    } else if (std::holds_alternative<_After_QNode>(_frame)) {
      auto _f = std::move(std::get<_After_QNode>(_frame));
      _stack.emplace_back(
          _After_QNode_1{std::move(_result), _f.a1, _f.a0, _f.a2});
      _stack.emplace_back(_Enter{_f.a3});
    } else if (std::holds_alternative<_After_QNode_1>(_frame)) {
      auto _f = std::move(std::get<_After_QNode_1>(_frame));
      _stack.emplace_back(_After_QNode_2{std::move(_f._result),
                                         std::move(_result), _f.a0, _f.a2});
      _stack.emplace_back(_Enter{_f.a1});
    } else if (std::holds_alternative<_After_QNode_2>(_frame)) {
      auto _f = std::move(std::get<_After_QNode_2>(_frame));
      _stack.emplace_back(_Combine_QNode{std::move(_f._result_0),
                                         std::move(_f._result_1),
                                         std::move(_result), _f.a2});
      _stack.emplace_back(_Enter{_f.a0});
    } else {
      auto _f = std::move(std::get<_Combine_QNode>(_frame));
      _result = _result.myapp(_f._result_2.myapp(
          mylist<uint64_t>::mycons(_f.a2, _f._result_1.myapp(_f._result_0))));
    }
  }
  return _result;
}

/// TEST 7: Build a 4-ary tree programmatically and check.
MemSafetyProbe17::qtree MemSafetyProbe17::make_qtree(
    uint64_t
        n) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    uint64_t n;
  };

  /// _After_n_: saves [n_, _s1, n, _s3], dispatches next recursive call.
  struct _After_n_ {
    uint64_t n_;
    decltype(qtree::qleaf()) _s1;
    uint64_t n;
    decltype(qtree::qleaf()) _s3;
  };

  /// _Combine_n_: receives partial results, combines with _result from final
  /// call.
  struct _Combine_n_ {
    MemSafetyProbe17::qtree _result;
    decltype(qtree::qleaf()) _s1;
    uint64_t n;
    decltype(qtree::qleaf()) _s3;
  };

  using _Frame = std::variant<_Enter, _After_n_, _Combine_n_>;
  MemSafetyProbe17::qtree _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{n});
  /// Loopified make_qtree: _Enter -> _After_n_ -> _Combine_n_.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      uint64_t n = _f.n;
      if (n <= 0) {
        _result = qtree::qleaf();
      } else {
        uint64_t n_ = n - 1;
        _stack.emplace_back(_After_n_{n_, qtree::qleaf(), n, qtree::qleaf()});
        _stack.emplace_back(_Enter{n_});
      }
    } else if (std::holds_alternative<_After_n_>(_frame)) {
      auto _f = std::move(std::get<_After_n_>(_frame));
      _stack.emplace_back(
          _Combine_n_{std::move(_result), _f._s1, _f.n, _f._s3});
      _stack.emplace_back(_Enter{_f.n_});
    } else {
      auto _f = std::move(std::get<_Combine_n_>(_frame));
      _result = qtree::qnode(_result, _f._s3, _f.n, _f._result, _f._s1);
    }
  }
  return _result;
}
