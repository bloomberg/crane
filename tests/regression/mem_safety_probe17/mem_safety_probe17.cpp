#include <mem_safety_probe17.h>

unsigned int MemSafetyProbe17::sum_list(
    const MemSafetyProbe17::mylist<unsigned int>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const MemSafetyProbe17::mylist<unsigned int> *l;
  };

  /// _Resume_Mycons: saves [d_a0], resumes after recursive call with _result.
  struct _Resume_Mycons {
    unsigned int d_a0;
  };

  using _Frame = std::variant<_Enter, _Resume_Mycons>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l});
  /// Loopified sum_list: _Enter -> _Resume_Mycons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const MemSafetyProbe17::mylist<unsigned int> &l = *(_f.l);
      if (std::holds_alternative<
              typename MemSafetyProbe17::mylist<unsigned int>::Mynil>(l.v())) {
        _result = 0u;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename MemSafetyProbe17::mylist<unsigned int>::Mycons>(
                l.v());
        _stack.emplace_back(_Resume_Mycons{d_a0});
        _stack.emplace_back(_Enter{d_a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Resume_Mycons>(_frame));
      _result = (_f.d_a0 + _result);
    }
  }
  return _result;
}

MemSafetyProbe17::mylist<unsigned int> MemSafetyProbe17::qtree_flatten(
    const MemSafetyProbe17::qtree
        &t) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const MemSafetyProbe17::qtree *t;
  };

  /// _After_QNode: saves [d_a3, d_a1, d_a0, d_a2], dispatches next recursive
  /// call.
  struct _After_QNode {
    const MemSafetyProbe17::qtree *d_a3;
    const MemSafetyProbe17::qtree *d_a1;
    const MemSafetyProbe17::qtree *d_a0;
    unsigned int d_a2;
  };

  /// _After_QNode_1: saves [_result, d_a1, d_a0, d_a2], dispatches next
  /// recursive call.
  struct _After_QNode_1 {
    MemSafetyProbe17::mylist<unsigned int> _result;
    const MemSafetyProbe17::qtree *d_a1;
    const MemSafetyProbe17::qtree *d_a0;
    unsigned int d_a2;
  };

  /// _After_QNode_2: saves [_result_0, _result_1, d_a0, d_a2], dispatches next
  /// recursive call.
  struct _After_QNode_2 {
    MemSafetyProbe17::mylist<unsigned int> _result_0;
    MemSafetyProbe17::mylist<unsigned int> _result_1;
    const MemSafetyProbe17::qtree *d_a0;
    unsigned int d_a2;
  };

  /// _Combine_QNode: receives partial results, combines with _result from final
  /// call.
  struct _Combine_QNode {
    MemSafetyProbe17::mylist<unsigned int> _result_0;
    MemSafetyProbe17::mylist<unsigned int> _result_1;
    MemSafetyProbe17::mylist<unsigned int> _result_2;
    unsigned int d_a2;
  };

  using _Frame = std::variant<_Enter, _After_QNode, _After_QNode_1,
                              _After_QNode_2, _Combine_QNode>;
  MemSafetyProbe17::mylist<unsigned int> _result{};
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
      const MemSafetyProbe17::qtree &t = *(_f.t);
      if (std::holds_alternative<typename MemSafetyProbe17::qtree::QLeaf>(
              t.v())) {
        _result = mylist<unsigned int>::mynil();
      } else {
        const auto &[d_a0, d_a1, d_a2, d_a3, d_a4] =
            std::get<typename MemSafetyProbe17::qtree::QNode>(t.v());
        _stack.emplace_back(
            _After_QNode{d_a3.get(), d_a1.get(), d_a0.get(), d_a2});
        _stack.emplace_back(_Enter{d_a4.get()});
      }
    } else if (std::holds_alternative<_After_QNode>(_frame)) {
      auto _f = std::move(std::get<_After_QNode>(_frame));
      _stack.emplace_back(
          _After_QNode_1{std::move(_result), _f.d_a1, _f.d_a0, _f.d_a2});
      _stack.emplace_back(_Enter{_f.d_a3});
    } else if (std::holds_alternative<_After_QNode_1>(_frame)) {
      auto _f = std::move(std::get<_After_QNode_1>(_frame));
      _stack.emplace_back(_After_QNode_2{std::move(_f._result),
                                         std::move(_result), _f.d_a0, _f.d_a2});
      _stack.emplace_back(_Enter{_f.d_a1});
    } else if (std::holds_alternative<_After_QNode_2>(_frame)) {
      auto _f = std::move(std::get<_After_QNode_2>(_frame));
      _stack.emplace_back(_Combine_QNode{std::move(_f._result_0),
                                         std::move(_f._result_1),
                                         std::move(_result), _f.d_a2});
      _stack.emplace_back(_Enter{_f.d_a0});
    } else {
      auto _f = std::move(std::get<_Combine_QNode>(_frame));
      _result = _result.myapp(_f._result_2.myapp(mylist<unsigned int>::mycons(
          _f.d_a2, _f._result_1.myapp(_f._result_0))));
    }
  }
  return _result;
}

/// TEST 7: Build a 4-ary tree programmatically and check.
MemSafetyProbe17::qtree MemSafetyProbe17::make_qtree(
    const unsigned int
        n) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    unsigned int n;
  };

  /// _After_n_: saves [n_, _s1, n, _s3], dispatches next recursive call.
  struct _After_n_ {
    unsigned int n_;
    decltype(qtree::qleaf()) _s1;
    unsigned int n;
    decltype(qtree::qleaf()) _s3;
  };

  /// _Combine_n_: receives partial results, combines with _result from final
  /// call.
  struct _Combine_n_ {
    MemSafetyProbe17::qtree _result;
    decltype(qtree::qleaf()) _s1;
    unsigned int n;
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
      const unsigned int n = _f.n;
      if (n <= 0) {
        _result = qtree::qleaf();
      } else {
        unsigned int n_ = n - 1;
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
