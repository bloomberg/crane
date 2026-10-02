#include "mem_safety_probe17.h"

uint64_t MemSafetyProbe17::sum_list(
    const MemSafetyProbe17::mylist<uint64_t>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const MemSafetyProbe17::mylist<uint64_t> *l;
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
      const MemSafetyProbe17::mylist<uint64_t> &l = *_f.l;
      if (std::holds_alternative<
              typename MemSafetyProbe17::mylist<uint64_t>::Mynil>(l.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] =
            std::get<typename MemSafetyProbe17::mylist<uint64_t>::Mycons>(
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

MemSafetyProbe17::mylist<uint64_t> MemSafetyProbe17::qtree_flatten(
    const MemSafetyProbe17::qtree
        &t) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const MemSafetyProbe17::qtree *t;
  };

  /// _Cont_QNode: saves [a1, a2, a3, a4], resumes after recursive call, then
  /// processes rest.
  struct _Cont_QNode {
    const MemSafetyProbe17::qtree *a1;
    uint64_t a2;
    const MemSafetyProbe17::qtree *a3;
    const MemSafetyProbe17::qtree *a4;
  };

  /// _Cont_QNode_1: saves [a2, a3, a4, r_], resumes after recursive call, then
  /// processes rest.
  struct _Cont_QNode_1 {
    uint64_t a2;
    const MemSafetyProbe17::qtree *a3;
    const MemSafetyProbe17::qtree *a4;
    MemSafetyProbe17::mylist<uint64_t> r_;
  };

  /// _Cont_QNode_2: saves [a2, a4, r_, r_0], resumes after recursive call, then
  /// processes rest.
  struct _Cont_QNode_2 {
    uint64_t a2;
    const MemSafetyProbe17::qtree *a4;
    MemSafetyProbe17::mylist<uint64_t> r_;
    MemSafetyProbe17::mylist<uint64_t> r_0;
  };

  /// _Cont_QNode_3: saves [a2, r_, r_0, r_1], resumes after recursive call,
  /// then processes rest.
  struct _Cont_QNode_3 {
    uint64_t a2;
    MemSafetyProbe17::mylist<uint64_t> r_;
    MemSafetyProbe17::mylist<uint64_t> r_0;
    MemSafetyProbe17::mylist<uint64_t> r_1;
  };

  using _Frame = std::variant<_Enter, _Cont_QNode, _Cont_QNode_1, _Cont_QNode_2,
                              _Cont_QNode_3>;
  MemSafetyProbe17::mylist<uint64_t> _result{};
  crane::small_vector<_Frame> _stack;
  _stack.emplace_back(_Enter{&t});
  /// Loopified qtree_flatten: _Enter -> _Cont_QNode -> _Cont_QNode_1 ->
  /// _Cont_QNode_2 -> _Cont_QNode_3.
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
        _stack.emplace_back(
            _Cont_QNode{crane_raw(a1), a2, crane_raw(a3), crane_raw(a4)});
        _stack.emplace_back(_Enter{crane_raw(a0)});
      }
    } else if (std::holds_alternative<_Cont_QNode>(_frame)) {
      auto _f = std::move(std::get<_Cont_QNode>(_frame));
      const MemSafetyProbe17::qtree &a1 = *_f.a1;
      uint64_t a2 = _f.a2;
      const MemSafetyProbe17::qtree &a3 = *_f.a3;
      const MemSafetyProbe17::qtree &a4 = *_f.a4;
      MemSafetyProbe17::mylist<uint64_t> r_ = std::move(_result);
      _stack.emplace_back(_Cont_QNode_1{a2, &a3, &a4, std::move(r_)});
      _stack.emplace_back(_Enter{&a1});
    } else if (std::holds_alternative<_Cont_QNode_1>(_frame)) {
      auto _f = std::move(std::get<_Cont_QNode_1>(_frame));
      uint64_t a2 = _f.a2;
      const MemSafetyProbe17::qtree &a3 = *_f.a3;
      const MemSafetyProbe17::qtree &a4 = *_f.a4;
      MemSafetyProbe17::mylist<uint64_t> r_ = std::move(_f.r_);
      MemSafetyProbe17::mylist<uint64_t> r_0 = std::move(_result);
      _stack.emplace_back(
          _Cont_QNode_2{a2, &a4, std::move(r_), std::move(r_0)});
      _stack.emplace_back(_Enter{&a3});
    } else if (std::holds_alternative<_Cont_QNode_2>(_frame)) {
      auto _f = std::move(std::get<_Cont_QNode_2>(_frame));
      uint64_t a2 = _f.a2;
      const MemSafetyProbe17::qtree &a4 = *_f.a4;
      MemSafetyProbe17::mylist<uint64_t> r_ = std::move(_f.r_);
      MemSafetyProbe17::mylist<uint64_t> r_0 = std::move(_f.r_0);
      MemSafetyProbe17::mylist<uint64_t> r_1 = std::move(_result);
      _stack.emplace_back(
          _Cont_QNode_3{a2, std::move(r_), std::move(r_0), std::move(r_1)});
      _stack.emplace_back(_Enter{&a4});
    } else {
      auto _f = std::move(std::get<_Cont_QNode_3>(_frame));
      uint64_t a2 = _f.a2;
      MemSafetyProbe17::mylist<uint64_t> r_ = std::move(_f.r_);
      MemSafetyProbe17::mylist<uint64_t> r_0 = std::move(_f.r_0);
      MemSafetyProbe17::mylist<uint64_t> r_1 = std::move(_f.r_1);
      MemSafetyProbe17::mylist<uint64_t> r_2 = std::move(_result);
      _result = std::move(r_).myapp(std::move(r_0).myapp(
          mylist<uint64_t>::mycons(a2, std::move(r_1).myapp(std::move(r_2)))));
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
    MemSafetyProbe17::qtree _s1;
    uint64_t n;
    MemSafetyProbe17::qtree _s3;
  };

  /// _Combine_n_: receives partial results, combines with _result from final
  /// call.
  struct _Combine_n_ {
    MemSafetyProbe17::qtree _result;
    MemSafetyProbe17::qtree _s1;
    uint64_t n;
    MemSafetyProbe17::qtree _s3;
  };

  using _Frame = std::variant<_Enter, _After_n_, _Combine_n_>;
  MemSafetyProbe17::qtree _result{};
  crane::small_vector<_Frame> _stack;
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
      _stack.emplace_back(_Combine_n_{std::move(_result), std::move(_f._s1),
                                      _f.n, std::move(_f._s3)});
      _stack.emplace_back(_Enter{_f.n_});
    } else {
      auto _f = std::move(std::get<_Combine_n_>(_frame));
      _result = qtree::qnode(std::move(_result), std::move(_f._s3), _f.n,
                             std::move(_f._result), std::move(_f._s1));
    }
  }
  return _result;
}
