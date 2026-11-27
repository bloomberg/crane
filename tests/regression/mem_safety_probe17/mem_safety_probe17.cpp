#include "mem_safety_probe17.h"

uint64_t
MemSafetyProbe17::sum_list(const MemSafetyProbe17::mylist<uint64_t> &l) {
  // Explicit stack replaces the non-tail recursion of sum_list: _call frames
  // are pending calls, _after frames resume a caller.
  struct _call {
    const MemSafetyProbe17::mylist<uint64_t> *l;
  };

  struct _after_sum_list_in_Mycons {
    uint64_t a0;
  };

  using _frame = std::variant<_call, _after_sum_list_in_Mycons>;
  uint64_t _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&l});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const MemSafetyProbe17::mylist<uint64_t> &l = *_f.l;
      if (std::holds_alternative<
              typename MemSafetyProbe17::mylist<uint64_t>::Mynil>(l.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] = std::get<
            typename MemSafetyProbe17::mylist<uint64_t>::Mycons>(l.v());
        _stack.emplace_back(_after_sum_list_in_Mycons{a0});
        _stack.emplace_back(_call{crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<_after_sum_list_in_Mycons>(_popped));
      _stack.pop_back();
      uint64_t a0 = _f.a0;
      _result = a0 + _result;
    }
  }
  return _result;
}

MemSafetyProbe17::mylist<uint64_t>
MemSafetyProbe17::qtree_flatten(const MemSafetyProbe17::qtree &t) {
  // Explicit stack replaces the non-tail recursion of qtree_flatten: _call
  // frames are pending calls, _after frames resume a caller.
  struct _call {
    const MemSafetyProbe17::qtree *t;
  };

  struct _after_qtree_flatten_in_QNode {
    const MemSafetyProbe17::qtree *a1;
    uint64_t a2;
    const MemSafetyProbe17::qtree *a3;
    const MemSafetyProbe17::qtree *a4;
  };

  struct _after_qtree_flatten_in_QNode_2 {
    uint64_t a2;
    const MemSafetyProbe17::qtree *a3;
    const MemSafetyProbe17::qtree *a4;
    MemSafetyProbe17::mylist<uint64_t> _tmp4;
  };

  struct _after_qtree_flatten_in_QNode_3 {
    uint64_t a2;
    const MemSafetyProbe17::qtree *a4;
    MemSafetyProbe17::mylist<uint64_t> _tmp4;
    MemSafetyProbe17::mylist<uint64_t> _tmp3;
  };

  struct _after_qtree_flatten_in_QNode_4 {
    uint64_t a2;
    MemSafetyProbe17::mylist<uint64_t> _tmp4;
    MemSafetyProbe17::mylist<uint64_t> _tmp3;
    MemSafetyProbe17::mylist<uint64_t> _tmp2;
  };

  using _frame = std::variant<
      _call, _after_qtree_flatten_in_QNode, _after_qtree_flatten_in_QNode_2,
      _after_qtree_flatten_in_QNode_3, _after_qtree_flatten_in_QNode_4>;
  MemSafetyProbe17::mylist<uint64_t> _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&t});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const MemSafetyProbe17::qtree &t = *_f.t;
      if (std::holds_alternative<typename MemSafetyProbe17::qtree::QLeaf>(t.v())) {
        _result = mylist<uint64_t>::mynil();
      } else {
        const auto &[a0, a1, a2, a3, a4] =
            std::get<typename MemSafetyProbe17::qtree::QNode>(t.v());
        _stack.emplace_back(_after_qtree_flatten_in_QNode{
            crane_raw(a1), a2, crane_raw(a3), crane_raw(a4)});
        _stack.emplace_back(_call{crane_raw(a0)});
      }
    } else if (std::holds_alternative<_after_qtree_flatten_in_QNode>(_popped)) {
      auto _f = std::move(std::get<_after_qtree_flatten_in_QNode>(_popped));
      _stack.pop_back();
      const MemSafetyProbe17::qtree &a1 = *_f.a1;
      uint64_t a2 = _f.a2;
      const MemSafetyProbe17::qtree &a3 = *_f.a3;
      const MemSafetyProbe17::qtree &a4 = *_f.a4;
      _stack.emplace_back(
          _after_qtree_flatten_in_QNode_2{a2, &a3, &a4, std::move(_result)});
      _stack.emplace_back(_call{&a1});
    } else if (std::holds_alternative<_after_qtree_flatten_in_QNode_2>(_popped)) {
      auto _f = std::move(std::get<_after_qtree_flatten_in_QNode_2>(_popped));
      _stack.pop_back();
      uint64_t a2 = _f.a2;
      const MemSafetyProbe17::qtree &a3 = *_f.a3;
      const MemSafetyProbe17::qtree &a4 = *_f.a4;
      _stack.emplace_back(_after_qtree_flatten_in_QNode_3{
          a2, &a4, std::move(_f._tmp4), std::move(_result)});
      _stack.emplace_back(_call{&a3});
    } else if (std::holds_alternative<_after_qtree_flatten_in_QNode_3>(_popped)) {
      auto _f = std::move(std::get<_after_qtree_flatten_in_QNode_3>(_popped));
      _stack.pop_back();
      uint64_t a2 = _f.a2;
      const MemSafetyProbe17::qtree &a4 = *_f.a4;
      _stack.emplace_back(_after_qtree_flatten_in_QNode_4{
          a2, std::move(_f._tmp4), std::move(_f._tmp3), std::move(_result)});
      _stack.emplace_back(_call{&a4});
    } else {
      auto _f = std::move(std::get<_after_qtree_flatten_in_QNode_4>(_popped));
      _stack.pop_back();
      uint64_t a2 = _f.a2;
      _result = _f._tmp4.myapp(_f._tmp3.myapp(
          mylist<uint64_t>::mycons(a2, _f._tmp2.myapp(std::move(_result)))));
    }
  }
  return _result;
}

/// TEST 7: Build a 4-ary tree programmatically and check.
MemSafetyProbe17::qtree MemSafetyProbe17::make_qtree(uint64_t n) {
  // Explicit stack replaces the non-tail recursion of make_qtree: _call frames
  // are pending calls, _after frames resume a caller.
  struct _call {
    uint64_t n;
  };

  struct _after_make_qtree_in_S {
    uint64_t n;
    uint64_t n_;
  };

  struct _after_make_qtree_in_S_2 {
    uint64_t n;
    MemSafetyProbe17::qtree _tmp2;
  };

  using _frame =
      std::variant<_call, _after_make_qtree_in_S, _after_make_qtree_in_S_2>;
  MemSafetyProbe17::qtree _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{n});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      uint64_t n = _f.n;
      if (n <= 0) {
        _result = qtree::qleaf();
      } else {
        uint64_t n_ = n - 1;
        _stack.emplace_back(_after_make_qtree_in_S{n, n_});
        _stack.emplace_back(_call{n_});
      }
    } else if (std::holds_alternative<_after_make_qtree_in_S>(_popped)) {
      auto _f = std::move(std::get<_after_make_qtree_in_S>(_popped));
      _stack.pop_back();
      uint64_t n = _f.n;
      uint64_t n_ = _f.n_;
      _stack.emplace_back(_after_make_qtree_in_S_2{n, std::move(_result)});
      _stack.emplace_back(_call{n_});
    } else {
      auto _f = std::move(std::get<_after_make_qtree_in_S_2>(_popped));
      _stack.pop_back();
      uint64_t n = _f.n;
      _result = qtree::qnode(std::move(_f._tmp2), qtree::qleaf(), n,
                             std::move(_result), qtree::qleaf());
    }
  }
  return _result;
}
