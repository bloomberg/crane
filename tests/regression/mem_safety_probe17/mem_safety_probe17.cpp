#include "mem_safety_probe17.h"

uint64_t
MemSafetyProbe17::sum_list(const MemSafetyProbe17::mylist<uint64_t>
                               &l) { /// CraneEnter: captures varying parameters
                                     /// for each recursive call.

  struct CraneEnter {
    const MemSafetyProbe17::mylist<uint64_t> *l;
  };

  /// CraneCont_Mycons: saves [a0], resumes after recursive call, then processes
  /// rest.
  struct CraneCont_Mycons {
    uint64_t a0;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont_Mycons>;
  uint64_t _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{&l});
  /// Loopified sum_list: CraneEnter -> CraneCont_Mycons.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      const MemSafetyProbe17::mylist<uint64_t> &l = *_f.l;
      if (std::holds_alternative<
              typename MemSafetyProbe17::mylist<uint64_t>::Mynil>(l.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] =
            std::get<typename MemSafetyProbe17::mylist<uint64_t>::Mycons>(
                l.v());
        _stack.emplace_back(CraneCont_Mycons{a0});
        _stack.emplace_back(CraneEnter{crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<CraneCont_Mycons>(_frame));
      uint64_t a0 = _f.a0;
      _result = (a0 + std::move(_result));
    }
  }
  return _result;
}

MemSafetyProbe17::mylist<uint64_t> MemSafetyProbe17::qtree_flatten(
    const MemSafetyProbe17::qtree &t) { /// CraneEnter: captures varying
                                        /// parameters for each recursive call.

  struct CraneEnter {
    const MemSafetyProbe17::qtree *t;
  };

  /// CraneCont_QNode: saves [a1, a2, a3, a4], resumes after recursive call,
  /// then processes rest.
  struct CraneCont_QNode {
    const MemSafetyProbe17::qtree *a1;
    uint64_t a2;
    const MemSafetyProbe17::qtree *a3;
    const MemSafetyProbe17::qtree *a4;
  };

  /// CraneCont_QNode_1: saves [_tmp4, a2, a3, a4], resumes after recursive
  /// call, then processes rest.
  struct CraneCont_QNode_1 {
    MemSafetyProbe17::mylist<uint64_t> _tmp4;
    uint64_t a2;
    const MemSafetyProbe17::qtree *a3;
    const MemSafetyProbe17::qtree *a4;
  };

  /// CraneCont_QNode_2: saves [_tmp3, _tmp4, a2, a4], resumes after recursive
  /// call, then processes rest.
  struct CraneCont_QNode_2 {
    MemSafetyProbe17::mylist<uint64_t> _tmp3;
    MemSafetyProbe17::mylist<uint64_t> _tmp4;
    uint64_t a2;
    const MemSafetyProbe17::qtree *a4;
  };

  /// CraneCont_QNode_3: saves [_tmp2, _tmp3, _tmp4, a2], resumes after
  /// recursive call, then processes rest.
  struct CraneCont_QNode_3 {
    MemSafetyProbe17::mylist<uint64_t> _tmp2;
    MemSafetyProbe17::mylist<uint64_t> _tmp3;
    MemSafetyProbe17::mylist<uint64_t> _tmp4;
    uint64_t a2;
  };

  using CraneFrame =
      std::variant<CraneEnter, CraneCont_QNode, CraneCont_QNode_1,
                   CraneCont_QNode_2, CraneCont_QNode_3>;
  MemSafetyProbe17::mylist<uint64_t> _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{&t});
  /// Loopified qtree_flatten: CraneEnter -> CraneCont_QNode ->
  /// CraneCont_QNode_1 -> CraneCont_QNode_2 -> CraneCont_QNode_3.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      const MemSafetyProbe17::qtree &t = *_f.t;
      if (std::holds_alternative<typename MemSafetyProbe17::qtree::QLeaf>(
              t.v())) {
        _result = mylist<uint64_t>::mynil();
      } else {
        const auto &[a0, a1, a2, a3, a4] =
            std::get<typename MemSafetyProbe17::qtree::QNode>(t.v());
        _stack.emplace_back(
            CraneCont_QNode{crane_raw(a1), a2, crane_raw(a3), crane_raw(a4)});
        _stack.emplace_back(CraneEnter{crane_raw(a0)});
      }
    } else if (std::holds_alternative<CraneCont_QNode>(_frame)) {
      auto _f = std::move(std::get<CraneCont_QNode>(_frame));
      const MemSafetyProbe17::qtree &a1 = *_f.a1;
      uint64_t a2 = _f.a2;
      const MemSafetyProbe17::qtree &a3 = *_f.a3;
      const MemSafetyProbe17::qtree &a4 = *_f.a4;
      _stack.emplace_back(CraneCont_QNode_1{std::move(_result), a2, &a3, &a4});
      _stack.emplace_back(CraneEnter{&a1});
    } else if (std::holds_alternative<CraneCont_QNode_1>(_frame)) {
      auto _f = std::move(std::get<CraneCont_QNode_1>(_frame));
      uint64_t a2 = _f.a2;
      const MemSafetyProbe17::qtree &a3 = *_f.a3;
      const MemSafetyProbe17::qtree &a4 = *_f.a4;
      _stack.emplace_back(
          CraneCont_QNode_2{std::move(_result), std::move(_f._tmp4), a2, &a4});
      _stack.emplace_back(CraneEnter{&a3});
    } else if (std::holds_alternative<CraneCont_QNode_2>(_frame)) {
      auto _f = std::move(std::get<CraneCont_QNode_2>(_frame));
      uint64_t a2 = _f.a2;
      const MemSafetyProbe17::qtree &a4 = *_f.a4;
      _stack.emplace_back(CraneCont_QNode_3{
          std::move(_result), std::move(_f._tmp3), std::move(_f._tmp4), a2});
      _stack.emplace_back(CraneEnter{&a4});
    } else {
      auto _f = std::move(std::get<CraneCont_QNode_3>(_frame));
      uint64_t a2 = _f.a2;
      _result = std::move(_f._tmp4).myapp(
          std::move(_f._tmp3).myapp(mylist<uint64_t>::mycons(
              a2, std::move(_f._tmp2).myapp(std::move(_result)))));
    }
  }
  return _result;
}

/// TEST 7: Build a 4-ary tree programmatically and check.
MemSafetyProbe17::qtree MemSafetyProbe17::make_qtree(
    uint64_t n) { /// CraneEnter: captures varying parameters for each recursive
                  /// call.

  struct CraneEnter {
    uint64_t n;
  };

  /// CraneCont_n_: saves [n, n_], resumes after recursive call, then processes
  /// rest.
  struct CraneCont_n_ {
    uint64_t n;
    uint64_t n_;
  };

  /// CraneCont_n__1: saves [_tmp2, n], resumes after recursive call, then
  /// processes rest.
  struct CraneCont_n__1 {
    MemSafetyProbe17::qtree _tmp2;
    uint64_t n;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont_n_, CraneCont_n__1>;
  MemSafetyProbe17::qtree _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{n});
  /// Loopified make_qtree: CraneEnter -> CraneCont_n_ -> CraneCont_n__1.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      uint64_t n = _f.n;
      if (n <= 0) {
        _result = qtree::qleaf();
      } else {
        uint64_t n_ = n - 1;
        _stack.emplace_back(CraneCont_n_{n, n_});
        _stack.emplace_back(CraneEnter{n_});
      }
    } else if (std::holds_alternative<CraneCont_n_>(_frame)) {
      auto _f = std::move(std::get<CraneCont_n_>(_frame));
      uint64_t n = _f.n;
      uint64_t n_ = _f.n_;
      _stack.emplace_back(CraneCont_n__1{std::move(_result), n});
      _stack.emplace_back(CraneEnter{n_});
    } else {
      auto _f = std::move(std::get<CraneCont_n__1>(_frame));
      uint64_t n = _f.n;
      _result = qtree::qnode(std::move(_f._tmp2), qtree::qleaf(), n,
                             std::move(_result), qtree::qleaf());
    }
  }
  return _result;
}
