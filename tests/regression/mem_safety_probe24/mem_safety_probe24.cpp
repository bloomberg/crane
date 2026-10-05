#include "mem_safety_probe24.h"

uint64_t
MemSafetyProbe24::sum_list(const MemSafetyProbe24::mylist<uint64_t> &l) {
  {
    const MemSafetyProbe24::mylist<uint64_t> &_lc1_l0 = l;
    uint64_t _lc1_acc = UINT64_C(0);
    uint64_t _lc1_loop_acc = _lc1_acc;
    const MemSafetyProbe24::mylist<uint64_t> *_lc1_loop_l0 = &_lc1_l0;
    while (true) {
      if (std::holds_alternative<
              typename MemSafetyProbe24::mylist<uint64_t>::Mynil>(
              _lc1_loop_l0->v())) {
        return _lc1_loop_acc;
      } else {
        const auto &[a0, a1] =
            std::get<typename MemSafetyProbe24::mylist<uint64_t>::Mycons>(
                _lc1_loop_l0->v());
        _lc1_loop_acc = (_lc1_loop_acc + a0);
        _lc1_loop_l0 = crane_raw(a1);
      }
    }
  }
}

MemSafetyProbe24::mylist<uint64_t> MemSafetyProbe24::tree_to_list(
    const MemSafetyProbe24::tree &t) { /// CraneEnter: captures varying
                                       /// parameters for each recursive call.

  struct CraneEnter {
    const MemSafetyProbe24::tree *t;
  };

  /// CraneCont_Node: saves [a1, a2], resumes after recursive call, then
  /// processes rest.
  struct CraneCont_Node {
    uint64_t a1;
    const MemSafetyProbe24::tree *a2;
  };

  /// CraneCont_Node_1: saves [_tmp2, a1], resumes after recursive call, then
  /// processes rest.
  struct CraneCont_Node_1 {
    MemSafetyProbe24::mylist<uint64_t> _tmp2;
    uint64_t a1;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont_Node, CraneCont_Node_1>;
  MemSafetyProbe24::mylist<uint64_t> _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{&t});
  /// Loopified tree_to_list: CraneEnter -> CraneCont_Node -> CraneCont_Node_1.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      const MemSafetyProbe24::tree &t = *_f.t;
      if (std::holds_alternative<typename MemSafetyProbe24::tree::Leaf>(
              t.v())) {
        _result = mylist<uint64_t>::mynil();
      } else {
        const auto &[a0, a1, a2] =
            std::get<typename MemSafetyProbe24::tree::Node>(t.v());
        _stack.emplace_back(CraneCont_Node{a1, crane_raw(a2)});
        _stack.emplace_back(CraneEnter{crane_raw(a0)});
      }
    } else if (std::holds_alternative<CraneCont_Node>(_frame)) {
      auto _f = std::move(std::get<CraneCont_Node>(_frame));
      uint64_t a1 = _f.a1;
      const MemSafetyProbe24::tree &a2 = *_f.a2;
      _stack.emplace_back(CraneCont_Node_1{std::move(_result), a1});
      _stack.emplace_back(CraneEnter{&a2});
    } else {
      auto _f = std::move(std::get<CraneCont_Node_1>(_frame));
      uint64_t a1 = _f.a1;
      _result = std::move(_f._tmp2).app(
          mylist<uint64_t>::mycons(a1, std::move(_result)));
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
    const MemSafetyProbe24::tree &t2) { /// CraneEnter: captures varying
                                        /// parameters for each recursive call.

  struct CraneEnter {
    const MemSafetyProbe24::tree *t2;
    const MemSafetyProbe24::tree *t1;
  };

  /// CraneCont_Node: saves [a1, a10, a2, a20], resumes after recursive call,
  /// then processes rest.
  struct CraneCont_Node {
    uint64_t a1;
    uint64_t a10;
    const MemSafetyProbe24::tree *a2;
    const MemSafetyProbe24::tree *a20;
  };

  /// CraneCont_Node_1: saves [_tmp2, a1, a10], resumes after recursive call,
  /// then processes rest.
  struct CraneCont_Node_1 {
    MemSafetyProbe24::mylist<std::pair<uint64_t, uint64_t>> _tmp2;
    uint64_t a1;
    uint64_t a10;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont_Node, CraneCont_Node_1>;
  MemSafetyProbe24::mylist<std::pair<uint64_t, uint64_t>> _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{&t2, &t1});
  /// Loopified zip_trees: CraneEnter -> CraneCont_Node -> CraneCont_Node_1.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
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
              CraneCont_Node{a1, a10, crane_raw(a2), crane_raw(a20)});
          _stack.emplace_back(CraneEnter{crane_raw(a00), crane_raw(a0)});
        }
      }
    } else if (std::holds_alternative<CraneCont_Node>(_frame)) {
      auto _f = std::move(std::get<CraneCont_Node>(_frame));
      uint64_t a1 = _f.a1;
      uint64_t a10 = _f.a10;
      const MemSafetyProbe24::tree &a2 = *_f.a2;
      const MemSafetyProbe24::tree &a20 = *_f.a20;
      _stack.emplace_back(CraneCont_Node_1{std::move(_result), a1, a10});
      _stack.emplace_back(CraneEnter{&a20, &a2});
    } else {
      auto _f = std::move(std::get<CraneCont_Node_1>(_frame));
      uint64_t a1 = _f.a1;
      uint64_t a10 = _f.a10;
      _result =
          std::move(_f._tmp2).app(mylist<std::pair<uint64_t, uint64_t>>::mycons(
              std::make_pair(a1, a10), std::move(_result)));
    }
  }
  return _result;
}
