#include "loopify_moves_captured_closure.h"

uint64_t
LoopifyMovesCapturedClosure::sumw(uint64_t w,
                                  const LoopifyMovesCapturedClosure::tree &t) {
  crane::fn<uint64_t(uint64_t)> weigh = [=](uint64_t x) { return (x * w); };
  {
    const LoopifyMovesCapturedClosure::tree &_lc1_t0 = t;

    /// CraneEnter: captures varying parameters for each recursive call.
    struct CraneEnter {
      const LoopifyMovesCapturedClosure::tree *t0;
    };

    /// CraneCont_Node: saves [a1, a2, weigh], resumes after recursive call,
    /// then processes rest.
    struct CraneCont_Node {
      uint64_t a1;
      const LoopifyMovesCapturedClosure::tree *a2;
      crane::fn<uint64_t(uint64_t)> weigh;
    };

    /// CraneCont_Node_1: saves [_tmp2, a1, weigh], resumes after recursive
    /// call, then processes rest.
    struct CraneCont_Node_1 {
      uint64_t _tmp2;
      uint64_t a1;
      crane::fn<uint64_t(uint64_t)> weigh;
    };

    using CraneFrame =
        std::variant<CraneEnter, CraneCont_Node, CraneCont_Node_1>;
    uint64_t _lc1_result{};
    crane::small_vector<CraneFrame> _lc1_stack;
    _lc1_stack.emplace_back(CraneEnter{&_lc1_t0});
    /// Loopified go: CraneEnter -> CraneCont_Node -> CraneCont_Node_1.
    while (!_lc1_stack.empty()) {
      CraneFrame _frame = std::move(_lc1_stack.back());
      _lc1_stack.pop_back();
      if (std::holds_alternative<CraneEnter>(_frame)) {
        auto _f = std::move(std::get<CraneEnter>(_frame));
        const LoopifyMovesCapturedClosure::tree &_lc1_t0 = *_f.t0;
        if (std::holds_alternative<
                typename LoopifyMovesCapturedClosure::tree::Leaf>(
                _lc1_t0.v())) {
          _lc1_result = UINT64_C(0);
        } else {
          const auto &[a0, a1, a2] =
              std::get<typename LoopifyMovesCapturedClosure::tree::Node>(
                  _lc1_t0.v());
          _lc1_stack.emplace_back(
              CraneCont_Node{a1, crane_raw(a2), std::move(weigh)});
          _lc1_stack.emplace_back(CraneEnter{crane_raw(a0)});
        }
      } else if (std::holds_alternative<CraneCont_Node>(_frame)) {
        auto _f = std::move(std::get<CraneCont_Node>(_frame));
        uint64_t a1 = _f.a1;
        const LoopifyMovesCapturedClosure::tree &a2 = *_f.a2;
        crane::fn<uint64_t(uint64_t)> weigh = std::move(_f.weigh);
        _lc1_stack.emplace_back(
            CraneCont_Node_1{std::move(_lc1_result), a1, std::move(weigh)});
        _lc1_stack.emplace_back(CraneEnter{&a2});
      } else {
        auto _f = std::move(std::get<CraneCont_Node_1>(_frame));
        uint64_t a1 = _f.a1;
        crane::fn<uint64_t(uint64_t)> weigh = std::move(_f.weigh);
        _lc1_result = ((_f._tmp2 + weigh(a1)) + std::move(_lc1_result));
      }
    }
    return _lc1_result;
  }
}

uint64_t LoopifyMovesCapturedClosure::sumw_list(uint64_t w,
                                                const List<uint64_t> &l) {
  crane::fn<uint64_t(uint64_t)> weigh = [=](uint64_t x) { return (x * w); };
  {
    const List<uint64_t> &_lc1_l0 = l;

    /// CraneEnter: captures varying parameters for each recursive call.
    struct CraneEnter {
      const List<uint64_t> *l0;
    };

    /// CraneCont_Cons: saves [a0, weigh], resumes after recursive call, then
    /// processes rest.
    struct CraneCont_Cons {
      uint64_t a0;
      crane::fn<uint64_t(uint64_t)> weigh;
    };

    using CraneFrame = std::variant<CraneEnter, CraneCont_Cons>;
    uint64_t _lc1_result{};
    crane::small_vector<CraneFrame> _lc1_stack;
    _lc1_stack.emplace_back(CraneEnter{&_lc1_l0});
    /// Loopified go: CraneEnter -> CraneCont_Cons.
    while (!_lc1_stack.empty()) {
      CraneFrame _frame = std::move(_lc1_stack.back());
      _lc1_stack.pop_back();
      if (std::holds_alternative<CraneEnter>(_frame)) {
        auto _f = std::move(std::get<CraneEnter>(_frame));
        const List<uint64_t> &_lc1_l0 = *_f.l0;
        if (std::holds_alternative<typename List<uint64_t>::Nil>(_lc1_l0.v())) {
          _lc1_result = UINT64_C(0);
        } else {
          const auto &[a0, a1] =
              std::get<typename List<uint64_t>::Cons>(_lc1_l0.v());
          _lc1_stack.emplace_back(CraneCont_Cons{a0, std::move(weigh)});
          _lc1_stack.emplace_back(CraneEnter{crane_raw(a1)});
        }
      } else {
        auto _f = std::move(std::get<CraneCont_Cons>(_frame));
        uint64_t a0 = _f.a0;
        crane::fn<uint64_t(uint64_t)> weigh = std::move(_f.weigh);
        _lc1_result = (weigh(a0) + std::move(_lc1_result));
      }
    }
    return _lc1_result;
  }
}

uint64_t LoopifyMovesCapturedClosure::sumw_acc(uint64_t w,
                                               const List<uint64_t> &l) {
  crane::fn<uint64_t(uint64_t)> weigh = [=](uint64_t x) { return (x * w); };
  {
    const List<uint64_t> &_lc1_l0 = l;
    uint64_t _lc1_acc = UINT64_C(0);
    uint64_t _lc1_loop_acc = _lc1_acc;
    const List<uint64_t> *_lc1_loop_l0 = &_lc1_l0;
    while (true) {
      if (std::holds_alternative<typename List<uint64_t>::Nil>(
              _lc1_loop_l0->v())) {
        return _lc1_loop_acc;
      } else {
        const auto &[a0, a1] =
            std::get<typename List<uint64_t>::Cons>(_lc1_loop_l0->v());
        _lc1_loop_acc = (_lc1_loop_acc + weigh(a0));
        _lc1_loop_l0 = crane_raw(a1);
      }
    }
  }
}
