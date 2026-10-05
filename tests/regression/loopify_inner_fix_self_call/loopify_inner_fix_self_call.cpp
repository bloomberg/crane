#include "loopify_inner_fix_self_call.h"

/// An inner fixpoint, loopified, calling itself and its enclosing fixpoint
/// in non-tail positions -- the shape of FMapAVL.join's join_aux.
LoopifyInnerFixSelfCall::tree
LoopifyInnerFixSelfCall::node(const LoopifyInnerFixSelfCall::tree &l,
                              uint64_t x,
                              const LoopifyInnerFixSelfCall::tree &r) {
  return tree::node(l, x, r);
}

uint64_t
LoopifyInnerFixSelfCall::size(const LoopifyInnerFixSelfCall::tree
                                  &t) { /// CraneEnter: captures varying
                                        /// parameters for each recursive call.

  struct CraneEnter {
    const LoopifyInnerFixSelfCall::tree *t;
  };

  /// CraneCont_Node: saves [a2], resumes after recursive call, then processes
  /// rest.
  struct CraneCont_Node {
    const LoopifyInnerFixSelfCall::tree *a2;
  };

  /// CraneCont_Node_1: saves [_tmp2], resumes after recursive call, then
  /// processes rest.
  struct CraneCont_Node_1 {
    uint64_t _tmp2;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont_Node, CraneCont_Node_1>;
  uint64_t _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{&t});
  /// Loopified size: CraneEnter -> CraneCont_Node -> CraneCont_Node_1.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      const LoopifyInnerFixSelfCall::tree &t = *_f.t;
      if (std::holds_alternative<typename LoopifyInnerFixSelfCall::tree::Leaf>(
              t.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1, a2] =
            std::get<typename LoopifyInnerFixSelfCall::tree::Node>(t.v());
        _stack.emplace_back(CraneCont_Node{crane_raw(a2)});
        _stack.emplace_back(CraneEnter{crane_raw(a0)});
      }
    } else if (std::holds_alternative<CraneCont_Node>(_frame)) {
      auto _f = std::move(std::get<CraneCont_Node>(_frame));
      const LoopifyInnerFixSelfCall::tree &a2 = *_f.a2;
      _stack.emplace_back(CraneCont_Node_1{std::move(_result)});
      _stack.emplace_back(CraneEnter{&a2});
    } else {
      auto _f = std::move(std::get<CraneCont_Node_1>(_frame));
      _result = ((_f._tmp2 + std::move(_result)) + 1);
    }
  }
  return _result;
}

LoopifyInnerFixSelfCall::tree
LoopifyInnerFixSelfCall::add(uint64_t x,
                             const LoopifyInnerFixSelfCall::tree &r) {
  return node(tree::leaf(), x, r);
}

/// As FMapAVL.join: each branch is a function of the remaining
/// arguments, and the Node branch is the inner fixpoint itself.
LoopifyInnerFixSelfCall::tree LoopifyInnerFixSelfCall::join(
    const LoopifyInnerFixSelfCall::tree &l, uint64_t x0_,
    LoopifyInnerFixSelfCall::tree x1_) { /// CraneEnter: captures varying
                                         /// parameters for each recursive call.

  struct CraneEnter {
    LoopifyInnerFixSelfCall::tree x1_;
    uint64_t x0_;
    LoopifyInnerFixSelfCall::tree l;
  };

  /// CraneEnter_join_aux: captures varying parameters for each recursive call.
  struct CraneEnter_join_aux {
    LoopifyInnerFixSelfCall::tree r;
    std::shared_ptr<LoopifyInnerFixSelfCall::tree> a0;
    uint64_t a1;
    std::shared_ptr<LoopifyInnerFixSelfCall::tree> a2;
    LoopifyInnerFixSelfCall::tree l;
    uint64_t x0_;
  };

  /// CraneCont1: saves [a0, a1], resumes after recursive call, then processes
  /// rest.
  struct CraneCont1 {
    std::shared_ptr<LoopifyInnerFixSelfCall::tree> a0;
    uint64_t a1;
  };

  /// CraneCont2: saves [a10, a20], resumes after recursive call, then processes
  /// rest.
  struct CraneCont2 {
    uint64_t a10;
    std::shared_ptr<LoopifyInnerFixSelfCall::tree> a20;
  };

  using CraneFrame =
      std::variant<CraneEnter, CraneEnter_join_aux, CraneCont1, CraneCont2>;
  LoopifyInnerFixSelfCall::tree _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{std::move(x1_), x0_, l});
  /// Loopified join: CraneEnter -> CraneCont1 -> CraneCont2.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      LoopifyInnerFixSelfCall::tree x1_ = std::move(_f.x1_);
      uint64_t x0_ = _f.x0_;
      const LoopifyInnerFixSelfCall::tree &l = std::move(_f.l);
      if (std::holds_alternative<typename LoopifyInnerFixSelfCall::tree::Leaf>(
              l.v())) {
        _result = add(x0_, std::move(x1_));
      } else {
        const auto &[a0, a1, a2] =
            std::get<typename LoopifyInnerFixSelfCall::tree::Node>(l.v());
        {
        }
        {
        }
        _stack.emplace_back(
            CraneEnter_join_aux{std::move(x1_), a0, a1, a2, l, x0_});
      }
    } else if (std::holds_alternative<CraneEnter_join_aux>(_frame)) {
      auto _f = std::move(std::get<CraneEnter_join_aux>(_frame));
      const LoopifyInnerFixSelfCall::tree &r = std::move(_f.r);
      std::shared_ptr<LoopifyInnerFixSelfCall::tree> a0 = std::move(_f.a0);
      uint64_t a1 = _f.a1;
      std::shared_ptr<LoopifyInnerFixSelfCall::tree> a2 = std::move(_f.a2);
      const LoopifyInnerFixSelfCall::tree &l = std::move(_f.l);
      uint64_t x0_ = _f.x0_;
      if (std::holds_alternative<typename LoopifyInnerFixSelfCall::tree::Leaf>(
              r.v())) {
        _result = node(l, x0_, tree::leaf());
      } else {
        const auto &[a00, a10, a20] =
            std::get<typename LoopifyInnerFixSelfCall::tree::Node>(r.v());
        if (size(*a20) < a1) {
          _stack.emplace_back(CraneCont1{a0, a1});
          _stack.emplace_back(CraneEnter{r, x0_, *a2});
        } else {
          if (a1 < size(*a00)) {
            _stack.emplace_back(CraneCont2{a10, a20});
            _stack.emplace_back(CraneEnter_join_aux{*a00, a0, a1, a2, l, x0_});
          } else {
            _result = node(l, x0_, r);
          }
        }
      }
    } else if (std::holds_alternative<CraneCont1>(_frame)) {
      auto _f = std::move(std::get<CraneCont1>(_frame));
      std::shared_ptr<LoopifyInnerFixSelfCall::tree> a0 = std::move(_f.a0);
      uint64_t a1 = _f.a1;
      _result = node(*a0, a1, std::move(_result));
    } else {
      auto _f = std::move(std::get<CraneCont2>(_frame));
      uint64_t a10 = _f.a10;
      std::shared_ptr<LoopifyInnerFixSelfCall::tree> a20 = std::move(_f.a20);
      _result = node(std::move(_result), a10, *a20);
    }
  }
  return _result;
}
