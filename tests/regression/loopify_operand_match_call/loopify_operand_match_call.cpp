#include "loopify_operand_match_call.h"

uint64_t
LoopifyOperandMatchCall::depthish(const LoopifyOperandMatchCall::tree &t) {
  if (std::holds_alternative<typename LoopifyOperandMatchCall::tree::Leaf>(
          t.v())) {
    return UINT64_C(0);
  } else {
    const auto &[l0, r0] =
        std::get<typename LoopifyOperandMatchCall::tree::Node>(t.v());
    return (
        (std::holds_alternative<typename LoopifyOperandMatchCall::tree::Leaf>(
             l0->v())
             ? depthish(*r0)
             : (depthish(*l0) + depthish(*r0))) +
        1);
  }
}

LoopifyOperandMatchCall::tree
LoopifyOperandMatchCall::mirror(const LoopifyOperandMatchCall::tree &
                                    t) { /// CraneEnter: captures varying
                                         /// parameters for each recursive call.

  struct CraneEnter {
    const LoopifyOperandMatchCall::tree *t;
  };

  /// CraneCont_Node: saves [_tmp2], resumes after recursive call, then
  /// processes rest.
  struct CraneCont_Node {
    LoopifyOperandMatchCall::tree _tmp2;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont_Node>;
  LoopifyOperandMatchCall::tree _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{&t});
  /// Loopified mirror: CraneEnter -> CraneCont_Node.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      const LoopifyOperandMatchCall::tree &t = *_f.t;
      if (std::holds_alternative<typename LoopifyOperandMatchCall::tree::Leaf>(
              t.v())) {
        _result = tree::leaf();
      } else {
        const auto &[l0, r0] =
            std::get<typename LoopifyOperandMatchCall::tree::Node>(t.v());
        _stack.emplace_back(CraneCont_Node{
            (std::holds_alternative<
                 typename LoopifyOperandMatchCall::tree::Leaf>(r0->v())
                 ? mirror(*l0)
                 : mirror(*r0))});
        _stack.emplace_back(CraneEnter{crane_raw(l0)});
      }
    } else {
      auto _f = std::move(std::get<CraneCont_Node>(_frame));
      _result = tree::node(std::move(_f._tmp2), std::move(_result));
    }
  }
  return _result;
}

uint64_t
LoopifyOperandMatchCall::size(const LoopifyOperandMatchCall::tree
                                  &t) { /// CraneEnter: captures varying
                                        /// parameters for each recursive call.

  struct CraneEnter {
    const LoopifyOperandMatchCall::tree *t;
  };

  /// CraneCont_Node: saves [r0], resumes after recursive call, then processes
  /// rest.
  struct CraneCont_Node {
    const LoopifyOperandMatchCall::tree *r0;
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
      const LoopifyOperandMatchCall::tree &t = *_f.t;
      if (std::holds_alternative<typename LoopifyOperandMatchCall::tree::Leaf>(
              t.v())) {
        _result = UINT64_C(1);
      } else {
        const auto &[l0, r0] =
            std::get<typename LoopifyOperandMatchCall::tree::Node>(t.v());
        _stack.emplace_back(CraneCont_Node{crane_raw(r0)});
        _stack.emplace_back(CraneEnter{crane_raw(l0)});
      }
    } else if (std::holds_alternative<CraneCont_Node>(_frame)) {
      auto _f = std::move(std::get<CraneCont_Node>(_frame));
      const LoopifyOperandMatchCall::tree &r0 = *_f.r0;
      _stack.emplace_back(CraneCont_Node_1{std::move(_result)});
      _stack.emplace_back(CraneEnter{&r0});
    } else {
      auto _f = std::move(std::get<CraneCont_Node_1>(_frame));
      _result = (_f._tmp2 + std::move(_result));
    }
  }
  return _result;
}

LoopifyOperandMatchCall::tree LoopifyOperandMatchCall::comb(
    uint64_t n) { /// CraneEnter: captures varying parameters for each recursive
                  /// call.

  struct CraneEnter {
    uint64_t n;
  };

  /// CraneCont_m: saves [m], resumes after recursive call, then processes rest.
  struct CraneCont_m {
    uint64_t m;
  };

  /// CraneCont_m_1: saves [_tmp2], resumes after recursive call, then processes
  /// rest.
  struct CraneCont_m_1 {
    LoopifyOperandMatchCall::tree _tmp2;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont_m, CraneCont_m_1>;
  LoopifyOperandMatchCall::tree _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{n});
  /// Loopified comb: CraneEnter -> CraneCont_m -> CraneCont_m_1.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      uint64_t n = _f.n;
      if (n <= 0) {
        _result = tree::leaf();
      } else {
        uint64_t k = n - 1;
        if (k <= 0) {
          _result = tree::node(tree::leaf(), tree::leaf());
        } else {
          uint64_t m = k - 1;
          _stack.emplace_back(CraneCont_m{m});
          _stack.emplace_back(CraneEnter{k});
        }
      }
    } else if (std::holds_alternative<CraneCont_m>(_frame)) {
      auto _f = std::move(std::get<CraneCont_m>(_frame));
      uint64_t m = _f.m;
      _stack.emplace_back(CraneCont_m_1{std::move(_result)});
      _stack.emplace_back(CraneEnter{m});
    } else {
      auto _f = std::move(std::get<CraneCont_m_1>(_frame));
      _result = tree::node(std::move(_f._tmp2),
                           tree::node(tree::leaf(), std::move(_result)));
    }
  }
  return _result;
}
