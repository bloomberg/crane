#include "loopify_operand_match_call.h"

uint64_t LoopifyOperandMatchCall::depthish(
    const LoopifyOperandMatchCall::tree
        &t) { /// CraneEnter: captures varying parameters for each recursive
              /// call.

  struct CraneEnter {
    const LoopifyOperandMatchCall::tree *t;
  };

  /// CraneCont_Leaf: resumes after recursive call, then processes rest.
  struct CraneCont_Leaf {};

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

  using CraneFrame = std::variant<CraneEnter, CraneCont_Leaf, CraneCont_Node,
                                  CraneCont_Node_1>;
  uint64_t _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{&t});
  /// Loopified depthish: CraneEnter -> CraneCont_Leaf -> CraneCont_Node ->
  /// CraneCont_Node_1.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      const LoopifyOperandMatchCall::tree &t = *_f.t;
      if (std::holds_alternative<typename LoopifyOperandMatchCall::tree::Leaf>(
              t.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[l0, r0] =
            std::get<typename LoopifyOperandMatchCall::tree::Node>(t.v());
        auto &&_sv = *l0;
        if (std::holds_alternative<
                typename LoopifyOperandMatchCall::tree::Leaf>(_sv.v())) {
          _stack.emplace_back(CraneCont_Leaf{});
          _stack.emplace_back(CraneEnter{crane_raw(r0)});
        } else {
          _stack.emplace_back(CraneCont_Node{crane_raw(r0)});
          _stack.emplace_back(CraneEnter{crane_raw(l0)});
        }
      }
    } else if (std::holds_alternative<CraneCont_Leaf>(_frame)) {
      auto _f = std::move(std::get<CraneCont_Leaf>(_frame));
      _result = (std::move(_result) + 1);
    } else if (std::holds_alternative<CraneCont_Node>(_frame)) {
      auto _f = std::move(std::get<CraneCont_Node>(_frame));
      const LoopifyOperandMatchCall::tree &r0 = *_f.r0;
      _stack.emplace_back(CraneCont_Node_1{std::move(_result)});
      _stack.emplace_back(CraneEnter{&r0});
    } else {
      auto _f = std::move(std::get<CraneCont_Node_1>(_frame));
      _result = ((_f._tmp2 + std::move(_result)) + 1);
    }
  }
  return _result;
}

LoopifyOperandMatchCall::tree
LoopifyOperandMatchCall::mirror(const LoopifyOperandMatchCall::tree &
                                    t) { /// CraneEnter: captures varying
                                         /// parameters for each recursive call.

  struct CraneEnter {
    const LoopifyOperandMatchCall::tree *t;
  };

  /// CraneCont_Leaf: saves [l0], resumes after recursive call, then processes
  /// rest.
  struct CraneCont_Leaf {
    const LoopifyOperandMatchCall::tree *l0;
  };

  /// CraneCont_Leaf_1: saves [_tmp2], resumes after recursive call, then
  /// processes rest.
  struct CraneCont_Leaf_1 {
    LoopifyOperandMatchCall::tree _tmp2;
  };

  /// CraneCont_Node: saves [l0], resumes after recursive call, then processes
  /// rest.
  struct CraneCont_Node {
    const LoopifyOperandMatchCall::tree *l0;
  };

  /// CraneCont_Node_1: saves [_tmp4], resumes after recursive call, then
  /// processes rest.
  struct CraneCont_Node_1 {
    LoopifyOperandMatchCall::tree _tmp4;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont_Leaf, CraneCont_Leaf_1,
                                  CraneCont_Node, CraneCont_Node_1>;
  LoopifyOperandMatchCall::tree _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{&t});
  /// Loopified mirror: CraneEnter -> CraneCont_Leaf -> CraneCont_Leaf_1 ->
  /// CraneCont_Node -> CraneCont_Node_1.
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
        auto &&_sv = *r0;
        if (std::holds_alternative<
                typename LoopifyOperandMatchCall::tree::Leaf>(_sv.v())) {
          _stack.emplace_back(CraneCont_Leaf{crane_raw(l0)});
          _stack.emplace_back(CraneEnter{crane_raw(l0)});
        } else {
          _stack.emplace_back(CraneCont_Node{crane_raw(l0)});
          _stack.emplace_back(CraneEnter{crane_raw(r0)});
        }
      }
    } else if (std::holds_alternative<CraneCont_Leaf>(_frame)) {
      auto _f = std::move(std::get<CraneCont_Leaf>(_frame));
      const LoopifyOperandMatchCall::tree &l0 = *_f.l0;
      _stack.emplace_back(CraneCont_Leaf_1{std::move(_result)});
      _stack.emplace_back(CraneEnter{&l0});
    } else if (std::holds_alternative<CraneCont_Leaf_1>(_frame)) {
      auto _f = std::move(std::get<CraneCont_Leaf_1>(_frame));
      _result = tree::node(std::move(_f._tmp2), std::move(_result));
    } else if (std::holds_alternative<CraneCont_Node>(_frame)) {
      auto _f = std::move(std::get<CraneCont_Node>(_frame));
      const LoopifyOperandMatchCall::tree &l0 = *_f.l0;
      _stack.emplace_back(CraneCont_Node_1{std::move(_result)});
      _stack.emplace_back(CraneEnter{&l0});
    } else {
      auto _f = std::move(std::get<CraneCont_Node_1>(_frame));
      _result = tree::node(std::move(_f._tmp4), std::move(_result));
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
