#include "loopify_dispatch_on_call.h"

bool LoopifyDispatchOnCall::parity(
    const LoopifyDispatchOnCall::tree
        &t) { /// CraneEnter: captures varying parameters for each recursive
              /// call.

  struct CraneEnter {
    const LoopifyDispatchOnCall::tree *t;
  };

  /// CraneCont2: resumes after recursive call, then processes rest.
  struct CraneCont2 {};

  /// CraneCont_Node: saves [r0], resumes after recursive call, then processes
  /// rest.
  struct CraneCont_Node {
    const LoopifyDispatchOnCall::tree *r0;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont2, CraneCont_Node>;
  bool _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{&t});
  /// Loopified parity: CraneEnter -> CraneCont2 -> CraneCont_Node.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      const LoopifyDispatchOnCall::tree &t = *_f.t;
      if (std::holds_alternative<typename LoopifyDispatchOnCall::tree::Leaf>(
              t.v())) {
        _result = true;
      } else {
        const auto &[l0, r0] =
            std::get<typename LoopifyDispatchOnCall::tree::Node>(t.v());
        _stack.emplace_back(CraneCont_Node{crane_raw(r0)});
        _stack.emplace_back(CraneEnter{crane_raw(l0)});
      }
    } else if (std::holds_alternative<CraneCont2>(_frame)) {
      auto _f = std::move(std::get<CraneCont2>(_frame));
      _result = !(std::move(_result));
    } else {
      auto _f = std::move(std::get<CraneCont_Node>(_frame));
      const LoopifyDispatchOnCall::tree &r0 = *_f.r0;
      if (std::move(_result)) {
        _stack.emplace_back(CraneCont2{});
        _stack.emplace_back(CraneEnter{&r0});
      } else {
        _stack.emplace_back(CraneEnter{&r0});
      }
    }
  }
  return _result;
}

LoopifyDispatchOnCall::tree
LoopifyDispatchOnCall::graft(const LoopifyDispatchOnCall::tree
                                 &t) { /// CraneEnter: captures varying
                                       /// parameters for each recursive call.

  struct CraneEnter {
    const LoopifyDispatchOnCall::tree *t;
  };

  /// CraneCont_Leaf: resumes after recursive call, then processes rest.
  struct CraneCont_Leaf {};

  /// CraneCont_Node: saves [r0], resumes after recursive call, then processes
  /// rest.
  struct CraneCont_Node {
    const LoopifyDispatchOnCall::tree *r0;
  };

  /// CraneCont_Node_1: saves [l1, r1], resumes after recursive call, then
  /// processes rest.
  struct CraneCont_Node_1 {
    std::shared_ptr<LoopifyDispatchOnCall::tree> l1;
    std::shared_ptr<LoopifyDispatchOnCall::tree> r1;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont_Leaf, CraneCont_Node,
                                  CraneCont_Node_1>;
  LoopifyDispatchOnCall::tree _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{&t});
  /// Loopified graft: CraneEnter -> CraneCont_Leaf -> CraneCont_Node ->
  /// CraneCont_Node_1.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      const LoopifyDispatchOnCall::tree &t = *_f.t;
      if (std::holds_alternative<typename LoopifyDispatchOnCall::tree::Leaf>(
              t.v())) {
        _result = tree::leaf();
      } else {
        const auto &[l0, r0] =
            std::get<typename LoopifyDispatchOnCall::tree::Node>(t.v());
        _stack.emplace_back(CraneCont_Node{crane_raw(r0)});
        _stack.emplace_back(CraneEnter{crane_raw(l0)});
      }
    } else if (std::holds_alternative<CraneCont_Leaf>(_frame)) {
      auto _f = std::move(std::get<CraneCont_Leaf>(_frame));
      _result = tree::node(std::move(_result), tree::leaf());
    } else if (std::holds_alternative<CraneCont_Node>(_frame)) {
      auto _f = std::move(std::get<CraneCont_Node>(_frame));
      const LoopifyDispatchOnCall::tree &r0 = *_f.r0;
      LoopifyDispatchOnCall::tree _tmp3 = std::move(_result);
      if (std::holds_alternative<typename LoopifyDispatchOnCall::tree::Leaf>(
              _tmp3.v_mut())) {
        _stack.emplace_back(CraneCont_Leaf{});
        _stack.emplace_back(CraneEnter{&r0});
      } else {
        auto &[l1, r1] =
            std::get<typename LoopifyDispatchOnCall::tree::Node>(_tmp3.v_mut());
        _stack.emplace_back(CraneCont_Node_1{l1, r1});
        _stack.emplace_back(CraneEnter{&r0});
      }
    } else {
      auto _f = std::move(std::get<CraneCont_Node_1>(_frame));
      std::shared_ptr<LoopifyDispatchOnCall::tree> l1 = std::move(_f.l1);
      std::shared_ptr<LoopifyDispatchOnCall::tree> r1 = std::move(_f.r1);
      _result = tree::node(std::move(_result), tree::node(*r1, *l1));
    }
  }
  return _result;
}

uint64_t
LoopifyDispatchOnCall::size(const LoopifyDispatchOnCall::tree
                                &t) { /// CraneEnter: captures varying
                                      /// parameters for each recursive call.

  struct CraneEnter {
    const LoopifyDispatchOnCall::tree *t;
  };

  /// CraneCont_Node: saves [r0], resumes after recursive call, then processes
  /// rest.
  struct CraneCont_Node {
    const LoopifyDispatchOnCall::tree *r0;
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
      const LoopifyDispatchOnCall::tree &t = *_f.t;
      if (std::holds_alternative<typename LoopifyDispatchOnCall::tree::Leaf>(
              t.v())) {
        _result = UINT64_C(1);
      } else {
        const auto &[l0, r0] =
            std::get<typename LoopifyDispatchOnCall::tree::Node>(t.v());
        _stack.emplace_back(CraneCont_Node{crane_raw(r0)});
        _stack.emplace_back(CraneEnter{crane_raw(l0)});
      }
    } else if (std::holds_alternative<CraneCont_Node>(_frame)) {
      auto _f = std::move(std::get<CraneCont_Node>(_frame));
      const LoopifyDispatchOnCall::tree &r0 = *_f.r0;
      _stack.emplace_back(CraneCont_Node_1{std::move(_result)});
      _stack.emplace_back(CraneEnter{&r0});
    } else {
      auto _f = std::move(std::get<CraneCont_Node_1>(_frame));
      _result = (_f._tmp2 + std::move(_result));
    }
  }
  return _result;
}

LoopifyDispatchOnCall::tree LoopifyDispatchOnCall::comb(
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
    LoopifyDispatchOnCall::tree _tmp2;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont_m, CraneCont_m_1>;
  LoopifyDispatchOnCall::tree _result{};
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
