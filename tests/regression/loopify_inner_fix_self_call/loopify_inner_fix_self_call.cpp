#include "loopify_inner_fix_self_call.h"

/// An inner fixpoint, loopified, calling itself and its enclosing fixpoint
/// in non-tail positions -- the shape of FMapAVL.join's join_aux.
LoopifyInnerFixSelfCall::tree
LoopifyInnerFixSelfCall::node(const LoopifyInnerFixSelfCall::tree &l,
                              uint64_t x,
                              const LoopifyInnerFixSelfCall::tree &r) {
  return tree::node(l, x, r);
}

uint64_t LoopifyInnerFixSelfCall::size(const LoopifyInnerFixSelfCall::tree &t) {
  // Explicit stack replaces the non-tail recursion of size: _call frames are
  // pending calls, _after frames resume a caller.
  struct _call {
    const LoopifyInnerFixSelfCall::tree *t;
  };

  struct _after_size_in_Node {
    const LoopifyInnerFixSelfCall::tree *a2;
  };

  struct _after_size_in_Node_2 {
    uint64_t _tmp2;
  };

  using _frame =
      std::variant<_call, _after_size_in_Node, _after_size_in_Node_2>;
  uint64_t _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&t});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const LoopifyInnerFixSelfCall::tree &t = *_f.t;
      if (std::holds_alternative<typename LoopifyInnerFixSelfCall::tree::Leaf>(
              t.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, _, a2] =
            std::get<typename LoopifyInnerFixSelfCall::tree::Node>(t.v());
        _stack.emplace_back(_after_size_in_Node{crane_raw(a2)});
        _stack.emplace_back(_call{crane_raw(a0)});
      }
    } else if (std::holds_alternative<_after_size_in_Node>(_popped)) {
      auto _f = std::move(std::get<_after_size_in_Node>(_popped));
      _stack.pop_back();
      const LoopifyInnerFixSelfCall::tree &a2 = *_f.a2;
      _stack.emplace_back(_after_size_in_Node_2{std::move(_result)});
      _stack.emplace_back(_call{&a2});
    } else {
      auto _f = std::move(std::get<_after_size_in_Node_2>(_popped));
      _stack.pop_back();
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
LoopifyInnerFixSelfCall::tree
LoopifyInnerFixSelfCall::join(LoopifyInnerFixSelfCall::tree l, uint64_t x0_,
                              const LoopifyInnerFixSelfCall::tree &x1_) {
  // Explicit stack replaces the non-tail recursion of join: _call frames are
  // pending calls, _after frames resume a caller.
  struct _call {
    const LoopifyInnerFixSelfCall::tree *x1_;
    LoopifyInnerFixSelfCall::tree l;
  };

  struct _call_join_aux {
    const LoopifyInnerFixSelfCall::tree *r;
    std::shared_ptr<LoopifyInnerFixSelfCall::tree> a0;
    uint64_t a1;
    std::shared_ptr<LoopifyInnerFixSelfCall::tree> a2;
    LoopifyInnerFixSelfCall::tree l;
    uint64_t x0_;
  };

  struct _after_join_aux_in_true {
    uint64_t a10;
    std::shared_ptr<LoopifyInnerFixSelfCall::tree> a20;
  };

  struct _after_join_in_true {
    std::shared_ptr<LoopifyInnerFixSelfCall::tree> a0;
    uint64_t a1;
  };

  using _frame = std::variant<_call, _call_join_aux, _after_join_aux_in_true,
                              _after_join_in_true>;
  LoopifyInnerFixSelfCall::tree _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&x1_, std::move(l)});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const LoopifyInnerFixSelfCall::tree &x1_ = *_f.x1_;
      LoopifyInnerFixSelfCall::tree l = std::move(_f.l);
      if (std::holds_alternative<typename LoopifyInnerFixSelfCall::tree::Leaf>(
              l.v_mut())) {
        _result = add(x0_, x1_);
      } else {
        auto &[a0, a1, a2] =
            std::get<typename LoopifyInnerFixSelfCall::tree::Node>(l.v_mut());
        _stack.emplace_back(_call_join_aux{&x1_, a0, a1, a2, l, x0_});
      }
    } else if (std::holds_alternative<_call_join_aux>(_popped)) {
      auto _f = std::move(std::get<_call_join_aux>(_popped));
      _stack.pop_back();
      const LoopifyInnerFixSelfCall::tree &r = *_f.r;
      std::shared_ptr<LoopifyInnerFixSelfCall::tree> a0 = std::move(_f.a0);
      uint64_t a1 = _f.a1;
      std::shared_ptr<LoopifyInnerFixSelfCall::tree> a2 = std::move(_f.a2);
      LoopifyInnerFixSelfCall::tree l = std::move(_f.l);
      uint64_t x0_ = _f.x0_;
      if (std::holds_alternative<typename LoopifyInnerFixSelfCall::tree::Leaf>(
              r.v())) {
        _result = node(l, x0_, tree::leaf());
      } else {
        const auto &[a00, a10, a20] =
            std::get<typename LoopifyInnerFixSelfCall::tree::Node>(r.v());
        if (size(*a20) < a1) {
          _stack.emplace_back(_after_join_in_true{std::move(a0), a1});
          _stack.emplace_back(_call{&r, *a2});
        } else {
          if (a1 < size(*a00)) {
            _stack.emplace_back(_after_join_aux_in_true{a10, a20});
            _stack.emplace_back(
                _call_join_aux{crane_raw(a00), std::move(a0), a1, std::move(a2),
                               std::move(l), x0_});
          } else {
            _result = node(l, x0_, r);
          }
        }
      }
    } else if (std::holds_alternative<_after_join_aux_in_true>(_popped)) {
      auto _f = std::move(std::get<_after_join_aux_in_true>(_popped));
      _stack.pop_back();
      uint64_t a10 = _f.a10;
      std::shared_ptr<LoopifyInnerFixSelfCall::tree> a20 = std::move(_f.a20);
      _result = node(std::move(_result), a10, *a20);
    } else {
      auto _f = std::move(std::get<_after_join_in_true>(_popped));
      _stack.pop_back();
      std::shared_ptr<LoopifyInnerFixSelfCall::tree> a0 = std::move(_f.a0);
      uint64_t a1 = _f.a1;
      _result = node(*a0, a1, std::move(_result));
    }
  }
  return _result;
}
