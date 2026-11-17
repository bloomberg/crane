#include "loopify_dispatch_on_call.h"

bool LoopifyDispatchOnCall::parity(const LoopifyDispatchOnCall::tree &t) {
  // Explicit stack replaces the non-tail recursion of parity: _call frames are
  // pending calls, _after frames resume a caller.
  struct _call {
    const LoopifyDispatchOnCall::tree *t;
  };

  struct _after_parity_in_Node {
    const LoopifyDispatchOnCall::tree *r0;
  };

  struct _after_parity_in_true {};

  using _frame =
      std::variant<_call, _after_parity_in_Node, _after_parity_in_true>;
  bool _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&t});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const LoopifyDispatchOnCall::tree &t = *_f.t;
      if (std::holds_alternative<typename LoopifyDispatchOnCall::tree::Leaf>(
              t.v())) {
        _result = true;
      } else {
        const auto &[l0, r0] =
            std::get<typename LoopifyDispatchOnCall::tree::Node>(t.v());
        _stack.emplace_back(_after_parity_in_Node{crane_raw(r0)});
        _stack.emplace_back(_call{crane_raw(l0)});
      }
    } else if (std::holds_alternative<_after_parity_in_Node>(_popped)) {
      auto _f = std::move(std::get<_after_parity_in_Node>(_popped));
      _stack.pop_back();
      const LoopifyDispatchOnCall::tree &r0 = *_f.r0;
      if (std::move(_result)) {
        _stack.emplace_back(_after_parity_in_true{});
        _stack.emplace_back(_call{&r0});
      } else {
        _stack.emplace_back(_call{&r0});
      }
    } else {
      auto _f = std::move(std::get<_after_parity_in_true>(_popped));
      _stack.pop_back();
      _result = !(std::move(_result));
    }
  }
  return _result;
}

LoopifyDispatchOnCall::tree
LoopifyDispatchOnCall::graft(const LoopifyDispatchOnCall::tree &t) {
  // Explicit stack replaces the non-tail recursion of graft: _call frames are
  // pending calls, _after frames resume a caller.
  struct _call {
    const LoopifyDispatchOnCall::tree *t;
  };

  struct _after_graft_in_Leaf {};

  struct _after_graft_in_Node {
    const LoopifyDispatchOnCall::tree *r0;
  };

  struct _after_graft_in_Node_2 {
    std::shared_ptr<LoopifyDispatchOnCall::tree> l1;
    std::shared_ptr<LoopifyDispatchOnCall::tree> r1;
  };

  using _frame = std::variant<_call, _after_graft_in_Leaf, _after_graft_in_Node,
                              _after_graft_in_Node_2>;
  LoopifyDispatchOnCall::tree _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&t});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const LoopifyDispatchOnCall::tree &t = *_f.t;
      if (std::holds_alternative<typename LoopifyDispatchOnCall::tree::Leaf>(
              t.v())) {
        _result = tree::leaf();
      } else {
        const auto &[l0, r0] =
            std::get<typename LoopifyDispatchOnCall::tree::Node>(t.v());
        _stack.emplace_back(_after_graft_in_Node{crane_raw(r0)});
        _stack.emplace_back(_call{crane_raw(l0)});
      }
    } else if (std::holds_alternative<_after_graft_in_Leaf>(_popped)) {
      auto _f = std::move(std::get<_after_graft_in_Leaf>(_popped));
      _stack.pop_back();
      _result = tree::node(std::move(_result), tree::leaf());
    } else if (std::holds_alternative<_after_graft_in_Node>(_popped)) {
      auto _f = std::move(std::get<_after_graft_in_Node>(_popped));
      _stack.pop_back();
      const LoopifyDispatchOnCall::tree &r0 = *_f.r0;
      LoopifyDispatchOnCall::tree _tmp3 = std::move(_result);
      if (std::holds_alternative<typename LoopifyDispatchOnCall::tree::Leaf>(
              _tmp3.v_mut())) {
        _stack.emplace_back(_after_graft_in_Leaf{});
        _stack.emplace_back(_call{&r0});
      } else {
        auto &[l1, r1] =
            std::get<typename LoopifyDispatchOnCall::tree::Node>(_tmp3.v_mut());
        _stack.emplace_back(_after_graft_in_Node_2{l1, r1});
        _stack.emplace_back(_call{&r0});
      }
    } else {
      auto _f = std::move(std::get<_after_graft_in_Node_2>(_popped));
      _stack.pop_back();
      std::shared_ptr<LoopifyDispatchOnCall::tree> l1 = std::move(_f.l1);
      std::shared_ptr<LoopifyDispatchOnCall::tree> r1 = std::move(_f.r1);
      _result = tree::node(std::move(_result), tree::node(*r1, *l1));
    }
  }
  return _result;
}

uint64_t LoopifyDispatchOnCall::size(const LoopifyDispatchOnCall::tree &t) {
  // Explicit stack replaces the non-tail recursion of size: _call frames are
  // pending calls, _after frames resume a caller.
  struct _call {
    const LoopifyDispatchOnCall::tree *t;
  };

  struct _after_size_in_Node {
    const LoopifyDispatchOnCall::tree *r0;
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
      const LoopifyDispatchOnCall::tree &t = *_f.t;
      if (std::holds_alternative<typename LoopifyDispatchOnCall::tree::Leaf>(
              t.v())) {
        _result = UINT64_C(1);
      } else {
        const auto &[l0, r0] =
            std::get<typename LoopifyDispatchOnCall::tree::Node>(t.v());
        _stack.emplace_back(_after_size_in_Node{crane_raw(r0)});
        _stack.emplace_back(_call{crane_raw(l0)});
      }
    } else if (std::holds_alternative<_after_size_in_Node>(_popped)) {
      auto _f = std::move(std::get<_after_size_in_Node>(_popped));
      _stack.pop_back();
      const LoopifyDispatchOnCall::tree &r0 = *_f.r0;
      _stack.emplace_back(_after_size_in_Node_2{std::move(_result)});
      _stack.emplace_back(_call{&r0});
    } else {
      auto _f = std::move(std::get<_after_size_in_Node_2>(_popped));
      _stack.pop_back();
      _result = (_f._tmp2 + std::move(_result));
    }
  }
  return _result;
}

LoopifyDispatchOnCall::tree LoopifyDispatchOnCall::comb(uint64_t n) {
  // Explicit stack replaces the non-tail recursion of comb: _call frames are
  // pending calls, _after frames resume a caller.
  struct _call {
    uint64_t n;
  };

  struct _after_comb_in_S {
    uint64_t m;
  };

  struct _after_comb_in_S_2 {
    LoopifyDispatchOnCall::tree _tmp2;
  };

  using _frame = std::variant<_call, _after_comb_in_S, _after_comb_in_S_2>;
  LoopifyDispatchOnCall::tree _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{n});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      uint64_t n = _f.n;
      if (n <= 0) {
        _result = tree::leaf();
      } else {
        uint64_t k = n - 1;
        if (k <= 0) {
          _result = tree::node(tree::leaf(), tree::leaf());
        } else {
          uint64_t m = k - 1;
          _stack.emplace_back(_after_comb_in_S{m});
          _stack.emplace_back(_call{k});
        }
      }
    } else if (std::holds_alternative<_after_comb_in_S>(_popped)) {
      auto _f = std::move(std::get<_after_comb_in_S>(_popped));
      _stack.pop_back();
      uint64_t m = _f.m;
      _stack.emplace_back(_after_comb_in_S_2{std::move(_result)});
      _stack.emplace_back(_call{m});
    } else {
      auto _f = std::move(std::get<_after_comb_in_S_2>(_popped));
      _stack.pop_back();
      _result = tree::node(std::move(_f._tmp2),
                           tree::node(tree::leaf(), std::move(_result)));
    }
  }
  return _result;
}
