#include "loopify_operand_match_call.h"

uint64_t
LoopifyOperandMatchCall::depthish(const LoopifyOperandMatchCall::tree &t) {
  // Explicit stack replaces the non-tail recursion of depthish: _call frames
  // are pending calls, _after frames resume a caller.
  struct _call {
    const LoopifyOperandMatchCall::tree *t;
  };

  struct _after_depthish_in_Leaf {};

  struct _after_depthish_in_Node {
    const LoopifyOperandMatchCall::tree *r0;
  };

  struct _after_depthish_in_Node_2 {
    uint64_t _tmp2;
  };

  using _frame =
      std::variant<_call, _after_depthish_in_Leaf, _after_depthish_in_Node,
                   _after_depthish_in_Node_2>;
  uint64_t _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&t});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const LoopifyOperandMatchCall::tree &t = *_f.t;
      if (std::holds_alternative<typename LoopifyOperandMatchCall::tree::Leaf>(
              t.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[l0, r0] =
            std::get<typename LoopifyOperandMatchCall::tree::Node>(t.v());
        auto &&_sv = *l0;
        if (std::holds_alternative<typename LoopifyOperandMatchCall::tree::Leaf>(
                _sv.v())) {
          _stack.emplace_back(_after_depthish_in_Leaf{});
          _stack.emplace_back(_call{crane_raw(r0)});
        } else {
          _stack.emplace_back(_after_depthish_in_Node{crane_raw(r0)});
          _stack.emplace_back(_call{crane_raw(l0)});
        }
      }
    } else if (std::holds_alternative<_after_depthish_in_Leaf>(_popped)) {
      auto _f = std::move(std::get<_after_depthish_in_Leaf>(_popped));
      _stack.pop_back();
      _result = (_result + 1);
    } else if (std::holds_alternative<_after_depthish_in_Node>(_popped)) {
      auto _f = std::move(std::get<_after_depthish_in_Node>(_popped));
      _stack.pop_back();
      const LoopifyOperandMatchCall::tree &r0 = *_f.r0;
      _stack.emplace_back(_after_depthish_in_Node_2{_result});
      _stack.emplace_back(_call{&r0});
    } else {
      auto _f = std::move(std::get<_after_depthish_in_Node_2>(_popped));
      _stack.pop_back();
      _result = ((_f._tmp2 + _result) + 1);
    }
  }
  return _result;
}

LoopifyOperandMatchCall::tree
LoopifyOperandMatchCall::mirror(const LoopifyOperandMatchCall::tree &t) {
  // Explicit stack replaces the non-tail recursion of mirror: _call frames are
  // pending calls, _after frames resume a caller.
  struct _call {
    const LoopifyOperandMatchCall::tree *t;
  };

  struct _after_mirror_in_Leaf {
    const LoopifyOperandMatchCall::tree *l0;
  };

  struct _after_mirror_in_Leaf_2 {
    LoopifyOperandMatchCall::tree _tmp2;
  };

  struct _after_mirror_in_Node {
    const LoopifyOperandMatchCall::tree *l0;
  };

  struct _after_mirror_in_Node_2 {
    LoopifyOperandMatchCall::tree _tmp4;
  };

  using _frame =
      std::variant<_call, _after_mirror_in_Leaf, _after_mirror_in_Leaf_2,
                   _after_mirror_in_Node, _after_mirror_in_Node_2>;
  LoopifyOperandMatchCall::tree _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&t});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const LoopifyOperandMatchCall::tree &t = *_f.t;
      if (std::holds_alternative<typename LoopifyOperandMatchCall::tree::Leaf>(
              t.v())) {
        _result = tree::leaf();
      } else {
        const auto &[l0, r0] =
            std::get<typename LoopifyOperandMatchCall::tree::Node>(t.v());
        auto &&_sv = *r0;
        if (std::holds_alternative<typename LoopifyOperandMatchCall::tree::Leaf>(
                _sv.v())) {
          _stack.emplace_back(_after_mirror_in_Leaf{crane_raw(l0)});
          _stack.emplace_back(_call{crane_raw(l0)});
        } else {
          _stack.emplace_back(_after_mirror_in_Node{crane_raw(l0)});
          _stack.emplace_back(_call{crane_raw(r0)});
        }
      }
    } else if (std::holds_alternative<_after_mirror_in_Leaf>(_popped)) {
      auto _f = std::move(std::get<_after_mirror_in_Leaf>(_popped));
      _stack.pop_back();
      const LoopifyOperandMatchCall::tree &l0 = *_f.l0;
      _stack.emplace_back(_after_mirror_in_Leaf_2{std::move(_result)});
      _stack.emplace_back(_call{&l0});
    } else if (std::holds_alternative<_after_mirror_in_Leaf_2>(_popped)) {
      auto _f = std::move(std::get<_after_mirror_in_Leaf_2>(_popped));
      _stack.pop_back();
      _result = tree::node(std::move(_f._tmp2), std::move(_result));
    } else if (std::holds_alternative<_after_mirror_in_Node>(_popped)) {
      auto _f = std::move(std::get<_after_mirror_in_Node>(_popped));
      _stack.pop_back();
      const LoopifyOperandMatchCall::tree &l0 = *_f.l0;
      _stack.emplace_back(_after_mirror_in_Node_2{std::move(_result)});
      _stack.emplace_back(_call{&l0});
    } else {
      auto _f = std::move(std::get<_after_mirror_in_Node_2>(_popped));
      _stack.pop_back();
      _result = tree::node(std::move(_f._tmp4), std::move(_result));
    }
  }
  return _result;
}

uint64_t LoopifyOperandMatchCall::size(const LoopifyOperandMatchCall::tree &t) {
  // Explicit stack replaces the non-tail recursion of size: _call frames are
  // pending calls, _after frames resume a caller.
  struct _call {
    const LoopifyOperandMatchCall::tree *t;
  };

  struct _after_size_in_Node {
    const LoopifyOperandMatchCall::tree *r0;
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
      const LoopifyOperandMatchCall::tree &t = *_f.t;
      if (std::holds_alternative<typename LoopifyOperandMatchCall::tree::Leaf>(
              t.v())) {
        _result = UINT64_C(1);
      } else {
        const auto &[l0, r0] =
            std::get<typename LoopifyOperandMatchCall::tree::Node>(t.v());
        _stack.emplace_back(_after_size_in_Node{crane_raw(r0)});
        _stack.emplace_back(_call{crane_raw(l0)});
      }
    } else if (std::holds_alternative<_after_size_in_Node>(_popped)) {
      auto _f = std::move(std::get<_after_size_in_Node>(_popped));
      _stack.pop_back();
      const LoopifyOperandMatchCall::tree &r0 = *_f.r0;
      _stack.emplace_back(_after_size_in_Node_2{_result});
      _stack.emplace_back(_call{&r0});
    } else {
      auto _f = std::move(std::get<_after_size_in_Node_2>(_popped));
      _stack.pop_back();
      _result = (_f._tmp2 + _result);
    }
  }
  return _result;
}

LoopifyOperandMatchCall::tree LoopifyOperandMatchCall::comb(uint64_t n) {
  // Explicit stack replaces the non-tail recursion of comb: _call frames are
  // pending calls, _after frames resume a caller.
  struct _call {
    uint64_t n;
  };

  struct _after_comb_in_S {
    uint64_t m;
  };

  struct _after_comb_in_S_2 {
    LoopifyOperandMatchCall::tree _tmp2;
  };

  using _frame = std::variant<_call, _after_comb_in_S, _after_comb_in_S_2>;
  LoopifyOperandMatchCall::tree _result{};
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
