#include "immortal_global_constant.h"

ImmortalGlobalConstant::tree ImmortalGlobalConstant::full(uint64_t d) {
  // Explicit stack replaces the non-tail recursion of full: _call frames are
  // pending calls, _after frames resume a caller.
  struct _call {
    uint64_t d;
  };

  struct _after_full_in_S {
    uint64_t d;
    uint64_t k;
  };

  struct _after_full_in_S_2 {
    uint64_t d;
    ImmortalGlobalConstant::tree _tmp2;
  };

  using _frame = std::variant<_call, _after_full_in_S, _after_full_in_S_2>;
  ImmortalGlobalConstant::tree _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{d});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (crane::holds_alternative<_call>(_popped)) {
      auto _f = std::move(crane::get<_call>(_popped));
      _stack.pop_back();
      uint64_t d = _f.d;
      if (d <= 0) {
        _result = tree::leaf();
      } else {
        uint64_t k = d - 1;
        _stack.emplace_back(_after_full_in_S{d, k});
        _stack.emplace_back(_call{k});
      }
    } else if (crane::holds_alternative<_after_full_in_S>(_popped)) {
      auto _f = std::move(crane::get<_after_full_in_S>(_popped));
      _stack.pop_back();
      uint64_t d = _f.d;
      uint64_t k = _f.k;
      _stack.emplace_back(_after_full_in_S_2{d, std::move(_result)});
      _stack.emplace_back(_call{k});
    } else {
      auto _f = std::move(crane::get<_after_full_in_S_2>(_popped));
      _stack.pop_back();
      uint64_t d = _f.d;
      _result = tree::node(std::move(_f._tmp2), d, std::move(_result));
    }
  }
  return _result;
}

uint64_t ImmortalGlobalConstant::size(const ImmortalGlobalConstant::tree &t) {
  // Explicit stack replaces the non-tail recursion of size: _call frames are
  // pending calls, _after frames resume a caller.
  struct _call {
    const ImmortalGlobalConstant::tree *t;
  };

  struct _after_size_in_Node {
    const ImmortalGlobalConstant::tree *a2;
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
    if (crane::holds_alternative<_call>(_popped)) {
      auto _f = std::move(crane::get<_call>(_popped));
      _stack.pop_back();
      const ImmortalGlobalConstant::tree &t = *_f.t;
      if (crane::holds_alternative<typename ImmortalGlobalConstant::tree::Leaf>(
              t.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, _, a2] =
            crane::get<typename ImmortalGlobalConstant::tree::Node>(t.v());
        _stack.emplace_back(_after_size_in_Node{crane_raw(a2)});
        _stack.emplace_back(_call{crane_raw(a0)});
      }
    } else if (crane::holds_alternative<_after_size_in_Node>(_popped)) {
      auto _f = std::move(crane::get<_after_size_in_Node>(_popped));
      _stack.pop_back();
      const ImmortalGlobalConstant::tree &a2 = *_f.a2;
      _stack.emplace_back(_after_size_in_Node_2{std::move(_result)});
      _stack.emplace_back(_call{&a2});
    } else {
      auto _f = std::move(crane::get<_after_size_in_Node_2>(_popped));
      _stack.pop_back();
      _result = ((_f._tmp2 + std::move(_result)) + 1);
    }
  }
  return _result;
}

List<uint64_t> ImmortalGlobalConstant::upto(uint64_t n, List<uint64_t> acc) {
  // Loop replaces the tail recursion: each recursive call updates the loop
  // variables.
  List<uint64_t> _loop_acc = std::move(acc);
  uint64_t _loop_n = n;
  while (true) {
    if (_loop_n <= 0) {
      return _loop_acc;
    } else {
      uint64_t k = _loop_n - 1;
      uint64_t _next_n = k;
      _loop_acc = List<uint64_t>::cons(_loop_n, std::move(_loop_acc));
      _loop_n = _next_n;
    }
  }
}

/// Built at run time: counted.
ImmortalGlobalConstant::tree ImmortalGlobalConstant::fresh(uint64_t x0_) {
  return full(x0_);
}

/// A copy of the global per call.
uint64_t ImmortalGlobalConstant::sizes(uint64_t n) {
  return upto(n, List<uint64_t>::nil()).template fold_left<uint64_t>(
      [](uint64_t acc, uint64_t) { return (acc + size(table)); }, UINT64_C(0));
}
