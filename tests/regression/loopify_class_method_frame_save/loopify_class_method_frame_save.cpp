#include "loopify_class_method_frame_save.h"

/// Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
/// testing of Crane: a generated program, shrunk by ephyra and reduced by hand.
///
/// Under Loopify, a non-tail recursive call passed to a type-class method
/// (Nat.leb 1 (sz (g r))) fails the ownership check under CRANE_CHECK_IR=1
/// (the test suite's setting): "frame save: a frame save the plan decides
/// keeps a local the C++ reading would move".  Without the check the C++ is
/// right.
bool LoopifyClassMethodFrameSave::g(const List<uint64_t> &l) {
  // Explicit stack replaces the non-tail recursion of g: _call frames are
  // pending calls, _after frames resume a caller.
  struct _call {
    const List<uint64_t> *l;
  };

  struct _after_g_in_Cons {
    crane::fn<uint64_t(bool)> sz0;
  };

  using _frame = std::variant<_call, _after_g_in_Cons>;
  bool _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&l});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const List<uint64_t> &l = *_f.l;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
        _result = true;
      } else {
        const auto &[_, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
        crane::fn<uint64_t(bool)> sz0 = sz_bool::sz;
        _stack.emplace_back(_after_g_in_Cons{std::move(sz0)});
        _stack.emplace_back(_call{crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<_after_g_in_Cons>(_popped));
      _stack.pop_back();
      crane::fn<uint64_t(bool)> sz0 = std::move(_f.sz0);
      _result = UINT64_C(1) <= sz0(std::move(_result));
    }
  }
  return _result;
}

uint64_t LoopifyClassMethodFrameSave::h(uint64_t n) {
  // Explicit stack replaces the non-tail recursion of h: _call frames are
  // pending calls, _after frames resume a caller.
  struct _call {
    uint64_t n;
  };

  struct _after_h_in_S {
    crane::fn<uint64_t(uint64_t)> sz0;
    crane::fn<uint64_t(uint64_t)> sz1;
  };

  using _frame = std::variant<_call, _after_h_in_S>;
  uint64_t _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{n});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      uint64_t n = _f.n;
      if (n <= 0) {
        _result = UINT64_C(0);
      } else {
        uint64_t m = n - 1;
        crane::fn<uint64_t(uint64_t)> sz0 = sz_nat::sz;
        crane::fn<uint64_t(uint64_t)> sz1 = sz_nat::sz;
        _stack.emplace_back(_after_h_in_S{std::move(sz0), std::move(sz1)});
        _stack.emplace_back(_call{m});
      }
    } else {
      auto _f = std::move(std::get<_after_h_in_S>(_popped));
      _stack.pop_back();
      crane::fn<uint64_t(uint64_t)> sz0 = std::move(_f.sz0);
      crane::fn<uint64_t(uint64_t)> sz1 = std::move(_f.sz1);
      _result = sz0(sz1(std::move(_result)));
    }
  }
  return _result;
}
