#include "loopify_local_fix_outer_call.h"

/// Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
/// testing of Crane: a generated program, shrunk by ephyra and reduced by hand.
///
/// Under Loopify, a structurally recursive function whose recursive call sits
/// inside a local let fix accumulator: the explicit-stack frame for the
/// local fix is built from a1, a name only declared as a frame member, so
/// the generated code does not compile.  Under CRANE_CHECK_IR=1 (the test
/// suite) extraction stops first: "moved value read: in ...g, a1 is read
/// after it is moved".
List<uint64_t> LoopifyLocalFixOuterCall::g(const List<uint64_t> &l) {
  // Explicit stack replaces the non-tail recursion of g: _call frames are
  // pending calls, _after frames resume a caller.
  struct _call {
    const List<uint64_t> *l;
  };

  struct _call_go {
    List<uint64_t> acc;
    const List<uint64_t> *m;
    std::shared_ptr<List<uint64_t>> a1;
  };

  struct _after_g_in_Cons {
    std::shared_ptr<List<uint64_t>> a1;
    uint64_t a00;
    const List<uint64_t> *a10;
  };

  using _frame = std::variant<_call, _call_go, _after_g_in_Cons>;
  List<uint64_t> _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&l});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const List<uint64_t> &l = *_f.l;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
        _result = std::move(l);
      } else {
        const auto &[_, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
        _stack.emplace_back(_call_go{List<uint64_t>::nil(), &l, a1});
      }
    } else if (std::holds_alternative<_call_go>(_popped)) {
      auto _f = std::move(std::get<_call_go>(_popped));
      _stack.pop_back();
      List<uint64_t> acc = std::move(_f.acc);
      const List<uint64_t> &m = *_f.m;
      std::shared_ptr<List<uint64_t>> a1 = std::move(_f.a1);
      if (std::holds_alternative<typename List<uint64_t>::Nil>(m.v())) {
        _result = std::move(acc);
      } else {
        const auto &[a00, a10] = std::get<typename List<uint64_t>::Cons>(m.v());
        _stack.emplace_back(_after_g_in_Cons{a1, a00, crane_raw(a10)});
        _stack.emplace_back(_call{crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<_after_g_in_Cons>(_popped));
      _stack.pop_back();
      std::shared_ptr<List<uint64_t>> a1 = std::move(_f.a1);
      uint64_t a00 = _f.a00;
      const List<uint64_t> &a10 = *_f.a10;
      _stack.emplace_back(_call_go{
          List<uint64_t>::cons(a00, std::move(_result)), &a10, std::move(a1)});
    }
  }
  return _result;
}
