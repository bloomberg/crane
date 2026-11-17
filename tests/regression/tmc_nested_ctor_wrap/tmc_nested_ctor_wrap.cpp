#include "tmc_nested_ctor_wrap.h"

Nat TmcNestedCtorWrap::rsize(const TmcNestedCtorWrap::rose &r) {
  const auto &[a0] = std::get<typename TmcNestedCtorWrap::rose::Rnode>(r.v());
  const List<TmcNestedCtorWrap::rose> &a0_value = *a0;
  return Nat::s(a0_value.template fold_left<Nat>(
      [](const Nat &acc,
         const TmcNestedCtorWrap::rose &c) { return acc.add(rsize(c)); },
      Nat::o()));
}

TmcNestedCtorWrap::rose TmcNestedCtorWrap::spine(const Nat &n) {
  // Explicit stack replaces the non-tail recursion of spine: _call frames are
  // pending calls, _after frames resume a caller.
  struct _call {
    const Nat *n;
  };

  struct _after_spine_in_S {};

  using _frame = std::variant<_call, _after_spine_in_S>;
  TmcNestedCtorWrap::rose _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&n});
  while (!_stack.empty()) {
    _frame _popped = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      const Nat &n = *_f.n;
      if (std::holds_alternative<typename Nat::O>(n.v())) {
        _result = rose::rnode(List<TmcNestedCtorWrap::rose>::nil());
      } else {
        const auto &[a0] = std::get<typename Nat::S>(n.v());
        _stack.emplace_back(_after_spine_in_S{});
        _stack.emplace_back(_call{crane_raw(a0)});
      }
    } else {
      auto _f = std::move(std::get<_after_spine_in_S>(_popped));
      _result = rose::rnode(List<TmcNestedCtorWrap::rose>::cons(
          std::move(_result), List<TmcNestedCtorWrap::rose>::nil()));
    }
  }
  return _result;
}
