#include "tmc_nested_ctor_wrap.h"

Nat TmcNestedCtorWrap::rsize(const TmcNestedCtorWrap::rose &r) {
  const auto &[a0] = std::get<typename TmcNestedCtorWrap::rose::Rnode>(r.v());
  const List<TmcNestedCtorWrap::rose> &a0_value = *a0;
  return Nat::s(a0_value.template fold_left<Nat>(
      [](const Nat &acc, const TmcNestedCtorWrap::rose &c) {
        return acc.add(rsize(c));
      },
      Nat::o()));
}

TmcNestedCtorWrap::rose TmcNestedCtorWrap::spine(
    const Nat
        &n) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const Nat *n;
  };

  /// _Resume_S: saves [_s0], resumes after recursive call with _result.
  struct _Resume_S {
    List<TmcNestedCtorWrap::rose> _s0;
  };

  using _Frame = std::variant<_Enter, _Resume_S>;
  TmcNestedCtorWrap::rose _result{};
  crane::small_vector<_Frame> _stack;
  _stack.emplace_back(_Enter{&n});
  /// Loopified spine: _Enter -> _Resume_S.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const Nat &n = *_f.n;
      if (std::holds_alternative<typename Nat::O>(n.v())) {
        _result = rose::rnode(List<TmcNestedCtorWrap::rose>::nil());
      } else {
        const auto &[a0] = std::get<typename Nat::S>(n.v());
        _stack.emplace_back(_Resume_S{List<TmcNestedCtorWrap::rose>::nil()});
        _stack.emplace_back(_Enter{crane_raw(a0)});
      }
    } else {
      auto _f = std::move(std::get<_Resume_S>(_frame));
      _result = rose::rnode(List<TmcNestedCtorWrap::rose>::cons(
          std::move(_result), std::move(_f._s0)));
    }
  }
  return _result;
}
