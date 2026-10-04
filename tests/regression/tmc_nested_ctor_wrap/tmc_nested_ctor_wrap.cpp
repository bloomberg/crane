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

TmcNestedCtorWrap::rose
TmcNestedCtorWrap::spine(const Nat &n) { /// CraneEnter: captures varying
                                         /// parameters for each recursive call.

  struct CraneEnter {
    const Nat *n;
  };

  /// CraneCont_S: resumes after recursive call, then processes rest.
  struct CraneCont_S {};

  using CraneFrame = std::variant<CraneEnter, CraneCont_S>;
  TmcNestedCtorWrap::rose _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{&n});
  /// Loopified spine: CraneEnter -> CraneCont_S.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      const Nat &n = *_f.n;
      if (std::holds_alternative<typename Nat::O>(n.v())) {
        _result = rose::rnode(List<TmcNestedCtorWrap::rose>::nil());
      } else {
        const auto &[a0] = std::get<typename Nat::S>(n.v());
        _stack.emplace_back(CraneCont_S{});
        _stack.emplace_back(CraneEnter{crane_raw(a0)});
      }
    } else {
      auto _f = std::move(std::get<CraneCont_S>(_frame));
      _result = rose::rnode(List<TmcNestedCtorWrap::rose>::cons(
          std::move(_result), List<TmcNestedCtorWrap::rose>::nil()));
    }
  }
  return _result;
}
