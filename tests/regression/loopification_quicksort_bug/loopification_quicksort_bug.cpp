#include "loopification_quicksort_bug.h"

List<uint64_t> QuicksortFun::quicksort_fun(
    const List<uint64_t>
        &x) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    List<uint64_t> x;
  };

  /// _After_Cons: saves [_s0, _s1], dispatches next recursive call.
  struct _After_Cons {
    List<uint64_t> _s0;
    std::decay_t<decltype(List<uint64_t>::cons(std::declval<uint64_t &>(),
                                               List<uint64_t>::nil()))>
        _s1;
  };

  /// _Combine_Cons: receives partial results, combines with _result from final
  /// call.
  struct _Combine_Cons {
    List<uint64_t> _result;
    std::decay_t<decltype(List<uint64_t>::cons(std::declval<uint64_t &>(),
                                               List<uint64_t>::nil()))>
        _s1;
  };

  using _Frame = std::variant<_Enter, _After_Cons, _Combine_Cons>;
  List<uint64_t> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{x});
  /// Loopified quicksort_fun: _Enter -> _After_Cons -> _Combine_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<uint64_t> &x = std::move(_f.x);
      const List<uint64_t> &_inl_l = x;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(_inl_l.v())) {
        _result = List<uint64_t>::nil();
      } else {
        const auto &[_inl_a0, _inl_a1] =
            std::get<typename List<uint64_t>::Cons>(_inl_l.v());
        const List<uint64_t> &_inl_a1_value = *_inl_a1;
        _stack.emplace_back(_After_Cons{
            std::move(_inl_a1_value.filter(
                [=](uint64_t _inl_x) mutable { return _inl_x < _inl_a0; })),
            List<uint64_t>::cons(_inl_a0, List<uint64_t>::nil())});
        _stack.emplace_back(_Enter{_inl_a1_value.filter(
            [=](uint64_t _inl_x) mutable { return _inl_a0 <= _inl_x; })});
      }
    } else if (std::holds_alternative<_After_Cons>(_frame)) {
      auto _f = std::move(std::get<_After_Cons>(_frame));
      _stack.emplace_back(_Combine_Cons{std::move(_result), _f._s1});
      _stack.emplace_back(_Enter{std::move(_f._s0)});
    } else {
      auto _f = std::move(std::get<_Combine_Cons>(_frame));
      _result = std::move(_result).app(_f._s1.app(std::move(_f._result)));
    }
  }
  return _result;
}

std::string QuicksortFun::list_to_string_helper(
    const List<uint64_t>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<uint64_t> *l;
  };

  /// _Resume_Cons: saves [a0, _s1], resumes after recursive call with _result.
  struct _Resume_Cons {
    std::decay_t<decltype(std::to_string(std::declval<uint64_t &>()))> a0;
    std::decay_t<decltype(", ")> _s1;
  };

  using _Frame = std::variant<_Enter, _Resume_Cons>;
  std::string _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l});
  /// Loopified list_to_string_helper: _Enter -> _Resume_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<uint64_t> &l = *_f.l;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
        _result = "";
      } else {
        const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
        _stack.emplace_back(_Resume_Cons{std::to_string(a0), ", "});
        _stack.emplace_back(_Enter{a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Resume_Cons>(_frame));
      _result = _f.a0 + _f._s1 + std::move(_result);
    }
  }
  return _result;
}

std::string QuicksortFun::list_to_string(const List<uint64_t> &l) {
  return "[ "s + list_to_string_helper(l) + " ]"s;
}

std::string QuicksortFun::test_quicksort_fun(std::monostate) {
  List<uint64_t> out = quicksort_fun(input_lst1);
  return list_to_string(std::move(out));
}
