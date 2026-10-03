#include "loopification_quicksort_bug.h"

List<uint64_t> QuicksortFun::quicksort_fun(
    const List<uint64_t>
        &x) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    List<uint64_t> x;
  };

  using _Frame = std::variant<_Enter>;
  List<uint64_t> _result{};
  crane::small_vector<_Frame> _stack;
  _stack.emplace_back(_Enter{x});
  /// Loopified quicksort_fun: _Enter.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    auto _f = std::move(std::get<_Enter>(_frame));
    const List<uint64_t> &x = std::move(_f.x);
    _result = quicksort_fun_functional(
        x, [](const List<uint64_t> &y) { return quicksort_fun(y); });
  }
  return _result;
}

std::string QuicksortFun::list_to_string_helper(
    const List<uint64_t>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<uint64_t> *l;
  };

  /// _Cont_Cons: saves [a0], resumes after recursive call, then processes rest.
  struct _Cont_Cons {
    uint64_t a0;
  };

  using _Frame = std::variant<_Enter, _Cont_Cons>;
  std::string _result{};
  crane::small_vector<_Frame> _stack;
  _stack.emplace_back(_Enter{&l});
  /// Loopified list_to_string_helper: _Enter -> _Cont_Cons.
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
        _stack.emplace_back(_Cont_Cons{a0});
        _stack.emplace_back(_Enter{crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<_Cont_Cons>(_frame));
      uint64_t a0 = _f.a0;
      _result = std::to_string(a0) + ", "s + std::move(_result);
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
