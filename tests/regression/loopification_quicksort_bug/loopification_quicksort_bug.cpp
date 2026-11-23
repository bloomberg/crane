#include "loopification_quicksort_bug.h"

List<uint64_t> QuicksortFun::quicksort_fun(const List<uint64_t> &x) {
  // Explicit stack replaces the non-tail recursion of quicksort_fun: _call
  // frames are pending calls, _after frames resume a caller.
  struct _call {
    List<uint64_t> x;
  };

  struct _after_quicksort_fun_in_Cons {
    uint64_t a0;
    std::shared_ptr<List<uint64_t>> a1;
  };

  struct _after_quicksort_fun_in_Cons_2 {
    uint64_t a0;
    List<uint64_t> _tmp2;
  };

  using _frame = std::variant<_call, _after_quicksort_fun_in_Cons,
                              _after_quicksort_fun_in_Cons_2>;
  List<uint64_t> _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{x});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const List<uint64_t> &x = _f.x;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(x.v())) {
        _result = List<uint64_t>::nil();
      } else {
        const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(x.v());
        const List<uint64_t> &a1_value = *a1;
        _stack.emplace_back(_after_quicksort_fun_in_Cons{a0, a1});
        _stack.emplace_back(_call{a1_value.filter(
            [=, a0 = std::move(a0)](uint64_t x0) { return x0 < a0; })});
      }
    } else if (std::holds_alternative<_after_quicksort_fun_in_Cons>(_popped)) {
      auto _f = std::move(std::get<_after_quicksort_fun_in_Cons>(_popped));
      _stack.pop_back();
      uint64_t a0 = _f.a0;
      std::shared_ptr<List<uint64_t>> a1 = std::move(_f.a1);
      const List<uint64_t> &a1_value = *a1;
      _stack.emplace_back(
          _after_quicksort_fun_in_Cons_2{a0, std::move(_result)});
      _stack.emplace_back(_call{a1_value.filter(
          [=, a0 = std::move(a0)](uint64_t x0) { return a0 <= x0; })});
    } else {
      auto _f = std::move(std::get<_after_quicksort_fun_in_Cons_2>(_popped));
      _stack.pop_back();
      uint64_t a0 = _f.a0;
      _result = _f._tmp2.app(List<uint64_t>::cons(std::move(a0),
                                                  List<uint64_t>::nil())
                                 .app(std::move(_result)));
    }
  }
  return _result;
}

std::string QuicksortFun::list_to_string_helper(const List<uint64_t> &l) {
  // Explicit stack replaces the non-tail recursion of list_to_string_helper:
  // _call frames are pending calls, _after frames resume a caller.
  struct _call {
    const List<uint64_t> *l;
  };

  struct _after_list_to_string_helper_in_Cons {
    uint64_t a0;
  };

  using _frame = std::variant<_call, _after_list_to_string_helper_in_Cons>;
  std::string _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&l});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const List<uint64_t> &l = *_f.l;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
        _result = "";
      } else {
        const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
        _stack.emplace_back(_after_list_to_string_helper_in_Cons{a0});
        _stack.emplace_back(_call{crane_raw(a1)});
      }
    } else {
      auto _f =
          std::move(std::get<_after_list_to_string_helper_in_Cons>(_popped));
      _stack.pop_back();
      uint64_t a0 = _f.a0;
      _result = crane::string_capped(
          std::to_string(a0) +
          crane::string_capped(std::string(", ") + std::move(_result)));
    }
  }
  return _result;
}

std::string QuicksortFun::list_to_string(const List<uint64_t> &l) {
  return crane::string_capped(
      std::string("[ ") +
      crane::string_capped(list_to_string_helper(l) + std::string(" ]")));
}

std::string QuicksortFun::test_quicksort_fun() {
  List<uint64_t> out = quicksort_fun(input_lst1);
  return list_to_string(std::move(out));
}
