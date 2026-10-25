#include "loopification_quicksort_bug.h"

List<uint64_t> QuicksortFun::quicksort_fun(
    const List<uint64_t> &x) { /// CraneEnter: captures varying parameters for
                               /// each recursive call.

  struct CraneEnter {
    List<uint64_t> x;
  };

  /// CraneCont_Cons: saves [a0, a1], resumes after recursive call, then
  /// processes rest.
  struct CraneCont_Cons {
    uint64_t a0;
    std::shared_ptr<List<uint64_t>> a1;
  };

  /// CraneCont_Cons_1: saves [a0, _tmp2], resumes after recursive call, then
  /// processes rest.
  struct CraneCont_Cons_1 {
    uint64_t a0;
    List<uint64_t> _tmp2;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont_Cons, CraneCont_Cons_1>;
  List<uint64_t> _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{x});
  /// Loopified quicksort_fun: CraneEnter -> CraneCont_Cons -> CraneCont_Cons_1.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      const List<uint64_t> &x = std::move(_f.x);
      if (std::holds_alternative<typename List<uint64_t>::Nil>(x.v())) {
        _result = List<uint64_t>::nil();
      } else {
        const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(x.v());
        const List<uint64_t> &a1_value = *a1;
        _stack.emplace_back(CraneCont_Cons{a0, a1});
        _stack.emplace_back(
            CraneEnter{a1_value.filter([=](uint64_t x0) { return x0 < a0; })});
      }
    } else if (std::holds_alternative<CraneCont_Cons>(_frame)) {
      auto _f = std::move(std::get<CraneCont_Cons>(_frame));
      uint64_t a0 = _f.a0;
      std::shared_ptr<List<uint64_t>> a1 = std::move(_f.a1);
      const List<uint64_t> &a1_value = *a1;
      _stack.emplace_back(CraneCont_Cons_1{a0, std::move(_result)});
      _stack.emplace_back(
          CraneEnter{a1_value.filter([=](uint64_t x0) { return a0 <= x0; })});
    } else {
      auto _f = std::move(std::get<CraneCont_Cons_1>(_frame));
      uint64_t a0 = _f.a0;
      _result = _f._tmp2.app(List<uint64_t>::cons(a0, List<uint64_t>::nil())
                                 .app(std::move(_result)));
    }
  }
  return _result;
}

std::string QuicksortFun::list_to_string_helper(
    const List<uint64_t> &l) { /// CraneEnter: captures varying parameters for
                               /// each recursive call.

  struct CraneEnter {
    const List<uint64_t> *l;
  };

  /// CraneCont_Cons: saves [a0], resumes after recursive call, then processes
  /// rest.
  struct CraneCont_Cons {
    uint64_t a0;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont_Cons>;
  std::string _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{&l});
  /// Loopified list_to_string_helper: CraneEnter -> CraneCont_Cons.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      const List<uint64_t> &l = *_f.l;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
        _result = "";
      } else {
        const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
        _stack.emplace_back(CraneCont_Cons{a0});
        _stack.emplace_back(CraneEnter{crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<CraneCont_Cons>(_frame));
      uint64_t a0 = _f.a0;
      _result = std::to_string(a0) + std::string(", ") + std::move(_result);
    }
  }
  return _result;
}

std::string QuicksortFun::list_to_string(const List<uint64_t> &l) {
  return std::string("[ ") + list_to_string_helper(l) + std::string(" ]");
}

std::string QuicksortFun::test_quicksort_fun(std::monostate) {
  List<uint64_t> out = quicksort_fun(input_lst1);
  return list_to_string(std::move(out));
}
