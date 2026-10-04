#include "perceus_reuse_loopify.h"

R::lst R::rev_append1(const R::lst &l, R::lst acc) {
  R::lst _loop_acc = std::move(acc);
  const R::lst *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<typename R::lst::Nil>(_loop_l->v())) {
      return _loop_acc;
    } else {
      const auto &[a0, a1] = std::get<typename R::lst::Cons>(_loop_l->v());
      _loop_acc = lst::cons(a0, std::move(_loop_acc));
      _loop_l = crane_raw(a1);
    }
  }
}

R::lst R::rev1(const R::lst &l) { return rev_append1(l, lst::nil()); }

uint64_t R::sum1(const R::lst &l) { /// CraneEnter: captures varying parameters
                                    /// for each recursive call.

  struct CraneEnter {
    const R::lst *l;
  };

  /// CraneCont_Cons: saves [a0], resumes after recursive call, then processes
  /// rest.
  struct CraneCont_Cons {
    uint64_t a0;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont_Cons>;
  uint64_t _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{&l});
  /// Loopified sum1: CraneEnter -> CraneCont_Cons.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      const R::lst &l = *_f.l;
      if (std::holds_alternative<typename R::lst::Nil>(l.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] = std::get<typename R::lst::Cons>(l.v());
        _stack.emplace_back(CraneCont_Cons{a0});
        _stack.emplace_back(CraneEnter{crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<CraneCont_Cons>(_frame));
      uint64_t a0 = _f.a0;
      _result = (a0 + std::move(_result));
    }
  }
  return _result;
}
