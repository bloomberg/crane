#include "loopify_numeric_misc.h"

uint64_t LoopifyNumericMisc::sum_abs(
    const List<uint64_t>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<uint64_t> *l;
  };

  /// _Resume_Cons: saves [a0], resumes after recursive call with _result.
  struct _Resume_Cons {
    uint64_t a0;
  };

  using _Frame = std::variant<_Enter, _Resume_Cons>;
  uint64_t _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l});
  /// Loopified sum_abs: _Enter -> _Resume_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<uint64_t> &l = *_f.l;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
        _stack.emplace_back(_Resume_Cons{a0});
        _stack.emplace_back(_Enter{a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Resume_Cons>(_frame));
      _result = (_f.a0 + std::move(_result));
    }
  }
  return _result;
}

uint64_t LoopifyNumericMisc::alternating_ops(
    uint64_t
        n) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    uint64_t n;
  };

  /// _Resume1: saves [n_], resumes after recursive call with _result.
  struct _Resume1 {
    std::decay_t<decltype((std::declval<uint64_t &>() + 1))> n_;
  };

  /// _Resume2: saves [_s0], resumes after recursive call with _result.
  struct _Resume2 {
    std::decay_t<decltype(((std::declval<uint64_t &>() + 1) * UINT64_C(2)))>
        _s0;
  };

  using _Frame = std::variant<_Enter, _Resume1, _Resume2>;
  uint64_t _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{n});
  /// Loopified alternating_ops: _Enter -> _Resume1 -> _Resume2.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      uint64_t n = _f.n;
      if (n <= 0) {
        _result = UINT64_C(0);
      } else {
        uint64_t n_ = n - 1;
        if ((UINT64_C(2) ? (n_ + 1) % UINT64_C(2) : (n_ + 1)) == UINT64_C(0)) {
          _stack.emplace_back(_Resume1{(n_ + 1)});
          _stack.emplace_back(_Enter{n_});
        } else {
          _stack.emplace_back(_Resume2{((n_ + 1) * UINT64_C(2))});
          _stack.emplace_back(_Enter{n_});
        }
      }
    } else if (std::holds_alternative<_Resume1>(_frame)) {
      auto _f = std::move(std::get<_Resume1>(_frame));
      _result = (_f.n_ + std::move(_result));
    } else {
      auto _f = std::move(std::get<_Resume2>(_frame));
      _result = (_f._s0 + std::move(_result));
    }
  }
  return _result;
}

uint64_t LoopifyNumericMisc::count_even(
    const List<uint64_t>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<uint64_t> *l;
  };

  /// _Resume1: saves [_s0], resumes after recursive call with _result.
  struct _Resume1 {
    std::decay_t<decltype(UINT64_C(1))> _s0;
  };

  using _Frame = std::variant<_Enter, _Resume1>;
  uint64_t _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l});
  /// Loopified count_even: _Enter -> _Resume1.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<uint64_t> &l = *_f.l;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
        if ((UINT64_C(2) ? a0 % UINT64_C(2) : a0) == UINT64_C(0)) {
          _stack.emplace_back(_Resume1{UINT64_C(1)});
          _stack.emplace_back(_Enter{a1.get()});
        } else {
          _stack.emplace_back(_Enter{a1.get()});
        }
      }
    } else {
      auto _f = std::move(std::get<_Resume1>(_frame));
      _result = (_f._s0 + std::move(_result));
    }
  }
  return _result;
}

uint64_t LoopifyNumericMisc::count_odd(
    const List<uint64_t>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<uint64_t> *l;
  };

  /// _Resume1: saves [_s0], resumes after recursive call with _result.
  struct _Resume1 {
    std::decay_t<decltype(UINT64_C(1))> _s0;
  };

  using _Frame = std::variant<_Enter, _Resume1>;
  uint64_t _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l});
  /// Loopified count_odd: _Enter -> _Resume1.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<uint64_t> &l = *_f.l;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
        if ((UINT64_C(2) ? a0 % UINT64_C(2) : a0) == UINT64_C(1)) {
          _stack.emplace_back(_Resume1{UINT64_C(1)});
          _stack.emplace_back(_Enter{a1.get()});
        } else {
          _stack.emplace_back(_Enter{a1.get()});
        }
      }
    } else {
      auto _f = std::move(std::get<_Resume1>(_frame));
      _result = (_f._s0 + std::move(_result));
    }
  }
  return _result;
}

uint64_t LoopifyNumericMisc::product(
    const List<uint64_t>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<uint64_t> *l;
  };

  /// _Resume_Cons: saves [a0], resumes after recursive call with _result.
  struct _Resume_Cons {
    uint64_t a0;
  };

  using _Frame = std::variant<_Enter, _Resume_Cons>;
  uint64_t _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l});
  /// Loopified product: _Enter -> _Resume_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<uint64_t> &l = *_f.l;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
        _result = UINT64_C(1);
      } else {
        const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
        _stack.emplace_back(_Resume_Cons{a0});
        _stack.emplace_back(_Enter{a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Resume_Cons>(_frame));
      _result = (_f.a0 * std::move(_result));
    }
  }
  return _result;
}

uint64_t LoopifyNumericMisc::sum_of_squares(
    const List<uint64_t>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<uint64_t> *l;
  };

  /// _Resume_Cons: saves [_s0], resumes after recursive call with _result.
  struct _Resume_Cons {
    uint64_t _s0;
  };

  using _Frame = std::variant<_Enter, _Resume_Cons>;
  uint64_t _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l});
  /// Loopified sum_of_squares: _Enter -> _Resume_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<uint64_t> &l = *_f.l;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
        _stack.emplace_back(_Resume_Cons{(a0 * a0)});
        _stack.emplace_back(_Enter{a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Resume_Cons>(_frame));
      _result = (_f._s0 + std::move(_result));
    }
  }
  return _result;
}

uint64_t LoopifyNumericMisc::max_two(uint64_t a, uint64_t b) {
  if (a < b) {
    return b;
  } else {
    return a;
  }
}

uint64_t LoopifyNumericMisc::list_max(
    const List<uint64_t>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<uint64_t> *l;
  };

  /// _Resume_Cons: saves [a0], resumes after recursive call with _result.
  struct _Resume_Cons {
    uint64_t a0;
  };

  using _Frame = std::variant<_Enter, _Resume_Cons>;
  uint64_t _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l});
  /// Loopified list_max: _Enter -> _Resume_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<uint64_t> &l = *_f.l;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
        auto &&_sv = *a1;
        if (std::holds_alternative<typename List<uint64_t>::Nil>(_sv.v())) {
          _result = std::move(a0);
        } else {
          _stack.emplace_back(_Resume_Cons{a0});
          _stack.emplace_back(_Enter{a1.get()});
        }
      }
    } else {
      auto _f = std::move(std::get<_Resume_Cons>(_frame));
      _result = max_two(_f.a0, std::move(_result));
    }
  }
  return _result;
}

uint64_t LoopifyNumericMisc::list_min(
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
  uint64_t _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l});
  /// Loopified list_min: _Enter -> _Cont_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<uint64_t> &l = *_f.l;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
        auto &&_sv = *a1;
        if (std::holds_alternative<typename List<uint64_t>::Nil>(_sv.v())) {
          _result = std::move(a0);
        } else {
          _stack.emplace_back(_Cont_Cons{a0});
          _stack.emplace_back(_Enter{a1.get()});
        }
      }
    } else {
      auto _f = std::move(std::get<_Cont_Cons>(_frame));
      uint64_t a0 = _f.a0;
      uint64_t min_rest = std::move(_result);
      if (a0 < min_rest) {
        _result = std::move(a0);
      } else {
        _result = std::move(min_rest);
      }
    }
  }
  return _result;
}
