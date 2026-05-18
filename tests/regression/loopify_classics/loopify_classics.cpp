#include "loopify_classics.h"

uint64_t
LoopifyClassics::factorial(uint64_t n) { /// _Enter: captures varying parameters
                                         /// for each recursive call.

  struct _Enter {
    uint64_t n;
  };

  /// _Resume_n_: saves [n], resumes after recursive call with _result.
  struct _Resume_n_ {
    uint64_t n;
  };

  using _Frame = std::variant<_Enter, _Resume_n_>;
  uint64_t _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{n});
  /// Loopified factorial: _Enter -> _Resume_n_.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      uint64_t n = _f.n;
      if (n <= 0) {
        _result = UINT64_C(1);
      } else {
        uint64_t n_ = n - 1;
        _stack.emplace_back(_Resume_n_{n});
        _stack.emplace_back(_Enter{n_});
      }
    } else {
      auto _f = std::move(std::get<_Resume_n_>(_frame));
      _result = (_f.n * _result);
    }
  }
  return _result;
}

uint64_t
LoopifyClassics::fib(uint64_t n) { /// _Enter: captures varying parameters for
                                   /// each recursive call.

  struct _Enter {
    uint64_t n;
  };

  /// _After_n__: saves [n_], dispatches next recursive call.
  struct _After_n__ {
    uint64_t n_;
  };

  /// _Combine_n__: receives partial results, combines with _result from final
  /// call.
  struct _Combine_n__ {
    uint64_t _result;
  };

  using _Frame = std::variant<_Enter, _After_n__, _Combine_n__>;
  uint64_t _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{n});
  /// Loopified fib: _Enter -> _After_n__ -> _Combine_n__.
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
        if (n_ <= 0) {
          _result = UINT64_C(1);
        } else {
          uint64_t n__ = n_ - 1;
          _stack.emplace_back(_After_n__{n_});
          _stack.emplace_back(_Enter{n__});
        }
      }
    } else if (std::holds_alternative<_After_n__>(_frame)) {
      auto _f = std::move(std::get<_After_n__>(_frame));
      _stack.emplace_back(_Combine_n__{_result});
      _stack.emplace_back(_Enter{_f.n_});
    } else {
      auto _f = std::move(std::get<_Combine_n__>(_frame));
      _result = (std::move(_result) + std::move(_f._result));
    }
  }
  return _result;
}

uint64_t
LoopifyClassics::ack_fuel(uint64_t fuel, uint64_t m,
                          uint64_t n) { /// _Enter: captures varying parameters
                                        /// for each recursive call.

  struct _Enter {
    uint64_t n;
    uint64_t m;
    uint64_t fuel;
  };

  /// _Cont1: saves [fuel_, m], resumes after recursive call, then processes
  /// rest.
  struct _Cont1 {
    uint64_t fuel_;
    uint64_t m;
  };

  using _Frame = std::variant<_Enter, _Cont1>;
  uint64_t _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{n, m, fuel});
  /// Loopified ack_fuel: _Enter -> _Cont1.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      uint64_t n = _f.n;
      uint64_t m = _f.m;
      uint64_t fuel = _f.fuel;
      if (fuel <= 0) {
        _result = (n + UINT64_C(1));
      } else {
        uint64_t fuel_ = fuel - 1;
        if (m == UINT64_C(0)) {
          _result = (n + UINT64_C(1));
        } else {
          if (n == UINT64_C(0)) {
            _stack.emplace_back(_Enter{
                UINT64_C(1), (((m - UINT64_C(1)) > m ? 0 : (m - UINT64_C(1)))),
                fuel_});
          } else {
            _stack.emplace_back(_Cont1{fuel_, m});
            _stack.emplace_back(_Enter{
                (((n - UINT64_C(1)) > n ? 0 : (n - UINT64_C(1)))), m, fuel_});
          }
        }
      }
    } else {
      auto _f = std::move(std::get<_Cont1>(_frame));
      uint64_t fuel_ = _f.fuel_;
      uint64_t m = _f.m;
      uint64_t inner = _result;
      _stack.emplace_back(_Enter{
          inner, (((m - UINT64_C(1)) > m ? 0 : (m - UINT64_C(1)))), fuel_});
    }
  }
  return _result;
}

uint64_t LoopifyClassics::ack(uint64_t m, uint64_t n) {
  return ack_fuel(((UINT64_C(100) * (m + UINT64_C(1))) * (n + UINT64_C(1))), m,
                  n);
}

uint64_t LoopifyClassics::binomial_fuel(
    uint64_t fuel, uint64_t n,
    uint64_t
        k) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    uint64_t k;
    uint64_t n;
    uint64_t fuel;
  };

  /// _After2: saves [_s0, _s1, fuel_], dispatches next recursive call.
  struct _After2 {
    decltype((
        ((std::declval<uint64_t &>() - UINT64_C(1)) > std::declval<uint64_t &>()
             ? 0
             : (std::declval<uint64_t &>() - UINT64_C(1))))) _s0;
    decltype((
        ((std::declval<uint64_t &>() - UINT64_C(1)) > std::declval<uint64_t &>()
             ? 0
             : (std::declval<uint64_t &>() - UINT64_C(1))))) _s1;
    uint64_t fuel_;
  };

  /// _Combine1: receives partial results, combines with _result from final
  /// call.
  struct _Combine1 {
    uint64_t _result;
  };

  using _Frame = std::variant<_Enter, _After2, _Combine1>;
  uint64_t _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{k, n, fuel});
  /// Loopified binomial_fuel: _Enter -> _After2 -> _Combine1.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      uint64_t k = _f.k;
      uint64_t n = _f.n;
      uint64_t fuel = _f.fuel;
      if (fuel <= 0) {
        _result = UINT64_C(1);
      } else {
        uint64_t fuel_ = fuel - 1;
        if ((k == UINT64_C(0) || k == n)) {
          _result = UINT64_C(1);
        } else {
          _stack.emplace_back(_After2{
              (((k - UINT64_C(1)) > k ? 0 : (k - UINT64_C(1)))),
              (((n - UINT64_C(1)) > n ? 0 : (n - UINT64_C(1)))), fuel_});
          _stack.emplace_back(_Enter{
              k, (((n - UINT64_C(1)) > n ? 0 : (n - UINT64_C(1)))), fuel_});
        }
      }
    } else if (std::holds_alternative<_After2>(_frame)) {
      auto _f = std::move(std::get<_After2>(_frame));
      _stack.emplace_back(_Combine1{_result});
      _stack.emplace_back(_Enter{_f._s0, _f._s1, _f.fuel_});
    } else {
      auto _f = std::move(std::get<_Combine1>(_frame));
      _result = (std::move(_result) + std::move(_f._result));
    }
  }
  return _result;
}

uint64_t LoopifyClassics::binomial(uint64_t n, uint64_t k) {
  return binomial_fuel((n * k), n, k);
}

uint64_t LoopifyClassics::pascal_fuel(
    uint64_t fuel, uint64_t row,
    uint64_t
        col) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    uint64_t col;
    uint64_t row;
    uint64_t fuel;
  };

  /// _After2: saves [_s0, _s1, fuel_], dispatches next recursive call.
  struct _After2 {
    decltype((
        ((std::declval<uint64_t &>() - UINT64_C(1)) > std::declval<uint64_t &>()
             ? 0
             : (std::declval<uint64_t &>() - UINT64_C(1))))) _s0;
    decltype((
        ((std::declval<uint64_t &>() - UINT64_C(1)) > std::declval<uint64_t &>()
             ? 0
             : (std::declval<uint64_t &>() - UINT64_C(1))))) _s1;
    uint64_t fuel_;
  };

  /// _Combine1: receives partial results, combines with _result from final
  /// call.
  struct _Combine1 {
    uint64_t _result;
  };

  using _Frame = std::variant<_Enter, _After2, _Combine1>;
  uint64_t _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{col, row, fuel});
  /// Loopified pascal_fuel: _Enter -> _After2 -> _Combine1.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      uint64_t col = _f.col;
      uint64_t row = _f.row;
      uint64_t fuel = _f.fuel;
      if (fuel <= 0) {
        _result = UINT64_C(1);
      } else {
        uint64_t fuel_ = fuel - 1;
        if ((col == UINT64_C(0) || col == row)) {
          _result = UINT64_C(1);
        } else {
          _stack.emplace_back(_After2{
              (((col - UINT64_C(1)) > col ? 0 : (col - UINT64_C(1)))),
              (((row - UINT64_C(1)) > row ? 0 : (row - UINT64_C(1)))), fuel_});
          _stack.emplace_back(_Enter{
              col, (((row - UINT64_C(1)) > row ? 0 : (row - UINT64_C(1)))),
              fuel_});
        }
      }
    } else if (std::holds_alternative<_After2>(_frame)) {
      auto _f = std::move(std::get<_After2>(_frame));
      _stack.emplace_back(_Combine1{_result});
      _stack.emplace_back(_Enter{_f._s0, _f._s1, _f.fuel_});
    } else {
      auto _f = std::move(std::get<_Combine1>(_frame));
      _result = (std::move(_result) + std::move(_f._result));
    }
  }
  return _result;
}

uint64_t LoopifyClassics::pascal(uint64_t row, uint64_t col) {
  return pascal_fuel((row * col), row, col);
}

uint64_t LoopifyClassics::gcd_fuel(uint64_t fuel, uint64_t a, uint64_t b) {
  uint64_t _loop_b = std::move(b);
  uint64_t _loop_a = std::move(a);
  uint64_t _loop_fuel = std::move(fuel);
  while (true) {
    if (_loop_fuel <= 0) {
      return _loop_a;
    } else {
      uint64_t fuel_ = _loop_fuel - 1;
      if (_loop_b == UINT64_C(0)) {
        return _loop_a;
      } else {
        uint64_t _next_b = (_loop_b ? _loop_a % _loop_b : _loop_a);
        uint64_t _next_a = _loop_b;
        _loop_fuel = fuel_;
        _loop_b = _next_b;
        _loop_a = _next_a;
      }
    }
  }
}

uint64_t LoopifyClassics::gcd(uint64_t a, uint64_t b) {
  return gcd_fuel((a + b), a, b);
}

uint64_t
LoopifyClassics::power(uint64_t base,
                       uint64_t exp) { /// _Enter: captures varying parameters
                                       /// for each recursive call.

  struct _Enter {
    uint64_t exp;
  };

  /// _Resume_exp_: saves [base], resumes after recursive call with _result.
  struct _Resume_exp_ {
    uint64_t base;
  };

  using _Frame = std::variant<_Enter, _Resume_exp_>;
  uint64_t _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{exp});
  /// Loopified power: _Enter -> _Resume_exp_.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      uint64_t exp = _f.exp;
      if (exp <= 0) {
        _result = UINT64_C(1);
      } else {
        uint64_t exp_ = exp - 1;
        _stack.emplace_back(_Resume_exp_{base});
        _stack.emplace_back(_Enter{exp_});
      }
    } else {
      auto _f = std::move(std::get<_Resume_exp_>(_frame));
      _result = (_f.base * _result);
    }
  }
  return _result;
}

uint64_t
LoopifyClassics::sum_to(uint64_t n) { /// _Enter: captures varying parameters
                                      /// for each recursive call.

  struct _Enter {
    uint64_t n;
  };

  /// _Resume_n_: saves [n], resumes after recursive call with _result.
  struct _Resume_n_ {
    uint64_t n;
  };

  using _Frame = std::variant<_Enter, _Resume_n_>;
  uint64_t _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{n});
  /// Loopified sum_to: _Enter -> _Resume_n_.
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
        _stack.emplace_back(_Resume_n_{n});
        _stack.emplace_back(_Enter{n_});
      }
    } else {
      auto _f = std::move(std::get<_Resume_n_>(_frame));
      _result = (_f.n + _result);
    }
  }
  return _result;
}

uint64_t LoopifyClassics::sum_squares(
    uint64_t
        n) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    uint64_t n;
  };

  /// _Resume_n_: saves [_s0], resumes after recursive call with _result.
  struct _Resume_n_ {
    uint64_t _s0;
  };

  using _Frame = std::variant<_Enter, _Resume_n_>;
  uint64_t _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{n});
  /// Loopified sum_squares: _Enter -> _Resume_n_.
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
        _stack.emplace_back(_Resume_n_{(n * n)});
        _stack.emplace_back(_Enter{n_});
      }
    } else {
      auto _f = std::move(std::get<_Resume_n_>(_frame));
      _result = (_f._s0 + _result);
    }
  }
  return _result;
}
