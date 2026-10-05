#include "loopify_classics.h"

uint64_t
LoopifyClassics::factorial(uint64_t n) { /// CraneEnter: captures varying
                                         /// parameters for each recursive call.

  struct CraneEnter {
    uint64_t n;
  };

  /// CraneCont_n_: saves [n], resumes after recursive call, then processes
  /// rest.
  struct CraneCont_n_ {
    uint64_t n;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont_n_>;
  uint64_t _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{n});
  /// Loopified factorial: CraneEnter -> CraneCont_n_.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      uint64_t n = _f.n;
      if (n <= 0) {
        _result = UINT64_C(1);
      } else {
        uint64_t n_ = n - 1;
        _stack.emplace_back(CraneCont_n_{n});
        _stack.emplace_back(CraneEnter{n_});
      }
    } else {
      auto _f = std::move(std::get<CraneCont_n_>(_frame));
      uint64_t n = _f.n;
      _result = (n * std::move(_result));
    }
  }
  return _result;
}

uint64_t
LoopifyClassics::fib(uint64_t n) { /// CraneEnter: captures varying parameters
                                   /// for each recursive call.

  struct CraneEnter {
    uint64_t n;
  };

  /// CraneCont_n_p: saves [n_p], resumes after recursive call, then processes
  /// rest.
  struct CraneCont_n_p {
    uint64_t n_p;
  };

  /// CraneCont_n_p_1: saves [_tmp2], resumes after recursive call, then
  /// processes rest.
  struct CraneCont_n_p_1 {
    uint64_t _tmp2;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont_n_p, CraneCont_n_p_1>;
  uint64_t _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{n});
  /// Loopified fib: CraneEnter -> CraneCont_n_p -> CraneCont_n_p_1.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      uint64_t n = _f.n;
      if (n <= 0) {
        _result = UINT64_C(0);
      } else {
        uint64_t n_ = n - 1;
        if (n_ <= 0) {
          _result = UINT64_C(1);
        } else {
          uint64_t n_p = n_ - 1;
          _stack.emplace_back(CraneCont_n_p{n_p});
          _stack.emplace_back(CraneEnter{n_});
        }
      }
    } else if (std::holds_alternative<CraneCont_n_p>(_frame)) {
      auto _f = std::move(std::get<CraneCont_n_p>(_frame));
      uint64_t n_p = _f.n_p;
      _stack.emplace_back(CraneCont_n_p_1{std::move(_result)});
      _stack.emplace_back(CraneEnter{n_p});
    } else {
      auto _f = std::move(std::get<CraneCont_n_p_1>(_frame));
      _result = (_f._tmp2 + std::move(_result));
    }
  }
  return _result;
}

uint64_t
LoopifyClassics::ack_fuel(uint64_t fuel, uint64_t m,
                          uint64_t n) { /// CraneEnter: captures varying
                                        /// parameters for each recursive call.

  struct CraneEnter {
    uint64_t n;
    uint64_t m;
    uint64_t fuel;
  };

  /// CraneCont1: saves [fuel_, m], resumes after recursive call, then processes
  /// rest.
  struct CraneCont1 {
    uint64_t fuel_;
    uint64_t m;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont1>;
  uint64_t _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{n, m, fuel});
  /// Loopified ack_fuel: CraneEnter -> CraneCont1.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
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
            _stack.emplace_back(CraneEnter{
                UINT64_C(1), (((m - UINT64_C(1)) > m ? 0 : (m - UINT64_C(1)))),
                fuel_});
          } else {
            _stack.emplace_back(CraneCont1{fuel_, m});
            _stack.emplace_back(CraneEnter{
                (((n - UINT64_C(1)) > n ? 0 : (n - UINT64_C(1)))), m, fuel_});
          }
        }
      }
    } else {
      auto _f = std::move(std::get<CraneCont1>(_frame));
      uint64_t fuel_ = _f.fuel_;
      uint64_t m = _f.m;
      uint64_t inner = std::move(_result);
      _stack.emplace_back(CraneEnter{
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
    uint64_t k) { /// CraneEnter: captures varying parameters for each recursive
                  /// call.

  struct CraneEnter {
    uint64_t k;
    uint64_t n;
    uint64_t fuel;
  };

  /// CraneCont1: saves [fuel_, k, n], resumes after recursive call, then
  /// processes rest.
  struct CraneCont1 {
    uint64_t fuel_;
    uint64_t k;
    uint64_t n;
  };

  /// CraneCont2: saves [_tmp2], resumes after recursive call, then processes
  /// rest.
  struct CraneCont2 {
    uint64_t _tmp2;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont1, CraneCont2>;
  uint64_t _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{k, n, fuel});
  /// Loopified binomial_fuel: CraneEnter -> CraneCont1 -> CraneCont2.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
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
          _stack.emplace_back(CraneCont1{fuel_, k, n});
          _stack.emplace_back(CraneEnter{
              (((k - UINT64_C(1)) > k ? 0 : (k - UINT64_C(1)))),
              (((n - UINT64_C(1)) > n ? 0 : (n - UINT64_C(1)))), fuel_});
        }
      }
    } else if (std::holds_alternative<CraneCont1>(_frame)) {
      auto _f = std::move(std::get<CraneCont1>(_frame));
      uint64_t fuel_ = _f.fuel_;
      uint64_t k = _f.k;
      uint64_t n = _f.n;
      _stack.emplace_back(CraneCont2{std::move(_result)});
      _stack.emplace_back(CraneEnter{
          k, (((n - UINT64_C(1)) > n ? 0 : (n - UINT64_C(1)))), fuel_});
    } else {
      auto _f = std::move(std::get<CraneCont2>(_frame));
      _result = (_f._tmp2 + std::move(_result));
    }
  }
  return _result;
}

uint64_t LoopifyClassics::binomial(uint64_t n, uint64_t k) {
  return binomial_fuel((n * k), n, k);
}

uint64_t LoopifyClassics::pascal_fuel(uint64_t fuel, uint64_t row,
                                      uint64_t col) {
  return binomial_fuel(fuel, row, col);
}

uint64_t LoopifyClassics::pascal(uint64_t row, uint64_t col) {
  return pascal_fuel((row * col), row, col);
}

uint64_t LoopifyClassics::gcd_fuel(uint64_t fuel, uint64_t a, uint64_t b) {
  uint64_t _loop_b = b;
  uint64_t _loop_a = a;
  uint64_t _loop_fuel = fuel;
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
                       uint64_t exp) { /// CraneEnter: captures varying
                                       /// parameters for each recursive call.

  struct CraneEnter {
    uint64_t exp;
  };

  /// CraneCont_exp_: resumes after recursive call, then processes rest.
  struct CraneCont_exp_ {};

  using CraneFrame = std::variant<CraneEnter, CraneCont_exp_>;
  uint64_t _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{exp});
  /// Loopified power: CraneEnter -> CraneCont_exp_.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      uint64_t exp = _f.exp;
      if (exp <= 0) {
        _result = UINT64_C(1);
      } else {
        uint64_t exp_ = exp - 1;
        _stack.emplace_back(CraneCont_exp_{});
        _stack.emplace_back(CraneEnter{exp_});
      }
    } else {
      auto _f = std::move(std::get<CraneCont_exp_>(_frame));
      _result = (base * std::move(_result));
    }
  }
  return _result;
}

uint64_t
LoopifyClassics::sum_to(uint64_t n) { /// CraneEnter: captures varying
                                      /// parameters for each recursive call.

  struct CraneEnter {
    uint64_t n;
  };

  /// CraneCont_n_: saves [n], resumes after recursive call, then processes
  /// rest.
  struct CraneCont_n_ {
    uint64_t n;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont_n_>;
  uint64_t _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{n});
  /// Loopified sum_to: CraneEnter -> CraneCont_n_.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      uint64_t n = _f.n;
      if (n <= 0) {
        _result = UINT64_C(0);
      } else {
        uint64_t n_ = n - 1;
        _stack.emplace_back(CraneCont_n_{n});
        _stack.emplace_back(CraneEnter{n_});
      }
    } else {
      auto _f = std::move(std::get<CraneCont_n_>(_frame));
      uint64_t n = _f.n;
      _result = (n + std::move(_result));
    }
  }
  return _result;
}

uint64_t LoopifyClassics::sum_squares(
    uint64_t n) { /// CraneEnter: captures varying parameters for each recursive
                  /// call.

  struct CraneEnter {
    uint64_t n;
  };

  /// CraneCont_n_: saves [n], resumes after recursive call, then processes
  /// rest.
  struct CraneCont_n_ {
    uint64_t n;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont_n_>;
  uint64_t _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{n});
  /// Loopified sum_squares: CraneEnter -> CraneCont_n_.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      uint64_t n = _f.n;
      if (n <= 0) {
        _result = UINT64_C(0);
      } else {
        uint64_t n_ = n - 1;
        _stack.emplace_back(CraneCont_n_{n});
        _stack.emplace_back(CraneEnter{n_});
      }
    } else {
      auto _f = std::move(std::get<CraneCont_n_>(_frame));
      uint64_t n = _f.n;
      _result = ((n * n) + std::move(_result));
    }
  }
  return _result;
}
