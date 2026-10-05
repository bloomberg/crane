#include "loopify_numbers.h"

/// Consolidated UNIQUE numeric algorithms - no basic arithmetic.
/// Tests loopification on number theory and recursive sequences.
uint64_t
LoopifyNumbers::factorial(uint64_t n) { /// CraneEnter: captures varying
                                        /// parameters for each recursive call.

  struct CraneEnter {
    uint64_t n;
  };

  /// CraneCont_m: saves [n], resumes after recursive call, then processes rest.
  struct CraneCont_m {
    uint64_t n;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont_m>;
  uint64_t _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{n});
  /// Loopified factorial: CraneEnter -> CraneCont_m.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      uint64_t n = _f.n;
      if (n <= 0) {
        _result = UINT64_C(1);
      } else {
        uint64_t m = n - 1;
        _stack.emplace_back(CraneCont_m{n});
        _stack.emplace_back(CraneEnter{m});
      }
    } else {
      auto _f = std::move(std::get<CraneCont_m>(_frame));
      uint64_t n = _f.n;
      _result = (n * std::move(_result));
    }
  }
  return _result;
}

uint64_t
LoopifyNumbers::fib(uint64_t n) { /// CraneEnter: captures varying parameters
                                  /// for each recursive call.

  struct CraneEnter {
    uint64_t n;
  };

  /// CraneCont_m: saves [m], resumes after recursive call, then processes rest.
  struct CraneCont_m {
    uint64_t m;
  };

  /// CraneCont_m_1: saves [_tmp2], resumes after recursive call, then processes
  /// rest.
  struct CraneCont_m_1 {
    uint64_t _tmp2;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont_m, CraneCont_m_1>;
  uint64_t _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{n});
  /// Loopified fib: CraneEnter -> CraneCont_m -> CraneCont_m_1.
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
          uint64_t m = n_ - 1;
          _stack.emplace_back(CraneCont_m{m});
          _stack.emplace_back(CraneEnter{n_});
        }
      }
    } else if (std::holds_alternative<CraneCont_m>(_frame)) {
      auto _f = std::move(std::get<CraneCont_m>(_frame));
      uint64_t m = _f.m;
      _stack.emplace_back(CraneCont_m_1{std::move(_result)});
      _stack.emplace_back(CraneEnter{m});
    } else {
      auto _f = std::move(std::get<CraneCont_m_1>(_frame));
      _result = (_f._tmp2 + std::move(_result));
    }
  }
  return _result;
}

uint64_t LoopifyNumbers::tribonacci_fuel(
    uint64_t fuel, uint64_t n) { /// CraneEnter: captures varying parameters for
                                 /// each recursive call.

  struct CraneEnter {
    uint64_t n;
    uint64_t fuel;
  };

  /// CraneCont_m: saves [f, m], resumes after recursive call, then processes
  /// rest.
  struct CraneCont_m {
    uint64_t f;
    uint64_t m;
  };

  /// CraneCont_m_1: saves [_tmp3, f, m], resumes after recursive call, then
  /// processes rest.
  struct CraneCont_m_1 {
    uint64_t _tmp3;
    uint64_t f;
    uint64_t m;
  };

  /// CraneCont_m_2: saves [_tmp2, _tmp3], resumes after recursive call, then
  /// processes rest.
  struct CraneCont_m_2 {
    uint64_t _tmp2;
    uint64_t _tmp3;
  };

  using CraneFrame =
      std::variant<CraneEnter, CraneCont_m, CraneCont_m_1, CraneCont_m_2>;
  uint64_t _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{n, fuel});
  /// Loopified tribonacci_fuel: CraneEnter -> CraneCont_m -> CraneCont_m_1 ->
  /// CraneCont_m_2.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      uint64_t n = _f.n;
      uint64_t fuel = _f.fuel;
      if (fuel <= 0) {
        _result = UINT64_C(0);
      } else {
        uint64_t f = fuel - 1;
        if (n <= 0) {
          _result = UINT64_C(0);
        } else {
          uint64_t n0 = n - 1;
          if (n0 <= 0) {
            _result = UINT64_C(0);
          } else {
            uint64_t n1 = n0 - 1;
            if (n1 <= 0) {
              _result = UINT64_C(1);
            } else {
              uint64_t m = n1 - 1;
              _stack.emplace_back(CraneCont_m{f, m});
              _stack.emplace_back(CraneEnter{((m + 1) + 1), f});
            }
          }
        }
      }
    } else if (std::holds_alternative<CraneCont_m>(_frame)) {
      auto _f = std::move(std::get<CraneCont_m>(_frame));
      uint64_t f = _f.f;
      uint64_t m = _f.m;
      _stack.emplace_back(CraneCont_m_1{std::move(_result), f, m});
      _stack.emplace_back(CraneEnter{(m + 1), f});
    } else if (std::holds_alternative<CraneCont_m_1>(_frame)) {
      auto _f = std::move(std::get<CraneCont_m_1>(_frame));
      uint64_t f = _f.f;
      uint64_t m = _f.m;
      _stack.emplace_back(CraneCont_m_2{std::move(_result), _f._tmp3});
      _stack.emplace_back(CraneEnter{m, f});
    } else {
      auto _f = std::move(std::get<CraneCont_m_2>(_frame));
      _result = (_f._tmp3 + (_f._tmp2 + std::move(_result)));
    }
  }
  return _result;
}

uint64_t LoopifyNumbers::tribonacci(uint64_t n) {
  return tribonacci_fuel(UINT64_C(100), n);
}

uint64_t LoopifyNumbers::gcd_fuel(uint64_t fuel, uint64_t a, uint64_t b) {
  uint64_t _loop_b = b;
  uint64_t _loop_a = a;
  uint64_t _loop_fuel = fuel;
  while (true) {
    if (_loop_fuel <= 0) {
      return _loop_a;
    } else {
      uint64_t f = _loop_fuel - 1;
      if (_loop_b <= 0) {
        return _loop_a;
      } else {
        uint64_t _x = _loop_b - 1;
        uint64_t _next_b = (_loop_b ? _loop_a % _loop_b : _loop_a);
        uint64_t _next_a = _loop_b;
        _loop_fuel = f;
        _loop_b = _next_b;
        _loop_a = _next_a;
      }
    }
  }
}

uint64_t LoopifyNumbers::gcd(uint64_t a, uint64_t b) {
  return gcd_fuel((a + b), a, b);
}

uint64_t
LoopifyNumbers::binomial(uint64_t n,
                         uint64_t k) { /// CraneEnter: captures varying
                                       /// parameters for each recursive call.

  struct CraneEnter {
    uint64_t k;
    uint64_t n;
  };

  /// CraneCont_k_: saves [k, n_], resumes after recursive call, then processes
  /// rest.
  struct CraneCont_k_ {
    uint64_t k;
    uint64_t n_;
  };

  /// CraneCont_k__1: saves [_tmp2], resumes after recursive call, then
  /// processes rest.
  struct CraneCont_k__1 {
    uint64_t _tmp2;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont_k_, CraneCont_k__1>;
  uint64_t _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{k, n});
  /// Loopified binomial: CraneEnter -> CraneCont_k_ -> CraneCont_k__1.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      uint64_t k = _f.k;
      uint64_t n = _f.n;
      if (n <= 0) {
        if (k <= 0) {
          _result = UINT64_C(1);
        } else {
          uint64_t _x = k - 1;
          _result = UINT64_C(0);
        }
      } else {
        uint64_t n_ = n - 1;
        if (k <= 0) {
          _result = UINT64_C(1);
        } else {
          uint64_t k_ = k - 1;
          _stack.emplace_back(CraneCont_k_{k, n_});
          _stack.emplace_back(CraneEnter{k_, n_});
        }
      }
    } else if (std::holds_alternative<CraneCont_k_>(_frame)) {
      auto _f = std::move(std::get<CraneCont_k_>(_frame));
      uint64_t k = _f.k;
      uint64_t n_ = _f.n_;
      _stack.emplace_back(CraneCont_k__1{std::move(_result)});
      _stack.emplace_back(CraneEnter{k, n_});
    } else {
      auto _f = std::move(std::get<CraneCont_k__1>(_frame));
      _result = (_f._tmp2 + std::move(_result));
    }
  }
  return _result;
}

uint64_t
LoopifyNumbers::pascal(uint64_t row,
                       uint64_t col) { /// CraneEnter: captures varying
                                       /// parameters for each recursive call.

  struct CraneEnter {
    uint64_t col;
    uint64_t row;
  };

  /// CraneCont_r: saves [c, r], resumes after recursive call, then processes
  /// rest.
  struct CraneCont_r {
    uint64_t c;
    uint64_t r;
  };

  /// CraneCont_r_1: saves [_tmp2], resumes after recursive call, then processes
  /// rest.
  struct CraneCont_r_1 {
    uint64_t _tmp2;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont_r, CraneCont_r_1>;
  uint64_t _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{col, row});
  /// Loopified pascal: CraneEnter -> CraneCont_r -> CraneCont_r_1.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      uint64_t col = _f.col;
      uint64_t row = _f.row;
      if (col <= 0) {
        _result = UINT64_C(1);
      } else {
        uint64_t c = col - 1;
        if (row <= 0) {
          _result = UINT64_C(0);
        } else {
          uint64_t r = row - 1;
          _stack.emplace_back(CraneCont_r{c, r});
          _stack.emplace_back(CraneEnter{c, r});
        }
      }
    } else if (std::holds_alternative<CraneCont_r>(_frame)) {
      auto _f = std::move(std::get<CraneCont_r>(_frame));
      uint64_t c = _f.c;
      uint64_t r = _f.r;
      _stack.emplace_back(CraneCont_r_1{std::move(_result)});
      _stack.emplace_back(CraneEnter{(c + 1), r});
    } else {
      auto _f = std::move(std::get<CraneCont_r_1>(_frame));
      _result = (_f._tmp2 + std::move(_result));
    }
  }
  return _result;
}

uint64_t LoopifyNumbers::ackermann_fuel(
    uint64_t fuel, uint64_t m,
    uint64_t n) { /// CraneEnter: captures varying parameters for each recursive
                  /// call.

  struct CraneEnter {
    uint64_t n;
    uint64_t m;
    uint64_t fuel;
  };

  /// CraneCont_n_: saves [f, m_], resumes after recursive call, then processes
  /// rest.
  struct CraneCont_n_ {
    uint64_t f;
    uint64_t m_;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont_n_>;
  uint64_t _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{n, m, fuel});
  /// Loopified ackermann_fuel: CraneEnter -> CraneCont_n_.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      uint64_t n = _f.n;
      uint64_t m = _f.m;
      uint64_t fuel = _f.fuel;
      if (fuel <= 0) {
        _result = UINT64_C(0);
      } else {
        uint64_t f = fuel - 1;
        if (m <= 0) {
          _result = (n + 1);
        } else {
          uint64_t m_ = m - 1;
          if (n <= 0) {
            _stack.emplace_back(CraneEnter{UINT64_C(1), m_, f});
          } else {
            uint64_t n_ = n - 1;
            _stack.emplace_back(CraneCont_n_{f, m_});
            _stack.emplace_back(CraneEnter{n_, m, f});
          }
        }
      }
    } else {
      auto _f = std::move(std::get<CraneCont_n_>(_frame));
      uint64_t f = _f.f;
      uint64_t m_ = _f.m_;
      _stack.emplace_back(CraneEnter{std::move(_result), m_, f});
    }
  }
  return _result;
}

uint64_t LoopifyNumbers::ack(uint64_t m, uint64_t n) {
  return ackermann_fuel(UINT64_C(1000), m, n);
}

uint64_t LoopifyNumbers::collatz_length_fuel(
    uint64_t fuel, uint64_t n) { /// CraneEnter: captures varying parameters for
                                 /// each recursive call.

  struct CraneEnter {
    uint64_t n;
    uint64_t fuel;
  };

  /// CraneCont1: resumes after recursive call, then processes rest.
  struct CraneCont1 {};

  /// CraneCont2: resumes after recursive call, then processes rest.
  struct CraneCont2 {};

  using CraneFrame = std::variant<CraneEnter, CraneCont1, CraneCont2>;
  uint64_t _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{n, fuel});
  /// Loopified collatz_length_fuel: CraneEnter -> CraneCont1 -> CraneCont2.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      uint64_t n = _f.n;
      uint64_t fuel = _f.fuel;
      if (fuel <= 0) {
        _result = UINT64_C(0);
      } else {
        uint64_t f = fuel - 1;
        if (n == UINT64_C(1)) {
          _result = UINT64_C(0);
        } else {
          if ((n % UINT64_C(2)) == UINT64_C(0)) {
            _stack.emplace_back(CraneCont1{});
            _stack.emplace_back(CraneEnter{(n / UINT64_C(2)), f});
          } else {
            _stack.emplace_back(CraneCont2{});
            _stack.emplace_back(
                CraneEnter{((UINT64_C(3) * n) + UINT64_C(1)), f});
          }
        }
      }
    } else if (std::holds_alternative<CraneCont1>(_frame)) {
      auto _f = std::move(std::get<CraneCont1>(_frame));
      _result = (std::move(_result) + 1);
    } else {
      auto _f = std::move(std::get<CraneCont2>(_frame));
      _result = (std::move(_result) + 1);
    }
  }
  return _result;
}

uint64_t LoopifyNumbers::collatz_length(uint64_t n) {
  return collatz_length_fuel(UINT64_C(1000), n);
}

uint64_t LoopifyNumbers::digitsum_fuel(
    uint64_t fuel, uint64_t n) { /// CraneEnter: captures varying parameters for
                                 /// each recursive call.

  struct CraneEnter {
    uint64_t n;
    uint64_t fuel;
  };

  /// CraneCont_px: saves [n], resumes after recursive call, then processes
  /// rest.
  struct CraneCont_px {
    uint64_t n;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont_px>;
  uint64_t _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{n, fuel});
  /// Loopified digitsum_fuel: CraneEnter -> CraneCont_px.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      uint64_t n = _f.n;
      uint64_t fuel = _f.fuel;
      if (fuel <= 0) {
        _result = UINT64_C(0);
      } else {
        uint64_t f = fuel - 1;
        if (n <= 0) {
          _result = UINT64_C(0);
        } else {
          uint64_t _x = n - 1;
          _stack.emplace_back(CraneCont_px{n});
          _stack.emplace_back(CraneEnter{(n / UINT64_C(10)), f});
        }
      }
    } else {
      auto _f = std::move(std::get<CraneCont_px>(_frame));
      uint64_t n = _f.n;
      _result = ((n % UINT64_C(10)) + std::move(_result));
    }
  }
  return _result;
}

uint64_t LoopifyNumbers::digitsum(uint64_t n) {
  return digitsum_fuel(UINT64_C(100), n);
}

uint64_t LoopifyNumbers::dec_to_bin_fuel(
    uint64_t fuel, uint64_t n) { /// CraneEnter: captures varying parameters for
                                 /// each recursive call.

  struct CraneEnter {
    uint64_t n;
    uint64_t fuel;
  };

  /// CraneCont_px: saves [digit], resumes after recursive call, then processes
  /// rest.
  struct CraneCont_px {
    uint64_t digit;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont_px>;
  uint64_t _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{n, fuel});
  /// Loopified dec_to_bin_fuel: CraneEnter -> CraneCont_px.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      uint64_t n = _f.n;
      uint64_t fuel = _f.fuel;
      if (fuel <= 0) {
        _result = UINT64_C(0);
      } else {
        uint64_t f = fuel - 1;
        if (n <= 0) {
          _result = UINT64_C(0);
        } else {
          uint64_t _x = n - 1;
          uint64_t digit = (n % UINT64_C(2));
          _stack.emplace_back(CraneCont_px{digit});
          _stack.emplace_back(CraneEnter{(n / UINT64_C(2)), f});
        }
      }
    } else {
      auto _f = std::move(std::get<CraneCont_px>(_frame));
      uint64_t digit = _f.digit;
      uint64_t rest = std::move(_result);
      _result = (digit + (UINT64_C(10) * rest));
    }
  }
  return _result;
}

uint64_t LoopifyNumbers::dec_to_bin(uint64_t n) {
  return dec_to_bin_fuel(UINT64_C(100), n);
}

uint64_t
LoopifyNumbers::sum_to(uint64_t n) { /// CraneEnter: captures varying parameters
                                     /// for each recursive call.

  struct CraneEnter {
    uint64_t n;
  };

  /// CraneCont_m: saves [n], resumes after recursive call, then processes rest.
  struct CraneCont_m {
    uint64_t n;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont_m>;
  uint64_t _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{n});
  /// Loopified sum_to: CraneEnter -> CraneCont_m.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      uint64_t n = _f.n;
      if (n <= 0) {
        _result = UINT64_C(0);
      } else {
        uint64_t m = n - 1;
        _stack.emplace_back(CraneCont_m{n});
        _stack.emplace_back(CraneEnter{m});
      }
    } else {
      auto _f = std::move(std::get<CraneCont_m>(_frame));
      uint64_t n = _f.n;
      _result = (n + std::move(_result));
    }
  }
  return _result;
}

uint64_t LoopifyNumbers::sum_squares(
    uint64_t n) { /// CraneEnter: captures varying parameters for each recursive
                  /// call.

  struct CraneEnter {
    uint64_t n;
  };

  /// CraneCont_m: saves [n], resumes after recursive call, then processes rest.
  struct CraneCont_m {
    uint64_t n;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont_m>;
  uint64_t _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{n});
  /// Loopified sum_squares: CraneEnter -> CraneCont_m.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      uint64_t n = _f.n;
      if (n <= 0) {
        _result = UINT64_C(0);
      } else {
        uint64_t m = n - 1;
        _stack.emplace_back(CraneCont_m{n});
        _stack.emplace_back(CraneEnter{m});
      }
    } else {
      auto _f = std::move(std::get<CraneCont_m>(_frame));
      uint64_t n = _f.n;
      _result = ((n * n) + std::move(_result));
    }
  }
  return _result;
}

uint64_t LoopifyNumbers::alternating_sum(bool sign, uint64_t acc, uint64_t n) {
  uint64_t _loop_n = n;
  uint64_t _loop_acc = acc;
  bool _loop_sign = sign;
  while (true) {
    if (_loop_n <= 0) {
      return _loop_acc;
    } else {
      uint64_t m = _loop_n - 1;
      uint64_t new_acc;
      if (_loop_sign) {
        new_acc = (_loop_acc + _loop_n);
      } else {
        new_acc =
            (((_loop_acc - _loop_n) > _loop_acc ? 0 : (_loop_acc - _loop_n)));
      }
      _loop_n = m;
      _loop_acc = new_acc;
      _loop_sign = !(_loop_sign);
    }
  }
}

uint64_t LoopifyNumbers::staircase_fuel(
    uint64_t fuel, uint64_t n) { /// CraneEnter: captures varying parameters for
                                 /// each recursive call.

  struct CraneEnter {
    uint64_t n;
    uint64_t fuel;
  };

  /// CraneCont_m: saves [f, m], resumes after recursive call, then processes
  /// rest.
  struct CraneCont_m {
    uint64_t f;
    uint64_t m;
  };

  /// CraneCont_m_1: saves [_tmp3, f, m], resumes after recursive call, then
  /// processes rest.
  struct CraneCont_m_1 {
    uint64_t _tmp3;
    uint64_t f;
    uint64_t m;
  };

  /// CraneCont_m_2: saves [_tmp2, _tmp3], resumes after recursive call, then
  /// processes rest.
  struct CraneCont_m_2 {
    uint64_t _tmp2;
    uint64_t _tmp3;
  };

  using CraneFrame =
      std::variant<CraneEnter, CraneCont_m, CraneCont_m_1, CraneCont_m_2>;
  uint64_t _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{n, fuel});
  /// Loopified staircase_fuel: CraneEnter -> CraneCont_m -> CraneCont_m_1 ->
  /// CraneCont_m_2.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      uint64_t n = _f.n;
      uint64_t fuel = _f.fuel;
      if (fuel <= 0) {
        _result = UINT64_C(0);
      } else {
        uint64_t f = fuel - 1;
        if (n <= 0) {
          _result = UINT64_C(1);
        } else {
          uint64_t n0 = n - 1;
          if (n0 <= 0) {
            _result = UINT64_C(1);
          } else {
            uint64_t n1 = n0 - 1;
            if (n1 <= 0) {
              _result = UINT64_C(2);
            } else {
              uint64_t m = n1 - 1;
              _stack.emplace_back(CraneCont_m{f, m});
              _stack.emplace_back(CraneEnter{((m + 1) + 1), f});
            }
          }
        }
      }
    } else if (std::holds_alternative<CraneCont_m>(_frame)) {
      auto _f = std::move(std::get<CraneCont_m>(_frame));
      uint64_t f = _f.f;
      uint64_t m = _f.m;
      _stack.emplace_back(CraneCont_m_1{std::move(_result), f, m});
      _stack.emplace_back(CraneEnter{(m + 1), f});
    } else if (std::holds_alternative<CraneCont_m_1>(_frame)) {
      auto _f = std::move(std::get<CraneCont_m_1>(_frame));
      uint64_t f = _f.f;
      uint64_t m = _f.m;
      _stack.emplace_back(CraneCont_m_2{std::move(_result), _f._tmp3});
      _stack.emplace_back(CraneEnter{m, f});
    } else {
      auto _f = std::move(std::get<CraneCont_m_2>(_frame));
      _result = (_f._tmp3 + (_f._tmp2 + std::move(_result)));
    }
  }
  return _result;
}

uint64_t LoopifyNumbers::staircase(uint64_t n) {
  return staircase_fuel(UINT64_C(100), n);
}

/// iterate_pred n applies predecessor n times, starting from n.
/// Tests church-style iteration with concrete function.
uint64_t LoopifyNumbers::iterate_pred(uint64_t n) {
  return church(
      n,
      [](uint64_t x) -> uint64_t {
        if (x <= 0) {
          return UINT64_C(0);
        } else {
          uint64_t m = x - 1;
          return m;
        }
      },
      n);
}

/// sum_while_positive n sums numbers from n down to 0, but only positive ones.
/// Tests conditional accumulation in recursion.
uint64_t LoopifyNumbers::sum_while_positive(uint64_t n) { return sum_to(n); }

/// count_down_by k n counts down from n by steps of k.
/// Tests recursion with non-standard step size.
uint64_t LoopifyNumbers::count_down_by_fuel(
    uint64_t fuel, uint64_t k,
    uint64_t n) { /// CraneEnter: captures varying parameters for each recursive
                  /// call.

  struct CraneEnter {
    uint64_t n;
    uint64_t fuel;
  };

  /// CraneCont1: resumes after recursive call, then processes rest.
  struct CraneCont1 {};

  using CraneFrame = std::variant<CraneEnter, CraneCont1>;
  uint64_t _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{n, fuel});
  /// Loopified count_down_by_fuel: CraneEnter -> CraneCont1.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      uint64_t n = _f.n;
      uint64_t fuel = _f.fuel;
      if (fuel <= 0) {
        _result = UINT64_C(0);
      } else {
        uint64_t f = fuel - 1;
        if (n <= 0) {
          _result = UINT64_C(1);
        } else {
          uint64_t _x = n - 1;
          if (n < k) {
            _result = UINT64_C(1);
          } else {
            _stack.emplace_back(CraneCont1{});
            _stack.emplace_back(CraneEnter{(n - k), f});
          }
        }
      }
    } else {
      auto _f = std::move(std::get<CraneCont1>(_frame));
      _result = (std::move(_result) + 1);
    }
  }
  return _result;
}

uint64_t LoopifyNumbers::count_down_by(uint64_t k, uint64_t n) {
  return count_down_by_fuel(UINT64_C(100), k, n);
}

/// mixed_arith n combines multiplication and addition in recursion.
uint64_t LoopifyNumbers::mixed_arith_fuel(
    uint64_t fuel, uint64_t n) { /// CraneEnter: captures varying parameters for
                                 /// each recursive call.

  struct CraneEnter {
    uint64_t n;
    uint64_t fuel;
  };

  /// CraneCont_m: saves [f, m], resumes after recursive call, then processes
  /// rest.
  struct CraneCont_m {
    uint64_t f;
    uint64_t m;
  };

  /// CraneCont_m_1: saves [_tmp3, f, m], resumes after recursive call, then
  /// processes rest.
  struct CraneCont_m_1 {
    uint64_t _tmp3;
    uint64_t f;
    uint64_t m;
  };

  /// CraneCont_m_2: saves [_tmp2, _tmp3], resumes after recursive call, then
  /// processes rest.
  struct CraneCont_m_2 {
    uint64_t _tmp2;
    uint64_t _tmp3;
  };

  using CraneFrame =
      std::variant<CraneEnter, CraneCont_m, CraneCont_m_1, CraneCont_m_2>;
  uint64_t _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{n, fuel});
  /// Loopified mixed_arith_fuel: CraneEnter -> CraneCont_m -> CraneCont_m_1 ->
  /// CraneCont_m_2.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      uint64_t n = _f.n;
      uint64_t fuel = _f.fuel;
      if (fuel <= 0) {
        _result = UINT64_C(1);
      } else {
        uint64_t f = fuel - 1;
        if (n <= 0) {
          _result = UINT64_C(1);
        } else {
          uint64_t n0 = n - 1;
          if (n0 <= 0) {
            _result = UINT64_C(1);
          } else {
            uint64_t n_ = n0 - 1;
            if (n_ <= 0) {
              _result = UINT64_C(1);
            } else {
              uint64_t m = n_ - 1;
              _stack.emplace_back(CraneCont_m{f, m});
              _stack.emplace_back(CraneEnter{n_, f});
            }
          }
        }
      }
    } else if (std::holds_alternative<CraneCont_m>(_frame)) {
      auto _f = std::move(std::get<CraneCont_m>(_frame));
      uint64_t f = _f.f;
      uint64_t m = _f.m;
      _stack.emplace_back(CraneCont_m_1{std::move(_result), f, m});
      _stack.emplace_back(CraneEnter{m, f});
    } else if (std::holds_alternative<CraneCont_m_1>(_frame)) {
      auto _f = std::move(std::get<CraneCont_m_1>(_frame));
      uint64_t f = _f.f;
      uint64_t m = _f.m;
      _stack.emplace_back(CraneCont_m_2{std::move(_result), _f._tmp3});
      _stack.emplace_back(
          CraneEnter{(m == UINT64_C(0) ? UINT64_C(0) : (m - UINT64_C(1))), f});
    } else {
      auto _f = std::move(std::get<CraneCont_m_2>(_frame));
      _result = ((_f._tmp3 * _f._tmp2) + std::move(_result));
    }
  }
  return _result;
}

uint64_t LoopifyNumbers::mixed_arith(uint64_t n) {
  return mixed_arith_fuel(UINT64_C(1000), n);
}

/// is_even n checks if n is even (mutually recursive with is_odd).
bool LoopifyNumbers::is_even_fuel(uint64_t fuel, uint64_t n) {
  uint64_t _loop_n = n;
  uint64_t _loop_fuel = fuel;
  while (true) {
    if (_loop_fuel <= 0) {
      return true;
    } else {
      uint64_t f = _loop_fuel - 1;
      if (_loop_n == UINT64_C(0)) {
        return true;
      } else {
        uint64_t _inl_n = (_loop_n - UINT64_C(1));
        uint64_t _inl_fuel = f;
        if (_inl_fuel <= 0) {
          return false;
        } else {
          uint64_t _inl_f = _inl_fuel - 1;
          if (_inl_n == UINT64_C(0)) {
            return false;
          } else {
            _loop_n = (_inl_n - UINT64_C(1));
            _loop_fuel = _inl_f;
          }
        }
      }
    }
  }
}

bool LoopifyNumbers::is_odd_fuel(uint64_t fuel, uint64_t n) {
  uint64_t _loop_n = n;
  uint64_t _loop_fuel = fuel;
  while (true) {
    if (_loop_fuel <= 0) {
      return false;
    } else {
      uint64_t f = _loop_fuel - 1;
      if (_loop_n == UINT64_C(0)) {
        return false;
      } else {
        uint64_t _inl_n = (_loop_n - UINT64_C(1));
        uint64_t _inl_fuel = f;
        if (_inl_fuel <= 0) {
          return true;
        } else {
          uint64_t _inl_f = _inl_fuel - 1;
          if (_inl_n == UINT64_C(0)) {
            return true;
          } else {
            _loop_n = (_inl_n - UINT64_C(1));
            _loop_fuel = _inl_f;
          }
        }
      }
    }
  }
}

bool LoopifyNumbers::is_even(uint64_t n) {
  return is_even_fuel(UINT64_C(1000), n);
}

bool LoopifyNumbers::is_odd(uint64_t n) {
  return is_odd_fuel(UINT64_C(1000), n);
}

/// power b e computes b^e.
uint64_t
LoopifyNumbers::power(uint64_t b,
                      uint64_t e) { /// CraneEnter: captures varying parameters
                                    /// for each recursive call.

  struct CraneEnter {
    uint64_t e;
  };

  /// CraneCont_e_: resumes after recursive call, then processes rest.
  struct CraneCont_e_ {};

  using CraneFrame = std::variant<CraneEnter, CraneCont_e_>;
  uint64_t _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{e});
  /// Loopified power: CraneEnter -> CraneCont_e_.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      uint64_t e = _f.e;
      if (e <= 0) {
        _result = UINT64_C(1);
      } else {
        uint64_t e_ = e - 1;
        _stack.emplace_back(CraneCont_e_{});
        _stack.emplace_back(CraneEnter{e_});
      }
    } else {
      auto _f = std::move(std::get<CraneCont_e_>(_frame));
      _result = (b * std::move(_result));
    }
  }
  return _result;
}

/// power_mod b e m computes (b^e) mod m efficiently.
uint64_t LoopifyNumbers::power_mod_fuel(
    uint64_t fuel, uint64_t b, uint64_t e,
    uint64_t m) { /// CraneEnter: captures varying parameters for each recursive
                  /// call.

  struct CraneEnter {
    uint64_t e;
    uint64_t fuel;
  };

  /// CraneCont1: resumes after recursive call, then processes rest.
  struct CraneCont1 {};

  /// CraneCont2: resumes after recursive call, then processes rest.
  struct CraneCont2 {};

  using CraneFrame = std::variant<CraneEnter, CraneCont1, CraneCont2>;
  uint64_t _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{e, fuel});
  /// Loopified power_mod_fuel: CraneEnter -> CraneCont1 -> CraneCont2.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      uint64_t e = _f.e;
      uint64_t fuel = _f.fuel;
      if (fuel <= 0) {
        _result = UINT64_C(0);
      } else {
        uint64_t f = fuel - 1;
        if (e == UINT64_C(0)) {
          _result = UINT64_C(1);
        } else {
          if ((e % UINT64_C(2)) == UINT64_C(0)) {
            _stack.emplace_back(CraneCont1{});
            _stack.emplace_back(CraneEnter{(e / UINT64_C(2)), f});
          } else {
            _stack.emplace_back(CraneCont2{});
            _stack.emplace_back(CraneEnter{(e / UINT64_C(2)), f});
          }
        }
      }
    } else if (std::holds_alternative<CraneCont1>(_frame)) {
      auto _f = std::move(std::get<CraneCont1>(_frame));
      uint64_t half = std::move(_result);
      auto &&_once1 = (half * half);
      _result = (m ? _once1 % m : _once1);
    } else {
      auto _f = std::move(std::get<CraneCont2>(_frame));
      uint64_t half = std::move(_result);
      auto &&_once2 = (b * (half * half));
      _result = (m ? _once2 % m : _once2);
    }
  }
  return _result;
}

uint64_t LoopifyNumbers::power_mod(uint64_t b, uint64_t e, uint64_t m) {
  return power_mod_fuel(UINT64_C(1000), b, e, m);
}

/// sum_divisors n sums all divisors of n (excluding n itself).
uint64_t LoopifyNumbers::sum_divisors_aux(
    uint64_t n, uint64_t k) { /// CraneEnter: captures varying parameters for
                              /// each recursive call.

  struct CraneEnter {
    uint64_t k;
  };

  /// CraneCont1: saves [k], resumes after recursive call, then processes rest.
  struct CraneCont1 {
    uint64_t k;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont1>;
  uint64_t _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{k});
  /// Loopified sum_divisors_aux: CraneEnter -> CraneCont1.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      uint64_t k = _f.k;
      if (k <= 0) {
        _result = UINT64_C(0);
      } else {
        uint64_t k_ = k - 1;
        if (k_ <= 0) {
          _result = UINT64_C(0);
        } else {
          uint64_t _x = k_ - 1;
          if ((k ? n % k : n) == UINT64_C(0)) {
            _stack.emplace_back(CraneCont1{k});
            _stack.emplace_back(CraneEnter{k_});
          } else {
            _stack.emplace_back(CraneEnter{k_});
          }
        }
      }
    } else {
      auto _f = std::move(std::get<CraneCont1>(_frame));
      uint64_t k = _f.k;
      _result = (k + std::move(_result));
    }
  }
  return _result;
}

uint64_t LoopifyNumbers::sum_divisors(uint64_t n) {
  if (n <= 0) {
    return UINT64_C(0);
  } else {
    uint64_t n_ = n - 1;
    if (n_ <= 0) {
      return UINT64_C(0);
    } else {
      uint64_t _x = n_ - 1;
      return sum_divisors_aux(n_, (n_ - UINT64_C(1)));
    }
  }
}

/// sum_odd_indices l and sum_even_indices l are mutually recursive.
/// sum_odd_indices adds elements at odd positions (0, 2, 4...).
/// sum_even_indices processes even positions (1, 3, 5...) by calling
/// sum_odd_indices.
uint64_t LoopifyNumbers::sum_odd_indices_fuel(
    uint64_t fuel,
    const List<uint64_t> &l) { /// CraneEnter: captures varying parameters for
                               /// each recursive call.

  struct CraneEnter {
    List<uint64_t> l;
    uint64_t fuel;
  };

  /// CraneEnter_inl: captures varying parameters for each recursive call.
  struct CraneEnter_inl {
    List<uint64_t> _inl_l;
    uint64_t _inl_fuel;
  };

  /// CraneCont_Cons: saves [a0], resumes after recursive call, then processes
  /// rest.
  struct CraneCont_Cons {
    uint64_t a0;
  };

  using CraneFrame = std::variant<CraneEnter, CraneEnter_inl, CraneCont_Cons>;
  uint64_t _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{l, fuel});
  /// Loopified sum_odd_indices_fuel: CraneEnter -> CraneCont_Cons.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      const List<uint64_t> &l = std::move(_f.l);
      uint64_t fuel = _f.fuel;
      if (fuel <= 0) {
        _result = UINT64_C(0);
      } else {
        uint64_t f = fuel - 1;
        if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
          _result = UINT64_C(0);
        } else {
          const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
          _stack.emplace_back(CraneCont_Cons{a0});
          _stack.emplace_back(CraneEnter_inl{*a1, f});
        }
      }
    } else if (std::holds_alternative<CraneEnter_inl>(_frame)) {
      auto _f = std::move(std::get<CraneEnter_inl>(_frame));
      const List<uint64_t> &_inl_l = std::move(_f._inl_l);
      uint64_t _inl_fuel = _f._inl_fuel;
      if (_inl_fuel <= 0) {
        _result = UINT64_C(0);
      } else {
        uint64_t _inl_f = _inl_fuel - 1;
        if (std::holds_alternative<typename List<uint64_t>::Nil>(_inl_l.v())) {
          _result = UINT64_C(0);
        } else {
          const auto &[_inl_a0, _inl_a1] =
              std::get<typename List<uint64_t>::Cons>(_inl_l.v());
          _stack.emplace_back(CraneEnter{*_inl_a1, _inl_f});
        }
      }
    } else {
      auto _f = std::move(std::get<CraneCont_Cons>(_frame));
      uint64_t a0 = _f.a0;
      _result = (a0 + std::move(_result));
    }
  }
  return _result;
}

uint64_t LoopifyNumbers::sum_even_indices_fuel(
    uint64_t fuel,
    const List<uint64_t> &l) { /// CraneEnter: captures varying parameters for
                               /// each recursive call.

  struct CraneEnter {
    const List<uint64_t> *l;
    uint64_t fuel;
  };

  /// CraneCont_Cons: saves [_inl_a0], resumes after recursive call, then
  /// processes rest.
  struct CraneCont_Cons {
    uint64_t _inl_a0;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont_Cons>;
  uint64_t _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{&l, fuel});
  /// Loopified sum_even_indices_fuel: CraneEnter -> CraneCont_Cons.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      const List<uint64_t> &l = *_f.l;
      uint64_t fuel = _f.fuel;
      if (fuel <= 0) {
        _result = UINT64_C(0);
      } else {
        uint64_t f = fuel - 1;
        if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
          _result = UINT64_C(0);
        } else {
          const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
          const List<uint64_t> &_inl_l = *a1;
          uint64_t _inl_fuel = f;
          if (_inl_fuel <= 0) {
            _result = UINT64_C(0);
          } else {
            uint64_t _inl_f = _inl_fuel - 1;
            if (std::holds_alternative<typename List<uint64_t>::Nil>(
                    _inl_l.v())) {
              _result = UINT64_C(0);
            } else {
              const auto &[_inl_a0, _inl_a1] =
                  std::get<typename List<uint64_t>::Cons>(_inl_l.v());
              _stack.emplace_back(CraneCont_Cons{_inl_a0});
              _stack.emplace_back(CraneEnter{crane_raw(_inl_a1), _inl_f});
            }
          }
        }
      }
    } else {
      auto _f = std::move(std::get<CraneCont_Cons>(_frame));
      uint64_t _inl_a0 = _f._inl_a0;
      uint64_t _inl_tmp1 = std::move(_result);
      _result = (_inl_a0 + _inl_tmp1);
    }
  }
  return _result;
}

uint64_t LoopifyNumbers::sum_odd_indices(const List<uint64_t> &l) {
  return sum_odd_indices_fuel(l.length(), l);
}

uint64_t LoopifyNumbers::sum_even_indices(const List<uint64_t> &l) {
  return sum_even_indices_fuel(l.length(), l);
}

/// collatz_list n generates collatz sequence as a list.
List<uint64_t> LoopifyNumbers::collatz_list_fuel(uint64_t fuel, uint64_t n) {
  std::optional<List<uint64_t>> _root{};
  std::shared_ptr<List<uint64_t>> *_write = nullptr;
  uint64_t _loop_n = n;
  uint64_t _loop_fuel = fuel;
  while (true) {
    if (_loop_fuel <= 0) {
      auto _value = List<uint64_t>::nil();
      (_write ? *(*_write = std::make_shared<List<uint64_t>>(std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      uint64_t f = _loop_fuel - 1;
      if (_loop_n == UINT64_C(1)) {
        auto _value = List<uint64_t>::cons(UINT64_C(1), List<uint64_t>::nil());
        (_write
             ? *(*_write = std::make_shared<List<uint64_t>>(std::move(_value)))
             : _root.emplace(std::move(_value)));
        break;
      } else {
        if ((_loop_n % UINT64_C(2)) == UINT64_C(0)) {
          auto _cell = typename List<uint64_t>::Cons(_loop_n, nullptr);
          List<uint64_t> &_node =
              (_write ? *(*_write = std::make_shared<List<uint64_t>>(
                              std::move(_cell)))
                      : _root.emplace(std::move(_cell)));
          _write = &std::get<typename List<uint64_t>::Cons>(_node.v_mut()).l;
          _loop_n = (_loop_n / UINT64_C(2));
          _loop_fuel = f;
          continue;
        } else {
          if ((_loop_n % UINT64_C(3)) == UINT64_C(0)) {
            auto _cell = typename List<uint64_t>::Cons(_loop_n, nullptr);
            List<uint64_t> &_node =
                (_write ? *(*_write = std::make_shared<List<uint64_t>>(
                                std::move(_cell)))
                        : _root.emplace(std::move(_cell)));
            _write = &std::get<typename List<uint64_t>::Cons>(_node.v_mut()).l;
            _loop_n = (_loop_n / UINT64_C(3));
            _loop_fuel = f;
            continue;
          } else {
            auto _cell = typename List<uint64_t>::Cons(_loop_n, nullptr);
            List<uint64_t> &_node =
                (_write ? *(*_write = std::make_shared<List<uint64_t>>(
                                std::move(_cell)))
                        : _root.emplace(std::move(_cell)));
            _write = &std::get<typename List<uint64_t>::Cons>(_node.v_mut()).l;
            _loop_n = ((UINT64_C(3) * _loop_n) + UINT64_C(1));
            _loop_fuel = f;
            continue;
          }
        }
      }
    }
  }
  return std::move(*_root);
}

List<uint64_t> LoopifyNumbers::collatz_list(uint64_t n) {
  return collatz_list_fuel(UINT64_C(1000), n);
}

/// sum_divisible_by k n sums all numbers from 1 to n divisible by k.
uint64_t LoopifyNumbers::sum_divisible_by(
    uint64_t k, uint64_t n) { /// CraneEnter: captures varying parameters for
                              /// each recursive call.

  struct CraneEnter {
    uint64_t n;
  };

  /// CraneCont1: saves [n], resumes after recursive call, then processes rest.
  struct CraneCont1 {
    uint64_t n;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont1>;
  uint64_t _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{n});
  /// Loopified sum_divisible_by: CraneEnter -> CraneCont1.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      uint64_t n = _f.n;
      if (n <= 0) {
        _result = UINT64_C(0);
      } else {
        uint64_t m = n - 1;
        if ((k ? n % k : n) == UINT64_C(0)) {
          _stack.emplace_back(CraneCont1{n});
          _stack.emplace_back(CraneEnter{m});
        } else {
          _stack.emplace_back(CraneEnter{m});
        }
      }
    } else {
      auto _f = std::move(std::get<CraneCont1>(_frame));
      uint64_t n = _f.n;
      _result = (n + std::move(_result));
    }
  }
  return _result;
}
