#include "loopify_nested_constructs.h"

uint64_t LoopifyNestedConstructs::multi_let(
    uint64_t n) { /// CraneEnter: captures varying parameters for each recursive
                  /// call.

  struct CraneEnter {
    uint64_t n;
  };

  /// CraneCont_n_: saves [c], resumes after recursive call, then processes
  /// rest.
  struct CraneCont_n_ {
    uint64_t c;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont_n_>;
  uint64_t _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{n});
  /// Loopified multi_let: CraneEnter -> CraneCont_n_.
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
        uint64_t b = (n_ * UINT64_C(2));
        uint64_t c = (b + UINT64_C(3));
        _stack.emplace_back(CraneCont_n_{c});
        _stack.emplace_back(CraneEnter{n_});
      }
    } else {
      auto _f = std::move(std::get<CraneCont_n_>(_frame));
      uint64_t c = _f.c;
      _result = (c + std::move(_result));
    }
  }
  return _result;
}

uint64_t LoopifyNestedConstructs::nested_if_fuel(uint64_t fuel, uint64_t n) {
  uint64_t _loop_n = std::move(n);
  uint64_t _loop_fuel = std::move(fuel);
  while (true) {
    if (_loop_fuel <= 0) {
      return UINT64_C(0);
    } else {
      uint64_t fuel_ = _loop_fuel - 1;
      if (_loop_n <= UINT64_C(0)) {
        return UINT64_C(0);
      } else {
        if (_loop_n == UINT64_C(1)) {
          return UINT64_C(1);
        } else {
          if ((UINT64_C(2) ? _loop_n % UINT64_C(2) : _loop_n) == UINT64_C(0)) {
            if (UINT64_C(10) < _loop_n) {
              _loop_n = (UINT64_C(2) ? _loop_n / UINT64_C(2) : 0);
              _loop_fuel = fuel_;
            } else {
              _loop_n = (((_loop_n - UINT64_C(1)) > _loop_n
                              ? 0
                              : (_loop_n - UINT64_C(1))));
              _loop_fuel = fuel_;
            }
          } else {
            _loop_n =
                (((_loop_n - UINT64_C(2)) > _loop_n ? 0
                                                    : (_loop_n - UINT64_C(2))));
            _loop_fuel = fuel_;
          }
        }
      }
    }
  }
}

uint64_t LoopifyNestedConstructs::nested_if(uint64_t n) {
  return nested_if_fuel(n, n);
}

uint64_t LoopifyNestedConstructs::deep_nest(
    uint64_t n) { /// CraneEnter: captures varying parameters for each recursive
                  /// call.

  struct CraneEnter {
    uint64_t n;
  };

  /// CraneCont_n_: resumes after recursive call, then processes rest.
  struct CraneCont_n_ {};

  using CraneFrame = std::variant<CraneEnter, CraneCont_n_>;
  uint64_t _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{n});
  /// Loopified deep_nest: CraneEnter -> CraneCont_n_.
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
        _stack.emplace_back(CraneCont_n_{});
        _stack.emplace_back(CraneEnter{n_});
      }
    } else {
      auto _f = std::move(std::get<CraneCont_n_>(_frame));
      uint64_t inner = std::move(_result);
      uint64_t mid = (inner + UINT64_C(1));
      _result = (mid * UINT64_C(2));
    }
  }
  return _result;
}

uint64_t LoopifyNestedConstructs::let_nested(
    uint64_t n) { /// CraneEnter: captures varying parameters for each recursive
                  /// call.

  struct CraneEnter {
    uint64_t n;
  };

  /// CraneCont_n_: saves [a], resumes after recursive call, then processes
  /// rest.
  struct CraneCont_n_ {
    uint64_t a;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont_n_>;
  uint64_t _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{n});
  /// Loopified let_nested: CraneEnter -> CraneCont_n_.
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
        uint64_t a = (n_ + UINT64_C(1));
        _stack.emplace_back(CraneCont_n_{a});
        _stack.emplace_back(CraneEnter{n_});
      }
    } else {
      auto _f = std::move(std::get<CraneCont_n_>(_frame));
      uint64_t a = _f.a;
      _result = (a + std::move(_result));
    }
  }
  return _result;
}

uint64_t LoopifyNestedConstructs::mod_pattern_fuel(
    uint64_t fuel, uint64_t n) { /// CraneEnter: captures varying parameters for
                                 /// each recursive call.

  struct CraneEnter {
    uint64_t n;
    uint64_t fuel;
  };

  /// CraneCont1: saves [n], resumes after recursive call, then processes rest.
  struct CraneCont1 {
    uint64_t n;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont1>;
  uint64_t _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{n, fuel});
  /// Loopified mod_pattern_fuel: CraneEnter -> CraneCont1.
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
        uint64_t fuel_ = fuel - 1;
        if (n <= UINT64_C(1)) {
          _result = UINT64_C(1);
        } else {
          _stack.emplace_back(CraneCont1{n});
          _stack.emplace_back(CraneEnter{
              (((n - UINT64_C(1)) > n ? 0 : (n - UINT64_C(1)))), fuel_});
        }
      }
    } else {
      auto _f = std::move(std::get<CraneCont1>(_frame));
      uint64_t n = _f.n;
      _result = ((UINT64_C(1) + std::move(_result))
                     ? n % (UINT64_C(1) + std::move(_result))
                     : n);
    }
  }
  return _result;
}

uint64_t LoopifyNestedConstructs::mod_pattern(uint64_t n) {
  return mod_pattern_fuel(n, n);
}

std::pair<std::pair<uint64_t, uint64_t>, uint64_t>
LoopifyNestedConstructs::tuple_constr(
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
  std::pair<std::pair<uint64_t, uint64_t>, uint64_t> _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{n});
  /// Loopified tuple_constr: CraneEnter -> CraneCont_n_.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      uint64_t n = _f.n;
      if (n <= 0) {
        _result = std::make_pair(std::make_pair(UINT64_C(0), UINT64_C(0)),
                                 UINT64_C(0));
      } else {
        uint64_t n_ = n - 1;
        _stack.emplace_back(CraneCont_n_{n});
        _stack.emplace_back(CraneEnter{n_});
      }
    } else {
      auto _f = std::move(std::get<CraneCont_n_>(_frame));
      uint64_t n = _f.n;
      auto [p, c] = std::move(_result);
      auto [a, b] = std::move(p);
      _result = std::make_pair(std::make_pair((a + UINT64_C(1)), (b + n)),
                               (c + (n * n)));
    }
  }
  return _result;
}

uint64_t LoopifyNestedConstructs::alternating_ops(
    uint64_t n) { /// CraneEnter: captures varying parameters for each recursive
                  /// call.

  struct CraneEnter {
    uint64_t n;
  };

  /// CraneCont1: saves [n], resumes after recursive call, then processes rest.
  struct CraneCont1 {
    uint64_t n;
  };

  /// CraneCont2: saves [n], resumes after recursive call, then processes rest.
  struct CraneCont2 {
    uint64_t n;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont1, CraneCont2>;
  uint64_t _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{n});
  /// Loopified alternating_ops: CraneEnter -> CraneCont1 -> CraneCont2.
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
        if ((UINT64_C(2) ? n % UINT64_C(2) : n) == UINT64_C(0)) {
          _stack.emplace_back(CraneCont1{n});
          _stack.emplace_back(CraneEnter{n_});
        } else {
          _stack.emplace_back(CraneCont2{n});
          _stack.emplace_back(CraneEnter{n_});
        }
      }
    } else if (std::holds_alternative<CraneCont1>(_frame)) {
      auto _f = std::move(std::get<CraneCont1>(_frame));
      uint64_t n = _f.n;
      _result = (n + std::move(_result));
    } else {
      auto _f = std::move(std::get<CraneCont2>(_frame));
      uint64_t n = _f.n;
      _result = ((n * UINT64_C(2)) + std::move(_result));
    }
  }
  return _result;
}

bool LoopifyNestedConstructs::chained_comp_fuel(
    uint64_t fuel, uint64_t n) { /// CraneEnter: captures varying parameters for
                                 /// each recursive call.

  struct CraneEnter {
    uint64_t n;
    uint64_t fuel;
  };

  /// CraneCont1: saves [fuel_, n], resumes after recursive call, then processes
  /// rest.
  struct CraneCont1 {
    uint64_t fuel_;
    uint64_t n;
  };

  /// CraneCont2: saves [_tmp2], resumes after recursive call, then processes
  /// rest.
  struct CraneCont2 {
    bool _tmp2;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont1, CraneCont2>;
  bool _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{n, fuel});
  /// Loopified chained_comp_fuel: CraneEnter -> CraneCont1 -> CraneCont2.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      uint64_t n = _f.n;
      uint64_t fuel = _f.fuel;
      if (fuel <= 0) {
        _result = true;
      } else {
        uint64_t fuel_ = fuel - 1;
        if (n <= UINT64_C(2)) {
          _result = true;
        } else {
          _stack.emplace_back(CraneCont1{fuel_, n});
          _stack.emplace_back(CraneEnter{
              (((n - UINT64_C(1)) > n ? 0 : (n - UINT64_C(1)))), fuel_});
        }
      }
    } else if (std::holds_alternative<CraneCont1>(_frame)) {
      auto _f = std::move(std::get<CraneCont1>(_frame));
      uint64_t fuel_ = _f.fuel_;
      uint64_t n = _f.n;
      _stack.emplace_back(CraneCont2{std::move(_result)});
      _stack.emplace_back(
          CraneEnter{(((n - UINT64_C(2)) > n ? 0 : (n - UINT64_C(2)))), fuel_});
    } else {
      auto _f = std::move(std::get<CraneCont2>(_frame));
      _result = (_f._tmp2 && std::move(_result));
    }
  }
  return _result;
}

uint64_t LoopifyNestedConstructs::chained_comp(uint64_t n) {
  if (chained_comp_fuel((n * UINT64_C(2)), n)) {
    return UINT64_C(1);
  } else {
    return UINT64_C(0);
  }
}

uint64_t LoopifyNestedConstructs::compute_with_lets(
    uint64_t n) { /// CraneEnter: captures varying parameters for each recursive
                  /// call.

  struct CraneEnter {
    uint64_t n;
  };

  /// CraneCont_n_p: saves [n_p], resumes after recursive call, then processes
  /// rest.
  struct CraneCont_n_p {
    uint64_t n_p;
  };

  /// CraneCont_n_p_1: saves [x], resumes after recursive call, then processes
  /// rest.
  struct CraneCont_n_p_1 {
    uint64_t x;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont_n_p, CraneCont_n_p_1>;
  uint64_t _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{n});
  /// Loopified compute_with_lets: CraneEnter -> CraneCont_n_p ->
  /// CraneCont_n_p_1.
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
      uint64_t x = std::move(_result);
      _stack.emplace_back(CraneCont_n_p_1{x});
      _stack.emplace_back(CraneEnter{n_p});
    } else {
      auto _f = std::move(std::get<CraneCont_n_p_1>(_frame));
      uint64_t x = _f.x;
      uint64_t y = std::move(_result);
      uint64_t z = (x + y);
      _result = (z * UINT64_C(2));
    }
  }
  return _result;
}

uint64_t LoopifyNestedConstructs::nested_match(
    uint64_t n) { /// CraneEnter: captures varying parameters for each recursive
                  /// call.

  struct CraneEnter {
    uint64_t n;
  };

  /// CraneCont_n_p: saves [n], resumes after recursive call, then processes
  /// rest.
  struct CraneCont_n_p {
    uint64_t n;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont_n_p>;
  uint64_t _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{n});
  /// Loopified nested_match: CraneEnter -> CraneCont_n_p.
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
          _stack.emplace_back(CraneCont_n_p{n});
          _stack.emplace_back(CraneEnter{n_p});
        }
      }
    } else {
      auto _f = std::move(std::get<CraneCont_n_p>(_frame));
      uint64_t n = _f.n;
      _result = (n + std::move(_result));
    }
  }
  return _result;
}
