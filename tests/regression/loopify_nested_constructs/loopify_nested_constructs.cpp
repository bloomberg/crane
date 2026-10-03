#include "loopify_nested_constructs.h"

uint64_t LoopifyNestedConstructs::multi_let(
    uint64_t
        n) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    uint64_t n;
  };

  /// _Cont_n_: saves [c], resumes after recursive call, then processes rest.
  struct _Cont_n_ {
    uint64_t c;
  };

  using _Frame = std::variant<_Enter, _Cont_n_>;
  uint64_t _result{};
  crane::small_vector<_Frame> _stack;
  _stack.emplace_back(_Enter{n});
  /// Loopified multi_let: _Enter -> _Cont_n_.
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
        uint64_t b = (n_ * UINT64_C(2));
        uint64_t c = (b + UINT64_C(3));
        _stack.emplace_back(_Cont_n_{c});
        _stack.emplace_back(_Enter{n_});
      }
    } else {
      auto _f = std::move(std::get<_Cont_n_>(_frame));
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
    uint64_t
        n) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    uint64_t n;
  };

  /// _Cont_n_: resumes after recursive call, then processes rest.
  struct _Cont_n_ {};

  using _Frame = std::variant<_Enter, _Cont_n_>;
  uint64_t _result{};
  crane::small_vector<_Frame> _stack;
  _stack.emplace_back(_Enter{n});
  /// Loopified deep_nest: _Enter -> _Cont_n_.
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
        _stack.emplace_back(_Cont_n_{});
        _stack.emplace_back(_Enter{n_});
      }
    } else {
      auto _f = std::move(std::get<_Cont_n_>(_frame));
      uint64_t inner = std::move(_result);
      uint64_t mid = (inner + UINT64_C(1));
      _result = (mid * UINT64_C(2));
    }
  }
  return _result;
}

uint64_t LoopifyNestedConstructs::let_nested(
    uint64_t
        n) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    uint64_t n;
  };

  /// _Cont_n_: saves [a], resumes after recursive call, then processes rest.
  struct _Cont_n_ {
    uint64_t a;
  };

  using _Frame = std::variant<_Enter, _Cont_n_>;
  uint64_t _result{};
  crane::small_vector<_Frame> _stack;
  _stack.emplace_back(_Enter{n});
  /// Loopified let_nested: _Enter -> _Cont_n_.
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
        uint64_t a = (n_ + UINT64_C(1));
        _stack.emplace_back(_Cont_n_{a});
        _stack.emplace_back(_Enter{n_});
      }
    } else {
      auto _f = std::move(std::get<_Cont_n_>(_frame));
      uint64_t a = _f.a;
      _result = (a + std::move(_result));
    }
  }
  return _result;
}

uint64_t LoopifyNestedConstructs::mod_pattern_fuel(
    uint64_t fuel,
    uint64_t
        n) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    uint64_t n;
    uint64_t fuel;
  };

  /// _Cont1: saves [n], resumes after recursive call, then processes rest.
  struct _Cont1 {
    uint64_t n;
  };

  using _Frame = std::variant<_Enter, _Cont1>;
  uint64_t _result{};
  crane::small_vector<_Frame> _stack;
  _stack.emplace_back(_Enter{n, fuel});
  /// Loopified mod_pattern_fuel: _Enter -> _Cont1.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      uint64_t n = _f.n;
      uint64_t fuel = _f.fuel;
      if (fuel <= 0) {
        _result = UINT64_C(1);
      } else {
        uint64_t fuel_ = fuel - 1;
        if (n <= UINT64_C(1)) {
          _result = UINT64_C(1);
        } else {
          _stack.emplace_back(_Cont1{n});
          _stack.emplace_back(
              _Enter{(((n - UINT64_C(1)) > n ? 0 : (n - UINT64_C(1)))), fuel_});
        }
      }
    } else {
      auto _f = std::move(std::get<_Cont1>(_frame));
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
    uint64_t
        n) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    uint64_t n;
  };

  /// _Cont_n_: saves [n], resumes after recursive call, then processes rest.
  struct _Cont_n_ {
    uint64_t n;
  };

  using _Frame = std::variant<_Enter, _Cont_n_>;
  std::pair<std::pair<uint64_t, uint64_t>, uint64_t> _result{};
  crane::small_vector<_Frame> _stack;
  _stack.emplace_back(_Enter{n});
  /// Loopified tuple_constr: _Enter -> _Cont_n_.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      uint64_t n = _f.n;
      if (n <= 0) {
        _result = std::make_pair(std::make_pair(UINT64_C(0), UINT64_C(0)),
                                 UINT64_C(0));
      } else {
        uint64_t n_ = n - 1;
        _stack.emplace_back(_Cont_n_{n});
        _stack.emplace_back(_Enter{n_});
      }
    } else {
      auto _f = std::move(std::get<_Cont_n_>(_frame));
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
    uint64_t
        n) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    uint64_t n;
  };

  /// _Cont1: saves [n], resumes after recursive call, then processes rest.
  struct _Cont1 {
    uint64_t n;
  };

  /// _Cont2: saves [n], resumes after recursive call, then processes rest.
  struct _Cont2 {
    uint64_t n;
  };

  using _Frame = std::variant<_Enter, _Cont1, _Cont2>;
  uint64_t _result{};
  crane::small_vector<_Frame> _stack;
  _stack.emplace_back(_Enter{n});
  /// Loopified alternating_ops: _Enter -> _Cont1 -> _Cont2.
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
        if ((UINT64_C(2) ? n % UINT64_C(2) : n) == UINT64_C(0)) {
          _stack.emplace_back(_Cont1{n});
          _stack.emplace_back(_Enter{n_});
        } else {
          _stack.emplace_back(_Cont2{n});
          _stack.emplace_back(_Enter{n_});
        }
      }
    } else if (std::holds_alternative<_Cont1>(_frame)) {
      auto _f = std::move(std::get<_Cont1>(_frame));
      uint64_t n = _f.n;
      _result = (n + std::move(_result));
    } else {
      auto _f = std::move(std::get<_Cont2>(_frame));
      uint64_t n = _f.n;
      _result = ((n * UINT64_C(2)) + std::move(_result));
    }
  }
  return _result;
}

bool LoopifyNestedConstructs::chained_comp_fuel(
    uint64_t fuel,
    uint64_t
        n) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    uint64_t n;
    uint64_t fuel;
  };

  /// _Cont1: saves [fuel_, n], resumes after recursive call, then processes
  /// rest.
  struct _Cont1 {
    uint64_t fuel_;
    uint64_t n;
  };

  /// _Cont2: saves [_tmp2], resumes after recursive call, then processes rest.
  struct _Cont2 {
    bool _tmp2;
  };

  using _Frame = std::variant<_Enter, _Cont1, _Cont2>;
  bool _result{};
  crane::small_vector<_Frame> _stack;
  _stack.emplace_back(_Enter{n, fuel});
  /// Loopified chained_comp_fuel: _Enter -> _Cont1 -> _Cont2.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      uint64_t n = _f.n;
      uint64_t fuel = _f.fuel;
      if (fuel <= 0) {
        _result = true;
      } else {
        uint64_t fuel_ = fuel - 1;
        if (n <= UINT64_C(2)) {
          _result = true;
        } else {
          _stack.emplace_back(_Cont1{fuel_, n});
          _stack.emplace_back(
              _Enter{(((n - UINT64_C(1)) > n ? 0 : (n - UINT64_C(1)))), fuel_});
        }
      }
    } else if (std::holds_alternative<_Cont1>(_frame)) {
      auto _f = std::move(std::get<_Cont1>(_frame));
      uint64_t fuel_ = _f.fuel_;
      uint64_t n = _f.n;
      _stack.emplace_back(_Cont2{std::move(_result)});
      _stack.emplace_back(
          _Enter{(((n - UINT64_C(2)) > n ? 0 : (n - UINT64_C(2)))), fuel_});
    } else {
      auto _f = std::move(std::get<_Cont2>(_frame));
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
    uint64_t
        n) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    uint64_t n;
  };

  /// _Cont_n__: saves [n__], resumes after recursive call, then processes rest.
  struct _Cont_n__ {
    uint64_t n__;
  };

  /// _Cont_n___1: saves [x], resumes after recursive call, then processes rest.
  struct _Cont_n___1 {
    uint64_t x;
  };

  using _Frame = std::variant<_Enter, _Cont_n__, _Cont_n___1>;
  uint64_t _result{};
  crane::small_vector<_Frame> _stack;
  _stack.emplace_back(_Enter{n});
  /// Loopified compute_with_lets: _Enter -> _Cont_n__ -> _Cont_n___1.
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
          _stack.emplace_back(_Cont_n__{n__});
          _stack.emplace_back(_Enter{n_});
        }
      }
    } else if (std::holds_alternative<_Cont_n__>(_frame)) {
      auto _f = std::move(std::get<_Cont_n__>(_frame));
      uint64_t n__ = _f.n__;
      uint64_t x = std::move(_result);
      _stack.emplace_back(_Cont_n___1{x});
      _stack.emplace_back(_Enter{n__});
    } else {
      auto _f = std::move(std::get<_Cont_n___1>(_frame));
      uint64_t x = _f.x;
      uint64_t y = std::move(_result);
      uint64_t z = (x + y);
      _result = (z * UINT64_C(2));
    }
  }
  return _result;
}

uint64_t LoopifyNestedConstructs::nested_match(
    uint64_t
        n) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    uint64_t n;
  };

  /// _Cont_n__: saves [n], resumes after recursive call, then processes rest.
  struct _Cont_n__ {
    uint64_t n;
  };

  using _Frame = std::variant<_Enter, _Cont_n__>;
  uint64_t _result{};
  crane::small_vector<_Frame> _stack;
  _stack.emplace_back(_Enter{n});
  /// Loopified nested_match: _Enter -> _Cont_n__.
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
          _stack.emplace_back(_Cont_n__{n});
          _stack.emplace_back(_Enter{n__});
        }
      }
    } else {
      auto _f = std::move(std::get<_Cont_n__>(_frame));
      uint64_t n = _f.n;
      _result = (n + std::move(_result));
    }
  }
  return _result;
}
