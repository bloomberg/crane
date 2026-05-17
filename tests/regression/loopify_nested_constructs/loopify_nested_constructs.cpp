#include "loopify_nested_constructs.h"

uint64_t LoopifyNestedConstructs::multi_let(
    uint64_t
        n) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    uint64_t n;
  };

  /// _Resume_n_: saves [c], resumes after recursive call with _result.
  struct _Resume_n_ {
    uint64_t c;
  };

  using _Frame = std::variant<_Enter, _Resume_n_>;
  uint64_t _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{n});
  /// Loopified multi_let: _Enter -> _Resume_n_.
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
        _stack.emplace_back(_Resume_n_{c});
        _stack.emplace_back(_Enter{n_});
      }
    } else {
      auto _f = std::move(std::get<_Resume_n_>(_frame));
      _result = (_f.c + _result);
    }
  }
  return _result;
}

uint64_t LoopifyNestedConstructs::nested_if_fuel(uint64_t fuel, uint64_t n) {
  uint64_t _result;
  uint64_t _loop_n = std::move(n);
  uint64_t _loop_fuel = std::move(fuel);
  while (true) {
    if (_loop_fuel <= 0) {
      _result = UINT64_C(0);
      break;
    } else {
      uint64_t fuel_ = _loop_fuel - 1;
      if (_loop_n <= UINT64_C(0)) {
        _result = UINT64_C(0);
        break;
      } else {
        if (_loop_n == UINT64_C(1)) {
          _result = UINT64_C(1);
          break;
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
  return _result;
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
  std::vector<_Frame> _stack;
  _stack.reserve(8);
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
      uint64_t inner = _result;
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

  /// _Resume_n_: saves [a], resumes after recursive call with _result.
  struct _Resume_n_ {
    uint64_t a;
  };

  using _Frame = std::variant<_Enter, _Resume_n_>;
  uint64_t _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{n});
  /// Loopified let_nested: _Enter -> _Resume_n_.
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
        _stack.emplace_back(_Resume_n_{a});
        _stack.emplace_back(_Enter{n_});
      }
    } else {
      auto _f = std::move(std::get<_Resume_n_>(_frame));
      _result = (_f.a + _result);
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

  /// _Resume1: saves [n, _s1], resumes after recursive call with _result.
  struct _Resume1 {
    uint64_t n;
    decltype(UINT64_C(1)) _s1;
  };

  using _Frame = std::variant<_Enter, _Resume1>;
  uint64_t _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{n, fuel});
  /// Loopified mod_pattern_fuel: _Enter -> _Resume1.
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
          _stack.emplace_back(_Resume1{n, UINT64_C(1)});
          _stack.emplace_back(
              _Enter{(((n - UINT64_C(1)) > n ? 0 : (n - UINT64_C(1)))), fuel_});
        }
      }
    } else {
      auto _f = std::move(std::get<_Resume1>(_frame));
      _result = ((_f._s1 + _result) ? _f.n % (_f._s1 + _result) : _f.n);
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
  std::vector<_Frame> _stack;
  _stack.reserve(8);
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
      const std::pair<uint64_t, uint64_t> &p = _result.first;
      const uint64_t &c = _result.second;
      const uint64_t &a = p.first;
      const uint64_t &b = p.second;
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

  /// _Resume1: saves [n], resumes after recursive call with _result.
  struct _Resume1 {
    uint64_t n;
  };

  /// _Resume2: saves [_s0], resumes after recursive call with _result.
  struct _Resume2 {
    uint64_t _s0;
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
        if ((UINT64_C(2) ? n % UINT64_C(2) : n) == UINT64_C(0)) {
          _stack.emplace_back(_Resume1{n});
          _stack.emplace_back(_Enter{n_});
        } else {
          _stack.emplace_back(_Resume2{(n * UINT64_C(2))});
          _stack.emplace_back(_Enter{n_});
        }
      }
    } else if (std::holds_alternative<_Resume1>(_frame)) {
      auto _f = std::move(std::get<_Resume1>(_frame));
      _result = (_f.n + _result);
    } else {
      auto _f = std::move(std::get<_Resume2>(_frame));
      _result = (_f._s0 + _result);
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

  /// _After2: saves [_s0, fuel_], dispatches next recursive call.
  struct _After2 {
    decltype((
        ((std::declval<uint64_t &>() - UINT64_C(1)) > std::declval<uint64_t &>()
             ? 0
             : (std::declval<uint64_t &>() - UINT64_C(1))))) _s0;
    uint64_t fuel_;
  };

  /// _Combine1: receives partial results, combines with _result from final
  /// call.
  struct _Combine1 {
    bool _result;
  };

  using _Frame = std::variant<_Enter, _After2, _Combine1>;
  bool _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{n, fuel});
  /// Loopified chained_comp_fuel: _Enter -> _After2 -> _Combine1.
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
          _stack.emplace_back(_After2{
              (((n - UINT64_C(1)) > n ? 0 : (n - UINT64_C(1)))), fuel_});
          _stack.emplace_back(
              _Enter{(((n - UINT64_C(2)) > n ? 0 : (n - UINT64_C(2)))), fuel_});
        }
      }
    } else if (std::holds_alternative<_After2>(_frame)) {
      auto _f = std::move(std::get<_After2>(_frame));
      _stack.emplace_back(_Combine1{_result});
      _stack.emplace_back(_Enter{_f._s0, _f.fuel_});
    } else {
      auto _f = std::move(std::get<_Combine1>(_frame));
      _result = (_result && _f._result);
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
  std::vector<_Frame> _stack;
  _stack.reserve(8);
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
      uint64_t x = _result;
      _stack.emplace_back(_Cont_n___1{x});
      _stack.emplace_back(_Enter{n__});
    } else {
      auto _f = std::move(std::get<_Cont_n___1>(_frame));
      uint64_t x = _f.x;
      uint64_t y = _result;
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

  /// _Resume_n__: saves [n], resumes after recursive call with _result.
  struct _Resume_n__ {
    uint64_t n;
  };

  using _Frame = std::variant<_Enter, _Resume_n__>;
  uint64_t _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{n});
  /// Loopified nested_match: _Enter -> _Resume_n__.
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
          _stack.emplace_back(_Resume_n__{n});
          _stack.emplace_back(_Enter{n__});
        }
      }
    } else {
      auto _f = std::move(std::get<_Resume_n__>(_frame));
      _result = (_f.n + _result);
    }
  }
  return _result;
}
