#include <loopify_nested_constructs.h>

unsigned int LoopifyNestedConstructs::multi_let(
    const unsigned int
        n) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    unsigned int n;
  };

  /// _Resume_n_: saves [c], resumes after recursive call with _result.
  struct _Resume_n_ {
    unsigned int c;
  };

  using _Frame = std::variant<_Enter, _Resume_n_>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{n});
  /// Loopified multi_let: _Enter -> _Resume_n_.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const unsigned int n = _f.n;
      if (n <= 0) {
        _result = 0u;
      } else {
        unsigned int n_ = n - 1;
        unsigned int b = (n_ * 2u);
        unsigned int c = (b + 3u);
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

unsigned int LoopifyNestedConstructs::nested_if_fuel(const unsigned int fuel,
                                                     const unsigned int n) {
  unsigned int _result;
  unsigned int _loop_n = n;
  unsigned int _loop_fuel = fuel;
  while (true) {
    if (_loop_fuel <= 0) {
      _result = 0u;
      break;
    } else {
      unsigned int fuel_ = _loop_fuel - 1;
      if (_loop_n <= 0u) {
        _result = 0u;
        break;
      } else {
        if (_loop_n == 1u) {
          _result = 1u;
          break;
        } else {
          if ((2u ? _loop_n % 2u : _loop_n) == 0u) {
            if (10u < _loop_n) {
              _loop_n = (2u ? _loop_n / 2u : 0);
              _loop_fuel = fuel_;
            } else {
              _loop_n = (((_loop_n - 1u) > _loop_n ? 0 : (_loop_n - 1u)));
              _loop_fuel = fuel_;
            }
          } else {
            _loop_n = (((_loop_n - 2u) > _loop_n ? 0 : (_loop_n - 2u)));
            _loop_fuel = fuel_;
          }
        }
      }
    }
  }
  return _result;
}

unsigned int LoopifyNestedConstructs::nested_if(const unsigned int n) {
  return nested_if_fuel(n, n);
}

unsigned int LoopifyNestedConstructs::deep_nest(
    const unsigned int
        n) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    unsigned int n;
  };

  /// _Cont_n_: resumes after recursive call, then processes rest.
  struct _Cont_n_ {};

  using _Frame = std::variant<_Enter, _Cont_n_>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{n});
  /// Loopified deep_nest: _Enter -> _Cont_n_.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const unsigned int n = _f.n;
      if (n <= 0) {
        _result = 0u;
      } else {
        unsigned int n_ = n - 1;
        _stack.emplace_back(_Cont_n_{});
        _stack.emplace_back(_Enter{n_});
      }
    } else {
      auto _f = std::move(std::get<_Cont_n_>(_frame));
      unsigned int inner = _result;
      unsigned int mid = (inner + 1u);
      _result = (mid * 2u);
    }
  }
  return _result;
}

unsigned int LoopifyNestedConstructs::let_nested(
    const unsigned int
        n) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    unsigned int n;
  };

  /// _Resume_n_: saves [a], resumes after recursive call with _result.
  struct _Resume_n_ {
    unsigned int a;
  };

  using _Frame = std::variant<_Enter, _Resume_n_>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{n});
  /// Loopified let_nested: _Enter -> _Resume_n_.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const unsigned int n = _f.n;
      if (n <= 0) {
        _result = 0u;
      } else {
        unsigned int n_ = n - 1;
        unsigned int a = (n_ + 1u);
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

unsigned int LoopifyNestedConstructs::mod_pattern_fuel(
    const unsigned int fuel,
    const unsigned int
        n) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    unsigned int n;
    unsigned int fuel;
  };

  /// _Resume1: saves [n, _s1], resumes after recursive call with _result.
  struct _Resume1 {
    unsigned int n;
    decltype(1u) _s1;
  };

  using _Frame = std::variant<_Enter, _Resume1>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{n, fuel});
  /// Loopified mod_pattern_fuel: _Enter -> _Resume1.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const unsigned int n = _f.n;
      const unsigned int fuel = _f.fuel;
      if (fuel <= 0) {
        _result = 1u;
      } else {
        unsigned int fuel_ = fuel - 1;
        if (n <= 1u) {
          _result = 1u;
        } else {
          _stack.emplace_back(_Resume1{n, 1u});
          _stack.emplace_back(_Enter{(((n - 1u) > n ? 0 : (n - 1u))), fuel_});
        }
      }
    } else {
      auto _f = std::move(std::get<_Resume1>(_frame));
      _result = ((_f._s1 + _result) ? _f.n % (_f._s1 + _result) : _f.n);
    }
  }
  return _result;
}

unsigned int LoopifyNestedConstructs::mod_pattern(const unsigned int n) {
  return mod_pattern_fuel(n, n);
}

std::pair<std::pair<unsigned int, unsigned int>, unsigned int>
LoopifyNestedConstructs::tuple_constr(
    const unsigned int
        n) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    unsigned int n;
  };

  /// _Cont_n_: saves [n], resumes after recursive call, then processes rest.
  struct _Cont_n_ {
    unsigned int n;
  };

  using _Frame = std::variant<_Enter, _Cont_n_>;
  std::pair<std::pair<unsigned int, unsigned int>, unsigned int> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{n});
  /// Loopified tuple_constr: _Enter -> _Cont_n_.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const unsigned int n = _f.n;
      if (n <= 0) {
        _result = std::make_pair(std::make_pair(0u, 0u), 0u);
      } else {
        unsigned int n_ = n - 1;
        _stack.emplace_back(_Cont_n_{n});
        _stack.emplace_back(_Enter{n_});
      }
    } else {
      auto _f = std::move(std::get<_Cont_n_>(_frame));
      const unsigned int n = _f.n;
      const std::pair<unsigned int, unsigned int> &p = _result.first;
      const unsigned int &c = _result.second;
      const unsigned int &a = p.first;
      const unsigned int &b = p.second;
      _result =
          std::make_pair(std::make_pair((a + 1u), (b + n)), (c + (n * n)));
    }
  }
  return _result;
}

unsigned int LoopifyNestedConstructs::alternating_ops(
    const unsigned int
        n) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    unsigned int n;
  };

  /// _Resume1: saves [n], resumes after recursive call with _result.
  struct _Resume1 {
    unsigned int n;
  };

  /// _Resume2: saves [_s0], resumes after recursive call with _result.
  struct _Resume2 {
    unsigned int _s0;
  };

  using _Frame = std::variant<_Enter, _Resume1, _Resume2>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{n});
  /// Loopified alternating_ops: _Enter -> _Resume1 -> _Resume2.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const unsigned int n = _f.n;
      if (n <= 0) {
        _result = 0u;
      } else {
        unsigned int n_ = n - 1;
        if ((2u ? n % 2u : n) == 0u) {
          _stack.emplace_back(_Resume1{n});
          _stack.emplace_back(_Enter{n_});
        } else {
          _stack.emplace_back(_Resume2{(n * 2u)});
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
    const unsigned int fuel,
    const unsigned int
        n) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    unsigned int n;
    unsigned int fuel;
  };

  /// _After2: saves [_s0, fuel_], dispatches next recursive call.
  struct _After2 {
    decltype((((std::declval<const unsigned int &>() - 1u) >
                       std::declval<const unsigned int &>()
                   ? 0
                   : (std::declval<const unsigned int &>() - 1u)))) _s0;
    unsigned int fuel_;
  };

  /// _Combine1: receives partial results, combines with _result from final
  /// call.
  struct _Combine1 {
    bool _result;
  };

  using _Frame = std::variant<_Enter, _After2, _Combine1>;
  bool _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{n, fuel});
  /// Loopified chained_comp_fuel: _Enter -> _After2 -> _Combine1.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const unsigned int n = _f.n;
      const unsigned int fuel = _f.fuel;
      if (fuel <= 0) {
        _result = true;
      } else {
        unsigned int fuel_ = fuel - 1;
        if (n <= 2u) {
          _result = true;
        } else {
          _stack.emplace_back(_After2{(((n - 1u) > n ? 0 : (n - 1u))), fuel_});
          _stack.emplace_back(_Enter{(((n - 2u) > n ? 0 : (n - 2u))), fuel_});
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

unsigned int LoopifyNestedConstructs::chained_comp(const unsigned int n) {
  if (chained_comp_fuel((n * 2u), n)) {
    return 1u;
  } else {
    return 0u;
  }
}

unsigned int LoopifyNestedConstructs::compute_with_lets(
    const unsigned int
        n) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    unsigned int n;
  };

  /// _Cont_n__: saves [n__], resumes after recursive call, then processes rest.
  struct _Cont_n__ {
    unsigned int n__;
  };

  /// _Cont_n___1: saves [x], resumes after recursive call, then processes rest.
  struct _Cont_n___1 {
    unsigned int x;
  };

  using _Frame = std::variant<_Enter, _Cont_n__, _Cont_n___1>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{n});
  /// Loopified compute_with_lets: _Enter -> _Cont_n__ -> _Cont_n___1.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const unsigned int n = _f.n;
      if (n <= 0) {
        _result = 0u;
      } else {
        unsigned int n_ = n - 1;
        if (n_ <= 0) {
          _result = 1u;
        } else {
          unsigned int n__ = n_ - 1;
          _stack.emplace_back(_Cont_n__{n__});
          _stack.emplace_back(_Enter{n_});
        }
      }
    } else if (std::holds_alternative<_Cont_n__>(_frame)) {
      auto _f = std::move(std::get<_Cont_n__>(_frame));
      unsigned int n__ = _f.n__;
      unsigned int x = _result;
      _stack.emplace_back(_Cont_n___1{x});
      _stack.emplace_back(_Enter{n__});
    } else {
      auto _f = std::move(std::get<_Cont_n___1>(_frame));
      unsigned int x = _f.x;
      unsigned int y = _result;
      unsigned int z = (x + y);
      _result = (z * 2u);
    }
  }
  return _result;
}

unsigned int LoopifyNestedConstructs::nested_match(
    const unsigned int
        n) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    unsigned int n;
  };

  /// _Resume_n__: saves [n], resumes after recursive call with _result.
  struct _Resume_n__ {
    unsigned int n;
  };

  using _Frame = std::variant<_Enter, _Resume_n__>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{n});
  /// Loopified nested_match: _Enter -> _Resume_n__.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const unsigned int n = _f.n;
      if (n <= 0) {
        _result = 0u;
      } else {
        unsigned int n_ = n - 1;
        if (n_ <= 0) {
          _result = 1u;
        } else {
          unsigned int n__ = n_ - 1;
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
