#include <loopify_nested_constructs.h>

unsigned int LoopifyNestedConstructs::multi_let(const unsigned int &n) {
  struct _Enter {
    unsigned int n;
  };

  /// Continuation: saves [c] across recursive call.
  struct _Resume1 {
    unsigned int c;
  };

  using _Frame = std::variant<_Enter, _Resume1>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{n});
  /// Frame dispatch: _Enter, _Resume1.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const unsigned int &n = _f.n;
      if (n <= 0) {
        _result = 0u;
      } else {
        unsigned int n_ = n - 1;
        unsigned int b = (n_ * 2u);
        unsigned int c = (b + 3u);
        _stack.emplace_back(_Resume1{c});
        _stack.emplace_back(_Enter{n_});
      }
    } else {
      auto _f = std::move(std::get<_Resume1>(_frame));
      _result = (_f.c + _result);
    }
  }
  return _result;
}

unsigned int LoopifyNestedConstructs::nested_if_fuel(const unsigned int &fuel,
                                                     const unsigned int &n) {
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
              unsigned int _next_n = (2u ? _loop_n / 2u : 0);
              unsigned int _next_fuel = fuel_;
              _loop_n = std::move(_next_n);
              _loop_fuel = std::move(_next_fuel);
            } else {
              unsigned int _next_n =
                  (((_loop_n - 1u) > _loop_n ? 0 : (_loop_n - 1u)));
              unsigned int _next_fuel = fuel_;
              _loop_n = std::move(_next_n);
              _loop_fuel = std::move(_next_fuel);
            }
          } else {
            unsigned int _next_n =
                (((_loop_n - 2u) > _loop_n ? 0 : (_loop_n - 2u)));
            unsigned int _next_fuel = fuel_;
            _loop_n = std::move(_next_n);
            _loop_fuel = std::move(_next_fuel);
          }
        }
      }
    }
  }
  return _result;
}

unsigned int LoopifyNestedConstructs::nested_if(const unsigned int &n) {
  return nested_if_fuel(n, n);
}

unsigned int LoopifyNestedConstructs::deep_nest(const unsigned int &n) {
  struct _Enter {
    unsigned int n;
  };

  /// Continuation: saves across recursive call, then processes rest.
  struct _Cont1 {};

  using _Frame = std::variant<_Enter, _Cont1>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{n});
  /// Frame dispatch: _Enter, _Cont1.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const unsigned int &n = _f.n;
      if (n <= 0) {
        _result = 0u;
      } else {
        unsigned int n_ = n - 1;
        _stack.emplace_back(_Cont1{});
        _stack.emplace_back(_Enter{n_});
      }
    } else {
      auto _f = std::move(std::get<_Cont1>(_frame));
      unsigned int inner = _result;
      unsigned int mid = (inner + 1u);
      _result = (mid * 2u);
    }
  }
  return _result;
}

unsigned int LoopifyNestedConstructs::let_nested(const unsigned int &n) {
  struct _Enter {
    unsigned int n;
  };

  /// Continuation: saves [a] across recursive call.
  struct _Resume1 {
    unsigned int a;
  };

  using _Frame = std::variant<_Enter, _Resume1>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{n});
  /// Frame dispatch: _Enter, _Resume1.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const unsigned int &n = _f.n;
      if (n <= 0) {
        _result = 0u;
      } else {
        unsigned int n_ = n - 1;
        unsigned int a = (n_ + 1u);
        _stack.emplace_back(_Resume1{a});
        _stack.emplace_back(_Enter{n_});
      }
    } else {
      auto _f = std::move(std::get<_Resume1>(_frame));
      _result = (_f.a + _result);
    }
  }
  return _result;
}

unsigned int LoopifyNestedConstructs::mod_pattern_fuel(const unsigned int &fuel,
                                                       const unsigned int &n) {
  struct _Enter {
    unsigned int n;
    unsigned int fuel;
  };

  /// Continuation: saves [n, _s1] across recursive call.
  struct _Resume1 {
    unsigned int n;
    decltype(1u) _s1;
  };

  using _Frame = std::variant<_Enter, _Resume1>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{n, fuel});
  /// Frame dispatch: _Enter, _Resume1.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const unsigned int &n = _f.n;
      const unsigned int &fuel = _f.fuel;
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

unsigned int LoopifyNestedConstructs::mod_pattern(const unsigned int &n) {
  return mod_pattern_fuel(n, n);
}

std::pair<std::pair<unsigned int, unsigned int>, unsigned int>
LoopifyNestedConstructs::tuple_constr(const unsigned int &n) {
  struct _Enter {
    unsigned int n;
  };

  /// Continuation: saves [n] across recursive call, then processes rest.
  struct _Cont1 {
    unsigned int n;
  };

  using _Frame = std::variant<_Enter, _Cont1>;
  std::pair<std::pair<unsigned int, unsigned int>, unsigned int> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{n});
  /// Frame dispatch: _Enter, _Cont1.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const unsigned int &n = _f.n;
      if (n <= 0) {
        _result = std::make_pair(std::make_pair(0u, 0u), 0u);
      } else {
        unsigned int n_ = n - 1;
        _stack.emplace_back(_Cont1{n});
        _stack.emplace_back(_Enter{n_});
      }
    } else {
      auto _f = std::move(std::get<_Cont1>(_frame));
      const unsigned int &n = _f.n;
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

unsigned int LoopifyNestedConstructs::alternating_ops(const unsigned int &n) {
  struct _Enter {
    unsigned int n;
  };

  /// Continuation: saves [n] across recursive call.
  struct _Resume1 {
    unsigned int n;
  };

  /// Continuation: saves [_s0] across recursive call.
  struct _Resume2 {
    decltype((std::declval<const unsigned int &>() * 2u)) _s0;
  };

  using _Frame = std::variant<_Enter, _Resume1, _Resume2>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{n});
  /// Frame dispatch: _Enter, _Resume1, _Resume2.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const unsigned int &n = _f.n;
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

bool LoopifyNestedConstructs::chained_comp_fuel(const unsigned int &fuel,
                                                const unsigned int &n) {
  struct _Enter {
    unsigned int n;
    unsigned int fuel;
  };

  /// Intermediate: saves [_s0, fuel_], dispatches next recursive call.
  struct _After2 {
    decltype((((std::declval<const unsigned int &>() - 1u) >
                       std::declval<const unsigned int &>()
                   ? 0
                   : (std::declval<const unsigned int &>() - 1u)))) _s0;
    unsigned int fuel_;
  };

  /// Combiner: receives first result, combines with second recursive call.
  struct _Combine1 {
    bool _result;
  };

  using _Frame = std::variant<_Enter, _After2, _Combine1>;
  bool _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{n, fuel});
  /// Frame dispatch: _Enter, _After2, _Combine1.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const unsigned int &n = _f.n;
      const unsigned int &fuel = _f.fuel;
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

unsigned int LoopifyNestedConstructs::chained_comp(const unsigned int &n) {
  if (chained_comp_fuel((n * 2u), n)) {
    return 1u;
  } else {
    return 0u;
  }
}

unsigned int LoopifyNestedConstructs::compute_with_lets(const unsigned int &n) {
  struct _Enter {
    unsigned int n;
  };

  /// Continuation: saves [n__] across recursive call, then processes rest.
  struct _Cont1 {
    unsigned int n__;
  };

  /// Continuation: saves [x] across recursive call, then processes rest.
  struct _Cont2 {
    unsigned int x;
  };

  using _Frame = std::variant<_Enter, _Cont1, _Cont2>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{n});
  /// Frame dispatch: _Enter, _Cont1, _Cont2.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const unsigned int &n = _f.n;
      if (n <= 0) {
        _result = 0u;
      } else {
        unsigned int n_ = n - 1;
        if (n_ <= 0) {
          _result = 1u;
        } else {
          unsigned int n__ = n_ - 1;
          _stack.emplace_back(_Cont1{n__});
          _stack.emplace_back(_Enter{n_});
        }
      }
    } else if (std::holds_alternative<_Cont1>(_frame)) {
      auto _f = std::move(std::get<_Cont1>(_frame));
      unsigned int n__ = std::move(_f.n__);
      unsigned int x = _result;
      _stack.emplace_back(_Cont2{x});
      _stack.emplace_back(_Enter{n__});
    } else {
      auto _f = std::move(std::get<_Cont2>(_frame));
      unsigned int x = std::move(_f.x);
      unsigned int y = _result;
      unsigned int z = (x + y);
      _result = (z * 2u);
    }
  }
  return _result;
}

unsigned int LoopifyNestedConstructs::nested_match(const unsigned int &n) {
  struct _Enter {
    unsigned int n;
  };

  /// Continuation: saves [n] across recursive call.
  struct _Resume1 {
    unsigned int n;
  };

  using _Frame = std::variant<_Enter, _Resume1>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{n});
  /// Frame dispatch: _Enter, _Resume1.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const unsigned int &n = _f.n;
      if (n <= 0) {
        _result = 0u;
      } else {
        unsigned int n_ = n - 1;
        if (n_ <= 0) {
          _result = 1u;
        } else {
          unsigned int n__ = n_ - 1;
          _stack.emplace_back(_Resume1{n});
          _stack.emplace_back(_Enter{n__});
        }
      }
    } else {
      auto _f = std::move(std::get<_Resume1>(_frame));
      _result = (_f.n + _result);
    }
  }
  return _result;
}
