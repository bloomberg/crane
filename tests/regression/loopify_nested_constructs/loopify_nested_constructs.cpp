#include <loopify_nested_constructs.h>

#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

__attribute__((pure)) unsigned int
LoopifyNestedConstructs::multi_let(const unsigned int n) {
  struct _Enter {
    const unsigned int n;
  };

  struct _Call1 {
    unsigned int _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.emplace_back(_Enter{n});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      const auto &_f = std::get<_Enter>(_frame);
      const unsigned int n = _f.n;
      if (n <= 0) {
        _result = 0u;
      } else {
        unsigned int n_ = n - 1;
        unsigned int b = (n_ * 2u);
        unsigned int c = (b + 3u);
        _stack.emplace_back(_Call1{c});
        _stack.emplace_back(_Enter{n_});
      }
    } else {
      const auto &_f = std::get<_Call1>(_frame);
      _result = (_f._s0 + _result);
    }
  }
  return _result;
}

__attribute__((pure)) unsigned int
LoopifyNestedConstructs::nested_if_fuel(const unsigned int fuel,
                                        const unsigned int n) {
  unsigned int _result;
  unsigned int _loop_n = n;
  unsigned int _loop_fuel = fuel;
  bool _continue = true;
  while (_continue) {
    if (_loop_fuel <= 0) {
      _result = 0u;
      _continue = false;
    } else {
      unsigned int fuel_ = _loop_fuel - 1;
      if (_loop_n <= 0u) {
        _result = 0u;
        _continue = false;
      } else {
        if (_loop_n == 1u) {
          _result = 1u;
          _continue = false;
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

__attribute__((pure)) unsigned int
LoopifyNestedConstructs::nested_if(const unsigned int n) {
  return nested_if_fuel(n, n);
}

__attribute__((pure)) unsigned int
LoopifyNestedConstructs::deep_nest(const unsigned int n) {
  struct _Enter {
    const unsigned int n;
  };

  struct _Call1 {};

  using _Frame = std::variant<_Enter, _Call1>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.emplace_back(_Enter{n});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      const auto &_f = std::get<_Enter>(_frame);
      const unsigned int n = _f.n;
      if (n <= 0) {
        _result = 0u;
      } else {
        unsigned int n_ = n - 1;
        _stack.emplace_back(_Call1{});
        _stack.emplace_back(_Enter{n_});
      }
    } else {
      const auto &_f = std::get<_Call1>(_frame);
      unsigned int inner = _result;
      unsigned int mid = (inner + 1u);
      _result = (mid * 2u);
    }
  }
  return _result;
}

__attribute__((pure)) unsigned int
LoopifyNestedConstructs::let_nested(const unsigned int n) {
  struct _Enter {
    const unsigned int n;
  };

  struct _Call1 {
    unsigned int _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.emplace_back(_Enter{n});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      const auto &_f = std::get<_Enter>(_frame);
      const unsigned int n = _f.n;
      if (n <= 0) {
        _result = 0u;
      } else {
        unsigned int n_ = n - 1;
        unsigned int a = (n_ + 1u);
        _stack.emplace_back(_Call1{a});
        _stack.emplace_back(_Enter{n_});
      }
    } else {
      const auto &_f = std::get<_Call1>(_frame);
      _result = (_f._s0 + _result);
    }
  }
  return _result;
}

__attribute__((pure)) unsigned int
LoopifyNestedConstructs::mod_pattern_fuel(const unsigned int fuel,
                                          const unsigned int n) {
  struct _Enter {
    const unsigned int n;
    const unsigned int fuel;
  };

  struct _Call1 {
    const unsigned int _s0;
    decltype(1u) _s1;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.emplace_back(_Enter{n, fuel});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      const auto &_f = std::get<_Enter>(_frame);
      const unsigned int n = _f.n;
      const unsigned int fuel = _f.fuel;
      if (fuel <= 0) {
        _result = 1u;
      } else {
        unsigned int fuel_ = fuel - 1;
        if (n <= 1u) {
          _result = 1u;
        } else {
          _stack.emplace_back(_Call1{n, 1u});
          _stack.emplace_back(_Enter{(((n - 1u) > n ? 0 : (n - 1u))), fuel_});
        }
      }
    } else {
      const auto &_f = std::get<_Call1>(_frame);
      _result = ((_f._s1 + _result) ? _f._s0 % (_f._s1 + _result) : _f._s0);
    }
  }
  return _result;
}

__attribute__((pure)) unsigned int
LoopifyNestedConstructs::mod_pattern(const unsigned int n) {
  return mod_pattern_fuel(n, n);
}

__attribute__((pure))
std::pair<std::pair<unsigned int, unsigned int>, unsigned int>
LoopifyNestedConstructs::tuple_constr(const unsigned int n) {
  struct _Enter {
    const unsigned int n;
  };

  struct _Call1 {
    const unsigned int _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::pair<std::pair<unsigned int, unsigned int>, unsigned int> _result{};
  std::vector<_Frame> _stack;
  _stack.emplace_back(_Enter{n});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      const auto &_f = std::get<_Enter>(_frame);
      const unsigned int n = _f.n;
      if (n <= 0) {
        _result = std::make_pair(std::make_pair(0u, 0u), 0u);
      } else {
        unsigned int n_ = n - 1;
        _stack.emplace_back(_Call1{n});
        _stack.emplace_back(_Enter{n_});
      }
    } else {
      const auto &_f = std::get<_Call1>(_frame);
      const unsigned int n = _f._s0;
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

__attribute__((pure)) unsigned int
LoopifyNestedConstructs::alternating_ops(const unsigned int n) {
  struct _Enter {
    const unsigned int n;
  };

  struct _Call1 {
    const unsigned int _s0;
  };

  struct _Call2 {
    decltype((std::declval<const unsigned int &>() * 2u)) _s0;
  };

  using _Frame = std::variant<_Enter, _Call1, _Call2>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.emplace_back(_Enter{n});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      const auto &_f = std::get<_Enter>(_frame);
      const unsigned int n = _f.n;
      if (n <= 0) {
        _result = 0u;
      } else {
        unsigned int n_ = n - 1;
        if ((2u ? n % 2u : n) == 0u) {
          _stack.emplace_back(_Call1{n});
          _stack.emplace_back(_Enter{n_});
        } else {
          _stack.emplace_back(_Call2{(n * 2u)});
          _stack.emplace_back(_Enter{n_});
        }
      }
    } else if (std::holds_alternative<_Call1>(_frame)) {
      const auto &_f = std::get<_Call1>(_frame);
      _result = (_f._s0 + _result);
    } else {
      const auto &_f = std::get<_Call2>(_frame);
      _result = (_f._s0 + _result);
    }
  }
  return _result;
}

__attribute__((pure)) bool
LoopifyNestedConstructs::chained_comp_fuel(const unsigned int fuel,
                                           const unsigned int n) {
  struct _Enter {
    const unsigned int n;
    const unsigned int fuel;
  };

  struct _Call1 {
    decltype((((std::declval<const unsigned int &>() - 1u) >
                       std::declval<const unsigned int &>()
                   ? 0
                   : (std::declval<const unsigned int &>() - 1u)))) _s0;
    unsigned int _s1;
  };

  struct _Call2 {
    bool _s0;
  };

  using _Frame = std::variant<_Enter, _Call1, _Call2>;
  bool _result{};
  std::vector<_Frame> _stack;
  _stack.emplace_back(_Enter{n, fuel});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      const auto &_f = std::get<_Enter>(_frame);
      const unsigned int n = _f.n;
      const unsigned int fuel = _f.fuel;
      if (fuel <= 0) {
        _result = true;
      } else {
        unsigned int fuel_ = fuel - 1;
        if (n <= 2u) {
          _result = true;
        } else {
          _stack.emplace_back(_Call1{(((n - 1u) > n ? 0 : (n - 1u))), fuel_});
          _stack.emplace_back(_Enter{(((n - 2u) > n ? 0 : (n - 2u))), fuel_});
        }
      }
    } else if (std::holds_alternative<_Call1>(_frame)) {
      const auto &_f = std::get<_Call1>(_frame);
      _stack.emplace_back(_Call2{_result});
      _stack.emplace_back(_Enter{_f._s0, _f._s1});
    } else {
      const auto &_f = std::get<_Call2>(_frame);
      _result = (_result && _f._s0);
    }
  }
  return _result;
}

__attribute__((pure)) unsigned int
LoopifyNestedConstructs::chained_comp(const unsigned int n) {
  if (chained_comp_fuel((n * 2u), n)) {
    return 1u;
  } else {
    return 0u;
  }
}

__attribute__((pure)) unsigned int
LoopifyNestedConstructs::compute_with_lets(const unsigned int n) {
  struct _Enter {
    const unsigned int n;
  };

  struct _Call1 {
    unsigned int _s0;
  };

  struct _Call2 {
    unsigned int _s0;
  };

  using _Frame = std::variant<_Enter, _Call1, _Call2>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.emplace_back(_Enter{n});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      const auto &_f = std::get<_Enter>(_frame);
      const unsigned int n = _f.n;
      if (n <= 0) {
        _result = 0u;
      } else {
        unsigned int n_ = n - 1;
        if (n_ <= 0) {
          _result = 1u;
        } else {
          unsigned int n__ = n_ - 1;
          _stack.emplace_back(_Call1{n__});
          _stack.emplace_back(_Enter{n_});
        }
      }
    } else if (std::holds_alternative<_Call1>(_frame)) {
      const auto &_f = std::get<_Call1>(_frame);
      unsigned int n__ = _f._s0;
      unsigned int x = _result;
      _stack.emplace_back(_Call2{x});
      _stack.emplace_back(_Enter{n__});
    } else {
      const auto &_f = std::get<_Call2>(_frame);
      unsigned int x = _f._s0;
      unsigned int y = _result;
      unsigned int z = (x + y);
      _result = (z * 2u);
    }
  }
  return _result;
}

__attribute__((pure)) unsigned int
LoopifyNestedConstructs::nested_match(const unsigned int n) {
  struct _Enter {
    const unsigned int n;
  };

  struct _Call1 {
    const unsigned int _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.emplace_back(_Enter{n});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      const auto &_f = std::get<_Enter>(_frame);
      const unsigned int n = _f.n;
      if (n <= 0) {
        _result = 0u;
      } else {
        unsigned int n_ = n - 1;
        if (n_ <= 0) {
          _result = 1u;
        } else {
          unsigned int n__ = n_ - 1;
          _stack.emplace_back(_Call1{n});
          _stack.emplace_back(_Enter{n__});
        }
      }
    } else {
      const auto &_f = std::get<_Call1>(_frame);
      _result = (_f._s0 + _result);
    }
  }
  return _result;
}
