#include "loopify_nested_constructs.h"

uint64_t LoopifyNestedConstructs::multi_let(uint64_t n) {
  // Explicit stack replaces the non-tail recursion of multi_let: _call frames
  // are pending calls, _after frames resume a caller.
  struct _call {
    uint64_t n;
  };

  struct _after_multi_let_in_S {
    uint64_t c;
  };

  using _frame = std::variant<_call, _after_multi_let_in_S>;
  uint64_t _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{n});
  while (!_stack.empty()) {
    _frame _popped = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      uint64_t n = _f.n;
      if (n <= 0) {
        _result = UINT64_C(0);
      } else {
        uint64_t n_ = n - 1;
        uint64_t b = (n_ * UINT64_C(2));
        uint64_t c = (b + UINT64_C(3));
        _stack.emplace_back(_after_multi_let_in_S{c});
        _stack.emplace_back(_call{n_});
      }
    } else {
      auto _f = std::move(std::get<_after_multi_let_in_S>(_popped));
      uint64_t c = _f.c;
      _result = (c + std::move(_result));
    }
  }
  return _result;
}

uint64_t LoopifyNestedConstructs::nested_if_fuel(uint64_t fuel, uint64_t n) {
  // Loop replaces the tail recursion: each recursive call updates the loop
  // variables.
  uint64_t _loop_n = n;
  uint64_t _loop_fuel = fuel;
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
              _loop_n =
                  (((_loop_n - UINT64_C(1)) > _loop_n ? 0
                                                      : (_loop_n -
                                                         UINT64_C(1))));
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

uint64_t LoopifyNestedConstructs::deep_nest(uint64_t n) {
  // Explicit stack replaces the non-tail recursion of deep_nest: _call frames
  // are pending calls, _after frames resume a caller.
  struct _call {
    uint64_t n;
  };

  struct _after_deep_nest_in_S {};

  using _frame = std::variant<_call, _after_deep_nest_in_S>;
  uint64_t _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{n});
  while (!_stack.empty()) {
    _frame _popped = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      uint64_t n = _f.n;
      if (n <= 0) {
        _result = UINT64_C(0);
      } else {
        uint64_t n_ = n - 1;
        _stack.emplace_back(_after_deep_nest_in_S{});
        _stack.emplace_back(_call{n_});
      }
    } else {
      auto _f = std::move(std::get<_after_deep_nest_in_S>(_popped));
      uint64_t inner = std::move(_result);
      uint64_t mid = (inner + UINT64_C(1));
      _result = (mid * UINT64_C(2));
    }
  }
  return _result;
}

uint64_t LoopifyNestedConstructs::let_nested(uint64_t n) {
  // Explicit stack replaces the non-tail recursion of let_nested: _call frames
  // are pending calls, _after frames resume a caller.
  struct _call {
    uint64_t n;
  };

  struct _after_let_nested_in_S {
    uint64_t a;
  };

  using _frame = std::variant<_call, _after_let_nested_in_S>;
  uint64_t _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{n});
  while (!_stack.empty()) {
    _frame _popped = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      uint64_t n = _f.n;
      if (n <= 0) {
        _result = UINT64_C(0);
      } else {
        uint64_t n_ = n - 1;
        uint64_t a = (n_ + UINT64_C(1));
        _stack.emplace_back(_after_let_nested_in_S{a});
        _stack.emplace_back(_call{n_});
      }
    } else {
      auto _f = std::move(std::get<_after_let_nested_in_S>(_popped));
      uint64_t a = _f.a;
      _result = (a + std::move(_result));
    }
  }
  return _result;
}

uint64_t LoopifyNestedConstructs::mod_pattern_fuel(uint64_t fuel, uint64_t n) {
  // Explicit stack replaces the non-tail recursion of mod_pattern_fuel: _call
  // frames are pending calls, _after frames resume a caller.
  struct _call {
    uint64_t n;
    uint64_t fuel;
  };

  struct _after_mod_pattern_fuel_in_false {
    uint64_t n;
  };

  using _frame = std::variant<_call, _after_mod_pattern_fuel_in_false>;
  uint64_t _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{n, fuel});
  while (!_stack.empty()) {
    _frame _popped = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      uint64_t n = _f.n;
      uint64_t fuel = _f.fuel;
      if (fuel <= 0) {
        _result = UINT64_C(1);
      } else {
        uint64_t fuel_ = fuel - 1;
        if (n <= UINT64_C(1)) {
          _result = UINT64_C(1);
        } else {
          _stack.emplace_back(_after_mod_pattern_fuel_in_false{n});
          _stack.emplace_back(
              _call{(((n - UINT64_C(1)) > n ? 0 : (n - UINT64_C(1)))), fuel_});
        }
      }
    } else {
      auto _f = std::move(std::get<_after_mod_pattern_fuel_in_false>(_popped));
      uint64_t n = _f.n;
      auto &&_once1 = (UINT64_C(1) + std::move(_result));
      _result = (_once1 ? n % _once1 : n);
    }
  }
  return _result;
}

uint64_t LoopifyNestedConstructs::mod_pattern(uint64_t n) {
  return mod_pattern_fuel(n, n);
}

std::pair<std::pair<uint64_t, uint64_t>, uint64_t>
LoopifyNestedConstructs::tuple_constr(uint64_t n) {
  // Explicit stack replaces the non-tail recursion of tuple_constr: _call
  // frames are pending calls, _after frames resume a caller.
  struct _call {
    uint64_t n;
  };

  struct _after_tuple_constr_in_S {
    uint64_t n;
  };

  using _frame = std::variant<_call, _after_tuple_constr_in_S>;
  std::pair<std::pair<uint64_t, uint64_t>, uint64_t> _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{n});
  while (!_stack.empty()) {
    _frame _popped = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      uint64_t n = _f.n;
      if (n <= 0) {
        _result = std::make_pair(std::make_pair(UINT64_C(0), UINT64_C(0)),
                                 UINT64_C(0));
      } else {
        uint64_t n_ = n - 1;
        _stack.emplace_back(_after_tuple_constr_in_S{n});
        _stack.emplace_back(_call{n_});
      }
    } else {
      auto _f = std::move(std::get<_after_tuple_constr_in_S>(_popped));
      uint64_t n = _f.n;
      std::pair<std::pair<uint64_t, uint64_t>, uint64_t> _tmp1 =
          std::move(_result);
      const auto &[p, c] = _tmp1;
      const auto &[a, b] = p;
      _result = std::make_pair(std::make_pair((a + UINT64_C(1)), (b + n)),
                               (c + (n * n)));
    }
  }
  return _result;
}

uint64_t LoopifyNestedConstructs::alternating_ops(uint64_t n) {
  // Explicit stack replaces the non-tail recursion of alternating_ops: _call
  // frames are pending calls, _after frames resume a caller.
  struct _call {
    uint64_t n;
  };

  struct _after_alternating_ops_in_false {
    uint64_t n;
  };

  struct _after_alternating_ops_in_true {
    uint64_t n;
  };

  using _frame = std::variant<_call, _after_alternating_ops_in_false,
                              _after_alternating_ops_in_true>;
  uint64_t _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{n});
  while (!_stack.empty()) {
    _frame _popped = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      uint64_t n = _f.n;
      if (n <= 0) {
        _result = UINT64_C(0);
      } else {
        uint64_t n_ = n - 1;
        if ((UINT64_C(2) ? n % UINT64_C(2) : n) == UINT64_C(0)) {
          _stack.emplace_back(_after_alternating_ops_in_true{n});
          _stack.emplace_back(_call{n_});
        } else {
          _stack.emplace_back(_after_alternating_ops_in_false{n});
          _stack.emplace_back(_call{n_});
        }
      }
    } else if (std::holds_alternative<_after_alternating_ops_in_false>(_popped)) {
      auto _f = std::move(std::get<_after_alternating_ops_in_false>(_popped));
      uint64_t n = _f.n;
      _result = ((n * UINT64_C(2)) + std::move(_result));
    } else {
      auto _f = std::move(std::get<_after_alternating_ops_in_true>(_popped));
      uint64_t n = _f.n;
      _result = (n + std::move(_result));
    }
  }
  return _result;
}

bool LoopifyNestedConstructs::chained_comp_fuel(uint64_t fuel, uint64_t n) {
  // Explicit stack replaces the non-tail recursion of chained_comp_fuel: _call
  // frames are pending calls, _after frames resume a caller.
  struct _call {
    uint64_t n;
    uint64_t fuel;
  };

  struct _after_chained_comp_fuel_in_false {
    uint64_t n;
    uint64_t fuel_;
  };

  struct _after_chained_comp_fuel_in_false_2 {
    bool _tmp2;
  };

  using _frame = std::variant<_call, _after_chained_comp_fuel_in_false,
                              _after_chained_comp_fuel_in_false_2>;
  bool _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{n, fuel});
  while (!_stack.empty()) {
    _frame _popped = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      uint64_t n = _f.n;
      uint64_t fuel = _f.fuel;
      if (fuel <= 0) {
        _result = true;
      } else {
        uint64_t fuel_ = fuel - 1;
        if (n <= UINT64_C(2)) {
          _result = true;
        } else {
          _stack.emplace_back(_after_chained_comp_fuel_in_false{n, fuel_});
          _stack.emplace_back(
              _call{(((n - UINT64_C(1)) > n ? 0 : (n - UINT64_C(1)))), fuel_});
        }
      }
    } else if (
            std::holds_alternative<_after_chained_comp_fuel_in_false>(_popped)) {
      auto _f = std::move(std::get<_after_chained_comp_fuel_in_false>(_popped));
      uint64_t n = _f.n;
      uint64_t fuel_ = _f.fuel_;
      _stack.emplace_back(
          _after_chained_comp_fuel_in_false_2{std::move(_result)});
      _stack.emplace_back(
          _call{(((n - UINT64_C(2)) > n ? 0 : (n - UINT64_C(2)))), fuel_});
    } else {
      auto _f =
          std::move(std::get<_after_chained_comp_fuel_in_false_2>(_popped));
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

uint64_t LoopifyNestedConstructs::compute_with_lets(uint64_t n) {
  // Explicit stack replaces the non-tail recursion of compute_with_lets: _call
  // frames are pending calls, _after frames resume a caller.
  struct _call {
    uint64_t n;
  };

  struct _after_compute_with_lets_in_S {
    uint64_t n_p;
  };

  struct _after_compute_with_lets_in_S_2 {
    uint64_t x;
  };

  using _frame = std::variant<_call, _after_compute_with_lets_in_S,
                              _after_compute_with_lets_in_S_2>;
  uint64_t _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{n});
  while (!_stack.empty()) {
    _frame _popped = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      uint64_t n = _f.n;
      if (n <= 0) {
        _result = UINT64_C(0);
      } else {
        uint64_t n_ = n - 1;
        if (n_ <= 0) {
          _result = UINT64_C(1);
        } else {
          uint64_t n_p = n_ - 1;
          _stack.emplace_back(_after_compute_with_lets_in_S{n_p});
          _stack.emplace_back(_call{n_});
        }
      }
    } else if (std::holds_alternative<_after_compute_with_lets_in_S>(_popped)) {
      auto _f = std::move(std::get<_after_compute_with_lets_in_S>(_popped));
      uint64_t n_p = _f.n_p;
      uint64_t x = std::move(_result);
      _stack.emplace_back(_after_compute_with_lets_in_S_2{x});
      _stack.emplace_back(_call{n_p});
    } else {
      auto _f = std::move(std::get<_after_compute_with_lets_in_S_2>(_popped));
      uint64_t x = _f.x;
      uint64_t y = std::move(_result);
      uint64_t z = (x + y);
      _result = (z * UINT64_C(2));
    }
  }
  return _result;
}

uint64_t LoopifyNestedConstructs::nested_match(uint64_t n) {
  // Explicit stack replaces the non-tail recursion of nested_match: _call
  // frames are pending calls, _after frames resume a caller.
  struct _call {
    uint64_t n;
  };

  struct _after_nested_match_in_S {
    uint64_t n;
  };

  using _frame = std::variant<_call, _after_nested_match_in_S>;
  uint64_t _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{n});
  while (!_stack.empty()) {
    _frame _popped = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      uint64_t n = _f.n;
      if (n <= 0) {
        _result = UINT64_C(0);
      } else {
        uint64_t n_ = n - 1;
        if (n_ <= 0) {
          _result = UINT64_C(1);
        } else {
          uint64_t n_p = n_ - 1;
          _stack.emplace_back(_after_nested_match_in_S{n});
          _stack.emplace_back(_call{n_p});
        }
      }
    } else {
      auto _f = std::move(std::get<_after_nested_match_in_S>(_popped));
      uint64_t n = _f.n;
      _result = (n + std::move(_result));
    }
  }
  return _result;
}
