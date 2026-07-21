#include "loopify_patterns.h"

/// Complex control flow and pattern matching edge cases.
/// multi_let n multiple sequential let bindings before recursion.
uint64_t
LoopifyPatterns::multi_let(uint64_t n) { /// _Enter: captures varying parameters
                                         /// for each recursive call.

  struct _Enter {
    uint64_t n;
  };

  /// _Resume_m: saves [c], resumes after recursive call with _result.
  struct _Resume_m {
    uint64_t c;
  };

  using _Frame = std::variant<_Enter, _Resume_m>;
  uint64_t _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{n});
  /// Loopified multi_let: _Enter -> _Resume_m.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      uint64_t n = _f.n;
      if (n <= 0) {
        _result = UINT64_C(0);
      } else {
        uint64_t m = n - 1;
        uint64_t b = (m * UINT64_C(2));
        uint64_t c = (b + UINT64_C(3));
        _stack.emplace_back(_Resume_m{c});
        _stack.emplace_back(_Enter{m});
      }
    } else {
      auto _f = std::move(std::get<_Resume_m>(_frame));
      _result = (_f.c + std::move(_result));
    }
  }
  return _result;
}

/// nested_if n deeply nested if-then-else with recursion at different depths.
uint64_t LoopifyPatterns::nested_if_fuel(uint64_t fuel, uint64_t n) {
  uint64_t _loop_n = std::move(n);
  uint64_t _loop_fuel = std::move(fuel);
  while (true) {
    if (_loop_fuel <= 0) {
      return UINT64_C(0);
    } else {
      uint64_t f = _loop_fuel - 1;
      if (_loop_n <= 0) {
        return UINT64_C(0);
      } else {
        uint64_t n_ = _loop_n - 1;
        if (n_ <= 0) {
          return UINT64_C(1);
        } else {
          uint64_t m = n_ - 1;
          if ((UINT64_C(2) ? n_ % UINT64_C(2) : n_) == UINT64_C(0)) {
            if (UINT64_C(10) < n_) {
              _loop_n = (UINT64_C(2) ? n_ / UINT64_C(2) : 0);
              _loop_fuel = f;
            } else {
              _loop_n = m;
              _loop_fuel = f;
            }
          } else {
            _loop_n = (m == UINT64_C(0)
                           ? UINT64_C(0)
                           : (((m - UINT64_C(1)) > m ? 0 : (m - UINT64_C(1)))));
            _loop_fuel = f;
          }
        }
      }
    }
  }
}

uint64_t LoopifyPatterns::nested_if(uint64_t n) {
  return nested_if_fuel(UINT64_C(1000), n);
}

/// deep_nest n deeply nested function application.
uint64_t
LoopifyPatterns::deep_nest(uint64_t n) { /// _Enter: captures varying parameters
                                         /// for each recursive call.

  struct _Enter {
    uint64_t n;
  };

  /// _Resume_m: saves [_s0, _s1, _s2], resumes after recursive call with
  /// _result.
  struct _Resume_m {
    std::decay_t<decltype(UINT64_C(1))> _s0;
    std::decay_t<decltype(UINT64_C(1))> _s1;
    std::decay_t<decltype(UINT64_C(1))> _s2;
  };

  using _Frame = std::variant<_Enter, _Resume_m>;
  uint64_t _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{n});
  /// Loopified deep_nest: _Enter -> _Resume_m.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      uint64_t n = _f.n;
      if (n <= 0) {
        _result = UINT64_C(0);
      } else {
        uint64_t m = n - 1;
        _stack.emplace_back(_Resume_m{UINT64_C(1), UINT64_C(1), UINT64_C(1)});
        _stack.emplace_back(_Enter{m});
      }
    } else {
      auto _f = std::move(std::get<_Resume_m>(_frame));
      _result = (_f._s0 + (_f._s1 + (_f._s2 + std::move(_result))));
    }
  }
  return _result;
}

/// bool_chain n target multiple recursive calls in || chain.
bool LoopifyPatterns::bool_chain_fuel(
    uint64_t fuel, uint64_t n,
    uint64_t target) { /// _Enter: captures varying parameters for each
                       /// recursive call.

  struct _Enter {
    uint64_t n;
    uint64_t fuel;
  };

  /// _After2: saves [_s0, f], dispatches next recursive call.
  struct _After2 {
    std::decay_t<decltype((
        ((std::declval<uint64_t &>() - UINT64_C(1)) > std::declval<uint64_t &>()
             ? 0
             : (std::declval<uint64_t &>() - UINT64_C(1)))))>
        _s0;
    uint64_t f;
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
  /// Loopified bool_chain_fuel: _Enter -> _After2 -> _Combine1.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      uint64_t n = _f.n;
      uint64_t fuel = _f.fuel;
      if (fuel <= 0) {
        _result = false;
      } else {
        uint64_t f = fuel - 1;
        if (n == UINT64_C(0)) {
          _result = false;
        } else {
          if (n == target) {
            _result = true;
          } else {
            if (n == UINT64_C(1)) {
              _result = false;
            } else {
              _stack.emplace_back(_After2{
                  (((n - UINT64_C(1)) > n ? 0 : (n - UINT64_C(1)))), f});
              _stack.emplace_back(
                  _Enter{(((n - UINT64_C(2)) > n ? 0 : (n - UINT64_C(2)))), f});
            }
          }
        }
      }
    } else if (std::holds_alternative<_After2>(_frame)) {
      auto _f = std::move(std::get<_After2>(_frame));
      _stack.emplace_back(_Combine1{std::move(_result)});
      _stack.emplace_back(_Enter{_f._s0, _f.f});
    } else {
      auto _f = std::move(std::get<_Combine1>(_frame));
      _result = (std::move(_result) || std::move(_f._result));
    }
  }
  return _result;
}

bool LoopifyPatterns::bool_chain(uint64_t n, uint64_t target) {
  return bool_chain_fuel(UINT64_C(1000), n, target);
}

/// chained_comp n boolean result with double recursion.
bool LoopifyPatterns::chained_comp(
    uint64_t
        n) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    uint64_t n;
  };

  /// _After_m: saves [n_], dispatches next recursive call.
  struct _After_m {
    uint64_t n_;
  };

  /// _Combine_m: receives partial results, combines with _result from final
  /// call.
  struct _Combine_m {
    bool _result;
  };

  using _Frame = std::variant<_Enter, _After_m, _Combine_m>;
  bool _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{n});
  /// Loopified chained_comp: _Enter -> _After_m -> _Combine_m.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      uint64_t n = _f.n;
      if (n <= 0) {
        _result = true;
      } else {
        uint64_t n_ = n - 1;
        if (n_ <= 0) {
          _result = true;
        } else {
          uint64_t m = n_ - 1;
          _stack.emplace_back(_After_m{n_});
          _stack.emplace_back(_Enter{m});
        }
      }
    } else if (std::holds_alternative<_After_m>(_frame)) {
      auto _f = std::move(std::get<_After_m>(_frame));
      _stack.emplace_back(_Combine_m{std::move(_result)});
      _stack.emplace_back(_Enter{_f.n_});
    } else {
      auto _f = std::move(std::get<_Combine_m>(_frame));
      _result = (std::move(_result) && std::move(_f._result));
    }
  }
  return _result;
}

/// tuple_constr n recursive calls in multiple tuple positions.
std::pair<std::pair<uint64_t, uint64_t>, uint64_t>
LoopifyPatterns::tuple_constr(
    uint64_t
        n) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    uint64_t n;
  };

  /// _Cont_m: saves [n], resumes after recursive call, then processes rest.
  struct _Cont_m {
    uint64_t n;
  };

  using _Frame = std::variant<_Enter, _Cont_m>;
  std::pair<std::pair<uint64_t, uint64_t>, uint64_t> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{n});
  /// Loopified tuple_constr: _Enter -> _Cont_m.
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
        uint64_t m = n - 1;
        _stack.emplace_back(_Cont_m{n});
        _stack.emplace_back(_Enter{m});
      }
    } else {
      auto _f = std::move(std::get<_Cont_m>(_frame));
      uint64_t n = _f.n;
      std::pair<std::pair<uint64_t, uint64_t>, uint64_t> _rc1 =
          std::move(_result);
      auto [p, c] = _rc1;
      auto [a, b] = std::move(p);
      _result = std::make_pair(std::make_pair((a + 1), (b + n)), (c + (n * n)));
    }
  }
  return _result;
}

/// sum_prod_count l a_sum a_prod a_count multiple accumulator updates.
std::pair<std::pair<uint64_t, uint64_t>, uint64_t>
LoopifyPatterns::sum_prod_count(const LoopifyPatterns::list<uint64_t> &l,
                                uint64_t a_sum, uint64_t a_prod,
                                uint64_t a_count) {
  uint64_t _loop_a_count = std::move(a_count);
  uint64_t _loop_a_prod = std::move(a_prod);
  uint64_t _loop_a_sum = std::move(a_sum);
  const LoopifyPatterns::list<uint64_t> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<typename LoopifyPatterns::list<uint64_t>::Nil>(
            _loop_l->v())) {
      return std::make_pair(std::make_pair(_loop_a_sum, _loop_a_prod),
                            _loop_a_count);
    } else {
      const auto &[a0, a1] =
          std::get<typename LoopifyPatterns::list<uint64_t>::Cons>(
              _loop_l->v());
      _loop_a_count = (_loop_a_count + 1);
      _loop_a_prod = (_loop_a_prod * a0);
      _loop_a_sum = (_loop_a_sum + a0);
      _loop_l = a1.get();
    }
  }
}

/// split_by_sign l pos neg partition with dual accumulators.
std::pair<LoopifyPatterns::list<uint64_t>, LoopifyPatterns::list<uint64_t>>
LoopifyPatterns::split_by_sign_aux(const LoopifyPatterns::list<uint64_t> &l,
                                   uint64_t base,
                                   LoopifyPatterns::list<uint64_t> pos,
                                   LoopifyPatterns::list<uint64_t> neg) {
  LoopifyPatterns::list<uint64_t> _loop_neg = std::move(neg);
  LoopifyPatterns::list<uint64_t> _loop_pos = std::move(pos);
  const LoopifyPatterns::list<uint64_t> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<typename LoopifyPatterns::list<uint64_t>::Nil>(
            _loop_l->v())) {
      return std::make_pair(std::move(_loop_pos), std::move(_loop_neg));
    } else {
      const auto &[a0, a1] =
          std::get<typename LoopifyPatterns::list<uint64_t>::Cons>(
              _loop_l->v());
      if (base <= a0) {
        _loop_pos = list<uint64_t>::cons(a0, std::move(_loop_pos));
        _loop_l = a1.get();
      } else {
        _loop_neg = list<uint64_t>::cons(a0, std::move(_loop_neg));
        _loop_l = a1.get();
      }
    }
  }
}

std::pair<LoopifyPatterns::list<uint64_t>, LoopifyPatterns::list<uint64_t>>
LoopifyPatterns::split_by_sign(const LoopifyPatterns::list<uint64_t> &l,
                               uint64_t base) {
  return split_by_sign_aux(l, base, list<uint64_t>::nil(),
                           list<uint64_t>::nil());
}

/// guard_accum acc l multiple when-style guards with different logic.
uint64_t
LoopifyPatterns::guard_accum(uint64_t acc,
                             const LoopifyPatterns::list<uint64_t> &l) {
  const LoopifyPatterns::list<uint64_t> *_loop_l = &l;
  uint64_t _loop_acc = std::move(acc);
  while (true) {
    if (std::holds_alternative<typename LoopifyPatterns::list<uint64_t>::Nil>(
            _loop_l->v())) {
      return _loop_acc;
    } else {
      const auto &[a0, a1] =
          std::get<typename LoopifyPatterns::list<uint64_t>::Cons>(
              _loop_l->v());
      if (UINT64_C(100) < a0) {
        _loop_l = a1.get();
        _loop_acc = (_loop_acc * UINT64_C(2));
      } else {
        if (UINT64_C(50) < a0) {
          _loop_l = a1.get();
          _loop_acc = (_loop_acc + a0);
        } else {
          if (UINT64_C(0) < a0) {
            _loop_l = a1.get();
            _loop_acc = (_loop_acc + 1);
          } else {
            _loop_l = a1.get();
          }
        }
      }
    }
  }
}

/// cons_computed n l cons with conditional parameter change.
LoopifyPatterns::list<uint64_t> LoopifyPatterns::cons_computed(
    uint64_t n,
    const LoopifyPatterns::list<uint64_t>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const LoopifyPatterns::list<uint64_t> *l;
    uint64_t n;
  };

  /// _Resume_Cons: saves [a0], resumes after recursive call with _result.
  struct _Resume_Cons {
    uint64_t a0;
  };

  using _Frame = std::variant<_Enter, _Resume_Cons>;
  LoopifyPatterns::list<uint64_t> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l, n});
  /// Loopified cons_computed: _Enter -> _Resume_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const LoopifyPatterns::list<uint64_t> &l = *_f.l;
      uint64_t n = _f.n;
      if (std::holds_alternative<typename LoopifyPatterns::list<uint64_t>::Nil>(
              l.v())) {
        _result = list<uint64_t>::nil();
      } else {
        const auto &[a0, a1] =
            std::get<typename LoopifyPatterns::list<uint64_t>::Cons>(l.v());
        uint64_t next_n;
        if (UINT64_C(0) < n) {
          next_n = (((n - UINT64_C(1)) > n ? 0 : (n - UINT64_C(1))));
        } else {
          next_n = n;
        }
        _stack.emplace_back(_Resume_Cons{a0});
        _stack.emplace_back(_Enter{a1.get(), next_n});
      }
    } else {
      auto _f = std::move(std::get<_Resume_Cons>(_frame));
      _result = list<uint64_t>::cons(_f.a0, std::move(_result));
    }
  }
  return _result;
}

/// mod_pattern n recursive call in mod expression.
uint64_t LoopifyPatterns::mod_pattern(
    uint64_t
        n) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    uint64_t n;
  };

  /// _Resume_m: saves [n_], resumes after recursive call with _result.
  struct _Resume_m {
    uint64_t n_;
  };

  using _Frame = std::variant<_Enter, _Resume_m>;
  uint64_t _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{n});
  /// Loopified mod_pattern: _Enter -> _Resume_m.
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
        if (n_ <= 0) {
          _result = UINT64_C(1);
        } else {
          uint64_t m = n_ - 1;
          _stack.emplace_back(_Resume_m{n_});
          _stack.emplace_back(_Enter{m});
        }
      }
    } else {
      auto _f = std::move(std::get<_Resume_m>(_frame));
      _result =
          ((std::move(_result) + 1) ? _f.n_ % (std::move(_result) + 1) : _f.n_);
    }
  }
  return _result;
}

/// alternating_ops n alternating operations based on modulo.
uint64_t LoopifyPatterns::alternating_ops(
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
        uint64_t m = n - 1;
        if ((UINT64_C(2) ? n % UINT64_C(2) : n) == UINT64_C(0)) {
          _stack.emplace_back(_Resume1{n});
          _stack.emplace_back(_Enter{m});
        } else {
          _stack.emplace_back(_Resume2{(n * UINT64_C(2))});
          _stack.emplace_back(_Enter{m});
        }
      }
    } else if (std::holds_alternative<_Resume1>(_frame)) {
      auto _f = std::move(std::get<_Resume1>(_frame));
      _result = (_f.n + std::move(_result));
    } else {
      auto _f = std::move(std::get<_Resume2>(_frame));
      _result = (_f._s0 + std::move(_result));
    }
  }
  return _result;
}

/// replace_at idx value l replace element at index.
LoopifyPatterns::list<uint64_t> LoopifyPatterns::replace_at(
    uint64_t idx, uint64_t value,
    const LoopifyPatterns::list<uint64_t>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const LoopifyPatterns::list<uint64_t> *l;
    uint64_t idx;
  };

  /// _Resume_i: saves [a0], resumes after recursive call with _result.
  struct _Resume_i {
    uint64_t a0;
  };

  using _Frame = std::variant<_Enter, _Resume_i>;
  LoopifyPatterns::list<uint64_t> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l, idx});
  /// Loopified replace_at: _Enter -> _Resume_i.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const LoopifyPatterns::list<uint64_t> &l = *_f.l;
      uint64_t idx = _f.idx;
      if (std::holds_alternative<typename LoopifyPatterns::list<uint64_t>::Nil>(
              l.v())) {
        _result = list<uint64_t>::nil();
      } else {
        const auto &[a0, a1] =
            std::get<typename LoopifyPatterns::list<uint64_t>::Cons>(l.v());
        if (idx <= 0) {
          _result = list<uint64_t>::cons(value, *a1);
        } else {
          uint64_t i = idx - 1;
          _stack.emplace_back(_Resume_i{a0});
          _stack.emplace_back(_Enter{a1.get(), i});
        }
      }
    } else {
      auto _f = std::move(std::get<_Resume_i>(_frame));
      _result = list<uint64_t>::cons(_f.a0, std::move(_result));
    }
  }
  return _result;
}

/// nested_pattern l three-element tuple pattern.
uint64_t LoopifyPatterns::nested_pattern(
    const LoopifyPatterns::list<
        std::pair<std::pair<uint64_t, uint64_t>, uint64_t>>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const LoopifyPatterns::list<
        std::pair<std::pair<uint64_t, uint64_t>, uint64_t>> *l;
  };

  /// _Resume_a: saves [a, b, c], resumes after recursive call with _result.
  struct _Resume_a {
    uint64_t a;
    uint64_t b;
    uint64_t c;
  };

  using _Frame = std::variant<_Enter, _Resume_a>;
  uint64_t _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l});
  /// Loopified nested_pattern: _Enter -> _Resume_a.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const LoopifyPatterns::list<
          std::pair<std::pair<uint64_t, uint64_t>, uint64_t>> &l = *_f.l;
      if (std::holds_alternative<typename LoopifyPatterns::list<
              std::pair<std::pair<uint64_t, uint64_t>, uint64_t>>::Nil>(
              l.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] = std::get<typename LoopifyPatterns::list<
            std::pair<std::pair<uint64_t, uint64_t>, uint64_t>>::Cons>(l.v());
        const auto &[p0, c] = a0;
        const auto &[a, b] = p0;
        _stack.emplace_back(_Resume_a{a, b, c});
        _stack.emplace_back(_Enter{a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Resume_a>(_frame));
      _result = (_f.a + (_f.b + (_f.c + std::move(_result))));
    }
  }
  return _result;
}

/// let_nested n let with nested let in binding.
uint64_t LoopifyPatterns::let_nested(
    uint64_t
        n) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    uint64_t n;
  };

  /// _Resume_m: saves [a], resumes after recursive call with _result.
  struct _Resume_m {
    uint64_t a;
  };

  using _Frame = std::variant<_Enter, _Resume_m>;
  uint64_t _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{n});
  /// Loopified let_nested: _Enter -> _Resume_m.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      uint64_t n = _f.n;
      if (n <= 0) {
        _result = UINT64_C(0);
      } else {
        uint64_t m = n - 1;
        uint64_t a = (m + 1);
        _stack.emplace_back(_Resume_m{a});
        _stack.emplace_back(_Enter{m});
      }
    } else {
      auto _f = std::move(std::get<_Resume_m>(_frame));
      _result = (_f.a + std::move(_result));
    }
  }
  return _result;
}

/// Helper: list length.
uint64_t LoopifyPatterns::list_len(
    const LoopifyPatterns::list<uint64_t>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const LoopifyPatterns::list<uint64_t> *l;
  };

  /// _Resume_Cons: resumes after recursive call with _result.
  struct _Resume_Cons {};

  using _Frame = std::variant<_Enter, _Resume_Cons>;
  uint64_t _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l});
  /// Loopified list_len: _Enter -> _Resume_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const LoopifyPatterns::list<uint64_t> &l = *_f.l;
      if (std::holds_alternative<typename LoopifyPatterns::list<uint64_t>::Nil>(
              l.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] =
            std::get<typename LoopifyPatterns::list<uint64_t>::Cons>(l.v());
        _stack.emplace_back(_Resume_Cons{});
        _stack.emplace_back(_Enter{a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Resume_Cons>(_frame));
      _result = (std::move(_result) + 1);
    }
  }
  return _result;
}

/// process_twice l applies recursion twice: process(process(xs)).
LoopifyPatterns::list<uint64_t> LoopifyPatterns::process_twice_fuel(
    uint64_t fuel,
    LoopifyPatterns::list<uint64_t>
        l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    LoopifyPatterns::list<uint64_t> l;
    uint64_t fuel;
  };

  /// _Cont_Cons: saves [a0, f], resumes after recursive call, then processes
  /// rest.
  struct _Cont_Cons {
    uint64_t a0;
    uint64_t f;
  };

  /// _Cont_Cons_1: saves [a0], resumes after recursive call, then processes
  /// rest.
  struct _Cont_Cons_1 {
    uint64_t a0;
  };

  using _Frame = std::variant<_Enter, _Cont_Cons, _Cont_Cons_1>;
  LoopifyPatterns::list<uint64_t> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{std::move(l), fuel});
  /// Loopified process_twice_fuel: _Enter -> _Cont_Cons -> _Cont_Cons_1.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      LoopifyPatterns::list<uint64_t> l = std::move(_f.l);
      uint64_t fuel = _f.fuel;
      if (fuel <= 0) {
        _result = std::move(l);
      } else {
        uint64_t f = fuel - 1;
        if (std::holds_alternative<
                typename LoopifyPatterns::list<uint64_t>::Nil>(l.v_mut())) {
          _result = list<uint64_t>::nil();
        } else {
          auto &[a0, a1] =
              std::get<typename LoopifyPatterns::list<uint64_t>::Cons>(
                  l.v_mut());
          _stack.emplace_back(_Cont_Cons{a0, f});
          _stack.emplace_back(_Enter{*a1, f});
        }
      }
    } else if (std::holds_alternative<_Cont_Cons>(_frame)) {
      auto _f = std::move(std::get<_Cont_Cons>(_frame));
      uint64_t a0 = _f.a0;
      uint64_t f = _f.f;
      LoopifyPatterns::list<uint64_t> first = std::move(_result);
      _stack.emplace_back(_Cont_Cons_1{a0});
      _stack.emplace_back(_Enter{std::move(first), f});
    } else {
      auto _f = std::move(std::get<_Cont_Cons_1>(_frame));
      uint64_t a0 = _f.a0;
      LoopifyPatterns::list<uint64_t> second = std::move(_result);
      _result = list<uint64_t>::cons(std::move(a0), std::move(second));
    }
  }
  return _result;
}

LoopifyPatterns::list<uint64_t>
LoopifyPatterns::process_twice(const LoopifyPatterns::list<uint64_t> &l) {
  return process_twice_fuel(UINT64_C(100), l);
}

/// as_guard l uses as-pattern with guard (length check).
LoopifyPatterns::list<uint64_t> LoopifyPatterns::as_guard_fuel(
    uint64_t fuel,
    const LoopifyPatterns::list<uint64_t>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const LoopifyPatterns::list<uint64_t> *l;
    uint64_t fuel;
  };

  /// _Resume1: saves [a0], resumes after recursive call with _result.
  struct _Resume1 {
    uint64_t a0;
  };

  using _Frame = std::variant<_Enter, _Resume1>;
  LoopifyPatterns::list<uint64_t> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l, fuel});
  /// Loopified as_guard_fuel: _Enter -> _Resume1.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const LoopifyPatterns::list<uint64_t> &l = *_f.l;
      uint64_t fuel = _f.fuel;
      if (fuel <= 0) {
        _result = list<uint64_t>::nil();
      } else {
        uint64_t f = fuel - 1;
        if (std::holds_alternative<
                typename LoopifyPatterns::list<uint64_t>::Nil>(l.v())) {
          _result = list<uint64_t>::nil();
        } else {
          const auto &[a0, a1] =
              std::get<typename LoopifyPatterns::list<uint64_t>::Cons>(l.v());
          LoopifyPatterns::list<uint64_t> all = list<uint64_t>::cons(a0, *a1);
          if (UINT64_C(3) < list_len(std::move(all))) {
            _stack.emplace_back(_Resume1{a0});
            _stack.emplace_back(_Enter{a1.get(), f});
          } else {
            _stack.emplace_back(_Enter{a1.get(), f});
          }
        }
      }
    } else {
      auto _f = std::move(std::get<_Resume1>(_frame));
      _result = list<uint64_t>::cons(_f.a0, std::move(_result));
    }
  }
  return _result;
}

LoopifyPatterns::list<uint64_t>
LoopifyPatterns::as_guard(const LoopifyPatterns::list<uint64_t> &l) {
  return as_guard_fuel(UINT64_C(100), l);
}

/// quad_sum_pattern l pattern with 4-way split.
uint64_t LoopifyPatterns::quad_sum_pattern(
    const LoopifyPatterns::list<uint64_t>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const LoopifyPatterns::list<uint64_t> *l;
  };

  /// _Resume_Cons: saves [_s0, _s1], resumes after recursive call with _result.
  struct _Resume_Cons {
    uint64_t _s0;
    uint64_t _s1;
  };

  using _Frame = std::variant<_Enter, _Resume_Cons>;
  uint64_t _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l});
  /// Loopified quad_sum_pattern: _Enter -> _Resume_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const LoopifyPatterns::list<uint64_t> &l = *_f.l;
      if (std::holds_alternative<typename LoopifyPatterns::list<uint64_t>::Nil>(
              l.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] =
            std::get<typename LoopifyPatterns::list<uint64_t>::Cons>(l.v());
        auto &&_sv0 = *a1;
        if (std::holds_alternative<
                typename LoopifyPatterns::list<uint64_t>::Nil>(_sv0.v())) {
          _result = std::move(a0);
        } else {
          const auto &[a00, a10] =
              std::get<typename LoopifyPatterns::list<uint64_t>::Cons>(
                  _sv0.v());
          auto &&_sv1 = *a10;
          if (std::holds_alternative<
                  typename LoopifyPatterns::list<uint64_t>::Nil>(_sv1.v())) {
            _result = (a0 + a00);
          } else {
            const auto &[a01, a11] =
                std::get<typename LoopifyPatterns::list<uint64_t>::Cons>(
                    _sv1.v());
            auto &&_sv2 = *a11;
            if (std::holds_alternative<
                    typename LoopifyPatterns::list<uint64_t>::Nil>(_sv2.v())) {
              _result = (a0 + (a00 + a01));
            } else {
              const auto &[a02, a12] =
                  std::get<typename LoopifyPatterns::list<uint64_t>::Cons>(
                      _sv2.v());
              _stack.emplace_back(_Resume_Cons{(a0 + a00), (a01 + a02)});
              _stack.emplace_back(_Enter{a12.get()});
            }
          }
        }
      }
    } else {
      auto _f = std::move(std::get<_Resume_Cons>(_frame));
      _result = (_f._s0 + (_f._s1 + std::move(_result)));
    }
  }
  return _result;
}

/// multi_guard l demonstrates pattern with multiple conditional branches.
uint64_t LoopifyPatterns::multi_guard(
    const LoopifyPatterns::list<uint64_t>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const LoopifyPatterns::list<uint64_t> *l;
  };

  /// _Cont_Cons: saves [a0], resumes after recursive call, then processes rest.
  struct _Cont_Cons {
    uint64_t a0;
  };

  using _Frame = std::variant<_Enter, _Cont_Cons>;
  uint64_t _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l});
  /// Loopified multi_guard: _Enter -> _Cont_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const LoopifyPatterns::list<uint64_t> &l = *_f.l;
      if (std::holds_alternative<typename LoopifyPatterns::list<uint64_t>::Nil>(
              l.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] =
            std::get<typename LoopifyPatterns::list<uint64_t>::Cons>(l.v());
        _stack.emplace_back(_Cont_Cons{a0});
        _stack.emplace_back(_Enter{a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Cont_Cons>(_frame));
      uint64_t a0 = _f.a0;
      uint64_t rest = std::move(_result);
      if (UINT64_C(10) < a0) {
        _result = (a0 + rest);
      } else {
        if (UINT64_C(0) < a0) {
          _result = std::move(rest);
        } else {
          _result = (UINT64_C(1) + rest);
        }
      }
    }
  }
  return _result;
}

/// Internal helper for double_append.
LoopifyPatterns::list<uint64_t> LoopifyPatterns::append_lists(
    const LoopifyPatterns::list<uint64_t> &l1,
    LoopifyPatterns::list<uint64_t>
        l2) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    LoopifyPatterns::list<uint64_t> l2;
    const LoopifyPatterns::list<uint64_t> *l1;
  };

  /// _Resume_Cons: saves [a0], resumes after recursive call with _result.
  struct _Resume_Cons {
    uint64_t a0;
  };

  using _Frame = std::variant<_Enter, _Resume_Cons>;
  LoopifyPatterns::list<uint64_t> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{std::move(l2), &l1});
  /// Loopified append_lists: _Enter -> _Resume_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      LoopifyPatterns::list<uint64_t> l2 = std::move(_f.l2);
      const LoopifyPatterns::list<uint64_t> &l1 = *_f.l1;
      if (std::holds_alternative<typename LoopifyPatterns::list<uint64_t>::Nil>(
              l1.v())) {
        _result = std::move(l2);
      } else {
        const auto &[a0, a1] =
            std::get<typename LoopifyPatterns::list<uint64_t>::Cons>(l1.v());
        _stack.emplace_back(_Resume_Cons{a0});
        _stack.emplace_back(_Enter{std::move(l2), a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Resume_Cons>(_frame));
      _result = list<uint64_t>::cons(_f.a0, std::move(_result));
    }
  }
  return _result;
}

/// double_append l1 l2 uses recursive result twice: h :: (rest @ rest).
LoopifyPatterns::list<uint64_t> LoopifyPatterns::double_append(
    const LoopifyPatterns::list<uint64_t> &l1,
    LoopifyPatterns::list<uint64_t>
        l2) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    LoopifyPatterns::list<uint64_t> l2;
    const LoopifyPatterns::list<uint64_t> *l1;
  };

  /// _Cont_Cons: saves [a0], resumes after recursive call, then processes rest.
  struct _Cont_Cons {
    uint64_t a0;
  };

  using _Frame = std::variant<_Enter, _Cont_Cons>;
  LoopifyPatterns::list<uint64_t> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{std::move(l2), &l1});
  /// Loopified double_append: _Enter -> _Cont_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      LoopifyPatterns::list<uint64_t> l2 = std::move(_f.l2);
      const LoopifyPatterns::list<uint64_t> &l1 = *_f.l1;
      if (std::holds_alternative<typename LoopifyPatterns::list<uint64_t>::Nil>(
              l1.v())) {
        _result = std::move(l2);
      } else {
        const auto &[a0, a1] =
            std::get<typename LoopifyPatterns::list<uint64_t>::Cons>(l1.v());
        _stack.emplace_back(_Cont_Cons{a0});
        _stack.emplace_back(_Enter{std::move(l2), a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Cont_Cons>(_frame));
      uint64_t a0 = _f.a0;
      LoopifyPatterns::list<uint64_t> rest = std::move(_result);
      _result = list<uint64_t>::cons(a0, append_lists(rest, rest));
    }
  }
  return _result;
}

/// process_twice_alt l applies transformation twice on recursive result.
LoopifyPatterns::list<uint64_t> LoopifyPatterns::process_twice_alt_fuel(
    uint64_t fuel,
    LoopifyPatterns::list<uint64_t>
        l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    LoopifyPatterns::list<uint64_t> l;
    uint64_t fuel;
  };

  /// _Cont_Cons: saves [a0, f], resumes after recursive call, then processes
  /// rest.
  struct _Cont_Cons {
    uint64_t a0;
    uint64_t f;
  };

  /// _Cont_Cons_1: saves [a0], resumes after recursive call, then processes
  /// rest.
  struct _Cont_Cons_1 {
    uint64_t a0;
  };

  using _Frame = std::variant<_Enter, _Cont_Cons, _Cont_Cons_1>;
  LoopifyPatterns::list<uint64_t> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{std::move(l), fuel});
  /// Loopified process_twice_alt_fuel: _Enter -> _Cont_Cons -> _Cont_Cons_1.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      LoopifyPatterns::list<uint64_t> l = std::move(_f.l);
      uint64_t fuel = _f.fuel;
      if (fuel <= 0) {
        _result = std::move(l);
      } else {
        uint64_t f = fuel - 1;
        if (std::holds_alternative<
                typename LoopifyPatterns::list<uint64_t>::Nil>(l.v_mut())) {
          _result = list<uint64_t>::nil();
        } else {
          auto &[a0, a1] =
              std::get<typename LoopifyPatterns::list<uint64_t>::Cons>(
                  l.v_mut());
          _stack.emplace_back(_Cont_Cons{a0, f});
          _stack.emplace_back(_Enter{*a1, f});
        }
      }
    } else if (std::holds_alternative<_Cont_Cons>(_frame)) {
      auto _f = std::move(std::get<_Cont_Cons>(_frame));
      uint64_t a0 = _f.a0;
      uint64_t f = _f.f;
      LoopifyPatterns::list<uint64_t> once = std::move(_result);
      _stack.emplace_back(_Cont_Cons_1{a0});
      _stack.emplace_back(_Enter{std::move(once), f});
    } else {
      auto _f = std::move(std::get<_Cont_Cons_1>(_frame));
      uint64_t a0 = _f.a0;
      LoopifyPatterns::list<uint64_t> twice = std::move(_result);
      _result = list<uint64_t>::cons(std::move(a0), std::move(twice));
    }
  }
  return _result;
}

LoopifyPatterns::list<uint64_t>
LoopifyPatterns::process_twice_alt(const LoopifyPatterns::list<uint64_t> &l) {
  return process_twice_alt_fuel(UINT64_C(100), l);
}

/// sum_if_positive_else_double l conditional logic on each element.
uint64_t LoopifyPatterns::sum_if_positive_else_double(
    const LoopifyPatterns::list<uint64_t>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const LoopifyPatterns::list<uint64_t> *l;
  };

  /// _Cont_Cons: saves [a0], resumes after recursive call, then processes rest.
  struct _Cont_Cons {
    uint64_t a0;
  };

  using _Frame = std::variant<_Enter, _Cont_Cons>;
  uint64_t _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l});
  /// Loopified sum_if_positive_else_double: _Enter -> _Cont_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const LoopifyPatterns::list<uint64_t> &l = *_f.l;
      if (std::holds_alternative<typename LoopifyPatterns::list<uint64_t>::Nil>(
              l.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] =
            std::get<typename LoopifyPatterns::list<uint64_t>::Cons>(l.v());
        _stack.emplace_back(_Cont_Cons{a0});
        _stack.emplace_back(_Enter{a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Cont_Cons>(_frame));
      uint64_t a0 = _f.a0;
      uint64_t rest = std::move(_result);
      if (a0 == UINT64_C(0)) {
        _result = ((UINT64_C(2) * a0) + rest);
      } else {
        _result = (a0 + rest);
      }
    }
  }
  return _result;
}

/// merge_alternating l1 l2 merges two lists by alternating elements.
LoopifyPatterns::list<uint64_t> LoopifyPatterns::merge_alternating(
    LoopifyPatterns::list<uint64_t> l1,
    LoopifyPatterns::list<uint64_t>
        l2) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    LoopifyPatterns::list<uint64_t> l2;
    LoopifyPatterns::list<uint64_t> l1;
  };

  /// _Resume_Cons: saves [a0, a00], resumes after recursive call with _result.
  struct _Resume_Cons {
    uint64_t a0;
    uint64_t a00;
  };

  using _Frame = std::variant<_Enter, _Resume_Cons>;
  LoopifyPatterns::list<uint64_t> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{std::move(l2), std::move(l1)});
  /// Loopified merge_alternating: _Enter -> _Resume_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      LoopifyPatterns::list<uint64_t> l2 = std::move(_f.l2);
      LoopifyPatterns::list<uint64_t> l1 = std::move(_f.l1);
      if (std::holds_alternative<typename LoopifyPatterns::list<uint64_t>::Nil>(
              l1.v_mut())) {
        _result = std::move(l2);
      } else {
        auto &[a0, a1] =
            std::get<typename LoopifyPatterns::list<uint64_t>::Cons>(
                l1.v_mut());
        if (std::holds_alternative<
                typename LoopifyPatterns::list<uint64_t>::Nil>(l2.v_mut())) {
          _result = std::move(l1);
        } else {
          auto &[a00, a10] =
              std::get<typename LoopifyPatterns::list<uint64_t>::Cons>(
                  l2.v_mut());
          _stack.emplace_back(_Resume_Cons{std::move(a0), std::move(a00)});
          _stack.emplace_back(_Enter{*a10, *a1});
        }
      }
    } else {
      auto _f = std::move(std::get<_Resume_Cons>(_frame));
      _result = list<uint64_t>::cons(
          _f.a0, list<uint64_t>::cons(_f.a00, std::move(_result)));
    }
  }
  return _result;
}

/// four_elem l four-element destructuring pattern with fallback cases.
uint64_t LoopifyPatterns::four_elem(
    const LoopifyPatterns::list<uint64_t>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const LoopifyPatterns::list<uint64_t> *l;
  };

  /// _Resume_Cons: saves [a0, a00, a01, a02], resumes after recursive call with
  /// _result.
  struct _Resume_Cons {
    uint64_t a0;
    uint64_t a00;
    uint64_t a01;
    uint64_t a02;
  };

  using _Frame = std::variant<_Enter, _Resume_Cons>;
  uint64_t _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l});
  /// Loopified four_elem: _Enter -> _Resume_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const LoopifyPatterns::list<uint64_t> &l = *_f.l;
      if (std::holds_alternative<typename LoopifyPatterns::list<uint64_t>::Nil>(
              l.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] =
            std::get<typename LoopifyPatterns::list<uint64_t>::Cons>(l.v());
        auto &&_sv0 = *a1;
        if (std::holds_alternative<
                typename LoopifyPatterns::list<uint64_t>::Nil>(_sv0.v())) {
          _result = UINT64_C(1);
        } else {
          const auto &[a00, a10] =
              std::get<typename LoopifyPatterns::list<uint64_t>::Cons>(
                  _sv0.v());
          auto &&_sv1 = *a10;
          if (std::holds_alternative<
                  typename LoopifyPatterns::list<uint64_t>::Nil>(_sv1.v())) {
            _result = UINT64_C(2);
          } else {
            const auto &[a01, a11] =
                std::get<typename LoopifyPatterns::list<uint64_t>::Cons>(
                    _sv1.v());
            auto &&_sv2 = *a11;
            if (std::holds_alternative<
                    typename LoopifyPatterns::list<uint64_t>::Nil>(_sv2.v())) {
              _result = UINT64_C(3);
            } else {
              const auto &[a02, a12] =
                  std::get<typename LoopifyPatterns::list<uint64_t>::Cons>(
                      _sv2.v());
              _stack.emplace_back(_Resume_Cons{a0, a00, a01, a02});
              _stack.emplace_back(_Enter{a12.get()});
            }
          }
        }
      }
    } else {
      auto _f = std::move(std::get<_Resume_Cons>(_frame));
      _result = (_f.a0 + (_f.a00 + (_f.a01 + (_f.a02 + std::move(_result)))));
    }
  }
  return _result;
}
