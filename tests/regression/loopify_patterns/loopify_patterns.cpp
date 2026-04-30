#include <loopify_patterns.h>

/// Complex control flow and pattern matching edge cases.
/// multi_let n multiple sequential let bindings before recursion.
unsigned int LoopifyPatterns::multi_let(const unsigned int &n) {
  struct _Enter {
    unsigned int n;
  };

  struct _Call1 {
    unsigned int _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{n});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const unsigned int &n = _f.n;
      if (n <= 0) {
        _result = 0u;
      } else {
        unsigned int m = n - 1;
        unsigned int b = (m * 2u);
        unsigned int c = (b + 3u);
        _stack.emplace_back(_Call1{c});
        _stack.emplace_back(_Enter{m});
      }
    } else {
      auto _f = std::move(std::get<_Call1>(_frame));
      _result = (_f._s0 + _result);
    }
  }
  return _result;
}

/// nested_if n deeply nested if-then-else with recursion at different depths.
unsigned int LoopifyPatterns::nested_if_fuel(const unsigned int &fuel,
                                             const unsigned int &n) {
  unsigned int _result;
  unsigned int _loop_n = n;
  unsigned int _loop_fuel = fuel;
  while (true) {
    if (_loop_fuel <= 0) {
      _result = 0u;
      break;
    } else {
      unsigned int f = _loop_fuel - 1;
      if (_loop_n <= 0) {
        _result = 0u;
        break;
      } else {
        unsigned int n_ = _loop_n - 1;
        if (n_ <= 0) {
          _result = 1u;
          break;
        } else {
          unsigned int m = n_ - 1;
          if ((2u ? n_ % 2u : n_) == 0u) {
            if (10u < n_) {
              unsigned int _next_n = (2u ? n_ / 2u : 0);
              unsigned int _next_fuel = f;
              _loop_n = std::move(_next_n);
              _loop_fuel = std::move(_next_fuel);
            } else {
              unsigned int _next_n = m;
              unsigned int _next_fuel = f;
              _loop_n = std::move(_next_n);
              _loop_fuel = std::move(_next_fuel);
            }
          } else {
            unsigned int _next_n =
                (m == 0u ? 0u : (((m - 1u) > m ? 0 : (m - 1u))));
            unsigned int _next_fuel = f;
            _loop_n = std::move(_next_n);
            _loop_fuel = std::move(_next_fuel);
          }
        }
      }
    }
  }
  return _result;
}

unsigned int LoopifyPatterns::nested_if(const unsigned int &n) {
  return nested_if_fuel(1000u, n);
}

/// deep_nest n deeply nested function application.
unsigned int LoopifyPatterns::deep_nest(const unsigned int &n) {
  struct _Enter {
    unsigned int n;
  };

  struct _Call1 {
    decltype(1u) _s0;
    decltype(1u) _s1;
    decltype(1u) _s2;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{n});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const unsigned int &n = _f.n;
      if (n <= 0) {
        _result = 0u;
      } else {
        unsigned int m = n - 1;
        _stack.emplace_back(_Call1{1u, 1u, 1u});
        _stack.emplace_back(_Enter{m});
      }
    } else {
      auto _f = std::move(std::get<_Call1>(_frame));
      _result = (_f._s0 + (_f._s1 + (_f._s2 + _result)));
    }
  }
  return _result;
}

/// bool_chain n target multiple recursive calls in || chain.
bool LoopifyPatterns::bool_chain_fuel(const unsigned int &fuel,
                                      const unsigned int &n,
                                      const unsigned int &target) {
  struct _Enter {
    unsigned int n;
    unsigned int fuel;
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
  _stack.reserve(16);
  _stack.emplace_back(_Enter{n, fuel});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const unsigned int &n = _f.n;
      const unsigned int &fuel = _f.fuel;
      if (fuel <= 0) {
        _result = false;
      } else {
        unsigned int f = fuel - 1;
        if (n == 0u) {
          _result = false;
        } else {
          if (n == target) {
            _result = true;
          } else {
            if (n == 1u) {
              _result = false;
            } else {
              _stack.emplace_back(_Call1{(((n - 1u) > n ? 0 : (n - 1u))), f});
              _stack.emplace_back(_Enter{(((n - 2u) > n ? 0 : (n - 2u))), f});
            }
          }
        }
      }
    } else if (std::holds_alternative<_Call1>(_frame)) {
      auto _f = std::move(std::get<_Call1>(_frame));
      _stack.emplace_back(_Call2{_result});
      _stack.emplace_back(_Enter{_f._s0, _f._s1});
    } else {
      auto _f = std::move(std::get<_Call2>(_frame));
      _result = (_result || _f._s0);
    }
  }
  return _result;
}

bool LoopifyPatterns::bool_chain(const unsigned int &n,
                                 const unsigned int &target) {
  return bool_chain_fuel(1000u, n, target);
}

/// chained_comp n boolean result with double recursion.
bool LoopifyPatterns::chained_comp(const unsigned int &n) {
  struct _Enter {
    unsigned int n;
  };

  struct _Call1 {
    unsigned int _s0;
  };

  struct _Call2 {
    bool _s0;
  };

  using _Frame = std::variant<_Enter, _Call1, _Call2>;
  bool _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{n});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const unsigned int &n = _f.n;
      if (n <= 0) {
        _result = true;
      } else {
        unsigned int n_ = n - 1;
        if (n_ <= 0) {
          _result = true;
        } else {
          unsigned int m = n_ - 1;
          _stack.emplace_back(_Call1{n_});
          _stack.emplace_back(_Enter{m});
        }
      }
    } else if (std::holds_alternative<_Call1>(_frame)) {
      auto _f = std::move(std::get<_Call1>(_frame));
      _stack.emplace_back(_Call2{_result});
      _stack.emplace_back(_Enter{_f._s0});
    } else {
      auto _f = std::move(std::get<_Call2>(_frame));
      _result = (_result && _f._s0);
    }
  }
  return _result;
}

/// tuple_constr n recursive calls in multiple tuple positions.
std::pair<std::pair<unsigned int, unsigned int>, unsigned int>
LoopifyPatterns::tuple_constr(const unsigned int &n) {
  struct _Enter {
    unsigned int n;
  };

  struct _Call1 {
    unsigned int _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::pair<std::pair<unsigned int, unsigned int>, unsigned int> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{n});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const unsigned int &n = _f.n;
      if (n <= 0) {
        _result = std::make_pair(std::make_pair(0u, 0u), 0u);
      } else {
        unsigned int m = n - 1;
        _stack.emplace_back(_Call1{n});
        _stack.emplace_back(_Enter{m});
      }
    } else {
      auto _f = std::move(std::get<_Call1>(_frame));
      const unsigned int &n = _f._s0;
      const std::pair<unsigned int, unsigned int> &p = _result.first;
      const unsigned int &c = _result.second;
      const unsigned int &a = p.first;
      const unsigned int &b = p.second;
      _result = std::make_pair(std::make_pair((a + 1), (b + n)), (c + (n * n)));
    }
  }
  return _result;
}

/// sum_prod_count l a_sum a_prod a_count multiple accumulator updates.
std::pair<std::pair<unsigned int, unsigned int>, unsigned int>
LoopifyPatterns::sum_prod_count(const LoopifyPatterns::list<unsigned int> &l,
                                unsigned int a_sum, unsigned int a_prod,
                                unsigned int a_count) {
  std::pair<std::pair<unsigned int, unsigned int>, unsigned int> _result;
  unsigned int _loop_a_count = std::move(a_count);
  unsigned int _loop_a_prod = std::move(a_prod);
  unsigned int _loop_a_sum = std::move(a_sum);
  const LoopifyPatterns::list<unsigned int> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<
            typename LoopifyPatterns::list<unsigned int>::Nil>(_loop_l->v())) {
      _result = std::make_pair(std::make_pair(_loop_a_sum, _loop_a_prod),
                               _loop_a_count);
      break;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename LoopifyPatterns::list<unsigned int>::Cons>(
              _loop_l->v());
      unsigned int _next_a_count = (_loop_a_count + 1);
      unsigned int _next_a_prod = (_loop_a_prod * d_a0);
      unsigned int _next_a_sum = (_loop_a_sum + d_a0);
      const LoopifyPatterns::list<unsigned int> *_next_l = d_a1.get();
      _loop_a_count = std::move(_next_a_count);
      _loop_a_prod = std::move(_next_a_prod);
      _loop_a_sum = std::move(_next_a_sum);
      _loop_l = _next_l;
    }
  }
  return _result;
}

/// split_by_sign l pos neg partition with dual accumulators.
std::pair<LoopifyPatterns::list<unsigned int>,
          LoopifyPatterns::list<unsigned int>>
LoopifyPatterns::split_by_sign_aux(const LoopifyPatterns::list<unsigned int> &l,
                                   const unsigned int &base,
                                   LoopifyPatterns::list<unsigned int> pos,
                                   LoopifyPatterns::list<unsigned int> neg) {
  std::pair<LoopifyPatterns::list<unsigned int>,
            LoopifyPatterns::list<unsigned int>>
      _result;
  LoopifyPatterns::list<unsigned int> _loop_neg = std::move(neg);
  LoopifyPatterns::list<unsigned int> _loop_pos = std::move(pos);
  const LoopifyPatterns::list<unsigned int> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<
            typename LoopifyPatterns::list<unsigned int>::Nil>(_loop_l->v())) {
      _result = std::make_pair(std::move(_loop_pos), std::move(_loop_neg));
      break;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename LoopifyPatterns::list<unsigned int>::Cons>(
              _loop_l->v());
      if (base <= d_a0) {
        LoopifyPatterns::list<unsigned int> _next_neg = std::move(_loop_neg);
        LoopifyPatterns::list<unsigned int> _next_pos =
            list<unsigned int>::cons(d_a0, std::move(_loop_pos));
        const LoopifyPatterns::list<unsigned int> *_next_l = d_a1.get();
        _loop_neg = std::move(_next_neg);
        _loop_pos = std::move(_next_pos);
        _loop_l = _next_l;
      } else {
        LoopifyPatterns::list<unsigned int> _next_neg =
            list<unsigned int>::cons(d_a0, std::move(_loop_neg));
        LoopifyPatterns::list<unsigned int> _next_pos = std::move(_loop_pos);
        const LoopifyPatterns::list<unsigned int> *_next_l = d_a1.get();
        _loop_neg = std::move(_next_neg);
        _loop_pos = std::move(_next_pos);
        _loop_l = _next_l;
      }
    }
  }
  return _result;
}

std::pair<LoopifyPatterns::list<unsigned int>,
          LoopifyPatterns::list<unsigned int>>
LoopifyPatterns::split_by_sign(const LoopifyPatterns::list<unsigned int> &l,
                               const unsigned int &base) {
  return split_by_sign_aux(l, base, list<unsigned int>::nil(),
                           list<unsigned int>::nil());
}

/// guard_accum acc l multiple when-style guards with different logic.
unsigned int
LoopifyPatterns::guard_accum(unsigned int acc,
                             const LoopifyPatterns::list<unsigned int> &l) {
  unsigned int _result;
  const LoopifyPatterns::list<unsigned int> *_loop_l = &l;
  unsigned int _loop_acc = std::move(acc);
  while (true) {
    if (std::holds_alternative<
            typename LoopifyPatterns::list<unsigned int>::Nil>(_loop_l->v())) {
      _result = _loop_acc;
      break;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename LoopifyPatterns::list<unsigned int>::Cons>(
              _loop_l->v());
      if (100u < d_a0) {
        const LoopifyPatterns::list<unsigned int> *_next_l = d_a1.get();
        unsigned int _next_acc = (_loop_acc * 2u);
        _loop_l = _next_l;
        _loop_acc = std::move(_next_acc);
      } else {
        if (50u < d_a0) {
          const LoopifyPatterns::list<unsigned int> *_next_l = d_a1.get();
          unsigned int _next_acc = (_loop_acc + d_a0);
          _loop_l = _next_l;
          _loop_acc = std::move(_next_acc);
        } else {
          if (0u < d_a0) {
            const LoopifyPatterns::list<unsigned int> *_next_l = d_a1.get();
            unsigned int _next_acc = (_loop_acc + 1);
            _loop_l = _next_l;
            _loop_acc = std::move(_next_acc);
          } else {
            _loop_l = d_a1.get();
          }
        }
      }
    }
  }
  return _result;
}

/// cons_computed n l cons with conditional parameter change.
LoopifyPatterns::list<unsigned int>
LoopifyPatterns::cons_computed(const unsigned int &n,
                               const LoopifyPatterns::list<unsigned int> &l) {
  std::unique_ptr<LoopifyPatterns::list<unsigned int>> _head{};
  std::unique_ptr<LoopifyPatterns::list<unsigned int>> *_write = &_head;
  const LoopifyPatterns::list<unsigned int> *_loop_l = &l;
  unsigned int _loop_n = n;
  while (true) {
    if (std::holds_alternative<
            typename LoopifyPatterns::list<unsigned int>::Nil>(_loop_l->v())) {
      *(_write) = std::make_unique<LoopifyPatterns::list<unsigned int>>(
          list<unsigned int>::nil());
      break;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename LoopifyPatterns::list<unsigned int>::Cons>(
              _loop_l->v());
      unsigned int next_n;
      if (0u < _loop_n) {
        next_n = (((_loop_n - 1u) > _loop_n ? 0 : (_loop_n - 1u)));
      } else {
        next_n = _loop_n;
      }
      auto _cell = std::make_unique<LoopifyPatterns::list<unsigned int>>(
          typename list<unsigned int>::Cons(d_a0, nullptr));
      *(_write) = std::move(_cell);
      _write =
          &std::get<typename list<unsigned int>::Cons>((*_write)->v_mut()).d_a1;
      const LoopifyPatterns::list<unsigned int> *_next_l = d_a1.get();
      unsigned int _next_n = next_n;
      _loop_l = _next_l;
      _loop_n = std::move(_next_n);
      continue;
    }
  }
  return std::move(*(_head));
}

/// mod_pattern n recursive call in mod expression.
unsigned int LoopifyPatterns::mod_pattern(const unsigned int &n) {
  struct _Enter {
    unsigned int n;
  };

  struct _Call1 {
    unsigned int _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{n});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const unsigned int &n = _f.n;
      if (n <= 0) {
        _result = 1u;
      } else {
        unsigned int n_ = n - 1;
        if (n_ <= 0) {
          _result = 1u;
        } else {
          unsigned int m = n_ - 1;
          _stack.emplace_back(_Call1{n_});
          _stack.emplace_back(_Enter{m});
        }
      }
    } else {
      auto _f = std::move(std::get<_Call1>(_frame));
      _result = ((_result + 1) ? _f._s0 % (_result + 1) : _f._s0);
    }
  }
  return _result;
}

/// alternating_ops n alternating operations based on modulo.
unsigned int LoopifyPatterns::alternating_ops(const unsigned int &n) {
  struct _Enter {
    unsigned int n;
  };

  struct _Call1 {
    unsigned int _s0;
  };

  struct _Call2 {
    decltype((std::declval<const unsigned int &>() * 2u)) _s0;
  };

  using _Frame = std::variant<_Enter, _Call1, _Call2>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{n});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const unsigned int &n = _f.n;
      if (n <= 0) {
        _result = 0u;
      } else {
        unsigned int m = n - 1;
        if ((2u ? n % 2u : n) == 0u) {
          _stack.emplace_back(_Call1{n});
          _stack.emplace_back(_Enter{m});
        } else {
          _stack.emplace_back(_Call2{(n * 2u)});
          _stack.emplace_back(_Enter{m});
        }
      }
    } else if (std::holds_alternative<_Call1>(_frame)) {
      auto _f = std::move(std::get<_Call1>(_frame));
      _result = (_f._s0 + _result);
    } else {
      auto _f = std::move(std::get<_Call2>(_frame));
      _result = (_f._s0 + _result);
    }
  }
  return _result;
}

/// replace_at idx value l replace element at index.
LoopifyPatterns::list<unsigned int>
LoopifyPatterns::replace_at(const unsigned int &idx, unsigned int value,
                            const LoopifyPatterns::list<unsigned int> &l) {
  std::unique_ptr<LoopifyPatterns::list<unsigned int>> _head{};
  std::unique_ptr<LoopifyPatterns::list<unsigned int>> *_write = &_head;
  const LoopifyPatterns::list<unsigned int> *_loop_l = &l;
  unsigned int _loop_idx = idx;
  while (true) {
    if (std::holds_alternative<
            typename LoopifyPatterns::list<unsigned int>::Nil>(_loop_l->v())) {
      *(_write) = std::make_unique<LoopifyPatterns::list<unsigned int>>(
          list<unsigned int>::nil());
      break;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename LoopifyPatterns::list<unsigned int>::Cons>(
              _loop_l->v());
      if (_loop_idx <= 0) {
        *(_write) = std::make_unique<LoopifyPatterns::list<unsigned int>>(
            list<unsigned int>::cons(value, *(d_a1)));
        break;
      } else {
        unsigned int i = _loop_idx - 1;
        auto _cell = std::make_unique<LoopifyPatterns::list<unsigned int>>(
            typename list<unsigned int>::Cons(d_a0, nullptr));
        *(_write) = std::move(_cell);
        _write =
            &std::get<typename list<unsigned int>::Cons>((*_write)->v_mut())
                 .d_a1;
        const LoopifyPatterns::list<unsigned int> *_next_l = d_a1.get();
        unsigned int _next_idx = i;
        _loop_l = _next_l;
        _loop_idx = std::move(_next_idx);
        continue;
      }
    }
  }
  return std::move(*(_head));
}

/// nested_pattern l three-element tuple pattern.
unsigned int LoopifyPatterns::nested_pattern(
    const LoopifyPatterns::list<
        std::pair<std::pair<unsigned int, unsigned int>, unsigned int>> &l) {
  struct _Enter {
    const LoopifyPatterns::list<
        std::pair<std::pair<unsigned int, unsigned int>, unsigned int>> *l;
  };

  struct _Call1 {
    unsigned int _s0;
    unsigned int _s1;
    unsigned int _s2;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{&l});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const LoopifyPatterns::list<
          std::pair<std::pair<unsigned int, unsigned int>, unsigned int>> &l =
          *(_f.l);
      if (std::holds_alternative<typename LoopifyPatterns::list<std::pair<
              std::pair<unsigned int, unsigned int>, unsigned int>>::Nil>(
              l.v())) {
        _result = 0u;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename LoopifyPatterns::list<std::pair<
                std::pair<unsigned int, unsigned int>, unsigned int>>::Cons>(
                l.v());
        const std::pair<unsigned int, unsigned int> &p0 = d_a0.first;
        const unsigned int &c = d_a0.second;
        const unsigned int &a = p0.first;
        const unsigned int &b = p0.second;
        _stack.emplace_back(_Call1{a, b, c});
        _stack.emplace_back(_Enter{d_a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Call1>(_frame));
      _result = (_f._s0 + (_f._s1 + (_f._s2 + _result)));
    }
  }
  return _result;
}

/// let_nested n let with nested let in binding.
unsigned int LoopifyPatterns::let_nested(const unsigned int &n) {
  struct _Enter {
    unsigned int n;
  };

  struct _Call1 {
    unsigned int _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{n});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const unsigned int &n = _f.n;
      if (n <= 0) {
        _result = 0u;
      } else {
        unsigned int m = n - 1;
        unsigned int a = (m + 1);
        _stack.emplace_back(_Call1{a});
        _stack.emplace_back(_Enter{m});
      }
    } else {
      auto _f = std::move(std::get<_Call1>(_frame));
      _result = (_f._s0 + _result);
    }
  }
  return _result;
}

/// Helper: list length.
unsigned int
LoopifyPatterns::list_len(const LoopifyPatterns::list<unsigned int> &l) {
  struct _Enter {
    const LoopifyPatterns::list<unsigned int> *l;
  };

  struct _Call1 {};

  using _Frame = std::variant<_Enter, _Call1>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{&l});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const LoopifyPatterns::list<unsigned int> &l = *(_f.l);
      if (std::holds_alternative<
              typename LoopifyPatterns::list<unsigned int>::Nil>(l.v())) {
        _result = 0u;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename LoopifyPatterns::list<unsigned int>::Cons>(l.v());
        _stack.emplace_back(_Call1{});
        _stack.emplace_back(_Enter{d_a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Call1>(_frame));
      _result = (_result + 1);
    }
  }
  return _result;
}

/// process_twice l applies recursion twice: process(process(xs)).
LoopifyPatterns::list<unsigned int>
LoopifyPatterns::process_twice_fuel(const unsigned int &fuel,
                                    LoopifyPatterns::list<unsigned int> l) {
  struct _Enter {
    LoopifyPatterns::list<unsigned int> l;
    unsigned int fuel;
  };

  struct _Call1 {
    unsigned int _s0;
    unsigned int _s1;
  };

  struct _Call2 {
    unsigned int _s0;
  };

  using _Frame = std::variant<_Enter, _Call1, _Call2>;
  LoopifyPatterns::list<unsigned int> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{l, fuel});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      LoopifyPatterns::list<unsigned int> l = std::move(_f.l);
      const unsigned int &fuel = _f.fuel;
      if (fuel <= 0) {
        _result = std::move(l);
      } else {
        unsigned int f = fuel - 1;
        if (std::holds_alternative<
                typename LoopifyPatterns::list<unsigned int>::Nil>(l.v_mut())) {
          _result = list<unsigned int>::nil();
        } else {
          auto &[d_a0, d_a1] =
              std::get<typename LoopifyPatterns::list<unsigned int>::Cons>(
                  l.v_mut());
          _stack.emplace_back(_Call1{d_a0, f});
          _stack.emplace_back(_Enter{*(d_a1), f});
        }
      }
    } else if (std::holds_alternative<_Call1>(_frame)) {
      auto _f = std::move(std::get<_Call1>(_frame));
      unsigned int d_a0 = std::move(_f._s0);
      unsigned int f = std::move(_f._s1);
      LoopifyPatterns::list<unsigned int> first = _result;
      _stack.emplace_back(_Call2{d_a0});
      _stack.emplace_back(_Enter{std::move(first), f});
    } else {
      auto _f = std::move(std::get<_Call2>(_frame));
      unsigned int d_a0 = std::move(_f._s0);
      LoopifyPatterns::list<unsigned int> second = _result;
      _result = list<unsigned int>::cons(d_a0, std::move(second));
    }
  }
  return _result;
}

LoopifyPatterns::list<unsigned int>
LoopifyPatterns::process_twice(const LoopifyPatterns::list<unsigned int> &l) {
  return process_twice_fuel(100u, l);
}

/// as_guard l uses as-pattern with guard (length check).
LoopifyPatterns::list<unsigned int>
LoopifyPatterns::as_guard_fuel(const unsigned int &fuel,
                               const LoopifyPatterns::list<unsigned int> &l) {
  std::unique_ptr<LoopifyPatterns::list<unsigned int>> _head{};
  std::unique_ptr<LoopifyPatterns::list<unsigned int>> *_write = &_head;
  const LoopifyPatterns::list<unsigned int> *_loop_l = &l;
  unsigned int _loop_fuel = fuel;
  while (true) {
    if (_loop_fuel <= 0) {
      *(_write) = std::make_unique<LoopifyPatterns::list<unsigned int>>(
          list<unsigned int>::nil());
      break;
    } else {
      unsigned int f = _loop_fuel - 1;
      if (std::holds_alternative<
              typename LoopifyPatterns::list<unsigned int>::Nil>(
              _loop_l->v())) {
        *(_write) = std::make_unique<LoopifyPatterns::list<unsigned int>>(
            list<unsigned int>::nil());
        break;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename LoopifyPatterns::list<unsigned int>::Cons>(
                _loop_l->v());
        LoopifyPatterns::list<unsigned int> all =
            list<unsigned int>::cons(d_a0, *(d_a1));
        if (3u < list_len(std::move(all))) {
          auto _cell = std::make_unique<LoopifyPatterns::list<unsigned int>>(
              typename list<unsigned int>::Cons(d_a0, nullptr));
          *(_write) = std::move(_cell);
          _write =
              &std::get<typename list<unsigned int>::Cons>((*_write)->v_mut())
                   .d_a1;
          const LoopifyPatterns::list<unsigned int> *_next_l = d_a1.get();
          unsigned int _next_fuel = f;
          _loop_l = _next_l;
          _loop_fuel = std::move(_next_fuel);
          continue;
        } else {
          const LoopifyPatterns::list<unsigned int> *_next_l = d_a1.get();
          unsigned int _next_fuel = f;
          _loop_l = _next_l;
          _loop_fuel = std::move(_next_fuel);
          continue;
        }
      }
    }
  }
  return std::move(*(_head));
}

LoopifyPatterns::list<unsigned int>
LoopifyPatterns::as_guard(const LoopifyPatterns::list<unsigned int> &l) {
  return as_guard_fuel(100u, l);
}

/// quad_sum_pattern l pattern with 4-way split.
unsigned int LoopifyPatterns::quad_sum_pattern(
    const LoopifyPatterns::list<unsigned int> &l) {
  struct _Enter {
    const LoopifyPatterns::list<unsigned int> *l;
  };

  struct _Call1 {
    decltype((std::declval<unsigned int &>() +
              std::declval<unsigned int &>())) _s0;
    decltype((std::declval<unsigned int &>() +
              std::declval<unsigned int &>())) _s1;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{&l});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const LoopifyPatterns::list<unsigned int> &l = *(_f.l);
      if (std::holds_alternative<
              typename LoopifyPatterns::list<unsigned int>::Nil>(l.v())) {
        _result = 0u;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename LoopifyPatterns::list<unsigned int>::Cons>(l.v());
        auto &&_sv0 = *(d_a1);
        if (std::holds_alternative<
                typename LoopifyPatterns::list<unsigned int>::Nil>(_sv0.v())) {
          _result = d_a0;
        } else {
          const auto &[d_a00, d_a10] =
              std::get<typename LoopifyPatterns::list<unsigned int>::Cons>(
                  _sv0.v());
          auto &&_sv1 = *(d_a10);
          if (std::holds_alternative<
                  typename LoopifyPatterns::list<unsigned int>::Nil>(
                  _sv1.v())) {
            _result = (d_a0 + d_a00);
          } else {
            const auto &[d_a01, d_a11] =
                std::get<typename LoopifyPatterns::list<unsigned int>::Cons>(
                    _sv1.v());
            auto &&_sv2 = *(d_a11);
            if (std::holds_alternative<
                    typename LoopifyPatterns::list<unsigned int>::Nil>(
                    _sv2.v())) {
              _result = (d_a0 + (d_a00 + d_a01));
            } else {
              const auto &[d_a02, d_a12] =
                  std::get<typename LoopifyPatterns::list<unsigned int>::Cons>(
                      _sv2.v());
              _stack.emplace_back(_Call1{(d_a0 + d_a00), (d_a01 + d_a02)});
              _stack.emplace_back(_Enter{d_a12.get()});
            }
          }
        }
      }
    } else {
      auto _f = std::move(std::get<_Call1>(_frame));
      _result = (_f._s0 + (_f._s1 + _result));
    }
  }
  return _result;
}

/// multi_guard l demonstrates pattern with multiple conditional branches.
unsigned int
LoopifyPatterns::multi_guard(const LoopifyPatterns::list<unsigned int> &l) {
  struct _Enter {
    const LoopifyPatterns::list<unsigned int> *l;
  };

  struct _Call1 {
    unsigned int _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{&l});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const LoopifyPatterns::list<unsigned int> &l = *(_f.l);
      if (std::holds_alternative<
              typename LoopifyPatterns::list<unsigned int>::Nil>(l.v())) {
        _result = 0u;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename LoopifyPatterns::list<unsigned int>::Cons>(l.v());
        _stack.emplace_back(_Call1{d_a0});
        _stack.emplace_back(_Enter{d_a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Call1>(_frame));
      unsigned int d_a0 = std::move(_f._s0);
      unsigned int rest = _result;
      if (10u < d_a0) {
        _result = (d_a0 + rest);
      } else {
        if (0u < d_a0) {
          _result = rest;
        } else {
          _result = (1u + rest);
        }
      }
    }
  }
  return _result;
}

/// Internal helper for double_append.
LoopifyPatterns::list<unsigned int>
LoopifyPatterns::append_lists(const LoopifyPatterns::list<unsigned int> &l1,
                              LoopifyPatterns::list<unsigned int> l2) {
  std::unique_ptr<LoopifyPatterns::list<unsigned int>> _head{};
  std::unique_ptr<LoopifyPatterns::list<unsigned int>> *_write = &_head;
  LoopifyPatterns::list<unsigned int> _loop_l2 = std::move(l2);
  const LoopifyPatterns::list<unsigned int> *_loop_l1 = &l1;
  while (true) {
    if (std::holds_alternative<
            typename LoopifyPatterns::list<unsigned int>::Nil>(_loop_l1->v())) {
      *(_write) = std::make_unique<LoopifyPatterns::list<unsigned int>>(
          std::move(_loop_l2));
      break;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename LoopifyPatterns::list<unsigned int>::Cons>(
              _loop_l1->v());
      auto _cell = std::make_unique<LoopifyPatterns::list<unsigned int>>(
          typename list<unsigned int>::Cons(d_a0, nullptr));
      *(_write) = std::move(_cell);
      _write =
          &std::get<typename list<unsigned int>::Cons>((*_write)->v_mut()).d_a1;
      LoopifyPatterns::list<unsigned int> _next_l2 = std::move(_loop_l2);
      const LoopifyPatterns::list<unsigned int> *_next_l1 = d_a1.get();
      _loop_l2 = std::move(_next_l2);
      _loop_l1 = _next_l1;
      continue;
    }
  }
  return std::move(*(_head));
}

/// double_append l1 l2 uses recursive result twice: h :: (rest @ rest).
LoopifyPatterns::list<unsigned int>
LoopifyPatterns::double_append(const LoopifyPatterns::list<unsigned int> &l1,
                               LoopifyPatterns::list<unsigned int> l2) {
  struct _Enter {
    LoopifyPatterns::list<unsigned int> l2;
    const LoopifyPatterns::list<unsigned int> *l1;
  };

  struct _Call1 {
    unsigned int _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  LoopifyPatterns::list<unsigned int> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{l2, &l1});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      LoopifyPatterns::list<unsigned int> l2 = std::move(_f.l2);
      const LoopifyPatterns::list<unsigned int> &l1 = *(_f.l1);
      if (std::holds_alternative<
              typename LoopifyPatterns::list<unsigned int>::Nil>(l1.v())) {
        _result = std::move(l2);
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename LoopifyPatterns::list<unsigned int>::Cons>(
                l1.v());
        _stack.emplace_back(_Call1{d_a0});
        _stack.emplace_back(_Enter{std::move(l2), d_a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Call1>(_frame));
      unsigned int d_a0 = std::move(_f._s0);
      LoopifyPatterns::list<unsigned int> rest = _result;
      _result = list<unsigned int>::cons(d_a0, append_lists(rest, rest));
    }
  }
  return _result;
}

/// process_twice_alt l applies transformation twice on recursive result.
LoopifyPatterns::list<unsigned int>
LoopifyPatterns::process_twice_alt_fuel(const unsigned int &fuel,
                                        LoopifyPatterns::list<unsigned int> l) {
  struct _Enter {
    LoopifyPatterns::list<unsigned int> l;
    unsigned int fuel;
  };

  struct _Call1 {
    unsigned int _s0;
    unsigned int _s1;
  };

  struct _Call2 {
    unsigned int _s0;
  };

  using _Frame = std::variant<_Enter, _Call1, _Call2>;
  LoopifyPatterns::list<unsigned int> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{l, fuel});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      LoopifyPatterns::list<unsigned int> l = std::move(_f.l);
      const unsigned int &fuel = _f.fuel;
      if (fuel <= 0) {
        _result = std::move(l);
      } else {
        unsigned int f = fuel - 1;
        if (std::holds_alternative<
                typename LoopifyPatterns::list<unsigned int>::Nil>(l.v_mut())) {
          _result = list<unsigned int>::nil();
        } else {
          auto &[d_a0, d_a1] =
              std::get<typename LoopifyPatterns::list<unsigned int>::Cons>(
                  l.v_mut());
          _stack.emplace_back(_Call1{d_a0, f});
          _stack.emplace_back(_Enter{*(d_a1), f});
        }
      }
    } else if (std::holds_alternative<_Call1>(_frame)) {
      auto _f = std::move(std::get<_Call1>(_frame));
      unsigned int d_a0 = std::move(_f._s0);
      unsigned int f = std::move(_f._s1);
      LoopifyPatterns::list<unsigned int> once = _result;
      _stack.emplace_back(_Call2{d_a0});
      _stack.emplace_back(_Enter{std::move(once), f});
    } else {
      auto _f = std::move(std::get<_Call2>(_frame));
      unsigned int d_a0 = std::move(_f._s0);
      LoopifyPatterns::list<unsigned int> twice = _result;
      _result = list<unsigned int>::cons(d_a0, std::move(twice));
    }
  }
  return _result;
}

LoopifyPatterns::list<unsigned int> LoopifyPatterns::process_twice_alt(
    const LoopifyPatterns::list<unsigned int> &l) {
  return process_twice_alt_fuel(100u, l);
}

/// sum_if_positive_else_double l conditional logic on each element.
unsigned int LoopifyPatterns::sum_if_positive_else_double(
    const LoopifyPatterns::list<unsigned int> &l) {
  struct _Enter {
    const LoopifyPatterns::list<unsigned int> *l;
  };

  struct _Call1 {
    unsigned int _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{&l});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const LoopifyPatterns::list<unsigned int> &l = *(_f.l);
      if (std::holds_alternative<
              typename LoopifyPatterns::list<unsigned int>::Nil>(l.v())) {
        _result = 0u;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename LoopifyPatterns::list<unsigned int>::Cons>(l.v());
        _stack.emplace_back(_Call1{d_a0});
        _stack.emplace_back(_Enter{d_a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Call1>(_frame));
      unsigned int d_a0 = std::move(_f._s0);
      unsigned int rest = _result;
      if (d_a0 == 0u) {
        _result = ((2u * d_a0) + rest);
      } else {
        _result = (d_a0 + rest);
      }
    }
  }
  return _result;
}

/// merge_alternating l1 l2 merges two lists by alternating elements.
LoopifyPatterns::list<unsigned int>
LoopifyPatterns::merge_alternating(LoopifyPatterns::list<unsigned int> l1,
                                   LoopifyPatterns::list<unsigned int> l2) {
  std::unique_ptr<LoopifyPatterns::list<unsigned int>> _head{};
  std::unique_ptr<LoopifyPatterns::list<unsigned int>> *_write = &_head;
  LoopifyPatterns::list<unsigned int> _loop_l2 = std::move(l2);
  LoopifyPatterns::list<unsigned int> _loop_l1 = std::move(l1);
  while (true) {
    if (std::holds_alternative<
            typename LoopifyPatterns::list<unsigned int>::Nil>(
            _loop_l1.v_mut())) {
      *(_write) = std::make_unique<LoopifyPatterns::list<unsigned int>>(
          std::move(_loop_l2));
      break;
    } else {
      auto &[d_a0, d_a1] =
          std::get<typename LoopifyPatterns::list<unsigned int>::Cons>(
              _loop_l1.v_mut());
      if (std::holds_alternative<
              typename LoopifyPatterns::list<unsigned int>::Nil>(
              _loop_l2.v_mut())) {
        *(_write) =
            std::make_unique<LoopifyPatterns::list<unsigned int>>(_loop_l1);
        break;
      } else {
        auto &[d_a00, d_a10] =
            std::get<typename LoopifyPatterns::list<unsigned int>::Cons>(
                _loop_l2.v_mut());
        auto _cell = std::make_unique<LoopifyPatterns::list<unsigned int>>(
            typename list<unsigned int>::Cons(d_a0, nullptr));
        auto _cell1 = std::make_unique<LoopifyPatterns::list<unsigned int>>(
            typename list<unsigned int>::Cons(d_a00, nullptr));
        std::get<typename list<unsigned int>::Cons>(_cell->v_mut()).d_a1 =
            std::move(_cell1);
        *(_write) = std::move(_cell);
        _write =
            &std::get<typename list<unsigned int>::Cons>(
                 std::get<typename list<unsigned int>::Cons>((*_write)->v_mut())
                     .d_a1->v_mut())
                 .d_a1;
        LoopifyPatterns::list<unsigned int> _next_l2 = std::move(*(d_a10));
        LoopifyPatterns::list<unsigned int> _next_l1 = std::move(*(d_a1));
        _loop_l2 = std::move(_next_l2);
        _loop_l1 = std::move(_next_l1);
        continue;
      }
    }
  }
  return std::move(*(_head));
}

/// four_elem l four-element destructuring pattern with fallback cases.
unsigned int
LoopifyPatterns::four_elem(const LoopifyPatterns::list<unsigned int> &l) {
  struct _Enter {
    const LoopifyPatterns::list<unsigned int> *l;
  };

  struct _Call1 {
    unsigned int _s0;
    unsigned int _s1;
    unsigned int _s2;
    unsigned int _s3;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{&l});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const LoopifyPatterns::list<unsigned int> &l = *(_f.l);
      if (std::holds_alternative<
              typename LoopifyPatterns::list<unsigned int>::Nil>(l.v())) {
        _result = 0u;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename LoopifyPatterns::list<unsigned int>::Cons>(l.v());
        auto &&_sv0 = *(d_a1);
        if (std::holds_alternative<
                typename LoopifyPatterns::list<unsigned int>::Nil>(_sv0.v())) {
          _result = 1u;
        } else {
          const auto &[d_a00, d_a10] =
              std::get<typename LoopifyPatterns::list<unsigned int>::Cons>(
                  _sv0.v());
          auto &&_sv1 = *(d_a10);
          if (std::holds_alternative<
                  typename LoopifyPatterns::list<unsigned int>::Nil>(
                  _sv1.v())) {
            _result = 2u;
          } else {
            const auto &[d_a01, d_a11] =
                std::get<typename LoopifyPatterns::list<unsigned int>::Cons>(
                    _sv1.v());
            auto &&_sv2 = *(d_a11);
            if (std::holds_alternative<
                    typename LoopifyPatterns::list<unsigned int>::Nil>(
                    _sv2.v())) {
              _result = 3u;
            } else {
              const auto &[d_a02, d_a12] =
                  std::get<typename LoopifyPatterns::list<unsigned int>::Cons>(
                      _sv2.v());
              _stack.emplace_back(_Call1{d_a0, d_a00, d_a01, d_a02});
              _stack.emplace_back(_Enter{d_a12.get()});
            }
          }
        }
      }
    } else {
      auto _f = std::move(std::get<_Call1>(_frame));
      _result = (_f._s0 + (_f._s1 + (_f._s2 + (_f._s3 + _result))));
    }
  }
  return _result;
}
