#include <loopify_patterns.h>

#include <functional>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

/// Complex control flow and pattern matching edge cases.
/// multi_let n multiple sequential let bindings before recursion.
__attribute__((pure)) unsigned int
LoopifyPatterns::multi_let(const unsigned int n) {
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
        unsigned int m = n - 1;
        unsigned int b = (m * 2u);
        unsigned int c = (b + 3u);
        _stack.emplace_back(_Call1{c});
        _stack.emplace_back(_Enter{m});
      }
    } else {
      const auto &_f = std::get<_Call1>(_frame);
      _result = (_f._s0 + _result);
    }
  }
  return _result;
}

/// nested_if n deeply nested if-then-else with recursion at different depths.
__attribute__((pure)) unsigned int
LoopifyPatterns::nested_if_fuel(const unsigned int fuel, const unsigned int n) {
  unsigned int _result;
  unsigned int _loop_n = n;
  unsigned int _loop_fuel = fuel;
  bool _continue = true;
  while (_continue) {
    if (_loop_fuel <= 0) {
      _result = 0u;
      _continue = false;
    } else {
      unsigned int f = _loop_fuel - 1;
      if (_loop_n <= 0) {
        _result = 0u;
        _continue = false;
      } else {
        unsigned int n_ = _loop_n - 1;
        if (n_ <= 0) {
          _result = 1u;
          _continue = false;
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
            unsigned int _next_n = [&]() -> unsigned int {
              if (m == 0u) {
                return 0u;
              } else {
                return (((m - 1u) > m ? 0 : (m - 1u)));
              }
            }();
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

__attribute__((pure)) unsigned int
LoopifyPatterns::nested_if(const unsigned int n) {
  return nested_if_fuel(1000u, n);
}

/// deep_nest n deeply nested function application.
__attribute__((pure)) unsigned int
LoopifyPatterns::deep_nest(const unsigned int n) {
  struct _Enter {
    const unsigned int n;
  };

  struct _Call1 {
    decltype(1u) _s0;
    decltype(1u) _s1;
    decltype(1u) _s2;
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
        unsigned int m = n - 1;
        _stack.emplace_back(_Call1{1u, 1u, 1u});
        _stack.emplace_back(_Enter{m});
      }
    } else {
      const auto &_f = std::get<_Call1>(_frame);
      _result = (_f._s0 + (_f._s1 + (_f._s2 + _result)));
    }
  }
  return _result;
}

/// bool_chain n target multiple recursive calls in || chain.
__attribute__((pure)) bool
LoopifyPatterns::bool_chain_fuel(const unsigned int fuel, const unsigned int n,
                                 const unsigned int target) {
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
      const auto &_f = std::get<_Call1>(_frame);
      _stack.emplace_back(_Call2{_result});
      _stack.emplace_back(_Enter{_f._s0, _f._s1});
    } else {
      const auto &_f = std::get<_Call2>(_frame);
      _result = (_result || _f._s0);
    }
  }
  return _result;
}

__attribute__((pure)) bool
LoopifyPatterns::bool_chain(const unsigned int n, const unsigned int target) {
  return bool_chain_fuel(1000u, n, target);
}

/// chained_comp n boolean result with double recursion.
__attribute__((pure)) bool LoopifyPatterns::chained_comp(const unsigned int n) {
  struct _Enter {
    const unsigned int n;
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
  _stack.emplace_back(_Enter{n});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      const auto &_f = std::get<_Enter>(_frame);
      const unsigned int n = _f.n;
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
      const auto &_f = std::get<_Call1>(_frame);
      _stack.emplace_back(_Call2{_result});
      _stack.emplace_back(_Enter{_f._s0});
    } else {
      const auto &_f = std::get<_Call2>(_frame);
      _result = (_result && _f._s0);
    }
  }
  return _result;
}

/// tuple_constr n recursive calls in multiple tuple positions.
__attribute__((pure))
std::pair<std::pair<unsigned int, unsigned int>, unsigned int>
LoopifyPatterns::tuple_constr(const unsigned int n) {
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
        unsigned int m = n - 1;
        _stack.emplace_back(_Call1{n});
        _stack.emplace_back(_Enter{m});
      }
    } else {
      const auto &_f = std::get<_Call1>(_frame);
      const unsigned int n = _f._s0;
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
__attribute__((pure))
std::pair<std::pair<unsigned int, unsigned int>, unsigned int>
LoopifyPatterns::sum_prod_count(
    const std::shared_ptr<LoopifyPatterns::list<unsigned int>> &l,
    const unsigned int a_sum, const unsigned int a_prod,
    const unsigned int a_count) {
  std::pair<std::pair<unsigned int, unsigned int>, unsigned int> _result;
  unsigned int _loop_a_count = a_count;
  unsigned int _loop_a_prod = a_prod;
  unsigned int _loop_a_sum = a_sum;
  std::shared_ptr<LoopifyPatterns::list<unsigned int>> _loop_l = l;
  bool _continue = true;
  while (_continue) {
    if (std::holds_alternative<
            typename LoopifyPatterns::list<unsigned int>::Nil>(_loop_l->v())) {
      _result = std::make_pair(std::make_pair(_loop_a_sum, _loop_a_prod),
                               _loop_a_count);
      _continue = false;
    } else {
      const auto &_m =
          *std::get_if<typename LoopifyPatterns::list<unsigned int>::Cons>(
              &_loop_l->v());
      unsigned int _next_a_count = (_loop_a_count + 1);
      unsigned int _next_a_prod = (_loop_a_prod * _m.d_a0);
      unsigned int _next_a_sum = (_loop_a_sum + _m.d_a0);
      std::shared_ptr<LoopifyPatterns::list<unsigned int>> _next_l = _m.d_a1;
      _loop_a_count = std::move(_next_a_count);
      _loop_a_prod = std::move(_next_a_prod);
      _loop_a_sum = std::move(_next_a_sum);
      _loop_l = std::move(_next_l);
    }
  }
  return _result;
}

/// split_by_sign l pos neg partition with dual accumulators.
__attribute__((pure))
std::pair<std::shared_ptr<LoopifyPatterns::list<unsigned int>>,
          std::shared_ptr<LoopifyPatterns::list<unsigned int>>>
LoopifyPatterns::split_by_sign_aux(
    const std::shared_ptr<LoopifyPatterns::list<unsigned int>> &l,
    const unsigned int base,
    std::shared_ptr<LoopifyPatterns::list<unsigned int>> pos,
    std::shared_ptr<LoopifyPatterns::list<unsigned int>> neg) {
  std::pair<std::shared_ptr<LoopifyPatterns::list<unsigned int>>,
            std::shared_ptr<LoopifyPatterns::list<unsigned int>>>
      _result;
  std::shared_ptr<LoopifyPatterns::list<unsigned int>> _loop_neg = neg;
  std::shared_ptr<LoopifyPatterns::list<unsigned int>> _loop_pos = pos;
  std::shared_ptr<LoopifyPatterns::list<unsigned int>> _loop_l = l;
  bool _continue = true;
  while (_continue) {
    if (std::holds_alternative<
            typename LoopifyPatterns::list<unsigned int>::Nil>(_loop_l->v())) {
      _result = std::make_pair(std::move(_loop_pos), std::move(_loop_neg));
      _continue = false;
    } else {
      const auto &_m =
          *std::get_if<typename LoopifyPatterns::list<unsigned int>::Cons>(
              &_loop_l->v());
      if (base <= _m.d_a0) {
        std::shared_ptr<LoopifyPatterns::list<unsigned int>> _next_neg =
            std::move(_loop_neg);
        std::shared_ptr<LoopifyPatterns::list<unsigned int>> _next_pos =
            list<unsigned int>::cons(_m.d_a0, _loop_pos);
        std::shared_ptr<LoopifyPatterns::list<unsigned int>> _next_l = _m.d_a1;
        _loop_neg = std::move(_next_neg);
        _loop_pos = std::move(_next_pos);
        _loop_l = std::move(_next_l);
      } else {
        std::shared_ptr<LoopifyPatterns::list<unsigned int>> _next_neg =
            list<unsigned int>::cons(_m.d_a0, _loop_neg);
        std::shared_ptr<LoopifyPatterns::list<unsigned int>> _next_pos =
            std::move(_loop_pos);
        std::shared_ptr<LoopifyPatterns::list<unsigned int>> _next_l = _m.d_a1;
        _loop_neg = std::move(_next_neg);
        _loop_pos = std::move(_next_pos);
        _loop_l = std::move(_next_l);
      }
    }
  }
  return _result;
}

__attribute__((pure))
std::pair<std::shared_ptr<LoopifyPatterns::list<unsigned int>>,
          std::shared_ptr<LoopifyPatterns::list<unsigned int>>>
LoopifyPatterns::split_by_sign(
    const std::shared_ptr<LoopifyPatterns::list<unsigned int>> &l,
    const unsigned int base) {
  return split_by_sign_aux(l, base, list<unsigned int>::nil(),
                           list<unsigned int>::nil());
}

/// guard_accum acc l multiple when-style guards with different logic.
__attribute__((pure)) unsigned int LoopifyPatterns::guard_accum(
    const unsigned int acc,
    const std::shared_ptr<LoopifyPatterns::list<unsigned int>> &l) {
  unsigned int _result;
  std::shared_ptr<LoopifyPatterns::list<unsigned int>> _loop_l = l;
  unsigned int _loop_acc = acc;
  bool _continue = true;
  while (_continue) {
    if (std::holds_alternative<
            typename LoopifyPatterns::list<unsigned int>::Nil>(_loop_l->v())) {
      _result = _loop_acc;
      _continue = false;
    } else {
      const auto &_m =
          *std::get_if<typename LoopifyPatterns::list<unsigned int>::Cons>(
              &_loop_l->v());
      if (100u < _m.d_a0) {
        std::shared_ptr<LoopifyPatterns::list<unsigned int>> _next_l = _m.d_a1;
        unsigned int _next_acc = (_loop_acc * 2u);
        _loop_l = std::move(_next_l);
        _loop_acc = std::move(_next_acc);
      } else {
        if (50u < _m.d_a0) {
          std::shared_ptr<LoopifyPatterns::list<unsigned int>> _next_l =
              _m.d_a1;
          unsigned int _next_acc = (_loop_acc + _m.d_a0);
          _loop_l = std::move(_next_l);
          _loop_acc = std::move(_next_acc);
        } else {
          if (0u < _m.d_a0) {
            std::shared_ptr<LoopifyPatterns::list<unsigned int>> _next_l =
                _m.d_a1;
            unsigned int _next_acc = (_loop_acc + 1);
            _loop_l = std::move(_next_l);
            _loop_acc = std::move(_next_acc);
          } else {
            _loop_l = _m.d_a1;
          }
        }
      }
    }
  }
  return _result;
}

/// cons_computed n l cons with conditional parameter change.
std::shared_ptr<LoopifyPatterns::list<unsigned int>>
LoopifyPatterns::cons_computed(
    const unsigned int n,
    const std::shared_ptr<LoopifyPatterns::list<unsigned int>> &l) {
  std::shared_ptr<LoopifyPatterns::list<unsigned int>> _head{};
  std::shared_ptr<LoopifyPatterns::list<unsigned int>> _last{};
  std::shared_ptr<LoopifyPatterns::list<unsigned int>> _loop_l = l;
  unsigned int _loop_n = n;
  bool _continue = true;
  while (_continue) {
    if (std::holds_alternative<
            typename LoopifyPatterns::list<unsigned int>::Nil>(_loop_l->v())) {
      if (_last) {
        std::get<typename list<unsigned int>::Cons>(_last->v_mut()).d_a1 =
            list<unsigned int>::nil();
      } else {
        _head = list<unsigned int>::nil();
      }
      _continue = false;
    } else {
      const auto &_m =
          *std::get_if<typename LoopifyPatterns::list<unsigned int>::Cons>(
              &_loop_l->v());
      unsigned int next_n;
      if (0u < _loop_n) {
        next_n = (((_loop_n - 1u) > _loop_n ? 0 : (_loop_n - 1u)));
      } else {
        next_n = _loop_n;
      }
      auto _cell = list<unsigned int>::cons(_m.d_a0, nullptr);
      if (_last) {
        std::get<typename list<unsigned int>::Cons>(_last->v_mut()).d_a1 =
            _cell;
      } else {
        _head = _cell;
      }
      _last = _cell;
      std::shared_ptr<LoopifyPatterns::list<unsigned int>> _next_l = _m.d_a1;
      unsigned int _next_n = next_n;
      _loop_l = std::move(_next_l);
      _loop_n = std::move(_next_n);
      continue;
    }
  }
  return _head;
}

/// mod_pattern n recursive call in mod expression.
__attribute__((pure)) unsigned int
LoopifyPatterns::mod_pattern(const unsigned int n) {
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
      const auto &_f = std::get<_Call1>(_frame);
      _result = ((_result + 1) ? _f._s0 % (_result + 1) : _f._s0);
    }
  }
  return _result;
}

/// alternating_ops n alternating operations based on modulo.
__attribute__((pure)) unsigned int
LoopifyPatterns::alternating_ops(const unsigned int n) {
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
      const auto &_f = std::get<_Call1>(_frame);
      _result = (_f._s0 + _result);
    } else {
      const auto &_f = std::get<_Call2>(_frame);
      _result = (_f._s0 + _result);
    }
  }
  return _result;
}

/// replace_at idx value l replace element at index.
std::shared_ptr<LoopifyPatterns::list<unsigned int>>
LoopifyPatterns::replace_at(
    const unsigned int idx, const unsigned int value,
    const std::shared_ptr<LoopifyPatterns::list<unsigned int>> &l) {
  std::shared_ptr<LoopifyPatterns::list<unsigned int>> _head{};
  std::shared_ptr<LoopifyPatterns::list<unsigned int>> _last{};
  std::shared_ptr<LoopifyPatterns::list<unsigned int>> _loop_l = l;
  unsigned int _loop_idx = idx;
  bool _continue = true;
  while (_continue) {
    if (std::holds_alternative<
            typename LoopifyPatterns::list<unsigned int>::Nil>(_loop_l->v())) {
      if (_last) {
        std::get<typename list<unsigned int>::Cons>(_last->v_mut()).d_a1 =
            list<unsigned int>::nil();
      } else {
        _head = list<unsigned int>::nil();
      }
      _continue = false;
    } else {
      const auto &_m =
          *std::get_if<typename LoopifyPatterns::list<unsigned int>::Cons>(
              &_loop_l->v());
      if (_loop_idx <= 0) {
        if (_last) {
          std::get<typename list<unsigned int>::Cons>(_last->v_mut()).d_a1 =
              list<unsigned int>::cons(value, _m.d_a1);
        } else {
          _head = list<unsigned int>::cons(value, _m.d_a1);
        }
        _continue = false;
      } else {
        unsigned int i = _loop_idx - 1;
        auto _cell = list<unsigned int>::cons(_m.d_a0, nullptr);
        if (_last) {
          std::get<typename list<unsigned int>::Cons>(_last->v_mut()).d_a1 =
              _cell;
        } else {
          _head = _cell;
        }
        _last = _cell;
        std::shared_ptr<LoopifyPatterns::list<unsigned int>> _next_l = _m.d_a1;
        unsigned int _next_idx = i;
        _loop_l = std::move(_next_l);
        _loop_idx = std::move(_next_idx);
        continue;
      }
    }
  }
  return _head;
}

/// nested_pattern l three-element tuple pattern.
__attribute__((pure)) unsigned int LoopifyPatterns::nested_pattern(
    const std::shared_ptr<LoopifyPatterns::list<
        std::pair<std::pair<unsigned int, unsigned int>, unsigned int>>> &l) {
  struct _Enter {
    const std::shared_ptr<LoopifyPatterns::list<
        std::pair<std::pair<unsigned int, unsigned int>, unsigned int>>>
        l;
  };

  struct _Call1 {
    unsigned int _s0;
    unsigned int _s1;
    unsigned int _s2;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.emplace_back(_Enter{l});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      const auto &_f = std::get<_Enter>(_frame);
      const std::shared_ptr<LoopifyPatterns::list<
          std::pair<std::pair<unsigned int, unsigned int>, unsigned int>>>
          l = _f.l;
      if (std::holds_alternative<typename LoopifyPatterns::list<std::pair<
              std::pair<unsigned int, unsigned int>, unsigned int>>::Nil>(
              l->v())) {
        _result = 0u;
      } else {
        const auto &_m = *std::get_if<typename LoopifyPatterns::list<std::pair<
            std::pair<unsigned int, unsigned int>, unsigned int>>::Cons>(
            &l->v());
        const std::pair<unsigned int, unsigned int> &p0 = _m.d_a0.first;
        const unsigned int &c = _m.d_a0.second;
        const unsigned int &a = p0.first;
        const unsigned int &b = p0.second;
        _stack.emplace_back(_Call1{a, b, c});
        _stack.emplace_back(_Enter{_m.d_a1});
      }
    } else {
      const auto &_f = std::get<_Call1>(_frame);
      _result = (_f._s0 + (_f._s1 + (_f._s2 + _result)));
    }
  }
  return _result;
}

/// let_nested n let with nested let in binding.
__attribute__((pure)) unsigned int
LoopifyPatterns::let_nested(const unsigned int n) {
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
        unsigned int m = n - 1;
        unsigned int a = (m + 1);
        _stack.emplace_back(_Call1{a});
        _stack.emplace_back(_Enter{m});
      }
    } else {
      const auto &_f = std::get<_Call1>(_frame);
      _result = (_f._s0 + _result);
    }
  }
  return _result;
}

/// Helper: list length.
__attribute__((pure)) unsigned int LoopifyPatterns::list_len(
    const std::shared_ptr<LoopifyPatterns::list<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<LoopifyPatterns::list<unsigned int>> l;
  };

  struct _Call1 {};

  using _Frame = std::variant<_Enter, _Call1>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.emplace_back(_Enter{l});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      const auto &_f = std::get<_Enter>(_frame);
      const std::shared_ptr<LoopifyPatterns::list<unsigned int>> l = _f.l;
      if (std::holds_alternative<
              typename LoopifyPatterns::list<unsigned int>::Nil>(l->v())) {
        _result = 0u;
      } else {
        const auto &_m =
            *std::get_if<typename LoopifyPatterns::list<unsigned int>::Cons>(
                &l->v());
        _stack.emplace_back(_Call1{});
        _stack.emplace_back(_Enter{_m.d_a1});
      }
    } else {
      const auto &_f = std::get<_Call1>(_frame);
      _result = (_result + 1);
    }
  }
  return _result;
}

/// process_twice l applies recursion twice: process(process(xs)).
std::shared_ptr<LoopifyPatterns::list<unsigned int>>
LoopifyPatterns::process_twice_fuel(
    const unsigned int fuel,
    std::shared_ptr<LoopifyPatterns::list<unsigned int>> l) {
  struct _Enter {
    std::shared_ptr<LoopifyPatterns::list<unsigned int>> l;
    const unsigned int fuel;
  };

  struct _Call1 {
    const typename LoopifyPatterns::list<unsigned int>::Cons _s0;
    unsigned int _s1;
  };

  struct _Call2 {
    const typename LoopifyPatterns::list<unsigned int>::Cons _s0;
  };

  using _Frame = std::variant<_Enter, _Call1, _Call2>;
  std::shared_ptr<LoopifyPatterns::list<unsigned int>> _result{};
  std::vector<_Frame> _stack;
  _stack.emplace_back(_Enter{l, fuel});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      const auto &_f = std::get<_Enter>(_frame);
      std::shared_ptr<LoopifyPatterns::list<unsigned int>> l = _f.l;
      const unsigned int fuel = _f.fuel;
      if (fuel <= 0) {
        _result = std::move(l);
      } else {
        unsigned int f = fuel - 1;
        if (std::holds_alternative<
                typename LoopifyPatterns::list<unsigned int>::Nil>(l->v()) &&
            l.use_count() == 1) {
          _result = l;
        } else if (std::holds_alternative<
                       typename LoopifyPatterns::list<unsigned int>::Nil>(
                       l->v())) {
          _result = list<unsigned int>::nil();
        } else {
          const auto &_m =
              *std::get_if<typename LoopifyPatterns::list<unsigned int>::Cons>(
                  &l->v());
          _stack.emplace_back(_Call1{_m, f});
          _stack.emplace_back(_Enter{_m.d_a1, f});
        }
      }
    } else if (std::holds_alternative<_Call1>(_frame)) {
      const auto &_f = std::get<_Call1>(_frame);
      const typename LoopifyPatterns::list<unsigned int>::Cons _m = _f._s0;
      unsigned int f = _f._s1;
      std::shared_ptr<LoopifyPatterns::list<unsigned int>> first = _result;
      _stack.emplace_back(_Call2{_m});
      _stack.emplace_back(_Enter{std::move(first), f});
    } else {
      const auto &_f = std::get<_Call2>(_frame);
      const typename LoopifyPatterns::list<unsigned int>::Cons _m = _f._s0;
      std::shared_ptr<LoopifyPatterns::list<unsigned int>> second = _result;
      _result = list<unsigned int>::cons(_m.d_a0, second);
    }
  }
  return _result;
}

std::shared_ptr<LoopifyPatterns::list<unsigned int>>
LoopifyPatterns::process_twice(
    const std::shared_ptr<LoopifyPatterns::list<unsigned int>> &l) {
  return process_twice_fuel(100u, l);
}

/// as_guard l uses as-pattern with guard (length check).
std::shared_ptr<LoopifyPatterns::list<unsigned int>>
LoopifyPatterns::as_guard_fuel(
    const unsigned int fuel,
    const std::shared_ptr<LoopifyPatterns::list<unsigned int>> &l) {
  std::shared_ptr<LoopifyPatterns::list<unsigned int>> _head{};
  std::shared_ptr<LoopifyPatterns::list<unsigned int>> _last{};
  std::shared_ptr<LoopifyPatterns::list<unsigned int>> _loop_l = l;
  unsigned int _loop_fuel = fuel;
  bool _continue = true;
  while (_continue) {
    if (_loop_fuel <= 0) {
      if (_last) {
        std::get<typename list<unsigned int>::Cons>(_last->v_mut()).d_a1 =
            list<unsigned int>::nil();
      } else {
        _head = list<unsigned int>::nil();
      }
      _continue = false;
    } else {
      unsigned int f = _loop_fuel - 1;
      if (std::holds_alternative<
              typename LoopifyPatterns::list<unsigned int>::Nil>(
              _loop_l->v())) {
        if (_last) {
          std::get<typename list<unsigned int>::Cons>(_last->v_mut()).d_a1 =
              list<unsigned int>::nil();
        } else {
          _head = list<unsigned int>::nil();
        }
        _continue = false;
      } else {
        const auto &_m =
            *std::get_if<typename LoopifyPatterns::list<unsigned int>::Cons>(
                &_loop_l->v());
        std::shared_ptr<LoopifyPatterns::list<unsigned int>> all =
            list<unsigned int>::cons(_m.d_a0, _m.d_a1);
        if (3u < list_len(std::move(all))) {
          auto _cell = list<unsigned int>::cons(_m.d_a0, nullptr);
          if (_last) {
            std::get<typename list<unsigned int>::Cons>(_last->v_mut()).d_a1 =
                _cell;
          } else {
            _head = _cell;
          }
          _last = _cell;
          std::shared_ptr<LoopifyPatterns::list<unsigned int>> _next_l =
              _m.d_a1;
          unsigned int _next_fuel = f;
          _loop_l = std::move(_next_l);
          _loop_fuel = std::move(_next_fuel);
          continue;
        } else {
          std::shared_ptr<LoopifyPatterns::list<unsigned int>> _next_l =
              _m.d_a1;
          unsigned int _next_fuel = f;
          _loop_l = std::move(_next_l);
          _loop_fuel = std::move(_next_fuel);
          continue;
        }
      }
    }
  }
  return _head;
}

std::shared_ptr<LoopifyPatterns::list<unsigned int>> LoopifyPatterns::as_guard(
    const std::shared_ptr<LoopifyPatterns::list<unsigned int>> &l) {
  return as_guard_fuel(100u, l);
}

/// quad_sum_pattern l pattern with 4-way split.
__attribute__((pure)) unsigned int LoopifyPatterns::quad_sum_pattern(
    const std::shared_ptr<LoopifyPatterns::list<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<LoopifyPatterns::list<unsigned int>> l;
  };

  struct _Call1 {
    decltype((
        std::declval<typename LoopifyPatterns::list<unsigned int>::Cons &>()
            .d_a0 +
        std::declval<typename LoopifyPatterns::list<unsigned int>::Cons &>()
            .d_a0)) _s0;
    decltype((
        std::declval<typename LoopifyPatterns::list<unsigned int>::Cons &>()
            .d_a0 +
        std::declval<typename LoopifyPatterns::list<unsigned int>::Cons &>()
            .d_a0)) _s1;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.emplace_back(_Enter{l});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      const auto &_f = std::get<_Enter>(_frame);
      const std::shared_ptr<LoopifyPatterns::list<unsigned int>> l = _f.l;
      if (std::holds_alternative<
              typename LoopifyPatterns::list<unsigned int>::Nil>(l->v())) {
        _result = 0u;
      } else {
        const auto &_m =
            *std::get_if<typename LoopifyPatterns::list<unsigned int>::Cons>(
                &l->v());
        auto &&_sv0 = _m.d_a1;
        if (std::holds_alternative<
                typename LoopifyPatterns::list<unsigned int>::Nil>(_sv0->v())) {
          _result = _m.d_a0;
        } else {
          const auto &_m0 =
              *std::get_if<typename LoopifyPatterns::list<unsigned int>::Cons>(
                  &_sv0->v());
          auto &&_sv1 = _m0.d_a1;
          if (std::holds_alternative<
                  typename LoopifyPatterns::list<unsigned int>::Nil>(
                  _sv1->v())) {
            _result = (_m.d_a0 + _m0.d_a0);
          } else {
            const auto &_m1 = *std::get_if<
                typename LoopifyPatterns::list<unsigned int>::Cons>(&_sv1->v());
            auto &&_sv2 = _m1.d_a1;
            if (std::holds_alternative<
                    typename LoopifyPatterns::list<unsigned int>::Nil>(
                    _sv2->v())) {
              _result = (_m.d_a0 + (_m0.d_a0 + _m1.d_a0));
            } else {
              const auto &_m2 = *std::get_if<
                  typename LoopifyPatterns::list<unsigned int>::Cons>(
                  &_sv2->v());
              _stack.emplace_back(
                  _Call1{(_m.d_a0 + _m0.d_a0), (_m1.d_a0 + _m2.d_a0)});
              _stack.emplace_back(_Enter{_m2.d_a1});
            }
          }
        }
      }
    } else {
      const auto &_f = std::get<_Call1>(_frame);
      _result = (_f._s0 + (_f._s1 + _result));
    }
  }
  return _result;
}

/// multi_guard l demonstrates pattern with multiple conditional branches.
__attribute__((pure)) unsigned int LoopifyPatterns::multi_guard(
    const std::shared_ptr<LoopifyPatterns::list<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<LoopifyPatterns::list<unsigned int>> l;
  };

  struct _Call1 {
    const typename LoopifyPatterns::list<unsigned int>::Cons _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.emplace_back(_Enter{l});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      const auto &_f = std::get<_Enter>(_frame);
      const std::shared_ptr<LoopifyPatterns::list<unsigned int>> l = _f.l;
      if (std::holds_alternative<
              typename LoopifyPatterns::list<unsigned int>::Nil>(l->v())) {
        _result = 0u;
      } else {
        const auto &_m =
            *std::get_if<typename LoopifyPatterns::list<unsigned int>::Cons>(
                &l->v());
        _stack.emplace_back(_Call1{_m});
        _stack.emplace_back(_Enter{_m.d_a1});
      }
    } else {
      const auto &_f = std::get<_Call1>(_frame);
      const typename LoopifyPatterns::list<unsigned int>::Cons _m = _f._s0;
      unsigned int rest = _result;
      if (10u < _m.d_a0) {
        _result = (_m.d_a0 + rest);
      } else {
        if (0u < _m.d_a0) {
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
std::shared_ptr<LoopifyPatterns::list<unsigned int>>
LoopifyPatterns::append_lists(
    const std::shared_ptr<LoopifyPatterns::list<unsigned int>> &l1,
    std::shared_ptr<LoopifyPatterns::list<unsigned int>> l2) {
  std::shared_ptr<LoopifyPatterns::list<unsigned int>> _head{};
  std::shared_ptr<LoopifyPatterns::list<unsigned int>> _last{};
  std::shared_ptr<LoopifyPatterns::list<unsigned int>> _loop_l1 = l1;
  bool _continue = true;
  while (_continue) {
    if (std::holds_alternative<
            typename LoopifyPatterns::list<unsigned int>::Nil>(_loop_l1->v())) {
      if (_last) {
        std::get<typename list<unsigned int>::Cons>(_last->v_mut()).d_a1 =
            std::move(l2);
      } else {
        _head = std::move(l2);
      }
      _continue = false;
    } else {
      const auto &_m =
          *std::get_if<typename LoopifyPatterns::list<unsigned int>::Cons>(
              &_loop_l1->v());
      auto _cell = list<unsigned int>::cons(_m.d_a0, nullptr);
      if (_last) {
        std::get<typename list<unsigned int>::Cons>(_last->v_mut()).d_a1 =
            _cell;
      } else {
        _head = _cell;
      }
      _last = _cell;
      _loop_l1 = _m.d_a1;
      continue;
    }
  }
  return _head;
}

/// double_append l1 l2 uses recursive result twice: h :: (rest @ rest).
std::shared_ptr<LoopifyPatterns::list<unsigned int>>
LoopifyPatterns::double_append(
    const std::shared_ptr<LoopifyPatterns::list<unsigned int>> &l1,
    std::shared_ptr<LoopifyPatterns::list<unsigned int>> l2) {
  struct _Enter {
    std::shared_ptr<LoopifyPatterns::list<unsigned int>> l2;
    const std::shared_ptr<LoopifyPatterns::list<unsigned int>> l1;
  };

  struct _Call1 {
    const typename LoopifyPatterns::list<unsigned int>::Cons _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::shared_ptr<LoopifyPatterns::list<unsigned int>> _result{};
  std::vector<_Frame> _stack;
  _stack.emplace_back(_Enter{l2, l1});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      const auto &_f = std::get<_Enter>(_frame);
      std::shared_ptr<LoopifyPatterns::list<unsigned int>> l2 = _f.l2;
      const std::shared_ptr<LoopifyPatterns::list<unsigned int>> l1 = _f.l1;
      if (std::holds_alternative<
              typename LoopifyPatterns::list<unsigned int>::Nil>(l1->v())) {
        _result = std::move(l2);
      } else {
        const auto &_m =
            *std::get_if<typename LoopifyPatterns::list<unsigned int>::Cons>(
                &l1->v());
        _stack.emplace_back(_Call1{_m});
        _stack.emplace_back(_Enter{std::move(l2), _m.d_a1});
      }
    } else {
      const auto &_f = std::get<_Call1>(_frame);
      const typename LoopifyPatterns::list<unsigned int>::Cons _m = _f._s0;
      std::shared_ptr<LoopifyPatterns::list<unsigned int>> rest = _result;
      _result = list<unsigned int>::cons(_m.d_a0, append_lists(rest, rest));
    }
  }
  return _result;
}

/// process_twice_alt l applies transformation twice on recursive result.
std::shared_ptr<LoopifyPatterns::list<unsigned int>>
LoopifyPatterns::process_twice_alt_fuel(
    const unsigned int fuel,
    std::shared_ptr<LoopifyPatterns::list<unsigned int>> l) {
  struct _Enter {
    std::shared_ptr<LoopifyPatterns::list<unsigned int>> l;
    const unsigned int fuel;
  };

  struct _Call1 {
    const typename LoopifyPatterns::list<unsigned int>::Cons _s0;
    unsigned int _s1;
  };

  struct _Call2 {
    const typename LoopifyPatterns::list<unsigned int>::Cons _s0;
  };

  using _Frame = std::variant<_Enter, _Call1, _Call2>;
  std::shared_ptr<LoopifyPatterns::list<unsigned int>> _result{};
  std::vector<_Frame> _stack;
  _stack.emplace_back(_Enter{l, fuel});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      const auto &_f = std::get<_Enter>(_frame);
      std::shared_ptr<LoopifyPatterns::list<unsigned int>> l = _f.l;
      const unsigned int fuel = _f.fuel;
      if (fuel <= 0) {
        _result = std::move(l);
      } else {
        unsigned int f = fuel - 1;
        if (std::holds_alternative<
                typename LoopifyPatterns::list<unsigned int>::Nil>(l->v()) &&
            l.use_count() == 1) {
          _result = l;
        } else if (std::holds_alternative<
                       typename LoopifyPatterns::list<unsigned int>::Nil>(
                       l->v())) {
          _result = list<unsigned int>::nil();
        } else {
          const auto &_m =
              *std::get_if<typename LoopifyPatterns::list<unsigned int>::Cons>(
                  &l->v());
          _stack.emplace_back(_Call1{_m, f});
          _stack.emplace_back(_Enter{_m.d_a1, f});
        }
      }
    } else if (std::holds_alternative<_Call1>(_frame)) {
      const auto &_f = std::get<_Call1>(_frame);
      const typename LoopifyPatterns::list<unsigned int>::Cons _m = _f._s0;
      unsigned int f = _f._s1;
      std::shared_ptr<LoopifyPatterns::list<unsigned int>> once = _result;
      _stack.emplace_back(_Call2{_m});
      _stack.emplace_back(_Enter{std::move(once), f});
    } else {
      const auto &_f = std::get<_Call2>(_frame);
      const typename LoopifyPatterns::list<unsigned int>::Cons _m = _f._s0;
      std::shared_ptr<LoopifyPatterns::list<unsigned int>> twice = _result;
      _result = list<unsigned int>::cons(_m.d_a0, twice);
    }
  }
  return _result;
}

std::shared_ptr<LoopifyPatterns::list<unsigned int>>
LoopifyPatterns::process_twice_alt(
    const std::shared_ptr<LoopifyPatterns::list<unsigned int>> &l) {
  return process_twice_alt_fuel(100u, l);
}

/// sum_if_positive_else_double l conditional logic on each element.
__attribute__((pure)) unsigned int LoopifyPatterns::sum_if_positive_else_double(
    const std::shared_ptr<LoopifyPatterns::list<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<LoopifyPatterns::list<unsigned int>> l;
  };

  struct _Call1 {
    const typename LoopifyPatterns::list<unsigned int>::Cons _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.emplace_back(_Enter{l});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      const auto &_f = std::get<_Enter>(_frame);
      const std::shared_ptr<LoopifyPatterns::list<unsigned int>> l = _f.l;
      if (std::holds_alternative<
              typename LoopifyPatterns::list<unsigned int>::Nil>(l->v())) {
        _result = 0u;
      } else {
        const auto &_m =
            *std::get_if<typename LoopifyPatterns::list<unsigned int>::Cons>(
                &l->v());
        _stack.emplace_back(_Call1{_m});
        _stack.emplace_back(_Enter{_m.d_a1});
      }
    } else {
      const auto &_f = std::get<_Call1>(_frame);
      const typename LoopifyPatterns::list<unsigned int>::Cons _m = _f._s0;
      unsigned int rest = _result;
      if (_m.d_a0 == 0u) {
        _result = ((2u * _m.d_a0) + rest);
      } else {
        _result = (_m.d_a0 + rest);
      }
    }
  }
  return _result;
}

/// merge_alternating l1 l2 merges two lists by alternating elements.
std::shared_ptr<LoopifyPatterns::list<unsigned int>>
LoopifyPatterns::merge_alternating(
    std::shared_ptr<LoopifyPatterns::list<unsigned int>> l1,
    std::shared_ptr<LoopifyPatterns::list<unsigned int>> l2) {
  std::shared_ptr<LoopifyPatterns::list<unsigned int>> _head{};
  std::shared_ptr<LoopifyPatterns::list<unsigned int>> _last{};
  std::shared_ptr<LoopifyPatterns::list<unsigned int>> _loop_l2 = l2;
  std::shared_ptr<LoopifyPatterns::list<unsigned int>> _loop_l1 = l1;
  bool _continue = true;
  while (_continue) {
    if (std::holds_alternative<
            typename LoopifyPatterns::list<unsigned int>::Nil>(_loop_l1->v())) {
      if (_last) {
        std::get<typename list<unsigned int>::Cons>(_last->v_mut()).d_a1 =
            std::move(_loop_l2);
      } else {
        _head = std::move(_loop_l2);
      }
      _continue = false;
    } else {
      const auto &_m =
          *std::get_if<typename LoopifyPatterns::list<unsigned int>::Cons>(
              &_loop_l1->v());
      if (std::holds_alternative<
              typename LoopifyPatterns::list<unsigned int>::Cons>(
              _loop_l2->v()) &&
          _loop_l2.use_count() == 1) {
        auto &_rf = std::get<1>(_loop_l2->v_mut());
        unsigned int y = std::move(_rf.d_a0);
        std::shared_ptr<LoopifyPatterns::list<unsigned int>> ys =
            std::move(_rf.d_a1);
        _rf.d_a0 = std::move(_m.d_a0);
        _rf.d_a1 = list<unsigned int>::cons(y, merge_alternating(_m.d_a1, ys));
        if (_last) {
          std::get<typename list<unsigned int>::Cons>(_last->v_mut()).d_a1 =
              _loop_l2;
        } else {
          _head = _loop_l2;
        }
        _continue = false;
      } else if (std::holds_alternative<
                     typename LoopifyPatterns::list<unsigned int>::Nil>(
                     _loop_l2->v())) {
        if (_last) {
          std::get<typename list<unsigned int>::Cons>(_last->v_mut()).d_a1 =
              std::move(_loop_l1);
        } else {
          _head = std::move(_loop_l1);
        }
        _continue = false;
      } else {
        const auto &_m0 =
            *std::get_if<typename LoopifyPatterns::list<unsigned int>::Cons>(
                &_loop_l2->v());
        auto _cell = list<unsigned int>::cons(_m.d_a0, nullptr);
        auto _cell1 = list<unsigned int>::cons(_m0.d_a0, nullptr);
        std::get<typename list<unsigned int>::Cons>(_cell->v_mut()).d_a1 =
            _cell1;
        if (_last) {
          std::get<typename list<unsigned int>::Cons>(_last->v_mut()).d_a1 =
              _cell;
        } else {
          _head = _cell;
        }
        _last = _cell1;
        std::shared_ptr<LoopifyPatterns::list<unsigned int>> _next_l2 =
            _m0.d_a1;
        std::shared_ptr<LoopifyPatterns::list<unsigned int>> _next_l1 = _m.d_a1;
        _loop_l2 = std::move(_next_l2);
        _loop_l1 = std::move(_next_l1);
        continue;
      }
    }
  }
  return _head;
}

/// four_elem l four-element destructuring pattern with fallback cases.
__attribute__((pure)) unsigned int LoopifyPatterns::four_elem(
    const std::shared_ptr<LoopifyPatterns::list<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<LoopifyPatterns::list<unsigned int>> l;
  };

  struct _Call1 {
    decltype(std::declval<
                 typename LoopifyPatterns::list<unsigned int>::Cons &>()
                 .d_a0) _s0;
    decltype(std::declval<
                 typename LoopifyPatterns::list<unsigned int>::Cons &>()
                 .d_a0) _s1;
    decltype(std::declval<
                 typename LoopifyPatterns::list<unsigned int>::Cons &>()
                 .d_a0) _s2;
    decltype(std::declval<
                 typename LoopifyPatterns::list<unsigned int>::Cons &>()
                 .d_a0) _s3;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.emplace_back(_Enter{l});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      const auto &_f = std::get<_Enter>(_frame);
      const std::shared_ptr<LoopifyPatterns::list<unsigned int>> l = _f.l;
      if (std::holds_alternative<
              typename LoopifyPatterns::list<unsigned int>::Nil>(l->v())) {
        _result = 0u;
      } else {
        const auto &_m =
            *std::get_if<typename LoopifyPatterns::list<unsigned int>::Cons>(
                &l->v());
        auto &&_sv0 = _m.d_a1;
        if (std::holds_alternative<
                typename LoopifyPatterns::list<unsigned int>::Nil>(_sv0->v())) {
          _result = 1u;
        } else {
          const auto &_m0 =
              *std::get_if<typename LoopifyPatterns::list<unsigned int>::Cons>(
                  &_sv0->v());
          auto &&_sv1 = _m0.d_a1;
          if (std::holds_alternative<
                  typename LoopifyPatterns::list<unsigned int>::Nil>(
                  _sv1->v())) {
            _result = 2u;
          } else {
            const auto &_m1 = *std::get_if<
                typename LoopifyPatterns::list<unsigned int>::Cons>(&_sv1->v());
            auto &&_sv2 = _m1.d_a1;
            if (std::holds_alternative<
                    typename LoopifyPatterns::list<unsigned int>::Nil>(
                    _sv2->v())) {
              _result = 3u;
            } else {
              const auto &_m2 = *std::get_if<
                  typename LoopifyPatterns::list<unsigned int>::Cons>(
                  &_sv2->v());
              _stack.emplace_back(
                  _Call1{_m.d_a0, _m0.d_a0, _m1.d_a0, _m2.d_a0});
              _stack.emplace_back(_Enter{_m2.d_a1});
            }
          }
        }
      }
    } else {
      const auto &_f = std::get<_Call1>(_frame);
      _result = (_f._s0 + (_f._s1 + (_f._s2 + (_f._s3 + _result))));
    }
  }
  return _result;
}
