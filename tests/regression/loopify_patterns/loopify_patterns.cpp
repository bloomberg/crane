#include "loopify_patterns.h"

/// Complex control flow and pattern matching edge cases.
/// multi_let n multiple sequential let bindings before recursion.
uint64_t
LoopifyPatterns::multi_let(uint64_t n) { /// CraneEnter: captures varying
                                         /// parameters for each recursive call.

  struct CraneEnter {
    uint64_t n;
  };

  /// CraneCont_m: saves [c], resumes after recursive call, then processes rest.
  struct CraneCont_m {
    uint64_t c;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont_m>;
  uint64_t _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{n});
  /// Loopified multi_let: CraneEnter -> CraneCont_m.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      uint64_t n = _f.n;
      if (n <= 0) {
        _result = UINT64_C(0);
      } else {
        uint64_t m = n - 1;
        uint64_t b = (m * UINT64_C(2));
        uint64_t c = (b + UINT64_C(3));
        _stack.emplace_back(CraneCont_m{c});
        _stack.emplace_back(CraneEnter{m});
      }
    } else {
      auto _f = std::move(std::get<CraneCont_m>(_frame));
      uint64_t c = _f.c;
      _result = (c + std::move(_result));
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
LoopifyPatterns::deep_nest(uint64_t n) { /// CraneEnter: captures varying
                                         /// parameters for each recursive call.

  struct CraneEnter {
    uint64_t n;
  };

  /// CraneCont_m: resumes after recursive call, then processes rest.
  struct CraneCont_m {};

  using CraneFrame = std::variant<CraneEnter, CraneCont_m>;
  uint64_t _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{n});
  /// Loopified deep_nest: CraneEnter -> CraneCont_m.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      uint64_t n = _f.n;
      if (n <= 0) {
        _result = UINT64_C(0);
      } else {
        uint64_t m = n - 1;
        _stack.emplace_back(CraneCont_m{});
        _stack.emplace_back(CraneEnter{m});
      }
    } else {
      auto _f = std::move(std::get<CraneCont_m>(_frame));
      _result =
          (UINT64_C(1) + (UINT64_C(1) + (UINT64_C(1) + std::move(_result))));
    }
  }
  return _result;
}

/// bool_chain n target multiple recursive calls in || chain.
bool LoopifyPatterns::bool_chain_fuel(
    uint64_t fuel, uint64_t n,
    uint64_t target) { /// CraneEnter: captures varying parameters for each
                       /// recursive call.

  struct CraneEnter {
    uint64_t n;
    uint64_t fuel;
  };

  /// CraneCont1: saves [f, n], resumes after recursive call, then processes
  /// rest.
  struct CraneCont1 {
    uint64_t f;
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
  /// Loopified bool_chain_fuel: CraneEnter -> CraneCont1 -> CraneCont2.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
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
              _stack.emplace_back(CraneCont1{f, n});
              _stack.emplace_back(CraneEnter{
                  (((n - UINT64_C(1)) > n ? 0 : (n - UINT64_C(1)))), f});
            }
          }
        }
      }
    } else if (std::holds_alternative<CraneCont1>(_frame)) {
      auto _f = std::move(std::get<CraneCont1>(_frame));
      uint64_t f = _f.f;
      uint64_t n = _f.n;
      _stack.emplace_back(CraneCont2{std::move(_result)});
      _stack.emplace_back(
          CraneEnter{(((n - UINT64_C(2)) > n ? 0 : (n - UINT64_C(2)))), f});
    } else {
      auto _f = std::move(std::get<CraneCont2>(_frame));
      _result = (_f._tmp2 || std::move(_result));
    }
  }
  return _result;
}

bool LoopifyPatterns::bool_chain(uint64_t n, uint64_t target) {
  return bool_chain_fuel(UINT64_C(1000), n, target);
}

/// chained_comp n boolean result with double recursion.
bool LoopifyPatterns::chained_comp(
    uint64_t n) { /// CraneEnter: captures varying parameters for each recursive
                  /// call.

  struct CraneEnter {
    uint64_t n;
  };

  /// CraneCont_m: saves [m], resumes after recursive call, then processes rest.
  struct CraneCont_m {
    uint64_t m;
  };

  /// CraneCont_m_1: saves [_tmp2], resumes after recursive call, then processes
  /// rest.
  struct CraneCont_m_1 {
    bool _tmp2;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont_m, CraneCont_m_1>;
  bool _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{n});
  /// Loopified chained_comp: CraneEnter -> CraneCont_m -> CraneCont_m_1.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      uint64_t n = _f.n;
      if (n <= 0) {
        _result = true;
      } else {
        uint64_t n_ = n - 1;
        if (n_ <= 0) {
          _result = true;
        } else {
          uint64_t m = n_ - 1;
          _stack.emplace_back(CraneCont_m{m});
          _stack.emplace_back(CraneEnter{n_});
        }
      }
    } else if (std::holds_alternative<CraneCont_m>(_frame)) {
      auto _f = std::move(std::get<CraneCont_m>(_frame));
      uint64_t m = _f.m;
      _stack.emplace_back(CraneCont_m_1{std::move(_result)});
      _stack.emplace_back(CraneEnter{m});
    } else {
      auto _f = std::move(std::get<CraneCont_m_1>(_frame));
      _result = (_f._tmp2 && std::move(_result));
    }
  }
  return _result;
}

/// tuple_constr n recursive calls in multiple tuple positions.
std::pair<std::pair<uint64_t, uint64_t>, uint64_t>
LoopifyPatterns::tuple_constr(
    uint64_t n) { /// CraneEnter: captures varying parameters for each recursive
                  /// call.

  struct CraneEnter {
    uint64_t n;
  };

  /// CraneCont_m: saves [n], resumes after recursive call, then processes rest.
  struct CraneCont_m {
    uint64_t n;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont_m>;
  std::pair<std::pair<uint64_t, uint64_t>, uint64_t> _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{n});
  /// Loopified tuple_constr: CraneEnter -> CraneCont_m.
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
        uint64_t m = n - 1;
        _stack.emplace_back(CraneCont_m{n});
        _stack.emplace_back(CraneEnter{m});
      }
    } else {
      auto _f = std::move(std::get<CraneCont_m>(_frame));
      uint64_t n = _f.n;
      auto [p, c] = std::move(_result);
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
      _loop_l = crane_raw(a1);
    }
  }
}

/// split_by_sign l pos neg partition with dual accumulators.
std::pair<LoopifyPatterns::list<uint64_t>, LoopifyPatterns::list<uint64_t>>
LoopifyPatterns::split_by_sign_aux(const LoopifyPatterns::list<uint64_t> &l,
                                   uint64_t base,
                                   const LoopifyPatterns::list<uint64_t> &pos,
                                   const LoopifyPatterns::list<uint64_t> &neg) {
  LoopifyPatterns::list<uint64_t> _loop_neg = neg;
  LoopifyPatterns::list<uint64_t> _loop_pos = pos;
  const LoopifyPatterns::list<uint64_t> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<typename LoopifyPatterns::list<uint64_t>::Nil>(
            _loop_l->v())) {
      return std::make_pair(_loop_pos, _loop_neg);
    } else {
      const auto &[a0, a1] =
          std::get<typename LoopifyPatterns::list<uint64_t>::Cons>(
              _loop_l->v());
      if (base <= a0) {
        _loop_pos = list<uint64_t>::cons(a0, _loop_pos);
        _loop_l = crane_raw(a1);
      } else {
        _loop_neg = list<uint64_t>::cons(a0, _loop_neg);
        _loop_l = crane_raw(a1);
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
        _loop_l = crane_raw(a1);
        _loop_acc = (_loop_acc * UINT64_C(2));
      } else {
        if (UINT64_C(50) < a0) {
          _loop_l = crane_raw(a1);
          _loop_acc = (_loop_acc + a0);
        } else {
          if (UINT64_C(0) < a0) {
            _loop_l = crane_raw(a1);
            _loop_acc = (_loop_acc + 1);
          } else {
            _loop_l = crane_raw(a1);
          }
        }
      }
    }
  }
}

/// cons_computed n l cons with conditional parameter change.
LoopifyPatterns::list<uint64_t>
LoopifyPatterns::cons_computed(uint64_t n,
                               const LoopifyPatterns::list<uint64_t> &l) {
  std::optional<LoopifyPatterns::list<uint64_t>> _root{};
  std::shared_ptr<LoopifyPatterns::list<uint64_t>> *_write = nullptr;
  const LoopifyPatterns::list<uint64_t> *_loop_l = &l;
  uint64_t _loop_n = std::move(n);
  while (true) {
    if (std::holds_alternative<typename LoopifyPatterns::list<uint64_t>::Nil>(
            _loop_l->v())) {
      auto _value = list<uint64_t>::nil();
      (_write ? *(*_write = std::make_shared<LoopifyPatterns::list<uint64_t>>(
                      std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename LoopifyPatterns::list<uint64_t>::Cons>(
              _loop_l->v());
      uint64_t next_n;
      if (UINT64_C(0) < _loop_n) {
        next_n =
            (((_loop_n - UINT64_C(1)) > _loop_n ? 0 : (_loop_n - UINT64_C(1))));
      } else {
        next_n = _loop_n;
      }
      auto _cell = typename LoopifyPatterns::list<uint64_t>::Cons(a0, nullptr);
      LoopifyPatterns::list<uint64_t> &_node =
          (_write
               ? *(*_write = std::make_shared<LoopifyPatterns::list<uint64_t>>(
                       std::move(_cell)))
               : _root.emplace(std::move(_cell)));
      _write = &std::get<typename LoopifyPatterns::list<uint64_t>::Cons>(
                    _node.v_mut())
                    .l;
      _loop_l = crane_raw(a1);
      _loop_n = next_n;
      continue;
    }
  }
  return std::move(*_root);
}

/// mod_pattern n recursive call in mod expression.
uint64_t LoopifyPatterns::mod_pattern(
    uint64_t n) { /// CraneEnter: captures varying parameters for each recursive
                  /// call.

  struct CraneEnter {
    uint64_t n;
  };

  /// CraneCont_m: saves [n_], resumes after recursive call, then processes
  /// rest.
  struct CraneCont_m {
    uint64_t n_;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont_m>;
  uint64_t _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{n});
  /// Loopified mod_pattern: CraneEnter -> CraneCont_m.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      uint64_t n = _f.n;
      if (n <= 0) {
        _result = UINT64_C(1);
      } else {
        uint64_t n_ = n - 1;
        if (n_ <= 0) {
          _result = UINT64_C(1);
        } else {
          uint64_t m = n_ - 1;
          _stack.emplace_back(CraneCont_m{n_});
          _stack.emplace_back(CraneEnter{m});
        }
      }
    } else {
      auto _f = std::move(std::get<CraneCont_m>(_frame));
      uint64_t n_ = _f.n_;
      _result = ((std::move(_result) + 1) ? n_ % (std::move(_result) + 1) : n_);
    }
  }
  return _result;
}

/// alternating_ops n alternating operations based on modulo.
uint64_t LoopifyPatterns::alternating_ops(
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
        uint64_t m = n - 1;
        if ((UINT64_C(2) ? n % UINT64_C(2) : n) == UINT64_C(0)) {
          _stack.emplace_back(CraneCont1{n});
          _stack.emplace_back(CraneEnter{m});
        } else {
          _stack.emplace_back(CraneCont2{n});
          _stack.emplace_back(CraneEnter{m});
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

/// replace_at idx value l replace element at index.
LoopifyPatterns::list<uint64_t>
LoopifyPatterns::replace_at(uint64_t idx, uint64_t value,
                            const LoopifyPatterns::list<uint64_t> &l) {
  std::optional<LoopifyPatterns::list<uint64_t>> _root{};
  std::shared_ptr<LoopifyPatterns::list<uint64_t>> *_write = nullptr;
  const LoopifyPatterns::list<uint64_t> *_loop_l = &l;
  uint64_t _loop_idx = std::move(idx);
  while (true) {
    if (std::holds_alternative<typename LoopifyPatterns::list<uint64_t>::Nil>(
            _loop_l->v())) {
      auto _value = list<uint64_t>::nil();
      (_write ? *(*_write = std::make_shared<LoopifyPatterns::list<uint64_t>>(
                      std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename LoopifyPatterns::list<uint64_t>::Cons>(
              _loop_l->v());
      if (_loop_idx <= 0) {
        auto _value = list<uint64_t>::cons(value, *a1);
        (_write ? *(*_write = std::make_shared<LoopifyPatterns::list<uint64_t>>(
                        std::move(_value)))
                : _root.emplace(std::move(_value)));
        break;
      } else {
        uint64_t i = _loop_idx - 1;
        auto _cell =
            typename LoopifyPatterns::list<uint64_t>::Cons(a0, nullptr);
        LoopifyPatterns::list<uint64_t> &_node =
            (_write ? *(*_write =
                            std::make_shared<LoopifyPatterns::list<uint64_t>>(
                                std::move(_cell)))
                    : _root.emplace(std::move(_cell)));
        _write = &std::get<typename LoopifyPatterns::list<uint64_t>::Cons>(
                      _node.v_mut())
                      .l;
        _loop_l = crane_raw(a1);
        _loop_idx = i;
        continue;
      }
    }
  }
  return std::move(*_root);
}

/// nested_pattern l three-element tuple pattern.
uint64_t LoopifyPatterns::nested_pattern(
    const LoopifyPatterns::list<
        std::pair<std::pair<uint64_t, uint64_t>, uint64_t>>
        &l) { /// CraneEnter: captures varying parameters for each recursive
              /// call.

  struct CraneEnter {
    const LoopifyPatterns::list<
        std::pair<std::pair<uint64_t, uint64_t>, uint64_t>> *l;
  };

  /// CraneCont_a: saves [a, b, c], resumes after recursive call, then processes
  /// rest.
  struct CraneCont_a {
    uint64_t a;
    uint64_t b;
    uint64_t c;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont_a>;
  uint64_t _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{&l});
  /// Loopified nested_pattern: CraneEnter -> CraneCont_a.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
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
        _stack.emplace_back(CraneCont_a{a, b, c});
        _stack.emplace_back(CraneEnter{crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<CraneCont_a>(_frame));
      uint64_t a = _f.a;
      uint64_t b = _f.b;
      uint64_t c = _f.c;
      _result = (a + (b + (c + std::move(_result))));
    }
  }
  return _result;
}

/// let_nested n let with nested let in binding.
uint64_t LoopifyPatterns::let_nested(
    uint64_t n) { /// CraneEnter: captures varying parameters for each recursive
                  /// call.

  struct CraneEnter {
    uint64_t n;
  };

  /// CraneCont_m: saves [a], resumes after recursive call, then processes rest.
  struct CraneCont_m {
    uint64_t a;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont_m>;
  uint64_t _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{n});
  /// Loopified let_nested: CraneEnter -> CraneCont_m.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      uint64_t n = _f.n;
      if (n <= 0) {
        _result = UINT64_C(0);
      } else {
        uint64_t m = n - 1;
        uint64_t a = (m + 1);
        _stack.emplace_back(CraneCont_m{a});
        _stack.emplace_back(CraneEnter{m});
      }
    } else {
      auto _f = std::move(std::get<CraneCont_m>(_frame));
      uint64_t a = _f.a;
      _result = (a + std::move(_result));
    }
  }
  return _result;
}

/// Helper: list length.
uint64_t
LoopifyPatterns::list_len(const LoopifyPatterns::list<uint64_t>
                              &l) { /// CraneEnter: captures varying parameters
                                    /// for each recursive call.

  struct CraneEnter {
    const LoopifyPatterns::list<uint64_t> *l;
  };

  /// CraneCont_Cons: resumes after recursive call, then processes rest.
  struct CraneCont_Cons {};

  using CraneFrame = std::variant<CraneEnter, CraneCont_Cons>;
  uint64_t _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{&l});
  /// Loopified list_len: CraneEnter -> CraneCont_Cons.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      const LoopifyPatterns::list<uint64_t> &l = *_f.l;
      if (std::holds_alternative<typename LoopifyPatterns::list<uint64_t>::Nil>(
              l.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] =
            std::get<typename LoopifyPatterns::list<uint64_t>::Cons>(l.v());
        _stack.emplace_back(CraneCont_Cons{});
        _stack.emplace_back(CraneEnter{crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<CraneCont_Cons>(_frame));
      _result = (std::move(_result) + 1);
    }
  }
  return _result;
}

/// process_twice l applies recursion twice: process(process(xs)).
LoopifyPatterns::list<uint64_t> LoopifyPatterns::process_twice_fuel(
    uint64_t fuel,
    LoopifyPatterns::list<uint64_t> l) { /// CraneEnter: captures varying
                                         /// parameters for each recursive call.

  struct CraneEnter {
    LoopifyPatterns::list<uint64_t> l;
    uint64_t fuel;
  };

  /// CraneCont_Cons: saves [a0, f], resumes after recursive call, then
  /// processes rest.
  struct CraneCont_Cons {
    uint64_t a0;
    uint64_t f;
  };

  /// CraneCont_Cons_1: saves [a0], resumes after recursive call, then processes
  /// rest.
  struct CraneCont_Cons_1 {
    uint64_t a0;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont_Cons, CraneCont_Cons_1>;
  LoopifyPatterns::list<uint64_t> _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{std::move(l), fuel});
  /// Loopified process_twice_fuel: CraneEnter -> CraneCont_Cons ->
  /// CraneCont_Cons_1.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
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
          _stack.emplace_back(CraneCont_Cons{a0, f});
          _stack.emplace_back(CraneEnter{*a1, f});
        }
      }
    } else if (std::holds_alternative<CraneCont_Cons>(_frame)) {
      auto _f = std::move(std::get<CraneCont_Cons>(_frame));
      uint64_t a0 = _f.a0;
      uint64_t f = _f.f;
      LoopifyPatterns::list<uint64_t> first = std::move(_result);
      _stack.emplace_back(CraneCont_Cons_1{a0});
      _stack.emplace_back(CraneEnter{std::move(first), f});
    } else {
      auto _f = std::move(std::get<CraneCont_Cons_1>(_frame));
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
LoopifyPatterns::list<uint64_t>
LoopifyPatterns::as_guard_fuel(uint64_t fuel,
                               const LoopifyPatterns::list<uint64_t> &l) {
  std::optional<LoopifyPatterns::list<uint64_t>> _root{};
  std::shared_ptr<LoopifyPatterns::list<uint64_t>> *_write = nullptr;
  const LoopifyPatterns::list<uint64_t> *_loop_l = &l;
  uint64_t _loop_fuel = std::move(fuel);
  while (true) {
    if (_loop_fuel <= 0) {
      auto _value = list<uint64_t>::nil();
      (_write ? *(*_write = std::make_shared<LoopifyPatterns::list<uint64_t>>(
                      std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      uint64_t f = _loop_fuel - 1;
      if (std::holds_alternative<typename LoopifyPatterns::list<uint64_t>::Nil>(
              _loop_l->v())) {
        auto _value = list<uint64_t>::nil();
        (_write ? *(*_write = std::make_shared<LoopifyPatterns::list<uint64_t>>(
                        std::move(_value)))
                : _root.emplace(std::move(_value)));
        break;
      } else {
        const auto &[a0, a1] =
            std::get<typename LoopifyPatterns::list<uint64_t>::Cons>(
                _loop_l->v());
        LoopifyPatterns::list<uint64_t> all = list<uint64_t>::cons(a0, *a1);
        if (UINT64_C(3) < list_len(std::move(all))) {
          auto _cell =
              typename LoopifyPatterns::list<uint64_t>::Cons(a0, nullptr);
          LoopifyPatterns::list<uint64_t> &_node =
              (_write ? *(*_write =
                              std::make_shared<LoopifyPatterns::list<uint64_t>>(
                                  std::move(_cell)))
                      : _root.emplace(std::move(_cell)));
          _write = &std::get<typename LoopifyPatterns::list<uint64_t>::Cons>(
                        _node.v_mut())
                        .l;
          _loop_l = crane_raw(a1);
          _loop_fuel = f;
          continue;
        } else {
          _loop_l = crane_raw(a1);
          _loop_fuel = f;
          continue;
        }
      }
    }
  }
  return std::move(*_root);
}

LoopifyPatterns::list<uint64_t>
LoopifyPatterns::as_guard(const LoopifyPatterns::list<uint64_t> &l) {
  return as_guard_fuel(UINT64_C(100), l);
}

/// quad_sum_pattern l pattern with 4-way split.
uint64_t LoopifyPatterns::quad_sum_pattern(
    const LoopifyPatterns::list<uint64_t>
        &l) { /// CraneEnter: captures varying parameters for each recursive
              /// call.

  struct CraneEnter {
    const LoopifyPatterns::list<uint64_t> *l;
  };

  /// CraneCont_Cons: saves [a0, a00, a01, a02], resumes after recursive call,
  /// then processes rest.
  struct CraneCont_Cons {
    uint64_t a0;
    uint64_t a00;
    uint64_t a01;
    uint64_t a02;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont_Cons>;
  uint64_t _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{&l});
  /// Loopified quad_sum_pattern: CraneEnter -> CraneCont_Cons.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
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
              _stack.emplace_back(CraneCont_Cons{a0, a00, a01, a02});
              _stack.emplace_back(CraneEnter{crane_raw(a12)});
            }
          }
        }
      }
    } else {
      auto _f = std::move(std::get<CraneCont_Cons>(_frame));
      uint64_t a0 = _f.a0;
      uint64_t a00 = _f.a00;
      uint64_t a01 = _f.a01;
      uint64_t a02 = _f.a02;
      _result = ((a0 + a00) + ((a01 + a02) + std::move(_result)));
    }
  }
  return _result;
}

/// multi_guard l demonstrates pattern with multiple conditional branches.
uint64_t
LoopifyPatterns::multi_guard(const LoopifyPatterns::list<uint64_t>
                                 &l) { /// CraneEnter: captures varying
                                       /// parameters for each recursive call.

  struct CraneEnter {
    const LoopifyPatterns::list<uint64_t> *l;
  };

  /// CraneCont_Cons: saves [a0], resumes after recursive call, then processes
  /// rest.
  struct CraneCont_Cons {
    uint64_t a0;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont_Cons>;
  uint64_t _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{&l});
  /// Loopified multi_guard: CraneEnter -> CraneCont_Cons.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      const LoopifyPatterns::list<uint64_t> &l = *_f.l;
      if (std::holds_alternative<typename LoopifyPatterns::list<uint64_t>::Nil>(
              l.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] =
            std::get<typename LoopifyPatterns::list<uint64_t>::Cons>(l.v());
        _stack.emplace_back(CraneCont_Cons{a0});
        _stack.emplace_back(CraneEnter{crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<CraneCont_Cons>(_frame));
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
LoopifyPatterns::list<uint64_t>
LoopifyPatterns::append_lists(const LoopifyPatterns::list<uint64_t> &l1,
                              LoopifyPatterns::list<uint64_t> l2) {
  std::optional<LoopifyPatterns::list<uint64_t>> _root{};
  std::shared_ptr<LoopifyPatterns::list<uint64_t>> *_write = nullptr;
  LoopifyPatterns::list<uint64_t> _loop_l2 = std::move(l2);
  const LoopifyPatterns::list<uint64_t> *_loop_l1 = &l1;
  while (true) {
    if (std::holds_alternative<typename LoopifyPatterns::list<uint64_t>::Nil>(
            _loop_l1->v())) {
      auto _value = std::move(_loop_l2);
      (_write ? *(*_write = std::make_shared<LoopifyPatterns::list<uint64_t>>(
                      std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename LoopifyPatterns::list<uint64_t>::Cons>(
              _loop_l1->v());
      auto _cell = typename LoopifyPatterns::list<uint64_t>::Cons(a0, nullptr);
      LoopifyPatterns::list<uint64_t> &_node =
          (_write
               ? *(*_write = std::make_shared<LoopifyPatterns::list<uint64_t>>(
                       std::move(_cell)))
               : _root.emplace(std::move(_cell)));
      _write = &std::get<typename LoopifyPatterns::list<uint64_t>::Cons>(
                    _node.v_mut())
                    .l;
      _loop_l1 = crane_raw(a1);
      continue;
    }
  }
  return std::move(*_root);
}

/// double_append l1 l2 uses recursive result twice: h :: (rest @ rest).
LoopifyPatterns::list<uint64_t>
LoopifyPatterns::double_append(const LoopifyPatterns::list<uint64_t> &l1,
                               LoopifyPatterns::list<uint64_t>
                                   l2) { /// CraneEnter: captures varying
                                         /// parameters for each recursive call.

  struct CraneEnter {
    LoopifyPatterns::list<uint64_t> l2;
    const LoopifyPatterns::list<uint64_t> *l1;
  };

  /// CraneCont_Cons: saves [a0], resumes after recursive call, then processes
  /// rest.
  struct CraneCont_Cons {
    uint64_t a0;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont_Cons>;
  LoopifyPatterns::list<uint64_t> _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{std::move(l2), &l1});
  /// Loopified double_append: CraneEnter -> CraneCont_Cons.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      LoopifyPatterns::list<uint64_t> l2 = std::move(_f.l2);
      const LoopifyPatterns::list<uint64_t> &l1 = *_f.l1;
      if (std::holds_alternative<typename LoopifyPatterns::list<uint64_t>::Nil>(
              l1.v())) {
        _result = std::move(l2);
      } else {
        const auto &[a0, a1] =
            std::get<typename LoopifyPatterns::list<uint64_t>::Cons>(l1.v());
        _stack.emplace_back(CraneCont_Cons{a0});
        _stack.emplace_back(CraneEnter{std::move(l2), crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<CraneCont_Cons>(_frame));
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
    LoopifyPatterns::list<uint64_t> l) { /// CraneEnter: captures varying
                                         /// parameters for each recursive call.

  struct CraneEnter {
    LoopifyPatterns::list<uint64_t> l;
    uint64_t fuel;
  };

  /// CraneCont_Cons: saves [a0, f], resumes after recursive call, then
  /// processes rest.
  struct CraneCont_Cons {
    uint64_t a0;
    uint64_t f;
  };

  /// CraneCont_Cons_1: saves [a0], resumes after recursive call, then processes
  /// rest.
  struct CraneCont_Cons_1 {
    uint64_t a0;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont_Cons, CraneCont_Cons_1>;
  LoopifyPatterns::list<uint64_t> _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{std::move(l), fuel});
  /// Loopified process_twice_alt_fuel: CraneEnter -> CraneCont_Cons ->
  /// CraneCont_Cons_1.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
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
          _stack.emplace_back(CraneCont_Cons{a0, f});
          _stack.emplace_back(CraneEnter{*a1, f});
        }
      }
    } else if (std::holds_alternative<CraneCont_Cons>(_frame)) {
      auto _f = std::move(std::get<CraneCont_Cons>(_frame));
      uint64_t a0 = _f.a0;
      uint64_t f = _f.f;
      LoopifyPatterns::list<uint64_t> once = std::move(_result);
      _stack.emplace_back(CraneCont_Cons_1{a0});
      _stack.emplace_back(CraneEnter{std::move(once), f});
    } else {
      auto _f = std::move(std::get<CraneCont_Cons_1>(_frame));
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
        &l) { /// CraneEnter: captures varying parameters for each recursive
              /// call.

  struct CraneEnter {
    const LoopifyPatterns::list<uint64_t> *l;
  };

  /// CraneCont_Cons: saves [a0], resumes after recursive call, then processes
  /// rest.
  struct CraneCont_Cons {
    uint64_t a0;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont_Cons>;
  uint64_t _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{&l});
  /// Loopified sum_if_positive_else_double: CraneEnter -> CraneCont_Cons.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      const LoopifyPatterns::list<uint64_t> &l = *_f.l;
      if (std::holds_alternative<typename LoopifyPatterns::list<uint64_t>::Nil>(
              l.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] =
            std::get<typename LoopifyPatterns::list<uint64_t>::Cons>(l.v());
        _stack.emplace_back(CraneCont_Cons{a0});
        _stack.emplace_back(CraneEnter{crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<CraneCont_Cons>(_frame));
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
LoopifyPatterns::list<uint64_t>
LoopifyPatterns::merge_alternating(LoopifyPatterns::list<uint64_t> l1,
                                   LoopifyPatterns::list<uint64_t> l2) {
  std::optional<LoopifyPatterns::list<uint64_t>> _root{};
  std::shared_ptr<LoopifyPatterns::list<uint64_t>> *_write = nullptr;
  LoopifyPatterns::list<uint64_t> _loop_l2 = std::move(l2);
  LoopifyPatterns::list<uint64_t> _loop_l1 = std::move(l1);
  while (true) {
    if (std::holds_alternative<typename LoopifyPatterns::list<uint64_t>::Nil>(
            _loop_l1.v_mut())) {
      auto _value = std::move(_loop_l2);
      (_write ? *(*_write = std::make_shared<LoopifyPatterns::list<uint64_t>>(
                      std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      auto &[a0, a1] = std::get<typename LoopifyPatterns::list<uint64_t>::Cons>(
          _loop_l1.v_mut());
      if (std::holds_alternative<typename LoopifyPatterns::list<uint64_t>::Nil>(
              _loop_l2.v_mut())) {
        auto _value = _loop_l1;
        (_write ? *(*_write = std::make_shared<LoopifyPatterns::list<uint64_t>>(
                        std::move(_value)))
                : _root.emplace(std::move(_value)));
        break;
      } else {
        auto &[a00, a10] =
            std::get<typename LoopifyPatterns::list<uint64_t>::Cons>(
                _loop_l2.v_mut());
        auto _cell1 = std::make_shared<LoopifyPatterns::list<uint64_t>>(
            typename LoopifyPatterns::list<uint64_t>::Cons(std::move(a00),
                                                           nullptr));
        auto _cell = typename LoopifyPatterns::list<uint64_t>::Cons(
            a0, std::move(_cell1));
        LoopifyPatterns::list<uint64_t> &_node =
            (_write ? *(*_write =
                            std::make_shared<LoopifyPatterns::list<uint64_t>>(
                                std::move(_cell)))
                    : _root.emplace(std::move(_cell)));
        _write = &std::get<typename LoopifyPatterns::list<uint64_t>::Cons>(
                      std::get<typename LoopifyPatterns::list<uint64_t>::Cons>(
                          _node.v_mut())
                          .l->v_mut())
                      .l;
        _loop_l2 = LoopifyPatterns::list<uint64_t>(*a10);
        _loop_l1 = LoopifyPatterns::list<uint64_t>(*a1);
        continue;
      }
    }
  }
  return std::move(*_root);
}

/// four_elem l four-element destructuring pattern with fallback cases.
uint64_t
LoopifyPatterns::four_elem(const LoopifyPatterns::list<uint64_t>
                               &l) { /// CraneEnter: captures varying parameters
                                     /// for each recursive call.

  struct CraneEnter {
    const LoopifyPatterns::list<uint64_t> *l;
  };

  /// CraneCont_Cons: saves [a0, a00, a01, a02], resumes after recursive call,
  /// then processes rest.
  struct CraneCont_Cons {
    uint64_t a0;
    uint64_t a00;
    uint64_t a01;
    uint64_t a02;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont_Cons>;
  uint64_t _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{&l});
  /// Loopified four_elem: CraneEnter -> CraneCont_Cons.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
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
              _stack.emplace_back(CraneCont_Cons{a0, a00, a01, a02});
              _stack.emplace_back(CraneEnter{crane_raw(a12)});
            }
          }
        }
      }
    } else {
      auto _f = std::move(std::get<CraneCont_Cons>(_frame));
      uint64_t a0 = _f.a0;
      uint64_t a00 = _f.a00;
      uint64_t a01 = _f.a01;
      uint64_t a02 = _f.a02;
      _result = (a0 + (a00 + (a01 + (a02 + std::move(_result)))));
    }
  }
  return _result;
}
