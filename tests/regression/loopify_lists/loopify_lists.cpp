#include "loopify_lists.h"

/// Consolidated UNIQUE list operations - no stdlib duplicates.
/// Tests loopification on domain-specific list algorithms.
/// range start count generates start, start+1, ..., start+count-1.
LoopifyLists::list<uint64_t> LoopifyLists::range(uint64_t start,
                                                 uint64_t count0) {
  std::unique_ptr<LoopifyLists::list<uint64_t>> _head{};
  std::unique_ptr<LoopifyLists::list<uint64_t>> *_write = &_head;
  uint64_t _loop_count0 = std::move(count0);
  uint64_t _loop_start = std::move(start);
  while (true) {
    if (_loop_count0 <= 0) {
      *_write =
          std::make_unique<LoopifyLists::list<uint64_t>>(list<uint64_t>::nil());
      break;
    } else {
      uint64_t c = _loop_count0 - 1;
      auto _cell = std::make_unique<LoopifyLists::list<uint64_t>>(
          typename list<uint64_t>::Cons(_loop_start, nullptr));
      *_write = std::move(_cell);
      _write = &std::get<typename list<uint64_t>::Cons>((*_write)->v_mut()).a1;
      _loop_count0 = c;
      _loop_start = (_loop_start + 1);
      continue;
    }
  }
  return std::move(*_head);
}

/// step_sum l sums with conditional contributions: even values as-is, odd
/// doubled.
uint64_t LoopifyLists::step_sum(
    const LoopifyLists::list<uint64_t>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const LoopifyLists::list<uint64_t> *l;
  };

  /// _Resume_Cons: saves [contribution], resumes after recursive call with
  /// _result.
  struct _Resume_Cons {
    uint64_t contribution;
  };

  using _Frame = std::variant<_Enter, _Resume_Cons>;
  uint64_t _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l});
  /// Loopified step_sum: _Enter -> _Resume_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const LoopifyLists::list<uint64_t> &l = *_f.l;
      if (std::holds_alternative<typename LoopifyLists::list<uint64_t>::Nil>(
              l.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] =
            std::get<typename LoopifyLists::list<uint64_t>::Cons>(l.v());
        uint64_t contribution;
        if ((UINT64_C(2) ? a0 % UINT64_C(2) : a0) == UINT64_C(0)) {
          contribution = a0;
        } else {
          contribution = (a0 * UINT64_C(2));
        }
        _stack.emplace_back(_Resume_Cons{contribution});
        _stack.emplace_back(_Enter{a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Resume_Cons>(_frame));
      _result = (_f.contribution + _result);
    }
  }
  return _result;
}

/// sum_abs l sums absolute values (using monus for nat).
uint64_t
LoopifyLists::sum_abs(const LoopifyLists::list<uint64_t> &l,
                      uint64_t base) { /// _Enter: captures varying parameters
                                       /// for each recursive call.

  struct _Enter {
    const LoopifyLists::list<uint64_t> *l;
  };

  /// _Resume_Cons: saves [abs_val], resumes after recursive call with _result.
  struct _Resume_Cons {
    uint64_t abs_val;
  };

  using _Frame = std::variant<_Enter, _Resume_Cons>;
  uint64_t _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l});
  /// Loopified sum_abs: _Enter -> _Resume_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const LoopifyLists::list<uint64_t> &l = *_f.l;
      if (std::holds_alternative<typename LoopifyLists::list<uint64_t>::Nil>(
              l.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] =
            std::get<typename LoopifyLists::list<uint64_t>::Cons>(l.v());
        uint64_t abs_val;
        if (base <= a0) {
          abs_val = (((a0 - base) > a0 ? 0 : (a0 - base)));
        } else {
          abs_val = (((base - a0) > base ? 0 : (base - a0)));
        }
        _stack.emplace_back(_Resume_Cons{abs_val});
        _stack.emplace_back(_Enter{a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Resume_Cons>(_frame));
      _result = (_f.abs_val + _result);
    }
  }
  return _result;
}

/// four_elem l multi-case pattern matching on list structure.
uint64_t LoopifyLists::four_elem(
    const LoopifyLists::list<uint64_t>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const LoopifyLists::list<uint64_t> *l;
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
  /// Loopified four_elem: _Enter -> _Resume_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const LoopifyLists::list<uint64_t> &l = *_f.l;
      if (std::holds_alternative<typename LoopifyLists::list<uint64_t>::Nil>(
              l.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] =
            std::get<typename LoopifyLists::list<uint64_t>::Cons>(l.v());
        auto &&_sv0 = *a1;
        if (std::holds_alternative<typename LoopifyLists::list<uint64_t>::Nil>(
                _sv0.v())) {
          _result = UINT64_C(1);
        } else {
          const auto &[a00, a10] =
              std::get<typename LoopifyLists::list<uint64_t>::Cons>(_sv0.v());
          auto &&_sv1 = *a10;
          if (std::holds_alternative<
                  typename LoopifyLists::list<uint64_t>::Nil>(_sv1.v())) {
            _result = UINT64_C(2);
          } else {
            const auto &[a01, a11] =
                std::get<typename LoopifyLists::list<uint64_t>::Cons>(_sv1.v());
            auto &&_sv2 = *a11;
            if (std::holds_alternative<
                    typename LoopifyLists::list<uint64_t>::Nil>(_sv2.v())) {
              _result = UINT64_C(3);
            } else {
              const auto &[a02, a12] =
                  std::get<typename LoopifyLists::list<uint64_t>::Cons>(
                      _sv2.v());
              _stack.emplace_back(_Resume_Cons{(a0 + a00), (a01 + a02)});
              _stack.emplace_back(_Enter{a12.get()});
            }
          }
        }
      }
    } else {
      auto _f = std::move(std::get<_Resume_Cons>(_frame));
      _result = (_f._s0 + (_f._s1 + _result));
    }
  }
  return _result;
}

/// between lo hi l filters elements in range lo, hi.
LoopifyLists::list<uint64_t>
LoopifyLists::between(uint64_t lo, uint64_t hi,
                      const LoopifyLists::list<uint64_t> &l) {
  std::unique_ptr<LoopifyLists::list<uint64_t>> _head{};
  std::unique_ptr<LoopifyLists::list<uint64_t>> *_write = &_head;
  const LoopifyLists::list<uint64_t> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<typename LoopifyLists::list<uint64_t>::Nil>(
            _loop_l->v())) {
      *_write =
          std::make_unique<LoopifyLists::list<uint64_t>>(list<uint64_t>::nil());
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename LoopifyLists::list<uint64_t>::Cons>(_loop_l->v());
      if ((lo <= a0 && a0 <= hi)) {
        auto _cell = std::make_unique<LoopifyLists::list<uint64_t>>(
            typename list<uint64_t>::Cons(a0, nullptr));
        *_write = std::move(_cell);
        _write =
            &std::get<typename list<uint64_t>::Cons>((*_write)->v_mut()).a1;
        _loop_l = a1.get();
        continue;
      } else {
        _loop_l = a1.get();
        continue;
      }
    }
  }
  return std::move(*_head);
}

/// categorize k l categorizes elements: 1 for <k, 2 for =k, 3 for >k.
uint64_t LoopifyLists::categorize(
    uint64_t k,
    const LoopifyLists::list<uint64_t>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const LoopifyLists::list<uint64_t> *l;
  };

  /// _Resume_Cons: saves [score], resumes after recursive call with _result.
  struct _Resume_Cons {
    uint64_t score;
  };

  using _Frame = std::variant<_Enter, _Resume_Cons>;
  uint64_t _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l});
  /// Loopified categorize: _Enter -> _Resume_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const LoopifyLists::list<uint64_t> &l = *_f.l;
      if (std::holds_alternative<typename LoopifyLists::list<uint64_t>::Nil>(
              l.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] =
            std::get<typename LoopifyLists::list<uint64_t>::Cons>(l.v());
        uint64_t score;
        if (k < a0) {
          score = UINT64_C(3);
        } else {
          if (a0 == k) {
            score = UINT64_C(2);
          } else {
            score = UINT64_C(1);
          }
        }
        _stack.emplace_back(_Resume_Cons{score});
        _stack.emplace_back(_Enter{a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Resume_Cons>(_frame));
      _result = (_f.score + _result);
    }
  }
  return _result;
}

/// max_prefix_sum l maximum prefix sum (Kadane-like).
uint64_t LoopifyLists::max_prefix_sum(
    const LoopifyLists::list<uint64_t>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const LoopifyLists::list<uint64_t> *l;
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
  /// Loopified max_prefix_sum: _Enter -> _Cont_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const LoopifyLists::list<uint64_t> &l = *_f.l;
      if (std::holds_alternative<typename LoopifyLists::list<uint64_t>::Nil>(
              l.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] =
            std::get<typename LoopifyLists::list<uint64_t>::Cons>(l.v());
        _stack.emplace_back(_Cont_Cons{a0});
        _stack.emplace_back(_Enter{a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Cont_Cons>(_frame));
      uint64_t a0 = _f.a0;
      uint64_t rest = _result;
      uint64_t sum = (a0 + rest);
      if (UINT64_C(0) <= sum) {
        _result = std::move(sum);
      } else {
        _result = UINT64_C(0);
      }
    }
  }
  return _result;
}

/// pairwise_sum l sums consecutive pairs: 1,2,3,4 -> 3,7.
LoopifyLists::list<uint64_t>
LoopifyLists::pairwise_sum(const LoopifyLists::list<uint64_t> &l) {
  std::unique_ptr<LoopifyLists::list<uint64_t>> _head{};
  std::unique_ptr<LoopifyLists::list<uint64_t>> *_write = &_head;
  const LoopifyLists::list<uint64_t> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<typename LoopifyLists::list<uint64_t>::Nil>(
            _loop_l->v())) {
      *_write =
          std::make_unique<LoopifyLists::list<uint64_t>>(list<uint64_t>::nil());
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename LoopifyLists::list<uint64_t>::Cons>(_loop_l->v());
      auto &&_sv0 = *a1;
      if (std::holds_alternative<typename LoopifyLists::list<uint64_t>::Nil>(
              _sv0.v())) {
        *_write = std::make_unique<LoopifyLists::list<uint64_t>>(
            list<uint64_t>::nil());
        break;
      } else {
        const auto &[a00, a10] =
            std::get<typename LoopifyLists::list<uint64_t>::Cons>(_sv0.v());
        auto _cell = std::make_unique<LoopifyLists::list<uint64_t>>(
            typename list<uint64_t>::Cons((a0 + a00), nullptr));
        *_write = std::move(_cell);
        _write =
            &std::get<typename list<uint64_t>::Cons>((*_write)->v_mut()).a1;
        _loop_l = a10.get();
        continue;
      }
    }
  }
  return std::move(*_head);
}

/// weighted_sum i l weighted sum with increasing weights.
uint64_t LoopifyLists::weighted_sum(
    uint64_t i,
    const LoopifyLists::list<uint64_t>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const LoopifyLists::list<uint64_t> *l;
    uint64_t i;
  };

  /// _Resume_Cons: saves [_s0], resumes after recursive call with _result.
  struct _Resume_Cons {
    uint64_t _s0;
  };

  using _Frame = std::variant<_Enter, _Resume_Cons>;
  uint64_t _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l, i});
  /// Loopified weighted_sum: _Enter -> _Resume_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const LoopifyLists::list<uint64_t> &l = *_f.l;
      uint64_t i = _f.i;
      if (std::holds_alternative<typename LoopifyLists::list<uint64_t>::Nil>(
              l.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] =
            std::get<typename LoopifyLists::list<uint64_t>::Cons>(l.v());
        _stack.emplace_back(_Resume_Cons{(i * a0)});
        _stack.emplace_back(_Enter{a1.get(), (i + 1)});
      }
    } else {
      auto _f = std::move(std::get<_Resume_Cons>(_frame));
      _result = (_f._s0 + _result);
    }
  }
  return _result;
}

/// prefix_sums acc l returns all prefix sums: 1,2,3 -> 0,1,3,6.
LoopifyLists::list<uint64_t>
LoopifyLists::prefix_sums(uint64_t acc, const LoopifyLists::list<uint64_t> &l) {
  std::unique_ptr<LoopifyLists::list<uint64_t>> _head{};
  std::unique_ptr<LoopifyLists::list<uint64_t>> *_write = &_head;
  const LoopifyLists::list<uint64_t> *_loop_l = &l;
  uint64_t _loop_acc = std::move(acc);
  while (true) {
    if (std::holds_alternative<typename LoopifyLists::list<uint64_t>::Nil>(
            _loop_l->v())) {
      *_write = std::make_unique<LoopifyLists::list<uint64_t>>(
          list<uint64_t>::cons(_loop_acc, list<uint64_t>::nil()));
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename LoopifyLists::list<uint64_t>::Cons>(_loop_l->v());
      auto _cell = std::make_unique<LoopifyLists::list<uint64_t>>(
          typename list<uint64_t>::Cons(_loop_acc, nullptr));
      *_write = std::move(_cell);
      _write = &std::get<typename list<uint64_t>::Cons>((*_write)->v_mut()).a1;
      _loop_l = a1.get();
      _loop_acc = (_loop_acc + a0);
      continue;
    }
  }
  return std::move(*_head);
}

/// uniq_sorted l removes consecutive duplicates from sorted list.
LoopifyLists::list<uint64_t>
LoopifyLists::uniq_sorted(const LoopifyLists::list<uint64_t> &l) {
  std::unique_ptr<LoopifyLists::list<uint64_t>> _head{};
  std::unique_ptr<LoopifyLists::list<uint64_t>> *_write = &_head;
  const LoopifyLists::list<uint64_t> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<typename LoopifyLists::list<uint64_t>::Nil>(
            _loop_l->v())) {
      *_write =
          std::make_unique<LoopifyLists::list<uint64_t>>(list<uint64_t>::nil());
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename LoopifyLists::list<uint64_t>::Cons>(_loop_l->v());
      auto &&_sv0 = *a1;
      if (std::holds_alternative<typename LoopifyLists::list<uint64_t>::Nil>(
              _sv0.v())) {
        *_write = std::make_unique<LoopifyLists::list<uint64_t>>(
            list<uint64_t>::cons(a0, list<uint64_t>::nil()));
        break;
      } else {
        const auto &[a00, a10] =
            std::get<typename LoopifyLists::list<uint64_t>::Cons>(_sv0.v());
        if (a0 == a00) {
          _loop_l = a1.get();
          continue;
        } else {
          auto _cell = std::make_unique<LoopifyLists::list<uint64_t>>(
              typename list<uint64_t>::Cons(a0, nullptr));
          *_write = std::move(_cell);
          _write =
              &std::get<typename list<uint64_t>::Cons>((*_write)->v_mut()).a1;
          _loop_l = a1.get();
          continue;
        }
      }
    }
  }
  return std::move(*_head);
}

/// Helper: take first n elements.
LoopifyLists::list<uint64_t>
LoopifyLists::take_n(uint64_t n, const LoopifyLists::list<uint64_t> &l) {
  std::unique_ptr<LoopifyLists::list<uint64_t>> _head{};
  std::unique_ptr<LoopifyLists::list<uint64_t>> *_write = &_head;
  const LoopifyLists::list<uint64_t> *_loop_l = &l;
  uint64_t _loop_n = std::move(n);
  while (true) {
    if (_loop_n <= 0) {
      *_write =
          std::make_unique<LoopifyLists::list<uint64_t>>(list<uint64_t>::nil());
      break;
    } else {
      uint64_t m = _loop_n - 1;
      if (std::holds_alternative<typename LoopifyLists::list<uint64_t>::Nil>(
              _loop_l->v())) {
        *_write = std::make_unique<LoopifyLists::list<uint64_t>>(
            list<uint64_t>::nil());
        break;
      } else {
        const auto &[a0, a1] =
            std::get<typename LoopifyLists::list<uint64_t>::Cons>(_loop_l->v());
        auto _cell = std::make_unique<LoopifyLists::list<uint64_t>>(
            typename list<uint64_t>::Cons(a0, nullptr));
        *_write = std::move(_cell);
        _write =
            &std::get<typename list<uint64_t>::Cons>((*_write)->v_mut()).a1;
        _loop_l = a1.get();
        _loop_n = m;
        continue;
      }
    }
  }
  return std::move(*_head);
}

/// Helper: list length.
uint64_t LoopifyLists::len_list(
    const LoopifyLists::list<uint64_t>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const LoopifyLists::list<uint64_t> *l;
  };

  /// _Resume_Cons: resumes after recursive call with _result.
  struct _Resume_Cons {};

  using _Frame = std::variant<_Enter, _Resume_Cons>;
  uint64_t _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l});
  /// Loopified len_list: _Enter -> _Resume_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const LoopifyLists::list<uint64_t> &l = *_f.l;
      if (std::holds_alternative<typename LoopifyLists::list<uint64_t>::Nil>(
              l.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] =
            std::get<typename LoopifyLists::list<uint64_t>::Cons>(l.v());
        _stack.emplace_back(_Resume_Cons{});
        _stack.emplace_back(_Enter{a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Resume_Cons>(_frame));
      _result = (_result + 1);
    }
  }
  return _result;
}

/// windows n l returns all sliding windows of size n.
LoopifyLists::list<LoopifyLists::list<uint64_t>>
LoopifyLists::windows_aux(uint64_t fuel, uint64_t n,
                          const LoopifyLists::list<uint64_t> &l) {
  std::unique_ptr<LoopifyLists::list<LoopifyLists::list<uint64_t>>> _head{};
  std::unique_ptr<LoopifyLists::list<LoopifyLists::list<uint64_t>>> *_write =
      &_head;
  const LoopifyLists::list<uint64_t> *_loop_l = &l;
  uint64_t _loop_fuel = std::move(fuel);
  while (true) {
    if (_loop_fuel <= 0) {
      *_write =
          std::make_unique<LoopifyLists::list<LoopifyLists::list<uint64_t>>>(
              list<LoopifyLists::list<uint64_t>>::nil());
      break;
    } else {
      uint64_t f = _loop_fuel - 1;
      if (std::holds_alternative<typename LoopifyLists::list<uint64_t>::Nil>(
              _loop_l->v())) {
        *_write =
            std::make_unique<LoopifyLists::list<LoopifyLists::list<uint64_t>>>(
                list<LoopifyLists::list<uint64_t>>::nil());
        break;
      } else {
        const auto &[a0, a1] =
            std::get<typename LoopifyLists::list<uint64_t>::Cons>(_loop_l->v());
        if (len_list(*_loop_l) < n) {
          *_write = std::make_unique<
              LoopifyLists::list<LoopifyLists::list<uint64_t>>>(
              list<LoopifyLists::list<uint64_t>>::nil());
          break;
        } else {
          LoopifyLists::list<uint64_t> window = take_n(n, *_loop_l);
          if (std::holds_alternative<
                  typename LoopifyLists::list<uint64_t>::Nil>(window.v_mut())) {
            *_write = std::make_unique<
                LoopifyLists::list<LoopifyLists::list<uint64_t>>>(
                list<LoopifyLists::list<uint64_t>>::nil());
            break;
          } else {
            auto _cell = std::make_unique<
                LoopifyLists::list<LoopifyLists::list<uint64_t>>>(
                typename list<LoopifyLists::list<uint64_t>>::Cons(window,
                                                                  nullptr));
            *_write = std::move(_cell);
            _write =
                &std::get<typename list<LoopifyLists::list<uint64_t>>::Cons>(
                     (*_write)->v_mut())
                     .a1;
            _loop_l = a1.get();
            _loop_fuel = f;
            continue;
          }
        }
      }
    }
  }
  return std::move(*_head);
}

LoopifyLists::list<LoopifyLists::list<uint64_t>>
LoopifyLists::windows(uint64_t n, const LoopifyLists::list<uint64_t> &l) {
  return windows_aux((len_list(l) + 1), n, l);
}

/// is_prefix_of l1 l2 checks if l1 is a prefix of l2.
bool LoopifyLists::is_prefix_of(const LoopifyLists::list<uint64_t> &l1,
                                const LoopifyLists::list<uint64_t> &l2) {
  bool _result;
  const LoopifyLists::list<uint64_t> *_loop_l2 = &l2;
  const LoopifyLists::list<uint64_t> *_loop_l1 = &l1;
  while (true) {
    if (std::holds_alternative<typename LoopifyLists::list<uint64_t>::Nil>(
            _loop_l1->v())) {
      _result = true;
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename LoopifyLists::list<uint64_t>::Cons>(_loop_l1->v());
      if (std::holds_alternative<typename LoopifyLists::list<uint64_t>::Nil>(
              _loop_l2->v())) {
        _result = false;
        break;
      } else {
        const auto &[a00, a10] =
            std::get<typename LoopifyLists::list<uint64_t>::Cons>(
                _loop_l2->v());
        if (a0 == a00) {
          _loop_l2 = a10.get();
          _loop_l1 = a1.get();
        } else {
          _result = false;
          break;
        }
      }
    }
  }
  return _result;
}

/// lookup_all key l finds all values for key in association list.
LoopifyLists::list<uint64_t> LoopifyLists::lookup_all(
    uint64_t key, const LoopifyLists::list<std::pair<uint64_t, uint64_t>> &l) {
  std::unique_ptr<LoopifyLists::list<uint64_t>> _head{};
  std::unique_ptr<LoopifyLists::list<uint64_t>> *_write = &_head;
  const LoopifyLists::list<std::pair<uint64_t, uint64_t>> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<
            typename LoopifyLists::list<std::pair<uint64_t, uint64_t>>::Nil>(
            _loop_l->v())) {
      *_write =
          std::make_unique<LoopifyLists::list<uint64_t>>(list<uint64_t>::nil());
      break;
    } else {
      const auto &[a0, a1] = std::get<
          typename LoopifyLists::list<std::pair<uint64_t, uint64_t>>::Cons>(
          _loop_l->v());
      const uint64_t &k = a0.first;
      const uint64_t &v = a0.second;
      if (k == key) {
        auto _cell = std::make_unique<LoopifyLists::list<uint64_t>>(
            typename list<uint64_t>::Cons(v, nullptr));
        *_write = std::move(_cell);
        _write =
            &std::get<typename list<uint64_t>::Cons>((*_write)->v_mut()).a1;
        _loop_l = a1.get();
        continue;
      } else {
        _loop_l = a1.get();
        continue;
      }
    }
  }
  return std::move(*_head);
}

/// member x l checks if x is in the list.
bool LoopifyLists::member(uint64_t x, const LoopifyLists::list<uint64_t> &l) {
  bool _result;
  const LoopifyLists::list<uint64_t> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<typename LoopifyLists::list<uint64_t>::Nil>(
            _loop_l->v())) {
      _result = false;
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename LoopifyLists::list<uint64_t>::Cons>(_loop_l->v());
      if (x == a0) {
        _result = true;
        break;
      } else {
        _loop_l = a1.get();
      }
    }
  }
  return _result;
}

/// product l multiplies all elements in the list.
uint64_t LoopifyLists::product(
    const LoopifyLists::list<uint64_t>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const LoopifyLists::list<uint64_t> *l;
  };

  /// _Resume_Cons: saves [a0], resumes after recursive call with _result.
  struct _Resume_Cons {
    uint64_t a0;
  };

  using _Frame = std::variant<_Enter, _Resume_Cons>;
  uint64_t _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l});
  /// Loopified product: _Enter -> _Resume_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const LoopifyLists::list<uint64_t> &l = *_f.l;
      if (std::holds_alternative<typename LoopifyLists::list<uint64_t>::Nil>(
              l.v())) {
        _result = UINT64_C(1);
      } else {
        const auto &[a0, a1] =
            std::get<typename LoopifyLists::list<uint64_t>::Cons>(l.v());
        _stack.emplace_back(_Resume_Cons{a0});
        _stack.emplace_back(_Enter{a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Resume_Cons>(_frame));
      _result = (_f.a0 * _result);
    }
  }
  return _result;
}

/// sum_list l sums all elements in the list.
uint64_t LoopifyLists::sum_list(
    const LoopifyLists::list<uint64_t>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const LoopifyLists::list<uint64_t> *l;
  };

  /// _Resume_Cons: saves [a0], resumes after recursive call with _result.
  struct _Resume_Cons {
    uint64_t a0;
  };

  using _Frame = std::variant<_Enter, _Resume_Cons>;
  uint64_t _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l});
  /// Loopified sum_list: _Enter -> _Resume_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const LoopifyLists::list<uint64_t> &l = *_f.l;
      if (std::holds_alternative<typename LoopifyLists::list<uint64_t>::Nil>(
              l.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] =
            std::get<typename LoopifyLists::list<uint64_t>::Cons>(l.v());
        _stack.emplace_back(_Resume_Cons{a0});
        _stack.emplace_back(_Enter{a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Resume_Cons>(_frame));
      _result = (_f.a0 + _result);
    }
  }
  return _result;
}

/// flatten_nested l alternative flatten with different pattern: flattens one
/// level at a time. Pattern:  :: rest -> flatten rest, (x :: xs) :: rest -> x
/// :: flatten (xs :: rest).
LoopifyLists::list<uint64_t> LoopifyLists::flatten_nested_fuel(
    uint64_t fuel, const LoopifyLists::list<LoopifyLists::list<uint64_t>> &l) {
  std::unique_ptr<LoopifyLists::list<uint64_t>> _head{};
  std::unique_ptr<LoopifyLists::list<uint64_t>> *_write = &_head;
  LoopifyLists::list<LoopifyLists::list<uint64_t>> _loop_l = l;
  uint64_t _loop_fuel = std::move(fuel);
  while (true) {
    if (_loop_fuel <= 0) {
      *_write =
          std::make_unique<LoopifyLists::list<uint64_t>>(list<uint64_t>::nil());
      break;
    } else {
      uint64_t f = _loop_fuel - 1;
      if (std::holds_alternative<
              typename LoopifyLists::list<LoopifyLists::list<uint64_t>>::Nil>(
              _loop_l.v())) {
        *_write = std::make_unique<LoopifyLists::list<uint64_t>>(
            list<uint64_t>::nil());
        break;
      } else {
        const auto &[a0, a1] = std::get<
            typename LoopifyLists::list<LoopifyLists::list<uint64_t>>::Cons>(
            _loop_l.v());
        if (std::holds_alternative<typename LoopifyLists::list<uint64_t>::Nil>(
                a0.v())) {
          _loop_l = std::move(*a1);
          _loop_fuel = f;
          continue;
        } else {
          const auto &[a00, a10] =
              std::get<typename LoopifyLists::list<uint64_t>::Cons>(a0.v());
          auto _cell = std::make_unique<LoopifyLists::list<uint64_t>>(
              typename list<uint64_t>::Cons(a00, nullptr));
          *_write = std::move(_cell);
          _write =
              &std::get<typename list<uint64_t>::Cons>((*_write)->v_mut()).a1;
          _loop_l = list<LoopifyLists::list<uint64_t>>::cons(*a10, *a1);
          _loop_fuel = f;
          continue;
        }
      }
    }
  }
  return std::move(*_head);
}

uint64_t LoopifyLists::sum_list_lengths(
    const LoopifyLists::list<LoopifyLists::list<uint64_t>>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const LoopifyLists::list<LoopifyLists::list<uint64_t>> *l;
  };

  /// _Resume_Cons: saves [a0], resumes after recursive call with _result.
  struct _Resume_Cons {
    decltype(len_list(std::declval<LoopifyLists::list<uint64_t> &>())) a0;
  };

  using _Frame = std::variant<_Enter, _Resume_Cons>;
  uint64_t _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l});
  /// Loopified sum_list_lengths: _Enter -> _Resume_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const LoopifyLists::list<LoopifyLists::list<uint64_t>> &l = *_f.l;
      if (std::holds_alternative<
              typename LoopifyLists::list<LoopifyLists::list<uint64_t>>::Nil>(
              l.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] = std::get<
            typename LoopifyLists::list<LoopifyLists::list<uint64_t>>::Cons>(
            l.v());
        _stack.emplace_back(_Resume_Cons{len_list(a0)});
        _stack.emplace_back(_Enter{a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Resume_Cons>(_frame));
      _result = (_f.a0 + _result);
    }
  }
  return _result;
}

LoopifyLists::list<uint64_t> LoopifyLists::flatten_nested(
    const LoopifyLists::list<LoopifyLists::list<uint64_t>> &l) {
  return flatten_nested_fuel((sum_list_lengths(l) + 1), l);
}

/// compress l removes consecutive duplicates: 1,1,2,2,2,3 -> 1,2,3.
LoopifyLists::list<uint64_t>
LoopifyLists::compress(const LoopifyLists::list<uint64_t> &l) {
  std::unique_ptr<LoopifyLists::list<uint64_t>> _head{};
  std::unique_ptr<LoopifyLists::list<uint64_t>> *_write = &_head;
  const LoopifyLists::list<uint64_t> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<typename LoopifyLists::list<uint64_t>::Nil>(
            _loop_l->v())) {
      *_write =
          std::make_unique<LoopifyLists::list<uint64_t>>(list<uint64_t>::nil());
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename LoopifyLists::list<uint64_t>::Cons>(_loop_l->v());
      auto &&_sv0 = *a1;
      if (std::holds_alternative<typename LoopifyLists::list<uint64_t>::Nil>(
              _sv0.v())) {
        *_write = std::make_unique<LoopifyLists::list<uint64_t>>(
            list<uint64_t>::cons(a0, list<uint64_t>::nil()));
        break;
      } else {
        const auto &[a00, a10] =
            std::get<typename LoopifyLists::list<uint64_t>::Cons>(_sv0.v());
        if (a0 == a00) {
          _loop_l = a1.get();
          continue;
        } else {
          auto _cell = std::make_unique<LoopifyLists::list<uint64_t>>(
              typename list<uint64_t>::Cons(a0, nullptr));
          *_write = std::move(_cell);
          _write =
              &std::get<typename list<uint64_t>::Cons>((*_write)->v_mut()).a1;
          _loop_l = a1.get();
          continue;
        }
      }
    }
  }
  return std::move(*_head);
}

/// group_pairs l groups consecutive elements into pairs: 1,2,3,4 ->
/// (1,2),(3,4).
LoopifyLists::list<std::pair<uint64_t, uint64_t>>
LoopifyLists::group_pairs(const LoopifyLists::list<uint64_t> &l) {
  std::unique_ptr<LoopifyLists::list<std::pair<uint64_t, uint64_t>>> _head{};
  std::unique_ptr<LoopifyLists::list<std::pair<uint64_t, uint64_t>>> *_write =
      &_head;
  const LoopifyLists::list<uint64_t> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<typename LoopifyLists::list<uint64_t>::Nil>(
            _loop_l->v())) {
      *_write =
          std::make_unique<LoopifyLists::list<std::pair<uint64_t, uint64_t>>>(
              list<std::pair<uint64_t, uint64_t>>::nil());
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename LoopifyLists::list<uint64_t>::Cons>(_loop_l->v());
      auto &&_sv0 = *a1;
      if (std::holds_alternative<typename LoopifyLists::list<uint64_t>::Nil>(
              _sv0.v())) {
        *_write =
            std::make_unique<LoopifyLists::list<std::pair<uint64_t, uint64_t>>>(
                list<std::pair<uint64_t, uint64_t>>::nil());
        break;
      } else {
        const auto &[a00, a10] =
            std::get<typename LoopifyLists::list<uint64_t>::Cons>(_sv0.v());
        auto _cell =
            std::make_unique<LoopifyLists::list<std::pair<uint64_t, uint64_t>>>(
                typename list<std::pair<uint64_t, uint64_t>>::Cons(
                    std::make_pair(a0, a00), nullptr));
        *_write = std::move(_cell);
        _write = &std::get<typename list<std::pair<uint64_t, uint64_t>>::Cons>(
                      (*_write)->v_mut())
                      .a1;
        _loop_l = a10.get();
        continue;
      }
    }
  }
  return std::move(*_head);
}

/// swizzle l separates elements by position: 1,2,3,4 -> (1,3,2,4).
std::pair<LoopifyLists::list<uint64_t>, LoopifyLists::list<uint64_t>>
LoopifyLists::swizzle(
    const LoopifyLists::list<uint64_t>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const LoopifyLists::list<uint64_t> *l;
  };

  /// _Cont_Cons: saves [a0], resumes after recursive call, then processes rest.
  struct _Cont_Cons {
    uint64_t a0;
  };

  using _Frame = std::variant<_Enter, _Cont_Cons>;
  std::pair<LoopifyLists::list<uint64_t>, LoopifyLists::list<uint64_t>>
      _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l});
  /// Loopified swizzle: _Enter -> _Cont_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const LoopifyLists::list<uint64_t> &l = *_f.l;
      if (std::holds_alternative<typename LoopifyLists::list<uint64_t>::Nil>(
              l.v())) {
        _result = std::make_pair(list<uint64_t>::nil(), list<uint64_t>::nil());
      } else {
        const auto &[a0, a1] =
            std::get<typename LoopifyLists::list<uint64_t>::Cons>(l.v());
        _stack.emplace_back(_Cont_Cons{a0});
        _stack.emplace_back(_Enter{a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Cont_Cons>(_frame));
      uint64_t a0 = _f.a0;
      const LoopifyLists::list<uint64_t> &odds = _result.first;
      const LoopifyLists::list<uint64_t> &evens = _result.second;
      _result = std::make_pair(list<uint64_t>::cons(a0, evens), odds);
    }
  }
  return _result;
}

/// index_of_aux x l i finds first index of x in l starting from i.
uint64_t LoopifyLists::index_of_aux(uint64_t x,
                                    const LoopifyLists::list<uint64_t> &l,
                                    uint64_t i) {
  uint64_t _result;
  uint64_t _loop_i = std::move(i);
  const LoopifyLists::list<uint64_t> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<typename LoopifyLists::list<uint64_t>::Nil>(
            _loop_l->v())) {
      _result = UINT64_C(0);
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename LoopifyLists::list<uint64_t>::Cons>(_loop_l->v());
      if (x == a0) {
        _result = std::move(_loop_i);
        break;
      } else {
        _loop_i = (_loop_i + 1);
        _loop_l = a1.get();
      }
    }
  }
  return _result;
}

uint64_t LoopifyLists::index_of(uint64_t x,
                                const LoopifyLists::list<uint64_t> &l) {
  return index_of_aux(x, l, UINT64_C(0));
}

/// interleave l1 l2 interleaves two lists: 1,2 3,4 -> 1,3,2,4.
LoopifyLists::list<uint64_t>
LoopifyLists::interleave(LoopifyLists::list<uint64_t> l1,
                         LoopifyLists::list<uint64_t> l2) {
  std::unique_ptr<LoopifyLists::list<uint64_t>> _head{};
  std::unique_ptr<LoopifyLists::list<uint64_t>> *_write = &_head;
  LoopifyLists::list<uint64_t> _loop_l2 = std::move(l2);
  LoopifyLists::list<uint64_t> _loop_l1 = std::move(l1);
  while (true) {
    if (std::holds_alternative<typename LoopifyLists::list<uint64_t>::Nil>(
            _loop_l1.v_mut())) {
      *_write =
          std::make_unique<LoopifyLists::list<uint64_t>>(std::move(_loop_l2));
      break;
    } else {
      auto &[a0, a1] = std::get<typename LoopifyLists::list<uint64_t>::Cons>(
          _loop_l1.v_mut());
      if (std::holds_alternative<typename LoopifyLists::list<uint64_t>::Nil>(
              _loop_l2.v_mut())) {
        *_write = std::make_unique<LoopifyLists::list<uint64_t>>(_loop_l1);
        break;
      } else {
        auto &[a00, a10] =
            std::get<typename LoopifyLists::list<uint64_t>::Cons>(
                _loop_l2.v_mut());
        auto _cell = std::make_unique<LoopifyLists::list<uint64_t>>(
            typename list<uint64_t>::Cons(std::move(a0), nullptr));
        auto _cell1 = std::make_unique<LoopifyLists::list<uint64_t>>(
            typename list<uint64_t>::Cons(std::move(a00), nullptr));
        std::get<typename list<uint64_t>::Cons>(_cell->v_mut()).a1 =
            std::move(_cell1);
        *_write = std::move(_cell);
        _write =
            &std::get<typename list<uint64_t>::Cons>(
                 std::get<typename list<uint64_t>::Cons>((*_write)->v_mut())
                     .a1->v_mut())
                 .a1;
        _loop_l2 = std::move(*a10);
        _loop_l1 = std::move(*a1);
        continue;
      }
    }
  }
  return std::move(*_head);
}

/// lookup key l finds value for key in association list.
uint64_t LoopifyLists::lookup(
    uint64_t key, const LoopifyLists::list<std::pair<uint64_t, uint64_t>> &l) {
  uint64_t _result;
  const LoopifyLists::list<std::pair<uint64_t, uint64_t>> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<
            typename LoopifyLists::list<std::pair<uint64_t, uint64_t>>::Nil>(
            _loop_l->v())) {
      _result = UINT64_C(0);
      break;
    } else {
      const auto &[a0, a1] = std::get<
          typename LoopifyLists::list<std::pair<uint64_t, uint64_t>>::Cons>(
          _loop_l->v());
      const uint64_t &k = a0.first;
      const uint64_t &v = a0.second;
      if (k == key) {
        _result = std::move(v);
        break;
      } else {
        _loop_l = a1.get();
      }
    }
  }
  return _result;
}

/// group l groups consecutive equal elements: 1,1,2,2,2,3 -> [1,1],[2,2,2],[3].
LoopifyLists::list<LoopifyLists::list<uint64_t>>
LoopifyLists::group_fuel(uint64_t fuel, const LoopifyLists::list<uint64_t> &l) {
  if (fuel <= 0) {
    return list<LoopifyLists::list<uint64_t>>::nil();
  } else {
    uint64_t f = fuel - 1;
    if (std::holds_alternative<typename LoopifyLists::list<uint64_t>::Nil>(
            l.v())) {
      return list<LoopifyLists::list<uint64_t>>::nil();
    } else {
      const auto &[a0, a1] =
          std::get<typename LoopifyLists::list<uint64_t>::Cons>(l.v());
      auto &&_sv0 = *a1;
      if (std::holds_alternative<typename LoopifyLists::list<uint64_t>::Nil>(
              _sv0.v())) {
        return list<LoopifyLists::list<uint64_t>>::cons(
            list<uint64_t>::cons(a0, list<uint64_t>::nil()),
            list<LoopifyLists::list<uint64_t>>::nil());
      } else {
        const auto &[a00, a10] =
            std::get<typename LoopifyLists::list<uint64_t>::Cons>(_sv0.v());
        if (a0 == a00) {
          auto &&_sv1 = group_fuel(f, *a1);
          if (std::holds_alternative<typename LoopifyLists::list<
                  LoopifyLists::list<uint64_t>>::Nil>(_sv1.v())) {
            return list<LoopifyLists::list<uint64_t>>::cons(
                list<uint64_t>::cons(a0, list<uint64_t>::nil()),
                list<LoopifyLists::list<uint64_t>>::nil());
          } else {
            const auto &[a01, a11] = std::get<typename LoopifyLists::list<
                LoopifyLists::list<uint64_t>>::Cons>(_sv1.v());
            return list<LoopifyLists::list<uint64_t>>::cons(
                list<uint64_t>::cons(a0, a01), *a11);
          }
        } else {
          return list<LoopifyLists::list<uint64_t>>::cons(
              list<uint64_t>::cons(a0, list<uint64_t>::nil()),
              group_fuel(f, *a1));
        }
      }
    }
  }
}

LoopifyLists::list<LoopifyLists::list<uint64_t>>
LoopifyLists::group(const LoopifyLists::list<uint64_t> &l) {
  return group_fuel((len_list(l) + 1), l);
}

/// Internal helper: reverse a list.
LoopifyLists::list<uint64_t>
LoopifyLists::rev_helper(LoopifyLists::list<uint64_t> acc,
                         const LoopifyLists::list<uint64_t> &l) {
  LoopifyLists::list<uint64_t> _result;
  const LoopifyLists::list<uint64_t> *_loop_l = &l;
  LoopifyLists::list<uint64_t> _loop_acc = std::move(acc);
  while (true) {
    if (std::holds_alternative<typename LoopifyLists::list<uint64_t>::Nil>(
            _loop_l->v())) {
      _result = std::move(_loop_acc);
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename LoopifyLists::list<uint64_t>::Cons>(_loop_l->v());
      _loop_l = a1.get();
      _loop_acc = list<uint64_t>::cons(a0, std::move(_loop_acc));
    }
  }
  return _result;
}

/// reverse_insert x l inserts x and reverses at each step.
LoopifyLists::list<uint64_t> LoopifyLists::reverse_insert(
    uint64_t x,
    const LoopifyLists::list<uint64_t>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const LoopifyLists::list<uint64_t> *l;
  };

  /// _Resume_Cons: saves [_s0, a0], resumes after recursive call with _result.
  struct _Resume_Cons {
    decltype(list<uint64_t>::nil()) _s0;
    uint64_t a0;
  };

  using _Frame = std::variant<_Enter, _Resume_Cons>;
  LoopifyLists::list<uint64_t> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l});
  /// Loopified reverse_insert: _Enter -> _Resume_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const LoopifyLists::list<uint64_t> &l = *_f.l;
      if (std::holds_alternative<typename LoopifyLists::list<uint64_t>::Nil>(
              l.v())) {
        _result = list<uint64_t>::cons(x, list<uint64_t>::nil());
      } else {
        const auto &[a0, a1] =
            std::get<typename LoopifyLists::list<uint64_t>::Cons>(l.v());
        _stack.emplace_back(_Resume_Cons{list<uint64_t>::nil(), a0});
        _stack.emplace_back(_Enter{a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Resume_Cons>(_frame));
      _result = rev_helper(_f._s0, list<uint64_t>::cons(_f.a0, _result));
    }
  }
  return _result;
}

/// Internal helper: append lists.
LoopifyLists::list<uint64_t>
LoopifyLists::app_helper(const LoopifyLists::list<uint64_t> &l1,
                         LoopifyLists::list<uint64_t> l2) {
  std::unique_ptr<LoopifyLists::list<uint64_t>> _head{};
  std::unique_ptr<LoopifyLists::list<uint64_t>> *_write = &_head;
  LoopifyLists::list<uint64_t> _loop_l2 = std::move(l2);
  const LoopifyLists::list<uint64_t> *_loop_l1 = &l1;
  while (true) {
    if (std::holds_alternative<typename LoopifyLists::list<uint64_t>::Nil>(
            _loop_l1->v())) {
      *_write =
          std::make_unique<LoopifyLists::list<uint64_t>>(std::move(_loop_l2));
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename LoopifyLists::list<uint64_t>::Cons>(_loop_l1->v());
      auto _cell = std::make_unique<LoopifyLists::list<uint64_t>>(
          typename list<uint64_t>::Cons(a0, nullptr));
      *_write = std::move(_cell);
      _write = &std::get<typename list<uint64_t>::Cons>((*_write)->v_mut()).a1;
      _loop_l1 = a1.get();
      continue;
    }
  }
  return std::move(*_head);
}

/// double_append l1 l2 appends with doubling: 1,2 3 -> 1,3,3,3,3.
LoopifyLists::list<uint64_t> LoopifyLists::double_append(
    const LoopifyLists::list<uint64_t> &l1,
    LoopifyLists::list<uint64_t>
        l2) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    LoopifyLists::list<uint64_t> l2;
    const LoopifyLists::list<uint64_t> *l1;
  };

  /// _Cont_Cons: saves [a0], resumes after recursive call, then processes rest.
  struct _Cont_Cons {
    uint64_t a0;
  };

  using _Frame = std::variant<_Enter, _Cont_Cons>;
  LoopifyLists::list<uint64_t> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{l2, &l1});
  /// Loopified double_append: _Enter -> _Cont_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      LoopifyLists::list<uint64_t> l2 = std::move(_f.l2);
      const LoopifyLists::list<uint64_t> &l1 = *_f.l1;
      if (std::holds_alternative<typename LoopifyLists::list<uint64_t>::Nil>(
              l1.v())) {
        _result = std::move(l2);
      } else {
        const auto &[a0, a1] =
            std::get<typename LoopifyLists::list<uint64_t>::Cons>(l1.v());
        _stack.emplace_back(_Cont_Cons{a0});
        _stack.emplace_back(_Enter{std::move(l2), a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Cont_Cons>(_frame));
      uint64_t a0 = _f.a0;
      LoopifyLists::list<uint64_t> rest = _result;
      _result = list<uint64_t>::cons(a0, app_helper(rest, rest));
    }
  }
  return _result;
}

/// remove_if_sum_even l removes element if sum with next is even.
LoopifyLists::list<uint64_t>
LoopifyLists::remove_if_sum_even(const LoopifyLists::list<uint64_t> &l) {
  std::unique_ptr<LoopifyLists::list<uint64_t>> _head{};
  std::unique_ptr<LoopifyLists::list<uint64_t>> *_write = &_head;
  const LoopifyLists::list<uint64_t> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<typename LoopifyLists::list<uint64_t>::Nil>(
            _loop_l->v())) {
      *_write =
          std::make_unique<LoopifyLists::list<uint64_t>>(list<uint64_t>::nil());
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename LoopifyLists::list<uint64_t>::Cons>(_loop_l->v());
      auto &&_sv0 = *a1;
      if (std::holds_alternative<typename LoopifyLists::list<uint64_t>::Nil>(
              _sv0.v())) {
        *_write = std::make_unique<LoopifyLists::list<uint64_t>>(
            list<uint64_t>::cons(a0, list<uint64_t>::nil()));
        break;
      } else {
        const auto &[a00, a10] =
            std::get<typename LoopifyLists::list<uint64_t>::Cons>(_sv0.v());
        if ((UINT64_C(2) ? (a0 + a00) % UINT64_C(2) : (a0 + a00)) ==
            UINT64_C(0)) {
          _loop_l = a1.get();
          continue;
        } else {
          auto _cell = std::make_unique<LoopifyLists::list<uint64_t>>(
              typename list<uint64_t>::Cons(a0, nullptr));
          *_write = std::move(_cell);
          _write =
              &std::get<typename list<uint64_t>::Cons>((*_write)->v_mut()).a1;
          _loop_l = a1.get();
          continue;
        }
      }
    }
  }
  return std::move(*_head);
}

/// split_at n l splits list at index n into (prefix, suffix).
std::pair<LoopifyLists::list<uint64_t>, LoopifyLists::list<uint64_t>>
LoopifyLists::split_at(
    uint64_t n,
    LoopifyLists::list<uint64_t>
        l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    LoopifyLists::list<uint64_t> l;
    uint64_t n;
  };

  /// _Cont1: saves [a0], resumes after recursive call, then processes rest.
  struct _Cont1 {
    uint64_t a0;
  };

  using _Frame = std::variant<_Enter, _Cont1>;
  std::pair<LoopifyLists::list<uint64_t>, LoopifyLists::list<uint64_t>>
      _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{l, n});
  /// Loopified split_at: _Enter -> _Cont1.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      LoopifyLists::list<uint64_t> l = std::move(_f.l);
      uint64_t n = _f.n;
      if (std::holds_alternative<typename LoopifyLists::list<uint64_t>::Nil>(
              l.v_mut())) {
        _result = std::make_pair(list<uint64_t>::nil(), list<uint64_t>::nil());
      } else {
        auto &[a0, a1] =
            std::get<typename LoopifyLists::list<uint64_t>::Cons>(l.v_mut());
        if (n == UINT64_C(0)) {
          _result = std::make_pair(list<uint64_t>::nil(), l);
        } else {
          _stack.emplace_back(_Cont1{a0});
          _stack.emplace_back(
              _Enter{std::move(*a1),
                     (((n - UINT64_C(1)) > n ? 0 : (n - UINT64_C(1))))});
        }
      }
    } else {
      auto _f = std::move(std::get<_Cont1>(_frame));
      uint64_t a0 = _f.a0;
      const LoopifyLists::list<uint64_t> &a = _result.first;
      const LoopifyLists::list<uint64_t> &b = _result.second;
      _result = std::make_pair(list<uint64_t>::cons(std::move(a0), a), b);
    }
  }
  return _result;
}

/// unzip l splits list of pairs into two lists.
std::pair<LoopifyLists::list<uint64_t>, LoopifyLists::list<uint64_t>>
LoopifyLists::unzip(
    const LoopifyLists::list<std::pair<uint64_t, uint64_t>>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const LoopifyLists::list<std::pair<uint64_t, uint64_t>> *l;
  };

  /// _Cont_a: saves [a, b], resumes after recursive call, then processes rest.
  struct _Cont_a {
    uint64_t a;
    uint64_t b;
  };

  using _Frame = std::variant<_Enter, _Cont_a>;
  std::pair<LoopifyLists::list<uint64_t>, LoopifyLists::list<uint64_t>>
      _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l});
  /// Loopified unzip: _Enter -> _Cont_a.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const LoopifyLists::list<std::pair<uint64_t, uint64_t>> &l = *_f.l;
      if (std::holds_alternative<
              typename LoopifyLists::list<std::pair<uint64_t, uint64_t>>::Nil>(
              l.v())) {
        _result = std::make_pair(list<uint64_t>::nil(), list<uint64_t>::nil());
      } else {
        const auto &[a0, a1] = std::get<
            typename LoopifyLists::list<std::pair<uint64_t, uint64_t>>::Cons>(
            l.v());
        const uint64_t &a = a0.first;
        const uint64_t &b = a0.second;
        _stack.emplace_back(_Cont_a{a, b});
        _stack.emplace_back(_Enter{a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Cont_a>(_frame));
      uint64_t a = _f.a;
      uint64_t b = _f.b;
      const LoopifyLists::list<uint64_t> &xs = _result.first;
      const LoopifyLists::list<uint64_t> &ys = _result.second;
      _result = std::make_pair(list<uint64_t>::cons(a, xs),
                               list<uint64_t>::cons(b, ys));
    }
  }
  return _result;
}

/// nth n l default returns nth element or default if out of bounds.
uint64_t LoopifyLists::nth(uint64_t n, const LoopifyLists::list<uint64_t> &l,
                           uint64_t default0) {
  uint64_t _result;
  const LoopifyLists::list<uint64_t> *_loop_l = &l;
  uint64_t _loop_n = std::move(n);
  while (true) {
    if (std::holds_alternative<typename LoopifyLists::list<uint64_t>::Nil>(
            _loop_l->v())) {
      _result = std::move(default0);
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename LoopifyLists::list<uint64_t>::Cons>(_loop_l->v());
      if (_loop_n == UINT64_C(0)) {
        _result = std::move(a0);
        break;
      } else {
        _loop_l = a1.get();
        _loop_n =
            (((_loop_n - UINT64_C(1)) > _loop_n ? 0 : (_loop_n - UINT64_C(1))));
      }
    }
  }
  return _result;
}

/// last l default returns last element or default if empty.
uint64_t LoopifyLists::last(const LoopifyLists::list<uint64_t> &l,
                            uint64_t default0) {
  uint64_t _result;
  const LoopifyLists::list<uint64_t> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<typename LoopifyLists::list<uint64_t>::Nil>(
            _loop_l->v())) {
      _result = std::move(default0);
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename LoopifyLists::list<uint64_t>::Cons>(_loop_l->v());
      auto &&_sv = *a1;
      if (std::holds_alternative<typename LoopifyLists::list<uint64_t>::Nil>(
              _sv.v())) {
        _result = std::move(a0);
        break;
      } else {
        _loop_l = a1.get();
      }
    }
  }
  return _result;
}

/// drop n l drops first n elements.
LoopifyLists::list<uint64_t>
LoopifyLists::drop(uint64_t n, LoopifyLists::list<uint64_t> l) {
  LoopifyLists::list<uint64_t> _result;
  LoopifyLists::list<uint64_t> _loop_l = std::move(l);
  uint64_t _loop_n = std::move(n);
  while (true) {
    if (std::holds_alternative<typename LoopifyLists::list<uint64_t>::Nil>(
            _loop_l.v_mut())) {
      _result = list<uint64_t>::nil();
      break;
    } else {
      auto &[a0, a1] = std::get<typename LoopifyLists::list<uint64_t>::Cons>(
          _loop_l.v_mut());
      if (_loop_n == UINT64_C(0)) {
        _result = std::move(_loop_l);
        break;
      } else {
        _loop_l = std::move(*a1);
        _loop_n =
            (((_loop_n - UINT64_C(1)) > _loop_n ? 0 : (_loop_n - UINT64_C(1))));
      }
    }
  }
  return _result;
}

/// init l returns all but last element.
LoopifyLists::list<uint64_t>
LoopifyLists::init(const LoopifyLists::list<uint64_t> &l) {
  std::unique_ptr<LoopifyLists::list<uint64_t>> _head{};
  std::unique_ptr<LoopifyLists::list<uint64_t>> *_write = &_head;
  const LoopifyLists::list<uint64_t> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<typename LoopifyLists::list<uint64_t>::Nil>(
            _loop_l->v())) {
      *_write =
          std::make_unique<LoopifyLists::list<uint64_t>>(list<uint64_t>::nil());
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename LoopifyLists::list<uint64_t>::Cons>(_loop_l->v());
      auto &&_sv = *a1;
      if (std::holds_alternative<typename LoopifyLists::list<uint64_t>::Nil>(
              _sv.v())) {
        *_write = std::make_unique<LoopifyLists::list<uint64_t>>(
            list<uint64_t>::nil());
        break;
      } else {
        auto _cell = std::make_unique<LoopifyLists::list<uint64_t>>(
            typename list<uint64_t>::Cons(a0, nullptr));
        *_write = std::move(_cell);
        _write =
            &std::get<typename list<uint64_t>::Cons>((*_write)->v_mut()).a1;
        _loop_l = a1.get();
        continue;
      }
    }
  }
  return std::move(*_head);
}

/// count x l counts occurrences of x in l.
uint64_t LoopifyLists::count(
    uint64_t x,
    const LoopifyLists::list<uint64_t>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const LoopifyLists::list<uint64_t> *l;
  };

  /// _Resume1: resumes after recursive call with _result.
  struct _Resume1 {};

  using _Frame = std::variant<_Enter, _Resume1>;
  uint64_t _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l});
  /// Loopified count: _Enter -> _Resume1.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const LoopifyLists::list<uint64_t> &l = *_f.l;
      if (std::holds_alternative<typename LoopifyLists::list<uint64_t>::Nil>(
              l.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] =
            std::get<typename LoopifyLists::list<uint64_t>::Cons>(l.v());
        if (x == a0) {
          _stack.emplace_back(_Resume1{});
          _stack.emplace_back(_Enter{a1.get()});
        } else {
          _stack.emplace_back(_Enter{a1.get()});
        }
      }
    } else {
      auto _f = std::move(std::get<_Resume1>(_frame));
      _result = (_result + 1);
    }
  }
  return _result;
}

/// maximum l finds maximum element (returns 0 for empty list).
uint64_t LoopifyLists::maximum(
    const LoopifyLists::list<uint64_t>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const LoopifyLists::list<uint64_t> *l;
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
  /// Loopified maximum: _Enter -> _Cont_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const LoopifyLists::list<uint64_t> &l = *_f.l;
      if (std::holds_alternative<typename LoopifyLists::list<uint64_t>::Nil>(
              l.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] =
            std::get<typename LoopifyLists::list<uint64_t>::Cons>(l.v());
        auto &&_sv = *a1;
        if (std::holds_alternative<typename LoopifyLists::list<uint64_t>::Nil>(
                _sv.v())) {
          _result = std::move(a0);
        } else {
          _stack.emplace_back(_Cont_Cons{a0});
          _stack.emplace_back(_Enter{a1.get()});
        }
      }
    } else {
      auto _f = std::move(std::get<_Cont_Cons>(_frame));
      uint64_t a0 = _f.a0;
      uint64_t max_rest = _result;
      if (max_rest <= a0) {
        _result = std::move(a0);
      } else {
        _result = std::move(max_rest);
      }
    }
  }
  return _result;
}

/// minmax l finds both minimum and maximum in one pass.
std::pair<uint64_t, uint64_t> LoopifyLists::minmax(
    const LoopifyLists::list<uint64_t>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const LoopifyLists::list<uint64_t> *l;
  };

  /// _Cont_Cons: saves [a0], resumes after recursive call, then processes rest.
  struct _Cont_Cons {
    uint64_t a0;
  };

  using _Frame = std::variant<_Enter, _Cont_Cons>;
  std::pair<uint64_t, uint64_t> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l});
  /// Loopified minmax: _Enter -> _Cont_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const LoopifyLists::list<uint64_t> &l = *_f.l;
      if (std::holds_alternative<typename LoopifyLists::list<uint64_t>::Nil>(
              l.v())) {
        _result = std::make_pair(UINT64_C(0), UINT64_C(0));
      } else {
        const auto &[a0, a1] =
            std::get<typename LoopifyLists::list<uint64_t>::Cons>(l.v());
        auto &&_sv = *a1;
        if (std::holds_alternative<typename LoopifyLists::list<uint64_t>::Nil>(
                _sv.v())) {
          _result = std::make_pair(a0, a0);
        } else {
          _stack.emplace_back(_Cont_Cons{a0});
          _stack.emplace_back(_Enter{a1.get()});
        }
      }
    } else {
      auto _f = std::move(std::get<_Cont_Cons>(_frame));
      uint64_t a0 = _f.a0;
      const uint64_t &lo = _result.first;
      const uint64_t &hi = _result.second;
      _result = std::make_pair((a0 <= lo ? a0 : lo), (hi <= a0 ? a0 : hi));
    }
  }
  return _result;
}

/// Helper for rotate_left.
LoopifyLists::list<uint64_t>
LoopifyLists::rotate_left_fuel(uint64_t fuel, uint64_t n,
                               LoopifyLists::list<uint64_t> l) {
  LoopifyLists::list<uint64_t> _result;
  LoopifyLists::list<uint64_t> _loop_l = std::move(l);
  uint64_t _loop_n = std::move(n);
  uint64_t _loop_fuel = std::move(fuel);
  while (true) {
    if (_loop_fuel <= 0) {
      _result = std::move(_loop_l);
      break;
    } else {
      uint64_t f = _loop_fuel - 1;
      if (_loop_n == UINT64_C(0)) {
        _result = std::move(_loop_l);
        break;
      } else {
        if (std::holds_alternative<typename LoopifyLists::list<uint64_t>::Nil>(
                _loop_l.v_mut())) {
          _result = list<uint64_t>::nil();
          break;
        } else {
          auto &[a0, a1] =
              std::get<typename LoopifyLists::list<uint64_t>::Cons>(
                  _loop_l.v_mut());
          _loop_l = app_helper(
              *a1, list<uint64_t>::cons(std::move(a0), list<uint64_t>::nil()));
          _loop_n = ((
              (_loop_n - UINT64_C(1)) > _loop_n ? 0 : (_loop_n - UINT64_C(1))));
          _loop_fuel = f;
        }
      }
    }
  }
  return _result;
}

/// rotate_left n l rotates list left by n positions: rotate 2 1,2,3,4 ->
/// 3,4,1,2.
LoopifyLists::list<uint64_t>
LoopifyLists::rotate_left(uint64_t n, const LoopifyLists::list<uint64_t> &l) {
  return rotate_left_fuel((n + 1), n, l);
}

/// intercalate sep lists joins lists with separator: intercalate 0 [1,2],[3,4]
/// -> 1,2,0,3,4.
LoopifyLists::list<uint64_t>
LoopifyLists::intercalate(const LoopifyLists::list<uint64_t> &sep,
                          const LoopifyLists::list<LoopifyLists::list<uint64_t>>
                              &lists) { /// _Enter: captures varying parameters
                                        /// for each recursive call.

  struct _Enter {
    const LoopifyLists::list<LoopifyLists::list<uint64_t>> *lists;
  };

  /// _Resume_Cons: saves [a0, sep], resumes after recursive call with _result.
  struct _Resume_Cons {
    LoopifyLists::list<uint64_t> a0;
    LoopifyLists::list<uint64_t> sep;
  };

  using _Frame = std::variant<_Enter, _Resume_Cons>;
  LoopifyLists::list<uint64_t> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&lists});
  /// Loopified intercalate: _Enter -> _Resume_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const LoopifyLists::list<LoopifyLists::list<uint64_t>> &lists = *_f.lists;
      if (std::holds_alternative<
              typename LoopifyLists::list<LoopifyLists::list<uint64_t>>::Nil>(
              lists.v())) {
        _result = list<uint64_t>::nil();
      } else {
        const auto &[a0, a1] = std::get<
            typename LoopifyLists::list<LoopifyLists::list<uint64_t>>::Cons>(
            lists.v());
        auto &&_sv = *a1;
        if (std::holds_alternative<
                typename LoopifyLists::list<LoopifyLists::list<uint64_t>>::Nil>(
                _sv.v())) {
          _result = std::move(a0);
        } else {
          _stack.emplace_back(_Resume_Cons{a0, sep});
          _stack.emplace_back(_Enter{a1.get()});
        }
      }
    } else {
      auto _f = std::move(std::get<_Resume_Cons>(_frame));
      _result = app_helper(_f.a0, app_helper(_f.sep, _result));
    }
  }
  return _result;
}

/// majority l finds majority element using Boyer-Moore voting algorithm.
/// Returns (candidate, count).
std::pair<uint64_t, uint64_t> LoopifyLists::majority(
    const LoopifyLists::list<uint64_t>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const LoopifyLists::list<uint64_t> *l;
  };

  /// _Cont_Cons: saves [a0], resumes after recursive call, then processes rest.
  struct _Cont_Cons {
    uint64_t a0;
  };

  using _Frame = std::variant<_Enter, _Cont_Cons>;
  std::pair<uint64_t, uint64_t> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l});
  /// Loopified majority: _Enter -> _Cont_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const LoopifyLists::list<uint64_t> &l = *_f.l;
      if (std::holds_alternative<typename LoopifyLists::list<uint64_t>::Nil>(
              l.v())) {
        _result = std::make_pair(UINT64_C(0), UINT64_C(0));
      } else {
        const auto &[a0, a1] =
            std::get<typename LoopifyLists::list<uint64_t>::Cons>(l.v());
        auto &&_sv = *a1;
        if (std::holds_alternative<typename LoopifyLists::list<uint64_t>::Nil>(
                _sv.v())) {
          _result = std::make_pair(a0, UINT64_C(1));
        } else {
          _stack.emplace_back(_Cont_Cons{a0});
          _stack.emplace_back(_Enter{a1.get()});
        }
      }
    } else {
      auto _f = std::move(std::get<_Cont_Cons>(_frame));
      uint64_t a0 = _f.a0;
      const uint64_t &cand = _result.first;
      const uint64_t &cnt = _result.second;
      if (a0 == cand) {
        _result = std::make_pair(cand, (cnt + 1));
      } else {
        if (cnt == UINT64_C(0)) {
          _result = std::make_pair(a0, UINT64_C(1));
        } else {
          _result = std::make_pair(
              cand, (((cnt - UINT64_C(1)) > cnt ? 0 : (cnt - UINT64_C(1)))));
        }
      }
    }
  }
  return _result;
}

/// zip3 l1 l2 l3 zips three lists into triples.
LoopifyLists::list<std::pair<std::pair<uint64_t, uint64_t>, uint64_t>>
LoopifyLists::zip3(const LoopifyLists::list<uint64_t> &l1,
                   const LoopifyLists::list<uint64_t> &l2,
                   const LoopifyLists::list<uint64_t> &l3) {
  std::unique_ptr<
      LoopifyLists::list<std::pair<std::pair<uint64_t, uint64_t>, uint64_t>>>
      _head{};
  std::unique_ptr<
      LoopifyLists::list<std::pair<std::pair<uint64_t, uint64_t>, uint64_t>>>
      *_write = &_head;
  const LoopifyLists::list<uint64_t> *_loop_l3 = &l3;
  const LoopifyLists::list<uint64_t> *_loop_l2 = &l2;
  const LoopifyLists::list<uint64_t> *_loop_l1 = &l1;
  while (true) {
    if (std::holds_alternative<typename LoopifyLists::list<uint64_t>::Nil>(
            _loop_l1->v())) {
      *_write = std::make_unique<LoopifyLists::list<
          std::pair<std::pair<uint64_t, uint64_t>, uint64_t>>>(
          list<std::pair<std::pair<uint64_t, uint64_t>, uint64_t>>::nil());
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename LoopifyLists::list<uint64_t>::Cons>(_loop_l1->v());
      if (std::holds_alternative<typename LoopifyLists::list<uint64_t>::Nil>(
              _loop_l2->v())) {
        *_write = std::make_unique<LoopifyLists::list<
            std::pair<std::pair<uint64_t, uint64_t>, uint64_t>>>(
            list<std::pair<std::pair<uint64_t, uint64_t>, uint64_t>>::nil());
        break;
      } else {
        const auto &[a00, a10] =
            std::get<typename LoopifyLists::list<uint64_t>::Cons>(
                _loop_l2->v());
        if (std::holds_alternative<typename LoopifyLists::list<uint64_t>::Nil>(
                _loop_l3->v())) {
          *_write = std::make_unique<LoopifyLists::list<
              std::pair<std::pair<uint64_t, uint64_t>, uint64_t>>>(
              list<std::pair<std::pair<uint64_t, uint64_t>, uint64_t>>::nil());
          break;
        } else {
          const auto &[a01, a11] =
              std::get<typename LoopifyLists::list<uint64_t>::Cons>(
                  _loop_l3->v());
          auto _cell = std::make_unique<LoopifyLists::list<
              std::pair<std::pair<uint64_t, uint64_t>, uint64_t>>>(
              typename list<
                  std::pair<std::pair<uint64_t, uint64_t>, uint64_t>>::
                  Cons(std::make_pair(std::make_pair(a0, a00), a01), nullptr));
          *_write = std::move(_cell);
          _write = &std::get<typename list<
              std::pair<std::pair<uint64_t, uint64_t>, uint64_t>>::Cons>(
                        (*_write)->v_mut())
                        .a1;
          _loop_l3 = a11.get();
          _loop_l2 = a10.get();
          _loop_l1 = a1.get();
          continue;
        }
      }
    }
  }
  return std::move(*_head);
}

/// sum_and_count l returns both sum and count in one pass.
std::pair<uint64_t, uint64_t> LoopifyLists::sum_and_count(
    const LoopifyLists::list<uint64_t>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const LoopifyLists::list<uint64_t> *l;
  };

  /// _Cont_Cons: saves [a0], resumes after recursive call, then processes rest.
  struct _Cont_Cons {
    uint64_t a0;
  };

  using _Frame = std::variant<_Enter, _Cont_Cons>;
  std::pair<uint64_t, uint64_t> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l});
  /// Loopified sum_and_count: _Enter -> _Cont_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const LoopifyLists::list<uint64_t> &l = *_f.l;
      if (std::holds_alternative<typename LoopifyLists::list<uint64_t>::Nil>(
              l.v())) {
        _result = std::make_pair(UINT64_C(0), UINT64_C(0));
      } else {
        const auto &[a0, a1] =
            std::get<typename LoopifyLists::list<uint64_t>::Cons>(l.v());
        _stack.emplace_back(_Cont_Cons{a0});
        _stack.emplace_back(_Enter{a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Cont_Cons>(_frame));
      uint64_t a0 = _f.a0;
      const uint64_t &s = _result.first;
      const uint64_t &c = _result.second;
      _result = std::make_pair((a0 + s), (c + 1));
    }
  }
  return _result;
}

/// elem_at n l returns element at index n (like nth but with different name).
std::optional<uint64_t>
LoopifyLists::elem_at(uint64_t n, const LoopifyLists::list<uint64_t> &l) {
  std::optional<uint64_t> _result;
  const LoopifyLists::list<uint64_t> *_loop_l = &l;
  uint64_t _loop_n = std::move(n);
  while (true) {
    if (std::holds_alternative<typename LoopifyLists::list<uint64_t>::Nil>(
            _loop_l->v())) {
      _result = std::optional<uint64_t>();
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename LoopifyLists::list<uint64_t>::Cons>(_loop_l->v());
      if (_loop_n == UINT64_C(0)) {
        _result = std::make_optional<uint64_t>(a0);
        break;
      } else {
        _loop_l = a1.get();
        _loop_n =
            (((_loop_n - UINT64_C(1)) > _loop_n ? 0 : (_loop_n - UINT64_C(1))));
      }
    }
  }
  return _result;
}
