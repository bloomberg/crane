#include "loopify_lists.h"

/// Consolidated UNIQUE list operations - no stdlib duplicates.
/// Tests loopification on domain-specific list algorithms.
/// range start count generates start, start+1, ..., start+count-1.
LoopifyLists::list<unsigned int> LoopifyLists::range(unsigned int start,
                                                     unsigned int count0) {
  std::unique_ptr<LoopifyLists::list<unsigned int>> _head{};
  std::unique_ptr<LoopifyLists::list<unsigned int>> *_write = &_head;
  unsigned int _loop_count0 = std::move(count0);
  unsigned int _loop_start = std::move(start);
  while (true) {
    if (_loop_count0 <= 0) {
      *_write = std::make_unique<LoopifyLists::list<unsigned int>>(
          list<unsigned int>::nil());
      break;
    } else {
      unsigned int c = _loop_count0 - 1;
      auto _cell = std::make_unique<LoopifyLists::list<unsigned int>>(
          typename list<unsigned int>::Cons(_loop_start, nullptr));
      *_write = std::move(_cell);
      _write =
          &std::get<typename list<unsigned int>::Cons>((*_write)->v_mut()).a1;
      _loop_count0 = c;
      _loop_start = (_loop_start + 1);
      continue;
    }
  }
  return std::move(*_head);
}

/// step_sum l sums with conditional contributions: even values as-is, odd
/// doubled.
unsigned int LoopifyLists::step_sum(
    const LoopifyLists::list<unsigned int>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const LoopifyLists::list<unsigned int> *l;
  };

  /// _Resume_Cons: saves [contribution], resumes after recursive call with
  /// _result.
  struct _Resume_Cons {
    unsigned int contribution;
  };

  using _Frame = std::variant<_Enter, _Resume_Cons>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l});
  /// Loopified step_sum: _Enter -> _Resume_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const LoopifyLists::list<unsigned int> &l = *_f.l;
      if (std::holds_alternative<
              typename LoopifyLists::list<unsigned int>::Nil>(l.v())) {
        _result = 0u;
      } else {
        const auto &[a0, a1] =
            std::get<typename LoopifyLists::list<unsigned int>::Cons>(l.v());
        unsigned int contribution;
        if ((2u ? a0 % 2u : a0) == 0u) {
          contribution = a0;
        } else {
          contribution = (a0 * 2u);
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
unsigned int LoopifyLists::sum_abs(
    const LoopifyLists::list<unsigned int> &l,
    unsigned int
        base) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const LoopifyLists::list<unsigned int> *l;
  };

  /// _Resume_Cons: saves [abs_val], resumes after recursive call with _result.
  struct _Resume_Cons {
    unsigned int abs_val;
  };

  using _Frame = std::variant<_Enter, _Resume_Cons>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l});
  /// Loopified sum_abs: _Enter -> _Resume_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const LoopifyLists::list<unsigned int> &l = *_f.l;
      if (std::holds_alternative<
              typename LoopifyLists::list<unsigned int>::Nil>(l.v())) {
        _result = 0u;
      } else {
        const auto &[a0, a1] =
            std::get<typename LoopifyLists::list<unsigned int>::Cons>(l.v());
        unsigned int abs_val;
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
unsigned int LoopifyLists::four_elem(
    const LoopifyLists::list<unsigned int>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const LoopifyLists::list<unsigned int> *l;
  };

  /// _Resume_Cons: saves [_s0, _s1], resumes after recursive call with _result.
  struct _Resume_Cons {
    unsigned int _s0;
    unsigned int _s1;
  };

  using _Frame = std::variant<_Enter, _Resume_Cons>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l});
  /// Loopified four_elem: _Enter -> _Resume_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const LoopifyLists::list<unsigned int> &l = *_f.l;
      if (std::holds_alternative<
              typename LoopifyLists::list<unsigned int>::Nil>(l.v())) {
        _result = 0u;
      } else {
        const auto &[a0, a1] =
            std::get<typename LoopifyLists::list<unsigned int>::Cons>(l.v());
        auto &&_sv0 = *a1;
        if (std::holds_alternative<
                typename LoopifyLists::list<unsigned int>::Nil>(_sv0.v())) {
          _result = 1u;
        } else {
          const auto &[a00, a10] =
              std::get<typename LoopifyLists::list<unsigned int>::Cons>(
                  _sv0.v());
          auto &&_sv1 = *a10;
          if (std::holds_alternative<
                  typename LoopifyLists::list<unsigned int>::Nil>(_sv1.v())) {
            _result = 2u;
          } else {
            const auto &[a01, a11] =
                std::get<typename LoopifyLists::list<unsigned int>::Cons>(
                    _sv1.v());
            auto &&_sv2 = *a11;
            if (std::holds_alternative<
                    typename LoopifyLists::list<unsigned int>::Nil>(_sv2.v())) {
              _result = 3u;
            } else {
              const auto &[a02, a12] =
                  std::get<typename LoopifyLists::list<unsigned int>::Cons>(
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
LoopifyLists::list<unsigned int>
LoopifyLists::between(unsigned int lo, unsigned int hi,
                      const LoopifyLists::list<unsigned int> &l) {
  std::unique_ptr<LoopifyLists::list<unsigned int>> _head{};
  std::unique_ptr<LoopifyLists::list<unsigned int>> *_write = &_head;
  const LoopifyLists::list<unsigned int> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<typename LoopifyLists::list<unsigned int>::Nil>(
            _loop_l->v())) {
      *_write = std::make_unique<LoopifyLists::list<unsigned int>>(
          list<unsigned int>::nil());
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename LoopifyLists::list<unsigned int>::Cons>(
              _loop_l->v());
      if ((lo <= a0 && a0 <= hi)) {
        auto _cell = std::make_unique<LoopifyLists::list<unsigned int>>(
            typename list<unsigned int>::Cons(a0, nullptr));
        *_write = std::move(_cell);
        _write =
            &std::get<typename list<unsigned int>::Cons>((*_write)->v_mut()).a1;
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
unsigned int LoopifyLists::categorize(
    unsigned int k,
    const LoopifyLists::list<unsigned int>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const LoopifyLists::list<unsigned int> *l;
  };

  /// _Resume_Cons: saves [score], resumes after recursive call with _result.
  struct _Resume_Cons {
    unsigned int score;
  };

  using _Frame = std::variant<_Enter, _Resume_Cons>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l});
  /// Loopified categorize: _Enter -> _Resume_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const LoopifyLists::list<unsigned int> &l = *_f.l;
      if (std::holds_alternative<
              typename LoopifyLists::list<unsigned int>::Nil>(l.v())) {
        _result = 0u;
      } else {
        const auto &[a0, a1] =
            std::get<typename LoopifyLists::list<unsigned int>::Cons>(l.v());
        unsigned int score;
        if (k < a0) {
          score = 3u;
        } else {
          if (a0 == k) {
            score = 2u;
          } else {
            score = 1u;
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
unsigned int LoopifyLists::max_prefix_sum(
    const LoopifyLists::list<unsigned int>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const LoopifyLists::list<unsigned int> *l;
  };

  /// _Cont_Cons: saves [a0], resumes after recursive call, then processes rest.
  struct _Cont_Cons {
    unsigned int a0;
  };

  using _Frame = std::variant<_Enter, _Cont_Cons>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l});
  /// Loopified max_prefix_sum: _Enter -> _Cont_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const LoopifyLists::list<unsigned int> &l = *_f.l;
      if (std::holds_alternative<
              typename LoopifyLists::list<unsigned int>::Nil>(l.v())) {
        _result = 0u;
      } else {
        const auto &[a0, a1] =
            std::get<typename LoopifyLists::list<unsigned int>::Cons>(l.v());
        _stack.emplace_back(_Cont_Cons{a0});
        _stack.emplace_back(_Enter{a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Cont_Cons>(_frame));
      unsigned int a0 = _f.a0;
      unsigned int rest = _result;
      unsigned int sum = (a0 + rest);
      if (0u <= sum) {
        _result = sum;
      } else {
        _result = 0u;
      }
    }
  }
  return _result;
}

/// pairwise_sum l sums consecutive pairs: 1,2,3,4 -> 3,7.
LoopifyLists::list<unsigned int>
LoopifyLists::pairwise_sum(const LoopifyLists::list<unsigned int> &l) {
  std::unique_ptr<LoopifyLists::list<unsigned int>> _head{};
  std::unique_ptr<LoopifyLists::list<unsigned int>> *_write = &_head;
  const LoopifyLists::list<unsigned int> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<typename LoopifyLists::list<unsigned int>::Nil>(
            _loop_l->v())) {
      *_write = std::make_unique<LoopifyLists::list<unsigned int>>(
          list<unsigned int>::nil());
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename LoopifyLists::list<unsigned int>::Cons>(
              _loop_l->v());
      auto &&_sv0 = *a1;
      if (std::holds_alternative<
              typename LoopifyLists::list<unsigned int>::Nil>(_sv0.v())) {
        *_write = std::make_unique<LoopifyLists::list<unsigned int>>(
            list<unsigned int>::nil());
        break;
      } else {
        const auto &[a00, a10] =
            std::get<typename LoopifyLists::list<unsigned int>::Cons>(_sv0.v());
        auto _cell = std::make_unique<LoopifyLists::list<unsigned int>>(
            typename list<unsigned int>::Cons((a0 + a00), nullptr));
        *_write = std::move(_cell);
        _write =
            &std::get<typename list<unsigned int>::Cons>((*_write)->v_mut()).a1;
        _loop_l = a10.get();
        continue;
      }
    }
  }
  return std::move(*_head);
}

/// weighted_sum i l weighted sum with increasing weights.
unsigned int LoopifyLists::weighted_sum(
    unsigned int i,
    const LoopifyLists::list<unsigned int>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const LoopifyLists::list<unsigned int> *l;
    unsigned int i;
  };

  /// _Resume_Cons: saves [_s0], resumes after recursive call with _result.
  struct _Resume_Cons {
    unsigned int _s0;
  };

  using _Frame = std::variant<_Enter, _Resume_Cons>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l, i});
  /// Loopified weighted_sum: _Enter -> _Resume_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const LoopifyLists::list<unsigned int> &l = *_f.l;
      unsigned int i = _f.i;
      if (std::holds_alternative<
              typename LoopifyLists::list<unsigned int>::Nil>(l.v())) {
        _result = 0u;
      } else {
        const auto &[a0, a1] =
            std::get<typename LoopifyLists::list<unsigned int>::Cons>(l.v());
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
LoopifyLists::list<unsigned int>
LoopifyLists::prefix_sums(unsigned int acc,
                          const LoopifyLists::list<unsigned int> &l) {
  std::unique_ptr<LoopifyLists::list<unsigned int>> _head{};
  std::unique_ptr<LoopifyLists::list<unsigned int>> *_write = &_head;
  const LoopifyLists::list<unsigned int> *_loop_l = &l;
  unsigned int _loop_acc = std::move(acc);
  while (true) {
    if (std::holds_alternative<typename LoopifyLists::list<unsigned int>::Nil>(
            _loop_l->v())) {
      *_write = std::make_unique<LoopifyLists::list<unsigned int>>(
          list<unsigned int>::cons(_loop_acc, list<unsigned int>::nil()));
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename LoopifyLists::list<unsigned int>::Cons>(
              _loop_l->v());
      auto _cell = std::make_unique<LoopifyLists::list<unsigned int>>(
          typename list<unsigned int>::Cons(_loop_acc, nullptr));
      *_write = std::move(_cell);
      _write =
          &std::get<typename list<unsigned int>::Cons>((*_write)->v_mut()).a1;
      _loop_l = a1.get();
      _loop_acc = (_loop_acc + a0);
      continue;
    }
  }
  return std::move(*_head);
}

/// uniq_sorted l removes consecutive duplicates from sorted list.
LoopifyLists::list<unsigned int>
LoopifyLists::uniq_sorted(const LoopifyLists::list<unsigned int> &l) {
  std::unique_ptr<LoopifyLists::list<unsigned int>> _head{};
  std::unique_ptr<LoopifyLists::list<unsigned int>> *_write = &_head;
  const LoopifyLists::list<unsigned int> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<typename LoopifyLists::list<unsigned int>::Nil>(
            _loop_l->v())) {
      *_write = std::make_unique<LoopifyLists::list<unsigned int>>(
          list<unsigned int>::nil());
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename LoopifyLists::list<unsigned int>::Cons>(
              _loop_l->v());
      auto &&_sv0 = *a1;
      if (std::holds_alternative<
              typename LoopifyLists::list<unsigned int>::Nil>(_sv0.v())) {
        *_write = std::make_unique<LoopifyLists::list<unsigned int>>(
            list<unsigned int>::cons(a0, list<unsigned int>::nil()));
        break;
      } else {
        const auto &[a00, a10] =
            std::get<typename LoopifyLists::list<unsigned int>::Cons>(_sv0.v());
        if (a0 == a00) {
          _loop_l = a1.get();
          continue;
        } else {
          auto _cell = std::make_unique<LoopifyLists::list<unsigned int>>(
              typename list<unsigned int>::Cons(a0, nullptr));
          *_write = std::move(_cell);
          _write =
              &std::get<typename list<unsigned int>::Cons>((*_write)->v_mut())
                   .a1;
          _loop_l = a1.get();
          continue;
        }
      }
    }
  }
  return std::move(*_head);
}

/// Helper: take first n elements.
LoopifyLists::list<unsigned int>
LoopifyLists::take_n(unsigned int n,
                     const LoopifyLists::list<unsigned int> &l) {
  std::unique_ptr<LoopifyLists::list<unsigned int>> _head{};
  std::unique_ptr<LoopifyLists::list<unsigned int>> *_write = &_head;
  const LoopifyLists::list<unsigned int> *_loop_l = &l;
  unsigned int _loop_n = std::move(n);
  while (true) {
    if (_loop_n <= 0) {
      *_write = std::make_unique<LoopifyLists::list<unsigned int>>(
          list<unsigned int>::nil());
      break;
    } else {
      unsigned int m = _loop_n - 1;
      if (std::holds_alternative<
              typename LoopifyLists::list<unsigned int>::Nil>(_loop_l->v())) {
        *_write = std::make_unique<LoopifyLists::list<unsigned int>>(
            list<unsigned int>::nil());
        break;
      } else {
        const auto &[a0, a1] =
            std::get<typename LoopifyLists::list<unsigned int>::Cons>(
                _loop_l->v());
        auto _cell = std::make_unique<LoopifyLists::list<unsigned int>>(
            typename list<unsigned int>::Cons(a0, nullptr));
        *_write = std::move(_cell);
        _write =
            &std::get<typename list<unsigned int>::Cons>((*_write)->v_mut()).a1;
        _loop_l = a1.get();
        _loop_n = m;
        continue;
      }
    }
  }
  return std::move(*_head);
}

/// Helper: list length.
unsigned int LoopifyLists::len_list(
    const LoopifyLists::list<unsigned int>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const LoopifyLists::list<unsigned int> *l;
  };

  /// _Resume_Cons: resumes after recursive call with _result.
  struct _Resume_Cons {};

  using _Frame = std::variant<_Enter, _Resume_Cons>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l});
  /// Loopified len_list: _Enter -> _Resume_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const LoopifyLists::list<unsigned int> &l = *_f.l;
      if (std::holds_alternative<
              typename LoopifyLists::list<unsigned int>::Nil>(l.v())) {
        _result = 0u;
      } else {
        const auto &[a0, a1] =
            std::get<typename LoopifyLists::list<unsigned int>::Cons>(l.v());
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
LoopifyLists::list<LoopifyLists::list<unsigned int>>
LoopifyLists::windows_aux(unsigned int fuel, unsigned int n,
                          const LoopifyLists::list<unsigned int> &l) {
  std::unique_ptr<LoopifyLists::list<LoopifyLists::list<unsigned int>>> _head{};
  std::unique_ptr<LoopifyLists::list<LoopifyLists::list<unsigned int>>>
      *_write = &_head;
  const LoopifyLists::list<unsigned int> *_loop_l = &l;
  unsigned int _loop_fuel = std::move(fuel);
  while (true) {
    if (_loop_fuel <= 0) {
      *_write = std::make_unique<
          LoopifyLists::list<LoopifyLists::list<unsigned int>>>(
          list<LoopifyLists::list<unsigned int>>::nil());
      break;
    } else {
      unsigned int f = _loop_fuel - 1;
      if (std::holds_alternative<
              typename LoopifyLists::list<unsigned int>::Nil>(_loop_l->v())) {
        *_write = std::make_unique<
            LoopifyLists::list<LoopifyLists::list<unsigned int>>>(
            list<LoopifyLists::list<unsigned int>>::nil());
        break;
      } else {
        const auto &[a0, a1] =
            std::get<typename LoopifyLists::list<unsigned int>::Cons>(
                _loop_l->v());
        if (len_list(*_loop_l) < n) {
          *_write = std::make_unique<
              LoopifyLists::list<LoopifyLists::list<unsigned int>>>(
              list<LoopifyLists::list<unsigned int>>::nil());
          break;
        } else {
          LoopifyLists::list<unsigned int> window = take_n(n, *_loop_l);
          if (std::holds_alternative<
                  typename LoopifyLists::list<unsigned int>::Nil>(
                  window.v_mut())) {
            *_write = std::make_unique<
                LoopifyLists::list<LoopifyLists::list<unsigned int>>>(
                list<LoopifyLists::list<unsigned int>>::nil());
            break;
          } else {
            auto _cell = std::make_unique<
                LoopifyLists::list<LoopifyLists::list<unsigned int>>>(
                typename list<LoopifyLists::list<unsigned int>>::Cons(window,
                                                                      nullptr));
            *_write = std::move(_cell);
            _write =
                &std::get<
                     typename list<LoopifyLists::list<unsigned int>>::Cons>(
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

LoopifyLists::list<LoopifyLists::list<unsigned int>>
LoopifyLists::windows(unsigned int n,
                      const LoopifyLists::list<unsigned int> &l) {
  return windows_aux((len_list(l) + 1), n, l);
}

/// is_prefix_of l1 l2 checks if l1 is a prefix of l2.
bool LoopifyLists::is_prefix_of(const LoopifyLists::list<unsigned int> &l1,
                                const LoopifyLists::list<unsigned int> &l2) {
  bool _result;
  const LoopifyLists::list<unsigned int> *_loop_l2 = &l2;
  const LoopifyLists::list<unsigned int> *_loop_l1 = &l1;
  while (true) {
    if (std::holds_alternative<typename LoopifyLists::list<unsigned int>::Nil>(
            _loop_l1->v())) {
      _result = true;
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename LoopifyLists::list<unsigned int>::Cons>(
              _loop_l1->v());
      if (std::holds_alternative<
              typename LoopifyLists::list<unsigned int>::Nil>(_loop_l2->v())) {
        _result = false;
        break;
      } else {
        const auto &[a00, a10] =
            std::get<typename LoopifyLists::list<unsigned int>::Cons>(
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
LoopifyLists::list<unsigned int> LoopifyLists::lookup_all(
    unsigned int key,
    const LoopifyLists::list<std::pair<unsigned int, unsigned int>> &l) {
  std::unique_ptr<LoopifyLists::list<unsigned int>> _head{};
  std::unique_ptr<LoopifyLists::list<unsigned int>> *_write = &_head;
  const LoopifyLists::list<std::pair<unsigned int, unsigned int>> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<typename LoopifyLists::list<
            std::pair<unsigned int, unsigned int>>::Nil>(_loop_l->v())) {
      *_write = std::make_unique<LoopifyLists::list<unsigned int>>(
          list<unsigned int>::nil());
      break;
    } else {
      const auto &[a0, a1] = std::get<typename LoopifyLists::list<
          std::pair<unsigned int, unsigned int>>::Cons>(_loop_l->v());
      const unsigned int &k = a0.first;
      const unsigned int &v = a0.second;
      if (k == key) {
        auto _cell = std::make_unique<LoopifyLists::list<unsigned int>>(
            typename list<unsigned int>::Cons(v, nullptr));
        *_write = std::move(_cell);
        _write =
            &std::get<typename list<unsigned int>::Cons>((*_write)->v_mut()).a1;
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
bool LoopifyLists::member(unsigned int x,
                          const LoopifyLists::list<unsigned int> &l) {
  bool _result;
  const LoopifyLists::list<unsigned int> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<typename LoopifyLists::list<unsigned int>::Nil>(
            _loop_l->v())) {
      _result = false;
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename LoopifyLists::list<unsigned int>::Cons>(
              _loop_l->v());
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
unsigned int LoopifyLists::product(
    const LoopifyLists::list<unsigned int>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const LoopifyLists::list<unsigned int> *l;
  };

  /// _Resume_Cons: saves [a0], resumes after recursive call with _result.
  struct _Resume_Cons {
    unsigned int a0;
  };

  using _Frame = std::variant<_Enter, _Resume_Cons>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l});
  /// Loopified product: _Enter -> _Resume_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const LoopifyLists::list<unsigned int> &l = *_f.l;
      if (std::holds_alternative<
              typename LoopifyLists::list<unsigned int>::Nil>(l.v())) {
        _result = 1u;
      } else {
        const auto &[a0, a1] =
            std::get<typename LoopifyLists::list<unsigned int>::Cons>(l.v());
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
unsigned int LoopifyLists::sum_list(
    const LoopifyLists::list<unsigned int>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const LoopifyLists::list<unsigned int> *l;
  };

  /// _Resume_Cons: saves [a0], resumes after recursive call with _result.
  struct _Resume_Cons {
    unsigned int a0;
  };

  using _Frame = std::variant<_Enter, _Resume_Cons>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l});
  /// Loopified sum_list: _Enter -> _Resume_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const LoopifyLists::list<unsigned int> &l = *_f.l;
      if (std::holds_alternative<
              typename LoopifyLists::list<unsigned int>::Nil>(l.v())) {
        _result = 0u;
      } else {
        const auto &[a0, a1] =
            std::get<typename LoopifyLists::list<unsigned int>::Cons>(l.v());
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
LoopifyLists::list<unsigned int> LoopifyLists::flatten_nested_fuel(
    unsigned int fuel,
    const LoopifyLists::list<LoopifyLists::list<unsigned int>> &l) {
  std::unique_ptr<LoopifyLists::list<unsigned int>> _head{};
  std::unique_ptr<LoopifyLists::list<unsigned int>> *_write = &_head;
  LoopifyLists::list<LoopifyLists::list<unsigned int>> _loop_l = l;
  unsigned int _loop_fuel = std::move(fuel);
  while (true) {
    if (_loop_fuel <= 0) {
      *_write = std::make_unique<LoopifyLists::list<unsigned int>>(
          list<unsigned int>::nil());
      break;
    } else {
      unsigned int f = _loop_fuel - 1;
      if (std::holds_alternative<typename LoopifyLists::list<
              LoopifyLists::list<unsigned int>>::Nil>(_loop_l.v())) {
        *_write = std::make_unique<LoopifyLists::list<unsigned int>>(
            list<unsigned int>::nil());
        break;
      } else {
        const auto &[a0, a1] = std::get<typename LoopifyLists::list<
            LoopifyLists::list<unsigned int>>::Cons>(_loop_l.v());
        if (std::holds_alternative<
                typename LoopifyLists::list<unsigned int>::Nil>(a0.v())) {
          _loop_l = std::move(*a1);
          _loop_fuel = f;
          continue;
        } else {
          const auto &[a00, a10] =
              std::get<typename LoopifyLists::list<unsigned int>::Cons>(a0.v());
          auto _cell = std::make_unique<LoopifyLists::list<unsigned int>>(
              typename list<unsigned int>::Cons(a00, nullptr));
          *_write = std::move(_cell);
          _write =
              &std::get<typename list<unsigned int>::Cons>((*_write)->v_mut())
                   .a1;
          _loop_l = list<LoopifyLists::list<unsigned int>>::cons(*a10, *a1);
          _loop_fuel = f;
          continue;
        }
      }
    }
  }
  return std::move(*_head);
}

unsigned int LoopifyLists::sum_list_lengths(
    const LoopifyLists::list<LoopifyLists::list<unsigned int>>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const LoopifyLists::list<LoopifyLists::list<unsigned int>> *l;
  };

  /// _Resume_Cons: saves [a0], resumes after recursive call with _result.
  struct _Resume_Cons {
    decltype(len_list(std::declval<LoopifyLists::list<unsigned int> &>())) a0;
  };

  using _Frame = std::variant<_Enter, _Resume_Cons>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l});
  /// Loopified sum_list_lengths: _Enter -> _Resume_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const LoopifyLists::list<LoopifyLists::list<unsigned int>> &l = *_f.l;
      if (std::holds_alternative<typename LoopifyLists::list<
              LoopifyLists::list<unsigned int>>::Nil>(l.v())) {
        _result = 0u;
      } else {
        const auto &[a0, a1] = std::get<typename LoopifyLists::list<
            LoopifyLists::list<unsigned int>>::Cons>(l.v());
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

LoopifyLists::list<unsigned int> LoopifyLists::flatten_nested(
    const LoopifyLists::list<LoopifyLists::list<unsigned int>> &l) {
  return flatten_nested_fuel((sum_list_lengths(l) + 1), l);
}

/// compress l removes consecutive duplicates: 1,1,2,2,2,3 -> 1,2,3.
LoopifyLists::list<unsigned int>
LoopifyLists::compress(const LoopifyLists::list<unsigned int> &l) {
  std::unique_ptr<LoopifyLists::list<unsigned int>> _head{};
  std::unique_ptr<LoopifyLists::list<unsigned int>> *_write = &_head;
  const LoopifyLists::list<unsigned int> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<typename LoopifyLists::list<unsigned int>::Nil>(
            _loop_l->v())) {
      *_write = std::make_unique<LoopifyLists::list<unsigned int>>(
          list<unsigned int>::nil());
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename LoopifyLists::list<unsigned int>::Cons>(
              _loop_l->v());
      auto &&_sv0 = *a1;
      if (std::holds_alternative<
              typename LoopifyLists::list<unsigned int>::Nil>(_sv0.v())) {
        *_write = std::make_unique<LoopifyLists::list<unsigned int>>(
            list<unsigned int>::cons(a0, list<unsigned int>::nil()));
        break;
      } else {
        const auto &[a00, a10] =
            std::get<typename LoopifyLists::list<unsigned int>::Cons>(_sv0.v());
        if (a0 == a00) {
          _loop_l = a1.get();
          continue;
        } else {
          auto _cell = std::make_unique<LoopifyLists::list<unsigned int>>(
              typename list<unsigned int>::Cons(a0, nullptr));
          *_write = std::move(_cell);
          _write =
              &std::get<typename list<unsigned int>::Cons>((*_write)->v_mut())
                   .a1;
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
LoopifyLists::list<std::pair<unsigned int, unsigned int>>
LoopifyLists::group_pairs(const LoopifyLists::list<unsigned int> &l) {
  std::unique_ptr<LoopifyLists::list<std::pair<unsigned int, unsigned int>>>
      _head{};
  std::unique_ptr<LoopifyLists::list<std::pair<unsigned int, unsigned int>>>
      *_write = &_head;
  const LoopifyLists::list<unsigned int> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<typename LoopifyLists::list<unsigned int>::Nil>(
            _loop_l->v())) {
      *_write = std::make_unique<
          LoopifyLists::list<std::pair<unsigned int, unsigned int>>>(
          list<std::pair<unsigned int, unsigned int>>::nil());
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename LoopifyLists::list<unsigned int>::Cons>(
              _loop_l->v());
      auto &&_sv0 = *a1;
      if (std::holds_alternative<
              typename LoopifyLists::list<unsigned int>::Nil>(_sv0.v())) {
        *_write = std::make_unique<
            LoopifyLists::list<std::pair<unsigned int, unsigned int>>>(
            list<std::pair<unsigned int, unsigned int>>::nil());
        break;
      } else {
        const auto &[a00, a10] =
            std::get<typename LoopifyLists::list<unsigned int>::Cons>(_sv0.v());
        auto _cell = std::make_unique<
            LoopifyLists::list<std::pair<unsigned int, unsigned int>>>(
            typename list<std::pair<unsigned int, unsigned int>>::Cons(
                std::make_pair(a0, a00), nullptr));
        *_write = std::move(_cell);
        _write =
            &std::get<
                 typename list<std::pair<unsigned int, unsigned int>>::Cons>(
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
std::pair<LoopifyLists::list<unsigned int>, LoopifyLists::list<unsigned int>>
LoopifyLists::swizzle(
    const LoopifyLists::list<unsigned int>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const LoopifyLists::list<unsigned int> *l;
  };

  /// _Cont_Cons: saves [a0], resumes after recursive call, then processes rest.
  struct _Cont_Cons {
    unsigned int a0;
  };

  using _Frame = std::variant<_Enter, _Cont_Cons>;
  std::pair<LoopifyLists::list<unsigned int>, LoopifyLists::list<unsigned int>>
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
      const LoopifyLists::list<unsigned int> &l = *_f.l;
      if (std::holds_alternative<
              typename LoopifyLists::list<unsigned int>::Nil>(l.v())) {
        _result = std::make_pair(list<unsigned int>::nil(),
                                 list<unsigned int>::nil());
      } else {
        const auto &[a0, a1] =
            std::get<typename LoopifyLists::list<unsigned int>::Cons>(l.v());
        _stack.emplace_back(_Cont_Cons{a0});
        _stack.emplace_back(_Enter{a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Cont_Cons>(_frame));
      unsigned int a0 = _f.a0;
      const LoopifyLists::list<unsigned int> &odds = _result.first;
      const LoopifyLists::list<unsigned int> &evens = _result.second;
      _result = std::make_pair(list<unsigned int>::cons(a0, evens), odds);
    }
  }
  return _result;
}

/// index_of_aux x l i finds first index of x in l starting from i.
unsigned int LoopifyLists::index_of_aux(
    unsigned int x, const LoopifyLists::list<unsigned int> &l, unsigned int i) {
  unsigned int _result;
  unsigned int _loop_i = std::move(i);
  const LoopifyLists::list<unsigned int> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<typename LoopifyLists::list<unsigned int>::Nil>(
            _loop_l->v())) {
      _result = 0u;
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename LoopifyLists::list<unsigned int>::Cons>(
              _loop_l->v());
      if (x == a0) {
        _result = _loop_i;
        break;
      } else {
        _loop_i = (_loop_i + 1);
        _loop_l = a1.get();
      }
    }
  }
  return _result;
}

unsigned int LoopifyLists::index_of(unsigned int x,
                                    const LoopifyLists::list<unsigned int> &l) {
  return index_of_aux(x, l, 0u);
}

/// interleave l1 l2 interleaves two lists: 1,2 3,4 -> 1,3,2,4.
LoopifyLists::list<unsigned int>
LoopifyLists::interleave(LoopifyLists::list<unsigned int> l1,
                         LoopifyLists::list<unsigned int> l2) {
  std::unique_ptr<LoopifyLists::list<unsigned int>> _head{};
  std::unique_ptr<LoopifyLists::list<unsigned int>> *_write = &_head;
  LoopifyLists::list<unsigned int> _loop_l2 = std::move(l2);
  LoopifyLists::list<unsigned int> _loop_l1 = std::move(l1);
  while (true) {
    if (std::holds_alternative<typename LoopifyLists::list<unsigned int>::Nil>(
            _loop_l1.v_mut())) {
      *_write = std::make_unique<LoopifyLists::list<unsigned int>>(
          std::move(_loop_l2));
      break;
    } else {
      auto &[a0, a1] =
          std::get<typename LoopifyLists::list<unsigned int>::Cons>(
              _loop_l1.v_mut());
      if (std::holds_alternative<
              typename LoopifyLists::list<unsigned int>::Nil>(
              _loop_l2.v_mut())) {
        *_write = std::make_unique<LoopifyLists::list<unsigned int>>(_loop_l1);
        break;
      } else {
        auto &[a00, a10] =
            std::get<typename LoopifyLists::list<unsigned int>::Cons>(
                _loop_l2.v_mut());
        auto _cell = std::make_unique<LoopifyLists::list<unsigned int>>(
            typename list<unsigned int>::Cons(std::move(a0), nullptr));
        auto _cell1 = std::make_unique<LoopifyLists::list<unsigned int>>(
            typename list<unsigned int>::Cons(std::move(a00), nullptr));
        std::get<typename list<unsigned int>::Cons>(_cell->v_mut()).a1 =
            std::move(_cell1);
        *_write = std::move(_cell);
        _write =
            &std::get<typename list<unsigned int>::Cons>(
                 std::get<typename list<unsigned int>::Cons>((*_write)->v_mut())
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
unsigned int LoopifyLists::lookup(
    unsigned int key,
    const LoopifyLists::list<std::pair<unsigned int, unsigned int>> &l) {
  unsigned int _result;
  const LoopifyLists::list<std::pair<unsigned int, unsigned int>> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<typename LoopifyLists::list<
            std::pair<unsigned int, unsigned int>>::Nil>(_loop_l->v())) {
      _result = 0u;
      break;
    } else {
      const auto &[a0, a1] = std::get<typename LoopifyLists::list<
          std::pair<unsigned int, unsigned int>>::Cons>(_loop_l->v());
      const unsigned int &k = a0.first;
      const unsigned int &v = a0.second;
      if (k == key) {
        _result = v;
        break;
      } else {
        _loop_l = a1.get();
      }
    }
  }
  return _result;
}

/// group l groups consecutive equal elements: 1,1,2,2,2,3 -> [1,1],[2,2,2],[3].
LoopifyLists::list<LoopifyLists::list<unsigned int>>
LoopifyLists::group_fuel(unsigned int fuel,
                         const LoopifyLists::list<unsigned int> &l) {
  if (fuel <= 0) {
    return list<LoopifyLists::list<unsigned int>>::nil();
  } else {
    unsigned int f = fuel - 1;
    if (std::holds_alternative<typename LoopifyLists::list<unsigned int>::Nil>(
            l.v())) {
      return list<LoopifyLists::list<unsigned int>>::nil();
    } else {
      const auto &[a0, a1] =
          std::get<typename LoopifyLists::list<unsigned int>::Cons>(l.v());
      auto &&_sv0 = *a1;
      if (std::holds_alternative<
              typename LoopifyLists::list<unsigned int>::Nil>(_sv0.v())) {
        return list<LoopifyLists::list<unsigned int>>::cons(
            list<unsigned int>::cons(a0, list<unsigned int>::nil()),
            list<LoopifyLists::list<unsigned int>>::nil());
      } else {
        const auto &[a00, a10] =
            std::get<typename LoopifyLists::list<unsigned int>::Cons>(_sv0.v());
        if (a0 == a00) {
          auto &&_sv1 = group_fuel(f, *a1);
          if (std::holds_alternative<typename LoopifyLists::list<
                  LoopifyLists::list<unsigned int>>::Nil>(_sv1.v())) {
            return list<LoopifyLists::list<unsigned int>>::cons(
                list<unsigned int>::cons(a0, list<unsigned int>::nil()),
                list<LoopifyLists::list<unsigned int>>::nil());
          } else {
            const auto &[a01, a11] = std::get<typename LoopifyLists::list<
                LoopifyLists::list<unsigned int>>::Cons>(_sv1.v());
            return list<LoopifyLists::list<unsigned int>>::cons(
                list<unsigned int>::cons(a0, a01), *a11);
          }
        } else {
          return list<LoopifyLists::list<unsigned int>>::cons(
              list<unsigned int>::cons(a0, list<unsigned int>::nil()),
              group_fuel(f, *a1));
        }
      }
    }
  }
}

LoopifyLists::list<LoopifyLists::list<unsigned int>>
LoopifyLists::group(const LoopifyLists::list<unsigned int> &l) {
  return group_fuel((len_list(l) + 1), l);
}

/// Internal helper: reverse a list.
LoopifyLists::list<unsigned int>
LoopifyLists::rev_helper(LoopifyLists::list<unsigned int> acc,
                         const LoopifyLists::list<unsigned int> &l) {
  LoopifyLists::list<unsigned int> _result;
  const LoopifyLists::list<unsigned int> *_loop_l = &l;
  LoopifyLists::list<unsigned int> _loop_acc = std::move(acc);
  while (true) {
    if (std::holds_alternative<typename LoopifyLists::list<unsigned int>::Nil>(
            _loop_l->v())) {
      _result = std::move(_loop_acc);
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename LoopifyLists::list<unsigned int>::Cons>(
              _loop_l->v());
      _loop_l = a1.get();
      _loop_acc = list<unsigned int>::cons(a0, std::move(_loop_acc));
    }
  }
  return _result;
}

/// reverse_insert x l inserts x and reverses at each step.
LoopifyLists::list<unsigned int> LoopifyLists::reverse_insert(
    unsigned int x,
    const LoopifyLists::list<unsigned int>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const LoopifyLists::list<unsigned int> *l;
  };

  /// _Resume_Cons: saves [_s0, a0], resumes after recursive call with _result.
  struct _Resume_Cons {
    decltype(list<unsigned int>::nil()) _s0;
    unsigned int a0;
  };

  using _Frame = std::variant<_Enter, _Resume_Cons>;
  LoopifyLists::list<unsigned int> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l});
  /// Loopified reverse_insert: _Enter -> _Resume_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const LoopifyLists::list<unsigned int> &l = *_f.l;
      if (std::holds_alternative<
              typename LoopifyLists::list<unsigned int>::Nil>(l.v())) {
        _result = list<unsigned int>::cons(x, list<unsigned int>::nil());
      } else {
        const auto &[a0, a1] =
            std::get<typename LoopifyLists::list<unsigned int>::Cons>(l.v());
        _stack.emplace_back(_Resume_Cons{list<unsigned int>::nil(), a0});
        _stack.emplace_back(_Enter{a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Resume_Cons>(_frame));
      _result = rev_helper(_f._s0, list<unsigned int>::cons(_f.a0, _result));
    }
  }
  return _result;
}

/// Internal helper: append lists.
LoopifyLists::list<unsigned int>
LoopifyLists::app_helper(const LoopifyLists::list<unsigned int> &l1,
                         LoopifyLists::list<unsigned int> l2) {
  std::unique_ptr<LoopifyLists::list<unsigned int>> _head{};
  std::unique_ptr<LoopifyLists::list<unsigned int>> *_write = &_head;
  LoopifyLists::list<unsigned int> _loop_l2 = std::move(l2);
  const LoopifyLists::list<unsigned int> *_loop_l1 = &l1;
  while (true) {
    if (std::holds_alternative<typename LoopifyLists::list<unsigned int>::Nil>(
            _loop_l1->v())) {
      *_write = std::make_unique<LoopifyLists::list<unsigned int>>(
          std::move(_loop_l2));
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename LoopifyLists::list<unsigned int>::Cons>(
              _loop_l1->v());
      auto _cell = std::make_unique<LoopifyLists::list<unsigned int>>(
          typename list<unsigned int>::Cons(a0, nullptr));
      *_write = std::move(_cell);
      _write =
          &std::get<typename list<unsigned int>::Cons>((*_write)->v_mut()).a1;
      _loop_l1 = a1.get();
      continue;
    }
  }
  return std::move(*_head);
}

/// double_append l1 l2 appends with doubling: 1,2 3 -> 1,3,3,3,3.
LoopifyLists::list<unsigned int> LoopifyLists::double_append(
    const LoopifyLists::list<unsigned int> &l1,
    LoopifyLists::list<unsigned int>
        l2) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    LoopifyLists::list<unsigned int> l2;
    const LoopifyLists::list<unsigned int> *l1;
  };

  /// _Cont_Cons: saves [a0], resumes after recursive call, then processes rest.
  struct _Cont_Cons {
    unsigned int a0;
  };

  using _Frame = std::variant<_Enter, _Cont_Cons>;
  LoopifyLists::list<unsigned int> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{l2, &l1});
  /// Loopified double_append: _Enter -> _Cont_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      LoopifyLists::list<unsigned int> l2 = std::move(_f.l2);
      const LoopifyLists::list<unsigned int> &l1 = *_f.l1;
      if (std::holds_alternative<
              typename LoopifyLists::list<unsigned int>::Nil>(l1.v())) {
        _result = std::move(l2);
      } else {
        const auto &[a0, a1] =
            std::get<typename LoopifyLists::list<unsigned int>::Cons>(l1.v());
        _stack.emplace_back(_Cont_Cons{a0});
        _stack.emplace_back(_Enter{std::move(l2), a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Cont_Cons>(_frame));
      unsigned int a0 = _f.a0;
      LoopifyLists::list<unsigned int> rest = _result;
      _result = list<unsigned int>::cons(a0, app_helper(rest, rest));
    }
  }
  return _result;
}

/// remove_if_sum_even l removes element if sum with next is even.
LoopifyLists::list<unsigned int>
LoopifyLists::remove_if_sum_even(const LoopifyLists::list<unsigned int> &l) {
  std::unique_ptr<LoopifyLists::list<unsigned int>> _head{};
  std::unique_ptr<LoopifyLists::list<unsigned int>> *_write = &_head;
  const LoopifyLists::list<unsigned int> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<typename LoopifyLists::list<unsigned int>::Nil>(
            _loop_l->v())) {
      *_write = std::make_unique<LoopifyLists::list<unsigned int>>(
          list<unsigned int>::nil());
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename LoopifyLists::list<unsigned int>::Cons>(
              _loop_l->v());
      auto &&_sv0 = *a1;
      if (std::holds_alternative<
              typename LoopifyLists::list<unsigned int>::Nil>(_sv0.v())) {
        *_write = std::make_unique<LoopifyLists::list<unsigned int>>(
            list<unsigned int>::cons(a0, list<unsigned int>::nil()));
        break;
      } else {
        const auto &[a00, a10] =
            std::get<typename LoopifyLists::list<unsigned int>::Cons>(_sv0.v());
        if ((2u ? (a0 + a00) % 2u : (a0 + a00)) == 0u) {
          _loop_l = a1.get();
          continue;
        } else {
          auto _cell = std::make_unique<LoopifyLists::list<unsigned int>>(
              typename list<unsigned int>::Cons(a0, nullptr));
          *_write = std::move(_cell);
          _write =
              &std::get<typename list<unsigned int>::Cons>((*_write)->v_mut())
                   .a1;
          _loop_l = a1.get();
          continue;
        }
      }
    }
  }
  return std::move(*_head);
}

/// split_at n l splits list at index n into (prefix, suffix).
std::pair<LoopifyLists::list<unsigned int>, LoopifyLists::list<unsigned int>>
LoopifyLists::split_at(
    unsigned int n,
    LoopifyLists::list<unsigned int>
        l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    LoopifyLists::list<unsigned int> l;
    unsigned int n;
  };

  /// _Cont1: saves [a0], resumes after recursive call, then processes rest.
  struct _Cont1 {
    unsigned int a0;
  };

  using _Frame = std::variant<_Enter, _Cont1>;
  std::pair<LoopifyLists::list<unsigned int>, LoopifyLists::list<unsigned int>>
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
      LoopifyLists::list<unsigned int> l = std::move(_f.l);
      unsigned int n = _f.n;
      if (std::holds_alternative<
              typename LoopifyLists::list<unsigned int>::Nil>(l.v_mut())) {
        _result = std::make_pair(list<unsigned int>::nil(),
                                 list<unsigned int>::nil());
      } else {
        auto &[a0, a1] =
            std::get<typename LoopifyLists::list<unsigned int>::Cons>(
                l.v_mut());
        if (n == 0u) {
          _result = std::make_pair(list<unsigned int>::nil(), l);
        } else {
          _stack.emplace_back(_Cont1{a0});
          _stack.emplace_back(
              _Enter{std::move(*a1), (((n - 1u) > n ? 0 : (n - 1u)))});
        }
      }
    } else {
      auto _f = std::move(std::get<_Cont1>(_frame));
      unsigned int a0 = _f.a0;
      const LoopifyLists::list<unsigned int> &a = _result.first;
      const LoopifyLists::list<unsigned int> &b = _result.second;
      _result = std::make_pair(list<unsigned int>::cons(std::move(a0), a), b);
    }
  }
  return _result;
}

/// unzip l splits list of pairs into two lists.
std::pair<LoopifyLists::list<unsigned int>, LoopifyLists::list<unsigned int>>
LoopifyLists::unzip(
    const LoopifyLists::list<std::pair<unsigned int, unsigned int>>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const LoopifyLists::list<std::pair<unsigned int, unsigned int>> *l;
  };

  /// _Cont_a: saves [a, b], resumes after recursive call, then processes rest.
  struct _Cont_a {
    unsigned int a;
    unsigned int b;
  };

  using _Frame = std::variant<_Enter, _Cont_a>;
  std::pair<LoopifyLists::list<unsigned int>, LoopifyLists::list<unsigned int>>
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
      const LoopifyLists::list<std::pair<unsigned int, unsigned int>> &l =
          *_f.l;
      if (std::holds_alternative<typename LoopifyLists::list<
              std::pair<unsigned int, unsigned int>>::Nil>(l.v())) {
        _result = std::make_pair(list<unsigned int>::nil(),
                                 list<unsigned int>::nil());
      } else {
        const auto &[a0, a1] = std::get<typename LoopifyLists::list<
            std::pair<unsigned int, unsigned int>>::Cons>(l.v());
        const unsigned int &a = a0.first;
        const unsigned int &b = a0.second;
        _stack.emplace_back(_Cont_a{a, b});
        _stack.emplace_back(_Enter{a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Cont_a>(_frame));
      unsigned int a = _f.a;
      unsigned int b = _f.b;
      const LoopifyLists::list<unsigned int> &xs = _result.first;
      const LoopifyLists::list<unsigned int> &ys = _result.second;
      _result = std::make_pair(list<unsigned int>::cons(a, xs),
                               list<unsigned int>::cons(b, ys));
    }
  }
  return _result;
}

/// nth n l default returns nth element or default if out of bounds.
unsigned int LoopifyLists::nth(unsigned int n,
                               const LoopifyLists::list<unsigned int> &l,
                               unsigned int default0) {
  unsigned int _result;
  const LoopifyLists::list<unsigned int> *_loop_l = &l;
  unsigned int _loop_n = std::move(n);
  while (true) {
    if (std::holds_alternative<typename LoopifyLists::list<unsigned int>::Nil>(
            _loop_l->v())) {
      _result = default0;
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename LoopifyLists::list<unsigned int>::Cons>(
              _loop_l->v());
      if (_loop_n == 0u) {
        _result = a0;
        break;
      } else {
        _loop_l = a1.get();
        _loop_n = (((_loop_n - 1u) > _loop_n ? 0 : (_loop_n - 1u)));
      }
    }
  }
  return _result;
}

/// last l default returns last element or default if empty.
unsigned int LoopifyLists::last(const LoopifyLists::list<unsigned int> &l,
                                unsigned int default0) {
  unsigned int _result;
  const LoopifyLists::list<unsigned int> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<typename LoopifyLists::list<unsigned int>::Nil>(
            _loop_l->v())) {
      _result = default0;
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename LoopifyLists::list<unsigned int>::Cons>(
              _loop_l->v());
      auto &&_sv = *a1;
      if (std::holds_alternative<
              typename LoopifyLists::list<unsigned int>::Nil>(_sv.v())) {
        _result = a0;
        break;
      } else {
        _loop_l = a1.get();
      }
    }
  }
  return _result;
}

/// drop n l drops first n elements.
LoopifyLists::list<unsigned int>
LoopifyLists::drop(unsigned int n, LoopifyLists::list<unsigned int> l) {
  LoopifyLists::list<unsigned int> _result;
  LoopifyLists::list<unsigned int> _loop_l = std::move(l);
  unsigned int _loop_n = std::move(n);
  while (true) {
    if (std::holds_alternative<typename LoopifyLists::list<unsigned int>::Nil>(
            _loop_l.v_mut())) {
      _result = list<unsigned int>::nil();
      break;
    } else {
      auto &[a0, a1] =
          std::get<typename LoopifyLists::list<unsigned int>::Cons>(
              _loop_l.v_mut());
      if (_loop_n == 0u) {
        _result = _loop_l;
        break;
      } else {
        _loop_l = std::move(*a1);
        _loop_n = (((_loop_n - 1u) > _loop_n ? 0 : (_loop_n - 1u)));
      }
    }
  }
  return _result;
}

/// init l returns all but last element.
LoopifyLists::list<unsigned int>
LoopifyLists::init(const LoopifyLists::list<unsigned int> &l) {
  std::unique_ptr<LoopifyLists::list<unsigned int>> _head{};
  std::unique_ptr<LoopifyLists::list<unsigned int>> *_write = &_head;
  const LoopifyLists::list<unsigned int> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<typename LoopifyLists::list<unsigned int>::Nil>(
            _loop_l->v())) {
      *_write = std::make_unique<LoopifyLists::list<unsigned int>>(
          list<unsigned int>::nil());
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename LoopifyLists::list<unsigned int>::Cons>(
              _loop_l->v());
      auto &&_sv = *a1;
      if (std::holds_alternative<
              typename LoopifyLists::list<unsigned int>::Nil>(_sv.v())) {
        *_write = std::make_unique<LoopifyLists::list<unsigned int>>(
            list<unsigned int>::nil());
        break;
      } else {
        auto _cell = std::make_unique<LoopifyLists::list<unsigned int>>(
            typename list<unsigned int>::Cons(a0, nullptr));
        *_write = std::move(_cell);
        _write =
            &std::get<typename list<unsigned int>::Cons>((*_write)->v_mut()).a1;
        _loop_l = a1.get();
        continue;
      }
    }
  }
  return std::move(*_head);
}

/// count x l counts occurrences of x in l.
unsigned int LoopifyLists::count(
    unsigned int x,
    const LoopifyLists::list<unsigned int>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const LoopifyLists::list<unsigned int> *l;
  };

  /// _Resume1: resumes after recursive call with _result.
  struct _Resume1 {};

  using _Frame = std::variant<_Enter, _Resume1>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l});
  /// Loopified count: _Enter -> _Resume1.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const LoopifyLists::list<unsigned int> &l = *_f.l;
      if (std::holds_alternative<
              typename LoopifyLists::list<unsigned int>::Nil>(l.v())) {
        _result = 0u;
      } else {
        const auto &[a0, a1] =
            std::get<typename LoopifyLists::list<unsigned int>::Cons>(l.v());
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
unsigned int LoopifyLists::maximum(
    const LoopifyLists::list<unsigned int>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const LoopifyLists::list<unsigned int> *l;
  };

  /// _Cont_Cons: saves [a0], resumes after recursive call, then processes rest.
  struct _Cont_Cons {
    unsigned int a0;
  };

  using _Frame = std::variant<_Enter, _Cont_Cons>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l});
  /// Loopified maximum: _Enter -> _Cont_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const LoopifyLists::list<unsigned int> &l = *_f.l;
      if (std::holds_alternative<
              typename LoopifyLists::list<unsigned int>::Nil>(l.v())) {
        _result = 0u;
      } else {
        const auto &[a0, a1] =
            std::get<typename LoopifyLists::list<unsigned int>::Cons>(l.v());
        auto &&_sv = *a1;
        if (std::holds_alternative<
                typename LoopifyLists::list<unsigned int>::Nil>(_sv.v())) {
          _result = a0;
        } else {
          _stack.emplace_back(_Cont_Cons{a0});
          _stack.emplace_back(_Enter{a1.get()});
        }
      }
    } else {
      auto _f = std::move(std::get<_Cont_Cons>(_frame));
      unsigned int a0 = _f.a0;
      unsigned int max_rest = _result;
      if (max_rest <= a0) {
        _result = a0;
      } else {
        _result = max_rest;
      }
    }
  }
  return _result;
}

/// minmax l finds both minimum and maximum in one pass.
std::pair<unsigned int, unsigned int> LoopifyLists::minmax(
    const LoopifyLists::list<unsigned int>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const LoopifyLists::list<unsigned int> *l;
  };

  /// _Cont_Cons: saves [a0], resumes after recursive call, then processes rest.
  struct _Cont_Cons {
    unsigned int a0;
  };

  using _Frame = std::variant<_Enter, _Cont_Cons>;
  std::pair<unsigned int, unsigned int> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l});
  /// Loopified minmax: _Enter -> _Cont_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const LoopifyLists::list<unsigned int> &l = *_f.l;
      if (std::holds_alternative<
              typename LoopifyLists::list<unsigned int>::Nil>(l.v())) {
        _result = std::make_pair(0u, 0u);
      } else {
        const auto &[a0, a1] =
            std::get<typename LoopifyLists::list<unsigned int>::Cons>(l.v());
        auto &&_sv = *a1;
        if (std::holds_alternative<
                typename LoopifyLists::list<unsigned int>::Nil>(_sv.v())) {
          _result = std::make_pair(a0, a0);
        } else {
          _stack.emplace_back(_Cont_Cons{a0});
          _stack.emplace_back(_Enter{a1.get()});
        }
      }
    } else {
      auto _f = std::move(std::get<_Cont_Cons>(_frame));
      unsigned int a0 = _f.a0;
      const unsigned int &lo = _result.first;
      const unsigned int &hi = _result.second;
      _result = std::make_pair((a0 <= lo ? a0 : lo), (hi <= a0 ? a0 : hi));
    }
  }
  return _result;
}

/// Helper for rotate_left.
LoopifyLists::list<unsigned int>
LoopifyLists::rotate_left_fuel(unsigned int fuel, unsigned int n,
                               LoopifyLists::list<unsigned int> l) {
  LoopifyLists::list<unsigned int> _result;
  LoopifyLists::list<unsigned int> _loop_l = std::move(l);
  unsigned int _loop_n = std::move(n);
  unsigned int _loop_fuel = std::move(fuel);
  while (true) {
    if (_loop_fuel <= 0) {
      _result = std::move(_loop_l);
      break;
    } else {
      unsigned int f = _loop_fuel - 1;
      if (_loop_n == 0u) {
        _result = std::move(_loop_l);
        break;
      } else {
        if (std::holds_alternative<
                typename LoopifyLists::list<unsigned int>::Nil>(
                _loop_l.v_mut())) {
          _result = list<unsigned int>::nil();
          break;
        } else {
          auto &[a0, a1] =
              std::get<typename LoopifyLists::list<unsigned int>::Cons>(
                  _loop_l.v_mut());
          _loop_l =
              app_helper(*a1, list<unsigned int>::cons(
                                  std::move(a0), list<unsigned int>::nil()));
          _loop_n = (((_loop_n - 1u) > _loop_n ? 0 : (_loop_n - 1u)));
          _loop_fuel = f;
        }
      }
    }
  }
  return _result;
}

/// rotate_left n l rotates list left by n positions: rotate 2 1,2,3,4 ->
/// 3,4,1,2.
LoopifyLists::list<unsigned int>
LoopifyLists::rotate_left(unsigned int n,
                          const LoopifyLists::list<unsigned int> &l) {
  return rotate_left_fuel((n + 1), n, l);
}

/// intercalate sep lists joins lists with separator: intercalate 0 [1,2],[3,4]
/// -> 1,2,0,3,4.
LoopifyLists::list<unsigned int> LoopifyLists::intercalate(
    const LoopifyLists::list<unsigned int> &sep,
    const LoopifyLists::list<LoopifyLists::list<unsigned int>>
        &lists) { /// _Enter: captures varying parameters for each recursive
                  /// call.

  struct _Enter {
    const LoopifyLists::list<LoopifyLists::list<unsigned int>> *lists;
  };

  /// _Resume_Cons: saves [a0, sep], resumes after recursive call with _result.
  struct _Resume_Cons {
    LoopifyLists::list<unsigned int> a0;
    LoopifyLists::list<unsigned int> sep;
  };

  using _Frame = std::variant<_Enter, _Resume_Cons>;
  LoopifyLists::list<unsigned int> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&lists});
  /// Loopified intercalate: _Enter -> _Resume_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const LoopifyLists::list<LoopifyLists::list<unsigned int>> &lists =
          *_f.lists;
      if (std::holds_alternative<typename LoopifyLists::list<
              LoopifyLists::list<unsigned int>>::Nil>(lists.v())) {
        _result = list<unsigned int>::nil();
      } else {
        const auto &[a0, a1] = std::get<typename LoopifyLists::list<
            LoopifyLists::list<unsigned int>>::Cons>(lists.v());
        auto &&_sv = *a1;
        if (std::holds_alternative<typename LoopifyLists::list<
                LoopifyLists::list<unsigned int>>::Nil>(_sv.v())) {
          _result = a0;
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
std::pair<unsigned int, unsigned int> LoopifyLists::majority(
    const LoopifyLists::list<unsigned int>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const LoopifyLists::list<unsigned int> *l;
  };

  /// _Cont_Cons: saves [a0], resumes after recursive call, then processes rest.
  struct _Cont_Cons {
    unsigned int a0;
  };

  using _Frame = std::variant<_Enter, _Cont_Cons>;
  std::pair<unsigned int, unsigned int> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l});
  /// Loopified majority: _Enter -> _Cont_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const LoopifyLists::list<unsigned int> &l = *_f.l;
      if (std::holds_alternative<
              typename LoopifyLists::list<unsigned int>::Nil>(l.v())) {
        _result = std::make_pair(0u, 0u);
      } else {
        const auto &[a0, a1] =
            std::get<typename LoopifyLists::list<unsigned int>::Cons>(l.v());
        auto &&_sv = *a1;
        if (std::holds_alternative<
                typename LoopifyLists::list<unsigned int>::Nil>(_sv.v())) {
          _result = std::make_pair(a0, 1u);
        } else {
          _stack.emplace_back(_Cont_Cons{a0});
          _stack.emplace_back(_Enter{a1.get()});
        }
      }
    } else {
      auto _f = std::move(std::get<_Cont_Cons>(_frame));
      unsigned int a0 = _f.a0;
      const unsigned int &cand = _result.first;
      const unsigned int &cnt = _result.second;
      if (a0 == cand) {
        _result = std::make_pair(cand, (cnt + 1));
      } else {
        if (cnt == 0u) {
          _result = std::make_pair(a0, 1u);
        } else {
          _result = std::make_pair(cand, (((cnt - 1u) > cnt ? 0 : (cnt - 1u))));
        }
      }
    }
  }
  return _result;
}

/// zip3 l1 l2 l3 zips three lists into triples.
LoopifyLists::list<
    std::pair<std::pair<unsigned int, unsigned int>, unsigned int>>
LoopifyLists::zip3(const LoopifyLists::list<unsigned int> &l1,
                   const LoopifyLists::list<unsigned int> &l2,
                   const LoopifyLists::list<unsigned int> &l3) {
  std::unique_ptr<LoopifyLists::list<
      std::pair<std::pair<unsigned int, unsigned int>, unsigned int>>>
      _head{};
  std::unique_ptr<LoopifyLists::list<
      std::pair<std::pair<unsigned int, unsigned int>, unsigned int>>> *_write =
      &_head;
  const LoopifyLists::list<unsigned int> *_loop_l3 = &l3;
  const LoopifyLists::list<unsigned int> *_loop_l2 = &l2;
  const LoopifyLists::list<unsigned int> *_loop_l1 = &l1;
  while (true) {
    if (std::holds_alternative<typename LoopifyLists::list<unsigned int>::Nil>(
            _loop_l1->v())) {
      *_write = std::make_unique<LoopifyLists::list<
          std::pair<std::pair<unsigned int, unsigned int>, unsigned int>>>(
          list<std::pair<std::pair<unsigned int, unsigned int>,
                         unsigned int>>::nil());
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename LoopifyLists::list<unsigned int>::Cons>(
              _loop_l1->v());
      if (std::holds_alternative<
              typename LoopifyLists::list<unsigned int>::Nil>(_loop_l2->v())) {
        *_write = std::make_unique<LoopifyLists::list<
            std::pair<std::pair<unsigned int, unsigned int>, unsigned int>>>(
            list<std::pair<std::pair<unsigned int, unsigned int>,
                           unsigned int>>::nil());
        break;
      } else {
        const auto &[a00, a10] =
            std::get<typename LoopifyLists::list<unsigned int>::Cons>(
                _loop_l2->v());
        if (std::holds_alternative<
                typename LoopifyLists::list<unsigned int>::Nil>(
                _loop_l3->v())) {
          *_write = std::make_unique<LoopifyLists::list<
              std::pair<std::pair<unsigned int, unsigned int>, unsigned int>>>(
              list<std::pair<std::pair<unsigned int, unsigned int>,
                             unsigned int>>::nil());
          break;
        } else {
          const auto &[a01, a11] =
              std::get<typename LoopifyLists::list<unsigned int>::Cons>(
                  _loop_l3->v());
          auto _cell = std::make_unique<LoopifyLists::list<
              std::pair<std::pair<unsigned int, unsigned int>, unsigned int>>>(
              typename list<std::pair<std::pair<unsigned int, unsigned int>,
                                      unsigned int>>::
                  Cons(std::make_pair(std::make_pair(a0, a00), a01), nullptr));
          *_write = std::move(_cell);
          _write = &std::get<typename list<std::pair<
              std::pair<unsigned int, unsigned int>, unsigned int>>::Cons>(
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
std::pair<unsigned int, unsigned int> LoopifyLists::sum_and_count(
    const LoopifyLists::list<unsigned int>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const LoopifyLists::list<unsigned int> *l;
  };

  /// _Cont_Cons: saves [a0], resumes after recursive call, then processes rest.
  struct _Cont_Cons {
    unsigned int a0;
  };

  using _Frame = std::variant<_Enter, _Cont_Cons>;
  std::pair<unsigned int, unsigned int> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l});
  /// Loopified sum_and_count: _Enter -> _Cont_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const LoopifyLists::list<unsigned int> &l = *_f.l;
      if (std::holds_alternative<
              typename LoopifyLists::list<unsigned int>::Nil>(l.v())) {
        _result = std::make_pair(0u, 0u);
      } else {
        const auto &[a0, a1] =
            std::get<typename LoopifyLists::list<unsigned int>::Cons>(l.v());
        _stack.emplace_back(_Cont_Cons{a0});
        _stack.emplace_back(_Enter{a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Cont_Cons>(_frame));
      unsigned int a0 = _f.a0;
      const unsigned int &s = _result.first;
      const unsigned int &c = _result.second;
      _result = std::make_pair((a0 + s), (c + 1));
    }
  }
  return _result;
}

/// elem_at n l returns element at index n (like nth but with different name).
std::optional<unsigned int>
LoopifyLists::elem_at(unsigned int n,
                      const LoopifyLists::list<unsigned int> &l) {
  std::optional<unsigned int> _result;
  const LoopifyLists::list<unsigned int> *_loop_l = &l;
  unsigned int _loop_n = std::move(n);
  while (true) {
    if (std::holds_alternative<typename LoopifyLists::list<unsigned int>::Nil>(
            _loop_l->v())) {
      _result = std::optional<unsigned int>();
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename LoopifyLists::list<unsigned int>::Cons>(
              _loop_l->v());
      if (_loop_n == 0u) {
        _result = std::make_optional<unsigned int>(a0);
        break;
      } else {
        _loop_l = a1.get();
        _loop_n = (((_loop_n - 1u) > _loop_n ? 0 : (_loop_n - 1u)));
      }
    }
  }
  return _result;
}
