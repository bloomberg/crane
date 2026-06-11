#include "loopify_lists.h"

/// Consolidated UNIQUE list operations - no stdlib duplicates.
/// Tests loopification on domain-specific list algorithms.
/// range start count generates start, start+1, ..., start+count-1.
LoopifyLists::list<uint64_t>
LoopifyLists::range(uint64_t start,
                    uint64_t count0) { /// _Enter: captures varying parameters
                                       /// for each recursive call.

  struct _Enter {
    uint64_t count0;
    uint64_t start;
  };

  /// _Resume_c: saves [start], resumes after recursive call with _result.
  struct _Resume_c {
    uint64_t start;
  };

  using _Frame = std::variant<_Enter, _Resume_c>;
  LoopifyLists::list<uint64_t> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{count0, start});
  /// Loopified range: _Enter -> _Resume_c.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      uint64_t count0 = _f.count0;
      uint64_t start = _f.start;
      if (count0 <= 0) {
        _result = list<uint64_t>::nil();
      } else {
        uint64_t c = count0 - 1;
        _stack.emplace_back(_Resume_c{start});
        _stack.emplace_back(_Enter{c, (start + 1)});
      }
    } else {
      auto _f = std::move(std::get<_Resume_c>(_frame));
      _result = list<uint64_t>::cons(_f.start, std::move(_result));
    }
  }
  return _result;
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
      _result = (_f.contribution + std::move(_result));
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
      _result = (_f.abs_val + std::move(_result));
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
      _result = (_f._s0 + (_f._s1 + std::move(_result)));
    }
  }
  return _result;
}

/// between lo hi l filters elements in range lo, hi.
LoopifyLists::list<uint64_t> LoopifyLists::between(
    uint64_t lo, uint64_t hi,
    const LoopifyLists::list<uint64_t>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const LoopifyLists::list<uint64_t> *l;
  };

  /// _Resume1: saves [a0], resumes after recursive call with _result.
  struct _Resume1 {
    uint64_t a0;
  };

  using _Frame = std::variant<_Enter, _Resume1>;
  LoopifyLists::list<uint64_t> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l});
  /// Loopified between: _Enter -> _Resume1.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const LoopifyLists::list<uint64_t> &l = *_f.l;
      if (std::holds_alternative<typename LoopifyLists::list<uint64_t>::Nil>(
              l.v())) {
        _result = list<uint64_t>::nil();
      } else {
        const auto &[a0, a1] =
            std::get<typename LoopifyLists::list<uint64_t>::Cons>(l.v());
        if ((lo <= a0 && a0 <= hi)) {
          _stack.emplace_back(_Resume1{a0});
          _stack.emplace_back(_Enter{a1.get()});
        } else {
          _stack.emplace_back(_Enter{a1.get()});
        }
      }
    } else {
      auto _f = std::move(std::get<_Resume1>(_frame));
      _result = list<uint64_t>::cons(_f.a0, std::move(_result));
    }
  }
  return _result;
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
      _result = (_f.score + std::move(_result));
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
      uint64_t rest = std::move(_result);
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
LoopifyLists::list<uint64_t> LoopifyLists::pairwise_sum(
    const LoopifyLists::list<uint64_t>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const LoopifyLists::list<uint64_t> *l;
  };

  /// _Resume_Cons: saves [_s0], resumes after recursive call with _result.
  struct _Resume_Cons {
    uint64_t _s0;
  };

  using _Frame = std::variant<_Enter, _Resume_Cons>;
  LoopifyLists::list<uint64_t> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l});
  /// Loopified pairwise_sum: _Enter -> _Resume_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const LoopifyLists::list<uint64_t> &l = *_f.l;
      if (std::holds_alternative<typename LoopifyLists::list<uint64_t>::Nil>(
              l.v())) {
        _result = list<uint64_t>::nil();
      } else {
        const auto &[a0, a1] =
            std::get<typename LoopifyLists::list<uint64_t>::Cons>(l.v());
        auto &&_sv0 = *a1;
        if (std::holds_alternative<typename LoopifyLists::list<uint64_t>::Nil>(
                _sv0.v())) {
          _result = list<uint64_t>::nil();
        } else {
          const auto &[a00, a10] =
              std::get<typename LoopifyLists::list<uint64_t>::Cons>(_sv0.v());
          _stack.emplace_back(_Resume_Cons{(a0 + a00)});
          _stack.emplace_back(_Enter{a10.get()});
        }
      }
    } else {
      auto _f = std::move(std::get<_Resume_Cons>(_frame));
      _result = list<uint64_t>::cons(_f._s0, std::move(_result));
    }
  }
  return _result;
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
      _result = (_f._s0 + std::move(_result));
    }
  }
  return _result;
}

/// prefix_sums acc l returns all prefix sums: 1,2,3 -> 0,1,3,6.
LoopifyLists::list<uint64_t> LoopifyLists::prefix_sums(
    uint64_t acc,
    const LoopifyLists::list<uint64_t>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const LoopifyLists::list<uint64_t> *l;
    uint64_t acc;
  };

  /// _Resume_Cons: saves [acc], resumes after recursive call with _result.
  struct _Resume_Cons {
    uint64_t acc;
  };

  using _Frame = std::variant<_Enter, _Resume_Cons>;
  LoopifyLists::list<uint64_t> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l, acc});
  /// Loopified prefix_sums: _Enter -> _Resume_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const LoopifyLists::list<uint64_t> &l = *_f.l;
      uint64_t acc = _f.acc;
      if (std::holds_alternative<typename LoopifyLists::list<uint64_t>::Nil>(
              l.v())) {
        _result = list<uint64_t>::cons(acc, list<uint64_t>::nil());
      } else {
        const auto &[a0, a1] =
            std::get<typename LoopifyLists::list<uint64_t>::Cons>(l.v());
        _stack.emplace_back(_Resume_Cons{acc});
        _stack.emplace_back(_Enter{a1.get(), (acc + a0)});
      }
    } else {
      auto _f = std::move(std::get<_Resume_Cons>(_frame));
      _result = list<uint64_t>::cons(_f.acc, std::move(_result));
    }
  }
  return _result;
}

/// uniq_sorted l removes consecutive duplicates from sorted list.
LoopifyLists::list<uint64_t> LoopifyLists::uniq_sorted(
    const LoopifyLists::list<uint64_t>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const LoopifyLists::list<uint64_t> *l;
  };

  /// _Resume1: saves [a0], resumes after recursive call with _result.
  struct _Resume1 {
    uint64_t a0;
  };

  using _Frame = std::variant<_Enter, _Resume1>;
  LoopifyLists::list<uint64_t> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l});
  /// Loopified uniq_sorted: _Enter -> _Resume1.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const LoopifyLists::list<uint64_t> &l = *_f.l;
      if (std::holds_alternative<typename LoopifyLists::list<uint64_t>::Nil>(
              l.v())) {
        _result = list<uint64_t>::nil();
      } else {
        const auto &[a0, a1] =
            std::get<typename LoopifyLists::list<uint64_t>::Cons>(l.v());
        auto &&_sv0 = *a1;
        if (std::holds_alternative<typename LoopifyLists::list<uint64_t>::Nil>(
                _sv0.v())) {
          _result = list<uint64_t>::cons(a0, list<uint64_t>::nil());
        } else {
          const auto &[a00, a10] =
              std::get<typename LoopifyLists::list<uint64_t>::Cons>(_sv0.v());
          if (a0 == a00) {
            _stack.emplace_back(_Enter{a1.get()});
          } else {
            _stack.emplace_back(_Resume1{a0});
            _stack.emplace_back(_Enter{a1.get()});
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

/// Helper: take first n elements.
LoopifyLists::list<uint64_t> LoopifyLists::take_n(
    uint64_t n,
    const LoopifyLists::list<uint64_t>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const LoopifyLists::list<uint64_t> *l;
    uint64_t n;
  };

  /// _Resume_Cons: saves [a0], resumes after recursive call with _result.
  struct _Resume_Cons {
    uint64_t a0;
  };

  using _Frame = std::variant<_Enter, _Resume_Cons>;
  LoopifyLists::list<uint64_t> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l, n});
  /// Loopified take_n: _Enter -> _Resume_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const LoopifyLists::list<uint64_t> &l = *_f.l;
      uint64_t n = _f.n;
      if (n <= 0) {
        _result = list<uint64_t>::nil();
      } else {
        uint64_t m = n - 1;
        if (std::holds_alternative<typename LoopifyLists::list<uint64_t>::Nil>(
                l.v())) {
          _result = list<uint64_t>::nil();
        } else {
          const auto &[a0, a1] =
              std::get<typename LoopifyLists::list<uint64_t>::Cons>(l.v());
          _stack.emplace_back(_Resume_Cons{a0});
          _stack.emplace_back(_Enter{a1.get(), m});
        }
      }
    } else {
      auto _f = std::move(std::get<_Resume_Cons>(_frame));
      _result = list<uint64_t>::cons(_f.a0, std::move(_result));
    }
  }
  return _result;
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
      _result = (std::move(_result) + 1);
    }
  }
  return _result;
}

/// windows n l returns all sliding windows of size n.
LoopifyLists::list<LoopifyLists::list<uint64_t>> LoopifyLists::windows_aux(
    uint64_t fuel, uint64_t n,
    const LoopifyLists::list<uint64_t>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const LoopifyLists::list<uint64_t> *l;
    uint64_t fuel;
  };

  /// _Resume_Cons: saves [window], resumes after recursive call with _result.
  struct _Resume_Cons {
    LoopifyLists::list<uint64_t> window;
  };

  using _Frame = std::variant<_Enter, _Resume_Cons>;
  LoopifyLists::list<LoopifyLists::list<uint64_t>> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l, fuel});
  /// Loopified windows_aux: _Enter -> _Resume_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const LoopifyLists::list<uint64_t> &l = *_f.l;
      uint64_t fuel = _f.fuel;
      if (fuel <= 0) {
        _result = list<LoopifyLists::list<uint64_t>>::nil();
      } else {
        uint64_t f = fuel - 1;
        if (std::holds_alternative<typename LoopifyLists::list<uint64_t>::Nil>(
                l.v())) {
          _result = list<LoopifyLists::list<uint64_t>>::nil();
        } else {
          const auto &[a0, a1] =
              std::get<typename LoopifyLists::list<uint64_t>::Cons>(l.v());
          if (len_list(l) < n) {
            _result = list<LoopifyLists::list<uint64_t>>::nil();
          } else {
            LoopifyLists::list<uint64_t> window = take_n(n, l);
            if (std::holds_alternative<
                    typename LoopifyLists::list<uint64_t>::Nil>(
                    window.v_mut())) {
              _result = list<LoopifyLists::list<uint64_t>>::nil();
            } else {
              _stack.emplace_back(_Resume_Cons{window});
              _stack.emplace_back(_Enter{a1.get(), f});
            }
          }
        }
      }
    } else {
      auto _f = std::move(std::get<_Resume_Cons>(_frame));
      _result = list<LoopifyLists::list<uint64_t>>::cons(std::move(_f.window),
                                                         std::move(_result));
    }
  }
  return _result;
}

LoopifyLists::list<LoopifyLists::list<uint64_t>>
LoopifyLists::windows(uint64_t n, const LoopifyLists::list<uint64_t> &l) {
  return windows_aux((len_list(l) + 1), n, l);
}

/// is_prefix_of l1 l2 checks if l1 is a prefix of l2.
bool LoopifyLists::is_prefix_of(const LoopifyLists::list<uint64_t> &l1,
                                const LoopifyLists::list<uint64_t> &l2) {
  const LoopifyLists::list<uint64_t> *_loop_l2 = &l2;
  const LoopifyLists::list<uint64_t> *_loop_l1 = &l1;
  while (true) {
    if (std::holds_alternative<typename LoopifyLists::list<uint64_t>::Nil>(
            _loop_l1->v())) {
      return true;
    } else {
      const auto &[a0, a1] =
          std::get<typename LoopifyLists::list<uint64_t>::Cons>(_loop_l1->v());
      if (std::holds_alternative<typename LoopifyLists::list<uint64_t>::Nil>(
              _loop_l2->v())) {
        return false;
      } else {
        const auto &[a00, a10] =
            std::get<typename LoopifyLists::list<uint64_t>::Cons>(
                _loop_l2->v());
        if (a0 == a00) {
          _loop_l2 = a10.get();
          _loop_l1 = a1.get();
        } else {
          return false;
        }
      }
    }
  }
}

/// lookup_all key l finds all values for key in association list.
LoopifyLists::list<uint64_t> LoopifyLists::lookup_all(
    uint64_t key,
    const LoopifyLists::list<std::pair<uint64_t, uint64_t>>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const LoopifyLists::list<std::pair<uint64_t, uint64_t>> *l;
  };

  /// _Resume1: saves [v], resumes after recursive call with _result.
  struct _Resume1 {
    uint64_t v;
  };

  using _Frame = std::variant<_Enter, _Resume1>;
  LoopifyLists::list<uint64_t> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l});
  /// Loopified lookup_all: _Enter -> _Resume1.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const LoopifyLists::list<std::pair<uint64_t, uint64_t>> &l = *_f.l;
      if (std::holds_alternative<
              typename LoopifyLists::list<std::pair<uint64_t, uint64_t>>::Nil>(
              l.v())) {
        _result = list<uint64_t>::nil();
      } else {
        const auto &[a0, a1] = std::get<
            typename LoopifyLists::list<std::pair<uint64_t, uint64_t>>::Cons>(
            l.v());
        const auto &[k, v] = a0;
        if (k == key) {
          _stack.emplace_back(_Resume1{v});
          _stack.emplace_back(_Enter{a1.get()});
        } else {
          _stack.emplace_back(_Enter{a1.get()});
        }
      }
    } else {
      auto _f = std::move(std::get<_Resume1>(_frame));
      _result = list<uint64_t>::cons(_f.v, std::move(_result));
    }
  }
  return _result;
}

/// member x l checks if x is in the list.
bool LoopifyLists::member(uint64_t x, const LoopifyLists::list<uint64_t> &l) {
  const LoopifyLists::list<uint64_t> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<typename LoopifyLists::list<uint64_t>::Nil>(
            _loop_l->v())) {
      return false;
    } else {
      const auto &[a0, a1] =
          std::get<typename LoopifyLists::list<uint64_t>::Cons>(_loop_l->v());
      if (x == a0) {
        return true;
      } else {
        _loop_l = a1.get();
      }
    }
  }
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
      _result = (_f.a0 * std::move(_result));
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
      _result = (_f.a0 + std::move(_result));
    }
  }
  return _result;
}

/// flatten_nested l alternative flatten with different pattern: flattens one
/// level at a time. Pattern:  :: rest -> flatten rest, (x :: xs) :: rest -> x
/// :: flatten (xs :: rest).
LoopifyLists::list<uint64_t> LoopifyLists::flatten_nested_fuel(
    uint64_t fuel,
    const LoopifyLists::list<LoopifyLists::list<uint64_t>>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    LoopifyLists::list<LoopifyLists::list<uint64_t>> l;
    uint64_t fuel;
  };

  /// _Resume_Cons: saves [a00], resumes after recursive call with _result.
  struct _Resume_Cons {
    uint64_t a00;
  };

  using _Frame = std::variant<_Enter, _Resume_Cons>;
  LoopifyLists::list<uint64_t> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{l, fuel});
  /// Loopified flatten_nested_fuel: _Enter -> _Resume_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const LoopifyLists::list<LoopifyLists::list<uint64_t>> &l =
          std::move(_f.l);
      uint64_t fuel = _f.fuel;
      if (fuel <= 0) {
        _result = list<uint64_t>::nil();
      } else {
        uint64_t f = fuel - 1;
        if (std::holds_alternative<
                typename LoopifyLists::list<LoopifyLists::list<uint64_t>>::Nil>(
                l.v())) {
          _result = list<uint64_t>::nil();
        } else {
          const auto &[a0, a1] = std::get<
              typename LoopifyLists::list<LoopifyLists::list<uint64_t>>::Cons>(
              l.v());
          if (std::holds_alternative<
                  typename LoopifyLists::list<uint64_t>::Nil>(a0.v())) {
            _stack.emplace_back(_Enter{*a1, f});
          } else {
            const auto &[a00, a10] =
                std::get<typename LoopifyLists::list<uint64_t>::Cons>(a0.v());
            _stack.emplace_back(_Resume_Cons{a00});
            _stack.emplace_back(
                _Enter{list<LoopifyLists::list<uint64_t>>::cons(*a10, *a1), f});
          }
        }
      }
    } else {
      auto _f = std::move(std::get<_Resume_Cons>(_frame));
      _result = list<uint64_t>::cons(_f.a00, std::move(_result));
    }
  }
  return _result;
}

uint64_t LoopifyLists::sum_list_lengths(
    const LoopifyLists::list<LoopifyLists::list<uint64_t>>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const LoopifyLists::list<LoopifyLists::list<uint64_t>> *l;
  };

  /// _Resume_Cons: saves [a0], resumes after recursive call with _result.
  struct _Resume_Cons {
    std::decay_t<decltype(len_list(
        std::declval<LoopifyLists::list<uint64_t> &>()))>
        a0;
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
      _result = (_f.a0 + std::move(_result));
    }
  }
  return _result;
}

LoopifyLists::list<uint64_t> LoopifyLists::flatten_nested(
    const LoopifyLists::list<LoopifyLists::list<uint64_t>> &l) {
  return flatten_nested_fuel((sum_list_lengths(l) + 1), l);
}

/// compress l removes consecutive duplicates: 1,1,2,2,2,3 -> 1,2,3.
LoopifyLists::list<uint64_t> LoopifyLists::compress(
    const LoopifyLists::list<uint64_t>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const LoopifyLists::list<uint64_t> *l;
  };

  /// _Resume1: saves [a0], resumes after recursive call with _result.
  struct _Resume1 {
    uint64_t a0;
  };

  using _Frame = std::variant<_Enter, _Resume1>;
  LoopifyLists::list<uint64_t> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l});
  /// Loopified compress: _Enter -> _Resume1.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const LoopifyLists::list<uint64_t> &l = *_f.l;
      if (std::holds_alternative<typename LoopifyLists::list<uint64_t>::Nil>(
              l.v())) {
        _result = list<uint64_t>::nil();
      } else {
        const auto &[a0, a1] =
            std::get<typename LoopifyLists::list<uint64_t>::Cons>(l.v());
        auto &&_sv0 = *a1;
        if (std::holds_alternative<typename LoopifyLists::list<uint64_t>::Nil>(
                _sv0.v())) {
          _result = list<uint64_t>::cons(a0, list<uint64_t>::nil());
        } else {
          const auto &[a00, a10] =
              std::get<typename LoopifyLists::list<uint64_t>::Cons>(_sv0.v());
          if (a0 == a00) {
            _stack.emplace_back(_Enter{a1.get()});
          } else {
            _stack.emplace_back(_Resume1{a0});
            _stack.emplace_back(_Enter{a1.get()});
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

/// group_pairs l groups consecutive elements into pairs: 1,2,3,4 ->
/// (1,2),(3,4).
LoopifyLists::list<std::pair<uint64_t, uint64_t>> LoopifyLists::group_pairs(
    const LoopifyLists::list<uint64_t>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const LoopifyLists::list<uint64_t> *l;
  };

  /// _Resume_Cons: saves [_s0], resumes after recursive call with _result.
  struct _Resume_Cons {
    std::decay_t<decltype(std::make_pair(std::declval<uint64_t &>(),
                                         std::declval<uint64_t &>()))>
        _s0;
  };

  using _Frame = std::variant<_Enter, _Resume_Cons>;
  LoopifyLists::list<std::pair<uint64_t, uint64_t>> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l});
  /// Loopified group_pairs: _Enter -> _Resume_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const LoopifyLists::list<uint64_t> &l = *_f.l;
      if (std::holds_alternative<typename LoopifyLists::list<uint64_t>::Nil>(
              l.v())) {
        _result = list<std::pair<uint64_t, uint64_t>>::nil();
      } else {
        const auto &[a0, a1] =
            std::get<typename LoopifyLists::list<uint64_t>::Cons>(l.v());
        auto &&_sv0 = *a1;
        if (std::holds_alternative<typename LoopifyLists::list<uint64_t>::Nil>(
                _sv0.v())) {
          _result = list<std::pair<uint64_t, uint64_t>>::nil();
        } else {
          const auto &[a00, a10] =
              std::get<typename LoopifyLists::list<uint64_t>::Cons>(_sv0.v());
          _stack.emplace_back(_Resume_Cons{std::make_pair(a0, a00)});
          _stack.emplace_back(_Enter{a10.get()});
        }
      }
    } else {
      auto _f = std::move(std::get<_Resume_Cons>(_frame));
      _result =
          list<std::pair<uint64_t, uint64_t>>::cons(_f._s0, std::move(_result));
    }
  }
  return _result;
}

/// swizzle l separates elements by position: 1,2,3,4 -> (1,3,2,4).
std::pair<LoopifyLists::list<uint64_t>, LoopifyLists::list<uint64_t>>
LoopifyLists::swizzle(const LoopifyLists::list<uint64_t> &l) {
  if (std::holds_alternative<typename LoopifyLists::list<uint64_t>::Nil>(
          l.v())) {
    return std::make_pair(list<uint64_t>::nil(), list<uint64_t>::nil());
  } else {
    const auto &[a0, a1] =
        std::get<typename LoopifyLists::list<uint64_t>::Cons>(l.v());
    auto [odds, evens] = swizzle(*a1);
    return std::make_pair(list<uint64_t>::cons(a0, std::move(evens)),
                          std::move(odds));
  }
}

/// index_of_aux x l i finds first index of x in l starting from i.
uint64_t LoopifyLists::index_of_aux(uint64_t x,
                                    const LoopifyLists::list<uint64_t> &l,
                                    uint64_t i) {
  uint64_t _loop_i = std::move(i);
  const LoopifyLists::list<uint64_t> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<typename LoopifyLists::list<uint64_t>::Nil>(
            _loop_l->v())) {
      return UINT64_C(0);
    } else {
      const auto &[a0, a1] =
          std::get<typename LoopifyLists::list<uint64_t>::Cons>(_loop_l->v());
      if (x == a0) {
        return _loop_i;
      } else {
        _loop_i = (_loop_i + 1);
        _loop_l = a1.get();
      }
    }
  }
}

uint64_t LoopifyLists::index_of(uint64_t x,
                                const LoopifyLists::list<uint64_t> &l) {
  return index_of_aux(x, l, UINT64_C(0));
}

/// interleave l1 l2 interleaves two lists: 1,2 3,4 -> 1,3,2,4.
LoopifyLists::list<uint64_t> LoopifyLists::interleave(
    LoopifyLists::list<uint64_t> l1,
    LoopifyLists::list<uint64_t>
        l2) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    LoopifyLists::list<uint64_t> l2;
    LoopifyLists::list<uint64_t> l1;
  };

  /// _Resume_Cons: saves [a0, a00], resumes after recursive call with _result.
  struct _Resume_Cons {
    uint64_t a0;
    uint64_t a00;
  };

  using _Frame = std::variant<_Enter, _Resume_Cons>;
  LoopifyLists::list<uint64_t> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{std::move(l2), std::move(l1)});
  /// Loopified interleave: _Enter -> _Resume_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      LoopifyLists::list<uint64_t> l2 = std::move(_f.l2);
      LoopifyLists::list<uint64_t> l1 = std::move(_f.l1);
      if (std::holds_alternative<typename LoopifyLists::list<uint64_t>::Nil>(
              l1.v_mut())) {
        _result = std::move(l2);
      } else {
        auto &[a0, a1] =
            std::get<typename LoopifyLists::list<uint64_t>::Cons>(l1.v_mut());
        if (std::holds_alternative<typename LoopifyLists::list<uint64_t>::Nil>(
                l2.v_mut())) {
          _result = std::move(l1);
        } else {
          auto &[a00, a10] =
              std::get<typename LoopifyLists::list<uint64_t>::Cons>(l2.v_mut());
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

/// lookup key l finds value for key in association list.
uint64_t LoopifyLists::lookup(
    uint64_t key, const LoopifyLists::list<std::pair<uint64_t, uint64_t>> &l) {
  const LoopifyLists::list<std::pair<uint64_t, uint64_t>> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<
            typename LoopifyLists::list<std::pair<uint64_t, uint64_t>>::Nil>(
            _loop_l->v())) {
      return UINT64_C(0);
    } else {
      const auto &[a0, a1] = std::get<
          typename LoopifyLists::list<std::pair<uint64_t, uint64_t>>::Cons>(
          _loop_l->v());
      const auto &[k, v] = a0;
      if (k == key) {
        return v;
      } else {
        _loop_l = a1.get();
      }
    }
  }
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
  const LoopifyLists::list<uint64_t> *_loop_l = &l;
  LoopifyLists::list<uint64_t> _loop_acc = std::move(acc);
  while (true) {
    if (std::holds_alternative<typename LoopifyLists::list<uint64_t>::Nil>(
            _loop_l->v())) {
      return _loop_acc;
    } else {
      const auto &[a0, a1] =
          std::get<typename LoopifyLists::list<uint64_t>::Cons>(_loop_l->v());
      _loop_l = a1.get();
      _loop_acc = list<uint64_t>::cons(a0, std::move(_loop_acc));
    }
  }
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
    std::decay_t<decltype(list<uint64_t>::nil())> _s0;
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
      _result =
          rev_helper(_f._s0, list<uint64_t>::cons(_f.a0, std::move(_result)));
    }
  }
  return _result;
}

/// Internal helper: append lists.
LoopifyLists::list<uint64_t> LoopifyLists::app_helper(
    const LoopifyLists::list<uint64_t> &l1,
    LoopifyLists::list<uint64_t>
        l2) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    LoopifyLists::list<uint64_t> l2;
    const LoopifyLists::list<uint64_t> *l1;
  };

  /// _Resume_Cons: saves [a0], resumes after recursive call with _result.
  struct _Resume_Cons {
    uint64_t a0;
  };

  using _Frame = std::variant<_Enter, _Resume_Cons>;
  LoopifyLists::list<uint64_t> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{std::move(l2), &l1});
  /// Loopified app_helper: _Enter -> _Resume_Cons.
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
  _stack.emplace_back(_Enter{std::move(l2), &l1});
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
      LoopifyLists::list<uint64_t> rest = std::move(_result);
      _result = list<uint64_t>::cons(a0, app_helper(rest, rest));
    }
  }
  return _result;
}

/// remove_if_sum_even l removes element if sum with next is even.
LoopifyLists::list<uint64_t> LoopifyLists::remove_if_sum_even(
    const LoopifyLists::list<uint64_t>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const LoopifyLists::list<uint64_t> *l;
  };

  /// _Resume1: saves [a0], resumes after recursive call with _result.
  struct _Resume1 {
    uint64_t a0;
  };

  using _Frame = std::variant<_Enter, _Resume1>;
  LoopifyLists::list<uint64_t> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l});
  /// Loopified remove_if_sum_even: _Enter -> _Resume1.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const LoopifyLists::list<uint64_t> &l = *_f.l;
      if (std::holds_alternative<typename LoopifyLists::list<uint64_t>::Nil>(
              l.v())) {
        _result = list<uint64_t>::nil();
      } else {
        const auto &[a0, a1] =
            std::get<typename LoopifyLists::list<uint64_t>::Cons>(l.v());
        auto &&_sv0 = *a1;
        if (std::holds_alternative<typename LoopifyLists::list<uint64_t>::Nil>(
                _sv0.v())) {
          _result = list<uint64_t>::cons(a0, list<uint64_t>::nil());
        } else {
          const auto &[a00, a10] =
              std::get<typename LoopifyLists::list<uint64_t>::Cons>(_sv0.v());
          if ((UINT64_C(2) ? (a0 + a00) % UINT64_C(2) : (a0 + a00)) ==
              UINT64_C(0)) {
            _stack.emplace_back(_Enter{a1.get()});
          } else {
            _stack.emplace_back(_Resume1{a0});
            _stack.emplace_back(_Enter{a1.get()});
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

/// split_at n l splits list at index n into (prefix, suffix).
std::pair<LoopifyLists::list<uint64_t>, LoopifyLists::list<uint64_t>>
LoopifyLists::split_at(uint64_t n, LoopifyLists::list<uint64_t> l) {
  if (std::holds_alternative<typename LoopifyLists::list<uint64_t>::Nil>(
          l.v_mut())) {
    return std::make_pair(list<uint64_t>::nil(), list<uint64_t>::nil());
  } else {
    auto &[a0, a1] =
        std::get<typename LoopifyLists::list<uint64_t>::Cons>(l.v_mut());
    if (n == UINT64_C(0)) {
      return std::make_pair(list<uint64_t>::nil(), l);
    } else {
      auto [a, b] =
          split_at((((n - UINT64_C(1)) > n ? 0 : (n - UINT64_C(1)))), *a1);
      return std::make_pair(list<uint64_t>::cons(std::move(a0), std::move(a)),
                            std::move(b));
    }
  }
}

/// unzip l splits list of pairs into two lists.
std::pair<LoopifyLists::list<uint64_t>, LoopifyLists::list<uint64_t>>
LoopifyLists::unzip(
    const LoopifyLists::list<std::pair<uint64_t, uint64_t>> &l) {
  if (std::holds_alternative<
          typename LoopifyLists::list<std::pair<uint64_t, uint64_t>>::Nil>(
          l.v())) {
    return std::make_pair(list<uint64_t>::nil(), list<uint64_t>::nil());
  } else {
    const auto &[a0, a1] = std::get<
        typename LoopifyLists::list<std::pair<uint64_t, uint64_t>>::Cons>(
        l.v());
    const auto &[a, b] = a0;
    auto [xs, ys] = unzip(*a1);
    return std::make_pair(list<uint64_t>::cons(a, std::move(xs)),
                          list<uint64_t>::cons(b, std::move(ys)));
  }
}

/// nth n l default returns nth element or default if out of bounds.
uint64_t LoopifyLists::nth(uint64_t n, const LoopifyLists::list<uint64_t> &l,
                           uint64_t default0) {
  const LoopifyLists::list<uint64_t> *_loop_l = &l;
  uint64_t _loop_n = std::move(n);
  while (true) {
    if (std::holds_alternative<typename LoopifyLists::list<uint64_t>::Nil>(
            _loop_l->v())) {
      return default0;
    } else {
      const auto &[a0, a1] =
          std::get<typename LoopifyLists::list<uint64_t>::Cons>(_loop_l->v());
      if (_loop_n == UINT64_C(0)) {
        return a0;
      } else {
        _loop_l = a1.get();
        _loop_n =
            (((_loop_n - UINT64_C(1)) > _loop_n ? 0 : (_loop_n - UINT64_C(1))));
      }
    }
  }
}

/// last l default returns last element or default if empty.
uint64_t LoopifyLists::last(const LoopifyLists::list<uint64_t> &l,
                            uint64_t default0) {
  const LoopifyLists::list<uint64_t> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<typename LoopifyLists::list<uint64_t>::Nil>(
            _loop_l->v())) {
      return default0;
    } else {
      const auto &[a0, a1] =
          std::get<typename LoopifyLists::list<uint64_t>::Cons>(_loop_l->v());
      auto &&_sv = *a1;
      if (std::holds_alternative<typename LoopifyLists::list<uint64_t>::Nil>(
              _sv.v())) {
        return a0;
      } else {
        _loop_l = a1.get();
      }
    }
  }
}

/// drop n l drops first n elements.
LoopifyLists::list<uint64_t>
LoopifyLists::drop(uint64_t n, LoopifyLists::list<uint64_t> l) {
  LoopifyLists::list<uint64_t> _loop_l = std::move(l);
  uint64_t _loop_n = std::move(n);
  while (true) {
    if (std::holds_alternative<typename LoopifyLists::list<uint64_t>::Nil>(
            _loop_l.v_mut())) {
      return list<uint64_t>::nil();
    } else {
      auto &[a0, a1] = std::get<typename LoopifyLists::list<uint64_t>::Cons>(
          _loop_l.v_mut());
      if (_loop_n == UINT64_C(0)) {
        return _loop_l;
      } else {
        _loop_l = *a1;
        _loop_n =
            (((_loop_n - UINT64_C(1)) > _loop_n ? 0 : (_loop_n - UINT64_C(1))));
      }
    }
  }
}

/// init l returns all but last element.
LoopifyLists::list<uint64_t> LoopifyLists::init(
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
  LoopifyLists::list<uint64_t> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l});
  /// Loopified init: _Enter -> _Resume_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const LoopifyLists::list<uint64_t> &l = *_f.l;
      if (std::holds_alternative<typename LoopifyLists::list<uint64_t>::Nil>(
              l.v())) {
        _result = list<uint64_t>::nil();
      } else {
        const auto &[a0, a1] =
            std::get<typename LoopifyLists::list<uint64_t>::Cons>(l.v());
        auto &&_sv = *a1;
        if (std::holds_alternative<typename LoopifyLists::list<uint64_t>::Nil>(
                _sv.v())) {
          _result = list<uint64_t>::nil();
        } else {
          _stack.emplace_back(_Resume_Cons{a0});
          _stack.emplace_back(_Enter{a1.get()});
        }
      }
    } else {
      auto _f = std::move(std::get<_Resume_Cons>(_frame));
      _result = list<uint64_t>::cons(_f.a0, std::move(_result));
    }
  }
  return _result;
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
      _result = (std::move(_result) + 1);
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
      uint64_t max_rest = std::move(_result);
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
std::pair<uint64_t, uint64_t>
LoopifyLists::minmax(const LoopifyLists::list<uint64_t> &l) {
  if (std::holds_alternative<typename LoopifyLists::list<uint64_t>::Nil>(
          l.v())) {
    return std::make_pair(UINT64_C(0), UINT64_C(0));
  } else {
    const auto &[a0, a1] =
        std::get<typename LoopifyLists::list<uint64_t>::Cons>(l.v());
    auto &&_sv = *a1;
    if (std::holds_alternative<typename LoopifyLists::list<uint64_t>::Nil>(
            _sv.v())) {
      return std::make_pair(a0, a0);
    } else {
      auto [lo, hi] = minmax(*a1);
      return std::make_pair((a0 <= lo ? a0 : lo), (hi <= a0 ? a0 : hi));
    }
  }
}

/// Helper for rotate_left.
LoopifyLists::list<uint64_t>
LoopifyLists::rotate_left_fuel(uint64_t fuel, uint64_t n,
                               LoopifyLists::list<uint64_t> l) {
  LoopifyLists::list<uint64_t> _loop_l = std::move(l);
  uint64_t _loop_n = std::move(n);
  uint64_t _loop_fuel = std::move(fuel);
  while (true) {
    if (_loop_fuel <= 0) {
      return _loop_l;
    } else {
      uint64_t f = _loop_fuel - 1;
      if (_loop_n == UINT64_C(0)) {
        return _loop_l;
      } else {
        if (std::holds_alternative<typename LoopifyLists::list<uint64_t>::Nil>(
                _loop_l.v_mut())) {
          return list<uint64_t>::nil();
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

  /// _Resume_Cons: saves [a0], resumes after recursive call with _result.
  struct _Resume_Cons {
    LoopifyLists::list<uint64_t> a0;
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
          _stack.emplace_back(_Resume_Cons{a0});
          _stack.emplace_back(_Enter{a1.get()});
        }
      }
    } else {
      auto _f = std::move(std::get<_Resume_Cons>(_frame));
      _result =
          app_helper(std::move(_f.a0), app_helper(sep, std::move(_result)));
    }
  }
  return _result;
}

/// majority l finds majority element using Boyer-Moore voting algorithm.
/// Returns (candidate, count).
std::pair<uint64_t, uint64_t>
LoopifyLists::majority(const LoopifyLists::list<uint64_t> &l) {
  if (std::holds_alternative<typename LoopifyLists::list<uint64_t>::Nil>(
          l.v())) {
    return std::make_pair(UINT64_C(0), UINT64_C(0));
  } else {
    const auto &[a0, a1] =
        std::get<typename LoopifyLists::list<uint64_t>::Cons>(l.v());
    auto &&_sv = *a1;
    if (std::holds_alternative<typename LoopifyLists::list<uint64_t>::Nil>(
            _sv.v())) {
      return std::make_pair(a0, UINT64_C(1));
    } else {
      auto [cand, cnt] = majority(*a1);
      if (a0 == cand) {
        return std::make_pair(cand, (cnt + 1));
      } else {
        if (cnt == UINT64_C(0)) {
          return std::make_pair(a0, UINT64_C(1));
        } else {
          return std::make_pair(
              cand, (((cnt - UINT64_C(1)) > cnt ? 0 : (cnt - UINT64_C(1)))));
        }
      }
    }
  }
}

/// zip3 l1 l2 l3 zips three lists into triples.
LoopifyLists::list<std::pair<std::pair<uint64_t, uint64_t>, uint64_t>>
LoopifyLists::zip3(
    const LoopifyLists::list<uint64_t> &l1,
    const LoopifyLists::list<uint64_t> &l2,
    const LoopifyLists::list<uint64_t>
        &l3) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const LoopifyLists::list<uint64_t> *l3;
    const LoopifyLists::list<uint64_t> *l2;
    const LoopifyLists::list<uint64_t> *l1;
  };

  /// _Resume_Cons: saves [_s0], resumes after recursive call with _result.
  struct _Resume_Cons {
    std::decay_t<decltype(std::make_pair(
        std::make_pair(std::declval<uint64_t &>(), std::declval<uint64_t &>()),
        std::declval<uint64_t &>()))>
        _s0;
  };

  using _Frame = std::variant<_Enter, _Resume_Cons>;
  LoopifyLists::list<std::pair<std::pair<uint64_t, uint64_t>, uint64_t>>
      _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l3, &l2, &l1});
  /// Loopified zip3: _Enter -> _Resume_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const LoopifyLists::list<uint64_t> &l3 = *_f.l3;
      const LoopifyLists::list<uint64_t> &l2 = *_f.l2;
      const LoopifyLists::list<uint64_t> &l1 = *_f.l1;
      if (std::holds_alternative<typename LoopifyLists::list<uint64_t>::Nil>(
              l1.v())) {
        _result =
            list<std::pair<std::pair<uint64_t, uint64_t>, uint64_t>>::nil();
      } else {
        const auto &[a0, a1] =
            std::get<typename LoopifyLists::list<uint64_t>::Cons>(l1.v());
        if (std::holds_alternative<typename LoopifyLists::list<uint64_t>::Nil>(
                l2.v())) {
          _result =
              list<std::pair<std::pair<uint64_t, uint64_t>, uint64_t>>::nil();
        } else {
          const auto &[a00, a10] =
              std::get<typename LoopifyLists::list<uint64_t>::Cons>(l2.v());
          if (std::holds_alternative<
                  typename LoopifyLists::list<uint64_t>::Nil>(l3.v())) {
            _result =
                list<std::pair<std::pair<uint64_t, uint64_t>, uint64_t>>::nil();
          } else {
            const auto &[a01, a11] =
                std::get<typename LoopifyLists::list<uint64_t>::Cons>(l3.v());
            _stack.emplace_back(
                _Resume_Cons{std::make_pair(std::make_pair(a0, a00), a01)});
            _stack.emplace_back(_Enter{a11.get(), a10.get(), a1.get()});
          }
        }
      }
    } else {
      auto _f = std::move(std::get<_Resume_Cons>(_frame));
      _result = list<std::pair<std::pair<uint64_t, uint64_t>, uint64_t>>::cons(
          _f._s0, std::move(_result));
    }
  }
  return _result;
}

/// sum_and_count l returns both sum and count in one pass.
std::pair<uint64_t, uint64_t>
LoopifyLists::sum_and_count(const LoopifyLists::list<uint64_t> &l) {
  if (std::holds_alternative<typename LoopifyLists::list<uint64_t>::Nil>(
          l.v())) {
    return std::make_pair(UINT64_C(0), UINT64_C(0));
  } else {
    const auto &[a0, a1] =
        std::get<typename LoopifyLists::list<uint64_t>::Cons>(l.v());
    auto [s, c] = sum_and_count(*a1);
    return std::make_pair((a0 + s), (c + 1));
  }
}

/// elem_at n l returns element at index n (like nth but with different name).
std::optional<uint64_t>
LoopifyLists::elem_at(uint64_t n, const LoopifyLists::list<uint64_t> &l) {
  const LoopifyLists::list<uint64_t> *_loop_l = &l;
  uint64_t _loop_n = std::move(n);
  while (true) {
    if (std::holds_alternative<typename LoopifyLists::list<uint64_t>::Nil>(
            _loop_l->v())) {
      return std::optional<uint64_t>();
    } else {
      const auto &[a0, a1] =
          std::get<typename LoopifyLists::list<uint64_t>::Cons>(_loop_l->v());
      if (_loop_n == UINT64_C(0)) {
        return std::make_optional<uint64_t>(a0);
      } else {
        _loop_l = a1.get();
        _loop_n =
            (((_loop_n - UINT64_C(1)) > _loop_n ? 0 : (_loop_n - UINT64_C(1))));
      }
    }
  }
}
