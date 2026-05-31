#include "loopify_algorithms.h"

/// Consolidated UNIQUE list/sequence algorithms.
uint64_t LoopifyAlgorithms::len_impl(
    const List<uint64_t>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<uint64_t> *l;
  };

  /// _Resume_Cons: resumes after recursive call with _result.
  struct _Resume_Cons {};

  using _Frame = std::variant<_Enter, _Resume_Cons>;
  uint64_t _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l});
  /// Loopified len_impl: _Enter -> _Resume_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<uint64_t> &l = *_f.l;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
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

/// sieve l Sieve of Eratosthenes - filters out multiples.
List<uint64_t> LoopifyAlgorithms::sieve_fuel(
    uint64_t fuel,
    List<uint64_t>
        l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    List<uint64_t> l;
    uint64_t fuel;
  };

  /// _Resume_Cons: saves [a0], resumes after recursive call with _result.
  struct _Resume_Cons {
    uint64_t a0;
  };

  using _Frame = std::variant<_Enter, _Resume_Cons>;
  List<uint64_t> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{std::move(l), fuel});
  /// Loopified sieve_fuel: _Enter -> _Resume_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      List<uint64_t> l = std::move(_f.l);
      uint64_t fuel = _f.fuel;
      if (fuel <= 0) {
        _result = std::move(l);
      } else {
        uint64_t f = fuel - 1;
        if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v_mut())) {
          _result = List<uint64_t>::nil();
        } else {
          auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v_mut());
          auto filter_multiples_impl =
              [](auto &_self_filter_multiples, uint64_t p,
                 const List<uint64_t> &rest) -> List<uint64_t> {
            if (std::holds_alternative<typename List<uint64_t>::Nil>(
                    rest.v())) {
              return List<uint64_t>::nil();
            } else {
              const auto &[a00, a10] =
                  std::get<typename List<uint64_t>::Cons>(rest.v());
              if ((p ? a00 % p : a00) == UINT64_C(0)) {
                return _self_filter_multiples(_self_filter_multiples, p, *a10);
              } else {
                return List<uint64_t>::cons(
                    a00,
                    _self_filter_multiples(_self_filter_multiples, p, *a10));
              }
            }
          };
          auto filter_multiples =
              [&](uint64_t p, const List<uint64_t> &rest) -> List<uint64_t> {
            return filter_multiples_impl(filter_multiples_impl, p, rest);
          };
          _stack.emplace_back(_Resume_Cons{a0});
          _stack.emplace_back(_Enter{filter_multiples(a0, *a1), f});
        }
      }
    } else {
      auto _f = std::move(std::get<_Resume_Cons>(_frame));
      _result = List<uint64_t>::cons(_f.a0, std::move(_result));
    }
  }
  return _result;
}

List<uint64_t> LoopifyAlgorithms::sieve(const List<uint64_t> &l) {
  return sieve_fuel(len_impl(l), l);
}

/// run_length_encode l encodes consecutive runs: 1,1,2,3,3,3 ->
/// (1,2),(2,1),(3,3).
List<std::pair<uint64_t, uint64_t>>
LoopifyAlgorithms::run_length_encode(const List<uint64_t> &l) {
  if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
    return List<std::pair<uint64_t, uint64_t>>::nil();
  } else {
    const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
    auto &&_sv0 = run_length_encode(*a1);
    if (std::holds_alternative<
            typename List<std::pair<uint64_t, uint64_t>>::Nil>(_sv0.v())) {
      return List<std::pair<uint64_t, uint64_t>>::cons(
          std::make_pair(a0, UINT64_C(1)),
          List<std::pair<uint64_t, uint64_t>>::nil());
    } else {
      const auto &[a00, a10] =
          std::get<typename List<std::pair<uint64_t, uint64_t>>::Cons>(
              _sv0.v());
      const uint64_t &y = a00.first;
      const uint64_t &n = a00.second;
      if (a0 == y) {
        return List<std::pair<uint64_t, uint64_t>>::cons(
            std::make_pair(y, (n + 1)), *a10);
      } else {
        return List<std::pair<uint64_t, uint64_t>>::cons(
            std::make_pair(a0, UINT64_C(1)),
            List<std::pair<uint64_t, uint64_t>>::cons(std::make_pair(y, n),
                                                      *a10));
      }
    }
  }
}

/// prefix_sums acc l cumulative sums: 1,2,3 with acc=0 -> 0,1,3,6.
List<uint64_t> LoopifyAlgorithms::prefix_sums(
    uint64_t acc,
    const List<uint64_t>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<uint64_t> *l;
    uint64_t acc;
  };

  /// _Resume_Cons: saves [acc], resumes after recursive call with _result.
  struct _Resume_Cons {
    uint64_t acc;
  };

  using _Frame = std::variant<_Enter, _Resume_Cons>;
  List<uint64_t> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l, acc});
  /// Loopified prefix_sums: _Enter -> _Resume_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<uint64_t> &l = *_f.l;
      uint64_t acc = _f.acc;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
        _result = List<uint64_t>::cons(acc, List<uint64_t>::nil());
      } else {
        const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
        _stack.emplace_back(_Resume_Cons{acc});
        _stack.emplace_back(_Enter{a1.get(), (acc + a0)});
      }
    } else {
      auto _f = std::move(std::get<_Resume_Cons>(_frame));
      _result = List<uint64_t>::cons(_f.acc, std::move(_result));
    }
  }
  return _result;
}

/// differences l consecutive differences: 5,3,8,2 -> -2,5,-6.
List<uint64_t> LoopifyAlgorithms::differences(
    const List<uint64_t>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<uint64_t> *l;
  };

  /// _Resume_Cons: saves [_s0], resumes after recursive call with _result.
  struct _Resume_Cons {
    std::decay_t<decltype((
        ((std::declval<uint64_t &>() - std::declval<uint64_t &>()) >
                 std::declval<uint64_t &>()
             ? 0
             : (std::declval<uint64_t &>() - std::declval<uint64_t &>()))))>
        _s0;
  };

  using _Frame = std::variant<_Enter, _Resume_Cons>;
  List<uint64_t> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l});
  /// Loopified differences: _Enter -> _Resume_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<uint64_t> &l = *_f.l;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
        _result = List<uint64_t>::nil();
      } else {
        const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
        auto &&_sv0 = *a1;
        if (std::holds_alternative<typename List<uint64_t>::Nil>(_sv0.v())) {
          _result = List<uint64_t>::nil();
        } else {
          const auto &[a00, a10] =
              std::get<typename List<uint64_t>::Cons>(_sv0.v());
          _stack.emplace_back(
              _Resume_Cons{(((a00 - a0) > a00 ? 0 : (a00 - a0)))});
          _stack.emplace_back(_Enter{a1.get()});
        }
      }
    } else {
      auto _f = std::move(std::get<_Resume_Cons>(_frame));
      _result = List<uint64_t>::cons(_f._s0, std::move(_result));
    }
  }
  return _result;
}

/// rotate_left n l rotates list left by n positions.
List<uint64_t> LoopifyAlgorithms::rotate_left_fuel(uint64_t fuel, uint64_t n,
                                                   List<uint64_t> l) {
  List<uint64_t> _loop_l = std::move(l);
  uint64_t _loop_n = std::move(n);
  uint64_t _loop_fuel = std::move(fuel);
  while (true) {
    if (_loop_fuel <= 0) {
      return _loop_l;
    } else {
      uint64_t f = _loop_fuel - 1;
      if (_loop_n <= UINT64_C(0)) {
        return _loop_l;
      } else {
        if (std::holds_alternative<typename List<uint64_t>::Nil>(
                _loop_l.v_mut())) {
          return List<uint64_t>::nil();
        } else {
          auto &[a0, a1] =
              std::get<typename List<uint64_t>::Cons>(_loop_l.v_mut());
          _loop_l = a1->app(
              List<uint64_t>::cons(std::move(a0), List<uint64_t>::nil()));
          _loop_n = ((
              (_loop_n - UINT64_C(1)) > _loop_n ? 0 : (_loop_n - UINT64_C(1))));
          _loop_fuel = f;
        }
      }
    }
  }
}

List<uint64_t> LoopifyAlgorithms::rotate_left(uint64_t n,
                                              const List<uint64_t> &l) {
  return rotate_left_fuel(n, n, l);
}

/// nub l removes ALL duplicates (not just consecutive): 1,2,1,3,2 -> 1,2,3.
List<uint64_t> LoopifyAlgorithms::nub_aux(
    const List<uint64_t> &l,
    uint64_t
        fuel) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    uint64_t fuel;
    List<uint64_t> l;
  };

  /// _Resume_Cons: saves [a0], resumes after recursive call with _result.
  struct _Resume_Cons {
    uint64_t a0;
  };

  using _Frame = std::variant<_Enter, _Resume_Cons>;
  List<uint64_t> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{fuel, l});
  /// Loopified nub_aux: _Enter -> _Resume_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      uint64_t fuel = _f.fuel;
      const List<uint64_t> &l = std::move(_f.l);
      if (fuel <= 0) {
        _result = List<uint64_t>::nil();
      } else {
        uint64_t f = fuel - 1;
        if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
          _result = List<uint64_t>::nil();
        } else {
          const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
          auto filter_out_impl =
              [](auto &_self_filter_out, uint64_t val,
                 const List<uint64_t> &rest) -> List<uint64_t> {
            if (std::holds_alternative<typename List<uint64_t>::Nil>(
                    rest.v())) {
              return List<uint64_t>::nil();
            } else {
              const auto &[a00, a10] =
                  std::get<typename List<uint64_t>::Cons>(rest.v());
              if (val == a00) {
                return _self_filter_out(_self_filter_out, val, *a10);
              } else {
                return List<uint64_t>::cons(
                    a00, _self_filter_out(_self_filter_out, val, *a10));
              }
            }
          };
          auto filter_out = [&](uint64_t val,
                                const List<uint64_t> &rest) -> List<uint64_t> {
            return filter_out_impl(filter_out_impl, val, rest);
          };
          _stack.emplace_back(_Resume_Cons{a0});
          _stack.emplace_back(_Enter{f, filter_out(a0, *a1)});
        }
      }
    } else {
      auto _f = std::move(std::get<_Resume_Cons>(_frame));
      _result = List<uint64_t>::cons(_f.a0, std::move(_result));
    }
  }
  return _result;
}

List<uint64_t> LoopifyAlgorithms::nub(const List<uint64_t> &l) {
  return nub_aux(l, len_impl(l));
}

/// Internal helpers for palindrome check.
List<uint64_t> LoopifyAlgorithms::rev_impl(List<uint64_t> acc,
                                           const List<uint64_t> &l) {
  const List<uint64_t> *_loop_l = &l;
  List<uint64_t> _loop_acc = std::move(acc);
  while (true) {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l->v())) {
      return _loop_acc;
    } else {
      const auto &[a0, a1] =
          std::get<typename List<uint64_t>::Cons>(_loop_l->v());
      _loop_l = a1.get();
      _loop_acc = List<uint64_t>::cons(a0, std::move(_loop_acc));
    }
  }
}

bool LoopifyAlgorithms::list_eq_impl(const List<uint64_t> &l1,
                                     const List<uint64_t> &l2) {
  const List<uint64_t> *_loop_l2 = &l2;
  const List<uint64_t> *_loop_l1 = &l1;
  while (true) {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l1->v())) {
      if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l2->v())) {
        return true;
      } else {
        return false;
      }
    } else {
      const auto &[a0, a1] =
          std::get<typename List<uint64_t>::Cons>(_loop_l1->v());
      if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l2->v())) {
        return false;
      } else {
        const auto &[a00, a10] =
            std::get<typename List<uint64_t>::Cons>(_loop_l2->v());
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

/// is_palindrome l checks if list reads same forwards and backwards.
bool LoopifyAlgorithms::is_palindrome(const List<uint64_t> &l) {
  return list_eq_impl(l, rev_impl(List<uint64_t>::nil(), l));
}

/// windows n l sliding windows of size n: windows 2 1,2,3,4 ->
/// [1,2],[2,3],[3,4].
List<uint64_t> LoopifyAlgorithms::take_impl(
    uint64_t k,
    const List<uint64_t>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<uint64_t> *l;
    uint64_t k;
  };

  /// _Resume_Cons: saves [a0], resumes after recursive call with _result.
  struct _Resume_Cons {
    uint64_t a0;
  };

  using _Frame = std::variant<_Enter, _Resume_Cons>;
  List<uint64_t> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l, k});
  /// Loopified take_impl: _Enter -> _Resume_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<uint64_t> &l = *_f.l;
      uint64_t k = _f.k;
      if (k <= 0) {
        _result = List<uint64_t>::nil();
      } else {
        uint64_t m = k - 1;
        if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
          _result = List<uint64_t>::nil();
        } else {
          const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
          _stack.emplace_back(_Resume_Cons{a0});
          _stack.emplace_back(_Enter{a1.get(), m});
        }
      }
    } else {
      auto _f = std::move(std::get<_Resume_Cons>(_frame));
      _result = List<uint64_t>::cons(_f.a0, std::move(_result));
    }
  }
  return _result;
}

List<List<uint64_t>> LoopifyAlgorithms::windows_aux(
    uint64_t n, const List<uint64_t> &l,
    uint64_t
        fuel) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    uint64_t fuel;
    const List<uint64_t> *l;
  };

  /// _Resume1: saves [_s0], resumes after recursive call with _result.
  struct _Resume1 {
    std::decay_t<decltype(take_impl(std::declval<uint64_t &>(),
                                    std::declval<const List<uint64_t> &>()))>
        _s0;
  };

  using _Frame = std::variant<_Enter, _Resume1>;
  List<List<uint64_t>> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{fuel, &l});
  /// Loopified windows_aux: _Enter -> _Resume1.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      uint64_t fuel = _f.fuel;
      const List<uint64_t> &l = *_f.l;
      if (fuel <= 0) {
        _result = List<List<uint64_t>>::nil();
      } else {
        uint64_t f = fuel - 1;
        if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
          _result = List<List<uint64_t>>::nil();
        } else {
          const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
          if (len_impl(l) < n) {
            _result = List<List<uint64_t>>::nil();
          } else {
            _stack.emplace_back(_Resume1{take_impl(n, l)});
            _stack.emplace_back(_Enter{f, a1.get()});
          }
        }
      }
    } else {
      auto _f = std::move(std::get<_Resume1>(_frame));
      _result = List<List<uint64_t>>::cons(_f._s0, std::move(_result));
    }
  }
  return _result;
}

List<List<uint64_t>> LoopifyAlgorithms::windows(uint64_t n,
                                                const List<uint64_t> &l) {
  return windows_aux(n, l, (len_impl(l) + 1));
}

/// sliding_pairs l returns consecutive pairs: 1,2,3,4 -> (1,2),(2,3),(3,4).
List<std::pair<uint64_t, uint64_t>> LoopifyAlgorithms::sliding_pairs(
    const List<uint64_t>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<uint64_t> *l;
  };

  /// _Resume_Cons: saves [_s0], resumes after recursive call with _result.
  struct _Resume_Cons {
    std::decay_t<decltype(std::make_pair(std::declval<uint64_t &>(),
                                         std::declval<uint64_t &>()))>
        _s0;
  };

  using _Frame = std::variant<_Enter, _Resume_Cons>;
  List<std::pair<uint64_t, uint64_t>> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l});
  /// Loopified sliding_pairs: _Enter -> _Resume_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<uint64_t> &l = *_f.l;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
        _result = List<std::pair<uint64_t, uint64_t>>::nil();
      } else {
        const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
        auto &&_sv0 = *a1;
        if (std::holds_alternative<typename List<uint64_t>::Nil>(_sv0.v())) {
          _result = List<std::pair<uint64_t, uint64_t>>::nil();
        } else {
          const auto &[a00, a10] =
              std::get<typename List<uint64_t>::Cons>(_sv0.v());
          _stack.emplace_back(_Resume_Cons{std::make_pair(a0, a00)});
          _stack.emplace_back(_Enter{a1.get()});
        }
      }
    } else {
      auto _f = std::move(std::get<_Resume_Cons>(_frame));
      _result =
          List<std::pair<uint64_t, uint64_t>>::cons(_f._s0, std::move(_result));
    }
  }
  return _result;
}

/// max_prefix_sum l maximum sum of prefix (Kadane-like pattern).
uint64_t LoopifyAlgorithms::max_prefix_sum(
    const List<uint64_t>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<uint64_t> *l;
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
      const List<uint64_t> &l = *_f.l;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
        _stack.emplace_back(_Cont_Cons{a0});
        _stack.emplace_back(_Enter{a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Cont_Cons>(_frame));
      uint64_t a0 = _f.a0;
      uint64_t rest = std::move(_result);
      uint64_t sum = (a0 + rest);
      if (rest == UINT64_C(0)) {
        _result = UINT64_C(0);
      } else {
        if (rest < sum) {
          _result = std::move(sum);
        } else {
          _result = std::move(rest);
        }
      }
    }
  }
  return _result;
}

/// weighted_sum i l computes weighted sum with increasing index.
uint64_t LoopifyAlgorithms::weighted_sum(
    uint64_t i,
    const List<uint64_t>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<uint64_t> *l;
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
      const List<uint64_t> &l = *_f.l;
      uint64_t i = _f.i;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
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

/// step_sum l sums with conditional doubling for odd numbers.
uint64_t LoopifyAlgorithms::step_sum(
    const List<uint64_t>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<uint64_t> *l;
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
      const List<uint64_t> &l = *_f.l;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
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

/// Helper: get head with default value.
uint64_t LoopifyAlgorithms::head_nat(uint64_t d, const List<uint64_t> &l) {
  if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
    return d;
  } else {
    const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
    return a0;
  }
}

/// suffix_sums l computes suffix sums (reverse of prefix sums).
List<uint64_t> LoopifyAlgorithms::suffix_sums(
    const List<uint64_t>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<uint64_t> *l;
  };

  /// _Cont_Cons: saves [a0], resumes after recursive call, then processes rest.
  struct _Cont_Cons {
    uint64_t a0;
  };

  using _Frame = std::variant<_Enter, _Cont_Cons>;
  List<uint64_t> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l});
  /// Loopified suffix_sums: _Enter -> _Cont_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<uint64_t> &l = *_f.l;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
        _result = List<uint64_t>::nil();
      } else {
        const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
        _stack.emplace_back(_Cont_Cons{a0});
        _stack.emplace_back(_Enter{a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Cont_Cons>(_frame));
      uint64_t a0 = _f.a0;
      List<uint64_t> rest = std::move(_result);
      _result = List<uint64_t>::cons((a0 + head_nat(UINT64_C(0), rest)), rest);
    }
  }
  return _result;
}
