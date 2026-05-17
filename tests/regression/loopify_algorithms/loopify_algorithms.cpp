#include "loopify_algorithms.h"

/// Consolidated UNIQUE list/sequence algorithms.
unsigned int LoopifyAlgorithms::len_impl(
    const List<unsigned int>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<unsigned int> *l;
  };

  /// _Resume_Cons: resumes after recursive call with _result.
  struct _Resume_Cons {};

  using _Frame = std::variant<_Enter, _Resume_Cons>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l});
  /// Loopified len_impl: _Enter -> _Resume_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<unsigned int> &l = *_f.l;
      if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
        _result = 0u;
      } else {
        const auto &[a0, a1] =
            std::get<typename List<unsigned int>::Cons>(l.v());
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

/// sieve l Sieve of Eratosthenes - filters out multiples.
List<unsigned int> LoopifyAlgorithms::sieve_fuel(unsigned int fuel,
                                                 List<unsigned int> l) {
  std::unique_ptr<List<unsigned int>> _head{};
  std::unique_ptr<List<unsigned int>> *_write = &_head;
  List<unsigned int> _loop_l = std::move(l);
  unsigned int _loop_fuel = std::move(fuel);
  while (true) {
    if (_loop_fuel <= 0) {
      *_write = std::make_unique<List<unsigned int>>(std::move(_loop_l));
      break;
    } else {
      unsigned int f = _loop_fuel - 1;
      if (std::holds_alternative<typename List<unsigned int>::Nil>(
              _loop_l.v_mut())) {
        *_write =
            std::make_unique<List<unsigned int>>(List<unsigned int>::nil());
        break;
      } else {
        auto &[a0, a1] =
            std::get<typename List<unsigned int>::Cons>(_loop_l.v_mut());
        auto filter_multiples_impl =
            [](auto &_self_filter_multiples, unsigned int p,
               const List<unsigned int> &rest) -> List<unsigned int> {
          if (std::holds_alternative<typename List<unsigned int>::Nil>(
                  rest.v())) {
            return List<unsigned int>::nil();
          } else {
            const auto &[a00, a10] =
                std::get<typename List<unsigned int>::Cons>(rest.v());
            if ((p ? a00 % p : a00) == 0u) {
              return _self_filter_multiples(_self_filter_multiples, p, *a10);
            } else {
              return List<unsigned int>::cons(
                  a00, _self_filter_multiples(_self_filter_multiples, p, *a10));
            }
          }
        };
        auto filter_multiples =
            [&](unsigned int p,
                const List<unsigned int> &rest) -> List<unsigned int> {
          return filter_multiples_impl(filter_multiples_impl, p, rest);
        };
        auto _cell = std::make_unique<List<unsigned int>>(
            typename List<unsigned int>::Cons(a0, nullptr));
        *_write = std::move(_cell);
        _write =
            &std::get<typename List<unsigned int>::Cons>((*_write)->v_mut()).a1;
        _loop_l = filter_multiples(a0, *a1);
        _loop_fuel = f;
        continue;
      }
    }
  }
  return std::move(*_head);
}

List<unsigned int> LoopifyAlgorithms::sieve(const List<unsigned int> &l) {
  return sieve_fuel(len_impl(l), l);
}

/// run_length_encode l encodes consecutive runs: 1,1,2,3,3,3 ->
/// (1,2),(2,1),(3,3).
List<std::pair<unsigned int, unsigned int>>
LoopifyAlgorithms::run_length_encode(const List<unsigned int> &l) {
  if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
    return List<std::pair<unsigned int, unsigned int>>::nil();
  } else {
    const auto &[a0, a1] = std::get<typename List<unsigned int>::Cons>(l.v());
    auto &&_sv0 = run_length_encode(*a1);
    if (std::holds_alternative<
            typename List<std::pair<unsigned int, unsigned int>>::Nil>(
            _sv0.v())) {
      return List<std::pair<unsigned int, unsigned int>>::cons(
          std::make_pair(a0, 1u),
          List<std::pair<unsigned int, unsigned int>>::nil());
    } else {
      const auto &[a00, a10] =
          std::get<typename List<std::pair<unsigned int, unsigned int>>::Cons>(
              _sv0.v());
      const unsigned int &y = a00.first;
      const unsigned int &n = a00.second;
      if (a0 == y) {
        return List<std::pair<unsigned int, unsigned int>>::cons(
            std::make_pair(y, (n + 1)), *a10);
      } else {
        return List<std::pair<unsigned int, unsigned int>>::cons(
            std::make_pair(a0, 1u),
            List<std::pair<unsigned int, unsigned int>>::cons(
                std::make_pair(y, n), *a10));
      }
    }
  }
}

/// prefix_sums acc l cumulative sums: 1,2,3 with acc=0 -> 0,1,3,6.
List<unsigned int> LoopifyAlgorithms::prefix_sums(unsigned int acc,
                                                  const List<unsigned int> &l) {
  std::unique_ptr<List<unsigned int>> _head{};
  std::unique_ptr<List<unsigned int>> *_write = &_head;
  const List<unsigned int> *_loop_l = &l;
  unsigned int _loop_acc = std::move(acc);
  while (true) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(
            _loop_l->v())) {
      *_write = std::make_unique<List<unsigned int>>(
          List<unsigned int>::cons(_loop_acc, List<unsigned int>::nil()));
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename List<unsigned int>::Cons>(_loop_l->v());
      auto _cell = std::make_unique<List<unsigned int>>(
          typename List<unsigned int>::Cons(_loop_acc, nullptr));
      *_write = std::move(_cell);
      _write =
          &std::get<typename List<unsigned int>::Cons>((*_write)->v_mut()).a1;
      _loop_l = a1.get();
      _loop_acc = (_loop_acc + a0);
      continue;
    }
  }
  return std::move(*_head);
}

/// differences l consecutive differences: 5,3,8,2 -> -2,5,-6.
List<unsigned int> LoopifyAlgorithms::differences(const List<unsigned int> &l) {
  std::unique_ptr<List<unsigned int>> _head{};
  std::unique_ptr<List<unsigned int>> *_write = &_head;
  const List<unsigned int> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(
            _loop_l->v())) {
      *_write = std::make_unique<List<unsigned int>>(List<unsigned int>::nil());
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename List<unsigned int>::Cons>(_loop_l->v());
      auto &&_sv0 = *a1;
      if (std::holds_alternative<typename List<unsigned int>::Nil>(_sv0.v())) {
        *_write =
            std::make_unique<List<unsigned int>>(List<unsigned int>::nil());
        break;
      } else {
        const auto &[a00, a10] =
            std::get<typename List<unsigned int>::Cons>(_sv0.v());
        auto _cell = std::make_unique<List<unsigned int>>(
            typename List<unsigned int>::Cons(
                (((a00 - a0) > a00 ? 0 : (a00 - a0))), nullptr));
        *_write = std::move(_cell);
        _write =
            &std::get<typename List<unsigned int>::Cons>((*_write)->v_mut()).a1;
        _loop_l = a1.get();
        continue;
      }
    }
  }
  return std::move(*_head);
}

/// rotate_left n l rotates list left by n positions.
List<unsigned int> LoopifyAlgorithms::rotate_left_fuel(unsigned int fuel,
                                                       unsigned int n,
                                                       List<unsigned int> l) {
  List<unsigned int> _result;
  List<unsigned int> _loop_l = std::move(l);
  unsigned int _loop_n = std::move(n);
  unsigned int _loop_fuel = std::move(fuel);
  while (true) {
    if (_loop_fuel <= 0) {
      _result = std::move(_loop_l);
      break;
    } else {
      unsigned int f = _loop_fuel - 1;
      if (_loop_n <= 0u) {
        _result = std::move(_loop_l);
        break;
      } else {
        if (std::holds_alternative<typename List<unsigned int>::Nil>(
                _loop_l.v_mut())) {
          _result = List<unsigned int>::nil();
          break;
        } else {
          auto &[a0, a1] =
              std::get<typename List<unsigned int>::Cons>(_loop_l.v_mut());
          _loop_l = (*a1).app(List<unsigned int>::cons(
              std::move(a0), List<unsigned int>::nil()));
          _loop_n = (((_loop_n - 1u) > _loop_n ? 0 : (_loop_n - 1u)));
          _loop_fuel = f;
        }
      }
    }
  }
  return _result;
}

List<unsigned int> LoopifyAlgorithms::rotate_left(unsigned int n,
                                                  const List<unsigned int> &l) {
  return rotate_left_fuel(n, n, l);
}

/// nub l removes ALL duplicates (not just consecutive): 1,2,1,3,2 -> 1,2,3.
List<unsigned int> LoopifyAlgorithms::nub_aux(const List<unsigned int> &l,
                                              unsigned int fuel) {
  std::unique_ptr<List<unsigned int>> _head{};
  std::unique_ptr<List<unsigned int>> *_write = &_head;
  unsigned int _loop_fuel = std::move(fuel);
  List<unsigned int> _loop_l = l;
  while (true) {
    if (_loop_fuel <= 0) {
      *_write = std::make_unique<List<unsigned int>>(List<unsigned int>::nil());
      break;
    } else {
      unsigned int f = _loop_fuel - 1;
      if (std::holds_alternative<typename List<unsigned int>::Nil>(
              _loop_l.v())) {
        *_write =
            std::make_unique<List<unsigned int>>(List<unsigned int>::nil());
        break;
      } else {
        const auto &[a0, a1] =
            std::get<typename List<unsigned int>::Cons>(_loop_l.v());
        auto filter_out_impl =
            [](auto &_self_filter_out, unsigned int val,
               const List<unsigned int> &rest) -> List<unsigned int> {
          if (std::holds_alternative<typename List<unsigned int>::Nil>(
                  rest.v())) {
            return List<unsigned int>::nil();
          } else {
            const auto &[a00, a10] =
                std::get<typename List<unsigned int>::Cons>(rest.v());
            if (val == a00) {
              return _self_filter_out(_self_filter_out, val, *a10);
            } else {
              return List<unsigned int>::cons(
                  a00, _self_filter_out(_self_filter_out, val, *a10));
            }
          }
        };
        auto filter_out =
            [&](unsigned int val,
                const List<unsigned int> &rest) -> List<unsigned int> {
          return filter_out_impl(filter_out_impl, val, rest);
        };
        auto _cell = std::make_unique<List<unsigned int>>(
            typename List<unsigned int>::Cons(a0, nullptr));
        *_write = std::move(_cell);
        _write =
            &std::get<typename List<unsigned int>::Cons>((*_write)->v_mut()).a1;
        _loop_fuel = f;
        _loop_l = filter_out(a0, *a1);
        continue;
      }
    }
  }
  return std::move(*_head);
}

List<unsigned int> LoopifyAlgorithms::nub(const List<unsigned int> &l) {
  return nub_aux(l, len_impl(l));
}

/// Internal helpers for palindrome check.
List<unsigned int> LoopifyAlgorithms::rev_impl(List<unsigned int> acc,
                                               const List<unsigned int> &l) {
  List<unsigned int> _result;
  const List<unsigned int> *_loop_l = &l;
  List<unsigned int> _loop_acc = std::move(acc);
  while (true) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(
            _loop_l->v())) {
      _result = std::move(_loop_acc);
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename List<unsigned int>::Cons>(_loop_l->v());
      _loop_l = a1.get();
      _loop_acc = List<unsigned int>::cons(a0, std::move(_loop_acc));
    }
  }
  return _result;
}

bool LoopifyAlgorithms::list_eq_impl(const List<unsigned int> &l1,
                                     const List<unsigned int> &l2) {
  bool _result;
  const List<unsigned int> *_loop_l2 = &l2;
  const List<unsigned int> *_loop_l1 = &l1;
  while (true) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(
            _loop_l1->v())) {
      if (std::holds_alternative<typename List<unsigned int>::Nil>(
              _loop_l2->v())) {
        _result = true;
        break;
      } else {
        _result = false;
        break;
      }
    } else {
      const auto &[a0, a1] =
          std::get<typename List<unsigned int>::Cons>(_loop_l1->v());
      if (std::holds_alternative<typename List<unsigned int>::Nil>(
              _loop_l2->v())) {
        _result = false;
        break;
      } else {
        const auto &[a00, a10] =
            std::get<typename List<unsigned int>::Cons>(_loop_l2->v());
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

/// is_palindrome l checks if list reads same forwards and backwards.
bool LoopifyAlgorithms::is_palindrome(const List<unsigned int> &l) {
  return list_eq_impl(l, rev_impl(List<unsigned int>::nil(), l));
}

/// windows n l sliding windows of size n: windows 2 1,2,3,4 ->
/// [1,2],[2,3],[3,4].
List<unsigned int> LoopifyAlgorithms::take_impl(unsigned int k,
                                                const List<unsigned int> &l) {
  std::unique_ptr<List<unsigned int>> _head{};
  std::unique_ptr<List<unsigned int>> *_write = &_head;
  const List<unsigned int> *_loop_l = &l;
  unsigned int _loop_k = std::move(k);
  while (true) {
    if (_loop_k <= 0) {
      *_write = std::make_unique<List<unsigned int>>(List<unsigned int>::nil());
      break;
    } else {
      unsigned int m = _loop_k - 1;
      if (std::holds_alternative<typename List<unsigned int>::Nil>(
              _loop_l->v())) {
        *_write =
            std::make_unique<List<unsigned int>>(List<unsigned int>::nil());
        break;
      } else {
        const auto &[a0, a1] =
            std::get<typename List<unsigned int>::Cons>(_loop_l->v());
        auto _cell = std::make_unique<List<unsigned int>>(
            typename List<unsigned int>::Cons(a0, nullptr));
        *_write = std::move(_cell);
        _write =
            &std::get<typename List<unsigned int>::Cons>((*_write)->v_mut()).a1;
        _loop_l = a1.get();
        _loop_k = m;
        continue;
      }
    }
  }
  return std::move(*_head);
}

List<List<unsigned int>>
LoopifyAlgorithms::windows_aux(unsigned int n, const List<unsigned int> &l,
                               unsigned int fuel) {
  std::unique_ptr<List<List<unsigned int>>> _head{};
  std::unique_ptr<List<List<unsigned int>>> *_write = &_head;
  unsigned int _loop_fuel = std::move(fuel);
  const List<unsigned int> *_loop_l = &l;
  while (true) {
    if (_loop_fuel <= 0) {
      *_write = std::make_unique<List<List<unsigned int>>>(
          List<List<unsigned int>>::nil());
      break;
    } else {
      unsigned int f = _loop_fuel - 1;
      if (std::holds_alternative<typename List<unsigned int>::Nil>(
              _loop_l->v())) {
        *_write = std::make_unique<List<List<unsigned int>>>(
            List<List<unsigned int>>::nil());
        break;
      } else {
        const auto &[a0, a1] =
            std::get<typename List<unsigned int>::Cons>(_loop_l->v());
        if (len_impl(*_loop_l) < n) {
          *_write = std::make_unique<List<List<unsigned int>>>(
              List<List<unsigned int>>::nil());
          break;
        } else {
          auto _cell = std::make_unique<List<List<unsigned int>>>(
              typename List<List<unsigned int>>::Cons(take_impl(n, *_loop_l),
                                                      nullptr));
          *_write = std::move(_cell);
          _write = &std::get<typename List<List<unsigned int>>::Cons>(
                        (*_write)->v_mut())
                        .a1;
          _loop_fuel = f;
          _loop_l = a1.get();
          continue;
        }
      }
    }
  }
  return std::move(*_head);
}

List<List<unsigned int>>
LoopifyAlgorithms::windows(unsigned int n, const List<unsigned int> &l) {
  return windows_aux(n, l, (len_impl(l) + 1));
}

/// sliding_pairs l returns consecutive pairs: 1,2,3,4 -> (1,2),(2,3),(3,4).
List<std::pair<unsigned int, unsigned int>>
LoopifyAlgorithms::sliding_pairs(const List<unsigned int> &l) {
  std::unique_ptr<List<std::pair<unsigned int, unsigned int>>> _head{};
  std::unique_ptr<List<std::pair<unsigned int, unsigned int>>> *_write = &_head;
  const List<unsigned int> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(
            _loop_l->v())) {
      *_write = std::make_unique<List<std::pair<unsigned int, unsigned int>>>(
          List<std::pair<unsigned int, unsigned int>>::nil());
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename List<unsigned int>::Cons>(_loop_l->v());
      auto &&_sv0 = *a1;
      if (std::holds_alternative<typename List<unsigned int>::Nil>(_sv0.v())) {
        *_write = std::make_unique<List<std::pair<unsigned int, unsigned int>>>(
            List<std::pair<unsigned int, unsigned int>>::nil());
        break;
      } else {
        const auto &[a00, a10] =
            std::get<typename List<unsigned int>::Cons>(_sv0.v());
        auto _cell =
            std::make_unique<List<std::pair<unsigned int, unsigned int>>>(
                typename List<std::pair<unsigned int, unsigned int>>::Cons(
                    std::make_pair(a0, a00), nullptr));
        *_write = std::move(_cell);
        _write =
            &std::get<
                 typename List<std::pair<unsigned int, unsigned int>>::Cons>(
                 (*_write)->v_mut())
                 .a1;
        _loop_l = a1.get();
        continue;
      }
    }
  }
  return std::move(*_head);
}

/// max_prefix_sum l maximum sum of prefix (Kadane-like pattern).
unsigned int LoopifyAlgorithms::max_prefix_sum(
    const List<unsigned int>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<unsigned int> *l;
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
      const List<unsigned int> &l = *_f.l;
      if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
        _result = 0u;
      } else {
        const auto &[a0, a1] =
            std::get<typename List<unsigned int>::Cons>(l.v());
        _stack.emplace_back(_Cont_Cons{a0});
        _stack.emplace_back(_Enter{a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Cont_Cons>(_frame));
      unsigned int a0 = _f.a0;
      unsigned int rest = _result;
      unsigned int sum = (a0 + rest);
      if (rest == 0u) {
        _result = 0u;
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
unsigned int LoopifyAlgorithms::weighted_sum(
    unsigned int i,
    const List<unsigned int>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<unsigned int> *l;
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
      const List<unsigned int> &l = *_f.l;
      unsigned int i = _f.i;
      if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
        _result = 0u;
      } else {
        const auto &[a0, a1] =
            std::get<typename List<unsigned int>::Cons>(l.v());
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

/// step_sum l sums with conditional doubling for odd numbers.
unsigned int LoopifyAlgorithms::step_sum(
    const List<unsigned int>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<unsigned int> *l;
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
      const List<unsigned int> &l = *_f.l;
      if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
        _result = 0u;
      } else {
        const auto &[a0, a1] =
            std::get<typename List<unsigned int>::Cons>(l.v());
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

/// Helper: get head with default value.
unsigned int LoopifyAlgorithms::head_nat(unsigned int d,
                                         const List<unsigned int> &l) {
  if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
    return d;
  } else {
    const auto &[a0, a1] = std::get<typename List<unsigned int>::Cons>(l.v());
    return a0;
  }
}

/// suffix_sums l computes suffix sums (reverse of prefix sums).
List<unsigned int> LoopifyAlgorithms::suffix_sums(
    const List<unsigned int>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<unsigned int> *l;
  };

  /// _Cont_Cons: saves [a0], resumes after recursive call, then processes rest.
  struct _Cont_Cons {
    unsigned int a0;
  };

  using _Frame = std::variant<_Enter, _Cont_Cons>;
  List<unsigned int> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l});
  /// Loopified suffix_sums: _Enter -> _Cont_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<unsigned int> &l = *_f.l;
      if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
        _result = List<unsigned int>::nil();
      } else {
        const auto &[a0, a1] =
            std::get<typename List<unsigned int>::Cons>(l.v());
        _stack.emplace_back(_Cont_Cons{a0});
        _stack.emplace_back(_Enter{a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Cont_Cons>(_frame));
      unsigned int a0 = _f.a0;
      List<unsigned int> rest = _result;
      _result = List<unsigned int>::cons((a0 + head_nat(0u, rest)), rest);
    }
  }
  return _result;
}
