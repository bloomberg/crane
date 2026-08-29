#include "loopify_algorithms.h"

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
  crane::small_vector<_Frame> _stack;
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
        _stack.emplace_back(_Enter{crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<_Resume_Cons>(_frame));
      _result = (std::move(_result) + 1);
    }
  }
  return _result;
}

List<uint64_t> LoopifyAlgorithms::sieve_fuel(uint64_t fuel, List<uint64_t> l) {
  std::shared_ptr<List<uint64_t>> _head{};
  std::shared_ptr<List<uint64_t>> *_write = &_head;
  List<uint64_t> _loop_l = std::move(l);
  uint64_t _loop_fuel = std::move(fuel);
  while (true) {
    if (_loop_fuel <= 0) {
      *_write = std::make_shared<List<uint64_t>>(std::move(_loop_l));
      break;
    } else {
      uint64_t f = _loop_fuel - 1;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(
              _loop_l.v_mut())) {
        *_write = std::make_shared<List<uint64_t>>(List<uint64_t>::nil());
        break;
      } else {
        auto &[a0, a1] =
            std::get<typename List<uint64_t>::Cons>(_loop_l.v_mut());
        auto filter_multiples_impl =
            [](auto &_self_filter_multiples, uint64_t p,
               const List<uint64_t> &rest) -> List<uint64_t> {
          if (std::holds_alternative<typename List<uint64_t>::Nil>(rest.v())) {
            return List<uint64_t>::nil();
          } else {
            const auto &[a00, a10] =
                std::get<typename List<uint64_t>::Cons>(rest.v());
            if ((p ? a00 % p : a00) == UINT64_C(0)) {
              return _self_filter_multiples(_self_filter_multiples, p, *a10);
            } else {
              return List<uint64_t>::cons(
                  a00, _self_filter_multiples(_self_filter_multiples, p, *a10));
            }
          }
        };
        auto filter_multiples =
            [&](uint64_t p, const List<uint64_t> &rest) -> List<uint64_t> {
          return filter_multiples_impl(filter_multiples_impl, p, rest);
        };
        auto _cell = std::make_shared<List<uint64_t>>(
            typename List<uint64_t>::Cons(a0, nullptr));
        *_write = std::move(_cell);
        _write = &std::get<typename List<uint64_t>::Cons>((*_write)->v_mut()).l;
        _loop_l = filter_multiples(a0, *a1);
        _loop_fuel = f;
        continue;
      }
    }
  }
  return std::move(*_head);
}

List<uint64_t> LoopifyAlgorithms::sieve(const List<uint64_t> &l) {
  return sieve_fuel(len_impl(l), l);
}

List<std::pair<uint64_t, uint64_t>> LoopifyAlgorithms::run_length_encode(
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
  List<std::pair<uint64_t, uint64_t>> _result{};
  crane::small_vector<_Frame> _stack;
  _stack.emplace_back(_Enter{&l});
  /// Loopified run_length_encode: _Enter -> _Cont_Cons.
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
        _stack.emplace_back(_Cont_Cons{a0});
        _stack.emplace_back(_Enter{crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<_Cont_Cons>(_frame));
      uint64_t a0 = _f.a0;
      List<std::pair<uint64_t, uint64_t>> _rc1 = std::move(_result);
      if (std::holds_alternative<
              typename List<std::pair<uint64_t, uint64_t>>::Nil>(_rc1.v())) {
        _result = List<std::pair<uint64_t, uint64_t>>::cons(
            std::make_pair(a0, UINT64_C(1)),
            List<std::pair<uint64_t, uint64_t>>::nil());
      } else {
        const auto &[a00, a10] =
            std::get<typename List<std::pair<uint64_t, uint64_t>>::Cons>(
                _rc1.v());
        const auto &[y, n] = a00;
        if (a0 == y) {
          _result = List<std::pair<uint64_t, uint64_t>>::cons(
              std::make_pair(y, (n + 1)), *a10);
        } else {
          _result = List<std::pair<uint64_t, uint64_t>>::cons(
              std::make_pair(a0, UINT64_C(1)),
              List<std::pair<uint64_t, uint64_t>>::cons(std::make_pair(y, n),
                                                        *a10));
        }
      }
    }
  }
  return _result;
}

List<uint64_t> LoopifyAlgorithms::prefix_sums(uint64_t acc,
                                              const List<uint64_t> &l) {
  std::shared_ptr<List<uint64_t>> _head{};
  std::shared_ptr<List<uint64_t>> *_write = &_head;
  const List<uint64_t> *_loop_l = &l;
  uint64_t _loop_acc = std::move(acc);
  while (true) {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l->v())) {
      *_write = std::make_shared<List<uint64_t>>(
          List<uint64_t>::cons(_loop_acc, List<uint64_t>::nil()));
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename List<uint64_t>::Cons>(_loop_l->v());
      auto _cell = std::make_shared<List<uint64_t>>(
          typename List<uint64_t>::Cons(_loop_acc, nullptr));
      *_write = std::move(_cell);
      _write = &std::get<typename List<uint64_t>::Cons>((*_write)->v_mut()).l;
      _loop_l = crane_raw(a1);
      _loop_acc = (_loop_acc + a0);
      continue;
    }
  }
  return std::move(*_head);
}

List<uint64_t> LoopifyAlgorithms::differences(const List<uint64_t> &l) {
  std::shared_ptr<List<uint64_t>> _head{};
  std::shared_ptr<List<uint64_t>> *_write = &_head;
  const List<uint64_t> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l->v())) {
      *_write = std::make_shared<List<uint64_t>>(List<uint64_t>::nil());
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename List<uint64_t>::Cons>(_loop_l->v());
      auto &&_sv0 = *a1;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(_sv0.v())) {
        *_write = std::make_shared<List<uint64_t>>(List<uint64_t>::nil());
        break;
      } else {
        const auto &[a00, a10] =
            std::get<typename List<uint64_t>::Cons>(_sv0.v());
        auto _cell =
            std::make_shared<List<uint64_t>>(typename List<uint64_t>::Cons(
                (((a00 - a0) > a00 ? 0 : (a00 - a0))), nullptr));
        *_write = std::move(_cell);
        _write = &std::get<typename List<uint64_t>::Cons>((*_write)->v_mut()).l;
        _loop_l = crane_raw(a1);
        continue;
      }
    }
  }
  return std::move(*_head);
}

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

List<uint64_t> LoopifyAlgorithms::nub_aux(const List<uint64_t> &l,
                                          uint64_t fuel) {
  std::shared_ptr<List<uint64_t>> _head{};
  std::shared_ptr<List<uint64_t>> *_write = &_head;
  uint64_t _loop_fuel = std::move(fuel);
  List<uint64_t> _loop_l = l;
  while (true) {
    if (_loop_fuel <= 0) {
      *_write = std::make_shared<List<uint64_t>>(List<uint64_t>::nil());
      break;
    } else {
      uint64_t f = _loop_fuel - 1;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l.v())) {
        *_write = std::make_shared<List<uint64_t>>(List<uint64_t>::nil());
        break;
      } else {
        const auto &[a0, a1] =
            std::get<typename List<uint64_t>::Cons>(_loop_l.v());
        auto filter_out_impl =
            [](auto &_self_filter_out, uint64_t val,
               const List<uint64_t> &rest) -> List<uint64_t> {
          if (std::holds_alternative<typename List<uint64_t>::Nil>(rest.v())) {
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
        auto _cell = std::make_shared<List<uint64_t>>(
            typename List<uint64_t>::Cons(a0, nullptr));
        *_write = std::move(_cell);
        _write = &std::get<typename List<uint64_t>::Cons>((*_write)->v_mut()).l;
        _loop_fuel = f;
        _loop_l = filter_out(a0, *a1);
        continue;
      }
    }
  }
  return std::move(*_head);
}

List<uint64_t> LoopifyAlgorithms::nub(const List<uint64_t> &l) {
  return nub_aux(l, len_impl(l));
}

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
      _loop_l = crane_raw(a1);
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
          _loop_l2 = crane_raw(a10);
          _loop_l1 = crane_raw(a1);
        } else {
          return false;
        }
      }
    }
  }
}

bool LoopifyAlgorithms::is_palindrome(const List<uint64_t> &l) {
  return list_eq_impl(l, rev_impl(List<uint64_t>::nil(), l));
}

List<uint64_t> LoopifyAlgorithms::take_impl(uint64_t k,
                                            const List<uint64_t> &l) {
  std::shared_ptr<List<uint64_t>> _head{};
  std::shared_ptr<List<uint64_t>> *_write = &_head;
  const List<uint64_t> *_loop_l = &l;
  uint64_t _loop_k = std::move(k);
  while (true) {
    if (_loop_k <= 0) {
      *_write = std::make_shared<List<uint64_t>>(List<uint64_t>::nil());
      break;
    } else {
      uint64_t m = _loop_k - 1;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l->v())) {
        *_write = std::make_shared<List<uint64_t>>(List<uint64_t>::nil());
        break;
      } else {
        const auto &[a0, a1] =
            std::get<typename List<uint64_t>::Cons>(_loop_l->v());
        auto _cell = std::make_shared<List<uint64_t>>(
            typename List<uint64_t>::Cons(a0, nullptr));
        *_write = std::move(_cell);
        _write = &std::get<typename List<uint64_t>::Cons>((*_write)->v_mut()).l;
        _loop_l = crane_raw(a1);
        _loop_k = m;
        continue;
      }
    }
  }
  return std::move(*_head);
}

List<List<uint64_t>> LoopifyAlgorithms::windows_aux(uint64_t n,
                                                    const List<uint64_t> &l,
                                                    uint64_t fuel) {
  std::shared_ptr<List<List<uint64_t>>> _head{};
  std::shared_ptr<List<List<uint64_t>>> *_write = &_head;
  uint64_t _loop_fuel = std::move(fuel);
  const List<uint64_t> *_loop_l = &l;
  while (true) {
    if (_loop_fuel <= 0) {
      *_write =
          std::make_shared<List<List<uint64_t>>>(List<List<uint64_t>>::nil());
      break;
    } else {
      uint64_t f = _loop_fuel - 1;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l->v())) {
        *_write =
            std::make_shared<List<List<uint64_t>>>(List<List<uint64_t>>::nil());
        break;
      } else {
        const auto &[a0, a1] =
            std::get<typename List<uint64_t>::Cons>(_loop_l->v());
        if (len_impl(*_loop_l) < n) {
          *_write = std::make_shared<List<List<uint64_t>>>(
              List<List<uint64_t>>::nil());
          break;
        } else {
          auto _cell = std::make_shared<List<List<uint64_t>>>(
              typename List<List<uint64_t>>::Cons(take_impl(n, *_loop_l),
                                                  nullptr));
          *_write = std::move(_cell);
          _write =
              &std::get<typename List<List<uint64_t>>::Cons>((*_write)->v_mut())
                   .l;
          _loop_fuel = f;
          _loop_l = crane_raw(a1);
          continue;
        }
      }
    }
  }
  return std::move(*_head);
}

List<List<uint64_t>> LoopifyAlgorithms::windows(uint64_t n,
                                                const List<uint64_t> &l) {
  return windows_aux(n, l, (len_impl(l) + 1));
}

List<std::pair<uint64_t, uint64_t>>
LoopifyAlgorithms::sliding_pairs(const List<uint64_t> &l) {
  std::shared_ptr<List<std::pair<uint64_t, uint64_t>>> _head{};
  std::shared_ptr<List<std::pair<uint64_t, uint64_t>>> *_write = &_head;
  const List<uint64_t> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l->v())) {
      *_write = std::make_shared<List<std::pair<uint64_t, uint64_t>>>(
          List<std::pair<uint64_t, uint64_t>>::nil());
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename List<uint64_t>::Cons>(_loop_l->v());
      auto &&_sv0 = *a1;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(_sv0.v())) {
        *_write = std::make_shared<List<std::pair<uint64_t, uint64_t>>>(
            List<std::pair<uint64_t, uint64_t>>::nil());
        break;
      } else {
        const auto &[a00, a10] =
            std::get<typename List<uint64_t>::Cons>(_sv0.v());
        auto _cell = std::make_shared<List<std::pair<uint64_t, uint64_t>>>(
            typename List<std::pair<uint64_t, uint64_t>>::Cons(
                std::make_pair(a0, a00), nullptr));
        *_write = std::move(_cell);
        _write = &std::get<typename List<std::pair<uint64_t, uint64_t>>::Cons>(
                      (*_write)->v_mut())
                      .l;
        _loop_l = crane_raw(a1);
        continue;
      }
    }
  }
  return std::move(*_head);
}

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
  crane::small_vector<_Frame> _stack;
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
        _stack.emplace_back(_Enter{crane_raw(a1)});
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
  crane::small_vector<_Frame> _stack;
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
        _stack.emplace_back(_Enter{crane_raw(a1), (i + 1)});
      }
    } else {
      auto _f = std::move(std::get<_Resume_Cons>(_frame));
      _result = (_f._s0 + std::move(_result));
    }
  }
  return _result;
}

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
  crane::small_vector<_Frame> _stack;
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
        _stack.emplace_back(_Enter{crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<_Resume_Cons>(_frame));
      _result = (_f.contribution + std::move(_result));
    }
  }
  return _result;
}

uint64_t LoopifyAlgorithms::head_nat(uint64_t d, const List<uint64_t> &l) {
  if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
    return d;
  } else {
    const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
    return a0;
  }
}

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
  crane::small_vector<_Frame> _stack;
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
        _stack.emplace_back(_Enter{crane_raw(a1)});
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
