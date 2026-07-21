#include "loopify_list_transforms.h"

List<std::pair<uint64_t, uint64_t>> LoopifyListTransforms::run_length_encode(
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
  std::vector<_Frame> _stack;
  _stack.reserve(8);
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
        auto &&_sv = *a1;
        if (std::holds_alternative<typename List<uint64_t>::Nil>(_sv.v())) {
          _result = List<std::pair<uint64_t, uint64_t>>::cons(
              std::make_pair(a0, UINT64_C(1)),
              List<std::pair<uint64_t, uint64_t>>::nil());
        } else {
          _stack.emplace_back(_Cont_Cons{a0});
          _stack.emplace_back(_Enter{a1.get()});
        }
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
        const auto &[a01, a11] =
            std::get<typename List<std::pair<uint64_t, uint64_t>>::Cons>(
                _rc1.v());
        const auto &[y, n] = a01;
        if (a0 == y) {
          _result = List<std::pair<uint64_t, uint64_t>>::cons(
              std::make_pair(y, (n + UINT64_C(1))), *a11);
        } else {
          _result = List<std::pair<uint64_t, uint64_t>>::cons(
              std::make_pair(a0, UINT64_C(1)),
              List<std::pair<uint64_t, uint64_t>>::cons(std::make_pair(y, n),
                                                        *a11));
        }
      }
    }
  }
  return _result;
}

List<uint64_t> LoopifyListTransforms::prefix_sums(
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

List<std::pair<uint64_t, uint64_t>> LoopifyListTransforms::sliding_pairs_fuel(
    uint64_t fuel,
    const List<uint64_t>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<uint64_t> *l;
    uint64_t fuel;
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
  _stack.emplace_back(_Enter{&l, fuel});
  /// Loopified sliding_pairs_fuel: _Enter -> _Resume_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<uint64_t> &l = *_f.l;
      uint64_t fuel = _f.fuel;
      if (fuel <= 0) {
        _result = List<std::pair<uint64_t, uint64_t>>::nil();
      } else {
        uint64_t fuel_ = fuel - 1;
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
            _stack.emplace_back(_Enter{a1.get(), fuel_});
          }
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

List<std::pair<uint64_t, uint64_t>>
LoopifyListTransforms::sliding_pairs(const List<uint64_t> &l) {
  uint64_t len = l.length();
  return sliding_pairs_fuel(len, l);
}

uint64_t LoopifyListTransforms::abs_diff(uint64_t x, uint64_t y) {
  if (y < x) {
    return (((x - y) > x ? 0 : (x - y)));
  } else {
    return (((y - x) > y ? 0 : (y - x)));
  }
}

List<uint64_t> LoopifyListTransforms::differences_fuel(
    uint64_t fuel,
    const List<uint64_t>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<uint64_t> *l;
    uint64_t fuel;
  };

  /// _Resume_Cons: saves [_s0], resumes after recursive call with _result.
  struct _Resume_Cons {
    std::decay_t<decltype(abs_diff(std::declval<uint64_t &>(),
                                   std::declval<uint64_t &>()))>
        _s0;
  };

  using _Frame = std::variant<_Enter, _Resume_Cons>;
  List<uint64_t> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l, fuel});
  /// Loopified differences_fuel: _Enter -> _Resume_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<uint64_t> &l = *_f.l;
      uint64_t fuel = _f.fuel;
      if (fuel <= 0) {
        _result = List<uint64_t>::nil();
      } else {
        uint64_t fuel_ = fuel - 1;
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
            _stack.emplace_back(_Resume_Cons{abs_diff(a0, a00)});
            _stack.emplace_back(_Enter{a1.get(), fuel_});
          }
        }
      }
    } else {
      auto _f = std::move(std::get<_Resume_Cons>(_frame));
      _result = List<uint64_t>::cons(_f._s0, std::move(_result));
    }
  }
  return _result;
}

List<uint64_t> LoopifyListTransforms::differences(const List<uint64_t> &l) {
  uint64_t len = l.length();
  return differences_fuel(len, l);
}

List<uint64_t> LoopifyListTransforms::take(
    uint64_t n,
    const List<uint64_t>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<uint64_t> *l;
    uint64_t n;
  };

  /// _Resume_Cons: saves [a0], resumes after recursive call with _result.
  struct _Resume_Cons {
    uint64_t a0;
  };

  using _Frame = std::variant<_Enter, _Resume_Cons>;
  List<uint64_t> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l, n});
  /// Loopified take: _Enter -> _Resume_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<uint64_t> &l = *_f.l;
      uint64_t n = _f.n;
      if (n <= 0) {
        _result = List<uint64_t>::nil();
      } else {
        uint64_t n_ = n - 1;
        if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
          _result = List<uint64_t>::nil();
        } else {
          const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
          _stack.emplace_back(_Resume_Cons{a0});
          _stack.emplace_back(_Enter{a1.get(), n_});
        }
      }
    } else {
      auto _f = std::move(std::get<_Resume_Cons>(_frame));
      _result = List<uint64_t>::cons(_f.a0, std::move(_result));
    }
  }
  return _result;
}

List<uint64_t> LoopifyListTransforms::drop(uint64_t n, List<uint64_t> l) {
  List<uint64_t> _loop_l = std::move(l);
  uint64_t _loop_n = std::move(n);
  while (true) {
    if (_loop_n <= 0) {
      return _loop_l;
    } else {
      uint64_t n_ = _loop_n - 1;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(
              _loop_l.v_mut())) {
        return List<uint64_t>::nil();
      } else {
        auto &[a0, a1] =
            std::get<typename List<uint64_t>::Cons>(_loop_l.v_mut());
        _loop_l = *a1;
        _loop_n = n_;
      }
    }
  }
}

List<List<uint64_t>> LoopifyListTransforms::chunks_of_fuel(
    uint64_t fuel, uint64_t n,
    const List<uint64_t>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    List<uint64_t> l;
    uint64_t fuel;
  };

  /// _Resume_Cons: saves [_s0], resumes after recursive call with _result.
  struct _Resume_Cons {
    std::decay_t<decltype(take(std::declval<uint64_t &>(),
                               std::declval<const List<uint64_t> &>()))>
        _s0;
  };

  using _Frame = std::variant<_Enter, _Resume_Cons>;
  List<List<uint64_t>> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{l, fuel});
  /// Loopified chunks_of_fuel: _Enter -> _Resume_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<uint64_t> &l = std::move(_f.l);
      uint64_t fuel = _f.fuel;
      if (fuel <= 0) {
        _result = List<List<uint64_t>>::nil();
      } else {
        uint64_t fuel_ = fuel - 1;
        if (n <= UINT64_C(0)) {
          _result = List<List<uint64_t>>::nil();
        } else {
          if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
            _result = List<List<uint64_t>>::nil();
          } else {
            _stack.emplace_back(_Resume_Cons{take(n, l)});
            _stack.emplace_back(_Enter{drop(n, l), fuel_});
          }
        }
      }
    } else {
      auto _f = std::move(std::get<_Resume_Cons>(_frame));
      _result = List<List<uint64_t>>::cons(_f._s0, std::move(_result));
    }
  }
  return _result;
}

List<List<uint64_t>> LoopifyListTransforms::chunks_of(uint64_t n,
                                                      const List<uint64_t> &l) {
  uint64_t len = l.length();
  return chunks_of_fuel(len, n, l);
}

List<uint64_t> LoopifyListTransforms::rotate_left_fuel(uint64_t fuel,
                                                       uint64_t n,
                                                       List<uint64_t> l) {
  List<uint64_t> _loop_l = std::move(l);
  uint64_t _loop_n = std::move(n);
  uint64_t _loop_fuel = std::move(fuel);
  while (true) {
    if (_loop_fuel <= 0) {
      return _loop_l;
    } else {
      uint64_t fuel_ = _loop_fuel - 1;
      if (_loop_n <= UINT64_C(0)) {
        return _loop_l;
      } else {
        if (std::holds_alternative<typename List<uint64_t>::Nil>(
                _loop_l.v_mut())) {
          return List<uint64_t>::nil();
        } else {
          auto &[a0, a1] =
              std::get<typename List<uint64_t>::Cons>(_loop_l.v_mut());
          List<uint64_t> rotated = a1->app(
              List<uint64_t>::cons(std::move(a0), List<uint64_t>::nil()));
          _loop_l = std::move(rotated);
          _loop_n = ((
              (_loop_n - UINT64_C(1)) > _loop_n ? 0 : (_loop_n - UINT64_C(1))));
          _loop_fuel = fuel_;
        }
      }
    }
  }
}

List<uint64_t> LoopifyListTransforms::rotate_left(uint64_t n,
                                                  const List<uint64_t> &l) {
  return rotate_left_fuel((n + UINT64_C(1)), n, l);
}

List<uint64_t> LoopifyListTransforms::uniq_sorted_fuel(
    uint64_t fuel,
    const List<uint64_t>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<uint64_t> *l;
    uint64_t fuel;
  };

  /// _Resume1: saves [a0], resumes after recursive call with _result.
  struct _Resume1 {
    uint64_t a0;
  };

  using _Frame = std::variant<_Enter, _Resume1>;
  List<uint64_t> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l, fuel});
  /// Loopified uniq_sorted_fuel: _Enter -> _Resume1.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<uint64_t> &l = *_f.l;
      uint64_t fuel = _f.fuel;
      if (fuel <= 0) {
        _result = List<uint64_t>::nil();
      } else {
        uint64_t fuel_ = fuel - 1;
        if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
          _result = List<uint64_t>::nil();
        } else {
          const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
          auto &&_sv0 = *a1;
          if (std::holds_alternative<typename List<uint64_t>::Nil>(_sv0.v())) {
            _result = List<uint64_t>::cons(a0, List<uint64_t>::nil());
          } else {
            const auto &[a00, a10] =
                std::get<typename List<uint64_t>::Cons>(_sv0.v());
            if (a0 == a00) {
              _stack.emplace_back(_Enter{a1.get(), fuel_});
            } else {
              _stack.emplace_back(_Resume1{a0});
              _stack.emplace_back(_Enter{a1.get(), fuel_});
            }
          }
        }
      }
    } else {
      auto _f = std::move(std::get<_Resume1>(_frame));
      _result = List<uint64_t>::cons(_f.a0, std::move(_result));
    }
  }
  return _result;
}

List<uint64_t> LoopifyListTransforms::uniq_sorted(const List<uint64_t> &l) {
  uint64_t len = l.length();
  return uniq_sorted_fuel(len, l);
}

uint64_t LoopifyListTransforms::step_sum(
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
