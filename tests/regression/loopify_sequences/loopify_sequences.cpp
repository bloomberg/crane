#include "loopify_sequences.h"

/// alternate_sum sign acc l alternating sum with sign flip.
uint64_t LoopifySequences::alternate_sum(uint64_t sign, uint64_t acc,
                                         const List<uint64_t> &l) {
  const List<uint64_t> *_loop_l = &l;
  uint64_t _loop_acc = std::move(acc);
  uint64_t _loop_sign = std::move(sign);
  while (true) {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l->v())) {
      return _loop_acc;
    } else {
      const auto &[a0, a1] =
          std::get<typename List<uint64_t>::Cons>(_loop_l->v());
      uint64_t new_acc;
      if (_loop_sign == UINT64_C(1)) {
        new_acc = (_loop_acc + a0);
      } else {
        new_acc = (((_loop_acc - a0) > _loop_acc ? 0 : (_loop_acc - a0)));
      }
      uint64_t new_sign;
      if (_loop_sign == UINT64_C(1)) {
        new_sign = UINT64_C(0);
      } else {
        new_sign = UINT64_C(1);
      }
      _loop_l = a1.get();
      _loop_acc = new_acc;
      _loop_sign = new_sign;
    }
  }
}

/// collatz_list n generates collatz sequence.
List<uint64_t> LoopifySequences::collatz_list_fuel(
    uint64_t fuel,
    uint64_t
        n) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    uint64_t n;
    uint64_t fuel;
  };

  using _Frame = std::variant<_Enter>;
  List<uint64_t> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{n, fuel});
  /// Loopified collatz_list_fuel: _Enter.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    auto _f = std::move(std::get<_Enter>(_frame));
    uint64_t n = _f.n;
    uint64_t fuel = _f.fuel;
    if (fuel <= 0) {
      _result = List<uint64_t>::nil();
    } else {
      uint64_t f = fuel - 1;
      if (n == UINT64_C(1)) {
        _result = List<uint64_t>::cons(UINT64_C(1), List<uint64_t>::nil());
      } else {
        if ((UINT64_C(2) ? n % UINT64_C(2) : n) == UINT64_C(0)) {
          _stack.emplace_back(_Enter{(UINT64_C(2) ? n / UINT64_C(2) : 0), f});
        } else {
          _stack.emplace_back(_Enter{((UINT64_C(3) * n) + UINT64_C(1)), f});
        }
      }
    }
  }
  return _result;
}

List<uint64_t> LoopifySequences::collatz_list(uint64_t n) {
  return collatz_list_fuel(UINT64_C(1000), n);
}

/// run_sum l running sum (scanl for addition).
List<uint64_t> LoopifySequences::run_sum_aux(
    uint64_t acc,
    const List<uint64_t>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<uint64_t> *l;
    uint64_t acc;
  };

  /// _Resume_Cons: saves [new_acc], resumes after recursive call with _result.
  struct _Resume_Cons {
    uint64_t new_acc;
  };

  using _Frame = std::variant<_Enter, _Resume_Cons>;
  List<uint64_t> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l, acc});
  /// Loopified run_sum_aux: _Enter -> _Resume_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<uint64_t> &l = *_f.l;
      uint64_t acc = _f.acc;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
        _result = List<uint64_t>::nil();
      } else {
        const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
        uint64_t new_acc = (acc + a0);
        _stack.emplace_back(_Resume_Cons{new_acc});
        _stack.emplace_back(_Enter{a1.get(), new_acc});
      }
    } else {
      auto _f = std::move(std::get<_Resume_Cons>(_frame));
      _result = List<uint64_t>::cons(_f.new_acc, std::move(_result));
    }
  }
  return _result;
}

List<uint64_t> LoopifySequences::run_sum(const List<uint64_t> &l) {
  return List<uint64_t>::cons(UINT64_C(0), run_sum_aux(UINT64_C(0), l));
}

/// rotate_left n l rotates list left by n positions.
List<uint64_t> LoopifySequences::rotate_left_fuel(uint64_t fuel, uint64_t n,
                                                  List<uint64_t> l) {
  List<uint64_t> _loop_l = std::move(l);
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

List<uint64_t> LoopifySequences::rotate_left(uint64_t n,
                                             const List<uint64_t> &l) {
  return rotate_left_fuel(UINT64_C(100), n, l);
}

/// sum_acc acc l sum with accumulator.
uint64_t LoopifySequences::sum_acc(uint64_t acc, const List<uint64_t> &l) {
  const List<uint64_t> *_loop_l = &l;
  uint64_t _loop_acc = std::move(acc);
  while (true) {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l->v())) {
      return _loop_acc;
    } else {
      const auto &[a0, a1] =
          std::get<typename List<uint64_t>::Cons>(_loop_l->v());
      _loop_l = a1.get();
      _loop_acc = (_loop_acc + a0);
    }
  }
}

/// repeat_string s n repeats string n times (using list as string).
List<uint64_t> LoopifySequences::repeat_string(
    const List<uint64_t> &s,
    uint64_t
        n) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    uint64_t n;
  };

  /// _Resume_m: saves [s], resumes after recursive call with _result.
  struct _Resume_m {
    List<uint64_t> s;
  };

  using _Frame = std::variant<_Enter, _Resume_m>;
  List<uint64_t> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{n});
  /// Loopified repeat_string: _Enter -> _Resume_m.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      uint64_t n = _f.n;
      if (n <= 0) {
        _result = List<uint64_t>::nil();
      } else {
        uint64_t m = n - 1;
        _stack.emplace_back(_Resume_m{s});
        _stack.emplace_back(_Enter{m});
      }
    } else {
      auto _f = std::move(std::get<_Resume_m>(_frame));
      _result = std::move(_f.s).app(std::move(_result));
    }
  }
  return _result;
}

/// repeat_with_sep s sep n repeats with separator.
List<uint64_t> LoopifySequences::repeat_with_sep(
    List<uint64_t> s, const List<uint64_t> &sep,
    uint64_t
        n) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    uint64_t n;
  };

  /// _Resume__x: saves [s, sep], resumes after recursive call with _result.
  struct _Resume__x {
    List<uint64_t> s;
    List<uint64_t> sep;
  };

  using _Frame = std::variant<_Enter, _Resume__x>;
  List<uint64_t> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{n});
  /// Loopified repeat_with_sep: _Enter -> _Resume__x.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      uint64_t n = _f.n;
      if (n <= 0) {
        _result = List<uint64_t>::nil();
      } else {
        uint64_t m = n - 1;
        if (m <= 0) {
          _result = std::move(s);
        } else {
          uint64_t _x = m - 1;
          _stack.emplace_back(_Resume__x{s, sep});
          _stack.emplace_back(_Enter{m});
        }
      }
    } else {
      auto _f = std::move(std::get<_Resume__x>(_frame));
      _result = std::move(_f.s).app(std::move(_f.sep).app(std::move(_result)));
    }
  }
  return _result;
}

/// string_chain s n recursive string chain: s-chain(s, n-1)-end.
List<uint64_t> LoopifySequences::string_chain_fuel(
    uint64_t fuel, const List<uint64_t> &s, uint64_t n,
    const List<uint64_t> &sep,
    const List<uint64_t> &end_marker) { /// _Enter: captures varying parameters
                                        /// for each recursive call.

  struct _Enter {
    uint64_t n;
    uint64_t fuel;
  };

  /// _Resume1: saves [s, sep, _s2], resumes after recursive call with _result.
  struct _Resume1 {
    List<uint64_t> s;
    List<uint64_t> sep;
    std::decay_t<decltype(std::declval<const List<uint64_t> &>().app(
        std::declval<const List<uint64_t> &>()))>
        _s2;
  };

  using _Frame = std::variant<_Enter, _Resume1>;
  List<uint64_t> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{n, fuel});
  /// Loopified string_chain_fuel: _Enter -> _Resume1.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      uint64_t n = _f.n;
      uint64_t fuel = _f.fuel;
      if (fuel <= 0) {
        _result = List<uint64_t>::nil();
      } else {
        uint64_t f = fuel - 1;
        if (n <= UINT64_C(0)) {
          _result = List<uint64_t>::nil();
        } else {
          _stack.emplace_back(_Resume1{s, sep, sep.app(end_marker)});
          _stack.emplace_back(
              _Enter{(((n - UINT64_C(1)) > n ? 0 : (n - UINT64_C(1)))), f});
        }
      }
    } else {
      auto _f = std::move(std::get<_Resume1>(_frame));
      _result = std::move(_f.s).app(
          std::move(_f.sep).app(std::move(_result).app(_f._s2)));
    }
  }
  return _result;
}

List<uint64_t>
LoopifySequences::string_chain(const List<uint64_t> &s, uint64_t n,
                               const List<uint64_t> &sep,
                               const List<uint64_t> &end_marker) {
  return string_chain_fuel(UINT64_C(1000), s, n, sep, end_marker);
}

/// split_by_sign l base pos neg splits list based on base threshold.
std::pair<List<uint64_t>, List<uint64_t>>
LoopifySequences::split_by_sign(const List<uint64_t> &l, uint64_t base,
                                List<uint64_t> pos, List<uint64_t> neg) {
  List<uint64_t> _loop_neg = std::move(neg);
  List<uint64_t> _loop_pos = std::move(pos);
  const List<uint64_t> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l->v())) {
      return std::make_pair(std::move(_loop_pos), std::move(_loop_neg));
    } else {
      const auto &[a0, a1] =
          std::get<typename List<uint64_t>::Cons>(_loop_l->v());
      if (base <= a0) {
        _loop_pos = List<uint64_t>::cons(a0, std::move(_loop_pos));
        _loop_l = a1.get();
      } else {
        _loop_neg = List<uint64_t>::cons(a0, std::move(_loop_neg));
        _loop_l = a1.get();
      }
    }
  }
}

/// differences l computes differences between consecutive elements.
List<uint64_t> LoopifySequences::differences(
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

/// replace_at idx value l replaces element at index with value.
List<uint64_t> LoopifySequences::replace_at(
    uint64_t idx, uint64_t value,
    const List<uint64_t>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<uint64_t> *l;
    uint64_t idx;
  };

  /// _Resume1: saves [a0], resumes after recursive call with _result.
  struct _Resume1 {
    uint64_t a0;
  };

  using _Frame = std::variant<_Enter, _Resume1>;
  List<uint64_t> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l, idx});
  /// Loopified replace_at: _Enter -> _Resume1.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<uint64_t> &l = *_f.l;
      uint64_t idx = _f.idx;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
        _result = List<uint64_t>::nil();
      } else {
        const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
        if (idx == UINT64_C(0)) {
          _result = List<uint64_t>::cons(value, *a1);
        } else {
          _stack.emplace_back(_Resume1{a0});
          _stack.emplace_back(
              _Enter{a1.get(),
                     (((idx - UINT64_C(1)) > idx ? 0 : (idx - UINT64_C(1))))});
        }
      }
    } else {
      auto _f = std::move(std::get<_Resume1>(_frame));
      _result = List<uint64_t>::cons(_f.a0, std::move(_result));
    }
  }
  return _result;
}

/// cycle n l repeats list n times.
List<uint64_t> LoopifySequences::cycle(
    uint64_t n,
    const List<uint64_t>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    uint64_t n;
  };

  /// _Resume_Cons: saves [l], resumes after recursive call with _result.
  struct _Resume_Cons {
    List<uint64_t> l;
  };

  using _Frame = std::variant<_Enter, _Resume_Cons>;
  List<uint64_t> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{n});
  /// Loopified cycle: _Enter -> _Resume_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      uint64_t n = _f.n;
      if (n <= 0) {
        _result = List<uint64_t>::nil();
      } else {
        uint64_t m = n - 1;
        if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
          _result = List<uint64_t>::nil();
        } else {
          _stack.emplace_back(_Resume_Cons{l});
          _stack.emplace_back(_Enter{m});
        }
      }
    } else {
      auto _f = std::move(std::get<_Resume_Cons>(_frame));
      _result = std::move(_f.l).app(std::move(_result));
    }
  }
  return _result;
}

/// Helper: get first element.
uint64_t LoopifySequences::first_elem(const List<uint64_t> &l) {
  if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
    return UINT64_C(0);
  } else {
    const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
    return a0;
  }
}

/// Helper: get last element.
uint64_t LoopifySequences::last_elem(const List<uint64_t> &l) {
  const List<uint64_t> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l->v())) {
      return UINT64_C(0);
    } else {
      const auto &[a0, a1] =
          std::get<typename List<uint64_t>::Cons>(_loop_l->v());
      auto &&_sv = *a1;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(_sv.v())) {
        return a0;
      } else {
        _loop_l = a1.get();
      }
    }
  }
}

/// Helper: remove first element.
List<uint64_t> LoopifySequences::tail_list(const List<uint64_t> &l) {
  if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
    return List<uint64_t>::nil();
  } else {
    const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
    return *a1;
  }
}

/// Helper: remove last element.
List<uint64_t> LoopifySequences::init_list(
    const List<uint64_t>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<uint64_t> *l;
  };

  /// _Resume_Cons: saves [a0], resumes after recursive call with _result.
  struct _Resume_Cons {
    uint64_t a0;
  };

  using _Frame = std::variant<_Enter, _Resume_Cons>;
  List<uint64_t> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l});
  /// Loopified init_list: _Enter -> _Resume_Cons.
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
        auto &&_sv = *a1;
        if (std::holds_alternative<typename List<uint64_t>::Nil>(_sv.v())) {
          _result = List<uint64_t>::nil();
        } else {
          _stack.emplace_back(_Resume_Cons{a0});
          _stack.emplace_back(_Enter{a1.get()});
        }
      }
    } else {
      auto _f = std::move(std::get<_Resume_Cons>(_frame));
      _result = List<uint64_t>::cons(_f.a0, std::move(_result));
    }
  }
  return _result;
}

/// is_palindrome s checks if list is a palindrome.
bool LoopifySequences::is_palindrome_fuel(uint64_t fuel,
                                          const List<uint64_t> &s) {
  List<uint64_t> _loop_s = s;
  uint64_t _loop_fuel = std::move(fuel);
  while (true) {
    if (_loop_fuel <= 0) {
      return true;
    } else {
      uint64_t f = _loop_fuel - 1;
      uint64_t n = _loop_s.length();
      if (n <= 0) {
        return true;
      } else {
        uint64_t n0 = n - 1;
        if (n0 <= 0) {
          return true;
        } else {
          uint64_t _x = n0 - 1;
          if (first_elem(_loop_s) == last_elem(_loop_s)) {
            _loop_s = init_list(tail_list(_loop_s));
            _loop_fuel = f;
          } else {
            return false;
          }
        }
      }
    }
  }
}

bool LoopifySequences::is_palindrome(const List<uint64_t> &s) {
  return is_palindrome_fuel(UINT64_C(1000), s);
}

/// string_subsequences s generates all subsequences treating list as string.
List<List<uint64_t>> LoopifySequences::string_subsequences(
    const List<uint64_t>
        &s) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<uint64_t> *s;
  };

  /// _Cont_Cons: saves [a0], resumes after recursive call, then processes rest.
  struct _Cont_Cons {
    uint64_t a0;
  };

  using _Frame = std::variant<_Enter, _Cont_Cons>;
  List<List<uint64_t>> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&s});
  /// Loopified string_subsequences: _Enter -> _Cont_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<uint64_t> &s = *_f.s;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(s.v())) {
        _result = List<List<uint64_t>>::cons(List<uint64_t>::nil(),
                                             List<List<uint64_t>>::nil());
      } else {
        const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(s.v());
        _stack.emplace_back(_Cont_Cons{a0});
        _stack.emplace_back(_Enter{a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Cont_Cons>(_frame));
      uint64_t a0 = _f.a0;
      List<List<uint64_t>> sub_rest = std::move(_result);
      auto map_prepend_c_impl =
          [&](auto &_self_map_prepend_c,
              const List<List<uint64_t>> &lsts) -> List<List<uint64_t>> {
        if (std::holds_alternative<typename List<List<uint64_t>>::Nil>(
                lsts.v())) {
          return List<List<uint64_t>>::nil();
        } else {
          const auto &[a00, a10] =
              std::get<typename List<List<uint64_t>>::Cons>(lsts.v());
          return List<List<uint64_t>>::cons(
              List<uint64_t>::cons(a0, a00),
              _self_map_prepend_c(_self_map_prepend_c, *a10));
        }
      };
      auto map_prepend_c =
          [&](const List<List<uint64_t>> &lsts) -> List<List<uint64_t>> {
        return map_prepend_c_impl(map_prepend_c_impl, lsts);
      };
      _result = sub_rest.app(map_prepend_c(sub_rest));
    }
  }
  return _result;
}

/// run_length_groups l groups consecutive runs into sublist lengths.
List<uint64_t> LoopifySequences::run_length_groups_aux(
    uint64_t prev, uint64_t count,
    const List<uint64_t>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<uint64_t> *l;
    uint64_t count;
    uint64_t prev;
  };

  /// _Resume1: saves [count], resumes after recursive call with _result.
  struct _Resume1 {
    uint64_t count;
  };

  using _Frame = std::variant<_Enter, _Resume1>;
  List<uint64_t> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l, count, prev});
  /// Loopified run_length_groups_aux: _Enter -> _Resume1.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<uint64_t> &l = *_f.l;
      uint64_t count = _f.count;
      uint64_t prev = _f.prev;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
        if (count == UINT64_C(0)) {
          _result = List<uint64_t>::nil();
        } else {
          _result = List<uint64_t>::cons(count, List<uint64_t>::nil());
        }
      } else {
        const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
        if (prev == a0) {
          _stack.emplace_back(_Enter{a1.get(), (count + 1), a0});
        } else {
          if (count == UINT64_C(0)) {
            _stack.emplace_back(_Enter{a1.get(), UINT64_C(1), a0});
          } else {
            _stack.emplace_back(_Resume1{count});
            _stack.emplace_back(_Enter{a1.get(), UINT64_C(1), a0});
          }
        }
      }
    } else {
      auto _f = std::move(std::get<_Resume1>(_frame));
      _result = List<uint64_t>::cons(_f.count, std::move(_result));
    }
  }
  return _result;
}

List<uint64_t> LoopifySequences::run_length_groups(const List<uint64_t> &l) {
  if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
    return List<uint64_t>::nil();
  } else {
    const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
    return run_length_groups_aux(a0, UINT64_C(1), *a1);
  }
}

/// is_prefix_of l1 l2 checks if l1 is a prefix of l2.
bool LoopifySequences::is_prefix_of(const List<uint64_t> &l1,
                                    const List<uint64_t> &l2) {
  const List<uint64_t> *_loop_l2 = &l2;
  const List<uint64_t> *_loop_l1 = &l1;
  while (true) {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l1->v())) {
      return true;
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

/// lis l longest increasing subsequence (greedy, not optimal).
List<uint64_t> LoopifySequences::lis(
    List<uint64_t>
        l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    List<uint64_t> l;
  };

  /// _Resume1: saves [a0], resumes after recursive call with _result.
  struct _Resume1 {
    uint64_t a0;
  };

  using _Frame = std::variant<_Enter, _Resume1>;
  List<uint64_t> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{std::move(l)});
  /// Loopified lis: _Enter -> _Resume1.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      List<uint64_t> l = std::move(_f.l);
      if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v_mut())) {
        _result = List<uint64_t>::nil();
      } else {
        auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v_mut());
        auto &&_sv0 = *a1;
        if (std::holds_alternative<typename List<uint64_t>::Nil>(_sv0.v())) {
          _result = std::move(l);
        } else {
          const auto &[a00, a10] =
              std::get<typename List<uint64_t>::Cons>(_sv0.v());
          if (a0 < a00) {
            _stack.emplace_back(_Resume1{std::move(a0)});
            _stack.emplace_back(_Enter{*a1});
          } else {
            _stack.emplace_back(_Enter{*a1});
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

/// Helper: check if element is in list.
bool LoopifySequences::elem(
    uint64_t x,
    const List<uint64_t>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<uint64_t> *l;
  };

  /// _Resume_Cons: saves [_s0], resumes after recursive call with _result.
  struct _Resume_Cons {
    std::decay_t<decltype(std::declval<uint64_t &>() ==
                          std::declval<uint64_t &>())>
        _s0;
  };

  using _Frame = std::variant<_Enter, _Resume_Cons>;
  bool _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l});
  /// Loopified elem: _Enter -> _Resume_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<uint64_t> &l = *_f.l;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
        _result = false;
      } else {
        const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
        _stack.emplace_back(_Resume_Cons{x == a0});
        _stack.emplace_back(_Enter{a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Resume_Cons>(_frame));
      _result = (_f._s0 || std::move(_result));
    }
  }
  return _result;
}

/// Helper: filter list.
List<uint64_t> LoopifySequences::filter_ne(
    uint64_t x,
    const List<uint64_t>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<uint64_t> *l;
  };

  /// _Resume1: saves [a0], resumes after recursive call with _result.
  struct _Resume1 {
    uint64_t a0;
  };

  using _Frame = std::variant<_Enter, _Resume1>;
  List<uint64_t> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l});
  /// Loopified filter_ne: _Enter -> _Resume1.
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
        if (x == a0) {
          _stack.emplace_back(_Enter{a1.get()});
        } else {
          _stack.emplace_back(_Resume1{a0});
          _stack.emplace_back(_Enter{a1.get()});
        }
      }
    } else {
      auto _f = std::move(std::get<_Resume1>(_frame));
      _result = List<uint64_t>::cons(_f.a0, std::move(_result));
    }
  }
  return _result;
}

/// nub l removes duplicates from list.
List<uint64_t> LoopifySequences::nub_fuel(
    uint64_t fuel,
    const List<uint64_t>
        &l) { /// _Enter: captures varying parameters for each recursive call.

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
  _stack.emplace_back(_Enter{l, fuel});
  /// Loopified nub_fuel: _Enter -> _Resume_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<uint64_t> &l = std::move(_f.l);
      uint64_t fuel = _f.fuel;
      if (fuel <= 0) {
        _result = List<uint64_t>::nil();
      } else {
        uint64_t f = fuel - 1;
        if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
          _result = List<uint64_t>::nil();
        } else {
          const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
          _stack.emplace_back(_Resume_Cons{a0});
          _stack.emplace_back(_Enter{filter_ne(a0, *a1), f});
        }
      }
    } else {
      auto _f = std::move(std::get<_Resume_Cons>(_frame));
      _result = List<uint64_t>::cons(_f.a0, std::move(_result));
    }
  }
  return _result;
}

List<uint64_t> LoopifySequences::nub(const List<uint64_t> &l) {
  return nub_fuel(l.length(), l);
}

/// group l groups consecutive equal elements.
List<List<uint64_t>> LoopifySequences::group_fuel(uint64_t fuel,
                                                  const List<uint64_t> &l) {
  if (fuel <= 0) {
    return List<List<uint64_t>>::nil();
  } else {
    uint64_t f = fuel - 1;
    if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
      return List<List<uint64_t>>::nil();
    } else {
      const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
      auto &&_sv0 = *a1;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(_sv0.v())) {
        return List<List<uint64_t>>::cons(
            List<uint64_t>::cons(a0, List<uint64_t>::nil()),
            List<List<uint64_t>>::nil());
      } else {
        const auto &[a00, a10] =
            std::get<typename List<uint64_t>::Cons>(_sv0.v());
        if (a0 == a00) {
          auto &&_sv1 = group_fuel(f, *a1);
          if (std::holds_alternative<typename List<List<uint64_t>>::Nil>(
                  _sv1.v())) {
            return List<List<uint64_t>>::cons(
                List<uint64_t>::cons(a0, List<uint64_t>::nil()),
                List<List<uint64_t>>::nil());
          } else {
            const auto &[a01, a11] =
                std::get<typename List<List<uint64_t>>::Cons>(_sv1.v());
            return List<List<uint64_t>>::cons(List<uint64_t>::cons(a0, a01),
                                              *a11);
          }
        } else {
          return List<List<uint64_t>>::cons(
              List<uint64_t>::cons(a0, List<uint64_t>::nil()),
              group_fuel(f, *a1));
        }
      }
    }
  }
}

List<List<uint64_t>> LoopifySequences::group(const List<uint64_t> &l) {
  return group_fuel(l.length(), l);
}

/// Helper: get head with default.
uint64_t LoopifySequences::head_or(uint64_t default0, const List<uint64_t> &l) {
  if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
    return default0;
  } else {
    const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
    return a0;
  }
}

/// remove_if_sum_even l removes elements where sum with next is even.
List<uint64_t> LoopifySequences::remove_if_sum_even(
    const List<uint64_t>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<uint64_t> *l;
  };

  /// _Resume1: saves [a0], resumes after recursive call with _result.
  struct _Resume1 {
    uint64_t a0;
  };

  using _Frame = std::variant<_Enter, _Resume1>;
  List<uint64_t> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l});
  /// Loopified remove_if_sum_even: _Enter -> _Resume1.
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
        uint64_t next = head_or(UINT64_C(0), *a1);
        if ((UINT64_C(2) ? (a0 + next) % UINT64_C(2) : (a0 + next)) ==
            UINT64_C(0)) {
          _stack.emplace_back(_Enter{a1.get()});
        } else {
          _stack.emplace_back(_Resume1{a0});
          _stack.emplace_back(_Enter{a1.get()});
        }
      }
    } else {
      auto _f = std::move(std::get<_Resume1>(_frame));
      _result = List<uint64_t>::cons(_f.a0, std::move(_result));
    }
  }
  return _result;
}

/// run_length_encode l encodes consecutive runs: 1,1,2,2,2 -> (1,2),(2,3).
List<std::pair<uint64_t, uint64_t>>
LoopifySequences::run_length_encode_fuel(uint64_t fuel,
                                         const List<uint64_t> &l) {
  if (fuel <= 0) {
    return List<std::pair<uint64_t, uint64_t>>::nil();
  } else {
    uint64_t f = fuel - 1;
    if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
      return List<std::pair<uint64_t, uint64_t>>::nil();
    } else {
      const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
      auto &&_sv = *a1;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(_sv.v())) {
        return List<std::pair<uint64_t, uint64_t>>::cons(
            std::make_pair(a0, UINT64_C(1)),
            List<std::pair<uint64_t, uint64_t>>::nil());
      } else {
        auto &&_sv1 = run_length_encode_fuel(f, *a1);
        if (std::holds_alternative<
                typename List<std::pair<uint64_t, uint64_t>>::Nil>(_sv1.v())) {
          return List<std::pair<uint64_t, uint64_t>>::cons(
              std::make_pair(a0, UINT64_C(1)),
              List<std::pair<uint64_t, uint64_t>>::nil());
        } else {
          const auto &[a01, a11] =
              std::get<typename List<std::pair<uint64_t, uint64_t>>::Cons>(
                  _sv1.v());
          const uint64_t &y = a01.first;
          const uint64_t &n = a01.second;
          if (a0 == y) {
            return List<std::pair<uint64_t, uint64_t>>::cons(
                std::make_pair(y, (n + 1)), *a11);
          } else {
            return List<std::pair<uint64_t, uint64_t>>::cons(
                std::make_pair(a0, UINT64_C(1)),
                List<std::pair<uint64_t, uint64_t>>::cons(std::make_pair(y, n),
                                                          *a11));
          }
        }
      }
    }
  }
}

List<std::pair<uint64_t, uint64_t>>
LoopifySequences::run_length_encode(const List<uint64_t> &l) {
  return run_length_encode_fuel(l.length(), l);
}

/// between lo hi l filters elements in range lo, hi.
List<uint64_t> LoopifySequences::between(
    uint64_t lo, uint64_t hi,
    const List<uint64_t>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<uint64_t> *l;
  };

  /// _Resume1: saves [a0], resumes after recursive call with _result.
  struct _Resume1 {
    uint64_t a0;
  };

  using _Frame = std::variant<_Enter, _Resume1>;
  List<uint64_t> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l});
  /// Loopified between: _Enter -> _Resume1.
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
        if ((lo <= a0 && a0 <= hi)) {
          _stack.emplace_back(_Resume1{a0});
          _stack.emplace_back(_Enter{a1.get()});
        } else {
          _stack.emplace_back(_Enter{a1.get()});
        }
      }
    } else {
      auto _f = std::move(std::get<_Resume1>(_frame));
      _result = List<uint64_t>::cons(_f.a0, std::move(_result));
    }
  }
  return _result;
}
