#include "loopify_list_windows.h"

uint64_t LoopifyListWindows::len(
    const List<uint64_t>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<uint64_t> *l;
  };

  /// _Resume_Cons: saves [_s0], resumes after recursive call with _result.
  struct _Resume_Cons {
    std::decay_t<decltype(UINT64_C(1))> _s0;
  };

  using _Frame = std::variant<_Enter, _Resume_Cons>;
  uint64_t _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l});
  /// Loopified len: _Enter -> _Resume_Cons.
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
        _stack.emplace_back(_Resume_Cons{UINT64_C(1)});
        _stack.emplace_back(_Enter{a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Resume_Cons>(_frame));
      _result = (_f._s0 + std::move(_result));
    }
  }
  return _result;
}

List<List<uint64_t>> LoopifyListWindows::map_cons_helper(
    uint64_t x,
    const List<List<uint64_t>>
        &ll) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<List<uint64_t>> *ll;
  };

  /// _Resume_Cons: saves [_s0], resumes after recursive call with _result.
  struct _Resume_Cons {
    std::decay_t<decltype(List<uint64_t>::cons(
        std::declval<uint64_t &>(), std::declval<List<uint64_t> &>()))>
        _s0;
  };

  using _Frame = std::variant<_Enter, _Resume_Cons>;
  List<List<uint64_t>> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&ll});
  /// Loopified map_cons_helper: _Enter -> _Resume_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<List<uint64_t>> &ll = *_f.ll;
      if (std::holds_alternative<typename List<List<uint64_t>>::Nil>(ll.v())) {
        _result = List<List<uint64_t>>::nil();
      } else {
        const auto &[a0, a1] =
            std::get<typename List<List<uint64_t>>::Cons>(ll.v());
        _stack.emplace_back(_Resume_Cons{List<uint64_t>::cons(x, a0)});
        _stack.emplace_back(_Enter{a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Resume_Cons>(_frame));
      _result = List<List<uint64_t>>::cons(_f._s0, std::move(_result));
    }
  }
  return _result;
}

List<uint64_t> LoopifyListWindows::drop(uint64_t m, List<uint64_t> xs) {
  List<uint64_t> _loop_xs = std::move(xs);
  uint64_t _loop_m = std::move(m);
  while (true) {
    if (_loop_m <= 0) {
      return _loop_xs;
    } else {
      uint64_t m_ = _loop_m - 1;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(
              _loop_xs.v_mut())) {
        return List<uint64_t>::nil();
      } else {
        auto &[a0, a1] =
            std::get<typename List<uint64_t>::Cons>(_loop_xs.v_mut());
        _loop_xs = *a1;
        _loop_m = m_;
      }
    }
  }
}

std::pair<List<uint64_t>, List<uint64_t>>
LoopifyListWindows::span_eq(uint64_t first, List<uint64_t> lst) {
  if (std::holds_alternative<typename List<uint64_t>::Nil>(lst.v_mut())) {
    return std::make_pair(List<uint64_t>::nil(), List<uint64_t>::nil());
  } else {
    auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(lst.v_mut());
    if (first == a0) {
      auto [s, r] = span_eq(first, *a1);
      return std::make_pair(List<uint64_t>::cons(std::move(a0), std::move(s)),
                            std::move(r));
    } else {
      return std::make_pair(List<uint64_t>::nil(), lst);
    }
  }
}

List<uint64_t> LoopifyListWindows::differences(
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
        auto &&_sv = *a1;
        if (std::holds_alternative<typename List<uint64_t>::Nil>(_sv.v())) {
          _result = List<uint64_t>::nil();
        } else {
          auto &&_sv1 = *a1;
          if (std::holds_alternative<typename List<uint64_t>::Nil>(_sv1.v())) {
            _result = List<uint64_t>::nil();
          } else {
            const auto &[a01, a11] =
                std::get<typename List<uint64_t>::Cons>(_sv1.v());
            _stack.emplace_back(
                _Resume_Cons{(((a01 - a0) > a01 ? 0 : (a01 - a0)))});
            _stack.emplace_back(_Enter{a1.get()});
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

List<std::pair<uint64_t, uint64_t>> LoopifyListWindows::sliding_pairs(
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
        auto &&_sv = *a1;
        if (std::holds_alternative<typename List<uint64_t>::Nil>(_sv.v())) {
          _result = List<std::pair<uint64_t, uint64_t>>::nil();
        } else {
          auto &&_sv1 = *a1;
          if (std::holds_alternative<typename List<uint64_t>::Nil>(_sv1.v())) {
            _result = List<std::pair<uint64_t, uint64_t>>::nil();
          } else {
            const auto &[a01, a11] =
                std::get<typename List<uint64_t>::Cons>(_sv1.v());
            _stack.emplace_back(_Resume_Cons{std::make_pair(a0, a01)});
            _stack.emplace_back(_Enter{a1.get()});
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

List<List<uint64_t>> LoopifyListWindows::inits(
    const List<uint64_t>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<uint64_t> *l;
  };

  /// _Resume_Cons: saves [_s0, a0], resumes after recursive call with _result.
  struct _Resume_Cons {
    std::decay_t<decltype(List<uint64_t>::nil())> _s0;
    uint64_t a0;
  };

  using _Frame = std::variant<_Enter, _Resume_Cons>;
  List<List<uint64_t>> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l});
  /// Loopified inits: _Enter -> _Resume_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<uint64_t> &l = *_f.l;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
        _result = List<List<uint64_t>>::cons(List<uint64_t>::nil(),
                                             List<List<uint64_t>>::nil());
      } else {
        const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
        _stack.emplace_back(_Resume_Cons{List<uint64_t>::nil(), a0});
        _stack.emplace_back(_Enter{a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Resume_Cons>(_frame));
      _result = List<List<uint64_t>>::cons(
          _f._s0, map_cons_helper(_f.a0, std::move(_result)));
    }
  }
  return _result;
}

List<List<uint64_t>> LoopifyListWindows::tails(
    List<uint64_t>
        l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    List<uint64_t> l;
  };

  /// _Resume_Cons: saves [l], resumes after recursive call with _result.
  struct _Resume_Cons {
    List<uint64_t> l;
  };

  using _Frame = std::variant<_Enter, _Resume_Cons>;
  List<List<uint64_t>> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{std::move(l)});
  /// Loopified tails: _Enter -> _Resume_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      List<uint64_t> l = std::move(_f.l);
      if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v_mut())) {
        _result = List<List<uint64_t>>::cons(List<uint64_t>::nil(),
                                             List<List<uint64_t>>::nil());
      } else {
        auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v_mut());
        _stack.emplace_back(_Resume_Cons{l});
        _stack.emplace_back(_Enter{*a1});
      }
    } else {
      auto _f = std::move(std::get<_Resume_Cons>(_frame));
      _result = List<List<uint64_t>>::cons(std::move(_f.l), std::move(_result));
    }
  }
  return _result;
}

List<uint64_t> LoopifyListWindows::take(
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

List<List<uint64_t>> LoopifyListWindows::windows_fuel(
    uint64_t fuel, uint64_t n,
    const List<uint64_t>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<uint64_t> *l;
    uint64_t fuel;
  };

  /// _Resume1: saves [_s0], resumes after recursive call with _result.
  struct _Resume1 {
    std::decay_t<decltype(take(std::declval<uint64_t &>(),
                               std::declval<const List<uint64_t> &>()))>
        _s0;
  };

  using _Frame = std::variant<_Enter, _Resume1>;
  List<List<uint64_t>> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l, fuel});
  /// Loopified windows_fuel: _Enter -> _Resume1.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<uint64_t> &l = *_f.l;
      uint64_t fuel = _f.fuel;
      if (fuel <= 0) {
        _result = List<List<uint64_t>>::nil();
      } else {
        uint64_t fuel_ = fuel - 1;
        if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
          _result = List<List<uint64_t>>::nil();
        } else {
          const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
          if (len(l) < n) {
            _result = List<List<uint64_t>>::nil();
          } else {
            _stack.emplace_back(_Resume1{take(n, l)});
            _stack.emplace_back(_Enter{a1.get(), fuel_});
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

List<List<uint64_t>> LoopifyListWindows::windows(uint64_t n,
                                                 const List<uint64_t> &l) {
  return windows_fuel(len(l), n, l);
}

List<List<uint64_t>> LoopifyListWindows::chunks_fuel(
    uint64_t fuel, uint64_t n,
    const List<uint64_t>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    List<uint64_t> l;
    uint64_t fuel;
  };

  /// _Resume_Cons: saves [_s0], resumes after recursive call with _result.
  struct _Resume_Cons {
    List<uint64_t> _s0;
  };

  using _Frame = std::variant<_Enter, _Resume_Cons>;
  List<List<uint64_t>> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{l, fuel});
  /// Loopified chunks_fuel: _Enter -> _Resume_Cons.
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
        if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
          _result = List<List<uint64_t>>::nil();
        } else {
          List<uint64_t> chunk = take(n, l);
          List<uint64_t> rest = drop(n, l);
          _stack.emplace_back(_Resume_Cons{std::move(std::move(chunk))});
          _stack.emplace_back(_Enter{std::move(rest), fuel_});
        }
      }
    } else {
      auto _f = std::move(std::get<_Resume_Cons>(_frame));
      _result =
          List<List<uint64_t>>::cons(std::move(_f._s0), std::move(_result));
    }
  }
  return _result;
}

List<List<uint64_t>> LoopifyListWindows::chunks(uint64_t n,
                                                const List<uint64_t> &l) {
  return chunks_fuel(len(l), n, l);
}

List<List<uint64_t>> LoopifyListWindows::group_fuel(
    uint64_t fuel,
    const List<uint64_t>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    List<uint64_t> l;
    uint64_t fuel;
  };

  /// _Resume_same: saves [_s0], resumes after recursive call with _result.
  struct _Resume_same {
    std::decay_t<decltype(List<uint64_t>::cons(
        std::declval<uint64_t &>(),
        std::move(std::declval<List<uint64_t> &>())))>
        _s0;
  };

  using _Frame = std::variant<_Enter, _Resume_same>;
  List<List<uint64_t>> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{l, fuel});
  /// Loopified group_fuel: _Enter -> _Resume_same.
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
        if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
          _result = List<List<uint64_t>>::nil();
        } else {
          const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
          auto [same, rest] = span_eq(a0, *a1);
          _stack.emplace_back(
              _Resume_same{List<uint64_t>::cons(a0, std::move(same))});
          _stack.emplace_back(_Enter{std::move(rest), fuel_});
        }
      }
    } else {
      auto _f = std::move(std::get<_Resume_same>(_frame));
      _result = List<List<uint64_t>>::cons(_f._s0, std::move(_result));
    }
  }
  return _result;
}

List<List<uint64_t>> LoopifyListWindows::group(const List<uint64_t> &l) {
  return group_fuel(len(l), l);
}
