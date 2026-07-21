#include "loopify_list_pairing.h"

std::pair<List<uint64_t>, List<uint64_t>> LoopifyListPairing::unzip(
    const List<std::pair<uint64_t, uint64_t>>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<std::pair<uint64_t, uint64_t>> *l;
  };

  /// _Cont_a: saves [a, b], resumes after recursive call, then processes rest.
  struct _Cont_a {
    uint64_t a;
    uint64_t b;
  };

  using _Frame = std::variant<_Enter, _Cont_a>;
  std::pair<List<uint64_t>, List<uint64_t>> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l});
  /// Loopified unzip: _Enter -> _Cont_a.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<std::pair<uint64_t, uint64_t>> &l = *_f.l;
      if (std::holds_alternative<
              typename List<std::pair<uint64_t, uint64_t>>::Nil>(l.v())) {
        _result = std::make_pair(List<uint64_t>::nil(), List<uint64_t>::nil());
      } else {
        const auto &[a0, a1] =
            std::get<typename List<std::pair<uint64_t, uint64_t>>::Cons>(l.v());
        const auto &[a, b] = a0;
        _stack.emplace_back(_Cont_a{a, b});
        _stack.emplace_back(_Enter{a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Cont_a>(_frame));
      uint64_t a = _f.a;
      uint64_t b = _f.b;
      std::pair<List<uint64_t>, List<uint64_t>> _rc1 = std::move(_result);
      auto [xs, ys] = _rc1;
      _result = std::make_pair(List<uint64_t>::cons(a, std::move(xs)),
                               List<uint64_t>::cons(b, std::move(ys)));
    }
  }
  return _result;
}

std::pair<List<uint64_t>, List<uint64_t>> LoopifyListPairing::swizzle(
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
  std::pair<List<uint64_t>, List<uint64_t>> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l});
  /// Loopified swizzle: _Enter -> _Cont_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<uint64_t> &l = *_f.l;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
        _result = std::make_pair(List<uint64_t>::nil(), List<uint64_t>::nil());
      } else {
        const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
        _stack.emplace_back(_Cont_Cons{a0});
        _stack.emplace_back(_Enter{a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Cont_Cons>(_frame));
      uint64_t a0 = _f.a0;
      std::pair<List<uint64_t>, List<uint64_t>> _rc1 = std::move(_result);
      auto [odds, evens] = _rc1;
      _result = std::make_pair(List<uint64_t>::cons(a0, std::move(evens)),
                               std::move(odds));
    }
  }
  return _result;
}

std::pair<List<uint64_t>, List<uint64_t>> LoopifyListPairing::partition(
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
  std::pair<List<uint64_t>, List<uint64_t>> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l});
  /// Loopified partition: _Enter -> _Cont_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<uint64_t> &l = *_f.l;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
        _result = std::make_pair(List<uint64_t>::nil(), List<uint64_t>::nil());
      } else {
        const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
        _stack.emplace_back(_Cont_Cons{a0});
        _stack.emplace_back(_Enter{a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Cont_Cons>(_frame));
      uint64_t a0 = _f.a0;
      std::pair<List<uint64_t>, List<uint64_t>> _rc1 = std::move(_result);
      auto [yes, no] = _rc1;
      if ((UINT64_C(2) ? a0 % UINT64_C(2) : a0) == UINT64_C(0)) {
        _result = std::make_pair(List<uint64_t>::cons(a0, std::move(yes)),
                                 std::move(no));
      } else {
        _result = std::make_pair(std::move(yes),
                                 List<uint64_t>::cons(a0, std::move(no)));
      }
    }
  }
  return _result;
}

List<std::pair<uint64_t, uint64_t>> LoopifyListPairing::zip_longest_fuel(
    uint64_t fuel, const List<uint64_t> &l1, const List<uint64_t> &l2,
    uint64_t default0) { /// _Enter: captures varying parameters for each
                         /// recursive call.

  struct _Enter {
    List<uint64_t> l2;
    List<uint64_t> l1;
    uint64_t fuel;
  };

  /// _Resume_Cons: saves [_s0], resumes after recursive call with _result.
  struct _Resume_Cons {
    std::decay_t<decltype(std::make_pair(std::declval<uint64_t &>(),
                                         std::declval<uint64_t &>()))>
        _s0;
  };

  /// _Resume_Cons_1: saves [_s0], resumes after recursive call with _result.
  struct _Resume_Cons_1 {
    std::decay_t<decltype(std::make_pair(std::declval<uint64_t &>(),
                                         std::declval<uint64_t &>()))>
        _s0;
  };

  /// _Resume_Nil: saves [_s0], resumes after recursive call with _result.
  struct _Resume_Nil {
    std::decay_t<decltype(std::make_pair(std::declval<uint64_t &>(),
                                         std::declval<uint64_t &>()))>
        _s0;
  };

  using _Frame =
      std::variant<_Enter, _Resume_Cons, _Resume_Cons_1, _Resume_Nil>;
  List<std::pair<uint64_t, uint64_t>> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{l2, l1, fuel});
  /// Loopified zip_longest_fuel: _Enter -> _Resume_Cons -> _Resume_Cons_1 ->
  /// _Resume_Nil.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<uint64_t> &l2 = std::move(_f.l2);
      const List<uint64_t> &l1 = std::move(_f.l1);
      uint64_t fuel = _f.fuel;
      if (fuel <= 0) {
        _result = List<std::pair<uint64_t, uint64_t>>::nil();
      } else {
        uint64_t fuel_ = fuel - 1;
        if (std::holds_alternative<typename List<uint64_t>::Nil>(l1.v())) {
          if (std::holds_alternative<typename List<uint64_t>::Nil>(l2.v())) {
            _result = List<std::pair<uint64_t, uint64_t>>::nil();
          } else {
            const auto &[a00, a10] =
                std::get<typename List<uint64_t>::Cons>(l2.v());
            _stack.emplace_back(_Resume_Cons{std::make_pair(default0, a00)});
            _stack.emplace_back(_Enter{*a10, List<uint64_t>::nil(), fuel_});
          }
        } else {
          const auto &[a0, a1] =
              std::get<typename List<uint64_t>::Cons>(l1.v());
          if (std::holds_alternative<typename List<uint64_t>::Nil>(l2.v())) {
            _stack.emplace_back(_Resume_Nil{std::make_pair(a0, default0)});
            _stack.emplace_back(_Enter{List<uint64_t>::nil(), *a1, fuel_});
          } else {
            const auto &[a00, a10] =
                std::get<typename List<uint64_t>::Cons>(l2.v());
            _stack.emplace_back(_Resume_Cons_1{std::make_pair(a0, a00)});
            _stack.emplace_back(_Enter{*a10, *a1, fuel_});
          }
        }
      }
    } else if (std::holds_alternative<_Resume_Cons>(_frame)) {
      auto _f = std::move(std::get<_Resume_Cons>(_frame));
      _result =
          List<std::pair<uint64_t, uint64_t>>::cons(_f._s0, std::move(_result));
    } else if (std::holds_alternative<_Resume_Cons_1>(_frame)) {
      auto _f = std::move(std::get<_Resume_Cons_1>(_frame));
      _result =
          List<std::pair<uint64_t, uint64_t>>::cons(_f._s0, std::move(_result));
    } else {
      auto _f = std::move(std::get<_Resume_Nil>(_frame));
      _result =
          List<std::pair<uint64_t, uint64_t>>::cons(_f._s0, std::move(_result));
    }
  }
  return _result;
}

List<std::pair<uint64_t, uint64_t>>
LoopifyListPairing::zip_longest(const List<uint64_t> &l1,
                                const List<uint64_t> &l2, uint64_t default0) {
  uint64_t len1 = l1.length();
  uint64_t len2 = l2.length();
  uint64_t maxlen;
  if (len1 < len2) {
    maxlen = len2;
  } else {
    maxlen = len1;
  }
  return zip_longest_fuel(maxlen, l1, l2, default0);
}

List<uint64_t> LoopifyListPairing::zipWith(
    const List<uint64_t> &l1,
    const List<uint64_t>
        &l2) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<uint64_t> *l2;
    const List<uint64_t> *l1;
  };

  /// _Resume_Cons: saves [_s0], resumes after recursive call with _result.
  struct _Resume_Cons {
    uint64_t _s0;
  };

  using _Frame = std::variant<_Enter, _Resume_Cons>;
  List<uint64_t> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l2, &l1});
  /// Loopified zipWith: _Enter -> _Resume_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<uint64_t> &l2 = *_f.l2;
      const List<uint64_t> &l1 = *_f.l1;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(l1.v())) {
        _result = List<uint64_t>::nil();
      } else {
        const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l1.v());
        if (std::holds_alternative<typename List<uint64_t>::Nil>(l2.v())) {
          _result = List<uint64_t>::nil();
        } else {
          const auto &[a00, a10] =
              std::get<typename List<uint64_t>::Cons>(l2.v());
          _stack.emplace_back(_Resume_Cons{(a0 + a00)});
          _stack.emplace_back(_Enter{a10.get(), a1.get()});
        }
      }
    } else {
      auto _f = std::move(std::get<_Resume_Cons>(_frame));
      _result = List<uint64_t>::cons(_f._s0, std::move(_result));
    }
  }
  return _result;
}

std::pair<List<uint64_t>, List<uint64_t>> LoopifyListPairing::split_even_odd(
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
  std::pair<List<uint64_t>, List<uint64_t>> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l});
  /// Loopified split_even_odd: _Enter -> _Cont_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<uint64_t> &l = *_f.l;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
        _result = std::make_pair(List<uint64_t>::nil(), List<uint64_t>::nil());
      } else {
        const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
        _stack.emplace_back(_Cont_Cons{a0});
        _stack.emplace_back(_Enter{a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Cont_Cons>(_frame));
      uint64_t a0 = _f.a0;
      std::pair<List<uint64_t>, List<uint64_t>> _rc1 = std::move(_result);
      auto [evens, odds] = _rc1;
      if ((UINT64_C(2) ? a0 % UINT64_C(2) : a0) == UINT64_C(0)) {
        _result = std::make_pair(List<uint64_t>::cons(a0, std::move(evens)),
                                 std::move(odds));
      } else {
        _result = std::make_pair(std::move(evens),
                                 List<uint64_t>::cons(a0, std::move(odds)));
      }
    }
  }
  return _result;
}
