#include "loopify_strings.h"

List<uint64_t> LoopifyStrings::append(const List<uint64_t> &l1,
                                      List<uint64_t> l2) {
  std::unique_ptr<List<uint64_t>> _head{};
  std::unique_ptr<List<uint64_t>> *_write = &_head;
  List<uint64_t> _loop_l2 = std::move(l2);
  const List<uint64_t> *_loop_l1 = &l1;
  while (true) {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l1->v())) {
      *_write = std::make_unique<List<uint64_t>>(std::move(_loop_l2));
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename List<uint64_t>::Cons>(_loop_l1->v());
      auto _cell = std::make_unique<List<uint64_t>>(
          typename List<uint64_t>::Cons(a0, nullptr));
      *_write = std::move(_cell);
      _write = &std::get<typename List<uint64_t>::Cons>((*_write)->v_mut()).a1;
      _loop_l1 = a1.get();
      continue;
    }
  }
  return std::move(*_head);
}

List<uint64_t> LoopifyStrings::join_with(uint64_t sep,
                                         const List<uint64_t> &l) {
  std::unique_ptr<List<uint64_t>> _head{};
  std::unique_ptr<List<uint64_t>> *_write = &_head;
  const List<uint64_t> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l->v())) {
      *_write = std::make_unique<List<uint64_t>>(List<uint64_t>::nil());
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename List<uint64_t>::Cons>(_loop_l->v());
      auto &&_sv = *a1;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(_sv.v())) {
        *_write = std::make_unique<List<uint64_t>>(
            List<uint64_t>::cons(a0, List<uint64_t>::nil()));
        break;
      } else {
        auto _cell = std::make_unique<List<uint64_t>>(
            typename List<uint64_t>::Cons(a0, nullptr));
        auto _cell1 = std::make_unique<List<uint64_t>>(
            typename List<uint64_t>::Cons(sep, nullptr));
        std::get<typename List<uint64_t>::Cons>(_cell->v_mut()).a1 =
            std::move(_cell1);
        *_write = std::move(_cell);
        _write =
            &std::get<typename List<uint64_t>::Cons>(
                 std::get<typename List<uint64_t>::Cons>((*_write)->v_mut())
                     .a1->v_mut())
                 .a1;
        _loop_l = a1.get();
        continue;
      }
    }
  }
  return std::move(*_head);
}

List<uint64_t> LoopifyStrings::repeat_string(
    const List<uint64_t> &s,
    uint64_t
        n) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    uint64_t n;
  };

  /// _Resume_n_: saves [s], resumes after recursive call with _result.
  struct _Resume_n_ {
    List<uint64_t> s;
  };

  using _Frame = std::variant<_Enter, _Resume_n_>;
  List<uint64_t> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{n});
  /// Loopified repeat_string: _Enter -> _Resume_n_.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      uint64_t n = _f.n;
      if (n <= 0) {
        _result = List<uint64_t>::nil();
      } else {
        uint64_t n_ = n - 1;
        _stack.emplace_back(_Resume_n_{s});
        _stack.emplace_back(_Enter{n_});
      }
    } else {
      auto _f = std::move(std::get<_Resume_n_>(_frame));
      _result = append(_f.s, _result);
    }
  }
  return _result;
}

List<uint64_t> LoopifyStrings::repeat_with_sep(
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
        uint64_t n_ = n - 1;
        if (n_ <= 0) {
          _result = std::move(s);
        } else {
          uint64_t _x = n_ - 1;
          _stack.emplace_back(_Resume__x{s, sep});
          _stack.emplace_back(_Enter{n_});
        }
      }
    } else {
      auto _f = std::move(std::get<_Resume__x>(_frame));
      _result = append(_f.s, append(_f.sep, _result));
    }
  }
  return _result;
}

List<uint64_t> LoopifyStrings::string_chain_fuel(
    uint64_t fuel, const List<uint64_t> &s, uint64_t n,
    const List<uint64_t> &sep,
    const List<uint64_t> &end_marker) { /// _Enter: captures varying parameters
                                        /// for each recursive call.

  struct _Enter {
    uint64_t n;
    uint64_t fuel;
  };

  /// _Resume1: saves [s, sep, end_marker], resumes after recursive call with
  /// _result.
  struct _Resume1 {
    List<uint64_t> s;
    List<uint64_t> sep;
    List<uint64_t> end_marker;
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
        uint64_t fuel_ = fuel - 1;
        if (n <= UINT64_C(0)) {
          _result = List<uint64_t>::nil();
        } else {
          _stack.emplace_back(_Resume1{s, sep, end_marker});
          _stack.emplace_back(
              _Enter{(((n - UINT64_C(1)) > n ? 0 : (n - UINT64_C(1)))), fuel_});
        }
      }
    } else {
      auto _f = std::move(std::get<_Resume1>(_frame));
      _result = append(_f.s, append(_f.sep, append(_result, _f.end_marker)));
    }
  }
  return _result;
}

List<uint64_t> LoopifyStrings::string_chain(const List<uint64_t> &s, uint64_t n,
                                            const List<uint64_t> &sep,
                                            const List<uint64_t> &end_marker) {
  return string_chain_fuel(n, s, n, sep, end_marker);
}

List<uint64_t> LoopifyStrings::reverse(
    const List<uint64_t>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<uint64_t> *l;
  };

  /// _Resume_Cons: saves [_s0], resumes after recursive call with _result.
  struct _Resume_Cons {
    decltype(List<uint64_t>::cons(std::declval<uint64_t &>(),
                                  List<uint64_t>::nil())) _s0;
  };

  using _Frame = std::variant<_Enter, _Resume_Cons>;
  List<uint64_t> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l});
  /// Loopified reverse: _Enter -> _Resume_Cons.
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
        _stack.emplace_back(
            _Resume_Cons{List<uint64_t>::cons(a0, List<uint64_t>::nil())});
        _stack.emplace_back(_Enter{a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Resume_Cons>(_frame));
      _result = append(_result, _f._s0);
    }
  }
  return _result;
}

bool LoopifyStrings::list_eq(
    const List<uint64_t> &l1,
    const List<uint64_t>
        &l2) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<uint64_t> *l2;
    const List<uint64_t> *l1;
  };

  /// _Resume_Cons: saves [_s0], resumes after recursive call with _result.
  struct _Resume_Cons {
    decltype(std::declval<uint64_t &>() == std::declval<uint64_t &>()) _s0;
  };

  using _Frame = std::variant<_Enter, _Resume_Cons>;
  bool _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l2, &l1});
  /// Loopified list_eq: _Enter -> _Resume_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<uint64_t> &l2 = *_f.l2;
      const List<uint64_t> &l1 = *_f.l1;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(l1.v())) {
        if (std::holds_alternative<typename List<uint64_t>::Nil>(l2.v())) {
          _result = true;
        } else {
          _result = false;
        }
      } else {
        const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l1.v());
        if (std::holds_alternative<typename List<uint64_t>::Nil>(l2.v())) {
          _result = false;
        } else {
          const auto &[a00, a10] =
              std::get<typename List<uint64_t>::Cons>(l2.v());
          _stack.emplace_back(_Resume_Cons{a0 == a00});
          _stack.emplace_back(_Enter{a10.get(), a1.get()});
        }
      }
    } else {
      auto _f = std::move(std::get<_Resume_Cons>(_frame));
      _result = (_f._s0 && _result);
    }
  }
  return _result;
}

bool LoopifyStrings::is_palindrome(const List<uint64_t> &l) {
  return list_eq(l, reverse(l));
}

List<uint64_t> LoopifyStrings::intersperse(uint64_t sep,
                                           const List<uint64_t> &l) {
  std::unique_ptr<List<uint64_t>> _head{};
  std::unique_ptr<List<uint64_t>> *_write = &_head;
  const List<uint64_t> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l->v())) {
      *_write = std::make_unique<List<uint64_t>>(List<uint64_t>::nil());
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename List<uint64_t>::Cons>(_loop_l->v());
      auto &&_sv = *a1;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(_sv.v())) {
        *_write = std::make_unique<List<uint64_t>>(
            List<uint64_t>::cons(a0, List<uint64_t>::nil()));
        break;
      } else {
        auto _cell = std::make_unique<List<uint64_t>>(
            typename List<uint64_t>::Cons(a0, nullptr));
        auto _cell1 = std::make_unique<List<uint64_t>>(
            typename List<uint64_t>::Cons(sep, nullptr));
        std::get<typename List<uint64_t>::Cons>(_cell->v_mut()).a1 =
            std::move(_cell1);
        *_write = std::move(_cell);
        _write =
            &std::get<typename List<uint64_t>::Cons>(
                 std::get<typename List<uint64_t>::Cons>((*_write)->v_mut())
                     .a1->v_mut())
                 .a1;
        _loop_l = a1.get();
        continue;
      }
    }
  }
  return std::move(*_head);
}

List<uint64_t> LoopifyStrings::intercalate(
    const List<uint64_t> &sep,
    const List<List<uint64_t>>
        &ll) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<List<uint64_t>> *ll;
  };

  /// _Resume_Cons: saves [a0, sep], resumes after recursive call with _result.
  struct _Resume_Cons {
    List<uint64_t> a0;
    List<uint64_t> sep;
  };

  using _Frame = std::variant<_Enter, _Resume_Cons>;
  List<uint64_t> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&ll});
  /// Loopified intercalate: _Enter -> _Resume_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<List<uint64_t>> &ll = *_f.ll;
      if (std::holds_alternative<typename List<List<uint64_t>>::Nil>(ll.v())) {
        _result = List<uint64_t>::nil();
      } else {
        const auto &[a0, a1] =
            std::get<typename List<List<uint64_t>>::Cons>(ll.v());
        auto &&_sv = *a1;
        if (std::holds_alternative<typename List<List<uint64_t>>::Nil>(
                _sv.v())) {
          _result = std::move(a0);
        } else {
          _stack.emplace_back(_Resume_Cons{a0, sep});
          _stack.emplace_back(_Enter{a1.get()});
        }
      }
    } else {
      auto _f = std::move(std::get<_Resume_Cons>(_frame));
      _result = append(_f.a0, append(_f.sep, _result));
    }
  }
  return _result;
}

List<uint64_t> LoopifyStrings::replicate(uint64_t n, uint64_t x) {
  std::unique_ptr<List<uint64_t>> _head{};
  std::unique_ptr<List<uint64_t>> *_write = &_head;
  uint64_t _loop_n = std::move(n);
  while (true) {
    if (_loop_n <= 0) {
      *_write = std::make_unique<List<uint64_t>>(List<uint64_t>::nil());
      break;
    } else {
      uint64_t n_ = _loop_n - 1;
      auto _cell = std::make_unique<List<uint64_t>>(
          typename List<uint64_t>::Cons(x, nullptr));
      *_write = std::move(_cell);
      _write = &std::get<typename List<uint64_t>::Cons>((*_write)->v_mut()).a1;
      _loop_n = n_;
      continue;
    }
  }
  return std::move(*_head);
}

List<std::pair<uint64_t, uint64_t>>
LoopifyStrings::run_length_aux(uint64_t current, uint64_t count,
                               const List<uint64_t> &l) {
  std::unique_ptr<List<std::pair<uint64_t, uint64_t>>> _head{};
  std::unique_ptr<List<std::pair<uint64_t, uint64_t>>> *_write = &_head;
  const List<uint64_t> *_loop_l = &l;
  uint64_t _loop_count = std::move(count);
  uint64_t _loop_current = std::move(current);
  while (true) {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l->v())) {
      if (_loop_count == UINT64_C(0)) {
        *_write = std::make_unique<List<std::pair<uint64_t, uint64_t>>>(
            List<std::pair<uint64_t, uint64_t>>::nil());
        break;
      } else {
        *_write = std::make_unique<List<std::pair<uint64_t, uint64_t>>>(
            List<std::pair<uint64_t, uint64_t>>::cons(
                std::make_pair(_loop_current, _loop_count),
                List<std::pair<uint64_t, uint64_t>>::nil()));
        break;
      }
    } else {
      const auto &[a0, a1] =
          std::get<typename List<uint64_t>::Cons>(_loop_l->v());
      if (a0 == _loop_current) {
        _loop_l = a1.get();
        _loop_count = (_loop_count + UINT64_C(1));
        continue;
      } else {
        if (_loop_count == UINT64_C(0)) {
          _loop_l = a1.get();
          _loop_count = UINT64_C(1);
          _loop_current = a0;
          continue;
        } else {
          auto _cell = std::make_unique<List<std::pair<uint64_t, uint64_t>>>(
              typename List<std::pair<uint64_t, uint64_t>>::Cons(
                  std::make_pair(_loop_current, _loop_count), nullptr));
          *_write = std::move(_cell);
          _write =
              &std::get<typename List<std::pair<uint64_t, uint64_t>>::Cons>(
                   (*_write)->v_mut())
                   .a1;
          _loop_l = a1.get();
          _loop_count = UINT64_C(1);
          _loop_current = a0;
          continue;
        }
      }
    }
  }
  return std::move(*_head);
}

List<std::pair<uint64_t, uint64_t>>
LoopifyStrings::run_length_encode(const List<uint64_t> &l) {
  if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
    return List<std::pair<uint64_t, uint64_t>>::nil();
  } else {
    const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
    return run_length_aux(a0, UINT64_C(1), *a1);
  }
}
