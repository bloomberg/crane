#include "loopify_list_windows.h"

uint64_t LoopifyListWindows::len(
    const List<uint64_t>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<uint64_t> *l;
  };

  /// _Resume_Cons: saves [_s0], resumes after recursive call with _result.
  struct _Resume_Cons {
    decltype(UINT64_C(1)) _s0;
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
      _result = (_f._s0 + _result);
    }
  }
  return _result;
}

List<List<uint64_t>>
LoopifyListWindows::map_cons_helper(uint64_t x,
                                    const List<List<uint64_t>> &ll) {
  std::unique_ptr<List<List<uint64_t>>> _head{};
  std::unique_ptr<List<List<uint64_t>>> *_write = &_head;
  const List<List<uint64_t>> *_loop_ll = &ll;
  while (true) {
    if (std::holds_alternative<typename List<List<uint64_t>>::Nil>(
            _loop_ll->v())) {
      *_write =
          std::make_unique<List<List<uint64_t>>>(List<List<uint64_t>>::nil());
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename List<List<uint64_t>>::Cons>(_loop_ll->v());
      auto _cell = std::make_unique<List<List<uint64_t>>>(
          typename List<List<uint64_t>>::Cons(List<uint64_t>::cons(x, a0),
                                              nullptr));
      *_write = std::move(_cell);
      _write =
          &std::get<typename List<List<uint64_t>>::Cons>((*_write)->v_mut()).a1;
      _loop_ll = a1.get();
      continue;
    }
  }
  return std::move(*_head);
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
        _loop_xs = std::move(*a1);
        _loop_m = m_;
      }
    }
  }
}

std::pair<List<uint64_t>, List<uint64_t>> LoopifyListWindows::span_eq(
    uint64_t first,
    List<uint64_t>
        lst) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    List<uint64_t> lst;
  };

  /// _Cont1: saves [a0], resumes after recursive call, then processes rest.
  struct _Cont1 {
    uint64_t a0;
  };

  using _Frame = std::variant<_Enter, _Cont1>;
  std::pair<List<uint64_t>, List<uint64_t>> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{lst});
  /// Loopified span_eq: _Enter -> _Cont1.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      List<uint64_t> lst = std::move(_f.lst);
      if (std::holds_alternative<typename List<uint64_t>::Nil>(lst.v_mut())) {
        _result = std::make_pair(List<uint64_t>::nil(), List<uint64_t>::nil());
      } else {
        auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(lst.v_mut());
        if (first == a0) {
          _stack.emplace_back(_Cont1{a0});
          _stack.emplace_back(_Enter{std::move(*a1)});
        } else {
          _result = std::make_pair(List<uint64_t>::nil(), lst);
        }
      }
    } else {
      auto _f = std::move(std::get<_Cont1>(_frame));
      uint64_t a0 = _f.a0;
      const List<uint64_t> &s = _result.first;
      const List<uint64_t> &r = _result.second;
      _result = std::make_pair(List<uint64_t>::cons(std::move(a0), s), r);
    }
  }
  return _result;
}

List<uint64_t> LoopifyListWindows::differences(const List<uint64_t> &l) {
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
        *_write = std::make_unique<List<uint64_t>>(List<uint64_t>::nil());
        break;
      } else {
        auto &&_sv1 = *a1;
        if (std::holds_alternative<typename List<uint64_t>::Nil>(_sv1.v())) {
          *_write = std::make_unique<List<uint64_t>>(List<uint64_t>::nil());
          break;
        } else {
          const auto &[a01, a11] =
              std::get<typename List<uint64_t>::Cons>(_sv1.v());
          auto _cell =
              std::make_unique<List<uint64_t>>(typename List<uint64_t>::Cons(
                  (((a01 - a0) > a01 ? 0 : (a01 - a0))), nullptr));
          *_write = std::move(_cell);
          _write =
              &std::get<typename List<uint64_t>::Cons>((*_write)->v_mut()).a1;
          _loop_l = a1.get();
          continue;
        }
      }
    }
  }
  return std::move(*_head);
}

List<std::pair<uint64_t, uint64_t>>
LoopifyListWindows::sliding_pairs(const List<uint64_t> &l) {
  std::unique_ptr<List<std::pair<uint64_t, uint64_t>>> _head{};
  std::unique_ptr<List<std::pair<uint64_t, uint64_t>>> *_write = &_head;
  const List<uint64_t> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l->v())) {
      *_write = std::make_unique<List<std::pair<uint64_t, uint64_t>>>(
          List<std::pair<uint64_t, uint64_t>>::nil());
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename List<uint64_t>::Cons>(_loop_l->v());
      auto &&_sv = *a1;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(_sv.v())) {
        *_write = std::make_unique<List<std::pair<uint64_t, uint64_t>>>(
            List<std::pair<uint64_t, uint64_t>>::nil());
        break;
      } else {
        auto &&_sv1 = *a1;
        if (std::holds_alternative<typename List<uint64_t>::Nil>(_sv1.v())) {
          *_write = std::make_unique<List<std::pair<uint64_t, uint64_t>>>(
              List<std::pair<uint64_t, uint64_t>>::nil());
          break;
        } else {
          const auto &[a01, a11] =
              std::get<typename List<uint64_t>::Cons>(_sv1.v());
          auto _cell = std::make_unique<List<std::pair<uint64_t, uint64_t>>>(
              typename List<std::pair<uint64_t, uint64_t>>::Cons(
                  std::make_pair(a0, a01), nullptr));
          *_write = std::move(_cell);
          _write =
              &std::get<typename List<std::pair<uint64_t, uint64_t>>::Cons>(
                   (*_write)->v_mut())
                   .a1;
          _loop_l = a1.get();
          continue;
        }
      }
    }
  }
  return std::move(*_head);
}

List<List<uint64_t>> LoopifyListWindows::inits(
    const List<uint64_t>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<uint64_t> *l;
  };

  /// _Resume_Cons: saves [_s0, a0], resumes after recursive call with _result.
  struct _Resume_Cons {
    decltype(List<uint64_t>::nil()) _s0;
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
      _result =
          List<List<uint64_t>>::cons(_f._s0, map_cons_helper(_f.a0, _result));
    }
  }
  return _result;
}

List<List<uint64_t>> LoopifyListWindows::tails(List<uint64_t> l) {
  std::unique_ptr<List<List<uint64_t>>> _head{};
  std::unique_ptr<List<List<uint64_t>>> *_write = &_head;
  List<uint64_t> _loop_l = std::move(l);
  while (true) {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l.v_mut())) {
      *_write =
          std::make_unique<List<List<uint64_t>>>(List<List<uint64_t>>::cons(
              List<uint64_t>::nil(), List<List<uint64_t>>::nil()));
      break;
    } else {
      auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(_loop_l.v_mut());
      auto _cell = std::make_unique<List<List<uint64_t>>>(
          typename List<List<uint64_t>>::Cons(_loop_l, nullptr));
      *_write = std::move(_cell);
      _write =
          &std::get<typename List<List<uint64_t>>::Cons>((*_write)->v_mut()).a1;
      _loop_l = std::move(*a1);
      continue;
    }
  }
  return std::move(*_head);
}

List<uint64_t> LoopifyListWindows::take(uint64_t n, const List<uint64_t> &l) {
  std::unique_ptr<List<uint64_t>> _head{};
  std::unique_ptr<List<uint64_t>> *_write = &_head;
  const List<uint64_t> *_loop_l = &l;
  uint64_t _loop_n = std::move(n);
  while (true) {
    if (_loop_n <= 0) {
      *_write = std::make_unique<List<uint64_t>>(List<uint64_t>::nil());
      break;
    } else {
      uint64_t n_ = _loop_n - 1;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l->v())) {
        *_write = std::make_unique<List<uint64_t>>(List<uint64_t>::nil());
        break;
      } else {
        const auto &[a0, a1] =
            std::get<typename List<uint64_t>::Cons>(_loop_l->v());
        auto _cell = std::make_unique<List<uint64_t>>(
            typename List<uint64_t>::Cons(a0, nullptr));
        *_write = std::move(_cell);
        _write =
            &std::get<typename List<uint64_t>::Cons>((*_write)->v_mut()).a1;
        _loop_l = a1.get();
        _loop_n = n_;
        continue;
      }
    }
  }
  return std::move(*_head);
}

List<List<uint64_t>> LoopifyListWindows::windows_fuel(uint64_t fuel, uint64_t n,
                                                      const List<uint64_t> &l) {
  std::unique_ptr<List<List<uint64_t>>> _head{};
  std::unique_ptr<List<List<uint64_t>>> *_write = &_head;
  const List<uint64_t> *_loop_l = &l;
  uint64_t _loop_fuel = std::move(fuel);
  while (true) {
    if (_loop_fuel <= 0) {
      *_write =
          std::make_unique<List<List<uint64_t>>>(List<List<uint64_t>>::nil());
      break;
    } else {
      uint64_t fuel_ = _loop_fuel - 1;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l->v())) {
        *_write =
            std::make_unique<List<List<uint64_t>>>(List<List<uint64_t>>::nil());
        break;
      } else {
        const auto &[a0, a1] =
            std::get<typename List<uint64_t>::Cons>(_loop_l->v());
        if (len(*_loop_l) < n) {
          *_write = std::make_unique<List<List<uint64_t>>>(
              List<List<uint64_t>>::nil());
          break;
        } else {
          auto _cell = std::make_unique<List<List<uint64_t>>>(
              typename List<List<uint64_t>>::Cons(take(n, *_loop_l), nullptr));
          *_write = std::move(_cell);
          _write =
              &std::get<typename List<List<uint64_t>>::Cons>((*_write)->v_mut())
                   .a1;
          _loop_l = a1.get();
          _loop_fuel = fuel_;
          continue;
        }
      }
    }
  }
  return std::move(*_head);
}

List<List<uint64_t>> LoopifyListWindows::windows(uint64_t n,
                                                 const List<uint64_t> &l) {
  return windows_fuel(len(l), n, l);
}

List<List<uint64_t>> LoopifyListWindows::chunks_fuel(uint64_t fuel, uint64_t n,
                                                     const List<uint64_t> &l) {
  std::unique_ptr<List<List<uint64_t>>> _head{};
  std::unique_ptr<List<List<uint64_t>>> *_write = &_head;
  List<uint64_t> _loop_l = l;
  uint64_t _loop_fuel = std::move(fuel);
  while (true) {
    if (_loop_fuel <= 0) {
      *_write =
          std::make_unique<List<List<uint64_t>>>(List<List<uint64_t>>::nil());
      break;
    } else {
      uint64_t fuel_ = _loop_fuel - 1;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l.v())) {
        *_write =
            std::make_unique<List<List<uint64_t>>>(List<List<uint64_t>>::nil());
        break;
      } else {
        List<uint64_t> chunk = take(n, _loop_l);
        List<uint64_t> rest = drop(n, _loop_l);
        auto _cell = std::make_unique<List<List<uint64_t>>>(
            typename List<List<uint64_t>>::Cons(std::move(chunk), nullptr));
        *_write = std::move(_cell);
        _write =
            &std::get<typename List<List<uint64_t>>::Cons>((*_write)->v_mut())
                 .a1;
        _loop_l = std::move(rest);
        _loop_fuel = fuel_;
        continue;
      }
    }
  }
  return std::move(*_head);
}

List<List<uint64_t>> LoopifyListWindows::chunks(uint64_t n,
                                                const List<uint64_t> &l) {
  return chunks_fuel(len(l), n, l);
}

List<List<uint64_t>> LoopifyListWindows::group_fuel(uint64_t fuel,
                                                    const List<uint64_t> &l) {
  std::unique_ptr<List<List<uint64_t>>> _head{};
  std::unique_ptr<List<List<uint64_t>>> *_write = &_head;
  List<uint64_t> _loop_l = l;
  uint64_t _loop_fuel = std::move(fuel);
  while (true) {
    if (_loop_fuel <= 0) {
      *_write =
          std::make_unique<List<List<uint64_t>>>(List<List<uint64_t>>::nil());
      break;
    } else {
      uint64_t fuel_ = _loop_fuel - 1;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l.v())) {
        *_write =
            std::make_unique<List<List<uint64_t>>>(List<List<uint64_t>>::nil());
        break;
      } else {
        const auto &[a0, a1] =
            std::get<typename List<uint64_t>::Cons>(_loop_l.v());
        auto _cs = span_eq(a0, *a1);
        const List<uint64_t> &same = _cs.first;
        const List<uint64_t> &rest = _cs.second;
        auto _cell = std::make_unique<List<List<uint64_t>>>(
            typename List<List<uint64_t>>::Cons(List<uint64_t>::cons(a0, same),
                                                nullptr));
        *_write = std::move(_cell);
        _write =
            &std::get<typename List<List<uint64_t>>::Cons>((*_write)->v_mut())
                 .a1;
        _loop_l = rest;
        _loop_fuel = fuel_;
        continue;
      }
    }
  }
  return std::move(*_head);
}

List<List<uint64_t>> LoopifyListWindows::group(const List<uint64_t> &l) {
  return group_fuel(len(l), l);
}
