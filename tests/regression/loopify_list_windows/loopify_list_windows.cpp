#include "loopify_list_windows.h"

unsigned int LoopifyListWindows::len(
    const List<unsigned int>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<unsigned int> *l;
  };

  /// _Resume_Cons: saves [_s0], resumes after recursive call with _result.
  struct _Resume_Cons {
    decltype(1u) _s0;
  };

  using _Frame = std::variant<_Enter, _Resume_Cons>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l});
  /// Loopified len: _Enter -> _Resume_Cons.
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
        _stack.emplace_back(_Resume_Cons{1u});
        _stack.emplace_back(_Enter{a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Resume_Cons>(_frame));
      _result = (_f._s0 + _result);
    }
  }
  return _result;
}

List<List<unsigned int>>
LoopifyListWindows::map_cons_helper(unsigned int x,
                                    const List<List<unsigned int>> &ll) {
  std::unique_ptr<List<List<unsigned int>>> _head{};
  std::unique_ptr<List<List<unsigned int>>> *_write = &_head;
  const List<List<unsigned int>> *_loop_ll = &ll;
  while (true) {
    if (std::holds_alternative<typename List<List<unsigned int>>::Nil>(
            _loop_ll->v())) {
      *_write = std::make_unique<List<List<unsigned int>>>(
          List<List<unsigned int>>::nil());
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename List<List<unsigned int>>::Cons>(_loop_ll->v());
      auto _cell = std::make_unique<List<List<unsigned int>>>(
          typename List<List<unsigned int>>::Cons(
              List<unsigned int>::cons(x, a0), nullptr));
      *_write = std::move(_cell);
      _write =
          &std::get<typename List<List<unsigned int>>::Cons>((*_write)->v_mut())
               .a1;
      _loop_ll = a1.get();
      continue;
    }
  }
  return std::move(*_head);
}

List<unsigned int> LoopifyListWindows::drop(unsigned int m,
                                            List<unsigned int> xs) {
  List<unsigned int> _result;
  List<unsigned int> _loop_xs = std::move(xs);
  unsigned int _loop_m = std::move(m);
  while (true) {
    if (_loop_m <= 0) {
      _result = std::move(_loop_xs);
      break;
    } else {
      unsigned int m_ = _loop_m - 1;
      if (std::holds_alternative<typename List<unsigned int>::Nil>(
              _loop_xs.v_mut())) {
        _result = List<unsigned int>::nil();
        break;
      } else {
        auto &[a0, a1] =
            std::get<typename List<unsigned int>::Cons>(_loop_xs.v_mut());
        _loop_xs = std::move(*a1);
        _loop_m = m_;
      }
    }
  }
  return _result;
}

std::pair<List<unsigned int>, List<unsigned int>> LoopifyListWindows::span_eq(
    unsigned int first,
    List<unsigned int>
        lst) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    List<unsigned int> lst;
  };

  /// _Cont1: saves [a0], resumes after recursive call, then processes rest.
  struct _Cont1 {
    unsigned int a0;
  };

  using _Frame = std::variant<_Enter, _Cont1>;
  std::pair<List<unsigned int>, List<unsigned int>> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{lst});
  /// Loopified span_eq: _Enter -> _Cont1.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      List<unsigned int> lst = std::move(_f.lst);
      if (std::holds_alternative<typename List<unsigned int>::Nil>(
              lst.v_mut())) {
        _result = std::make_pair(List<unsigned int>::nil(),
                                 List<unsigned int>::nil());
      } else {
        auto &[a0, a1] =
            std::get<typename List<unsigned int>::Cons>(lst.v_mut());
        if (first == a0) {
          _stack.emplace_back(_Cont1{a0});
          _stack.emplace_back(_Enter{std::move(*a1)});
        } else {
          _result = std::make_pair(List<unsigned int>::nil(), lst);
        }
      }
    } else {
      auto _f = std::move(std::get<_Cont1>(_frame));
      unsigned int a0 = _f.a0;
      const List<unsigned int> &s = _result.first;
      const List<unsigned int> &r = _result.second;
      _result = std::make_pair(List<unsigned int>::cons(std::move(a0), s), r);
    }
  }
  return _result;
}

List<unsigned int>
LoopifyListWindows::differences(const List<unsigned int> &l) {
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
      auto &&_sv = *a1;
      if (std::holds_alternative<typename List<unsigned int>::Nil>(_sv.v())) {
        *_write =
            std::make_unique<List<unsigned int>>(List<unsigned int>::nil());
        break;
      } else {
        auto &&_sv1 = *a1;
        if (std::holds_alternative<typename List<unsigned int>::Nil>(
                _sv1.v())) {
          *_write =
              std::make_unique<List<unsigned int>>(List<unsigned int>::nil());
          break;
        } else {
          const auto &[a01, a11] =
              std::get<typename List<unsigned int>::Cons>(_sv1.v());
          auto _cell = std::make_unique<List<unsigned int>>(
              typename List<unsigned int>::Cons(
                  (((a01 - a0) > a01 ? 0 : (a01 - a0))), nullptr));
          *_write = std::move(_cell);
          _write =
              &std::get<typename List<unsigned int>::Cons>((*_write)->v_mut())
                   .a1;
          _loop_l = a1.get();
          continue;
        }
      }
    }
  }
  return std::move(*_head);
}

List<std::pair<unsigned int, unsigned int>>
LoopifyListWindows::sliding_pairs(const List<unsigned int> &l) {
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
      auto &&_sv = *a1;
      if (std::holds_alternative<typename List<unsigned int>::Nil>(_sv.v())) {
        *_write = std::make_unique<List<std::pair<unsigned int, unsigned int>>>(
            List<std::pair<unsigned int, unsigned int>>::nil());
        break;
      } else {
        auto &&_sv1 = *a1;
        if (std::holds_alternative<typename List<unsigned int>::Nil>(
                _sv1.v())) {
          *_write =
              std::make_unique<List<std::pair<unsigned int, unsigned int>>>(
                  List<std::pair<unsigned int, unsigned int>>::nil());
          break;
        } else {
          const auto &[a01, a11] =
              std::get<typename List<unsigned int>::Cons>(_sv1.v());
          auto _cell =
              std::make_unique<List<std::pair<unsigned int, unsigned int>>>(
                  typename List<std::pair<unsigned int, unsigned int>>::Cons(
                      std::make_pair(a0, a01), nullptr));
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
  }
  return std::move(*_head);
}

List<List<unsigned int>> LoopifyListWindows::inits(
    const List<unsigned int>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<unsigned int> *l;
  };

  /// _Resume_Cons: saves [_s0, a0], resumes after recursive call with _result.
  struct _Resume_Cons {
    decltype(List<unsigned int>::nil()) _s0;
    unsigned int a0;
  };

  using _Frame = std::variant<_Enter, _Resume_Cons>;
  List<List<unsigned int>> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l});
  /// Loopified inits: _Enter -> _Resume_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<unsigned int> &l = *_f.l;
      if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
        _result = List<List<unsigned int>>::cons(
            List<unsigned int>::nil(), List<List<unsigned int>>::nil());
      } else {
        const auto &[a0, a1] =
            std::get<typename List<unsigned int>::Cons>(l.v());
        _stack.emplace_back(_Resume_Cons{List<unsigned int>::nil(), a0});
        _stack.emplace_back(_Enter{a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Resume_Cons>(_frame));
      _result = List<List<unsigned int>>::cons(_f._s0,
                                               map_cons_helper(_f.a0, _result));
    }
  }
  return _result;
}

List<List<unsigned int>> LoopifyListWindows::tails(List<unsigned int> l) {
  std::unique_ptr<List<List<unsigned int>>> _head{};
  std::unique_ptr<List<List<unsigned int>>> *_write = &_head;
  List<unsigned int> _loop_l = std::move(l);
  while (true) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(
            _loop_l.v_mut())) {
      *_write = std::make_unique<List<List<unsigned int>>>(
          List<List<unsigned int>>::cons(List<unsigned int>::nil(),
                                         List<List<unsigned int>>::nil()));
      break;
    } else {
      auto &[a0, a1] =
          std::get<typename List<unsigned int>::Cons>(_loop_l.v_mut());
      auto _cell = std::make_unique<List<List<unsigned int>>>(
          typename List<List<unsigned int>>::Cons(_loop_l, nullptr));
      *_write = std::move(_cell);
      _write =
          &std::get<typename List<List<unsigned int>>::Cons>((*_write)->v_mut())
               .a1;
      _loop_l = std::move(*a1);
      continue;
    }
  }
  return std::move(*_head);
}

List<unsigned int> LoopifyListWindows::take(unsigned int n,
                                            const List<unsigned int> &l) {
  std::unique_ptr<List<unsigned int>> _head{};
  std::unique_ptr<List<unsigned int>> *_write = &_head;
  const List<unsigned int> *_loop_l = &l;
  unsigned int _loop_n = std::move(n);
  while (true) {
    if (_loop_n <= 0) {
      *_write = std::make_unique<List<unsigned int>>(List<unsigned int>::nil());
      break;
    } else {
      unsigned int n_ = _loop_n - 1;
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
        _loop_n = n_;
        continue;
      }
    }
  }
  return std::move(*_head);
}

List<List<unsigned int>>
LoopifyListWindows::windows_fuel(unsigned int fuel, unsigned int n,
                                 const List<unsigned int> &l) {
  std::unique_ptr<List<List<unsigned int>>> _head{};
  std::unique_ptr<List<List<unsigned int>>> *_write = &_head;
  const List<unsigned int> *_loop_l = &l;
  unsigned int _loop_fuel = std::move(fuel);
  while (true) {
    if (_loop_fuel <= 0) {
      *_write = std::make_unique<List<List<unsigned int>>>(
          List<List<unsigned int>>::nil());
      break;
    } else {
      unsigned int fuel_ = _loop_fuel - 1;
      if (std::holds_alternative<typename List<unsigned int>::Nil>(
              _loop_l->v())) {
        *_write = std::make_unique<List<List<unsigned int>>>(
            List<List<unsigned int>>::nil());
        break;
      } else {
        const auto &[a0, a1] =
            std::get<typename List<unsigned int>::Cons>(_loop_l->v());
        if (len(*_loop_l) < n) {
          *_write = std::make_unique<List<List<unsigned int>>>(
              List<List<unsigned int>>::nil());
          break;
        } else {
          auto _cell = std::make_unique<List<List<unsigned int>>>(
              typename List<List<unsigned int>>::Cons(take(n, *_loop_l),
                                                      nullptr));
          *_write = std::move(_cell);
          _write = &std::get<typename List<List<unsigned int>>::Cons>(
                        (*_write)->v_mut())
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

List<List<unsigned int>>
LoopifyListWindows::windows(unsigned int n, const List<unsigned int> &l) {
  return windows_fuel(len(l), n, l);
}

List<List<unsigned int>>
LoopifyListWindows::chunks_fuel(unsigned int fuel, unsigned int n,
                                const List<unsigned int> &l) {
  std::unique_ptr<List<List<unsigned int>>> _head{};
  std::unique_ptr<List<List<unsigned int>>> *_write = &_head;
  List<unsigned int> _loop_l = l;
  unsigned int _loop_fuel = std::move(fuel);
  while (true) {
    if (_loop_fuel <= 0) {
      *_write = std::make_unique<List<List<unsigned int>>>(
          List<List<unsigned int>>::nil());
      break;
    } else {
      unsigned int fuel_ = _loop_fuel - 1;
      if (std::holds_alternative<typename List<unsigned int>::Nil>(
              _loop_l.v())) {
        *_write = std::make_unique<List<List<unsigned int>>>(
            List<List<unsigned int>>::nil());
        break;
      } else {
        List<unsigned int> chunk = take(n, _loop_l);
        List<unsigned int> rest = drop(n, _loop_l);
        auto _cell = std::make_unique<List<List<unsigned int>>>(
            typename List<List<unsigned int>>::Cons(std::move(chunk), nullptr));
        *_write = std::move(_cell);
        _write = &std::get<typename List<List<unsigned int>>::Cons>(
                      (*_write)->v_mut())
                      .a1;
        _loop_l = std::move(rest);
        _loop_fuel = fuel_;
        continue;
      }
    }
  }
  return std::move(*_head);
}

List<List<unsigned int>>
LoopifyListWindows::chunks(unsigned int n, const List<unsigned int> &l) {
  return chunks_fuel(len(l), n, l);
}

List<List<unsigned int>>
LoopifyListWindows::group_fuel(unsigned int fuel, const List<unsigned int> &l) {
  std::unique_ptr<List<List<unsigned int>>> _head{};
  std::unique_ptr<List<List<unsigned int>>> *_write = &_head;
  List<unsigned int> _loop_l = l;
  unsigned int _loop_fuel = std::move(fuel);
  while (true) {
    if (_loop_fuel <= 0) {
      *_write = std::make_unique<List<List<unsigned int>>>(
          List<List<unsigned int>>::nil());
      break;
    } else {
      unsigned int fuel_ = _loop_fuel - 1;
      if (std::holds_alternative<typename List<unsigned int>::Nil>(
              _loop_l.v())) {
        *_write = std::make_unique<List<List<unsigned int>>>(
            List<List<unsigned int>>::nil());
        break;
      } else {
        const auto &[a0, a1] =
            std::get<typename List<unsigned int>::Cons>(_loop_l.v());
        auto _cs = span_eq(a0, *a1);
        const List<unsigned int> &same = _cs.first;
        const List<unsigned int> &rest = _cs.second;
        auto _cell = std::make_unique<List<List<unsigned int>>>(
            typename List<List<unsigned int>>::Cons(
                List<unsigned int>::cons(a0, same), nullptr));
        *_write = std::move(_cell);
        _write = &std::get<typename List<List<unsigned int>>::Cons>(
                      (*_write)->v_mut())
                      .a1;
        _loop_l = rest;
        _loop_fuel = fuel_;
        continue;
      }
    }
  }
  return std::move(*_head);
}

List<List<unsigned int>>
LoopifyListWindows::group(const List<unsigned int> &l) {
  return group_fuel(len(l), l);
}
