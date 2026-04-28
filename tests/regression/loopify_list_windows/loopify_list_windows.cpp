#include <loopify_list_windows.h>

__attribute__((pure)) unsigned int
LoopifyListWindows::len(const List<unsigned int> &l) {
  struct _Enter {
    const List<unsigned int> l;
  };

  struct _Call1 {
    decltype(1u) _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{l});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<unsigned int> l = _f.l;
      if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
        _result = 0u;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<unsigned int>::Cons>(l.v());
        _stack.emplace_back(_Call1{1u});
        _stack.emplace_back(_Enter{*(d_a1)});
      }
    } else {
      auto _f = std::move(std::get<_Call1>(_frame));
      _result = (_f._s0 + _result);
    }
  }
  return _result;
}

__attribute__((pure)) List<List<unsigned int>>
LoopifyListWindows::map_cons_helper(unsigned int x,
                                    const List<List<unsigned int>> &ll) {
  std::unique_ptr<List<List<unsigned int>>> _head{};
  std::unique_ptr<List<List<unsigned int>>> *_write = &_head;
  List<List<unsigned int>> _loop_ll = ll;
  while (true) {
    if (std::holds_alternative<typename List<List<unsigned int>>::Nil>(
            _loop_ll.v())) {
      *(_write) = std::make_unique<List<List<unsigned int>>>(
          List<List<unsigned int>>::nil());
      break;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<List<unsigned int>>::Cons>(_loop_ll.v());
      auto _cell = std::make_unique<List<List<unsigned int>>>(
          typename List<List<unsigned int>>::Cons(
              List<unsigned int>::cons(x, d_a0), nullptr));
      *(_write) = std::move(_cell);
      _write =
          &std::get<typename List<List<unsigned int>>::Cons>((*_write)->v_mut())
               .d_a1;
      _loop_ll = *(d_a1);
      continue;
    }
  }
  return std::move(*(_head));
}

__attribute__((pure)) List<unsigned int>
LoopifyListWindows::drop(const unsigned int &m, List<unsigned int> xs) {
  List<unsigned int> _result;
  List<unsigned int> _loop_xs = std::move(xs);
  unsigned int _loop_m = m;
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
        auto &[d_a0, d_a1] =
            std::get<typename List<unsigned int>::Cons>(_loop_xs.v_mut());
        List<unsigned int> _next_xs = *(d_a1);
        unsigned int _next_m = m_;
        _loop_xs = std::move(_next_xs);
        _loop_m = std::move(_next_m);
      }
    }
  }
  return _result;
}

__attribute__((pure)) std::pair<List<unsigned int>, List<unsigned int>>
LoopifyListWindows::span_eq(const unsigned int &first, List<unsigned int> lst) {
  struct _Enter {
    List<unsigned int> lst;
  };

  struct _Call1 {
    unsigned int _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::pair<List<unsigned int>, List<unsigned int>> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{lst});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      List<unsigned int> lst = _f.lst;
      if (std::holds_alternative<typename List<unsigned int>::Nil>(
              lst.v_mut())) {
        _result = std::make_pair(List<unsigned int>::nil(),
                                 List<unsigned int>::nil());
      } else {
        auto &[d_a0, d_a1] =
            std::get<typename List<unsigned int>::Cons>(lst.v_mut());
        if (first == d_a0) {
          _stack.emplace_back(_Call1{d_a0});
          _stack.emplace_back(_Enter{*(d_a1)});
        } else {
          _result = std::make_pair(List<unsigned int>::nil(), lst);
        }
      }
    } else {
      auto _f = std::move(std::get<_Call1>(_frame));
      unsigned int d_a0 = _f._s0;
      const List<unsigned int> &s = _result.first;
      const List<unsigned int> &r = _result.second;
      _result = std::make_pair(List<unsigned int>::cons(d_a0, s), r);
    }
  }
  return _result;
}

__attribute__((pure)) List<unsigned int>
LoopifyListWindows::differences(const List<unsigned int> &l) {
  std::unique_ptr<List<unsigned int>> _head{};
  std::unique_ptr<List<unsigned int>> *_write = &_head;
  List<unsigned int> _loop_l = l;
  while (true) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(_loop_l.v())) {
      *(_write) =
          std::make_unique<List<unsigned int>>(List<unsigned int>::nil());
      break;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<unsigned int>::Cons>(_loop_l.v());
      auto &&_sv = *(d_a1);
      if (std::holds_alternative<typename List<unsigned int>::Nil>(_sv.v())) {
        *(_write) =
            std::make_unique<List<unsigned int>>(List<unsigned int>::nil());
        break;
      } else {
        auto &&_sv1 = *(d_a1);
        if (std::holds_alternative<typename List<unsigned int>::Nil>(
                _sv1.v())) {
          *(_write) =
              std::make_unique<List<unsigned int>>(List<unsigned int>::nil());
          break;
        } else {
          const auto &[d_a01, d_a11] =
              std::get<typename List<unsigned int>::Cons>(_sv1.v());
          auto _cell = std::make_unique<List<unsigned int>>(
              typename List<unsigned int>::Cons(
                  (((d_a01 - d_a0) > d_a01 ? 0 : (d_a01 - d_a0))), nullptr));
          *(_write) = std::move(_cell);
          _write =
              &std::get<typename List<unsigned int>::Cons>((*_write)->v_mut())
                   .d_a1;
          _loop_l = *(d_a1);
          continue;
        }
      }
    }
  }
  return std::move(*(_head));
}

__attribute__((pure)) List<std::pair<unsigned int, unsigned int>>
LoopifyListWindows::sliding_pairs(const List<unsigned int> &l) {
  std::unique_ptr<List<std::pair<unsigned int, unsigned int>>> _head{};
  std::unique_ptr<List<std::pair<unsigned int, unsigned int>>> *_write = &_head;
  List<unsigned int> _loop_l = l;
  while (true) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(_loop_l.v())) {
      *(_write) = std::make_unique<List<std::pair<unsigned int, unsigned int>>>(
          List<std::pair<unsigned int, unsigned int>>::nil());
      break;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<unsigned int>::Cons>(_loop_l.v());
      auto &&_sv = *(d_a1);
      if (std::holds_alternative<typename List<unsigned int>::Nil>(_sv.v())) {
        *(_write) =
            std::make_unique<List<std::pair<unsigned int, unsigned int>>>(
                List<std::pair<unsigned int, unsigned int>>::nil());
        break;
      } else {
        auto &&_sv1 = *(d_a1);
        if (std::holds_alternative<typename List<unsigned int>::Nil>(
                _sv1.v())) {
          *(_write) =
              std::make_unique<List<std::pair<unsigned int, unsigned int>>>(
                  List<std::pair<unsigned int, unsigned int>>::nil());
          break;
        } else {
          const auto &[d_a01, d_a11] =
              std::get<typename List<unsigned int>::Cons>(_sv1.v());
          auto _cell =
              std::make_unique<List<std::pair<unsigned int, unsigned int>>>(
                  typename List<std::pair<unsigned int, unsigned int>>::Cons(
                      std::make_pair(d_a0, d_a01), nullptr));
          *(_write) = std::move(_cell);
          _write =
              &std::get<
                   typename List<std::pair<unsigned int, unsigned int>>::Cons>(
                   (*_write)->v_mut())
                   .d_a1;
          _loop_l = *(d_a1);
          continue;
        }
      }
    }
  }
  return std::move(*(_head));
}

__attribute__((pure)) List<List<unsigned int>>
LoopifyListWindows::inits(const List<unsigned int> &l) {
  struct _Enter {
    const List<unsigned int> l;
  };

  struct _Call1 {
    decltype(List<unsigned int>::nil()) _s0;
    unsigned int _s1;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  List<List<unsigned int>> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{l});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<unsigned int> l = _f.l;
      if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
        _result = List<List<unsigned int>>::cons(
            List<unsigned int>::nil(), List<List<unsigned int>>::nil());
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<unsigned int>::Cons>(l.v());
        _stack.emplace_back(_Call1{List<unsigned int>::nil(), d_a0});
        _stack.emplace_back(_Enter{*(d_a1)});
      }
    } else {
      auto _f = std::move(std::get<_Call1>(_frame));
      _result = List<List<unsigned int>>::cons(
          _f._s0, map_cons_helper(_f._s1, _result));
    }
  }
  return _result;
}

__attribute__((pure)) List<List<unsigned int>>
LoopifyListWindows::tails(List<unsigned int> l) {
  std::unique_ptr<List<List<unsigned int>>> _head{};
  std::unique_ptr<List<List<unsigned int>>> *_write = &_head;
  List<unsigned int> _loop_l = std::move(l);
  while (true) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(
            _loop_l.v_mut())) {
      *(_write) = std::make_unique<List<List<unsigned int>>>(
          List<List<unsigned int>>::cons(List<unsigned int>::nil(),
                                         List<List<unsigned int>>::nil()));
      break;
    } else {
      auto &[d_a0, d_a1] =
          std::get<typename List<unsigned int>::Cons>(_loop_l.v_mut());
      auto _cell = std::make_unique<List<List<unsigned int>>>(
          typename List<List<unsigned int>>::Cons(_loop_l, nullptr));
      *(_write) = std::move(_cell);
      _write =
          &std::get<typename List<List<unsigned int>>::Cons>((*_write)->v_mut())
               .d_a1;
      _loop_l = *(d_a1);
      continue;
    }
  }
  return std::move(*(_head));
}

__attribute__((pure)) List<unsigned int>
LoopifyListWindows::take(const unsigned int &n, const List<unsigned int> &l) {
  std::unique_ptr<List<unsigned int>> _head{};
  std::unique_ptr<List<unsigned int>> *_write = &_head;
  List<unsigned int> _loop_l = l;
  unsigned int _loop_n = n;
  while (true) {
    if (_loop_n <= 0) {
      *(_write) =
          std::make_unique<List<unsigned int>>(List<unsigned int>::nil());
      break;
    } else {
      unsigned int n_ = _loop_n - 1;
      if (std::holds_alternative<typename List<unsigned int>::Nil>(
              _loop_l.v())) {
        *(_write) =
            std::make_unique<List<unsigned int>>(List<unsigned int>::nil());
        break;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<unsigned int>::Cons>(_loop_l.v());
        auto _cell = std::make_unique<List<unsigned int>>(
            typename List<unsigned int>::Cons(d_a0, nullptr));
        *(_write) = std::move(_cell);
        _write =
            &std::get<typename List<unsigned int>::Cons>((*_write)->v_mut())
                 .d_a1;
        List<unsigned int> _next_l = *(d_a1);
        unsigned int _next_n = n_;
        _loop_l = std::move(_next_l);
        _loop_n = std::move(_next_n);
        continue;
      }
    }
  }
  return std::move(*(_head));
}

__attribute__((pure)) List<List<unsigned int>>
LoopifyListWindows::windows_fuel(const unsigned int &fuel,
                                 const unsigned int &n,
                                 const List<unsigned int> &l) {
  std::unique_ptr<List<List<unsigned int>>> _head{};
  std::unique_ptr<List<List<unsigned int>>> *_write = &_head;
  List<unsigned int> _loop_l = l;
  unsigned int _loop_fuel = fuel;
  while (true) {
    if (_loop_fuel <= 0) {
      *(_write) = std::make_unique<List<List<unsigned int>>>(
          List<List<unsigned int>>::nil());
      break;
    } else {
      unsigned int fuel_ = _loop_fuel - 1;
      if (std::holds_alternative<typename List<unsigned int>::Nil>(
              _loop_l.v())) {
        *(_write) = std::make_unique<List<List<unsigned int>>>(
            List<List<unsigned int>>::nil());
        break;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<unsigned int>::Cons>(_loop_l.v());
        if (len(_loop_l) < n) {
          *(_write) = std::make_unique<List<List<unsigned int>>>(
              List<List<unsigned int>>::nil());
          break;
        } else {
          auto _cell = std::make_unique<List<List<unsigned int>>>(
              typename List<List<unsigned int>>::Cons(take(n, _loop_l),
                                                      nullptr));
          *(_write) = std::move(_cell);
          _write = &std::get<typename List<List<unsigned int>>::Cons>(
                        (*_write)->v_mut())
                        .d_a1;
          List<unsigned int> _next_l = *(d_a1);
          unsigned int _next_fuel = fuel_;
          _loop_l = std::move(_next_l);
          _loop_fuel = std::move(_next_fuel);
          continue;
        }
      }
    }
  }
  return std::move(*(_head));
}

__attribute__((pure)) List<List<unsigned int>>
LoopifyListWindows::windows(const unsigned int &n,
                            const List<unsigned int> &l) {
  return windows_fuel(len(l), n, l);
}

__attribute__((pure)) List<List<unsigned int>>
LoopifyListWindows::chunks_fuel(const unsigned int &fuel, const unsigned int &n,
                                const List<unsigned int> &l) {
  std::unique_ptr<List<List<unsigned int>>> _head{};
  std::unique_ptr<List<List<unsigned int>>> *_write = &_head;
  List<unsigned int> _loop_l = l;
  unsigned int _loop_fuel = fuel;
  while (true) {
    if (_loop_fuel <= 0) {
      *(_write) = std::make_unique<List<List<unsigned int>>>(
          List<List<unsigned int>>::nil());
      break;
    } else {
      unsigned int fuel_ = _loop_fuel - 1;
      if (std::holds_alternative<typename List<unsigned int>::Nil>(
              _loop_l.v())) {
        *(_write) = std::make_unique<List<List<unsigned int>>>(
            List<List<unsigned int>>::nil());
        break;
      } else {
        List<unsigned int> chunk = take(n, _loop_l);
        List<unsigned int> rest = drop(n, _loop_l);
        auto _cell = std::make_unique<List<List<unsigned int>>>(
            typename List<List<unsigned int>>::Cons(std::move(chunk), nullptr));
        *(_write) = std::move(_cell);
        _write = &std::get<typename List<List<unsigned int>>::Cons>(
                      (*_write)->v_mut())
                      .d_a1;
        List<unsigned int> _next_l = std::move(rest);
        unsigned int _next_fuel = fuel_;
        _loop_l = std::move(_next_l);
        _loop_fuel = std::move(_next_fuel);
        continue;
      }
    }
  }
  return std::move(*(_head));
}

__attribute__((pure)) List<List<unsigned int>>
LoopifyListWindows::chunks(const unsigned int &n, const List<unsigned int> &l) {
  return chunks_fuel(len(l), n, l);
}

__attribute__((pure)) List<List<unsigned int>>
LoopifyListWindows::group_fuel(const unsigned int &fuel,
                               const List<unsigned int> &l) {
  std::unique_ptr<List<List<unsigned int>>> _head{};
  std::unique_ptr<List<List<unsigned int>>> *_write = &_head;
  List<unsigned int> _loop_l = l;
  unsigned int _loop_fuel = fuel;
  while (true) {
    if (_loop_fuel <= 0) {
      *(_write) = std::make_unique<List<List<unsigned int>>>(
          List<List<unsigned int>>::nil());
      break;
    } else {
      unsigned int fuel_ = _loop_fuel - 1;
      if (std::holds_alternative<typename List<unsigned int>::Nil>(
              _loop_l.v())) {
        *(_write) = std::make_unique<List<List<unsigned int>>>(
            List<List<unsigned int>>::nil());
        break;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<unsigned int>::Cons>(_loop_l.v());
        auto _cs = span_eq(d_a0, *(d_a1));
        const List<unsigned int> &same = _cs.first;
        const List<unsigned int> &rest = _cs.second;
        auto _cell = std::make_unique<List<List<unsigned int>>>(
            typename List<List<unsigned int>>::Cons(
                List<unsigned int>::cons(d_a0, same), nullptr));
        *(_write) = std::move(_cell);
        _write = &std::get<typename List<List<unsigned int>>::Cons>(
                      (*_write)->v_mut())
                      .d_a1;
        List<unsigned int> _next_l = rest;
        unsigned int _next_fuel = fuel_;
        _loop_l = std::move(_next_l);
        _loop_fuel = std::move(_next_fuel);
        continue;
      }
    }
  }
  return std::move(*(_head));
}

__attribute__((pure)) List<List<unsigned int>>
LoopifyListWindows::group(const List<unsigned int> &l) {
  return group_fuel(len(l), l);
}
