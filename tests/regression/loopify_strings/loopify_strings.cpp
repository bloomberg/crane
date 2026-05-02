#include <loopify_strings.h>

List<unsigned int> LoopifyStrings::append(const List<unsigned int> &l1,
                                          List<unsigned int> l2) {
  std::unique_ptr<List<unsigned int>> _head{};
  std::unique_ptr<List<unsigned int>> *_write = &_head;
  List<unsigned int> _loop_l2 = std::move(l2);
  const List<unsigned int> *_loop_l1 = &l1;
  while (true) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(
            _loop_l1->v())) {
      *(_write) = std::make_unique<List<unsigned int>>(std::move(_loop_l2));
      break;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<unsigned int>::Cons>(_loop_l1->v());
      auto _cell = std::make_unique<List<unsigned int>>(
          typename List<unsigned int>::Cons(d_a0, nullptr));
      *(_write) = std::move(_cell);
      _write =
          &std::get<typename List<unsigned int>::Cons>((*_write)->v_mut()).d_a1;
      _loop_l1 = d_a1.get();
      continue;
    }
  }
  return std::move(*(_head));
}

List<unsigned int> LoopifyStrings::join_with(const unsigned int sep,
                                             const List<unsigned int> &l) {
  std::unique_ptr<List<unsigned int>> _head{};
  std::unique_ptr<List<unsigned int>> *_write = &_head;
  const List<unsigned int> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(
            _loop_l->v())) {
      *(_write) =
          std::make_unique<List<unsigned int>>(List<unsigned int>::nil());
      break;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<unsigned int>::Cons>(_loop_l->v());
      auto &&_sv = *(d_a1);
      if (std::holds_alternative<typename List<unsigned int>::Nil>(_sv.v())) {
        *(_write) = std::make_unique<List<unsigned int>>(
            List<unsigned int>::cons(d_a0, List<unsigned int>::nil()));
        break;
      } else {
        auto _cell = std::make_unique<List<unsigned int>>(
            typename List<unsigned int>::Cons(d_a0, nullptr));
        auto _cell1 = std::make_unique<List<unsigned int>>(
            typename List<unsigned int>::Cons(sep, nullptr));
        std::get<typename List<unsigned int>::Cons>(_cell->v_mut()).d_a1 =
            std::move(_cell1);
        *(_write) = std::move(_cell);
        _write =
            &std::get<typename List<unsigned int>::Cons>(
                 std::get<typename List<unsigned int>::Cons>((*_write)->v_mut())
                     .d_a1->v_mut())
                 .d_a1;
        _loop_l = d_a1.get();
        continue;
      }
    }
  }
  return std::move(*(_head));
}

List<unsigned int> LoopifyStrings::repeat_string(
    const List<unsigned int> &s,
    const unsigned int
        n) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    unsigned int n;
  };

  /// _Resume_n_: saves [s], resumes after recursive call with _result.
  struct _Resume_n_ {
    List<unsigned int> s;
  };

  using _Frame = std::variant<_Enter, _Resume_n_>;
  List<unsigned int> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{n});
  /// Loopified repeat_string: _Enter -> _Resume_n_.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const unsigned int n = _f.n;
      if (n <= 0) {
        _result = List<unsigned int>::nil();
      } else {
        unsigned int n_ = n - 1;
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

List<unsigned int> LoopifyStrings::repeat_with_sep(
    List<unsigned int> s, const List<unsigned int> &sep,
    const unsigned int
        n) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    unsigned int n;
  };

  /// _Resume__x: saves [s, sep], resumes after recursive call with _result.
  struct _Resume__x {
    List<unsigned int> s;
    List<unsigned int> sep;
  };

  using _Frame = std::variant<_Enter, _Resume__x>;
  List<unsigned int> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{n});
  /// Loopified repeat_with_sep: _Enter -> _Resume__x.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const unsigned int n = _f.n;
      if (n <= 0) {
        _result = List<unsigned int>::nil();
      } else {
        unsigned int n_ = n - 1;
        if (n_ <= 0) {
          _result = std::move(s);
        } else {
          unsigned int _x = n_ - 1;
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

List<unsigned int> LoopifyStrings::string_chain_fuel(
    const unsigned int fuel, const List<unsigned int> &s, const unsigned int n,
    const List<unsigned int> &sep,
    const List<unsigned int>
        &end_marker) { /// _Enter: captures varying parameters for each
                       /// recursive call.

  struct _Enter {
    unsigned int n;
    unsigned int fuel;
  };

  /// _Resume1: saves [s, sep, end_marker], resumes after recursive call with
  /// _result.
  struct _Resume1 {
    List<unsigned int> s;
    List<unsigned int> sep;
    List<unsigned int> end_marker;
  };

  using _Frame = std::variant<_Enter, _Resume1>;
  List<unsigned int> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{n, fuel});
  /// Loopified string_chain_fuel: _Enter -> _Resume1.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const unsigned int n = _f.n;
      const unsigned int fuel = _f.fuel;
      if (fuel <= 0) {
        _result = List<unsigned int>::nil();
      } else {
        unsigned int fuel_ = fuel - 1;
        if (n <= 0u) {
          _result = List<unsigned int>::nil();
        } else {
          _stack.emplace_back(_Resume1{s, sep, end_marker});
          _stack.emplace_back(_Enter{(((n - 1u) > n ? 0 : (n - 1u))), fuel_});
        }
      }
    } else {
      auto _f = std::move(std::get<_Resume1>(_frame));
      _result = append(_f.s, append(_f.sep, append(_result, _f.end_marker)));
    }
  }
  return _result;
}

List<unsigned int>
LoopifyStrings::string_chain(const List<unsigned int> &s, const unsigned int n,
                             const List<unsigned int> &sep,
                             const List<unsigned int> &end_marker) {
  return string_chain_fuel(n, s, n, sep, end_marker);
}

List<unsigned int> LoopifyStrings::reverse(
    const List<unsigned int>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<unsigned int> *l;
  };

  /// _Resume_Cons: saves [_s0], resumes after recursive call with _result.
  struct _Resume_Cons {
    decltype(List<unsigned int>::cons(std::declval<unsigned int &>(),
                                      List<unsigned int>::nil())) _s0;
  };

  using _Frame = std::variant<_Enter, _Resume_Cons>;
  List<unsigned int> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{&l});
  /// Loopified reverse: _Enter -> _Resume_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<unsigned int> &l = *(_f.l);
      if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
        _result = List<unsigned int>::nil();
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<unsigned int>::Cons>(l.v());
        _stack.emplace_back(_Resume_Cons{
            List<unsigned int>::cons(d_a0, List<unsigned int>::nil())});
        _stack.emplace_back(_Enter{d_a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Resume_Cons>(_frame));
      _result = append(_result, _f._s0);
    }
  }
  return _result;
}

bool LoopifyStrings::list_eq(
    const List<unsigned int> &l1,
    const List<unsigned int>
        &l2) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<unsigned int> *l2;
    const List<unsigned int> *l1;
  };

  /// _Resume_Cons: saves [_s0], resumes after recursive call with _result.
  struct _Resume_Cons {
    decltype(std::declval<unsigned int &>() ==
             std::declval<unsigned int &>()) _s0;
  };

  using _Frame = std::variant<_Enter, _Resume_Cons>;
  bool _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{&l2, &l1});
  /// Loopified list_eq: _Enter -> _Resume_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<unsigned int> &l2 = *(_f.l2);
      const List<unsigned int> &l1 = *(_f.l1);
      if (std::holds_alternative<typename List<unsigned int>::Nil>(l1.v())) {
        if (std::holds_alternative<typename List<unsigned int>::Nil>(l2.v())) {
          _result = true;
        } else {
          _result = false;
        }
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<unsigned int>::Cons>(l1.v());
        if (std::holds_alternative<typename List<unsigned int>::Nil>(l2.v())) {
          _result = false;
        } else {
          const auto &[d_a00, d_a10] =
              std::get<typename List<unsigned int>::Cons>(l2.v());
          _stack.emplace_back(_Resume_Cons{d_a0 == d_a00});
          _stack.emplace_back(_Enter{d_a10.get(), d_a1.get()});
        }
      }
    } else {
      auto _f = std::move(std::get<_Resume_Cons>(_frame));
      _result = (_f._s0 && _result);
    }
  }
  return _result;
}

bool LoopifyStrings::is_palindrome(const List<unsigned int> &l) {
  return list_eq(l, reverse(l));
}

List<unsigned int> LoopifyStrings::intersperse(const unsigned int sep,
                                               const List<unsigned int> &l) {
  std::unique_ptr<List<unsigned int>> _head{};
  std::unique_ptr<List<unsigned int>> *_write = &_head;
  const List<unsigned int> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(
            _loop_l->v())) {
      *(_write) =
          std::make_unique<List<unsigned int>>(List<unsigned int>::nil());
      break;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<unsigned int>::Cons>(_loop_l->v());
      auto &&_sv = *(d_a1);
      if (std::holds_alternative<typename List<unsigned int>::Nil>(_sv.v())) {
        *(_write) = std::make_unique<List<unsigned int>>(
            List<unsigned int>::cons(d_a0, List<unsigned int>::nil()));
        break;
      } else {
        auto _cell = std::make_unique<List<unsigned int>>(
            typename List<unsigned int>::Cons(d_a0, nullptr));
        auto _cell1 = std::make_unique<List<unsigned int>>(
            typename List<unsigned int>::Cons(sep, nullptr));
        std::get<typename List<unsigned int>::Cons>(_cell->v_mut()).d_a1 =
            std::move(_cell1);
        *(_write) = std::move(_cell);
        _write =
            &std::get<typename List<unsigned int>::Cons>(
                 std::get<typename List<unsigned int>::Cons>((*_write)->v_mut())
                     .d_a1->v_mut())
                 .d_a1;
        _loop_l = d_a1.get();
        continue;
      }
    }
  }
  return std::move(*(_head));
}

List<unsigned int> LoopifyStrings::intercalate(
    const List<unsigned int> &sep,
    const List<List<unsigned int>>
        &ll) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<List<unsigned int>> *ll;
  };

  /// _Resume_Cons: saves [d_a0, sep], resumes after recursive call with
  /// _result.
  struct _Resume_Cons {
    List<unsigned int> d_a0;
    List<unsigned int> sep;
  };

  using _Frame = std::variant<_Enter, _Resume_Cons>;
  List<unsigned int> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{&ll});
  /// Loopified intercalate: _Enter -> _Resume_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<List<unsigned int>> &ll = *(_f.ll);
      if (std::holds_alternative<typename List<List<unsigned int>>::Nil>(
              ll.v())) {
        _result = List<unsigned int>::nil();
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<List<unsigned int>>::Cons>(ll.v());
        auto &&_sv = *(d_a1);
        if (std::holds_alternative<typename List<List<unsigned int>>::Nil>(
                _sv.v())) {
          _result = d_a0;
        } else {
          _stack.emplace_back(_Resume_Cons{d_a0, sep});
          _stack.emplace_back(_Enter{d_a1.get()});
        }
      }
    } else {
      auto _f = std::move(std::get<_Resume_Cons>(_frame));
      _result = append(_f.d_a0, append(_f.sep, _result));
    }
  }
  return _result;
}

List<unsigned int> LoopifyStrings::replicate(const unsigned int n,
                                             const unsigned int x) {
  std::unique_ptr<List<unsigned int>> _head{};
  std::unique_ptr<List<unsigned int>> *_write = &_head;
  unsigned int _loop_n = n;
  while (true) {
    if (_loop_n <= 0) {
      *(_write) =
          std::make_unique<List<unsigned int>>(List<unsigned int>::nil());
      break;
    } else {
      unsigned int n_ = _loop_n - 1;
      auto _cell = std::make_unique<List<unsigned int>>(
          typename List<unsigned int>::Cons(x, nullptr));
      *(_write) = std::move(_cell);
      _write =
          &std::get<typename List<unsigned int>::Cons>((*_write)->v_mut()).d_a1;
      _loop_n = n_;
      continue;
    }
  }
  return std::move(*(_head));
}

List<std::pair<unsigned int, unsigned int>>
LoopifyStrings::run_length_aux(const unsigned int current,
                               const unsigned int count,
                               const List<unsigned int> &l) {
  std::unique_ptr<List<std::pair<unsigned int, unsigned int>>> _head{};
  std::unique_ptr<List<std::pair<unsigned int, unsigned int>>> *_write = &_head;
  const List<unsigned int> *_loop_l = &l;
  unsigned int _loop_count = count;
  unsigned int _loop_current = current;
  while (true) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(
            _loop_l->v())) {
      if (_loop_count == 0u) {
        *(_write) =
            std::make_unique<List<std::pair<unsigned int, unsigned int>>>(
                List<std::pair<unsigned int, unsigned int>>::nil());
        break;
      } else {
        *(_write) =
            std::make_unique<List<std::pair<unsigned int, unsigned int>>>(
                List<std::pair<unsigned int, unsigned int>>::cons(
                    std::make_pair(_loop_current, _loop_count),
                    List<std::pair<unsigned int, unsigned int>>::nil()));
        break;
      }
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<unsigned int>::Cons>(_loop_l->v());
      if (d_a0 == _loop_current) {
        _loop_l = d_a1.get();
        _loop_count = (_loop_count + 1u);
        continue;
      } else {
        if (_loop_count == 0u) {
          _loop_l = d_a1.get();
          _loop_count = 1u;
          _loop_current = d_a0;
          continue;
        } else {
          auto _cell =
              std::make_unique<List<std::pair<unsigned int, unsigned int>>>(
                  typename List<std::pair<unsigned int, unsigned int>>::Cons(
                      std::make_pair(_loop_current, _loop_count), nullptr));
          *(_write) = std::move(_cell);
          _write =
              &std::get<
                   typename List<std::pair<unsigned int, unsigned int>>::Cons>(
                   (*_write)->v_mut())
                   .d_a1;
          _loop_l = d_a1.get();
          _loop_count = 1u;
          _loop_current = d_a0;
          continue;
        }
      }
    }
  }
  return std::move(*(_head));
}

List<std::pair<unsigned int, unsigned int>>
LoopifyStrings::run_length_encode(const List<unsigned int> &l) {
  if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
    return List<std::pair<unsigned int, unsigned int>>::nil();
  } else {
    const auto &[d_a0, d_a1] =
        std::get<typename List<unsigned int>::Cons>(l.v());
    return run_length_aux(d_a0, 1u, *(d_a1));
  }
}
