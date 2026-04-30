#include <loopify_numeric_misc.h>

unsigned int LoopifyNumericMisc::sum_abs(const List<unsigned int> &l) {
  struct _Enter {
    const List<unsigned int> *l;
  };

  /// Continuation: saves [d_a0] across recursive call.
  struct _Resume1 {
    unsigned int d_a0;
  };

  using _Frame = std::variant<_Enter, _Resume1>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{&l});
  /// Frame dispatch: _Enter, _Resume1.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<unsigned int> &l = *(_f.l);
      if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
        _result = 0u;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<unsigned int>::Cons>(l.v());
        _stack.emplace_back(_Resume1{d_a0});
        _stack.emplace_back(_Enter{d_a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Resume1>(_frame));
      _result = (_f.d_a0 + _result);
    }
  }
  return _result;
}

unsigned int LoopifyNumericMisc::alternating_ops(const unsigned int &n) {
  struct _Enter {
    unsigned int n;
  };

  /// Continuation: saves [_s0] across recursive call.
  struct _Resume1 {
    decltype((std::declval<unsigned int &>() + 1)) _s0;
  };

  /// Continuation: saves [_s0] across recursive call.
  struct _Resume2 {
    decltype(((std::declval<unsigned int &>() + 1) * 2u)) _s0;
  };

  using _Frame = std::variant<_Enter, _Resume1, _Resume2>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{n});
  /// Frame dispatch: _Enter, _Resume1, _Resume2.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const unsigned int &n = _f.n;
      if (n <= 0) {
        _result = 0u;
      } else {
        unsigned int n_ = n - 1;
        if ((2u ? (n_ + 1) % 2u : (n_ + 1)) == 0u) {
          _stack.emplace_back(_Resume1{(n_ + 1)});
          _stack.emplace_back(_Enter{n_});
        } else {
          _stack.emplace_back(_Resume2{((n_ + 1) * 2u)});
          _stack.emplace_back(_Enter{n_});
        }
      }
    } else if (std::holds_alternative<_Resume1>(_frame)) {
      auto _f = std::move(std::get<_Resume1>(_frame));
      _result = (_f._s0 + _result);
    } else {
      auto _f = std::move(std::get<_Resume2>(_frame));
      _result = (_f._s0 + _result);
    }
  }
  return _result;
}

unsigned int LoopifyNumericMisc::count_even(const List<unsigned int> &l) {
  struct _Enter {
    const List<unsigned int> *l;
  };

  /// Continuation: saves [_s0] across recursive call.
  struct _Resume1 {
    decltype(1u) _s0;
  };

  using _Frame = std::variant<_Enter, _Resume1>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{&l});
  /// Frame dispatch: _Enter, _Resume1.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<unsigned int> &l = *(_f.l);
      if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
        _result = 0u;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<unsigned int>::Cons>(l.v());
        if ((2u ? d_a0 % 2u : d_a0) == 0u) {
          _stack.emplace_back(_Resume1{1u});
          _stack.emplace_back(_Enter{d_a1.get()});
        } else {
          _stack.emplace_back(_Enter{d_a1.get()});
        }
      }
    } else {
      auto _f = std::move(std::get<_Resume1>(_frame));
      _result = (_f._s0 + _result);
    }
  }
  return _result;
}

unsigned int LoopifyNumericMisc::count_odd(const List<unsigned int> &l) {
  struct _Enter {
    const List<unsigned int> *l;
  };

  /// Continuation: saves [_s0] across recursive call.
  struct _Resume1 {
    decltype(1u) _s0;
  };

  using _Frame = std::variant<_Enter, _Resume1>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{&l});
  /// Frame dispatch: _Enter, _Resume1.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<unsigned int> &l = *(_f.l);
      if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
        _result = 0u;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<unsigned int>::Cons>(l.v());
        if ((2u ? d_a0 % 2u : d_a0) == 1u) {
          _stack.emplace_back(_Resume1{1u});
          _stack.emplace_back(_Enter{d_a1.get()});
        } else {
          _stack.emplace_back(_Enter{d_a1.get()});
        }
      }
    } else {
      auto _f = std::move(std::get<_Resume1>(_frame));
      _result = (_f._s0 + _result);
    }
  }
  return _result;
}

unsigned int LoopifyNumericMisc::product(const List<unsigned int> &l) {
  struct _Enter {
    const List<unsigned int> *l;
  };

  /// Continuation: saves [d_a0] across recursive call.
  struct _Resume1 {
    unsigned int d_a0;
  };

  using _Frame = std::variant<_Enter, _Resume1>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{&l});
  /// Frame dispatch: _Enter, _Resume1.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<unsigned int> &l = *(_f.l);
      if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
        _result = 1u;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<unsigned int>::Cons>(l.v());
        _stack.emplace_back(_Resume1{d_a0});
        _stack.emplace_back(_Enter{d_a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Resume1>(_frame));
      _result = (_f.d_a0 * _result);
    }
  }
  return _result;
}

unsigned int LoopifyNumericMisc::sum_of_squares(const List<unsigned int> &l) {
  struct _Enter {
    const List<unsigned int> *l;
  };

  /// Continuation: saves [_s0] across recursive call.
  struct _Resume1 {
    decltype((std::declval<unsigned int &>() *
              std::declval<unsigned int &>())) _s0;
  };

  using _Frame = std::variant<_Enter, _Resume1>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{&l});
  /// Frame dispatch: _Enter, _Resume1.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<unsigned int> &l = *(_f.l);
      if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
        _result = 0u;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<unsigned int>::Cons>(l.v());
        _stack.emplace_back(_Resume1{(d_a0 * d_a0)});
        _stack.emplace_back(_Enter{d_a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Resume1>(_frame));
      _result = (_f._s0 + _result);
    }
  }
  return _result;
}

unsigned int LoopifyNumericMisc::max_two(unsigned int a, unsigned int b) {
  if (a < b) {
    return b;
  } else {
    return a;
  }
}

unsigned int LoopifyNumericMisc::list_max(const List<unsigned int> &l) {
  struct _Enter {
    const List<unsigned int> *l;
  };

  /// Continuation: saves [d_a0] across recursive call.
  struct _Resume1 {
    unsigned int d_a0;
  };

  using _Frame = std::variant<_Enter, _Resume1>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{&l});
  /// Frame dispatch: _Enter, _Resume1.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<unsigned int> &l = *(_f.l);
      if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
        _result = 0u;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<unsigned int>::Cons>(l.v());
        auto &&_sv = *(d_a1);
        if (std::holds_alternative<typename List<unsigned int>::Nil>(_sv.v())) {
          _result = d_a0;
        } else {
          _stack.emplace_back(_Resume1{d_a0});
          _stack.emplace_back(_Enter{d_a1.get()});
        }
      }
    } else {
      auto _f = std::move(std::get<_Resume1>(_frame));
      _result = max_two(_f.d_a0, _result);
    }
  }
  return _result;
}

unsigned int LoopifyNumericMisc::list_min(const List<unsigned int> &l) {
  struct _Enter {
    const List<unsigned int> *l;
  };

  /// Continuation: saves [d_a0] across recursive call, then processes rest.
  struct _Cont1 {
    unsigned int d_a0;
  };

  using _Frame = std::variant<_Enter, _Cont1>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{&l});
  /// Frame dispatch: _Enter, _Cont1.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<unsigned int> &l = *(_f.l);
      if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
        _result = 0u;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<unsigned int>::Cons>(l.v());
        auto &&_sv = *(d_a1);
        if (std::holds_alternative<typename List<unsigned int>::Nil>(_sv.v())) {
          _result = d_a0;
        } else {
          _stack.emplace_back(_Cont1{d_a0});
          _stack.emplace_back(_Enter{d_a1.get()});
        }
      }
    } else {
      auto _f = std::move(std::get<_Cont1>(_frame));
      unsigned int d_a0 = std::move(_f.d_a0);
      unsigned int min_rest = _result;
      if (d_a0 < min_rest) {
        _result = d_a0;
      } else {
        _result = min_rest;
      }
    }
  }
  return _result;
}
