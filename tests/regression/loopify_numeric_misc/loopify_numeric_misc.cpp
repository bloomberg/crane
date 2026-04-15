#include <loopify_numeric_misc.h>

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

__attribute__((pure)) unsigned int
LoopifyNumericMisc::sum_abs(const std::shared_ptr<List<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<List<unsigned int>> l;
  };

  struct _Call1 {
    decltype(std::declval<typename List<unsigned int>::Cons &>().d_a0) _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.emplace_back(_Enter{l});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      const auto &_f = std::get<_Enter>(_frame);
      const std::shared_ptr<List<unsigned int>> l = _f.l;
      if (std::holds_alternative<typename List<unsigned int>::Nil>(l->v())) {
        _result = 0u;
      } else {
        const auto &_m =
            *std::get_if<typename List<unsigned int>::Cons>(&l->v());
        _stack.emplace_back(_Call1{_m.d_a0});
        _stack.emplace_back(_Enter{_m.d_a1});
      }
    } else {
      const auto &_f = std::get<_Call1>(_frame);
      _result = (_f._s0 + _result);
    }
  }
  return _result;
}

__attribute__((pure)) unsigned int
LoopifyNumericMisc::alternating_ops(const unsigned int n) {
  struct _Enter {
    const unsigned int n;
  };

  struct _Call1 {
    decltype((std::declval<unsigned int &>() + 1)) _s0;
  };

  struct _Call2 {
    decltype(((std::declval<unsigned int &>() + 1) * 2u)) _s0;
  };

  using _Frame = std::variant<_Enter, _Call1, _Call2>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.emplace_back(_Enter{n});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      const auto &_f = std::get<_Enter>(_frame);
      const unsigned int n = _f.n;
      if (n <= 0) {
        _result = 0u;
      } else {
        unsigned int n_ = n - 1;
        if ((2u ? (n_ + 1) % 2u : (n_ + 1)) == 0u) {
          _stack.emplace_back(_Call1{(n_ + 1)});
          _stack.emplace_back(_Enter{n_});
        } else {
          _stack.emplace_back(_Call2{((n_ + 1) * 2u)});
          _stack.emplace_back(_Enter{n_});
        }
      }
    } else if (std::holds_alternative<_Call1>(_frame)) {
      const auto &_f = std::get<_Call1>(_frame);
      _result = (_f._s0 + _result);
    } else {
      const auto &_f = std::get<_Call2>(_frame);
      _result = (_f._s0 + _result);
    }
  }
  return _result;
}

__attribute__((pure)) unsigned int
LoopifyNumericMisc::count_even(const std::shared_ptr<List<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<List<unsigned int>> l;
  };

  struct _Call1 {
    decltype(1u) _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.emplace_back(_Enter{l});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      const auto &_f = std::get<_Enter>(_frame);
      const std::shared_ptr<List<unsigned int>> l = _f.l;
      if (std::holds_alternative<typename List<unsigned int>::Nil>(l->v())) {
        _result = 0u;
      } else {
        const auto &_m =
            *std::get_if<typename List<unsigned int>::Cons>(&l->v());
        if ((2u ? _m.d_a0 % 2u : _m.d_a0) == 0u) {
          _stack.emplace_back(_Call1{1u});
          _stack.emplace_back(_Enter{_m.d_a1});
        } else {
          _stack.emplace_back(_Enter{_m.d_a1});
        }
      }
    } else {
      const auto &_f = std::get<_Call1>(_frame);
      _result = (_f._s0 + _result);
    }
  }
  return _result;
}

__attribute__((pure)) unsigned int
LoopifyNumericMisc::count_odd(const std::shared_ptr<List<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<List<unsigned int>> l;
  };

  struct _Call1 {
    decltype(1u) _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.emplace_back(_Enter{l});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      const auto &_f = std::get<_Enter>(_frame);
      const std::shared_ptr<List<unsigned int>> l = _f.l;
      if (std::holds_alternative<typename List<unsigned int>::Nil>(l->v())) {
        _result = 0u;
      } else {
        const auto &_m =
            *std::get_if<typename List<unsigned int>::Cons>(&l->v());
        if ((2u ? _m.d_a0 % 2u : _m.d_a0) == 1u) {
          _stack.emplace_back(_Call1{1u});
          _stack.emplace_back(_Enter{_m.d_a1});
        } else {
          _stack.emplace_back(_Enter{_m.d_a1});
        }
      }
    } else {
      const auto &_f = std::get<_Call1>(_frame);
      _result = (_f._s0 + _result);
    }
  }
  return _result;
}

__attribute__((pure)) unsigned int
LoopifyNumericMisc::product(const std::shared_ptr<List<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<List<unsigned int>> l;
  };

  struct _Call1 {
    decltype(std::declval<typename List<unsigned int>::Cons &>().d_a0) _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.emplace_back(_Enter{l});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      const auto &_f = std::get<_Enter>(_frame);
      const std::shared_ptr<List<unsigned int>> l = _f.l;
      if (std::holds_alternative<typename List<unsigned int>::Nil>(l->v())) {
        _result = 1u;
      } else {
        const auto &_m =
            *std::get_if<typename List<unsigned int>::Cons>(&l->v());
        _stack.emplace_back(_Call1{_m.d_a0});
        _stack.emplace_back(_Enter{_m.d_a1});
      }
    } else {
      const auto &_f = std::get<_Call1>(_frame);
      _result = (_f._s0 * _result);
    }
  }
  return _result;
}

__attribute__((pure)) unsigned int LoopifyNumericMisc::sum_of_squares(
    const std::shared_ptr<List<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<List<unsigned int>> l;
  };

  struct _Call1 {
    decltype((std::declval<typename List<unsigned int>::Cons &>().d_a0 *
              std::declval<typename List<unsigned int>::Cons &>().d_a0)) _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.emplace_back(_Enter{l});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      const auto &_f = std::get<_Enter>(_frame);
      const std::shared_ptr<List<unsigned int>> l = _f.l;
      if (std::holds_alternative<typename List<unsigned int>::Nil>(l->v())) {
        _result = 0u;
      } else {
        const auto &_m =
            *std::get_if<typename List<unsigned int>::Cons>(&l->v());
        _stack.emplace_back(_Call1{(_m.d_a0 * _m.d_a0)});
        _stack.emplace_back(_Enter{_m.d_a1});
      }
    } else {
      const auto &_f = std::get<_Call1>(_frame);
      _result = (_f._s0 + _result);
    }
  }
  return _result;
}

__attribute__((pure)) unsigned int
LoopifyNumericMisc::max_two(const unsigned int a, const unsigned int b) {
  if (a < b) {
    return b;
  } else {
    return a;
  }
}

__attribute__((pure)) unsigned int
LoopifyNumericMisc::list_max(const std::shared_ptr<List<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<List<unsigned int>> l;
  };

  struct _Call1 {
    decltype(std::declval<typename List<unsigned int>::Cons &>().d_a0) _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.emplace_back(_Enter{l});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      const auto &_f = std::get<_Enter>(_frame);
      const std::shared_ptr<List<unsigned int>> l = _f.l;
      if (std::holds_alternative<typename List<unsigned int>::Nil>(l->v())) {
        _result = 0u;
      } else {
        const auto &_m =
            *std::get_if<typename List<unsigned int>::Cons>(&l->v());
        auto &&_sv = _m.d_a1;
        if (std::holds_alternative<typename List<unsigned int>::Nil>(
                _sv->v())) {
          _result = _m.d_a0;
        } else {
          _stack.emplace_back(_Call1{_m.d_a0});
          _stack.emplace_back(_Enter{_m.d_a1});
        }
      }
    } else {
      const auto &_f = std::get<_Call1>(_frame);
      _result = max_two(_f._s0, _result);
    }
  }
  return _result;
}

__attribute__((pure)) unsigned int
LoopifyNumericMisc::list_min(const std::shared_ptr<List<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<List<unsigned int>> l;
  };

  struct _Call1 {
    const typename List<unsigned int>::Cons _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.emplace_back(_Enter{l});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      const auto &_f = std::get<_Enter>(_frame);
      const std::shared_ptr<List<unsigned int>> l = _f.l;
      if (std::holds_alternative<typename List<unsigned int>::Nil>(l->v())) {
        _result = 0u;
      } else {
        const auto &_m =
            *std::get_if<typename List<unsigned int>::Cons>(&l->v());
        auto &&_sv = _m.d_a1;
        if (std::holds_alternative<typename List<unsigned int>::Nil>(
                _sv->v())) {
          _result = _m.d_a0;
        } else {
          _stack.emplace_back(_Call1{_m});
          _stack.emplace_back(_Enter{_m.d_a1});
        }
      }
    } else {
      const auto &_f = std::get<_Call1>(_frame);
      const typename List<unsigned int>::Cons _m = _f._s0;
      unsigned int min_rest = _result;
      if (_m.d_a0 < min_rest) {
        _result = _m.d_a0;
      } else {
        _result = min_rest;
      }
    }
  }
  return _result;
}
