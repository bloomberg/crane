#include <loopify_strings.h>

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

std::shared_ptr<List<unsigned int>>
LoopifyStrings::append(const std::shared_ptr<List<unsigned int>> &l1,
                       std::shared_ptr<List<unsigned int>> l2) {
  std::shared_ptr<List<unsigned int>> _head{};
  std::shared_ptr<List<unsigned int>> *_write = &_head;
  std::shared_ptr<List<unsigned int>> _loop_l1 = l1;
  while (true) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(
            _loop_l1->v())) {
      *_write = std::move(l2);
      break;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<unsigned int>::Cons>(_loop_l1->v());
      auto _cell = List<unsigned int>::cons(d_a0, nullptr);
      *_write = _cell;
      _write =
          &std::get<typename List<unsigned int>::Cons>(_cell->v_mut()).d_a1;
      _loop_l1 = d_a1;
      continue;
    }
  }
  return _head;
}

std::shared_ptr<List<unsigned int>>
LoopifyStrings::join_with(const unsigned int sep,
                          const std::shared_ptr<List<unsigned int>> &l) {
  std::shared_ptr<List<unsigned int>> _head{};
  std::shared_ptr<List<unsigned int>> *_write = &_head;
  std::shared_ptr<List<unsigned int>> _loop_l = l;
  while (true) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(
            _loop_l->v())) {
      *_write = List<unsigned int>::nil();
      break;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<unsigned int>::Cons>(_loop_l->v());
      if (std::holds_alternative<typename List<unsigned int>::Nil>(d_a1->v())) {
        *_write = List<unsigned int>::cons(d_a0, List<unsigned int>::nil());
        break;
      } else {
        auto _cell = List<unsigned int>::cons(d_a0, nullptr);
        auto _cell1 = List<unsigned int>::cons(sep, nullptr);
        std::get<typename List<unsigned int>::Cons>(_cell->v_mut()).d_a1 =
            _cell1;
        *_write = _cell;
        _write =
            &std::get<typename List<unsigned int>::Cons>(_cell1->v_mut()).d_a1;
        _loop_l = d_a1;
        continue;
      }
    }
  }
  return _head;
}

std::shared_ptr<List<unsigned int>>
LoopifyStrings::repeat_string(const std::shared_ptr<List<unsigned int>> &s,
                              const unsigned int n) {
  struct _Enter {
    const unsigned int n;
  };

  struct _Call1 {
    const std::shared_ptr<List<unsigned int>> _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::shared_ptr<List<unsigned int>> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{n});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      const auto &_f = std::get<_Enter>(_frame);
      const unsigned int n = _f.n;
      if (n <= 0) {
        _result = List<unsigned int>::nil();
      } else {
        unsigned int n_ = n - 1;
        _stack.emplace_back(_Call1{s});
        _stack.emplace_back(_Enter{n_});
      }
    } else {
      const auto &_f = std::get<_Call1>(_frame);
      _result = append(_f._s0, _result);
    }
  }
  return _result;
}

std::shared_ptr<List<unsigned int>>
LoopifyStrings::repeat_with_sep(std::shared_ptr<List<unsigned int>> s,
                                const std::shared_ptr<List<unsigned int>> &sep,
                                const unsigned int n) {
  struct _Enter {
    const unsigned int n;
  };

  struct _Call1 {
    std::shared_ptr<List<unsigned int>> _s0;
    const std::shared_ptr<List<unsigned int>> _s1;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::shared_ptr<List<unsigned int>> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{n});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      const auto &_f = std::get<_Enter>(_frame);
      const unsigned int n = _f.n;
      if (n <= 0) {
        _result = List<unsigned int>::nil();
      } else {
        unsigned int n_ = n - 1;
        if (n_ <= 0) {
          _result = std::move(s);
        } else {
          unsigned int _x = n_ - 1;
          _stack.emplace_back(_Call1{s, sep});
          _stack.emplace_back(_Enter{n_});
        }
      }
    } else {
      const auto &_f = std::get<_Call1>(_frame);
      _result = append(_f._s0, append(_f._s1, _result));
    }
  }
  return _result;
}

std::shared_ptr<List<unsigned int>> LoopifyStrings::string_chain_fuel(
    const unsigned int fuel, const std::shared_ptr<List<unsigned int>> &s,
    const unsigned int n, const std::shared_ptr<List<unsigned int>> &sep,
    const std::shared_ptr<List<unsigned int>> &end_marker) {
  struct _Enter {
    const unsigned int n;
    const unsigned int fuel;
  };

  struct _Call1 {
    const std::shared_ptr<List<unsigned int>> _s0;
    const std::shared_ptr<List<unsigned int>> _s1;
    const std::shared_ptr<List<unsigned int>> _s2;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::shared_ptr<List<unsigned int>> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{n, fuel});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      const auto &_f = std::get<_Enter>(_frame);
      const unsigned int n = _f.n;
      const unsigned int fuel = _f.fuel;
      if (fuel <= 0) {
        _result = List<unsigned int>::nil();
      } else {
        unsigned int fuel_ = fuel - 1;
        if (n <= 0u) {
          _result = List<unsigned int>::nil();
        } else {
          _stack.emplace_back(_Call1{s, sep, end_marker});
          _stack.emplace_back(_Enter{(((n - 1u) > n ? 0 : (n - 1u))), fuel_});
        }
      }
    } else {
      const auto &_f = std::get<_Call1>(_frame);
      _result = append(_f._s0, append(_f._s1, append(_result, _f._s2)));
    }
  }
  return _result;
}

std::shared_ptr<List<unsigned int>> LoopifyStrings::string_chain(
    const std::shared_ptr<List<unsigned int>> &s, const unsigned int n,
    const std::shared_ptr<List<unsigned int>> &sep,
    const std::shared_ptr<List<unsigned int>> &end_marker) {
  return string_chain_fuel(n, s, n, sep, end_marker);
}

std::shared_ptr<List<unsigned int>>
LoopifyStrings::reverse(const std::shared_ptr<List<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<List<unsigned int>> l;
  };

  struct _Call1 {
    decltype(List<unsigned int>::cons(std::declval<unsigned int &>(),
                                      List<unsigned int>::nil())) _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::shared_ptr<List<unsigned int>> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{l});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      const auto &_f = std::get<_Enter>(_frame);
      const std::shared_ptr<List<unsigned int>> l = _f.l;
      if (std::holds_alternative<typename List<unsigned int>::Nil>(l->v())) {
        _result = List<unsigned int>::nil();
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<unsigned int>::Cons>(l->v());
        _stack.emplace_back(
            _Call1{List<unsigned int>::cons(d_a0, List<unsigned int>::nil())});
        _stack.emplace_back(_Enter{d_a1});
      }
    } else {
      const auto &_f = std::get<_Call1>(_frame);
      _result = append(_result, _f._s0);
    }
  }
  return _result;
}

__attribute__((pure)) bool
LoopifyStrings::list_eq(const std::shared_ptr<List<unsigned int>> &l1,
                        const std::shared_ptr<List<unsigned int>> &l2) {
  struct _Enter {
    const std::shared_ptr<List<unsigned int>> l2;
    const std::shared_ptr<List<unsigned int>> l1;
  };

  struct _Call1 {
    decltype(std::declval<unsigned int &>() ==
             std::declval<unsigned int &>()) _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  bool _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{l2, l1});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      const auto &_f = std::get<_Enter>(_frame);
      const std::shared_ptr<List<unsigned int>> l2 = _f.l2;
      const std::shared_ptr<List<unsigned int>> l1 = _f.l1;
      if (std::holds_alternative<typename List<unsigned int>::Nil>(l1->v())) {
        if (std::holds_alternative<typename List<unsigned int>::Nil>(l2->v())) {
          _result = true;
        } else {
          _result = false;
        }
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<unsigned int>::Cons>(l1->v());
        if (std::holds_alternative<typename List<unsigned int>::Nil>(l2->v())) {
          _result = false;
        } else {
          const auto &[d_a00, d_a10] =
              std::get<typename List<unsigned int>::Cons>(l2->v());
          _stack.emplace_back(_Call1{d_a0 == d_a00});
          _stack.emplace_back(_Enter{d_a10, d_a1});
        }
      }
    } else {
      const auto &_f = std::get<_Call1>(_frame);
      _result = (_f._s0 && _result);
    }
  }
  return _result;
}

__attribute__((pure)) bool
LoopifyStrings::is_palindrome(const std::shared_ptr<List<unsigned int>> &l) {
  return list_eq(l, reverse(l));
}

std::shared_ptr<List<unsigned int>>
LoopifyStrings::intersperse(const unsigned int sep,
                            const std::shared_ptr<List<unsigned int>> &l) {
  std::shared_ptr<List<unsigned int>> _head{};
  std::shared_ptr<List<unsigned int>> *_write = &_head;
  std::shared_ptr<List<unsigned int>> _loop_l = l;
  while (true) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(
            _loop_l->v())) {
      *_write = List<unsigned int>::nil();
      break;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<unsigned int>::Cons>(_loop_l->v());
      if (std::holds_alternative<typename List<unsigned int>::Nil>(d_a1->v())) {
        *_write = List<unsigned int>::cons(d_a0, List<unsigned int>::nil());
        break;
      } else {
        auto _cell = List<unsigned int>::cons(d_a0, nullptr);
        auto _cell1 = List<unsigned int>::cons(sep, nullptr);
        std::get<typename List<unsigned int>::Cons>(_cell->v_mut()).d_a1 =
            _cell1;
        *_write = _cell;
        _write =
            &std::get<typename List<unsigned int>::Cons>(_cell1->v_mut()).d_a1;
        _loop_l = d_a1;
        continue;
      }
    }
  }
  return _head;
}

std::shared_ptr<List<unsigned int>> LoopifyStrings::intercalate(
    const std::shared_ptr<List<unsigned int>> &sep,
    const std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> &ll) {
  struct _Enter {
    const std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> ll;
  };

  struct _Call1 {
    std::shared_ptr<List<unsigned int>> _s0;
    const std::shared_ptr<List<unsigned int>> _s1;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::shared_ptr<List<unsigned int>> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{ll});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      const auto &_f = std::get<_Enter>(_frame);
      const std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> ll =
          _f.ll;
      if (std::holds_alternative<
              typename List<std::shared_ptr<List<unsigned int>>>::Nil>(
              ll->v())) {
        _result = List<unsigned int>::nil();
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<std::shared_ptr<List<unsigned int>>>::Cons>(
                ll->v());
        if (std::holds_alternative<
                typename List<std::shared_ptr<List<unsigned int>>>::Nil>(
                d_a1->v())) {
          _result = d_a0;
        } else {
          _stack.emplace_back(_Call1{d_a0, sep});
          _stack.emplace_back(_Enter{d_a1});
        }
      }
    } else {
      const auto &_f = std::get<_Call1>(_frame);
      _result = append(_f._s0, append(_f._s1, _result));
    }
  }
  return _result;
}

std::shared_ptr<List<unsigned int>>
LoopifyStrings::replicate(const unsigned int n, const unsigned int x) {
  std::shared_ptr<List<unsigned int>> _head{};
  std::shared_ptr<List<unsigned int>> *_write = &_head;
  unsigned int _loop_n = n;
  while (true) {
    if (_loop_n <= 0) {
      *_write = List<unsigned int>::nil();
      break;
    } else {
      unsigned int n_ = _loop_n - 1;
      auto _cell = List<unsigned int>::cons(x, nullptr);
      *_write = _cell;
      _write =
          &std::get<typename List<unsigned int>::Cons>(_cell->v_mut()).d_a1;
      _loop_n = n_;
      continue;
    }
  }
  return _head;
}

std::shared_ptr<List<std::pair<unsigned int, unsigned int>>>
LoopifyStrings::run_length_aux(const unsigned int current,
                               const unsigned int count,
                               const std::shared_ptr<List<unsigned int>> &l) {
  std::shared_ptr<List<std::pair<unsigned int, unsigned int>>> _head{};
  std::shared_ptr<List<std::pair<unsigned int, unsigned int>>> *_write = &_head;
  std::shared_ptr<List<unsigned int>> _loop_l = l;
  unsigned int _loop_count = count;
  unsigned int _loop_current = current;
  while (true) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(
            _loop_l->v())) {
      if (_loop_count == 0u) {
        *_write = List<std::pair<unsigned int, unsigned int>>::nil();
        break;
      } else {
        *_write = List<std::pair<unsigned int, unsigned int>>::cons(
            std::make_pair(_loop_current, _loop_count),
            List<std::pair<unsigned int, unsigned int>>::nil());
        break;
      }
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<unsigned int>::Cons>(_loop_l->v());
      if (d_a0 == _loop_current) {
        std::shared_ptr<List<unsigned int>> _next_l = d_a1;
        unsigned int _next_count = (_loop_count + 1u);
        _loop_l = std::move(_next_l);
        _loop_count = std::move(_next_count);
        continue;
      } else {
        if (_loop_count == 0u) {
          std::shared_ptr<List<unsigned int>> _next_l = d_a1;
          unsigned int _next_count = 1u;
          unsigned int _next_current = d_a0;
          _loop_l = std::move(_next_l);
          _loop_count = std::move(_next_count);
          _loop_current = std::move(_next_current);
          continue;
        } else {
          auto _cell = List<std::pair<unsigned int, unsigned int>>::cons(
              std::make_pair(_loop_current, _loop_count), nullptr);
          *_write = _cell;
          _write =
              &std::get<
                   typename List<std::pair<unsigned int, unsigned int>>::Cons>(
                   _cell->v_mut())
                   .d_a1;
          std::shared_ptr<List<unsigned int>> _next_l = d_a1;
          unsigned int _next_count = 1u;
          unsigned int _next_current = d_a0;
          _loop_l = std::move(_next_l);
          _loop_count = std::move(_next_count);
          _loop_current = std::move(_next_current);
          continue;
        }
      }
    }
  }
  return _head;
}

std::shared_ptr<List<std::pair<unsigned int, unsigned int>>>
LoopifyStrings::run_length_encode(
    const std::shared_ptr<List<unsigned int>> &l) {
  if (std::holds_alternative<typename List<unsigned int>::Nil>(l->v())) {
    return List<std::pair<unsigned int, unsigned int>>::nil();
  } else {
    const auto &[d_a0, d_a1] =
        std::get<typename List<unsigned int>::Cons>(l->v());
    return run_length_aux(d_a0, 1u, d_a1);
  }
}
