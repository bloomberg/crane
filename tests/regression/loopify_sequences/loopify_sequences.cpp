#include <loopify_sequences.h>

/// alternate_sum sign acc l alternating sum with sign flip.
__attribute__((pure)) unsigned int
LoopifySequences::alternate_sum(const unsigned int &sign, unsigned int acc,
                                const List<unsigned int> &l) {
  unsigned int _result;
  List<unsigned int> _loop_l = l;
  unsigned int _loop_acc = std::move(acc);
  unsigned int _loop_sign = sign;
  while (true) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(_loop_l.v())) {
      _result = _loop_acc;
      break;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<unsigned int>::Cons>(_loop_l.v());
      unsigned int new_acc;
      if (_loop_sign == 1u) {
        new_acc = (_loop_acc + d_a0);
      } else {
        new_acc = (((_loop_acc - d_a0) > _loop_acc ? 0 : (_loop_acc - d_a0)));
      }
      unsigned int new_sign;
      if (_loop_sign == 1u) {
        new_sign = 0u;
      } else {
        new_sign = 1u;
      }
      List<unsigned int> _next_l = *(d_a1);
      unsigned int _next_acc = new_acc;
      unsigned int _next_sign = new_sign;
      _loop_l = std::move(_next_l);
      _loop_acc = std::move(_next_acc);
      _loop_sign = std::move(_next_sign);
    }
  }
  return _result;
}

/// collatz_list n generates collatz sequence.
__attribute__((pure)) List<unsigned int>
LoopifySequences::collatz_list_fuel(const unsigned int &fuel, unsigned int n) {
  struct _Enter {
    unsigned int n;
    const unsigned int fuel;
  };

  using _Frame = std::variant<_Enter>;
  List<unsigned int> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{n, fuel});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    auto _f = std::move(std::get<_Enter>(_frame));
    unsigned int n = _f.n;
    const unsigned int fuel = _f.fuel;
    if (fuel <= 0) {
      _result = List<unsigned int>::nil();
    } else {
      unsigned int f = fuel - 1;
      if (n == 1u) {
        _result = List<unsigned int>::cons(1u, List<unsigned int>::nil());
      } else {
        if ((2u ? n % 2u : n) == 0u) {
          _stack.emplace_back(_Enter{(2u ? n / 2u : 0), f});
        } else {
          _stack.emplace_back(_Enter{((3u * n) + 1u), f});
        }
      }
    }
  }
  return _result;
}

__attribute__((pure)) List<unsigned int>
LoopifySequences::collatz_list(const unsigned int &n) {
  return collatz_list_fuel(1000u, n);
}

/// run_sum l running sum (scanl for addition).
__attribute__((pure)) List<unsigned int>
LoopifySequences::run_sum_aux(const unsigned int &acc,
                              const List<unsigned int> &l) {
  std::unique_ptr<List<unsigned int>> _head{};
  std::unique_ptr<List<unsigned int>> *_write = &_head;
  List<unsigned int> _loop_l = l;
  unsigned int _loop_acc = acc;
  while (true) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(_loop_l.v())) {
      *(_write) =
          std::make_unique<List<unsigned int>>(List<unsigned int>::nil());
      break;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<unsigned int>::Cons>(_loop_l.v());
      unsigned int new_acc = (_loop_acc + d_a0);
      auto _cell = std::make_unique<List<unsigned int>>(
          typename List<unsigned int>::Cons(new_acc, nullptr));
      *(_write) = std::move(_cell);
      _write =
          &std::get<typename List<unsigned int>::Cons>((*_write)->v_mut()).d_a1;
      List<unsigned int> _next_l = *(d_a1);
      unsigned int _next_acc = new_acc;
      _loop_l = std::move(_next_l);
      _loop_acc = std::move(_next_acc);
      continue;
    }
  }
  return std::move(*(_head));
}

__attribute__((pure)) List<unsigned int>
LoopifySequences::run_sum(const List<unsigned int> &l) {
  return List<unsigned int>::cons(0u, run_sum_aux(0u, l));
}

/// rotate_left n l rotates list left by n positions.
__attribute__((pure)) List<unsigned int> LoopifySequences::rotate_left_fuel(
    const unsigned int &fuel, const unsigned int &n, List<unsigned int> l) {
  List<unsigned int> _result;
  List<unsigned int> _loop_l = std::move(l);
  unsigned int _loop_n = n;
  unsigned int _loop_fuel = fuel;
  while (true) {
    if (_loop_fuel <= 0) {
      _result = _loop_l;
      break;
    } else {
      unsigned int f = _loop_fuel - 1;
      if (_loop_n == 0u) {
        _result = _loop_l;
        break;
      } else {
        if (std::holds_alternative<typename List<unsigned int>::Nil>(
                _loop_l.v())) {
          _result = List<unsigned int>::nil();
          break;
        } else {
          const auto &[d_a0, d_a1] =
              std::get<typename List<unsigned int>::Cons>(_loop_l.v());
          List<unsigned int> _next_l = (*(d_a1)).app(
              List<unsigned int>::cons(d_a0, List<unsigned int>::nil()));
          unsigned int _next_n =
              (((_loop_n - 1u) > _loop_n ? 0 : (_loop_n - 1u)));
          unsigned int _next_fuel = f;
          _loop_l = std::move(_next_l);
          _loop_n = std::move(_next_n);
          _loop_fuel = std::move(_next_fuel);
        }
      }
    }
  }
  return _result;
}

__attribute__((pure)) List<unsigned int>
LoopifySequences::rotate_left(const unsigned int &n,
                              const List<unsigned int> &l) {
  return rotate_left_fuel(100u, n, l);
}

/// sum_acc acc l sum with accumulator.
__attribute__((pure)) unsigned int
LoopifySequences::sum_acc(unsigned int acc, const List<unsigned int> &l) {
  unsigned int _result;
  List<unsigned int> _loop_l = l;
  unsigned int _loop_acc = std::move(acc);
  while (true) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(_loop_l.v())) {
      _result = _loop_acc;
      break;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<unsigned int>::Cons>(_loop_l.v());
      List<unsigned int> _next_l = *(d_a1);
      unsigned int _next_acc = (_loop_acc + d_a0);
      _loop_l = std::move(_next_l);
      _loop_acc = std::move(_next_acc);
    }
  }
  return _result;
}

/// repeat_string s n repeats string n times (using list as string).
__attribute__((pure)) List<unsigned int>
LoopifySequences::repeat_string(const List<unsigned int> &s,
                                const unsigned int &n) {
  struct _Enter {
    const unsigned int n;
  };

  struct _Call1 {
    const List<unsigned int> _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  List<unsigned int> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{n});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const unsigned int n = _f.n;
      if (n <= 0) {
        _result = List<unsigned int>::nil();
      } else {
        unsigned int m = n - 1;
        _stack.emplace_back(_Call1{s});
        _stack.emplace_back(_Enter{m});
      }
    } else {
      auto _f = std::move(std::get<_Call1>(_frame));
      _result = _f._s0.app(_result);
    }
  }
  return _result;
}

/// repeat_with_sep s sep n repeats with separator.
__attribute__((pure)) List<unsigned int>
LoopifySequences::repeat_with_sep(List<unsigned int> s,
                                  const List<unsigned int> &sep,
                                  const unsigned int &n) {
  struct _Enter {
    const unsigned int n;
  };

  struct _Call1 {
    List<unsigned int> _s0;
    const List<unsigned int> _s1;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  List<unsigned int> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{n});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const unsigned int n = _f.n;
      if (n <= 0) {
        _result = List<unsigned int>::nil();
      } else {
        unsigned int m = n - 1;
        if (m <= 0) {
          _result = s;
        } else {
          unsigned int _x = m - 1;
          _stack.emplace_back(_Call1{s, sep});
          _stack.emplace_back(_Enter{m});
        }
      }
    } else {
      auto _f = std::move(std::get<_Call1>(_frame));
      _result = _f._s0.app(_f._s1.app(_result));
    }
  }
  return _result;
}

/// string_chain s n recursive string chain: s-chain(s, n-1)-end.
__attribute__((pure)) List<unsigned int> LoopifySequences::string_chain_fuel(
    const unsigned int &fuel, const List<unsigned int> &s,
    const unsigned int &n, const List<unsigned int> &sep,
    const List<unsigned int> &end_marker) {
  struct _Enter {
    const unsigned int n;
    const unsigned int fuel;
  };

  struct _Call1 {
    const List<unsigned int> _s0;
    const List<unsigned int> _s1;
    decltype(std::declval<const List<unsigned int> &>().app(
        std::declval<const List<unsigned int> &>())) _s2;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  List<unsigned int> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{n, fuel});
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
        unsigned int f = fuel - 1;
        if (n <= 0u) {
          _result = List<unsigned int>::nil();
        } else {
          _stack.emplace_back(_Call1{s, sep, sep.app(end_marker)});
          _stack.emplace_back(_Enter{(((n - 1u) > n ? 0 : (n - 1u))), f});
        }
      }
    } else {
      auto _f = std::move(std::get<_Call1>(_frame));
      _result = _f._s0.app(_f._s1.app(_result.app(_f._s2)));
    }
  }
  return _result;
}

__attribute__((pure)) List<unsigned int> LoopifySequences::string_chain(
    const List<unsigned int> &s, const unsigned int &n,
    const List<unsigned int> &sep, const List<unsigned int> &end_marker) {
  return string_chain_fuel(1000u, s, n, sep, end_marker);
}

/// split_by_sign l base pos neg splits list based on base threshold.
__attribute__((pure)) std::pair<List<unsigned int>, List<unsigned int>>
LoopifySequences::split_by_sign(const List<unsigned int> &l,
                                const unsigned int &base,
                                List<unsigned int> pos,
                                List<unsigned int> neg) {
  std::pair<List<unsigned int>, List<unsigned int>> _result;
  List<unsigned int> _loop_neg = std::move(neg);
  List<unsigned int> _loop_pos = std::move(pos);
  List<unsigned int> _loop_l = l;
  while (true) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(_loop_l.v())) {
      _result = std::make_pair(_loop_pos, _loop_neg);
      break;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<unsigned int>::Cons>(_loop_l.v());
      if (base <= d_a0) {
        List<unsigned int> _next_pos =
            List<unsigned int>::cons(d_a0, _loop_pos);
        List<unsigned int> _next_l = *(d_a1);
        _loop_pos = std::move(_next_pos);
        _loop_l = std::move(_next_l);
      } else {
        List<unsigned int> _next_neg =
            List<unsigned int>::cons(d_a0, _loop_neg);
        List<unsigned int> _next_l = *(d_a1);
        _loop_neg = std::move(_next_neg);
        _loop_l = std::move(_next_l);
      }
    }
  }
  return _result;
}

/// differences l computes differences between consecutive elements.
__attribute__((pure)) List<unsigned int>
LoopifySequences::differences(const List<unsigned int> &l) {
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
      auto &&_sv0 = *(d_a1);
      if (std::holds_alternative<typename List<unsigned int>::Nil>(_sv0.v())) {
        *(_write) =
            std::make_unique<List<unsigned int>>(List<unsigned int>::nil());
        break;
      } else {
        const auto &[d_a00, d_a10] =
            std::get<typename List<unsigned int>::Cons>(_sv0.v());
        auto _cell = std::make_unique<List<unsigned int>>(
            typename List<unsigned int>::Cons(
                (((d_a00 - d_a0) > d_a00 ? 0 : (d_a00 - d_a0))), nullptr));
        *(_write) = std::move(_cell);
        _write =
            &std::get<typename List<unsigned int>::Cons>((*_write)->v_mut())
                 .d_a1;
        _loop_l = *(d_a1);
        continue;
      }
    }
  }
  return std::move(*(_head));
}

/// replace_at idx value l replaces element at index with value.
__attribute__((pure)) List<unsigned int>
LoopifySequences::replace_at(const unsigned int &idx, unsigned int value,
                             const List<unsigned int> &l) {
  std::unique_ptr<List<unsigned int>> _head{};
  std::unique_ptr<List<unsigned int>> *_write = &_head;
  List<unsigned int> _loop_l = l;
  unsigned int _loop_idx = idx;
  while (true) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(_loop_l.v())) {
      *(_write) =
          std::make_unique<List<unsigned int>>(List<unsigned int>::nil());
      break;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<unsigned int>::Cons>(_loop_l.v());
      if (_loop_idx == 0u) {
        *(_write) = std::make_unique<List<unsigned int>>(
            List<unsigned int>::cons(value, *(d_a1)));
        break;
      } else {
        auto _cell = std::make_unique<List<unsigned int>>(
            typename List<unsigned int>::Cons(d_a0, nullptr));
        *(_write) = std::move(_cell);
        _write =
            &std::get<typename List<unsigned int>::Cons>((*_write)->v_mut())
                 .d_a1;
        List<unsigned int> _next_l = *(d_a1);
        unsigned int _next_idx =
            (((_loop_idx - 1u) > _loop_idx ? 0 : (_loop_idx - 1u)));
        _loop_l = std::move(_next_l);
        _loop_idx = std::move(_next_idx);
        continue;
      }
    }
  }
  return std::move(*(_head));
}

/// cycle n l repeats list n times.
__attribute__((pure)) List<unsigned int>
LoopifySequences::cycle(const unsigned int &n, const List<unsigned int> &l) {
  struct _Enter {
    const unsigned int n;
  };

  struct _Call1 {
    const List<unsigned int> _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  List<unsigned int> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{n});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const unsigned int n = _f.n;
      if (n <= 0) {
        _result = List<unsigned int>::nil();
      } else {
        unsigned int m = n - 1;
        if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
          _result = List<unsigned int>::nil();
        } else {
          _stack.emplace_back(_Call1{l});
          _stack.emplace_back(_Enter{m});
        }
      }
    } else {
      auto _f = std::move(std::get<_Call1>(_frame));
      _result = _f._s0.app(_result);
    }
  }
  return _result;
}

/// Helper: get first element.
__attribute__((pure)) unsigned int
LoopifySequences::first_elem(const List<unsigned int> &l) {
  if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
    return 0u;
  } else {
    const auto &[d_a0, d_a1] =
        std::get<typename List<unsigned int>::Cons>(l.v());
    return d_a0;
  }
}

/// Helper: get last element.
__attribute__((pure)) unsigned int
LoopifySequences::last_elem(const List<unsigned int> &l) {
  unsigned int _result;
  List<unsigned int> _loop_l = l;
  while (true) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(_loop_l.v())) {
      _result = 0u;
      break;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<unsigned int>::Cons>(_loop_l.v());
      auto &&_sv = *(d_a1);
      if (std::holds_alternative<typename List<unsigned int>::Nil>(_sv.v())) {
        _result = d_a0;
        break;
      } else {
        _loop_l = *(d_a1);
      }
    }
  }
  return _result;
}

/// Helper: remove first element.
__attribute__((pure)) List<unsigned int>
LoopifySequences::tail_list(const List<unsigned int> &l) {
  if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
    return List<unsigned int>::nil();
  } else {
    const auto &[d_a0, d_a1] =
        std::get<typename List<unsigned int>::Cons>(l.v());
    return *(d_a1);
  }
}

/// Helper: remove last element.
__attribute__((pure)) List<unsigned int>
LoopifySequences::init_list(const List<unsigned int> &l) {
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
        auto _cell = std::make_unique<List<unsigned int>>(
            typename List<unsigned int>::Cons(d_a0, nullptr));
        *(_write) = std::move(_cell);
        _write =
            &std::get<typename List<unsigned int>::Cons>((*_write)->v_mut())
                 .d_a1;
        _loop_l = *(d_a1);
        continue;
      }
    }
  }
  return std::move(*(_head));
}

/// is_palindrome s checks if list is a palindrome.
__attribute__((pure)) bool
LoopifySequences::is_palindrome_fuel(const unsigned int &fuel,
                                     const List<unsigned int> &s) {
  bool _result;
  List<unsigned int> _loop_s = s;
  unsigned int _loop_fuel = fuel;
  while (true) {
    if (_loop_fuel <= 0) {
      _result = true;
      break;
    } else {
      unsigned int f = _loop_fuel - 1;
      unsigned int n = _loop_s.length();
      if (n <= 0) {
        _result = true;
        break;
      } else {
        unsigned int n0 = n - 1;
        if (n0 <= 0) {
          _result = true;
          break;
        } else {
          unsigned int _x = n0 - 1;
          if (first_elem(_loop_s) == last_elem(_loop_s)) {
            List<unsigned int> _next_s = init_list(tail_list(_loop_s));
            unsigned int _next_fuel = f;
            _loop_s = std::move(_next_s);
            _loop_fuel = std::move(_next_fuel);
          } else {
            _result = false;
            break;
          }
        }
      }
    }
  }
  return _result;
}

__attribute__((pure)) bool
LoopifySequences::is_palindrome(const List<unsigned int> &s) {
  return is_palindrome_fuel(1000u, s);
}

/// string_subsequences s generates all subsequences treating list as string.
__attribute__((pure)) List<List<unsigned int>>
LoopifySequences::string_subsequences(const List<unsigned int> &s) {
  struct _Enter {
    const List<unsigned int> s;
  };

  struct _Call1 {
    unsigned int _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  List<List<unsigned int>> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{s});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<unsigned int> s = _f.s;
      if (std::holds_alternative<typename List<unsigned int>::Nil>(s.v())) {
        _result = List<List<unsigned int>>::cons(
            List<unsigned int>::nil(), List<List<unsigned int>>::nil());
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<unsigned int>::Cons>(s.v());
        List<unsigned int> d_a1_value = List<unsigned int>(*(d_a1));
        _stack.emplace_back(_Call1{d_a0});
        _stack.emplace_back(_Enter{d_a1_value});
      }
    } else {
      auto _f = std::move(std::get<_Call1>(_frame));
      unsigned int d_a0 = _f._s0;
      List<List<unsigned int>> sub_rest = _result;
      std::function<List<List<unsigned int>>(List<List<unsigned int>>)>
          map_prepend_c;
      map_prepend_c =
          [&](List<List<unsigned int>> lsts) -> List<List<unsigned int>> {
        struct _Enter {
          List<List<unsigned int>> lsts;
        };
        struct _Call1 {
          decltype(List<unsigned int>::cons(
              d_a0, std::declval<List<unsigned int> &>())) _s0;
        };
        using _Frame = std::variant<_Enter, _Call1>;
        List<List<unsigned int>> _result{};
        std::vector<_Frame> _stack;
        _stack.reserve(16);
        _stack.emplace_back(_Enter{lsts});
        while (!_stack.empty()) {
          _Frame _frame = std::move(_stack.back());
          _stack.pop_back();
          if (std::holds_alternative<_Enter>(_frame)) {
            auto _f = std::move(std::get<_Enter>(_frame));
            List<List<unsigned int>> lsts = _f.lsts;
            if (std::holds_alternative<typename List<List<unsigned int>>::Nil>(
                    lsts.v())) {
              _result = List<List<unsigned int>>::nil();
            } else {
              const auto &[d_a00, d_a10] =
                  std::get<typename List<List<unsigned int>>::Cons>(lsts.v());
              _stack.emplace_back(
                  _Call1{List<unsigned int>::cons(d_a0, d_a00)});
              _stack.emplace_back(_Enter{*(d_a10)});
            }
          } else {
            auto _f = std::move(std::get<_Call1>(_frame));
            _result = List<List<unsigned int>>::cons(_f._s0, _result);
          }
        }
        return _result;
      };
      _result = sub_rest.app(map_prepend_c(sub_rest));
    }
  }
  return _result;
}

/// run_length_groups l groups consecutive runs into sublist lengths.
__attribute__((pure)) List<unsigned int>
LoopifySequences::run_length_groups_aux(const unsigned int &prev,
                                        unsigned int count,
                                        const List<unsigned int> &l) {
  std::unique_ptr<List<unsigned int>> _head{};
  std::unique_ptr<List<unsigned int>> *_write = &_head;
  List<unsigned int> _loop_l = l;
  unsigned int _loop_count = std::move(count);
  unsigned int _loop_prev = prev;
  while (true) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(_loop_l.v())) {
      if (_loop_count == 0u) {
        *(_write) =
            std::make_unique<List<unsigned int>>(List<unsigned int>::nil());
        break;
      } else {
        *(_write) = std::make_unique<List<unsigned int>>(
            List<unsigned int>::cons(_loop_count, List<unsigned int>::nil()));
        break;
      }
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<unsigned int>::Cons>(_loop_l.v());
      if (_loop_prev == d_a0) {
        List<unsigned int> _next_l = *(d_a1);
        unsigned int _next_count = (_loop_count + 1);
        unsigned int _next_prev = d_a0;
        _loop_l = std::move(_next_l);
        _loop_count = std::move(_next_count);
        _loop_prev = std::move(_next_prev);
        continue;
      } else {
        if (_loop_count == 0u) {
          List<unsigned int> _next_l = *(d_a1);
          unsigned int _next_count = 1u;
          unsigned int _next_prev = d_a0;
          _loop_l = std::move(_next_l);
          _loop_count = std::move(_next_count);
          _loop_prev = std::move(_next_prev);
          continue;
        } else {
          auto _cell = std::make_unique<List<unsigned int>>(
              typename List<unsigned int>::Cons(_loop_count, nullptr));
          *(_write) = std::move(_cell);
          _write =
              &std::get<typename List<unsigned int>::Cons>((*_write)->v_mut())
                   .d_a1;
          List<unsigned int> _next_l = *(d_a1);
          unsigned int _next_count = 1u;
          unsigned int _next_prev = d_a0;
          _loop_l = std::move(_next_l);
          _loop_count = std::move(_next_count);
          _loop_prev = std::move(_next_prev);
          continue;
        }
      }
    }
  }
  return std::move(*(_head));
}

__attribute__((pure)) List<unsigned int>
LoopifySequences::run_length_groups(const List<unsigned int> &l) {
  if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
    return List<unsigned int>::nil();
  } else {
    const auto &[d_a0, d_a1] =
        std::get<typename List<unsigned int>::Cons>(l.v());
    return run_length_groups_aux(d_a0, 1u, *(d_a1));
  }
}

/// is_prefix_of l1 l2 checks if l1 is a prefix of l2.
__attribute__((pure)) bool
LoopifySequences::is_prefix_of(const List<unsigned int> &l1,
                               const List<unsigned int> &l2) {
  bool _result;
  List<unsigned int> _loop_l2 = l2;
  List<unsigned int> _loop_l1 = l1;
  while (true) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(
            _loop_l1.v())) {
      _result = true;
      break;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<unsigned int>::Cons>(_loop_l1.v());
      if (std::holds_alternative<typename List<unsigned int>::Nil>(
              _loop_l2.v())) {
        _result = false;
        break;
      } else {
        const auto &[d_a00, d_a10] =
            std::get<typename List<unsigned int>::Cons>(_loop_l2.v());
        if (d_a0 == d_a00) {
          List<unsigned int> _next_l2 = *(d_a10);
          List<unsigned int> _next_l1 = *(d_a1);
          _loop_l2 = std::move(_next_l2);
          _loop_l1 = std::move(_next_l1);
        } else {
          _result = false;
          break;
        }
      }
    }
  }
  return _result;
}

/// lis l longest increasing subsequence (greedy, not optimal).
__attribute__((pure)) List<unsigned int>
LoopifySequences::lis(List<unsigned int> l) {
  std::unique_ptr<List<unsigned int>> _head{};
  std::unique_ptr<List<unsigned int>> *_write = &_head;
  List<unsigned int> _loop_l = std::move(l);
  while (true) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(_loop_l.v())) {
      *(_write) =
          std::make_unique<List<unsigned int>>(List<unsigned int>::nil());
      break;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<unsigned int>::Cons>(_loop_l.v());
      auto &&_sv0 = *(d_a1);
      if (std::holds_alternative<typename List<unsigned int>::Nil>(_sv0.v())) {
        *(_write) = std::make_unique<List<unsigned int>>(_loop_l);
        break;
      } else {
        const auto &[d_a00, d_a10] =
            std::get<typename List<unsigned int>::Cons>(_sv0.v());
        if (d_a0 < d_a00) {
          auto _cell = std::make_unique<List<unsigned int>>(
              typename List<unsigned int>::Cons(d_a0, nullptr));
          *(_write) = std::move(_cell);
          _write =
              &std::get<typename List<unsigned int>::Cons>((*_write)->v_mut())
                   .d_a1;
          _loop_l = *(d_a1);
          continue;
        } else {
          _loop_l = *(d_a1);
          continue;
        }
      }
    }
  }
  return std::move(*(_head));
}

/// Helper: check if element is in list.
__attribute__((pure)) bool LoopifySequences::elem(const unsigned int &x,
                                                  const List<unsigned int> &l) {
  struct _Enter {
    const List<unsigned int> l;
  };

  struct _Call1 {
    decltype(std::declval<const unsigned int &>() ==
             std::declval<unsigned int &>()) _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  bool _result{};
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
        _result = false;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<unsigned int>::Cons>(l.v());
        _stack.emplace_back(_Call1{x == d_a0});
        _stack.emplace_back(_Enter{*(d_a1)});
      }
    } else {
      auto _f = std::move(std::get<_Call1>(_frame));
      _result = (_f._s0 || _result);
    }
  }
  return _result;
}

/// Helper: filter list.
__attribute__((pure)) List<unsigned int>
LoopifySequences::filter_ne(const unsigned int &x,
                            const List<unsigned int> &l) {
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
      if (x == d_a0) {
        _loop_l = *(d_a1);
        continue;
      } else {
        auto _cell = std::make_unique<List<unsigned int>>(
            typename List<unsigned int>::Cons(d_a0, nullptr));
        *(_write) = std::move(_cell);
        _write =
            &std::get<typename List<unsigned int>::Cons>((*_write)->v_mut())
                 .d_a1;
        _loop_l = *(d_a1);
        continue;
      }
    }
  }
  return std::move(*(_head));
}

/// nub l removes duplicates from list.
__attribute__((pure)) List<unsigned int>
LoopifySequences::nub_fuel(const unsigned int &fuel,
                           const List<unsigned int> &l) {
  std::unique_ptr<List<unsigned int>> _head{};
  std::unique_ptr<List<unsigned int>> *_write = &_head;
  List<unsigned int> _loop_l = l;
  unsigned int _loop_fuel = fuel;
  while (true) {
    if (_loop_fuel <= 0) {
      *(_write) =
          std::make_unique<List<unsigned int>>(List<unsigned int>::nil());
      break;
    } else {
      unsigned int f = _loop_fuel - 1;
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
        List<unsigned int> _next_l = filter_ne(d_a0, *(d_a1));
        unsigned int _next_fuel = f;
        _loop_l = std::move(_next_l);
        _loop_fuel = std::move(_next_fuel);
        continue;
      }
    }
  }
  return std::move(*(_head));
}

__attribute__((pure)) List<unsigned int>
LoopifySequences::nub(const List<unsigned int> &l) {
  return nub_fuel(l.length(), l);
}

/// group l groups consecutive equal elements.
__attribute__((pure)) List<List<unsigned int>>
LoopifySequences::group_fuel(const unsigned int &fuel,
                             const List<unsigned int> &l) {
  if (fuel <= 0) {
    return List<List<unsigned int>>::nil();
  } else {
    unsigned int f = fuel - 1;
    if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
      return List<List<unsigned int>>::nil();
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<unsigned int>::Cons>(l.v());
      auto &&_sv0 = *(d_a1);
      if (std::holds_alternative<typename List<unsigned int>::Nil>(_sv0.v())) {
        return List<List<unsigned int>>::cons(
            List<unsigned int>::cons(d_a0, List<unsigned int>::nil()),
            List<List<unsigned int>>::nil());
      } else {
        const auto &[d_a00, d_a10] =
            std::get<typename List<unsigned int>::Cons>(_sv0.v());
        if (d_a0 == d_a00) {
          auto &&_sv1 = group_fuel(f, *(d_a1));
          if (std::holds_alternative<typename List<List<unsigned int>>::Nil>(
                  _sv1.v())) {
            return List<List<unsigned int>>::cons(
                List<unsigned int>::cons(d_a0, List<unsigned int>::nil()),
                List<List<unsigned int>>::nil());
          } else {
            const auto &[d_a01, d_a11] =
                std::get<typename List<List<unsigned int>>::Cons>(_sv1.v());
            return List<List<unsigned int>>::cons(
                List<unsigned int>::cons(d_a0, d_a01), *(d_a11));
          }
        } else {
          return List<List<unsigned int>>::cons(
              List<unsigned int>::cons(d_a0, List<unsigned int>::nil()),
              group_fuel(f, *(d_a1)));
        }
      }
    }
  }
}

__attribute__((pure)) List<List<unsigned int>>
LoopifySequences::group(const List<unsigned int> &l) {
  return group_fuel(l.length(), l);
}

/// Helper: get head with default.
__attribute__((pure)) unsigned int
LoopifySequences::head_or(unsigned int default0, const List<unsigned int> &l) {
  if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
    return default0;
  } else {
    const auto &[d_a0, d_a1] =
        std::get<typename List<unsigned int>::Cons>(l.v());
    return d_a0;
  }
}

/// remove_if_sum_even l removes elements where sum with next is even.
__attribute__((pure)) List<unsigned int>
LoopifySequences::remove_if_sum_even(const List<unsigned int> &l) {
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
      unsigned int next = head_or(0u, *(d_a1));
      if ((2u ? (d_a0 + next) % 2u : (d_a0 + next)) == 0u) {
        _loop_l = *(d_a1);
        continue;
      } else {
        auto _cell = std::make_unique<List<unsigned int>>(
            typename List<unsigned int>::Cons(d_a0, nullptr));
        *(_write) = std::move(_cell);
        _write =
            &std::get<typename List<unsigned int>::Cons>((*_write)->v_mut())
                 .d_a1;
        _loop_l = *(d_a1);
        continue;
      }
    }
  }
  return std::move(*(_head));
}

/// run_length_encode l encodes consecutive runs: 1,1,2,2,2 -> (1,2),(2,3).
__attribute__((pure)) List<std::pair<unsigned int, unsigned int>>
LoopifySequences::run_length_encode_fuel(const unsigned int &fuel,
                                         const List<unsigned int> &l) {
  if (fuel <= 0) {
    return List<std::pair<unsigned int, unsigned int>>::nil();
  } else {
    unsigned int f = fuel - 1;
    if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
      return List<std::pair<unsigned int, unsigned int>>::nil();
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<unsigned int>::Cons>(l.v());
      auto &&_sv = *(d_a1);
      if (std::holds_alternative<typename List<unsigned int>::Nil>(_sv.v())) {
        return List<std::pair<unsigned int, unsigned int>>::cons(
            std::make_pair(d_a0, 1u),
            List<std::pair<unsigned int, unsigned int>>::nil());
      } else {
        auto &&_sv1 = run_length_encode_fuel(f, *(d_a1));
        if (std::holds_alternative<
                typename List<std::pair<unsigned int, unsigned int>>::Nil>(
                _sv1.v())) {
          return List<std::pair<unsigned int, unsigned int>>::cons(
              std::make_pair(d_a0, 1u),
              List<std::pair<unsigned int, unsigned int>>::nil());
        } else {
          const auto &[d_a01, d_a11] = std::get<
              typename List<std::pair<unsigned int, unsigned int>>::Cons>(
              _sv1.v());
          const unsigned int &y = d_a01.first;
          const unsigned int &n = d_a01.second;
          if (d_a0 == y) {
            return List<std::pair<unsigned int, unsigned int>>::cons(
                std::make_pair(y, (n + 1)), *(d_a11));
          } else {
            return List<std::pair<unsigned int, unsigned int>>::cons(
                std::make_pair(d_a0, 1u),
                List<std::pair<unsigned int, unsigned int>>::cons(
                    std::make_pair(y, n), *(d_a11)));
          }
        }
      }
    }
  }
}

__attribute__((pure)) List<std::pair<unsigned int, unsigned int>>
LoopifySequences::run_length_encode(const List<unsigned int> &l) {
  return run_length_encode_fuel(l.length(), l);
}

/// between lo hi l filters elements in range lo, hi.
__attribute__((pure)) List<unsigned int>
LoopifySequences::between(const unsigned int &lo, const unsigned int &hi,
                          const List<unsigned int> &l) {
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
      if ((lo <= d_a0 && d_a0 <= hi)) {
        auto _cell = std::make_unique<List<unsigned int>>(
            typename List<unsigned int>::Cons(d_a0, nullptr));
        *(_write) = std::move(_cell);
        _write =
            &std::get<typename List<unsigned int>::Cons>((*_write)->v_mut())
                 .d_a1;
        _loop_l = *(d_a1);
        continue;
      } else {
        _loop_l = *(d_a1);
        continue;
      }
    }
  }
  return std::move(*(_head));
}
