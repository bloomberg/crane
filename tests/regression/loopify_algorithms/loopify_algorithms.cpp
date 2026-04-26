#include <loopify_algorithms.h>

#include <functional>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

/// Consolidated UNIQUE list/sequence algorithms.
__attribute__((pure)) unsigned int
LoopifyAlgorithms::len_impl(const List<unsigned int> &l) {
  struct _Enter {
    const List<unsigned int> l;
  };

  struct _Call1 {};

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
        _stack.emplace_back(_Call1{});
        _stack.emplace_back(_Enter{*(d_a1)});
      }
    } else {
      auto _f = std::move(std::get<_Call1>(_frame));
      _result = (_result + 1);
    }
  }
  return _result;
}

/// sieve l Sieve of Eratosthenes - filters out multiples.
__attribute__((pure)) List<unsigned int>
LoopifyAlgorithms::sieve_fuel(const unsigned int &fuel, List<unsigned int> l) {
  std::unique_ptr<List<unsigned int>> _head{};
  std::unique_ptr<List<unsigned int>> *_write = &_head;
  List<unsigned int> _loop_l = std::move(l);
  unsigned int _loop_fuel = fuel;
  while (true) {
    if (_loop_fuel <= 0) {
      *(_write) = std::make_unique<List<unsigned int>>(_loop_l);
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
        List<unsigned int> d_a1_value =
            clone_as_value<List<unsigned int>>(d_a1);
        std::function<List<unsigned int>(unsigned int, List<unsigned int>)>
            filter_multiples;
        filter_multiples = [&](unsigned int p,
                               List<unsigned int> rest) -> List<unsigned int> {
          struct _Enter {
            List<unsigned int> rest;
          };
          struct _Call1 {
            unsigned int _s0;
          };
          using _Frame = std::variant<_Enter, _Call1>;
          List<unsigned int> _result{};
          std::vector<_Frame> _stack;
          _stack.reserve(16);
          _stack.emplace_back(_Enter{rest});
          while (!_stack.empty()) {
            _Frame _frame = std::move(_stack.back());
            _stack.pop_back();
            if (std::holds_alternative<_Enter>(_frame)) {
              auto _f = std::move(std::get<_Enter>(_frame));
              List<unsigned int> rest = _f.rest;
              if (std::holds_alternative<typename List<unsigned int>::Nil>(
                      rest.v())) {
                _result = List<unsigned int>::nil();
              } else {
                const auto &[d_a00, d_a10] =
                    std::get<typename List<unsigned int>::Cons>(rest.v());
                if ((p ? d_a00 % p : d_a00) == 0u) {
                  _stack.emplace_back(_Enter{*(d_a10)});
                } else {
                  _stack.emplace_back(_Call1{d_a00});
                  _stack.emplace_back(_Enter{*(d_a10)});
                }
              }
            } else {
              auto _f = std::move(std::get<_Call1>(_frame));
              _result = List<unsigned int>::cons(_f._s0, _result);
            }
          }
          return _result;
        };
        auto _cell = std::make_unique<List<unsigned int>>(
            typename List<unsigned int>::Cons(d_a0, nullptr));
        *(_write) = std::move(_cell);
        _write =
            &std::get<typename List<unsigned int>::Cons>((*_write)->v_mut())
                 .d_a1;
        List<unsigned int> _next_l = filter_multiples(d_a0, d_a1_value);
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
LoopifyAlgorithms::sieve(const List<unsigned int> &l) {
  return sieve_fuel(len_impl(l), l);
}

/// run_length_encode l encodes consecutive runs: 1,1,2,3,3,3 ->
/// (1,2),(2,1),(3,3).
__attribute__((pure)) List<std::pair<unsigned int, unsigned int>>
LoopifyAlgorithms::run_length_encode(const List<unsigned int> &l) {
  if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
    return List<std::pair<unsigned int, unsigned int>>::nil();
  } else {
    const auto &[d_a0, d_a1] =
        std::get<typename List<unsigned int>::Cons>(l.v());
    auto &&_sv0 = run_length_encode(*(d_a1));
    if (std::holds_alternative<
            typename List<std::pair<unsigned int, unsigned int>>::Nil>(
            _sv0.v())) {
      return List<std::pair<unsigned int, unsigned int>>::cons(
          std::make_pair(d_a0, 1u),
          List<std::pair<unsigned int, unsigned int>>::nil());
    } else {
      const auto &[d_a00, d_a10] =
          std::get<typename List<std::pair<unsigned int, unsigned int>>::Cons>(
              _sv0.v());
      const unsigned int &y = d_a00.first;
      const unsigned int &n = d_a00.second;
      if (d_a0 == y) {
        return List<std::pair<unsigned int, unsigned int>>::cons(
            std::make_pair(y, (n + 1)), *(d_a10));
      } else {
        return List<std::pair<unsigned int, unsigned int>>::cons(
            std::make_pair(d_a0, 1u),
            List<std::pair<unsigned int, unsigned int>>::cons(
                std::make_pair(y, n), *(d_a10)));
      }
    }
  }
}

/// prefix_sums acc l cumulative sums: 1,2,3 with acc=0 -> 0,1,3,6.
__attribute__((pure)) List<unsigned int>
LoopifyAlgorithms::prefix_sums(unsigned int acc, const List<unsigned int> &l) {
  std::unique_ptr<List<unsigned int>> _head{};
  std::unique_ptr<List<unsigned int>> *_write = &_head;
  List<unsigned int> _loop_l = l;
  unsigned int _loop_acc = std::move(acc);
  while (true) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(_loop_l.v())) {
      *(_write) = std::make_unique<List<unsigned int>>(
          List<unsigned int>::cons(_loop_acc, List<unsigned int>::nil()));
      break;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<unsigned int>::Cons>(_loop_l.v());
      auto _cell = std::make_unique<List<unsigned int>>(
          typename List<unsigned int>::Cons(_loop_acc, nullptr));
      *(_write) = std::move(_cell);
      _write =
          &std::get<typename List<unsigned int>::Cons>((*_write)->v_mut()).d_a1;
      List<unsigned int> _next_l = *(d_a1);
      unsigned int _next_acc = (_loop_acc + d_a0);
      _loop_l = std::move(_next_l);
      _loop_acc = std::move(_next_acc);
      continue;
    }
  }
  return std::move(*(_head));
}

/// differences l consecutive differences: 5,3,8,2 -> -2,5,-6.
__attribute__((pure)) List<unsigned int>
LoopifyAlgorithms::differences(const List<unsigned int> &l) {
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

/// rotate_left n l rotates list left by n positions.
__attribute__((pure)) List<unsigned int> LoopifyAlgorithms::rotate_left_fuel(
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
      if (_loop_n <= 0u) {
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
LoopifyAlgorithms::rotate_left(const unsigned int &n,
                               const List<unsigned int> &l) {
  return rotate_left_fuel(n, n, l);
}

/// nub l removes ALL duplicates (not just consecutive): 1,2,1,3,2 -> 1,2,3.
__attribute__((pure)) List<unsigned int>
LoopifyAlgorithms::nub_aux(const List<unsigned int> &l,
                           const unsigned int &fuel) {
  std::unique_ptr<List<unsigned int>> _head{};
  std::unique_ptr<List<unsigned int>> *_write = &_head;
  unsigned int _loop_fuel = fuel;
  List<unsigned int> _loop_l = l;
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
        List<unsigned int> d_a1_value =
            clone_as_value<List<unsigned int>>(d_a1);
        std::function<List<unsigned int>(unsigned int, List<unsigned int>)>
            filter_out;
        filter_out = [&](unsigned int val,
                         List<unsigned int> rest) -> List<unsigned int> {
          struct _Enter {
            List<unsigned int> rest;
          };
          struct _Call1 {
            unsigned int _s0;
          };
          using _Frame = std::variant<_Enter, _Call1>;
          List<unsigned int> _result{};
          std::vector<_Frame> _stack;
          _stack.reserve(16);
          _stack.emplace_back(_Enter{rest});
          while (!_stack.empty()) {
            _Frame _frame = std::move(_stack.back());
            _stack.pop_back();
            if (std::holds_alternative<_Enter>(_frame)) {
              auto _f = std::move(std::get<_Enter>(_frame));
              List<unsigned int> rest = _f.rest;
              if (std::holds_alternative<typename List<unsigned int>::Nil>(
                      rest.v())) {
                _result = List<unsigned int>::nil();
              } else {
                const auto &[d_a00, d_a10] =
                    std::get<typename List<unsigned int>::Cons>(rest.v());
                if (val == d_a00) {
                  _stack.emplace_back(_Enter{*(d_a10)});
                } else {
                  _stack.emplace_back(_Call1{d_a00});
                  _stack.emplace_back(_Enter{*(d_a10)});
                }
              }
            } else {
              auto _f = std::move(std::get<_Call1>(_frame));
              _result = List<unsigned int>::cons(_f._s0, _result);
            }
          }
          return _result;
        };
        auto _cell = std::make_unique<List<unsigned int>>(
            typename List<unsigned int>::Cons(d_a0, nullptr));
        *(_write) = std::move(_cell);
        _write =
            &std::get<typename List<unsigned int>::Cons>((*_write)->v_mut())
                 .d_a1;
        unsigned int _next_fuel = f;
        List<unsigned int> _next_l = filter_out(d_a0, d_a1_value);
        _loop_fuel = std::move(_next_fuel);
        _loop_l = std::move(_next_l);
        continue;
      }
    }
  }
  return std::move(*(_head));
}

__attribute__((pure)) List<unsigned int>
LoopifyAlgorithms::nub(const List<unsigned int> &l) {
  return nub_aux(l, len_impl(l));
}

/// Internal helpers for palindrome check.
__attribute__((pure)) List<unsigned int>
LoopifyAlgorithms::rev_impl(List<unsigned int> acc,
                            const List<unsigned int> &l) {
  List<unsigned int> _result;
  List<unsigned int> _loop_l = l;
  List<unsigned int> _loop_acc = std::move(acc);
  while (true) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(_loop_l.v())) {
      _result = _loop_acc;
      break;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<unsigned int>::Cons>(_loop_l.v());
      List<unsigned int> _next_l = *(d_a1);
      List<unsigned int> _next_acc = List<unsigned int>::cons(d_a0, _loop_acc);
      _loop_l = std::move(_next_l);
      _loop_acc = std::move(_next_acc);
    }
  }
  return _result;
}

__attribute__((pure)) bool
LoopifyAlgorithms::list_eq_impl(const List<unsigned int> &l1,
                                const List<unsigned int> &l2) {
  bool _result;
  List<unsigned int> _loop_l2 = l2;
  List<unsigned int> _loop_l1 = l1;
  while (true) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(
            _loop_l1.v())) {
      if (std::holds_alternative<typename List<unsigned int>::Nil>(
              _loop_l2.v())) {
        _result = true;
        break;
      } else {
        _result = false;
        break;
      }
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

/// is_palindrome l checks if list reads same forwards and backwards.
__attribute__((pure)) bool
LoopifyAlgorithms::is_palindrome(const List<unsigned int> &l) {
  return list_eq_impl(l, rev_impl(List<unsigned int>::nil(), l));
}

/// windows n l sliding windows of size n: windows 2 1,2,3,4 ->
/// [1,2],[2,3],[3,4].
__attribute__((pure)) List<unsigned int>
LoopifyAlgorithms::take_impl(const unsigned int &k,
                             const List<unsigned int> &l) {
  std::unique_ptr<List<unsigned int>> _head{};
  std::unique_ptr<List<unsigned int>> *_write = &_head;
  List<unsigned int> _loop_l = l;
  unsigned int _loop_k = k;
  while (true) {
    if (_loop_k <= 0) {
      *(_write) =
          std::make_unique<List<unsigned int>>(List<unsigned int>::nil());
      break;
    } else {
      unsigned int m = _loop_k - 1;
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
        unsigned int _next_k = m;
        _loop_l = std::move(_next_l);
        _loop_k = std::move(_next_k);
        continue;
      }
    }
  }
  return std::move(*(_head));
}

__attribute__((pure)) List<List<unsigned int>>
LoopifyAlgorithms::windows_aux(const unsigned int &n,
                               const List<unsigned int> &l,
                               const unsigned int &fuel) {
  std::unique_ptr<List<List<unsigned int>>> _head{};
  std::unique_ptr<List<List<unsigned int>>> *_write = &_head;
  unsigned int _loop_fuel = fuel;
  List<unsigned int> _loop_l = l;
  while (true) {
    if (_loop_fuel <= 0) {
      *(_write) = std::make_unique<List<List<unsigned int>>>(
          List<List<unsigned int>>::nil());
      break;
    } else {
      unsigned int f = _loop_fuel - 1;
      if (std::holds_alternative<typename List<unsigned int>::Nil>(
              _loop_l.v())) {
        *(_write) = std::make_unique<List<List<unsigned int>>>(
            List<List<unsigned int>>::nil());
        break;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<unsigned int>::Cons>(_loop_l.v());
        if (len_impl(_loop_l) < n) {
          *(_write) = std::make_unique<List<List<unsigned int>>>(
              List<List<unsigned int>>::nil());
          break;
        } else {
          auto _cell = std::make_unique<List<List<unsigned int>>>(
              typename List<List<unsigned int>>::Cons(take_impl(n, _loop_l),
                                                      nullptr));
          *(_write) = std::move(_cell);
          _write = &std::get<typename List<List<unsigned int>>::Cons>(
                        (*_write)->v_mut())
                        .d_a1;
          unsigned int _next_fuel = f;
          List<unsigned int> _next_l = *(d_a1);
          _loop_fuel = std::move(_next_fuel);
          _loop_l = std::move(_next_l);
          continue;
        }
      }
    }
  }
  return std::move(*(_head));
}

__attribute__((pure)) List<List<unsigned int>>
LoopifyAlgorithms::windows(const unsigned int &n, const List<unsigned int> &l) {
  return windows_aux(n, l, (len_impl(l) + 1));
}

/// sliding_pairs l returns consecutive pairs: 1,2,3,4 -> (1,2),(2,3),(3,4).
__attribute__((pure)) List<std::pair<unsigned int, unsigned int>>
LoopifyAlgorithms::sliding_pairs(const List<unsigned int> &l) {
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
      auto &&_sv0 = *(d_a1);
      if (std::holds_alternative<typename List<unsigned int>::Nil>(_sv0.v())) {
        *(_write) =
            std::make_unique<List<std::pair<unsigned int, unsigned int>>>(
                List<std::pair<unsigned int, unsigned int>>::nil());
        break;
      } else {
        const auto &[d_a00, d_a10] =
            std::get<typename List<unsigned int>::Cons>(_sv0.v());
        auto _cell =
            std::make_unique<List<std::pair<unsigned int, unsigned int>>>(
                typename List<std::pair<unsigned int, unsigned int>>::Cons(
                    std::make_pair(d_a0, d_a00), nullptr));
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
  return std::move(*(_head));
}

/// max_prefix_sum l maximum sum of prefix (Kadane-like pattern).
__attribute__((pure)) unsigned int
LoopifyAlgorithms::max_prefix_sum(const List<unsigned int> &l) {
  struct _Enter {
    const List<unsigned int> l;
  };

  struct _Call1 {
    unsigned int _s0;
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
        _stack.emplace_back(_Call1{d_a0});
        _stack.emplace_back(_Enter{*(d_a1)});
      }
    } else {
      auto _f = std::move(std::get<_Call1>(_frame));
      unsigned int d_a0 = _f._s0;
      unsigned int rest = _result;
      unsigned int sum = (d_a0 + rest);
      if (rest == 0u) {
        _result = 0u;
      } else {
        if (rest < sum) {
          _result = sum;
        } else {
          _result = rest;
        }
      }
    }
  }
  return _result;
}

/// weighted_sum i l computes weighted sum with increasing index.
__attribute__((pure)) unsigned int
LoopifyAlgorithms::weighted_sum(unsigned int i, const List<unsigned int> &l) {
  struct _Enter {
    const List<unsigned int> l;
    unsigned int i;
  };

  struct _Call1 {
    decltype((std::declval<unsigned int &>() *
              std::declval<unsigned int &>())) _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{l, i});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<unsigned int> l = _f.l;
      unsigned int i = _f.i;
      if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
        _result = 0u;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<unsigned int>::Cons>(l.v());
        _stack.emplace_back(_Call1{(i * d_a0)});
        _stack.emplace_back(_Enter{*(d_a1), (i + 1)});
      }
    } else {
      auto _f = std::move(std::get<_Call1>(_frame));
      _result = (_f._s0 + _result);
    }
  }
  return _result;
}

/// step_sum l sums with conditional doubling for odd numbers.
__attribute__((pure)) unsigned int
LoopifyAlgorithms::step_sum(const List<unsigned int> &l) {
  struct _Enter {
    const List<unsigned int> l;
  };

  struct _Call1 {
    unsigned int _s0;
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
        unsigned int contribution;
        if ((2u ? d_a0 % 2u : d_a0) == 0u) {
          contribution = d_a0;
        } else {
          contribution = (d_a0 * 2u);
        }
        _stack.emplace_back(_Call1{contribution});
        _stack.emplace_back(_Enter{*(d_a1)});
      }
    } else {
      auto _f = std::move(std::get<_Call1>(_frame));
      _result = (_f._s0 + _result);
    }
  }
  return _result;
}

/// Helper: get head with default value.
__attribute__((pure)) unsigned int
LoopifyAlgorithms::head_nat(unsigned int d, const List<unsigned int> &l) {
  if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
    return d;
  } else {
    const auto &[d_a0, d_a1] =
        std::get<typename List<unsigned int>::Cons>(l.v());
    return d_a0;
  }
}

/// suffix_sums l computes suffix sums (reverse of prefix sums).
__attribute__((pure)) List<unsigned int>
LoopifyAlgorithms::suffix_sums(const List<unsigned int> &l) {
  struct _Enter {
    const List<unsigned int> l;
  };

  struct _Call1 {
    unsigned int _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  List<unsigned int> _result{};
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
        _result = List<unsigned int>::nil();
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<unsigned int>::Cons>(l.v());
        _stack.emplace_back(_Call1{d_a0});
        _stack.emplace_back(_Enter{*(d_a1)});
      }
    } else {
      auto _f = std::move(std::get<_Call1>(_frame));
      unsigned int d_a0 = _f._s0;
      List<unsigned int> rest = _result;
      _result = List<unsigned int>::cons((d_a0 + head_nat(0u, rest)), rest);
    }
  }
  return _result;
}
