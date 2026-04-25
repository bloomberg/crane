#include <loopify_lists.h>

#include <functional>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

/// Consolidated UNIQUE list operations - no stdlib duplicates.
/// Tests loopification on domain-specific list algorithms.
/// range start count generates start, start+1, ..., start+count-1.
__attribute__((pure)) LoopifyLists::list<unsigned int>
LoopifyLists::range(unsigned int start, const unsigned int &count0) {
  std::unique_ptr<LoopifyLists::list<unsigned int>> _head{};
  std::unique_ptr<LoopifyLists::list<unsigned int>> *_write = &_head;
  unsigned int _loop_count0 = count0;
  unsigned int _loop_start = std::move(start);
  while (true) {
    if (_loop_count0 <= 0) {
      *(_write) = std::make_unique<LoopifyLists::list<unsigned int>>(
          list<unsigned int>::nil());
      break;
    } else {
      unsigned int c = _loop_count0 - 1;
      auto _cell = std::make_unique<LoopifyLists::list<unsigned int>>(
          typename list<unsigned int>::Cons(_loop_start, nullptr));
      *(_write) = std::move(_cell);
      _write =
          &std::get<typename list<unsigned int>::Cons>((*_write)->v_mut()).d_a1;
      unsigned int _next_count0 = c;
      unsigned int _next_start = (_loop_start + 1);
      _loop_count0 = std::move(_next_count0);
      _loop_start = std::move(_next_start);
      continue;
    }
  }
  return std::move(*(_head));
}

/// step_sum l sums with conditional contributions: even values as-is, odd
/// doubled.
__attribute__((pure)) unsigned int
LoopifyLists::step_sum(const LoopifyLists::list<unsigned int> &l) {
  struct _Enter {
    const LoopifyLists::list<unsigned int> l;
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
      const LoopifyLists::list<unsigned int> l = _f.l;
      if (std::holds_alternative<
              typename LoopifyLists::list<unsigned int>::Nil>(l.v())) {
        _result = 0u;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename LoopifyLists::list<unsigned int>::Cons>(l.v());
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

/// sum_abs l sums absolute values (using monus for nat).
__attribute__((pure)) unsigned int
LoopifyLists::sum_abs(const LoopifyLists::list<unsigned int> &l,
                      const unsigned int &base) {
  struct _Enter {
    const LoopifyLists::list<unsigned int> l;
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
      const LoopifyLists::list<unsigned int> l = _f.l;
      if (std::holds_alternative<
              typename LoopifyLists::list<unsigned int>::Nil>(l.v())) {
        _result = 0u;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename LoopifyLists::list<unsigned int>::Cons>(l.v());
        unsigned int abs_val;
        if (base <= d_a0) {
          abs_val = (((d_a0 - base) > d_a0 ? 0 : (d_a0 - base)));
        } else {
          abs_val = (((base - d_a0) > base ? 0 : (base - d_a0)));
        }
        _stack.emplace_back(_Call1{abs_val});
        _stack.emplace_back(_Enter{*(d_a1)});
      }
    } else {
      auto _f = std::move(std::get<_Call1>(_frame));
      _result = (_f._s0 + _result);
    }
  }
  return _result;
}

/// four_elem l multi-case pattern matching on list structure.
__attribute__((pure)) unsigned int
LoopifyLists::four_elem(const LoopifyLists::list<unsigned int> &l) {
  struct _Enter {
    const LoopifyLists::list<unsigned int> l;
  };

  struct _Call1 {
    decltype((std::declval<unsigned int &>() +
              std::declval<unsigned int &>())) _s0;
    decltype((std::declval<unsigned int &>() +
              std::declval<unsigned int &>())) _s1;
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
      const LoopifyLists::list<unsigned int> l = _f.l;
      if (std::holds_alternative<
              typename LoopifyLists::list<unsigned int>::Nil>(l.v())) {
        _result = 0u;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename LoopifyLists::list<unsigned int>::Cons>(l.v());
        auto &&_sv0 = *(d_a1);
        if (std::holds_alternative<
                typename LoopifyLists::list<unsigned int>::Nil>(_sv0.v())) {
          _result = 1u;
        } else {
          const auto &[d_a00, d_a10] =
              std::get<typename LoopifyLists::list<unsigned int>::Cons>(
                  _sv0.v());
          auto &&_sv1 = *(d_a10);
          if (std::holds_alternative<
                  typename LoopifyLists::list<unsigned int>::Nil>(_sv1.v())) {
            _result = 2u;
          } else {
            const auto &[d_a01, d_a11] =
                std::get<typename LoopifyLists::list<unsigned int>::Cons>(
                    _sv1.v());
            auto &&_sv2 = *(d_a11);
            if (std::holds_alternative<
                    typename LoopifyLists::list<unsigned int>::Nil>(_sv2.v())) {
              _result = 3u;
            } else {
              const auto &[d_a02, d_a12] =
                  std::get<typename LoopifyLists::list<unsigned int>::Cons>(
                      _sv2.v());
              _stack.emplace_back(_Call1{(d_a0 + d_a00), (d_a01 + d_a02)});
              _stack.emplace_back(_Enter{*(d_a12)});
            }
          }
        }
      }
    } else {
      auto _f = std::move(std::get<_Call1>(_frame));
      _result = (_f._s0 + (_f._s1 + _result));
    }
  }
  return _result;
}

/// between lo hi l filters elements in range lo, hi.
__attribute__((pure)) LoopifyLists::list<unsigned int>
LoopifyLists::between(const unsigned int &lo, const unsigned int &hi,
                      const LoopifyLists::list<unsigned int> &l) {
  std::unique_ptr<LoopifyLists::list<unsigned int>> _head{};
  std::unique_ptr<LoopifyLists::list<unsigned int>> *_write = &_head;
  LoopifyLists::list<unsigned int> _loop_l = l;
  while (true) {
    if (std::holds_alternative<typename LoopifyLists::list<unsigned int>::Nil>(
            _loop_l.v())) {
      *(_write) = std::make_unique<LoopifyLists::list<unsigned int>>(
          list<unsigned int>::nil());
      break;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename LoopifyLists::list<unsigned int>::Cons>(
              _loop_l.v());
      if ((lo <= d_a0 && d_a0 <= hi)) {
        auto _cell = std::make_unique<LoopifyLists::list<unsigned int>>(
            typename list<unsigned int>::Cons(d_a0, nullptr));
        *(_write) = std::move(_cell);
        _write =
            &std::get<typename list<unsigned int>::Cons>((*_write)->v_mut())
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

/// categorize k l categorizes elements: 1 for <k, 2 for =k, 3 for >k.
__attribute__((pure)) unsigned int
LoopifyLists::categorize(const unsigned int &k,
                         const LoopifyLists::list<unsigned int> &l) {
  struct _Enter {
    const LoopifyLists::list<unsigned int> l;
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
      const LoopifyLists::list<unsigned int> l = _f.l;
      if (std::holds_alternative<
              typename LoopifyLists::list<unsigned int>::Nil>(l.v())) {
        _result = 0u;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename LoopifyLists::list<unsigned int>::Cons>(l.v());
        unsigned int score;
        if (k < d_a0) {
          score = 3u;
        } else {
          if (d_a0 == k) {
            score = 2u;
          } else {
            score = 1u;
          }
        }
        _stack.emplace_back(_Call1{score});
        _stack.emplace_back(_Enter{*(d_a1)});
      }
    } else {
      auto _f = std::move(std::get<_Call1>(_frame));
      _result = (_f._s0 + _result);
    }
  }
  return _result;
}

/// max_prefix_sum l maximum prefix sum (Kadane-like).
__attribute__((pure)) unsigned int
LoopifyLists::max_prefix_sum(const LoopifyLists::list<unsigned int> &l) {
  struct _Enter {
    const LoopifyLists::list<unsigned int> l;
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
      const LoopifyLists::list<unsigned int> l = _f.l;
      if (std::holds_alternative<
              typename LoopifyLists::list<unsigned int>::Nil>(l.v())) {
        _result = 0u;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename LoopifyLists::list<unsigned int>::Cons>(l.v());
        _stack.emplace_back(_Call1{d_a0});
        _stack.emplace_back(_Enter{*(d_a1)});
      }
    } else {
      auto _f = std::move(std::get<_Call1>(_frame));
      unsigned int d_a0 = _f._s0;
      unsigned int rest = _result;
      unsigned int sum = (d_a0 + rest);
      if (0u <= sum) {
        _result = sum;
      } else {
        _result = 0u;
      }
    }
  }
  return _result;
}

/// pairwise_sum l sums consecutive pairs: 1,2,3,4 -> 3,7.
__attribute__((pure)) LoopifyLists::list<unsigned int>
LoopifyLists::pairwise_sum(const LoopifyLists::list<unsigned int> &l) {
  std::unique_ptr<LoopifyLists::list<unsigned int>> _head{};
  std::unique_ptr<LoopifyLists::list<unsigned int>> *_write = &_head;
  LoopifyLists::list<unsigned int> _loop_l = l;
  while (true) {
    if (std::holds_alternative<typename LoopifyLists::list<unsigned int>::Nil>(
            _loop_l.v())) {
      *(_write) = std::make_unique<LoopifyLists::list<unsigned int>>(
          list<unsigned int>::nil());
      break;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename LoopifyLists::list<unsigned int>::Cons>(
              _loop_l.v());
      auto &&_sv0 = *(d_a1);
      if (std::holds_alternative<
              typename LoopifyLists::list<unsigned int>::Nil>(_sv0.v())) {
        *(_write) = std::make_unique<LoopifyLists::list<unsigned int>>(
            list<unsigned int>::nil());
        break;
      } else {
        const auto &[d_a00, d_a10] =
            std::get<typename LoopifyLists::list<unsigned int>::Cons>(_sv0.v());
        auto _cell = std::make_unique<LoopifyLists::list<unsigned int>>(
            typename list<unsigned int>::Cons((d_a0 + d_a00), nullptr));
        *(_write) = std::move(_cell);
        _write =
            &std::get<typename list<unsigned int>::Cons>((*_write)->v_mut())
                 .d_a1;
        _loop_l = *(d_a10);
        continue;
      }
    }
  }
  return std::move(*(_head));
}

/// weighted_sum i l weighted sum with increasing weights.
__attribute__((pure)) unsigned int
LoopifyLists::weighted_sum(unsigned int i,
                           const LoopifyLists::list<unsigned int> &l) {
  struct _Enter {
    const LoopifyLists::list<unsigned int> l;
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
      const LoopifyLists::list<unsigned int> l = _f.l;
      unsigned int i = _f.i;
      if (std::holds_alternative<
              typename LoopifyLists::list<unsigned int>::Nil>(l.v())) {
        _result = 0u;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename LoopifyLists::list<unsigned int>::Cons>(l.v());
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

/// prefix_sums acc l returns all prefix sums: 1,2,3 -> 0,1,3,6.
__attribute__((pure)) LoopifyLists::list<unsigned int>
LoopifyLists::prefix_sums(unsigned int acc,
                          const LoopifyLists::list<unsigned int> &l) {
  std::unique_ptr<LoopifyLists::list<unsigned int>> _head{};
  std::unique_ptr<LoopifyLists::list<unsigned int>> *_write = &_head;
  LoopifyLists::list<unsigned int> _loop_l = l;
  unsigned int _loop_acc = std::move(acc);
  while (true) {
    if (std::holds_alternative<typename LoopifyLists::list<unsigned int>::Nil>(
            _loop_l.v())) {
      *(_write) = std::make_unique<LoopifyLists::list<unsigned int>>(
          list<unsigned int>::cons(_loop_acc, list<unsigned int>::nil()));
      break;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename LoopifyLists::list<unsigned int>::Cons>(
              _loop_l.v());
      auto _cell = std::make_unique<LoopifyLists::list<unsigned int>>(
          typename list<unsigned int>::Cons(_loop_acc, nullptr));
      *(_write) = std::move(_cell);
      _write =
          &std::get<typename list<unsigned int>::Cons>((*_write)->v_mut()).d_a1;
      LoopifyLists::list<unsigned int> _next_l = *(d_a1);
      unsigned int _next_acc = (_loop_acc + d_a0);
      _loop_l = std::move(_next_l);
      _loop_acc = std::move(_next_acc);
      continue;
    }
  }
  return std::move(*(_head));
}

/// uniq_sorted l removes consecutive duplicates from sorted list.
__attribute__((pure)) LoopifyLists::list<unsigned int>
LoopifyLists::uniq_sorted(const LoopifyLists::list<unsigned int> &l) {
  std::unique_ptr<LoopifyLists::list<unsigned int>> _head{};
  std::unique_ptr<LoopifyLists::list<unsigned int>> *_write = &_head;
  LoopifyLists::list<unsigned int> _loop_l = l;
  while (true) {
    if (std::holds_alternative<typename LoopifyLists::list<unsigned int>::Nil>(
            _loop_l.v())) {
      *(_write) = std::make_unique<LoopifyLists::list<unsigned int>>(
          list<unsigned int>::nil());
      break;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename LoopifyLists::list<unsigned int>::Cons>(
              _loop_l.v());
      auto &&_sv0 = *(d_a1);
      if (std::holds_alternative<
              typename LoopifyLists::list<unsigned int>::Nil>(_sv0.v())) {
        *(_write) = std::make_unique<LoopifyLists::list<unsigned int>>(
            list<unsigned int>::cons(d_a0, list<unsigned int>::nil()));
        break;
      } else {
        const auto &[d_a00, d_a10] =
            std::get<typename LoopifyLists::list<unsigned int>::Cons>(_sv0.v());
        if (d_a0 == d_a00) {
          _loop_l = *(d_a1);
          continue;
        } else {
          auto _cell = std::make_unique<LoopifyLists::list<unsigned int>>(
              typename list<unsigned int>::Cons(d_a0, nullptr));
          *(_write) = std::move(_cell);
          _write =
              &std::get<typename list<unsigned int>::Cons>((*_write)->v_mut())
                   .d_a1;
          _loop_l = *(d_a1);
          continue;
        }
      }
    }
  }
  return std::move(*(_head));
}

/// Helper: take first n elements.
__attribute__((pure)) LoopifyLists::list<unsigned int>
LoopifyLists::take_n(const unsigned int &n,
                     const LoopifyLists::list<unsigned int> &l) {
  std::unique_ptr<LoopifyLists::list<unsigned int>> _head{};
  std::unique_ptr<LoopifyLists::list<unsigned int>> *_write = &_head;
  LoopifyLists::list<unsigned int> _loop_l = l;
  unsigned int _loop_n = n;
  while (true) {
    if (_loop_n <= 0) {
      *(_write) = std::make_unique<LoopifyLists::list<unsigned int>>(
          list<unsigned int>::nil());
      break;
    } else {
      unsigned int m = _loop_n - 1;
      if (std::holds_alternative<
              typename LoopifyLists::list<unsigned int>::Nil>(_loop_l.v())) {
        *(_write) = std::make_unique<LoopifyLists::list<unsigned int>>(
            list<unsigned int>::nil());
        break;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename LoopifyLists::list<unsigned int>::Cons>(
                _loop_l.v());
        auto _cell = std::make_unique<LoopifyLists::list<unsigned int>>(
            typename list<unsigned int>::Cons(d_a0, nullptr));
        *(_write) = std::move(_cell);
        _write =
            &std::get<typename list<unsigned int>::Cons>((*_write)->v_mut())
                 .d_a1;
        LoopifyLists::list<unsigned int> _next_l = *(d_a1);
        unsigned int _next_n = m;
        _loop_l = std::move(_next_l);
        _loop_n = std::move(_next_n);
        continue;
      }
    }
  }
  return std::move(*(_head));
}

/// Helper: list length.
__attribute__((pure)) unsigned int
LoopifyLists::len_list(const LoopifyLists::list<unsigned int> &l) {
  struct _Enter {
    const LoopifyLists::list<unsigned int> l;
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
      const LoopifyLists::list<unsigned int> l = _f.l;
      if (std::holds_alternative<
              typename LoopifyLists::list<unsigned int>::Nil>(l.v())) {
        _result = 0u;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename LoopifyLists::list<unsigned int>::Cons>(l.v());
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

/// windows n l returns all sliding windows of size n.
__attribute__((pure)) LoopifyLists::list<LoopifyLists::list<unsigned int>>
LoopifyLists::windows_aux(const unsigned int &fuel, const unsigned int &n,
                          const LoopifyLists::list<unsigned int> &l) {
  std::unique_ptr<LoopifyLists::list<LoopifyLists::list<unsigned int>>> _head{};
  std::unique_ptr<LoopifyLists::list<LoopifyLists::list<unsigned int>>>
      *_write = &_head;
  LoopifyLists::list<unsigned int> _loop_l = l;
  unsigned int _loop_fuel = fuel;
  while (true) {
    if (_loop_fuel <= 0) {
      *(_write) = std::make_unique<
          LoopifyLists::list<LoopifyLists::list<unsigned int>>>(
          list<LoopifyLists::list<unsigned int>>::nil());
      break;
    } else {
      unsigned int f = _loop_fuel - 1;
      if (std::holds_alternative<
              typename LoopifyLists::list<unsigned int>::Nil>(_loop_l.v())) {
        *(_write) = std::make_unique<
            LoopifyLists::list<LoopifyLists::list<unsigned int>>>(
            list<LoopifyLists::list<unsigned int>>::nil());
        break;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename LoopifyLists::list<unsigned int>::Cons>(
                _loop_l.v());
        if (len_list(_loop_l) < n) {
          *(_write) = std::make_unique<
              LoopifyLists::list<LoopifyLists::list<unsigned int>>>(
              list<LoopifyLists::list<unsigned int>>::nil());
          break;
        } else {
          LoopifyLists::list<unsigned int> window = take_n(n, _loop_l);
          if (std::holds_alternative<
                  typename LoopifyLists::list<unsigned int>::Nil>(window.v())) {
            *(_write) = std::make_unique<
                LoopifyLists::list<LoopifyLists::list<unsigned int>>>(
                list<LoopifyLists::list<unsigned int>>::nil());
            break;
          } else {
            auto _cell = std::make_unique<
                LoopifyLists::list<LoopifyLists::list<unsigned int>>>(
                typename list<LoopifyLists::list<unsigned int>>::Cons(window,
                                                                      nullptr));
            *(_write) = std::move(_cell);
            _write =
                &std::get<
                     typename list<LoopifyLists::list<unsigned int>>::Cons>(
                     (*_write)->v_mut())
                     .d_a1;
            LoopifyLists::list<unsigned int> _next_l = *(d_a1);
            unsigned int _next_fuel = f;
            _loop_l = std::move(_next_l);
            _loop_fuel = std::move(_next_fuel);
            continue;
          }
        }
      }
    }
  }
  return std::move(*(_head));
}

__attribute__((pure)) LoopifyLists::list<LoopifyLists::list<unsigned int>>
LoopifyLists::windows(const unsigned int &n,
                      const LoopifyLists::list<unsigned int> &l) {
  return windows_aux((len_list(l) + 1), n, l);
}

/// is_prefix_of l1 l2 checks if l1 is a prefix of l2.
__attribute__((pure)) bool
LoopifyLists::is_prefix_of(const LoopifyLists::list<unsigned int> &l1,
                           const LoopifyLists::list<unsigned int> &l2) {
  bool _result;
  LoopifyLists::list<unsigned int> _loop_l2 = l2;
  LoopifyLists::list<unsigned int> _loop_l1 = l1;
  while (true) {
    if (std::holds_alternative<typename LoopifyLists::list<unsigned int>::Nil>(
            _loop_l1.v())) {
      _result = true;
      break;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename LoopifyLists::list<unsigned int>::Cons>(
              _loop_l1.v());
      if (std::holds_alternative<
              typename LoopifyLists::list<unsigned int>::Nil>(_loop_l2.v())) {
        _result = false;
        break;
      } else {
        const auto &[d_a00, d_a10] =
            std::get<typename LoopifyLists::list<unsigned int>::Cons>(
                _loop_l2.v());
        if (d_a0 == d_a00) {
          LoopifyLists::list<unsigned int> _next_l2 = *(d_a10);
          LoopifyLists::list<unsigned int> _next_l1 = *(d_a1);
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

/// lookup_all key l finds all values for key in association list.
__attribute__((pure)) LoopifyLists::list<unsigned int> LoopifyLists::lookup_all(
    const unsigned int &key,
    const LoopifyLists::list<std::pair<unsigned int, unsigned int>> &l) {
  std::unique_ptr<LoopifyLists::list<unsigned int>> _head{};
  std::unique_ptr<LoopifyLists::list<unsigned int>> *_write = &_head;
  LoopifyLists::list<std::pair<unsigned int, unsigned int>> _loop_l = l;
  while (true) {
    if (std::holds_alternative<typename LoopifyLists::list<
            std::pair<unsigned int, unsigned int>>::Nil>(_loop_l.v())) {
      *(_write) = std::make_unique<LoopifyLists::list<unsigned int>>(
          list<unsigned int>::nil());
      break;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename LoopifyLists::list<
          std::pair<unsigned int, unsigned int>>::Cons>(_loop_l.v());
      const unsigned int &k = d_a0.first;
      const unsigned int &v = d_a0.second;
      if (k == key) {
        auto _cell = std::make_unique<LoopifyLists::list<unsigned int>>(
            typename list<unsigned int>::Cons(v, nullptr));
        *(_write) = std::move(_cell);
        _write =
            &std::get<typename list<unsigned int>::Cons>((*_write)->v_mut())
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

/// member x l checks if x is in the list.
__attribute__((pure)) bool
LoopifyLists::member(const unsigned int &x,
                     const LoopifyLists::list<unsigned int> &l) {
  bool _result;
  LoopifyLists::list<unsigned int> _loop_l = l;
  while (true) {
    if (std::holds_alternative<typename LoopifyLists::list<unsigned int>::Nil>(
            _loop_l.v())) {
      _result = false;
      break;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename LoopifyLists::list<unsigned int>::Cons>(
              _loop_l.v());
      if (x == d_a0) {
        _result = true;
        break;
      } else {
        _loop_l = *(d_a1);
      }
    }
  }
  return _result;
}

/// product l multiplies all elements in the list.
__attribute__((pure)) unsigned int
LoopifyLists::product(const LoopifyLists::list<unsigned int> &l) {
  struct _Enter {
    const LoopifyLists::list<unsigned int> l;
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
      const LoopifyLists::list<unsigned int> l = _f.l;
      if (std::holds_alternative<
              typename LoopifyLists::list<unsigned int>::Nil>(l.v())) {
        _result = 1u;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename LoopifyLists::list<unsigned int>::Cons>(l.v());
        _stack.emplace_back(_Call1{d_a0});
        _stack.emplace_back(_Enter{*(d_a1)});
      }
    } else {
      auto _f = std::move(std::get<_Call1>(_frame));
      _result = (_f._s0 * _result);
    }
  }
  return _result;
}

/// sum_list l sums all elements in the list.
__attribute__((pure)) unsigned int
LoopifyLists::sum_list(const LoopifyLists::list<unsigned int> &l) {
  struct _Enter {
    const LoopifyLists::list<unsigned int> l;
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
      const LoopifyLists::list<unsigned int> l = _f.l;
      if (std::holds_alternative<
              typename LoopifyLists::list<unsigned int>::Nil>(l.v())) {
        _result = 0u;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename LoopifyLists::list<unsigned int>::Cons>(l.v());
        _stack.emplace_back(_Call1{d_a0});
        _stack.emplace_back(_Enter{*(d_a1)});
      }
    } else {
      auto _f = std::move(std::get<_Call1>(_frame));
      _result = (_f._s0 + _result);
    }
  }
  return _result;
}

/// flatten_nested l alternative flatten with different pattern: flattens one
/// level at a time. Pattern:  :: rest -> flatten rest, (x :: xs) :: rest -> x
/// :: flatten (xs :: rest).
__attribute__((pure)) LoopifyLists::list<unsigned int>
LoopifyLists::flatten_nested_fuel(
    const unsigned int &fuel,
    const LoopifyLists::list<LoopifyLists::list<unsigned int>> &l) {
  std::unique_ptr<LoopifyLists::list<unsigned int>> _head{};
  std::unique_ptr<LoopifyLists::list<unsigned int>> *_write = &_head;
  LoopifyLists::list<LoopifyLists::list<unsigned int>> _loop_l = l;
  unsigned int _loop_fuel = fuel;
  while (true) {
    if (_loop_fuel <= 0) {
      *(_write) = std::make_unique<LoopifyLists::list<unsigned int>>(
          list<unsigned int>::nil());
      break;
    } else {
      unsigned int f = _loop_fuel - 1;
      if (std::holds_alternative<typename LoopifyLists::list<
              LoopifyLists::list<unsigned int>>::Nil>(_loop_l.v())) {
        *(_write) = std::make_unique<LoopifyLists::list<unsigned int>>(
            list<unsigned int>::nil());
        break;
      } else {
        const auto &[d_a0, d_a1] = std::get<typename LoopifyLists::list<
            LoopifyLists::list<unsigned int>>::Cons>(_loop_l.v());
        auto &&_sv0 = clone_as_value<LoopifyLists::list<unsigned int>>(d_a0);
        if (std::holds_alternative<
                typename LoopifyLists::list<unsigned int>::Nil>(_sv0.v())) {
          LoopifyLists::list<LoopifyLists::list<unsigned int>> _next_l =
              *(d_a1);
          unsigned int _next_fuel = f;
          _loop_l = std::move(_next_l);
          _loop_fuel = std::move(_next_fuel);
          continue;
        } else {
          const auto &[d_a00, d_a10] =
              std::get<typename LoopifyLists::list<unsigned int>::Cons>(
                  _sv0.v());
          auto _cell = std::make_unique<LoopifyLists::list<unsigned int>>(
              typename list<unsigned int>::Cons(d_a00, nullptr));
          *(_write) = std::move(_cell);
          _write =
              &std::get<typename list<unsigned int>::Cons>((*_write)->v_mut())
                   .d_a1;
          LoopifyLists::list<LoopifyLists::list<unsigned int>> _next_l =
              list<LoopifyLists::list<unsigned int>>::cons(*(d_a10), *(d_a1));
          unsigned int _next_fuel = f;
          _loop_l = std::move(_next_l);
          _loop_fuel = std::move(_next_fuel);
          continue;
        }
      }
    }
  }
  return std::move(*(_head));
}

__attribute__((pure)) unsigned int LoopifyLists::sum_list_lengths(
    const LoopifyLists::list<LoopifyLists::list<unsigned int>> &l) {
  struct _Enter {
    const LoopifyLists::list<LoopifyLists::list<unsigned int>> l;
  };

  struct _Call1 {
    decltype(len_list(clone_as_value<LoopifyLists::list<unsigned int>>(
        std::declval<std::shared_ptr<LoopifyLists::list<unsigned int>> &>())))
        _s0;
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
      const LoopifyLists::list<LoopifyLists::list<unsigned int>> l = _f.l;
      if (std::holds_alternative<typename LoopifyLists::list<
              LoopifyLists::list<unsigned int>>::Nil>(l.v())) {
        _result = 0u;
      } else {
        const auto &[d_a0, d_a1] = std::get<typename LoopifyLists::list<
            LoopifyLists::list<unsigned int>>::Cons>(l.v());
        _stack.emplace_back(_Call1{
            len_list(clone_as_value<LoopifyLists::list<unsigned int>>(d_a0))});
        _stack.emplace_back(_Enter{*(d_a1)});
      }
    } else {
      auto _f = std::move(std::get<_Call1>(_frame));
      _result = (_f._s0 + _result);
    }
  }
  return _result;
}

__attribute__((pure)) LoopifyLists::list<unsigned int>
LoopifyLists::flatten_nested(
    const LoopifyLists::list<LoopifyLists::list<unsigned int>> &l) {
  return flatten_nested_fuel((sum_list_lengths(l) + 1), l);
}

/// compress l removes consecutive duplicates: 1,1,2,2,2,3 -> 1,2,3.
__attribute__((pure)) LoopifyLists::list<unsigned int>
LoopifyLists::compress(const LoopifyLists::list<unsigned int> &l) {
  std::unique_ptr<LoopifyLists::list<unsigned int>> _head{};
  std::unique_ptr<LoopifyLists::list<unsigned int>> *_write = &_head;
  LoopifyLists::list<unsigned int> _loop_l = l;
  while (true) {
    if (std::holds_alternative<typename LoopifyLists::list<unsigned int>::Nil>(
            _loop_l.v())) {
      *(_write) = std::make_unique<LoopifyLists::list<unsigned int>>(
          list<unsigned int>::nil());
      break;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename LoopifyLists::list<unsigned int>::Cons>(
              _loop_l.v());
      auto &&_sv0 = *(d_a1);
      if (std::holds_alternative<
              typename LoopifyLists::list<unsigned int>::Nil>(_sv0.v())) {
        *(_write) = std::make_unique<LoopifyLists::list<unsigned int>>(
            list<unsigned int>::cons(d_a0, list<unsigned int>::nil()));
        break;
      } else {
        const auto &[d_a00, d_a10] =
            std::get<typename LoopifyLists::list<unsigned int>::Cons>(_sv0.v());
        if (d_a0 == d_a00) {
          _loop_l = *(d_a1);
          continue;
        } else {
          auto _cell = std::make_unique<LoopifyLists::list<unsigned int>>(
              typename list<unsigned int>::Cons(d_a0, nullptr));
          *(_write) = std::move(_cell);
          _write =
              &std::get<typename list<unsigned int>::Cons>((*_write)->v_mut())
                   .d_a1;
          _loop_l = *(d_a1);
          continue;
        }
      }
    }
  }
  return std::move(*(_head));
}

/// group_pairs l groups consecutive elements into pairs: 1,2,3,4 ->
/// (1,2),(3,4).
__attribute__((pure)) LoopifyLists::list<std::pair<unsigned int, unsigned int>>
LoopifyLists::group_pairs(const LoopifyLists::list<unsigned int> &l) {
  std::unique_ptr<LoopifyLists::list<std::pair<unsigned int, unsigned int>>>
      _head{};
  std::unique_ptr<LoopifyLists::list<std::pair<unsigned int, unsigned int>>>
      *_write = &_head;
  LoopifyLists::list<unsigned int> _loop_l = l;
  while (true) {
    if (std::holds_alternative<typename LoopifyLists::list<unsigned int>::Nil>(
            _loop_l.v())) {
      *(_write) = std::make_unique<
          LoopifyLists::list<std::pair<unsigned int, unsigned int>>>(
          list<std::pair<unsigned int, unsigned int>>::nil());
      break;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename LoopifyLists::list<unsigned int>::Cons>(
              _loop_l.v());
      auto &&_sv0 = *(d_a1);
      if (std::holds_alternative<
              typename LoopifyLists::list<unsigned int>::Nil>(_sv0.v())) {
        *(_write) = std::make_unique<
            LoopifyLists::list<std::pair<unsigned int, unsigned int>>>(
            list<std::pair<unsigned int, unsigned int>>::nil());
        break;
      } else {
        const auto &[d_a00, d_a10] =
            std::get<typename LoopifyLists::list<unsigned int>::Cons>(_sv0.v());
        auto _cell = std::make_unique<
            LoopifyLists::list<std::pair<unsigned int, unsigned int>>>(
            typename list<std::pair<unsigned int, unsigned int>>::Cons(
                std::make_pair(d_a0, d_a00), nullptr));
        *(_write) = std::move(_cell);
        _write =
            &std::get<
                 typename list<std::pair<unsigned int, unsigned int>>::Cons>(
                 (*_write)->v_mut())
                 .d_a1;
        _loop_l = *(d_a10);
        continue;
      }
    }
  }
  return std::move(*(_head));
}

/// swizzle l separates elements by position: 1,2,3,4 -> (1,3,2,4).
__attribute__((pure))
std::pair<LoopifyLists::list<unsigned int>, LoopifyLists::list<unsigned int>>
LoopifyLists::swizzle(const LoopifyLists::list<unsigned int> &l) {
  struct _Enter {
    const LoopifyLists::list<unsigned int> l;
  };

  struct _Call1 {
    unsigned int _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::pair<LoopifyLists::list<unsigned int>, LoopifyLists::list<unsigned int>>
      _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{l});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const LoopifyLists::list<unsigned int> l = _f.l;
      if (std::holds_alternative<
              typename LoopifyLists::list<unsigned int>::Nil>(l.v())) {
        _result = std::make_pair(list<unsigned int>::nil(),
                                 list<unsigned int>::nil());
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename LoopifyLists::list<unsigned int>::Cons>(l.v());
        _stack.emplace_back(_Call1{d_a0});
        _stack.emplace_back(_Enter{*(d_a1)});
      }
    } else {
      auto _f = std::move(std::get<_Call1>(_frame));
      unsigned int d_a0 = _f._s0;
      const LoopifyLists::list<unsigned int> &odds = _result.first;
      const LoopifyLists::list<unsigned int> &evens = _result.second;
      _result = std::make_pair(list<unsigned int>::cons(d_a0, evens), odds);
    }
  }
  return _result;
}

/// index_of_aux x l i finds first index of x in l starting from i.
__attribute__((pure)) unsigned int
LoopifyLists::index_of_aux(const unsigned int &x,
                           const LoopifyLists::list<unsigned int> &l,
                           unsigned int i) {
  unsigned int _result;
  unsigned int _loop_i = std::move(i);
  LoopifyLists::list<unsigned int> _loop_l = l;
  while (true) {
    if (std::holds_alternative<typename LoopifyLists::list<unsigned int>::Nil>(
            _loop_l.v())) {
      _result = 0u;
      break;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename LoopifyLists::list<unsigned int>::Cons>(
              _loop_l.v());
      if (x == d_a0) {
        _result = _loop_i;
        break;
      } else {
        unsigned int _next_i = (_loop_i + 1);
        LoopifyLists::list<unsigned int> _next_l = *(d_a1);
        _loop_i = std::move(_next_i);
        _loop_l = std::move(_next_l);
      }
    }
  }
  return _result;
}

__attribute__((pure)) unsigned int
LoopifyLists::index_of(const unsigned int &x,
                       const LoopifyLists::list<unsigned int> &l) {
  return index_of_aux(x, l, 0u);
}

/// interleave l1 l2 interleaves two lists: 1,2 3,4 -> 1,3,2,4.
__attribute__((pure)) LoopifyLists::list<unsigned int>
LoopifyLists::interleave(LoopifyLists::list<unsigned int> l1,
                         LoopifyLists::list<unsigned int> l2) {
  std::unique_ptr<LoopifyLists::list<unsigned int>> _head{};
  std::unique_ptr<LoopifyLists::list<unsigned int>> *_write = &_head;
  LoopifyLists::list<unsigned int> _loop_l2 = std::move(l2);
  LoopifyLists::list<unsigned int> _loop_l1 = std::move(l1);
  while (true) {
    if (std::holds_alternative<typename LoopifyLists::list<unsigned int>::Nil>(
            _loop_l1.v())) {
      *(_write) = std::make_unique<LoopifyLists::list<unsigned int>>(_loop_l2);
      break;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename LoopifyLists::list<unsigned int>::Cons>(
              _loop_l1.v());
      if (std::holds_alternative<
              typename LoopifyLists::list<unsigned int>::Nil>(_loop_l2.v())) {
        *(_write) =
            std::make_unique<LoopifyLists::list<unsigned int>>(_loop_l1);
        break;
      } else {
        const auto &[d_a00, d_a10] =
            std::get<typename LoopifyLists::list<unsigned int>::Cons>(
                _loop_l2.v());
        auto _cell = std::make_unique<LoopifyLists::list<unsigned int>>(
            typename list<unsigned int>::Cons(d_a0, nullptr));
        auto _cell1 = std::make_unique<LoopifyLists::list<unsigned int>>(
            typename list<unsigned int>::Cons(d_a00, nullptr));
        std::get<typename list<unsigned int>::Cons>(_cell->v_mut()).d_a1 =
            std::move(_cell1);
        *(_write) = std::move(_cell);
        _write =
            &std::get<typename list<unsigned int>::Cons>((*_write)->v_mut())
                 .d_a1;
        LoopifyLists::list<unsigned int> _next_l2 = *(d_a10);
        LoopifyLists::list<unsigned int> _next_l1 = *(d_a1);
        _loop_l2 = std::move(_next_l2);
        _loop_l1 = std::move(_next_l1);
        continue;
      }
    }
  }
  return std::move(*(_head));
}

/// lookup key l finds value for key in association list.
__attribute__((pure)) unsigned int LoopifyLists::lookup(
    const unsigned int &key,
    const LoopifyLists::list<std::pair<unsigned int, unsigned int>> &l) {
  unsigned int _result;
  LoopifyLists::list<std::pair<unsigned int, unsigned int>> _loop_l = l;
  while (true) {
    if (std::holds_alternative<typename LoopifyLists::list<
            std::pair<unsigned int, unsigned int>>::Nil>(_loop_l.v())) {
      _result = 0u;
      break;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename LoopifyLists::list<
          std::pair<unsigned int, unsigned int>>::Cons>(_loop_l.v());
      const unsigned int &k = d_a0.first;
      const unsigned int &v = d_a0.second;
      if (k == key) {
        _result = v;
        break;
      } else {
        _loop_l = *(d_a1);
      }
    }
  }
  return _result;
}

/// group l groups consecutive equal elements: 1,1,2,2,2,3 -> [1,1],[2,2,2],[3].
__attribute__((pure)) LoopifyLists::list<LoopifyLists::list<unsigned int>>
LoopifyLists::group_fuel(const unsigned int &fuel,
                         const LoopifyLists::list<unsigned int> &l) {
  std::unique_ptr<LoopifyLists::list<LoopifyLists::list<unsigned int>>> _head{};
  std::unique_ptr<LoopifyLists::list<LoopifyLists::list<unsigned int>>>
      *_write = &_head;
  LoopifyLists::list<unsigned int> _loop_l = l;
  unsigned int _loop_fuel = fuel;
  while (true) {
    if (_loop_fuel <= 0) {
      *(_write) = std::make_unique<
          LoopifyLists::list<LoopifyLists::list<unsigned int>>>(
          list<LoopifyLists::list<unsigned int>>::nil());
      break;
    } else {
      unsigned int f = _loop_fuel - 1;
      if (std::holds_alternative<
              typename LoopifyLists::list<unsigned int>::Nil>(_loop_l.v())) {
        *(_write) = std::make_unique<
            LoopifyLists::list<LoopifyLists::list<unsigned int>>>(
            list<LoopifyLists::list<unsigned int>>::nil());
        break;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename LoopifyLists::list<unsigned int>::Cons>(
                _loop_l.v());
        auto &&_sv0 = *(d_a1);
        if (std::holds_alternative<
                typename LoopifyLists::list<unsigned int>::Nil>(_sv0.v())) {
          *(_write) = std::make_unique<
              LoopifyLists::list<LoopifyLists::list<unsigned int>>>(
              list<LoopifyLists::list<unsigned int>>::cons(
                  list<unsigned int>::cons(d_a0, list<unsigned int>::nil()),
                  list<LoopifyLists::list<unsigned int>>::nil()));
          break;
        } else {
          const auto &[d_a00, d_a10] =
              std::get<typename LoopifyLists::list<unsigned int>::Cons>(
                  _sv0.v());
          if (d_a0 == d_a00) {
            auto &&_sv1 = group_fuel(f, *(d_a1));
            if (std::holds_alternative<typename LoopifyLists::list<
                    LoopifyLists::list<unsigned int>>::Nil>(_sv1.v())) {
              *(_write) = std::make_unique<
                  LoopifyLists::list<LoopifyLists::list<unsigned int>>>(
                  list<LoopifyLists::list<unsigned int>>::cons(
                      list<unsigned int>::cons(d_a0, list<unsigned int>::nil()),
                      list<LoopifyLists::list<unsigned int>>::nil()));
              break;
            } else {
              const auto &[d_a01, d_a11] = std::get<typename LoopifyLists::list<
                  LoopifyLists::list<unsigned int>>::Cons>(_sv1.v());
              *(_write) = std::make_unique<
                  LoopifyLists::list<LoopifyLists::list<unsigned int>>>(
                  list<LoopifyLists::list<unsigned int>>::cons(
                      list<unsigned int>::cons(
                          d_a0,
                          clone_as_value<LoopifyLists::list<unsigned int>>(
                              d_a01)),
                      *(d_a11)));
              break;
            }
          } else {
            auto _cell = std::make_unique<
                LoopifyLists::list<LoopifyLists::list<unsigned int>>>(
                typename list<LoopifyLists::list<unsigned int>>::Cons(
                    std::make_unique<
                        LoopifyLists::list<LoopifyLists::list<unsigned int>>>(
                        list<unsigned int>::cons(d_a0,
                                                 list<unsigned int>::nil())),
                    nullptr));
            *(_write) = std::move(_cell);
            _write =
                &std::get<
                     typename list<LoopifyLists::list<unsigned int>>::Cons>(
                     (*_write)->v_mut())
                     .d_a1;
            LoopifyLists::list<unsigned int> _next_l = *(d_a1);
            unsigned int _next_fuel = f;
            _loop_l = std::move(_next_l);
            _loop_fuel = std::move(_next_fuel);
            continue;
          }
        }
      }
    }
  }
  return std::move(*(_head));
}

__attribute__((pure)) LoopifyLists::list<LoopifyLists::list<unsigned int>>
LoopifyLists::group(const LoopifyLists::list<unsigned int> &l) {
  return group_fuel((len_list(l) + 1), l);
}

/// Internal helper: reverse a list.
__attribute__((pure)) LoopifyLists::list<unsigned int>
LoopifyLists::rev_helper(LoopifyLists::list<unsigned int> acc,
                         const LoopifyLists::list<unsigned int> &l) {
  LoopifyLists::list<unsigned int> _result;
  LoopifyLists::list<unsigned int> _loop_l = l;
  LoopifyLists::list<unsigned int> _loop_acc = std::move(acc);
  while (true) {
    if (std::holds_alternative<typename LoopifyLists::list<unsigned int>::Nil>(
            _loop_l.v())) {
      _result = _loop_acc;
      break;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename LoopifyLists::list<unsigned int>::Cons>(
              _loop_l.v());
      LoopifyLists::list<unsigned int> _next_l = *(d_a1);
      LoopifyLists::list<unsigned int> _next_acc =
          list<unsigned int>::cons(d_a0, _loop_acc);
      _loop_l = std::move(_next_l);
      _loop_acc = std::move(_next_acc);
    }
  }
  return _result;
}

/// reverse_insert x l inserts x and reverses at each step.
__attribute__((pure)) LoopifyLists::list<unsigned int>
LoopifyLists::reverse_insert(unsigned int x,
                             const LoopifyLists::list<unsigned int> &l) {
  struct _Enter {
    const LoopifyLists::list<unsigned int> l;
  };

  struct _Call1 {
    decltype(list<unsigned int>::nil()) _s0;
    unsigned int _s1;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  LoopifyLists::list<unsigned int> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{l});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const LoopifyLists::list<unsigned int> l = _f.l;
      if (std::holds_alternative<
              typename LoopifyLists::list<unsigned int>::Nil>(l.v())) {
        _result = list<unsigned int>::cons(x, list<unsigned int>::nil());
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename LoopifyLists::list<unsigned int>::Cons>(l.v());
        _stack.emplace_back(_Call1{list<unsigned int>::nil(), d_a0});
        _stack.emplace_back(_Enter{*(d_a1)});
      }
    } else {
      auto _f = std::move(std::get<_Call1>(_frame));
      _result = rev_helper(_f._s0, list<unsigned int>::cons(_f._s1, _result));
    }
  }
  return _result;
}

/// Internal helper: append lists.
__attribute__((pure)) LoopifyLists::list<unsigned int>
LoopifyLists::app_helper(const LoopifyLists::list<unsigned int> &l1,
                         LoopifyLists::list<unsigned int> l2) {
  std::unique_ptr<LoopifyLists::list<unsigned int>> _head{};
  std::unique_ptr<LoopifyLists::list<unsigned int>> *_write = &_head;
  LoopifyLists::list<unsigned int> _loop_l1 = l1;
  while (true) {
    if (std::holds_alternative<typename LoopifyLists::list<unsigned int>::Nil>(
            _loop_l1.v())) {
      *(_write) = std::make_unique<LoopifyLists::list<unsigned int>>(l2);
      break;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename LoopifyLists::list<unsigned int>::Cons>(
              _loop_l1.v());
      auto _cell = std::make_unique<LoopifyLists::list<unsigned int>>(
          typename list<unsigned int>::Cons(d_a0, nullptr));
      *(_write) = std::move(_cell);
      _write =
          &std::get<typename list<unsigned int>::Cons>((*_write)->v_mut()).d_a1;
      _loop_l1 = *(d_a1);
      continue;
    }
  }
  return std::move(*(_head));
}

/// double_append l1 l2 appends with doubling: 1,2 3 -> 1,3,3,3,3.
__attribute__((pure)) LoopifyLists::list<unsigned int>
LoopifyLists::double_append(const LoopifyLists::list<unsigned int> &l1,
                            LoopifyLists::list<unsigned int> l2) {
  struct _Enter {
    const LoopifyLists::list<unsigned int> l1;
  };

  struct _Call1 {
    unsigned int _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  LoopifyLists::list<unsigned int> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{l1});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const LoopifyLists::list<unsigned int> l1 = _f.l1;
      if (std::holds_alternative<
              typename LoopifyLists::list<unsigned int>::Nil>(l1.v())) {
        _result = l2;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename LoopifyLists::list<unsigned int>::Cons>(l1.v());
        _stack.emplace_back(_Call1{d_a0});
        _stack.emplace_back(_Enter{*(d_a1)});
      }
    } else {
      auto _f = std::move(std::get<_Call1>(_frame));
      unsigned int d_a0 = _f._s0;
      LoopifyLists::list<unsigned int> rest = _result;
      _result = list<unsigned int>::cons(d_a0, app_helper(rest, rest));
    }
  }
  return _result;
}

/// remove_if_sum_even l removes element if sum with next is even.
__attribute__((pure)) LoopifyLists::list<unsigned int>
LoopifyLists::remove_if_sum_even(const LoopifyLists::list<unsigned int> &l) {
  std::unique_ptr<LoopifyLists::list<unsigned int>> _head{};
  std::unique_ptr<LoopifyLists::list<unsigned int>> *_write = &_head;
  LoopifyLists::list<unsigned int> _loop_l = l;
  while (true) {
    if (std::holds_alternative<typename LoopifyLists::list<unsigned int>::Nil>(
            _loop_l.v())) {
      *(_write) = std::make_unique<LoopifyLists::list<unsigned int>>(
          list<unsigned int>::nil());
      break;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename LoopifyLists::list<unsigned int>::Cons>(
              _loop_l.v());
      auto &&_sv0 = *(d_a1);
      if (std::holds_alternative<
              typename LoopifyLists::list<unsigned int>::Nil>(_sv0.v())) {
        *(_write) = std::make_unique<LoopifyLists::list<unsigned int>>(
            list<unsigned int>::cons(d_a0, list<unsigned int>::nil()));
        break;
      } else {
        const auto &[d_a00, d_a10] =
            std::get<typename LoopifyLists::list<unsigned int>::Cons>(_sv0.v());
        if ((2u ? (d_a0 + d_a00) % 2u : (d_a0 + d_a00)) == 0u) {
          _loop_l = *(d_a1);
          continue;
        } else {
          auto _cell = std::make_unique<LoopifyLists::list<unsigned int>>(
              typename list<unsigned int>::Cons(d_a0, nullptr));
          *(_write) = std::move(_cell);
          _write =
              &std::get<typename list<unsigned int>::Cons>((*_write)->v_mut())
                   .d_a1;
          _loop_l = *(d_a1);
          continue;
        }
      }
    }
  }
  return std::move(*(_head));
}

/// split_at n l splits list at index n into (prefix, suffix).
__attribute__((pure))
std::pair<LoopifyLists::list<unsigned int>, LoopifyLists::list<unsigned int>>
LoopifyLists::split_at(const unsigned int &n,
                       LoopifyLists::list<unsigned int> l) {
  struct _Enter {
    LoopifyLists::list<unsigned int> l;
    const unsigned int n;
  };

  struct _Call1 {
    unsigned int _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::pair<LoopifyLists::list<unsigned int>, LoopifyLists::list<unsigned int>>
      _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{l, n});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      LoopifyLists::list<unsigned int> l = _f.l;
      const unsigned int n = _f.n;
      if (std::holds_alternative<
              typename LoopifyLists::list<unsigned int>::Nil>(l.v())) {
        _result = std::make_pair(list<unsigned int>::nil(),
                                 list<unsigned int>::nil());
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename LoopifyLists::list<unsigned int>::Cons>(l.v());
        if (n == 0u) {
          _result = std::make_pair(list<unsigned int>::nil(), l);
        } else {
          _stack.emplace_back(_Call1{d_a0});
          _stack.emplace_back(_Enter{*(d_a1), (((n - 1u) > n ? 0 : (n - 1u)))});
        }
      }
    } else {
      auto _f = std::move(std::get<_Call1>(_frame));
      unsigned int d_a0 = _f._s0;
      const LoopifyLists::list<unsigned int> &a = _result.first;
      const LoopifyLists::list<unsigned int> &b = _result.second;
      _result = std::make_pair(list<unsigned int>::cons(d_a0, a), b);
    }
  }
  return _result;
}

/// unzip l splits list of pairs into two lists.
__attribute__((pure))
std::pair<LoopifyLists::list<unsigned int>, LoopifyLists::list<unsigned int>>
LoopifyLists::unzip(
    const LoopifyLists::list<std::pair<unsigned int, unsigned int>> &l) {
  struct _Enter {
    const LoopifyLists::list<std::pair<unsigned int, unsigned int>> l;
  };

  struct _Call1 {
    unsigned int _s0;
    unsigned int _s1;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::pair<LoopifyLists::list<unsigned int>, LoopifyLists::list<unsigned int>>
      _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{l});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const LoopifyLists::list<std::pair<unsigned int, unsigned int>> l = _f.l;
      if (std::holds_alternative<typename LoopifyLists::list<
              std::pair<unsigned int, unsigned int>>::Nil>(l.v())) {
        _result = std::make_pair(list<unsigned int>::nil(),
                                 list<unsigned int>::nil());
      } else {
        const auto &[d_a0, d_a1] = std::get<typename LoopifyLists::list<
            std::pair<unsigned int, unsigned int>>::Cons>(l.v());
        const unsigned int &a = d_a0.first;
        const unsigned int &b = d_a0.second;
        _stack.emplace_back(_Call1{a, b});
        _stack.emplace_back(_Enter{*(d_a1)});
      }
    } else {
      auto _f = std::move(std::get<_Call1>(_frame));
      unsigned int a = _f._s0;
      unsigned int b = _f._s1;
      const LoopifyLists::list<unsigned int> &xs = _result.first;
      const LoopifyLists::list<unsigned int> &ys = _result.second;
      _result = std::make_pair(list<unsigned int>::cons(a, xs),
                               list<unsigned int>::cons(b, ys));
    }
  }
  return _result;
}

/// nth n l default returns nth element or default if out of bounds.
__attribute__((pure)) unsigned int
LoopifyLists::nth(const unsigned int &n,
                  const LoopifyLists::list<unsigned int> &l,
                  unsigned int default0) {
  unsigned int _result;
  LoopifyLists::list<unsigned int> _loop_l = l;
  unsigned int _loop_n = n;
  while (true) {
    if (std::holds_alternative<typename LoopifyLists::list<unsigned int>::Nil>(
            _loop_l.v())) {
      _result = default0;
      break;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename LoopifyLists::list<unsigned int>::Cons>(
              _loop_l.v());
      if (_loop_n == 0u) {
        _result = d_a0;
        break;
      } else {
        LoopifyLists::list<unsigned int> _next_l = *(d_a1);
        unsigned int _next_n =
            (((_loop_n - 1u) > _loop_n ? 0 : (_loop_n - 1u)));
        _loop_l = std::move(_next_l);
        _loop_n = std::move(_next_n);
      }
    }
  }
  return _result;
}

/// last l default returns last element or default if empty.
__attribute__((pure)) unsigned int
LoopifyLists::last(const LoopifyLists::list<unsigned int> &l,
                   unsigned int default0) {
  unsigned int _result;
  LoopifyLists::list<unsigned int> _loop_l = l;
  while (true) {
    if (std::holds_alternative<typename LoopifyLists::list<unsigned int>::Nil>(
            _loop_l.v())) {
      _result = default0;
      break;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename LoopifyLists::list<unsigned int>::Cons>(
              _loop_l.v());
      auto &&_sv = *(d_a1);
      if (std::holds_alternative<
              typename LoopifyLists::list<unsigned int>::Nil>(_sv.v())) {
        _result = d_a0;
        break;
      } else {
        _loop_l = *(d_a1);
      }
    }
  }
  return _result;
}

/// drop n l drops first n elements.
__attribute__((pure)) LoopifyLists::list<unsigned int>
LoopifyLists::drop(const unsigned int &n, LoopifyLists::list<unsigned int> l) {
  LoopifyLists::list<unsigned int> _result;
  LoopifyLists::list<unsigned int> _loop_l = std::move(l);
  unsigned int _loop_n = n;
  while (true) {
    if (std::holds_alternative<typename LoopifyLists::list<unsigned int>::Nil>(
            _loop_l.v())) {
      _result = list<unsigned int>::nil();
      break;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename LoopifyLists::list<unsigned int>::Cons>(
              _loop_l.v());
      if (_loop_n == 0u) {
        _result = _loop_l;
        break;
      } else {
        LoopifyLists::list<unsigned int> _next_l = *(d_a1);
        unsigned int _next_n =
            (((_loop_n - 1u) > _loop_n ? 0 : (_loop_n - 1u)));
        _loop_l = std::move(_next_l);
        _loop_n = std::move(_next_n);
      }
    }
  }
  return _result;
}

/// init l returns all but last element.
__attribute__((pure)) LoopifyLists::list<unsigned int>
LoopifyLists::init(const LoopifyLists::list<unsigned int> &l) {
  std::unique_ptr<LoopifyLists::list<unsigned int>> _head{};
  std::unique_ptr<LoopifyLists::list<unsigned int>> *_write = &_head;
  LoopifyLists::list<unsigned int> _loop_l = l;
  while (true) {
    if (std::holds_alternative<typename LoopifyLists::list<unsigned int>::Nil>(
            _loop_l.v())) {
      *(_write) = std::make_unique<LoopifyLists::list<unsigned int>>(
          list<unsigned int>::nil());
      break;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename LoopifyLists::list<unsigned int>::Cons>(
              _loop_l.v());
      auto &&_sv = *(d_a1);
      if (std::holds_alternative<
              typename LoopifyLists::list<unsigned int>::Nil>(_sv.v())) {
        *(_write) = std::make_unique<LoopifyLists::list<unsigned int>>(
            list<unsigned int>::nil());
        break;
      } else {
        auto _cell = std::make_unique<LoopifyLists::list<unsigned int>>(
            typename list<unsigned int>::Cons(d_a0, nullptr));
        *(_write) = std::move(_cell);
        _write =
            &std::get<typename list<unsigned int>::Cons>((*_write)->v_mut())
                 .d_a1;
        _loop_l = *(d_a1);
        continue;
      }
    }
  }
  return std::move(*(_head));
}

/// count x l counts occurrences of x in l.
__attribute__((pure)) unsigned int
LoopifyLists::count(const unsigned int &x,
                    const LoopifyLists::list<unsigned int> &l) {
  struct _Enter {
    const LoopifyLists::list<unsigned int> l;
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
      const LoopifyLists::list<unsigned int> l = _f.l;
      if (std::holds_alternative<
              typename LoopifyLists::list<unsigned int>::Nil>(l.v())) {
        _result = 0u;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename LoopifyLists::list<unsigned int>::Cons>(l.v());
        if (x == d_a0) {
          _stack.emplace_back(_Call1{});
          _stack.emplace_back(_Enter{*(d_a1)});
        } else {
          _stack.emplace_back(_Enter{*(d_a1)});
        }
      }
    } else {
      auto _f = std::move(std::get<_Call1>(_frame));
      _result = (_result + 1);
    }
  }
  return _result;
}

/// maximum l finds maximum element (returns 0 for empty list).
__attribute__((pure)) unsigned int
LoopifyLists::maximum(const LoopifyLists::list<unsigned int> &l) {
  struct _Enter {
    const LoopifyLists::list<unsigned int> l;
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
      const LoopifyLists::list<unsigned int> l = _f.l;
      if (std::holds_alternative<
              typename LoopifyLists::list<unsigned int>::Nil>(l.v())) {
        _result = 0u;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename LoopifyLists::list<unsigned int>::Cons>(l.v());
        auto &&_sv = *(d_a1);
        if (std::holds_alternative<
                typename LoopifyLists::list<unsigned int>::Nil>(_sv.v())) {
          _result = d_a0;
        } else {
          _stack.emplace_back(_Call1{d_a0});
          _stack.emplace_back(_Enter{*(d_a1)});
        }
      }
    } else {
      auto _f = std::move(std::get<_Call1>(_frame));
      unsigned int d_a0 = _f._s0;
      unsigned int max_rest = _result;
      if (max_rest <= d_a0) {
        _result = d_a0;
      } else {
        _result = max_rest;
      }
    }
  }
  return _result;
}

/// minmax l finds both minimum and maximum in one pass.
__attribute__((pure)) std::pair<unsigned int, unsigned int>
LoopifyLists::minmax(const LoopifyLists::list<unsigned int> &l) {
  struct _Enter {
    const LoopifyLists::list<unsigned int> l;
  };

  struct _Call1 {
    unsigned int _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::pair<unsigned int, unsigned int> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{l});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const LoopifyLists::list<unsigned int> l = _f.l;
      if (std::holds_alternative<
              typename LoopifyLists::list<unsigned int>::Nil>(l.v())) {
        _result = std::make_pair(0u, 0u);
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename LoopifyLists::list<unsigned int>::Cons>(l.v());
        LoopifyLists::list<unsigned int> d_a1_value =
            clone_as_value<LoopifyLists::list<unsigned int>>(d_a1);
        if (std::holds_alternative<
                typename LoopifyLists::list<unsigned int>::Nil>(
                d_a1_value.v())) {
          _result = std::make_pair(d_a0, d_a0);
        } else {
          _stack.emplace_back(_Call1{d_a0});
          _stack.emplace_back(_Enter{d_a1_value});
        }
      }
    } else {
      auto _f = std::move(std::get<_Call1>(_frame));
      unsigned int d_a0 = _f._s0;
      const unsigned int &lo = _result.first;
      const unsigned int &hi = _result.second;
      _result = std::make_pair(
          [&]() -> unsigned int {
            if (d_a0 <= lo) {
              return d_a0;
            } else {
              return lo;
            }
          }(),
          [&]() -> unsigned int {
            if (hi <= d_a0) {
              return d_a0;
            } else {
              return hi;
            }
          }());
    }
  }
  return _result;
}

/// Helper for rotate_left.
__attribute__((pure)) LoopifyLists::list<unsigned int>
LoopifyLists::rotate_left_fuel(const unsigned int &fuel, const unsigned int &n,
                               LoopifyLists::list<unsigned int> l) {
  LoopifyLists::list<unsigned int> _result;
  LoopifyLists::list<unsigned int> _loop_l = std::move(l);
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
        if (std::holds_alternative<
                typename LoopifyLists::list<unsigned int>::Nil>(_loop_l.v())) {
          _result = list<unsigned int>::nil();
          break;
        } else {
          const auto &[d_a0, d_a1] =
              std::get<typename LoopifyLists::list<unsigned int>::Cons>(
                  _loop_l.v());
          LoopifyLists::list<unsigned int> _next_l = app_helper(
              *(d_a1),
              list<unsigned int>::cons(d_a0, list<unsigned int>::nil()));
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

/// rotate_left n l rotates list left by n positions: rotate 2 1,2,3,4 ->
/// 3,4,1,2.
__attribute__((pure)) LoopifyLists::list<unsigned int>
LoopifyLists::rotate_left(unsigned int n,
                          const LoopifyLists::list<unsigned int> &l) {
  return rotate_left_fuel((n + 1), n, l);
}

/// intercalate sep lists joins lists with separator: intercalate 0 [1,2],[3,4]
/// -> 1,2,0,3,4.
__attribute__((pure)) LoopifyLists::list<unsigned int>
LoopifyLists::intercalate(
    const LoopifyLists::list<unsigned int> &sep,
    const LoopifyLists::list<LoopifyLists::list<unsigned int>> &lists) {
  struct _Enter {
    const LoopifyLists::list<LoopifyLists::list<unsigned int>> lists;
  };

  struct _Call1 {
    decltype(clone_as_value<LoopifyLists::list<unsigned int>>(
        std::declval<std::shared_ptr<LoopifyLists::list<unsigned int>> &>()))
        _s0;
    const LoopifyLists::list<unsigned int> _s1;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  LoopifyLists::list<unsigned int> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{lists});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const LoopifyLists::list<LoopifyLists::list<unsigned int>> lists =
          _f.lists;
      if (std::holds_alternative<typename LoopifyLists::list<
              LoopifyLists::list<unsigned int>>::Nil>(lists.v())) {
        _result = list<unsigned int>::nil();
      } else {
        const auto &[d_a0, d_a1] = std::get<typename LoopifyLists::list<
            LoopifyLists::list<unsigned int>>::Cons>(lists.v());
        auto &&_sv = *(d_a1);
        if (std::holds_alternative<typename LoopifyLists::list<
                LoopifyLists::list<unsigned int>>::Nil>(_sv.v())) {
          _result = clone_as_value<LoopifyLists::list<unsigned int>>(d_a0);
        } else {
          _stack.emplace_back(_Call1{
              clone_as_value<LoopifyLists::list<unsigned int>>(d_a0), sep});
          _stack.emplace_back(_Enter{*(d_a1)});
        }
      }
    } else {
      auto _f = std::move(std::get<_Call1>(_frame));
      _result = app_helper(_f._s0, app_helper(_f._s1, _result));
    }
  }
  return _result;
}

/// majority l finds majority element using Boyer-Moore voting algorithm.
/// Returns (candidate, count).
__attribute__((pure)) std::pair<unsigned int, unsigned int>
LoopifyLists::majority(const LoopifyLists::list<unsigned int> &l) {
  struct _Enter {
    const LoopifyLists::list<unsigned int> l;
  };

  struct _Call1 {
    unsigned int _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::pair<unsigned int, unsigned int> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{l});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const LoopifyLists::list<unsigned int> l = _f.l;
      if (std::holds_alternative<
              typename LoopifyLists::list<unsigned int>::Nil>(l.v())) {
        _result = std::make_pair(0u, 0u);
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename LoopifyLists::list<unsigned int>::Cons>(l.v());
        auto &&_sv = *(d_a1);
        if (std::holds_alternative<
                typename LoopifyLists::list<unsigned int>::Nil>(_sv.v())) {
          _result = std::make_pair(d_a0, 1u);
        } else {
          _stack.emplace_back(_Call1{d_a0});
          _stack.emplace_back(_Enter{*(d_a1)});
        }
      }
    } else {
      auto _f = std::move(std::get<_Call1>(_frame));
      unsigned int d_a0 = _f._s0;
      const unsigned int &cand = _result.first;
      const unsigned int &cnt = _result.second;
      if (d_a0 == cand) {
        _result = std::make_pair(cand, (cnt + 1));
      } else {
        if (cnt == 0u) {
          _result = std::make_pair(d_a0, 1u);
        } else {
          _result = std::make_pair(cand, (((cnt - 1u) > cnt ? 0 : (cnt - 1u))));
        }
      }
    }
  }
  return _result;
}

/// zip3 l1 l2 l3 zips three lists into triples.
__attribute__((pure)) LoopifyLists::list<
    std::pair<std::pair<unsigned int, unsigned int>, unsigned int>>
LoopifyLists::zip3(const LoopifyLists::list<unsigned int> &l1,
                   const LoopifyLists::list<unsigned int> &l2,
                   const LoopifyLists::list<unsigned int> &l3) {
  std::unique_ptr<LoopifyLists::list<
      std::pair<std::pair<unsigned int, unsigned int>, unsigned int>>>
      _head{};
  std::unique_ptr<LoopifyLists::list<
      std::pair<std::pair<unsigned int, unsigned int>, unsigned int>>> *_write =
      &_head;
  LoopifyLists::list<unsigned int> _loop_l3 = l3;
  LoopifyLists::list<unsigned int> _loop_l2 = l2;
  LoopifyLists::list<unsigned int> _loop_l1 = l1;
  while (true) {
    if (std::holds_alternative<typename LoopifyLists::list<unsigned int>::Nil>(
            _loop_l1.v())) {
      *(_write) = std::make_unique<LoopifyLists::list<
          std::pair<std::pair<unsigned int, unsigned int>, unsigned int>>>(
          list<std::pair<std::pair<unsigned int, unsigned int>,
                         unsigned int>>::nil());
      break;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename LoopifyLists::list<unsigned int>::Cons>(
              _loop_l1.v());
      if (std::holds_alternative<
              typename LoopifyLists::list<unsigned int>::Nil>(_loop_l2.v())) {
        *(_write) = std::make_unique<LoopifyLists::list<
            std::pair<std::pair<unsigned int, unsigned int>, unsigned int>>>(
            list<std::pair<std::pair<unsigned int, unsigned int>,
                           unsigned int>>::nil());
        break;
      } else {
        const auto &[d_a00, d_a10] =
            std::get<typename LoopifyLists::list<unsigned int>::Cons>(
                _loop_l2.v());
        if (std::holds_alternative<
                typename LoopifyLists::list<unsigned int>::Nil>(_loop_l3.v())) {
          *(_write) = std::make_unique<LoopifyLists::list<
              std::pair<std::pair<unsigned int, unsigned int>, unsigned int>>>(
              list<std::pair<std::pair<unsigned int, unsigned int>,
                             unsigned int>>::nil());
          break;
        } else {
          const auto &[d_a01, d_a11] =
              std::get<typename LoopifyLists::list<unsigned int>::Cons>(
                  _loop_l3.v());
          auto _cell = std::make_unique<LoopifyLists::list<
              std::pair<std::pair<unsigned int, unsigned int>, unsigned int>>>(
              typename list<std::pair<std::pair<unsigned int, unsigned int>,
                                      unsigned int>>::
                  Cons(std::make_pair(std::make_pair(d_a0, d_a00), d_a01),
                       nullptr));
          *(_write) = std::move(_cell);
          _write = &std::get<typename list<std::pair<
              std::pair<unsigned int, unsigned int>, unsigned int>>::Cons>(
                        (*_write)->v_mut())
                        .d_a1;
          LoopifyLists::list<unsigned int> _next_l3 = *(d_a11);
          LoopifyLists::list<unsigned int> _next_l2 = *(d_a10);
          LoopifyLists::list<unsigned int> _next_l1 = *(d_a1);
          _loop_l3 = std::move(_next_l3);
          _loop_l2 = std::move(_next_l2);
          _loop_l1 = std::move(_next_l1);
          continue;
        }
      }
    }
  }
  return std::move(*(_head));
}

/// sum_and_count l returns both sum and count in one pass.
__attribute__((pure)) std::pair<unsigned int, unsigned int>
LoopifyLists::sum_and_count(const LoopifyLists::list<unsigned int> &l) {
  struct _Enter {
    const LoopifyLists::list<unsigned int> l;
  };

  struct _Call1 {
    unsigned int _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::pair<unsigned int, unsigned int> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{l});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const LoopifyLists::list<unsigned int> l = _f.l;
      if (std::holds_alternative<
              typename LoopifyLists::list<unsigned int>::Nil>(l.v())) {
        _result = std::make_pair(0u, 0u);
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename LoopifyLists::list<unsigned int>::Cons>(l.v());
        _stack.emplace_back(_Call1{d_a0});
        _stack.emplace_back(_Enter{*(d_a1)});
      }
    } else {
      auto _f = std::move(std::get<_Call1>(_frame));
      unsigned int d_a0 = _f._s0;
      const unsigned int &s = _result.first;
      const unsigned int &c = _result.second;
      _result = std::make_pair((d_a0 + s), (c + 1));
    }
  }
  return _result;
}

/// elem_at n l returns element at index n (like nth but with different name).
__attribute__((pure)) std::optional<unsigned int>
LoopifyLists::elem_at(const unsigned int &n,
                      const LoopifyLists::list<unsigned int> &l) {
  std::optional<unsigned int> _result;
  LoopifyLists::list<unsigned int> _loop_l = l;
  unsigned int _loop_n = n;
  while (true) {
    if (std::holds_alternative<typename LoopifyLists::list<unsigned int>::Nil>(
            _loop_l.v())) {
      _result = std::optional<unsigned int>();
      break;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename LoopifyLists::list<unsigned int>::Cons>(
              _loop_l.v());
      if (_loop_n == 0u) {
        _result = std::make_optional<unsigned int>(d_a0);
        break;
      } else {
        LoopifyLists::list<unsigned int> _next_l = *(d_a1);
        unsigned int _next_n =
            (((_loop_n - 1u) > _loop_n ? 0 : (_loop_n - 1u)));
        _loop_l = std::move(_next_l);
        _loop_n = std::move(_next_n);
      }
    }
  }
  return _result;
}
