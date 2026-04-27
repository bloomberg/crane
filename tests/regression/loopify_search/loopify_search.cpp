#include <loopify_search.h>

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

/// Consolidated search and optimization algorithms.
/// knapsack capacity items solves 0/1 knapsack problem.
/// Items are (weight, value) pairs.
__attribute__((pure)) unsigned int LoopifySearch::knapsack_fuel(
    const unsigned int &fuel, const unsigned int &capacity,
    const List<std::pair<unsigned int, unsigned int>> &items) {
  if (fuel <= 0) {
    return 0u;
  } else {
    unsigned int f = fuel - 1;
    if (std::holds_alternative<
            typename List<std::pair<unsigned int, unsigned int>>::Nil>(
            items.v())) {
      return 0u;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<std::pair<unsigned int, unsigned int>>::Cons>(
              items.v());
      const unsigned int &weight = d_a0.first;
      const unsigned int &value = d_a0.second;
      if (capacity < weight) {
        return knapsack_fuel(f, capacity, *(d_a1));
      } else {
        if (knapsack_fuel(f, capacity, *(d_a1)) <=
            (value +
             knapsack_fuel(
                 f,
                 (((capacity - weight) > capacity ? 0 : (capacity - weight))),
                 *(d_a1)))) {
          return (value + knapsack_fuel(f,
                                        (((capacity - weight) > capacity
                                              ? 0
                                              : (capacity - weight))),
                                        *(d_a1)));
        } else {
          return knapsack_fuel(f, capacity, *(d_a1));
        }
      }
    }
  }
}

__attribute__((pure)) unsigned int LoopifySearch::knapsack(
    const unsigned int &capacity,
    const List<std::pair<unsigned int, unsigned int>> &items) {
  return knapsack_fuel(len_impl<std::pair<unsigned int, unsigned int>>(items),
                       capacity, items);
}

/// majority l finds majority element using Boyer-Moore algorithm.
/// Returns (candidate, count).
__attribute__((pure)) std::pair<unsigned int, unsigned int>
LoopifySearch::majority(const List<unsigned int> &l) {
  struct _Enter {
    const List<unsigned int> l;
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
      const List<unsigned int> l = _f.l;
      if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
        _result = std::make_pair(0u, 0u);
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<unsigned int>::Cons>(l.v());
        _stack.emplace_back(_Call1{d_a0});
        _stack.emplace_back(_Enter{*(d_a1)});
      }
    } else {
      auto _f = std::move(std::get<_Call1>(_frame));
      unsigned int d_a0 = _f._s0;
      const unsigned int &cand = _result.first;
      const unsigned int &count = _result.second;
      if (d_a0 == cand) {
        _result = std::make_pair(cand, (count + 1));
      } else {
        if (0u < count) {
          _result =
              std::make_pair(cand, (((count - 1u) > count ? 0 : (count - 1u))));
        } else {
          _result = std::make_pair(d_a0, 1u);
        }
      }
    }
  }
  return _result;
}

/// longest_increasing_subseq l finds a longest increasing subsequence (greedy).
__attribute__((pure)) List<unsigned int>
LoopifySearch::longest_increasing_subseq(const List<unsigned int> &l) {
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
        *(_write) = std::make_unique<List<unsigned int>>(
            List<unsigned int>::cons(d_a0, List<unsigned int>::nil()));
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

/// Helper for binary search: get nth element.
__attribute__((pure)) unsigned int
LoopifySearch::nth_impl(const unsigned int &n, const List<unsigned int> &l) {
  unsigned int _result;
  List<unsigned int> _loop_l = l;
  unsigned int _loop_n = n;
  while (true) {
    if (_loop_n <= 0) {
      if (std::holds_alternative<typename List<unsigned int>::Nil>(
              _loop_l.v())) {
        _result = 0u;
        break;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<unsigned int>::Cons>(_loop_l.v());
        _result = d_a0;
        break;
      }
    } else {
      unsigned int m = _loop_n - 1;
      if (std::holds_alternative<typename List<unsigned int>::Nil>(
              _loop_l.v())) {
        _result = 0u;
        break;
      } else {
        const auto &[d_a00, d_a10] =
            std::get<typename List<unsigned int>::Cons>(_loop_l.v());
        List<unsigned int> _next_l = *(d_a10);
        unsigned int _next_n = m;
        _loop_l = std::move(_next_l);
        _loop_n = std::move(_next_n);
      }
    }
  }
  return _result;
}

/// Helper for binary search: take first k elements.
__attribute__((pure)) List<unsigned int>
LoopifySearch::take_impl(const unsigned int &k, const List<unsigned int> &l) {
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

/// Helper for binary search: drop first k elements.
__attribute__((pure)) List<unsigned int>
LoopifySearch::drop_impl(const unsigned int &k, List<unsigned int> l) {
  List<unsigned int> _result;
  List<unsigned int> _loop_l = std::move(l);
  unsigned int _loop_k = k;
  while (true) {
    if (_loop_k <= 0) {
      _result = _loop_l;
      break;
    } else {
      unsigned int m = _loop_k - 1;
      if (std::holds_alternative<typename List<unsigned int>::Nil>(
              _loop_l.v())) {
        _result = List<unsigned int>::nil();
        break;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<unsigned int>::Cons>(_loop_l.v());
        List<unsigned int> _next_l = *(d_a1);
        unsigned int _next_k = m;
        _loop_l = std::move(_next_l);
        _loop_k = std::move(_next_k);
      }
    }
  }
  return _result;
}

/// binary_search_fuel target sorted_list searches for target in sorted list.
/// Returns true if found.
__attribute__((pure)) bool
LoopifySearch::binary_search_fuel(const unsigned int &fuel,
                                  const unsigned int &target,
                                  const List<unsigned int> &l) {
  bool _result;
  List<unsigned int> _loop_l = l;
  unsigned int _loop_fuel = fuel;
  while (true) {
    if (_loop_fuel <= 0) {
      _result = false;
      break;
    } else {
      unsigned int f = _loop_fuel - 1;
      unsigned int n = len_impl<unsigned int>(_loop_l);
      if (n <= 0) {
        _result = false;
        break;
      } else {
        unsigned int _x = n - 1;
        unsigned int mid = (2u ? n / 2u : 0);
        unsigned int mid_val = nth_impl(mid, _loop_l);
        if (target == mid_val) {
          _result = true;
          break;
        } else {
          if (target < mid_val) {
            List<unsigned int> _next_l = take_impl(mid, _loop_l);
            unsigned int _next_fuel = f;
            _loop_l = std::move(_next_l);
            _loop_fuel = std::move(_next_fuel);
          } else {
            List<unsigned int> _next_l = drop_impl((mid + 1), _loop_l);
            unsigned int _next_fuel = f;
            _loop_l = std::move(_next_l);
            _loop_fuel = std::move(_next_fuel);
          }
        }
      }
    }
  }
  return _result;
}

__attribute__((pure)) bool
LoopifySearch::binary_search(const unsigned int &target,
                             const List<unsigned int> &l) {
  return binary_search_fuel(len_impl<unsigned int>(l), target, l);
}

/// longest_run l finds the longest run of consecutive equal elements.
__attribute__((pure)) List<unsigned int>
LoopifySearch::longest_run_aux(List<unsigned int> current_run,
                               List<unsigned int> best_run,
                               const List<unsigned int> &l) {
  List<unsigned int> _result;
  List<unsigned int> _loop_l = l;
  List<unsigned int> _loop_best_run = std::move(best_run);
  List<unsigned int> _loop_current_run = std::move(current_run);
  while (true) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(_loop_l.v())) {
      if (len_impl<unsigned int>(_loop_current_run) <=
          len_impl<unsigned int>(_loop_best_run)) {
        _result = _loop_best_run;
        break;
      } else {
        _result = _loop_current_run;
        break;
      }
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<unsigned int>::Cons>(_loop_l.v());
      auto &&_sv0 = *(d_a1);
      if (std::holds_alternative<typename List<unsigned int>::Nil>(_sv0.v())) {
        List<unsigned int> new_run =
            List<unsigned int>::cons(d_a0, _loop_current_run);
        if (len_impl<unsigned int>(new_run) <=
            len_impl<unsigned int>(_loop_best_run)) {
          _result = _loop_best_run;
          break;
        } else {
          _result = new_run;
          break;
        }
      } else {
        const auto &[d_a00, d_a10] =
            std::get<typename List<unsigned int>::Cons>(_sv0.v());
        if (d_a0 == d_a00) {
          List<unsigned int> _next_l = *(d_a1);
          List<unsigned int> _next_current_run =
              List<unsigned int>::cons(d_a0, _loop_current_run);
          _loop_l = std::move(_next_l);
          _loop_current_run = std::move(_next_current_run);
        } else {
          List<unsigned int> new_run =
              List<unsigned int>::cons(d_a0, _loop_current_run);
          List<unsigned int> new_best;
          if (len_impl<unsigned int>(new_run) <=
              len_impl<unsigned int>(_loop_best_run)) {
            new_best = _loop_best_run;
          } else {
            new_best = new_run;
          }
          List<unsigned int> _next_l = *(d_a1);
          List<unsigned int> _next_best_run = new_best;
          List<unsigned int> _next_current_run = List<unsigned int>::nil();
          _loop_l = std::move(_next_l);
          _loop_best_run = std::move(_next_best_run);
          _loop_current_run = std::move(_next_current_run);
        }
      }
    }
  }
  return _result;
}

__attribute__((pure)) List<unsigned int>
LoopifySearch::longest_run(const List<unsigned int> &l) {
  return longest_run_aux(List<unsigned int>::nil(), List<unsigned int>::nil(),
                         l);
}

/// collatz n computes Collatz sequence length (not the list).
__attribute__((pure)) unsigned int
LoopifySearch::collatz_fuel(const unsigned int &fuel, const unsigned int &n) {
  struct _Enter {
    const unsigned int n;
    const unsigned int fuel;
  };

  struct _Call1 {};

  struct _Call2 {};

  using _Frame = std::variant<_Enter, _Call1, _Call2>;
  unsigned int _result{};
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
        _result = 0u;
      } else {
        unsigned int f = fuel - 1;
        if (n == 1u) {
          _result = 0u;
        } else {
          if ((2u ? n % 2u : n) == 0u) {
            _stack.emplace_back(_Call1{});
            _stack.emplace_back(_Enter{(2u ? n / 2u : 0), f});
          } else {
            _stack.emplace_back(_Call2{});
            _stack.emplace_back(_Enter{((3u * n) + 1u), f});
          }
        }
      }
    } else if (std::holds_alternative<_Call1>(_frame)) {
      auto _f = std::move(std::get<_Call1>(_frame));
      _result = (_result + 1);
    } else {
      auto _f = std::move(std::get<_Call2>(_frame));
      _result = (_result + 1);
    }
  }
  return _result;
}

__attribute__((pure)) unsigned int
LoopifySearch::collatz(const unsigned int &n) {
  return collatz_fuel(1000u, n);
}

/// lis l simple longest increasing subsequence (greedy approach).
__attribute__((pure)) List<unsigned int>
LoopifySearch::lis(const List<unsigned int> &l) {
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
        *(_write) = std::make_unique<List<unsigned int>>(
            List<unsigned int>::cons(d_a0, List<unsigned int>::nil()));
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

/// subset_sum target l checks if any subset sums to target.
__attribute__((pure)) bool
LoopifySearch::subset_sum_fuel(const unsigned int &fuel,
                               const unsigned int &target,
                               const List<unsigned int> &l) {
  if (fuel <= 0) {
    return false;
  } else {
    unsigned int f = fuel - 1;
    if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
      return target == 0u;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<unsigned int>::Cons>(l.v());
      bool without = subset_sum_fuel(f, target, *(d_a1));
      if (without) {
        return true;
      } else {
        if (d_a0 <= target) {
          return subset_sum_fuel(
              f, (((target - d_a0) > target ? 0 : (target - d_a0))), *(d_a1));
        } else {
          return false;
        }
      }
    }
  }
}

__attribute__((pure)) bool
LoopifySearch::subset_sum(const unsigned int &target,
                          const List<unsigned int> &l) {
  return subset_sum_fuel((len_impl<unsigned int>(l) + 1), target, l);
}

/// sieve l removes multiples (simplified sieve of Eratosthenes).
__attribute__((pure)) List<unsigned int>
LoopifySearch::sieve_fuel(const unsigned int &fuel, List<unsigned int> l) {
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
        List<unsigned int> d_a1_value = List<unsigned int>(*(d_a1));
        auto _cell = std::make_unique<List<unsigned int>>(
            typename List<unsigned int>::Cons(d_a0, nullptr));
        *(_write) = std::move(_cell);
        _write =
            &std::get<typename List<unsigned int>::Cons>((*_write)->v_mut())
                 .d_a1;
        List<unsigned int> _next_l = filter_impl(
            [=](const unsigned int &y) mutable {
              return !((d_a0 ? y % d_a0 : y) == 0u);
            },
            d_a1_value);
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
LoopifySearch::sieve(const List<unsigned int> &l) {
  return sieve_fuel(len_impl<unsigned int>(l), l);
}

/// Helper: check if element is in list.
__attribute__((pure)) bool
LoopifySearch::elem_impl(const unsigned int &x, const List<unsigned int> &l) {
  bool _result;
  List<unsigned int> _loop_l = l;
  while (true) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(_loop_l.v())) {
      _result = false;
      break;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<unsigned int>::Cons>(_loop_l.v());
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

/// nub l removes duplicates from list.
__attribute__((pure)) List<unsigned int>
LoopifySearch::nub_fuel(const unsigned int &fuel, List<unsigned int> l) {
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
        if (elem_impl(d_a0, *(d_a1))) {
          List<unsigned int> _next_l = *(d_a1);
          unsigned int _next_fuel = f;
          _loop_l = std::move(_next_l);
          _loop_fuel = std::move(_next_fuel);
          continue;
        } else {
          auto _cell = std::make_unique<List<unsigned int>>(
              typename List<unsigned int>::Cons(d_a0, nullptr));
          *(_write) = std::move(_cell);
          _write =
              &std::get<typename List<unsigned int>::Cons>((*_write)->v_mut())
                   .d_a1;
          List<unsigned int> _next_l = *(d_a1);
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

__attribute__((pure)) List<unsigned int>
LoopifySearch::nub(const List<unsigned int> &l) {
  return nub_fuel(len_impl<unsigned int>(l), l);
}

/// remove_duplicates l removes all duplicate elements.
__attribute__((pure)) List<unsigned int>
LoopifySearch::remove_duplicates_fuel(const unsigned int &fuel,
                                      List<unsigned int> l) {
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
        List<unsigned int> d_a1_value = List<unsigned int>(*(d_a1));
        if (elem_impl(d_a0, d_a1_value)) {
          List<unsigned int> _next_l = d_a1_value;
          unsigned int _next_fuel = f;
          _loop_l = std::move(_next_l);
          _loop_fuel = std::move(_next_fuel);
          continue;
        } else {
          auto _cell = std::make_unique<List<unsigned int>>(
              typename List<unsigned int>::Cons(d_a0, nullptr));
          *(_write) = std::move(_cell);
          _write =
              &std::get<typename List<unsigned int>::Cons>((*_write)->v_mut())
                   .d_a1;
          List<unsigned int> _next_l = filter_impl(
              [=](const unsigned int &y) mutable { return !(d_a0 == y); },
              d_a1_value);
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

__attribute__((pure)) List<unsigned int>
LoopifySearch::remove_duplicates(const List<unsigned int> &l) {
  return remove_duplicates_fuel(len_impl<unsigned int>(l), l);
}

/// quicksort l sorts list using quicksort with filter-based partitioning.
__attribute__((pure)) List<unsigned int>
LoopifySearch::quicksort_fuel(const unsigned int &fuel, List<unsigned int> l) {
  struct _Enter {
    List<unsigned int> l;
    const unsigned int fuel;
  };

  struct _Call1 {
    List<unsigned int> _s0;
    unsigned int _s1;
    unsigned int _s2;
  };

  struct _Call2 {
    List<unsigned int> _s0;
    unsigned int _s1;
  };

  using _Frame = std::variant<_Enter, _Call1, _Call2>;
  List<unsigned int> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{l, fuel});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      List<unsigned int> l = _f.l;
      const unsigned int fuel = _f.fuel;
      if (fuel <= 0) {
        _result = l;
      } else {
        unsigned int f = fuel - 1;
        if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
          _result = List<unsigned int>::nil();
        } else {
          const auto &[d_a0, d_a1] =
              std::get<typename List<unsigned int>::Cons>(l.v());
          List<unsigned int> d_a1_value = List<unsigned int>(*(d_a1));
          List<unsigned int> smaller = filter_impl(
              [=](const unsigned int &y) mutable { return y < d_a0; },
              d_a1_value);
          List<unsigned int> greater = filter_impl(
              [=](const unsigned int &y) mutable { return d_a0 <= y; },
              d_a1_value);
          _stack.emplace_back(_Call1{smaller, f, d_a0});
          _stack.emplace_back(_Enter{greater, f});
        }
      }
    } else if (std::holds_alternative<_Call1>(_frame)) {
      auto _f = std::move(std::get<_Call1>(_frame));
      _stack.emplace_back(_Call2{_result, _f._s2});
      _stack.emplace_back(_Enter{_f._s0, _f._s1});
    } else {
      auto _f = std::move(std::get<_Call2>(_frame));
      _result = _result.app(List<unsigned int>::cons(_f._s1, _f._s0));
    }
  }
  return _result;
}

__attribute__((pure)) List<unsigned int>
LoopifySearch::quicksort(const List<unsigned int> &l) {
  return quicksort_fuel(len_impl<unsigned int>(l), l);
}

/// Helper: split list into two roughly equal parts.
__attribute__((pure)) std::pair<List<unsigned int>, List<unsigned int>>
LoopifySearch::split_list(const List<unsigned int> &l) {
  struct _Enter {
    const List<unsigned int> l;
  };

  struct _Call1 {
    unsigned int _s0;
    unsigned int _s1;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::pair<List<unsigned int>, List<unsigned int>> _result{};
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
        _result = std::make_pair(List<unsigned int>::nil(),
                                 List<unsigned int>::nil());
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<unsigned int>::Cons>(l.v());
        auto &&_sv0 = *(d_a1);
        if (std::holds_alternative<typename List<unsigned int>::Nil>(
                _sv0.v())) {
          _result = std::make_pair(
              List<unsigned int>::cons(d_a0, List<unsigned int>::nil()),
              List<unsigned int>::nil());
        } else {
          const auto &[d_a00, d_a10] =
              std::get<typename List<unsigned int>::Cons>(_sv0.v());
          _stack.emplace_back(_Call1{d_a0, d_a00});
          _stack.emplace_back(_Enter{*(d_a10)});
        }
      }
    } else {
      auto _f = std::move(std::get<_Call1>(_frame));
      unsigned int d_a0 = _f._s0;
      unsigned int d_a00 = _f._s1;
      const List<unsigned int> &a = _result.first;
      const List<unsigned int> &b = _result.second;
      _result = std::make_pair(List<unsigned int>::cons(d_a0, a),
                               List<unsigned int>::cons(d_a00, b));
    }
  }
  return _result;
}

/// Helper: merge two sorted lists with fuel.
__attribute__((pure)) List<unsigned int>
LoopifySearch::merge_sorted_fuel(const unsigned int &fuel,
                                 List<unsigned int> l1, List<unsigned int> l2) {
  std::unique_ptr<List<unsigned int>> _head{};
  std::unique_ptr<List<unsigned int>> *_write = &_head;
  List<unsigned int> _loop_l2 = std::move(l2);
  List<unsigned int> _loop_l1 = std::move(l1);
  unsigned int _loop_fuel = fuel;
  while (true) {
    if (_loop_fuel <= 0) {
      *(_write) = std::make_unique<List<unsigned int>>(_loop_l1.app(_loop_l2));
      break;
    } else {
      unsigned int f = _loop_fuel - 1;
      if (std::holds_alternative<typename List<unsigned int>::Nil>(
              _loop_l1.v())) {
        *(_write) = std::make_unique<List<unsigned int>>(_loop_l2);
        break;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<unsigned int>::Cons>(_loop_l1.v());
        if (std::holds_alternative<typename List<unsigned int>::Nil>(
                _loop_l2.v())) {
          *(_write) = std::make_unique<List<unsigned int>>(_loop_l1);
          break;
        } else {
          const auto &[d_a00, d_a10] =
              std::get<typename List<unsigned int>::Cons>(_loop_l2.v());
          if (d_a0 <= d_a00) {
            auto _cell = std::make_unique<List<unsigned int>>(
                typename List<unsigned int>::Cons(d_a0, nullptr));
            *(_write) = std::move(_cell);
            _write =
                &std::get<typename List<unsigned int>::Cons>((*_write)->v_mut())
                     .d_a1;
            List<unsigned int> _next_l1 = *(d_a1);
            unsigned int _next_fuel = f;
            _loop_l1 = std::move(_next_l1);
            _loop_fuel = std::move(_next_fuel);
            continue;
          } else {
            auto _cell = std::make_unique<List<unsigned int>>(
                typename List<unsigned int>::Cons(d_a00, nullptr));
            *(_write) = std::move(_cell);
            _write =
                &std::get<typename List<unsigned int>::Cons>((*_write)->v_mut())
                     .d_a1;
            List<unsigned int> _next_l2 = *(d_a10);
            unsigned int _next_fuel = f;
            _loop_l2 = std::move(_next_l2);
            _loop_fuel = std::move(_next_fuel);
            continue;
          }
        }
      }
    }
  }
  return std::move(*(_head));
}

__attribute__((pure)) List<unsigned int>
LoopifySearch::merge_sorted(const List<unsigned int> &l1,
                            const List<unsigned int> &l2) {
  return merge_sorted_fuel(
      (len_impl<unsigned int>(l1) + len_impl<unsigned int>(l2)), l1, l2);
}

/// merge_sort l sorts list using merge sort.
__attribute__((pure)) List<unsigned int>
LoopifySearch::merge_sort_fuel(const unsigned int &fuel, List<unsigned int> l) {
  struct _Enter {
    List<unsigned int> l;
    const unsigned int fuel;
  };

  struct _Call1 {
    List<unsigned int> _s0;
    unsigned int _s1;
  };

  struct _Call2 {
    List<unsigned int> _s0;
  };

  using _Frame = std::variant<_Enter, _Call1, _Call2>;
  List<unsigned int> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{l, fuel});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      List<unsigned int> l = _f.l;
      const unsigned int fuel = _f.fuel;
      if (fuel <= 0) {
        _result = l;
      } else {
        unsigned int f = fuel - 1;
        if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
          _result = List<unsigned int>::nil();
        } else {
          const auto &[d_a0, d_a1] =
              std::get<typename List<unsigned int>::Cons>(l.v());
          auto &&_sv = *(d_a1);
          if (std::holds_alternative<typename List<unsigned int>::Nil>(
                  _sv.v())) {
            _result = l;
          } else {
            auto _cs = split_list(l);
            const List<unsigned int> &a = _cs.first;
            const List<unsigned int> &b = _cs.second;
            _stack.emplace_back(_Call1{a, f});
            _stack.emplace_back(_Enter{b, f});
          }
        }
      }
    } else if (std::holds_alternative<_Call1>(_frame)) {
      auto _f = std::move(std::get<_Call1>(_frame));
      _stack.emplace_back(_Call2{_result});
      _stack.emplace_back(_Enter{_f._s0, _f._s1});
    } else {
      auto _f = std::move(std::get<_Call2>(_frame));
      _result = merge_sorted(_result, _f._s0);
    }
  }
  return _result;
}

__attribute__((pure)) List<unsigned int>
LoopifySearch::merge_sort(const List<unsigned int> &l) {
  return merge_sort_fuel(len_impl<unsigned int>(l), l);
}

/// Helper: remove first occurrence of x from list.
__attribute__((pure)) List<unsigned int>
LoopifySearch::remove_first(const unsigned int &x,
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
        *(_write) = std::make_unique<List<unsigned int>>(*(d_a1));
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

/// Helper: map function that prepends element to each list.
__attribute__((pure)) List<List<unsigned int>>
LoopifySearch::map_cons(unsigned int x, const List<List<unsigned int>> &lsts) {
  std::unique_ptr<List<List<unsigned int>>> _head{};
  std::unique_ptr<List<List<unsigned int>>> *_write = &_head;
  List<List<unsigned int>> _loop_lsts = lsts;
  while (true) {
    if (std::holds_alternative<typename List<List<unsigned int>>::Nil>(
            _loop_lsts.v())) {
      *(_write) = std::make_unique<List<List<unsigned int>>>(
          List<List<unsigned int>>::nil());
      break;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<List<unsigned int>>::Cons>(_loop_lsts.v());
      auto _cell = std::make_unique<List<List<unsigned int>>>(
          typename List<List<unsigned int>>::Cons(
              List<unsigned int>::cons(x, d_a0), nullptr));
      *(_write) = std::move(_cell);
      _write =
          &std::get<typename List<List<unsigned int>>::Cons>((*_write)->v_mut())
               .d_a1;
      _loop_lsts = *(d_a1);
      continue;
    }
  }
  return std::move(*(_head));
}

/// perms_choices_fuel fuel choices orig generates permutations by iterating
/// over choices.  Single self-recursive function for full loopification.
/// Match on remaining is hoisted out of let-binding.
__attribute__((pure)) List<List<unsigned int>>
LoopifySearch::perms_choices_fuel(const unsigned int &fuel,
                                  const List<unsigned int> &choices,
                                  const List<unsigned int> &orig) {
  struct _Enter {
    const List<unsigned int> orig;
    const List<unsigned int> choices;
    const unsigned int fuel;
  };

  struct _Call1 {
    decltype(map_cons(
        std::declval<unsigned int &>(),
        List<List<unsigned int>>::cons(List<unsigned int>::nil(),
                                       List<List<unsigned int>>::nil()))) _s0;
  };

  struct _Call2 {
    List<unsigned int> _s0;
    List<unsigned int> _s1;
    unsigned int _s2;
    unsigned int _s3;
  };

  struct _Call3 {
    List<List<unsigned int>> _s0;
    unsigned int _s1;
  };

  using _Frame = std::variant<_Enter, _Call1, _Call2, _Call3>;
  List<List<unsigned int>> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{orig, choices, fuel});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<unsigned int> orig = _f.orig;
      const List<unsigned int> choices = _f.choices;
      const unsigned int fuel = _f.fuel;
      if (fuel <= 0) {
        _result = List<List<unsigned int>>::nil();
      } else {
        unsigned int f = fuel - 1;
        if (std::holds_alternative<typename List<unsigned int>::Nil>(
                choices.v())) {
          _result = List<List<unsigned int>>::nil();
        } else {
          const auto &[d_a0, d_a1] =
              std::get<typename List<unsigned int>::Cons>(choices.v());
          List<unsigned int> remaining = remove_first(d_a0, orig);
          if (std::holds_alternative<typename List<unsigned int>::Nil>(
                  remaining.v())) {
            _stack.emplace_back(
                _Call1{map_cons(d_a0, List<List<unsigned int>>::cons(
                                          List<unsigned int>::nil(),
                                          List<List<unsigned int>>::nil()))});
            _stack.emplace_back(_Enter{orig, *(d_a1), f});
          } else {
            _stack.emplace_back(_Call2{remaining, remaining, f, d_a0});
            _stack.emplace_back(_Enter{orig, *(d_a1), f});
          }
        }
      }
    } else if (std::holds_alternative<_Call1>(_frame)) {
      auto _f = std::move(std::get<_Call1>(_frame));
      _result = _f._s0.app(_result);
    } else if (std::holds_alternative<_Call2>(_frame)) {
      auto _f = std::move(std::get<_Call2>(_frame));
      _stack.emplace_back(_Call3{_result, _f._s3});
      _stack.emplace_back(_Enter{_f._s0, _f._s1, _f._s2});
    } else {
      auto _f = std::move(std::get<_Call3>(_frame));
      _result = map_cons(_f._s1, _result).app(_f._s0);
    }
  }
  return _result;
}

/// permutations_fuel fuel l generates all permutations of list.
__attribute__((pure)) List<List<unsigned int>>
LoopifySearch::permutations_fuel(const unsigned int &fuel,
                                 const List<unsigned int> &l) {
  if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
    return List<List<unsigned int>>::cons(List<unsigned int>::nil(),
                                          List<List<unsigned int>>::nil());
  } else {
    return perms_choices_fuel(fuel, l, l);
  }
}

__attribute__((pure)) List<List<unsigned int>>
LoopifySearch::permutations(const List<unsigned int> &l) {
  return permutations_fuel((len_impl<unsigned int>(l) + 1), l);
}

/// linear_search x l finds index of first occurrence of x.
__attribute__((pure)) std::optional<unsigned int>
LoopifySearch::linear_search_aux(const unsigned int &x,
                                 const List<unsigned int> &l,
                                 unsigned int idx) {
  std::optional<unsigned int> _result;
  unsigned int _loop_idx = std::move(idx);
  List<unsigned int> _loop_l = l;
  while (true) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(_loop_l.v())) {
      _result = std::optional<unsigned int>();
      break;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<unsigned int>::Cons>(_loop_l.v());
      if (x == d_a0) {
        _result = std::make_optional<unsigned int>(_loop_idx);
        break;
      } else {
        unsigned int _next_idx = (_loop_idx + 1);
        List<unsigned int> _next_l = *(d_a1);
        _loop_idx = std::move(_next_idx);
        _loop_l = std::move(_next_l);
      }
    }
  }
  return _result;
}

__attribute__((pure)) std::optional<unsigned int>
LoopifySearch::linear_search(const unsigned int &x,
                             const List<unsigned int> &l) {
  return linear_search_aux(x, l, 0u);
}

/// all_indices x l finds all indices where x occurs.
__attribute__((pure)) List<unsigned int>
LoopifySearch::all_indices_aux(const unsigned int &x,
                               const List<unsigned int> &l, unsigned int idx) {
  std::unique_ptr<List<unsigned int>> _head{};
  std::unique_ptr<List<unsigned int>> *_write = &_head;
  unsigned int _loop_idx = std::move(idx);
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
        auto _cell = std::make_unique<List<unsigned int>>(
            typename List<unsigned int>::Cons(_loop_idx, nullptr));
        *(_write) = std::move(_cell);
        _write =
            &std::get<typename List<unsigned int>::Cons>((*_write)->v_mut())
                 .d_a1;
        unsigned int _next_idx = (_loop_idx + 1);
        List<unsigned int> _next_l = *(d_a1);
        _loop_idx = std::move(_next_idx);
        _loop_l = std::move(_next_l);
        continue;
      } else {
        unsigned int _next_idx = (_loop_idx + 1);
        List<unsigned int> _next_l = *(d_a1);
        _loop_idx = std::move(_next_idx);
        _loop_l = std::move(_next_l);
        continue;
      }
    }
  }
  return std::move(*(_head));
}

__attribute__((pure)) List<unsigned int>
LoopifySearch::all_indices(const unsigned int &x, const List<unsigned int> &l) {
  return all_indices_aux(x, l, 0u);
}

/// min_element l finds minimum element in list.
__attribute__((pure)) unsigned int
LoopifySearch::min_element(const List<unsigned int> &l) {
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
        auto &&_sv = *(d_a1);
        if (std::holds_alternative<typename List<unsigned int>::Nil>(_sv.v())) {
          _result = d_a0;
        } else {
          _stack.emplace_back(_Call1{d_a0});
          _stack.emplace_back(_Enter{*(d_a1)});
        }
      }
    } else {
      auto _f = std::move(std::get<_Call1>(_frame));
      unsigned int d_a0 = _f._s0;
      unsigned int min_rest = _result;
      if (d_a0 <= min_rest) {
        _result = d_a0;
      } else {
        _result = min_rest;
      }
    }
  }
  return _result;
}
