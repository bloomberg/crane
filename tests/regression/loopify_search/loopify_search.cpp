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
    const unsigned int fuel, const unsigned int capacity,
    const std::shared_ptr<List<std::pair<unsigned int, unsigned int>>> &items) {
  struct _Enter {
    const std::shared_ptr<List<std::pair<unsigned int, unsigned int>>> items;
    const unsigned int capacity;
    const unsigned int fuel;
  };

  struct _Call1 {
    const typename List<std::pair<unsigned int, unsigned int>>::Cons _s0;
    const unsigned int _s1;
    unsigned int _s2;
    unsigned int _s3;
    unsigned int _s4;
  };

  struct _Call2 {
    unsigned int _s0;
    const typename List<std::pair<unsigned int, unsigned int>>::Cons _s1;
    const unsigned int _s2;
    unsigned int _s3;
    unsigned int _s4;
    unsigned int _s5;
  };

  struct _Call3 {
    unsigned int _s0;
  };

  using _Frame = std::variant<_Enter, _Call1, _Call2, _Call3>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.emplace_back(_Enter{items, capacity, fuel});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      const auto &_f = std::get<_Enter>(_frame);
      const std::shared_ptr<List<std::pair<unsigned int, unsigned int>>> items =
          _f.items;
      const unsigned int capacity = _f.capacity;
      const unsigned int fuel = _f.fuel;
      if (fuel <= 0) {
        _result = 0u;
      } else {
        unsigned int f = fuel - 1;
        if (std::holds_alternative<
                typename List<std::pair<unsigned int, unsigned int>>::Nil>(
                items->v())) {
          _result = 0u;
        } else {
          const auto &_m = *std::get_if<
              typename List<std::pair<unsigned int, unsigned int>>::Cons>(
              &items->v());
          const unsigned int &weight = _m.d_a0.first;
          const unsigned int &value = _m.d_a0.second;
          if (capacity < weight) {
            _stack.emplace_back(_Enter{_m.d_a1, capacity, f});
          } else {
            _stack.emplace_back(_Call1{_m, capacity, f, value, weight});
            _stack.emplace_back(_Enter{
                _m.d_a1,
                (((capacity - weight) > capacity ? 0 : (capacity - weight))),
                f});
          }
        }
      }
    } else if (std::holds_alternative<_Call1>(_frame)) {
      const auto &_f = std::get<_Call1>(_frame);
      const typename List<std::pair<unsigned int, unsigned int>>::Cons _m =
          _f._s0;
      const unsigned int capacity = _f._s1;
      unsigned int f = _f._s2;
      unsigned int value = _f._s3;
      unsigned int weight = _f._s4;
      unsigned int _cond0 = _result;
      _stack.emplace_back(_Call2{_cond0, _m, capacity, f, value, weight});
      _stack.emplace_back(_Enter{_m.d_a1, capacity, f});
    } else if (std::holds_alternative<_Call2>(_frame)) {
      const auto &_f = std::get<_Call2>(_frame);
      unsigned int _cond0 = _f._s0;
      const typename List<std::pair<unsigned int, unsigned int>>::Cons _m =
          _f._s1;
      const unsigned int capacity = _f._s2;
      unsigned int f = _f._s3;
      unsigned int value = _f._s4;
      unsigned int weight = _f._s5;
      unsigned int _cond1 = _result;
      if (_cond1 <= (value + _cond0)) {
        _stack.emplace_back(_Call3{value});
        _stack.emplace_back(_Enter{
            _m.d_a1,
            (((capacity - weight) > capacity ? 0 : (capacity - weight))), f});
      } else {
        _stack.emplace_back(_Enter{_m.d_a1, capacity, f});
      }
    } else {
      const auto &_f = std::get<_Call3>(_frame);
      _result = (_f._s0 + _result);
    }
  }
  return _result;
}

__attribute__((pure)) unsigned int LoopifySearch::knapsack(
    const unsigned int capacity,
    const std::shared_ptr<List<std::pair<unsigned int, unsigned int>>> &items) {
  return knapsack_fuel(len_impl<std::pair<unsigned int, unsigned int>>(items),
                       capacity, items);
}

/// majority l finds majority element using Boyer-Moore algorithm.
/// Returns (candidate, count).
__attribute__((pure)) std::pair<unsigned int, unsigned int>
LoopifySearch::majority(const std::shared_ptr<List<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<List<unsigned int>> l;
  };

  struct _Call1 {
    const typename List<unsigned int>::Cons _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::pair<unsigned int, unsigned int> _result{};
  std::vector<_Frame> _stack;
  _stack.emplace_back(_Enter{l});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      const auto &_f = std::get<_Enter>(_frame);
      const std::shared_ptr<List<unsigned int>> l = _f.l;
      if (std::holds_alternative<typename List<unsigned int>::Nil>(l->v())) {
        _result = std::make_pair(0u, 0u);
      } else {
        const auto &_m =
            *std::get_if<typename List<unsigned int>::Cons>(&l->v());
        _stack.emplace_back(_Call1{_m});
        _stack.emplace_back(_Enter{_m.d_a1});
      }
    } else {
      const auto &_f = std::get<_Call1>(_frame);
      const typename List<unsigned int>::Cons _m = _f._s0;
      const unsigned int &cand = _result.first;
      const unsigned int &count = _result.second;
      if (_m.d_a0 == cand) {
        _result = std::make_pair(cand, (count + 1));
      } else {
        if (0u < count) {
          _result =
              std::make_pair(cand, (((count - 1u) > count ? 0 : (count - 1u))));
        } else {
          _result = std::make_pair(_m.d_a0, 1u);
        }
      }
    }
  }
  return _result;
}

/// longest_increasing_subseq l finds a longest increasing subsequence (greedy).
std::shared_ptr<List<unsigned int>> LoopifySearch::longest_increasing_subseq(
    const std::shared_ptr<List<unsigned int>> &l) {
  std::shared_ptr<List<unsigned int>> _head{};
  std::shared_ptr<List<unsigned int>> _last{};
  std::shared_ptr<List<unsigned int>> _loop_l = l;
  bool _continue = true;
  while (_continue) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(
            _loop_l->v())) {
      if (_last) {
        std::get<typename List<unsigned int>::Cons>(_last->v_mut()).d_a1 =
            List<unsigned int>::nil();
      } else {
        _head = List<unsigned int>::nil();
      }
      _continue = false;
    } else {
      const auto &_m =
          *std::get_if<typename List<unsigned int>::Cons>(&_loop_l->v());
      auto &&_sv0 = _m.d_a1;
      if (std::holds_alternative<typename List<unsigned int>::Nil>(_sv0->v())) {
        if (_last) {
          std::get<typename List<unsigned int>::Cons>(_last->v_mut()).d_a1 =
              List<unsigned int>::cons(_m.d_a0, List<unsigned int>::nil());
        } else {
          _head = List<unsigned int>::cons(_m.d_a0, List<unsigned int>::nil());
        }
        _continue = false;
      } else {
        const auto &_m0 =
            *std::get_if<typename List<unsigned int>::Cons>(&_sv0->v());
        if (_m.d_a0 < _m0.d_a0) {
          auto _cell = List<unsigned int>::cons(_m.d_a0, nullptr);
          if (_last) {
            std::get<typename List<unsigned int>::Cons>(_last->v_mut()).d_a1 =
                _cell;
          } else {
            _head = _cell;
          }
          _last = _cell;
          _loop_l = _m.d_a1;
          continue;
        } else {
          _loop_l = _m.d_a1;
          continue;
        }
      }
    }
  }
  return _head;
}

/// Helper for binary search: get nth element.
__attribute__((pure)) unsigned int
LoopifySearch::nth_impl(const unsigned int n,
                        const std::shared_ptr<List<unsigned int>> &l) {
  unsigned int _result;
  std::shared_ptr<List<unsigned int>> _loop_l = l;
  unsigned int _loop_n = n;
  bool _continue = true;
  while (_continue) {
    if (_loop_n <= 0) {
      if (std::holds_alternative<typename List<unsigned int>::Nil>(
              _loop_l->v())) {
        _result = 0u;
        _continue = false;
      } else {
        const auto &_m =
            *std::get_if<typename List<unsigned int>::Cons>(&_loop_l->v());
        _result = _m.d_a0;
        _continue = false;
      }
    } else {
      unsigned int m = _loop_n - 1;
      if (std::holds_alternative<typename List<unsigned int>::Nil>(
              _loop_l->v())) {
        _result = 0u;
        _continue = false;
      } else {
        const auto &_m0 =
            *std::get_if<typename List<unsigned int>::Cons>(&_loop_l->v());
        std::shared_ptr<List<unsigned int>> _next_l = _m0.d_a1;
        unsigned int _next_n = m;
        _loop_l = std::move(_next_l);
        _loop_n = std::move(_next_n);
      }
    }
  }
  return _result;
}

/// Helper for binary search: take first k elements.
std::shared_ptr<List<unsigned int>>
LoopifySearch::take_impl(const unsigned int k,
                         const std::shared_ptr<List<unsigned int>> &l) {
  std::shared_ptr<List<unsigned int>> _head{};
  std::shared_ptr<List<unsigned int>> _last{};
  std::shared_ptr<List<unsigned int>> _loop_l = l;
  unsigned int _loop_k = k;
  bool _continue = true;
  while (_continue) {
    if (_loop_k <= 0) {
      if (_last) {
        std::get<typename List<unsigned int>::Cons>(_last->v_mut()).d_a1 =
            List<unsigned int>::nil();
      } else {
        _head = List<unsigned int>::nil();
      }
      _continue = false;
    } else {
      unsigned int m = _loop_k - 1;
      if (std::holds_alternative<typename List<unsigned int>::Nil>(
              _loop_l->v())) {
        if (_last) {
          std::get<typename List<unsigned int>::Cons>(_last->v_mut()).d_a1 =
              List<unsigned int>::nil();
        } else {
          _head = List<unsigned int>::nil();
        }
        _continue = false;
      } else {
        const auto &_m =
            *std::get_if<typename List<unsigned int>::Cons>(&_loop_l->v());
        auto _cell = List<unsigned int>::cons(_m.d_a0, nullptr);
        if (_last) {
          std::get<typename List<unsigned int>::Cons>(_last->v_mut()).d_a1 =
              _cell;
        } else {
          _head = _cell;
        }
        _last = _cell;
        std::shared_ptr<List<unsigned int>> _next_l = _m.d_a1;
        unsigned int _next_k = m;
        _loop_l = std::move(_next_l);
        _loop_k = std::move(_next_k);
        continue;
      }
    }
  }
  return _head;
}

/// Helper for binary search: drop first k elements.
std::shared_ptr<List<unsigned int>>
LoopifySearch::drop_impl(const unsigned int k,
                         std::shared_ptr<List<unsigned int>> l) {
  std::shared_ptr<List<unsigned int>> _result;
  std::shared_ptr<List<unsigned int>> _loop_l = l;
  unsigned int _loop_k = k;
  bool _continue = true;
  while (_continue) {
    if (_loop_k <= 0) {
      _result = std::move(_loop_l);
      _continue = false;
    } else {
      unsigned int m = _loop_k - 1;
      if (std::holds_alternative<typename List<unsigned int>::Nil>(
              _loop_l->v()) &&
          _loop_l.use_count() == 1) {
        _result = _loop_l;
        _continue = false;
      } else if (std::holds_alternative<typename List<unsigned int>::Nil>(
                     _loop_l->v())) {
        _result = List<unsigned int>::nil();
        _continue = false;
      } else {
        const auto &_m =
            *std::get_if<typename List<unsigned int>::Cons>(&_loop_l->v());
        std::shared_ptr<List<unsigned int>> _next_l = _m.d_a1;
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
__attribute__((pure)) bool LoopifySearch::binary_search_fuel(
    const unsigned int fuel, const unsigned int target,
    const std::shared_ptr<List<unsigned int>> &l) {
  bool _result;
  std::shared_ptr<List<unsigned int>> _loop_l = l;
  unsigned int _loop_fuel = fuel;
  bool _continue = true;
  while (_continue) {
    if (_loop_fuel <= 0) {
      _result = false;
      _continue = false;
    } else {
      unsigned int f = _loop_fuel - 1;
      unsigned int n = len_impl<unsigned int>(_loop_l);
      if (n <= 0) {
        _result = false;
        _continue = false;
      } else {
        unsigned int _x = n - 1;
        unsigned int mid = (2u ? n / 2u : 0);
        unsigned int mid_val = nth_impl(mid, _loop_l);
        if (target == mid_val) {
          _result = true;
          _continue = false;
        } else {
          if (target < mid_val) {
            std::shared_ptr<List<unsigned int>> _next_l =
                take_impl(mid, _loop_l);
            unsigned int _next_fuel = f;
            _loop_l = std::move(_next_l);
            _loop_fuel = std::move(_next_fuel);
          } else {
            std::shared_ptr<List<unsigned int>> _next_l =
                drop_impl((mid + 1), _loop_l);
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
LoopifySearch::binary_search(const unsigned int target,
                             const std::shared_ptr<List<unsigned int>> &l) {
  return binary_search_fuel(len_impl<unsigned int>(l), target, l);
}

/// longest_run l finds the longest run of consecutive equal elements.
std::shared_ptr<List<unsigned int>>
LoopifySearch::longest_run_aux(std::shared_ptr<List<unsigned int>> current_run,
                               std::shared_ptr<List<unsigned int>> best_run,
                               const std::shared_ptr<List<unsigned int>> &l) {
  std::shared_ptr<List<unsigned int>> _result;
  std::shared_ptr<List<unsigned int>> _loop_l = l;
  std::shared_ptr<List<unsigned int>> _loop_best_run = best_run;
  std::shared_ptr<List<unsigned int>> _loop_current_run = current_run;
  bool _continue = true;
  while (_continue) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(
            _loop_l->v())) {
      if (len_impl<unsigned int>(_loop_current_run) <=
          len_impl<unsigned int>(_loop_best_run)) {
        _result = std::move(_loop_best_run);
        _continue = false;
      } else {
        _result = std::move(_loop_current_run);
        _continue = false;
      }
    } else {
      const auto &_m =
          *std::get_if<typename List<unsigned int>::Cons>(&_loop_l->v());
      auto &&_sv0 = _m.d_a1;
      if (std::holds_alternative<typename List<unsigned int>::Nil>(_sv0->v())) {
        std::shared_ptr<List<unsigned int>> new_run =
            List<unsigned int>::cons(_m.d_a0, _loop_current_run);
        if (len_impl<unsigned int>(new_run) <=
            len_impl<unsigned int>(_loop_best_run)) {
          _result = std::move(_loop_best_run);
          _continue = false;
        } else {
          _result = std::move(new_run);
          _continue = false;
        }
      } else {
        const auto &_m0 =
            *std::get_if<typename List<unsigned int>::Cons>(&_sv0->v());
        if (_m.d_a0 == _m0.d_a0) {
          std::shared_ptr<List<unsigned int>> _next_l = _m.d_a1;
          std::shared_ptr<List<unsigned int>> _next_best_run =
              std::move(_loop_best_run);
          std::shared_ptr<List<unsigned int>> _next_current_run =
              List<unsigned int>::cons(_m.d_a0, _loop_current_run);
          _loop_l = std::move(_next_l);
          _loop_best_run = std::move(_next_best_run);
          _loop_current_run = std::move(_next_current_run);
        } else {
          std::shared_ptr<List<unsigned int>> new_run =
              List<unsigned int>::cons(_m.d_a0, _loop_current_run);
          std::shared_ptr<List<unsigned int>> new_best;
          if (len_impl<unsigned int>(new_run) <=
              len_impl<unsigned int>(_loop_best_run)) {
            new_best = _loop_best_run;
          } else {
            new_best = new_run;
          }
          std::shared_ptr<List<unsigned int>> _next_l = _m.d_a1;
          std::shared_ptr<List<unsigned int>> _next_best_run =
              std::move(new_best);
          std::shared_ptr<List<unsigned int>> _next_current_run =
              List<unsigned int>::nil();
          _loop_l = std::move(_next_l);
          _loop_best_run = std::move(_next_best_run);
          _loop_current_run = std::move(_next_current_run);
        }
      }
    }
  }
  return _result;
}

std::shared_ptr<List<unsigned int>>
LoopifySearch::longest_run(const std::shared_ptr<List<unsigned int>> &l) {
  return longest_run_aux(List<unsigned int>::nil(), List<unsigned int>::nil(),
                         l);
}

/// collatz n computes Collatz sequence length (not the list).
__attribute__((pure)) unsigned int
LoopifySearch::collatz_fuel(const unsigned int fuel, const unsigned int n) {
  struct _Enter {
    const unsigned int n;
    const unsigned int fuel;
  };

  struct _Call1 {};

  struct _Call2 {};

  using _Frame = std::variant<_Enter, _Call1, _Call2>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.emplace_back(_Enter{n, fuel});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      const auto &_f = std::get<_Enter>(_frame);
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
      const auto &_f = std::get<_Call1>(_frame);
      _result = (_result + 1);
    } else {
      const auto &_f = std::get<_Call2>(_frame);
      _result = (_result + 1);
    }
  }
  return _result;
}

__attribute__((pure)) unsigned int
LoopifySearch::collatz(const unsigned int n) {
  return collatz_fuel(1000u, n);
}

/// lis l simple longest increasing subsequence (greedy approach).
std::shared_ptr<List<unsigned int>>
LoopifySearch::lis(const std::shared_ptr<List<unsigned int>> &l) {
  std::shared_ptr<List<unsigned int>> _head{};
  std::shared_ptr<List<unsigned int>> _last{};
  std::shared_ptr<List<unsigned int>> _loop_l = l;
  bool _continue = true;
  while (_continue) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(
            _loop_l->v())) {
      if (_last) {
        std::get<typename List<unsigned int>::Cons>(_last->v_mut()).d_a1 =
            List<unsigned int>::nil();
      } else {
        _head = List<unsigned int>::nil();
      }
      _continue = false;
    } else {
      const auto &_m =
          *std::get_if<typename List<unsigned int>::Cons>(&_loop_l->v());
      auto &&_sv0 = _m.d_a1;
      if (std::holds_alternative<typename List<unsigned int>::Nil>(_sv0->v())) {
        if (_last) {
          std::get<typename List<unsigned int>::Cons>(_last->v_mut()).d_a1 =
              List<unsigned int>::cons(_m.d_a0, List<unsigned int>::nil());
        } else {
          _head = List<unsigned int>::cons(_m.d_a0, List<unsigned int>::nil());
        }
        _continue = false;
      } else {
        const auto &_m0 =
            *std::get_if<typename List<unsigned int>::Cons>(&_sv0->v());
        if (_m.d_a0 < _m0.d_a0) {
          auto _cell = List<unsigned int>::cons(_m.d_a0, nullptr);
          if (_last) {
            std::get<typename List<unsigned int>::Cons>(_last->v_mut()).d_a1 =
                _cell;
          } else {
            _head = _cell;
          }
          _last = _cell;
          _loop_l = _m.d_a1;
          continue;
        } else {
          _loop_l = _m.d_a1;
          continue;
        }
      }
    }
  }
  return _head;
}

/// subset_sum target l checks if any subset sums to target.
__attribute__((pure)) bool
LoopifySearch::subset_sum_fuel(const unsigned int fuel,
                               const unsigned int target,
                               const std::shared_ptr<List<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<List<unsigned int>> l;
    const unsigned int target;
    const unsigned int fuel;
  };

  struct _Call1 {
    const typename List<unsigned int>::Cons _s0;
    unsigned int _s1;
    const unsigned int _s2;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  bool _result{};
  std::vector<_Frame> _stack;
  _stack.emplace_back(_Enter{l, target, fuel});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      const auto &_f = std::get<_Enter>(_frame);
      const std::shared_ptr<List<unsigned int>> l = _f.l;
      const unsigned int target = _f.target;
      const unsigned int fuel = _f.fuel;
      if (fuel <= 0) {
        _result = false;
      } else {
        unsigned int f = fuel - 1;
        if (std::holds_alternative<typename List<unsigned int>::Nil>(l->v())) {
          _result = target == 0u;
        } else {
          const auto &_m =
              *std::get_if<typename List<unsigned int>::Cons>(&l->v());
          _stack.emplace_back(_Call1{_m, f, target});
          _stack.emplace_back(_Enter{_m.d_a1, target, f});
        }
      }
    } else {
      const auto &_f = std::get<_Call1>(_frame);
      const typename List<unsigned int>::Cons _m = _f._s0;
      unsigned int f = _f._s1;
      const unsigned int target = _f._s2;
      bool without = _result;
      if (without) {
        _result = true;
      } else {
        if (_m.d_a0 <= target) {
          _stack.emplace_back(_Enter{
              _m.d_a1, (((target - _m.d_a0) > target ? 0 : (target - _m.d_a0))),
              f});
        } else {
          _result = false;
        }
      }
    }
  }
  return _result;
}

__attribute__((pure)) bool
LoopifySearch::subset_sum(const unsigned int target,
                          const std::shared_ptr<List<unsigned int>> &l) {
  return subset_sum_fuel((len_impl<unsigned int>(l) + 1), target, l);
}

/// sieve l removes multiples (simplified sieve of Eratosthenes).
std::shared_ptr<List<unsigned int>>
LoopifySearch::sieve_fuel(const unsigned int fuel,
                          std::shared_ptr<List<unsigned int>> l) {
  std::shared_ptr<List<unsigned int>> _head{};
  std::shared_ptr<List<unsigned int>> _last{};
  std::shared_ptr<List<unsigned int>> _loop_l = l;
  unsigned int _loop_fuel = fuel;
  bool _continue = true;
  while (_continue) {
    if (_loop_fuel <= 0) {
      if (_last) {
        std::get<typename List<unsigned int>::Cons>(_last->v_mut()).d_a1 =
            std::move(_loop_l);
      } else {
        _head = std::move(_loop_l);
      }
      _continue = false;
    } else {
      unsigned int f = _loop_fuel - 1;
      if (std::holds_alternative<typename List<unsigned int>::Nil>(
              _loop_l->v()) &&
          _loop_l.use_count() == 1) {
        if (_last) {
          std::get<typename List<unsigned int>::Cons>(_last->v_mut()).d_a1 =
              _loop_l;
        } else {
          _head = _loop_l;
        }
        _continue = false;
      } else if (std::holds_alternative<typename List<unsigned int>::Nil>(
                     _loop_l->v())) {
        if (_last) {
          std::get<typename List<unsigned int>::Cons>(_last->v_mut()).d_a1 =
              List<unsigned int>::nil();
        } else {
          _head = List<unsigned int>::nil();
        }
        _continue = false;
      } else {
        const auto &_m =
            *std::get_if<typename List<unsigned int>::Cons>(&_loop_l->v());
        auto _cell = List<unsigned int>::cons(_m.d_a0, nullptr);
        if (_last) {
          std::get<typename List<unsigned int>::Cons>(_last->v_mut()).d_a1 =
              _cell;
        } else {
          _head = _cell;
        }
        _last = _cell;
        std::shared_ptr<List<unsigned int>> _next_l = filter_impl(
            [=](const unsigned int y) mutable {
              return !((_m.d_a0 ? y % _m.d_a0 : y) == 0u);
            },
            _m.d_a1);
        unsigned int _next_fuel = f;
        _loop_l = std::move(_next_l);
        _loop_fuel = std::move(_next_fuel);
        continue;
      }
    }
  }
  return _head;
}

std::shared_ptr<List<unsigned int>>
LoopifySearch::sieve(const std::shared_ptr<List<unsigned int>> &l) {
  return sieve_fuel(len_impl<unsigned int>(l), l);
}

/// Helper: check if element is in list.
__attribute__((pure)) bool
LoopifySearch::elem_impl(const unsigned int x,
                         const std::shared_ptr<List<unsigned int>> &l) {
  bool _result;
  std::shared_ptr<List<unsigned int>> _loop_l = l;
  bool _continue = true;
  while (_continue) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(
            _loop_l->v())) {
      _result = false;
      _continue = false;
    } else {
      const auto &_m =
          *std::get_if<typename List<unsigned int>::Cons>(&_loop_l->v());
      if (x == _m.d_a0) {
        _result = true;
        _continue = false;
      } else {
        _loop_l = _m.d_a1;
      }
    }
  }
  return _result;
}

/// nub l removes duplicates from list.
std::shared_ptr<List<unsigned int>>
LoopifySearch::nub_fuel(const unsigned int fuel,
                        std::shared_ptr<List<unsigned int>> l) {
  std::shared_ptr<List<unsigned int>> _head{};
  std::shared_ptr<List<unsigned int>> _last{};
  std::shared_ptr<List<unsigned int>> _loop_l = l;
  unsigned int _loop_fuel = fuel;
  bool _continue = true;
  while (_continue) {
    if (_loop_fuel <= 0) {
      if (_last) {
        std::get<typename List<unsigned int>::Cons>(_last->v_mut()).d_a1 =
            std::move(_loop_l);
      } else {
        _head = std::move(_loop_l);
      }
      _continue = false;
    } else {
      unsigned int f = _loop_fuel - 1;
      if (std::holds_alternative<typename List<unsigned int>::Nil>(
              _loop_l->v()) &&
          _loop_l.use_count() == 1) {
        if (_last) {
          std::get<typename List<unsigned int>::Cons>(_last->v_mut()).d_a1 =
              _loop_l;
        } else {
          _head = _loop_l;
        }
        _continue = false;
      } else if (std::holds_alternative<typename List<unsigned int>::Nil>(
                     _loop_l->v())) {
        if (_last) {
          std::get<typename List<unsigned int>::Cons>(_last->v_mut()).d_a1 =
              List<unsigned int>::nil();
        } else {
          _head = List<unsigned int>::nil();
        }
        _continue = false;
      } else {
        const auto &_m =
            *std::get_if<typename List<unsigned int>::Cons>(&_loop_l->v());
        if (elem_impl(_m.d_a0, _m.d_a1)) {
          std::shared_ptr<List<unsigned int>> _next_l = _m.d_a1;
          unsigned int _next_fuel = f;
          _loop_l = std::move(_next_l);
          _loop_fuel = std::move(_next_fuel);
          continue;
        } else {
          auto _cell = List<unsigned int>::cons(_m.d_a0, nullptr);
          if (_last) {
            std::get<typename List<unsigned int>::Cons>(_last->v_mut()).d_a1 =
                _cell;
          } else {
            _head = _cell;
          }
          _last = _cell;
          std::shared_ptr<List<unsigned int>> _next_l = _m.d_a1;
          unsigned int _next_fuel = f;
          _loop_l = std::move(_next_l);
          _loop_fuel = std::move(_next_fuel);
          continue;
        }
      }
    }
  }
  return _head;
}

std::shared_ptr<List<unsigned int>>
LoopifySearch::nub(const std::shared_ptr<List<unsigned int>> &l) {
  return nub_fuel(len_impl<unsigned int>(l), l);
}

/// remove_duplicates l removes all duplicate elements.
std::shared_ptr<List<unsigned int>>
LoopifySearch::remove_duplicates_fuel(const unsigned int fuel,
                                      std::shared_ptr<List<unsigned int>> l) {
  std::shared_ptr<List<unsigned int>> _head{};
  std::shared_ptr<List<unsigned int>> _last{};
  std::shared_ptr<List<unsigned int>> _loop_l = l;
  unsigned int _loop_fuel = fuel;
  bool _continue = true;
  while (_continue) {
    if (_loop_fuel <= 0) {
      if (_last) {
        std::get<typename List<unsigned int>::Cons>(_last->v_mut()).d_a1 =
            std::move(_loop_l);
      } else {
        _head = std::move(_loop_l);
      }
      _continue = false;
    } else {
      unsigned int f = _loop_fuel - 1;
      if (std::holds_alternative<typename List<unsigned int>::Nil>(
              _loop_l->v()) &&
          _loop_l.use_count() == 1) {
        if (_last) {
          std::get<typename List<unsigned int>::Cons>(_last->v_mut()).d_a1 =
              _loop_l;
        } else {
          _head = _loop_l;
        }
        _continue = false;
      } else if (std::holds_alternative<typename List<unsigned int>::Nil>(
                     _loop_l->v())) {
        if (_last) {
          std::get<typename List<unsigned int>::Cons>(_last->v_mut()).d_a1 =
              List<unsigned int>::nil();
        } else {
          _head = List<unsigned int>::nil();
        }
        _continue = false;
      } else {
        const auto &_m =
            *std::get_if<typename List<unsigned int>::Cons>(&_loop_l->v());
        if (elem_impl(_m.d_a0, _m.d_a1)) {
          std::shared_ptr<List<unsigned int>> _next_l = _m.d_a1;
          unsigned int _next_fuel = f;
          _loop_l = std::move(_next_l);
          _loop_fuel = std::move(_next_fuel);
          continue;
        } else {
          auto _cell = List<unsigned int>::cons(_m.d_a0, nullptr);
          if (_last) {
            std::get<typename List<unsigned int>::Cons>(_last->v_mut()).d_a1 =
                _cell;
          } else {
            _head = _cell;
          }
          _last = _cell;
          std::shared_ptr<List<unsigned int>> _next_l = filter_impl(
              [=](const unsigned int y) mutable { return !(_m.d_a0 == y); },
              _m.d_a1);
          unsigned int _next_fuel = f;
          _loop_l = std::move(_next_l);
          _loop_fuel = std::move(_next_fuel);
          continue;
        }
      }
    }
  }
  return _head;
}

std::shared_ptr<List<unsigned int>>
LoopifySearch::remove_duplicates(const std::shared_ptr<List<unsigned int>> &l) {
  return remove_duplicates_fuel(len_impl<unsigned int>(l), l);
}

/// quicksort l sorts list using quicksort with filter-based partitioning.
std::shared_ptr<List<unsigned int>>
LoopifySearch::quicksort_fuel(const unsigned int fuel,
                              std::shared_ptr<List<unsigned int>> l) {
  struct _Enter {
    std::shared_ptr<List<unsigned int>> l;
    const unsigned int fuel;
  };

  struct _Call1 {
    std::shared_ptr<List<unsigned int>> _s0;
    unsigned int _s1;
    decltype(std::declval<typename List<unsigned int>::Cons &>().d_a0) _s2;
  };

  struct _Call2 {
    std::shared_ptr<List<unsigned int>> _s0;
    decltype(std::declval<typename List<unsigned int>::Cons &>().d_a0) _s1;
  };

  using _Frame = std::variant<_Enter, _Call1, _Call2>;
  std::shared_ptr<List<unsigned int>> _result{};
  std::vector<_Frame> _stack;
  _stack.emplace_back(_Enter{l, fuel});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      const auto &_f = std::get<_Enter>(_frame);
      std::shared_ptr<List<unsigned int>> l = _f.l;
      const unsigned int fuel = _f.fuel;
      if (fuel <= 0) {
        _result = std::move(l);
      } else {
        unsigned int f = fuel - 1;
        if (std::holds_alternative<typename List<unsigned int>::Nil>(l->v()) &&
            l.use_count() == 1) {
          _result = l;
        } else if (std::holds_alternative<typename List<unsigned int>::Nil>(
                       l->v())) {
          _result = List<unsigned int>::nil();
        } else {
          const auto &_m =
              *std::get_if<typename List<unsigned int>::Cons>(&l->v());
          std::shared_ptr<List<unsigned int>> smaller = filter_impl(
              [=](const unsigned int y) mutable { return y < _m.d_a0; },
              _m.d_a1);
          std::shared_ptr<List<unsigned int>> greater = filter_impl(
              [=](const unsigned int y) mutable { return _m.d_a0 <= y; },
              _m.d_a1);
          _stack.emplace_back(_Call1{std::move(smaller), f, _m.d_a0});
          _stack.emplace_back(_Enter{greater, f});
        }
      }
    } else if (std::holds_alternative<_Call1>(_frame)) {
      const auto &_f = std::get<_Call1>(_frame);
      _stack.emplace_back(_Call2{_result, _f._s2});
      _stack.emplace_back(_Enter{_f._s0, _f._s1});
    } else {
      const auto &_f = std::get<_Call2>(_frame);
      _result = _result->app(List<unsigned int>::cons(_f._s1, _f._s0));
    }
  }
  return _result;
}

std::shared_ptr<List<unsigned int>>
LoopifySearch::quicksort(const std::shared_ptr<List<unsigned int>> &l) {
  return quicksort_fuel(len_impl<unsigned int>(l), l);
}

/// Helper: split list into two roughly equal parts.
__attribute__((pure)) std::pair<std::shared_ptr<List<unsigned int>>,
                                std::shared_ptr<List<unsigned int>>>
LoopifySearch::split_list(const std::shared_ptr<List<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<List<unsigned int>> l;
  };

  struct _Call1 {
    const typename List<unsigned int>::Cons _s0;
    const typename List<unsigned int>::Cons _s1;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::pair<std::shared_ptr<List<unsigned int>>,
            std::shared_ptr<List<unsigned int>>>
      _result{};
  std::vector<_Frame> _stack;
  _stack.emplace_back(_Enter{l});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      const auto &_f = std::get<_Enter>(_frame);
      const std::shared_ptr<List<unsigned int>> l = _f.l;
      if (std::holds_alternative<typename List<unsigned int>::Nil>(l->v())) {
        _result = std::make_pair(List<unsigned int>::nil(),
                                 List<unsigned int>::nil());
      } else {
        const auto &_m =
            *std::get_if<typename List<unsigned int>::Cons>(&l->v());
        auto &&_sv0 = _m.d_a1;
        if (std::holds_alternative<typename List<unsigned int>::Nil>(
                _sv0->v())) {
          _result = std::make_pair(
              List<unsigned int>::cons(_m.d_a0, List<unsigned int>::nil()),
              List<unsigned int>::nil());
        } else {
          const auto &_m0 =
              *std::get_if<typename List<unsigned int>::Cons>(&_sv0->v());
          _stack.emplace_back(_Call1{_m0, _m});
          _stack.emplace_back(_Enter{_m0.d_a1});
        }
      }
    } else {
      const auto &_f = std::get<_Call1>(_frame);
      const typename List<unsigned int>::Cons _m0 = _f._s0;
      const typename List<unsigned int>::Cons _m = _f._s1;
      const std::shared_ptr<List<unsigned int>> &a = _result.first;
      const std::shared_ptr<List<unsigned int>> &b = _result.second;
      _result = std::make_pair(List<unsigned int>::cons(_m.d_a0, a),
                               List<unsigned int>::cons(_m0.d_a0, b));
    }
  }
  return _result;
}

/// Helper: merge two sorted lists with fuel.
std::shared_ptr<List<unsigned int>>
LoopifySearch::merge_sorted_fuel(const unsigned int fuel,
                                 std::shared_ptr<List<unsigned int>> l1,
                                 std::shared_ptr<List<unsigned int>> l2) {
  std::shared_ptr<List<unsigned int>> _head{};
  std::shared_ptr<List<unsigned int>> _last{};
  std::shared_ptr<List<unsigned int>> _loop_l2 = l2;
  std::shared_ptr<List<unsigned int>> _loop_l1 = l1;
  unsigned int _loop_fuel = fuel;
  bool _continue = true;
  while (_continue) {
    if (_loop_fuel <= 0) {
      if (_last) {
        std::get<typename List<unsigned int>::Cons>(_last->v_mut()).d_a1 =
            std::move(_loop_l1)->app(std::move(_loop_l2));
      } else {
        _head = std::move(_loop_l1)->app(std::move(_loop_l2));
      }
      _continue = false;
    } else {
      unsigned int f = _loop_fuel - 1;
      if (std::holds_alternative<typename List<unsigned int>::Nil>(
              _loop_l1->v())) {
        if (_last) {
          std::get<typename List<unsigned int>::Cons>(_last->v_mut()).d_a1 =
              std::move(_loop_l2);
        } else {
          _head = std::move(_loop_l2);
        }
        _continue = false;
      } else {
        const auto &_m =
            *std::get_if<typename List<unsigned int>::Cons>(&_loop_l1->v());
        if (std::holds_alternative<typename List<unsigned int>::Nil>(
                _loop_l2->v())) {
          if (_last) {
            std::get<typename List<unsigned int>::Cons>(_last->v_mut()).d_a1 =
                std::move(_loop_l1);
          } else {
            _head = std::move(_loop_l1);
          }
          _continue = false;
        } else {
          const auto &_m0 =
              *std::get_if<typename List<unsigned int>::Cons>(&_loop_l2->v());
          if (_m.d_a0 <= _m0.d_a0) {
            auto _cell = List<unsigned int>::cons(_m.d_a0, nullptr);
            if (_last) {
              std::get<typename List<unsigned int>::Cons>(_last->v_mut()).d_a1 =
                  _cell;
            } else {
              _head = _cell;
            }
            _last = _cell;
            std::shared_ptr<List<unsigned int>> _next_l1 = _m.d_a1;
            unsigned int _next_fuel = f;
            _loop_l1 = std::move(_next_l1);
            _loop_fuel = std::move(_next_fuel);
            continue;
          } else {
            auto _cell = List<unsigned int>::cons(_m0.d_a0, nullptr);
            if (_last) {
              std::get<typename List<unsigned int>::Cons>(_last->v_mut()).d_a1 =
                  _cell;
            } else {
              _head = _cell;
            }
            _last = _cell;
            std::shared_ptr<List<unsigned int>> _next_l2 = _m0.d_a1;
            unsigned int _next_fuel = f;
            _loop_l2 = std::move(_next_l2);
            _loop_fuel = std::move(_next_fuel);
            continue;
          }
        }
      }
    }
  }
  return _head;
}

std::shared_ptr<List<unsigned int>>
LoopifySearch::merge_sorted(const std::shared_ptr<List<unsigned int>> &l1,
                            const std::shared_ptr<List<unsigned int>> &l2) {
  return merge_sorted_fuel(
      (len_impl<unsigned int>(l1) + len_impl<unsigned int>(l2)), l1, l2);
}

/// merge_sort l sorts list using merge sort.
std::shared_ptr<List<unsigned int>>
LoopifySearch::merge_sort_fuel(const unsigned int fuel,
                               std::shared_ptr<List<unsigned int>> l) {
  struct _Enter {
    std::shared_ptr<List<unsigned int>> l;
    const unsigned int fuel;
  };

  struct _Call1 {
    std::shared_ptr<List<unsigned int>> _s0;
    unsigned int _s1;
  };

  struct _Call2 {
    std::shared_ptr<List<unsigned int>> _s0;
  };

  using _Frame = std::variant<_Enter, _Call1, _Call2>;
  std::shared_ptr<List<unsigned int>> _result{};
  std::vector<_Frame> _stack;
  _stack.emplace_back(_Enter{l, fuel});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      const auto &_f = std::get<_Enter>(_frame);
      std::shared_ptr<List<unsigned int>> l = _f.l;
      const unsigned int fuel = _f.fuel;
      if (fuel <= 0) {
        _result = std::move(l);
      } else {
        unsigned int f = fuel - 1;
        if (std::holds_alternative<typename List<unsigned int>::Nil>(l->v()) &&
            l.use_count() == 1) {
          _result = l;
        } else if (std::holds_alternative<typename List<unsigned int>::Nil>(
                       l->v())) {
          _result = List<unsigned int>::nil();
        } else {
          const auto &_m =
              *std::get_if<typename List<unsigned int>::Cons>(&l->v());
          auto &&_sv = _m.d_a1;
          if (std::holds_alternative<typename List<unsigned int>::Nil>(
                  _sv->v())) {
            _result = std::move(l);
          } else {
            auto _cs = split_list(l);
            const std::shared_ptr<List<unsigned int>> &a = _cs.first;
            const std::shared_ptr<List<unsigned int>> &b = _cs.second;
            _stack.emplace_back(_Call1{a, f});
            _stack.emplace_back(_Enter{b, f});
          }
        }
      }
    } else if (std::holds_alternative<_Call1>(_frame)) {
      const auto &_f = std::get<_Call1>(_frame);
      _stack.emplace_back(_Call2{_result});
      _stack.emplace_back(_Enter{_f._s0, _f._s1});
    } else {
      const auto &_f = std::get<_Call2>(_frame);
      _result = merge_sorted(_result, _f._s0);
    }
  }
  return _result;
}

std::shared_ptr<List<unsigned int>>
LoopifySearch::merge_sort(const std::shared_ptr<List<unsigned int>> &l) {
  return merge_sort_fuel(len_impl<unsigned int>(l), l);
}

/// Helper: remove first occurrence of x from list.
std::shared_ptr<List<unsigned int>>
LoopifySearch::remove_first(const unsigned int x,
                            const std::shared_ptr<List<unsigned int>> &l) {
  std::shared_ptr<List<unsigned int>> _head{};
  std::shared_ptr<List<unsigned int>> _last{};
  std::shared_ptr<List<unsigned int>> _loop_l = l;
  bool _continue = true;
  while (_continue) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(
            _loop_l->v())) {
      if (_last) {
        std::get<typename List<unsigned int>::Cons>(_last->v_mut()).d_a1 =
            List<unsigned int>::nil();
      } else {
        _head = List<unsigned int>::nil();
      }
      _continue = false;
    } else {
      const auto &_m =
          *std::get_if<typename List<unsigned int>::Cons>(&_loop_l->v());
      if (x == _m.d_a0) {
        if (_last) {
          std::get<typename List<unsigned int>::Cons>(_last->v_mut()).d_a1 =
              _m.d_a1;
        } else {
          _head = _m.d_a1;
        }
        _continue = false;
      } else {
        auto _cell = List<unsigned int>::cons(_m.d_a0, nullptr);
        if (_last) {
          std::get<typename List<unsigned int>::Cons>(_last->v_mut()).d_a1 =
              _cell;
        } else {
          _head = _cell;
        }
        _last = _cell;
        _loop_l = _m.d_a1;
        continue;
      }
    }
  }
  return _head;
}

/// Helper: map function that prepends element to each list.
std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>
LoopifySearch::map_cons(
    const unsigned int x,
    const std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> &lsts) {
  std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> _head{};
  std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> _last{};
  std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> _loop_lsts = lsts;
  bool _continue = true;
  while (_continue) {
    if (std::holds_alternative<
            typename List<std::shared_ptr<List<unsigned int>>>::Nil>(
            _loop_lsts->v())) {
      if (_last) {
        std::get<typename List<std::shared_ptr<List<unsigned int>>>::Cons>(
            _last->v_mut())
            .d_a1 = List<std::shared_ptr<List<unsigned int>>>::nil();
      } else {
        _head = List<std::shared_ptr<List<unsigned int>>>::nil();
      }
      _continue = false;
    } else {
      const auto &_m = *std::get_if<
          typename List<std::shared_ptr<List<unsigned int>>>::Cons>(
          &_loop_lsts->v());
      auto _cell = List<std::shared_ptr<List<unsigned int>>>::cons(
          List<unsigned int>::cons(x, _m.d_a0), nullptr);
      if (_last) {
        std::get<typename List<std::shared_ptr<List<unsigned int>>>::Cons>(
            _last->v_mut())
            .d_a1 = _cell;
      } else {
        _head = _cell;
      }
      _last = _cell;
      _loop_lsts = _m.d_a1;
      continue;
    }
  }
  return _head;
}

/// perms_choices_fuel fuel choices orig generates permutations by iterating
/// over choices.  Single self-recursive function for full loopification.
/// Match on remaining is hoisted out of let-binding.
std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>
LoopifySearch::perms_choices_fuel(
    const unsigned int fuel, const std::shared_ptr<List<unsigned int>> &choices,
    const std::shared_ptr<List<unsigned int>> &orig) {
  struct _Enter {
    const std::shared_ptr<List<unsigned int>> orig;
    const std::shared_ptr<List<unsigned int>> choices;
    const unsigned int fuel;
  };

  struct _Call1 {
    decltype(map_cons(
        std::declval<typename List<unsigned int>::Cons &>().d_a0,
        List<std::shared_ptr<List<unsigned int>>>::cons(
            List<unsigned int>::nil(),
            List<std::shared_ptr<List<unsigned int>>>::nil()))) _s0;
  };

  struct _Call2 {
    std::shared_ptr<List<unsigned int>> _s0;
    std::shared_ptr<List<unsigned int>> _s1;
    unsigned int _s2;
    decltype(std::declval<typename List<unsigned int>::Cons &>().d_a0) _s3;
  };

  struct _Call3 {
    std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> _s0;
    decltype(std::declval<typename List<unsigned int>::Cons &>().d_a0) _s1;
  };

  using _Frame = std::variant<_Enter, _Call1, _Call2, _Call3>;
  std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> _result{};
  std::vector<_Frame> _stack;
  _stack.emplace_back(_Enter{orig, choices, fuel});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      const auto &_f = std::get<_Enter>(_frame);
      const std::shared_ptr<List<unsigned int>> orig = _f.orig;
      const std::shared_ptr<List<unsigned int>> choices = _f.choices;
      const unsigned int fuel = _f.fuel;
      if (fuel <= 0) {
        _result = List<std::shared_ptr<List<unsigned int>>>::nil();
      } else {
        unsigned int f = fuel - 1;
        if (std::holds_alternative<typename List<unsigned int>::Nil>(
                choices->v())) {
          _result = List<std::shared_ptr<List<unsigned int>>>::nil();
        } else {
          const auto &_m =
              *std::get_if<typename List<unsigned int>::Cons>(&choices->v());
          std::shared_ptr<List<unsigned int>> remaining =
              remove_first(_m.d_a0, orig);
          if (std::holds_alternative<typename List<unsigned int>::Nil>(
                  remaining->v())) {
            _stack.emplace_back(_Call1{map_cons(
                _m.d_a0,
                List<std::shared_ptr<List<unsigned int>>>::cons(
                    List<unsigned int>::nil(),
                    List<std::shared_ptr<List<unsigned int>>>::nil()))});
            _stack.emplace_back(_Enter{orig, _m.d_a1, f});
          } else {
            _stack.emplace_back(_Call2{remaining, remaining, f, _m.d_a0});
            _stack.emplace_back(_Enter{orig, _m.d_a1, f});
          }
        }
      }
    } else if (std::holds_alternative<_Call1>(_frame)) {
      const auto &_f = std::get<_Call1>(_frame);
      _result = _f._s0->app(_result);
    } else if (std::holds_alternative<_Call2>(_frame)) {
      const auto &_f = std::get<_Call2>(_frame);
      _stack.emplace_back(_Call3{_result, _f._s3});
      _stack.emplace_back(_Enter{_f._s0, _f._s1, _f._s2});
    } else {
      const auto &_f = std::get<_Call3>(_frame);
      _result = map_cons(_f._s1, _result)->app(_f._s0);
    }
  }
  return _result;
}

/// permutations_fuel fuel l generates all permutations of list.
std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>
LoopifySearch::permutations_fuel(const unsigned int fuel,
                                 const std::shared_ptr<List<unsigned int>> &l) {
  if (std::holds_alternative<typename List<unsigned int>::Nil>(l->v())) {
    return List<std::shared_ptr<List<unsigned int>>>::cons(
        List<unsigned int>::nil(),
        List<std::shared_ptr<List<unsigned int>>>::nil());
  } else {
    return perms_choices_fuel(fuel, l, l);
  }
}

std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>
LoopifySearch::permutations(const std::shared_ptr<List<unsigned int>> &l) {
  return permutations_fuel((len_impl<unsigned int>(l) + 1), l);
}

/// linear_search x l finds index of first occurrence of x.
__attribute__((pure)) std::optional<unsigned int>
LoopifySearch::linear_search_aux(const unsigned int x,
                                 const std::shared_ptr<List<unsigned int>> &l,
                                 const unsigned int idx) {
  std::optional<unsigned int> _result;
  unsigned int _loop_idx = idx;
  std::shared_ptr<List<unsigned int>> _loop_l = l;
  bool _continue = true;
  while (_continue) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(
            _loop_l->v())) {
      _result = std::optional<unsigned int>();
      _continue = false;
    } else {
      const auto &_m =
          *std::get_if<typename List<unsigned int>::Cons>(&_loop_l->v());
      if (x == _m.d_a0) {
        _result = std::make_optional<unsigned int>(_loop_idx);
        _continue = false;
      } else {
        unsigned int _next_idx = (_loop_idx + 1);
        std::shared_ptr<List<unsigned int>> _next_l = _m.d_a1;
        _loop_idx = std::move(_next_idx);
        _loop_l = std::move(_next_l);
      }
    }
  }
  return _result;
}

__attribute__((pure)) std::optional<unsigned int>
LoopifySearch::linear_search(const unsigned int x,
                             const std::shared_ptr<List<unsigned int>> &l) {
  return linear_search_aux(x, l, 0u);
}

/// all_indices x l finds all indices where x occurs.
std::shared_ptr<List<unsigned int>>
LoopifySearch::all_indices_aux(const unsigned int x,
                               const std::shared_ptr<List<unsigned int>> &l,
                               const unsigned int idx) {
  std::shared_ptr<List<unsigned int>> _head{};
  std::shared_ptr<List<unsigned int>> _last{};
  unsigned int _loop_idx = idx;
  std::shared_ptr<List<unsigned int>> _loop_l = l;
  bool _continue = true;
  while (_continue) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(
            _loop_l->v())) {
      if (_last) {
        std::get<typename List<unsigned int>::Cons>(_last->v_mut()).d_a1 =
            List<unsigned int>::nil();
      } else {
        _head = List<unsigned int>::nil();
      }
      _continue = false;
    } else {
      const auto &_m =
          *std::get_if<typename List<unsigned int>::Cons>(&_loop_l->v());
      if (x == _m.d_a0) {
        auto _cell = List<unsigned int>::cons(_loop_idx, nullptr);
        if (_last) {
          std::get<typename List<unsigned int>::Cons>(_last->v_mut()).d_a1 =
              _cell;
        } else {
          _head = _cell;
        }
        _last = _cell;
        unsigned int _next_idx = (_loop_idx + 1);
        std::shared_ptr<List<unsigned int>> _next_l = _m.d_a1;
        _loop_idx = std::move(_next_idx);
        _loop_l = std::move(_next_l);
        continue;
      } else {
        unsigned int _next_idx = (_loop_idx + 1);
        std::shared_ptr<List<unsigned int>> _next_l = _m.d_a1;
        _loop_idx = std::move(_next_idx);
        _loop_l = std::move(_next_l);
        continue;
      }
    }
  }
  return _head;
}

std::shared_ptr<List<unsigned int>>
LoopifySearch::all_indices(const unsigned int x,
                           const std::shared_ptr<List<unsigned int>> &l) {
  return all_indices_aux(x, l, 0u);
}

/// min_element l finds minimum element in list.
__attribute__((pure)) unsigned int
LoopifySearch::min_element(const std::shared_ptr<List<unsigned int>> &l) {
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
      if (_m.d_a0 <= min_rest) {
        _result = _m.d_a0;
      } else {
        _result = min_rest;
      }
    }
  }
  return _result;
}
