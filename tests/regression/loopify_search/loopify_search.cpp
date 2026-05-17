#include "loopify_search.h"

/// Consolidated search and optimization algorithms.
/// knapsack capacity items solves 0/1 knapsack problem.
/// Items are (weight, value) pairs.
uint64_t
LoopifySearch::knapsack_fuel(uint64_t fuel, uint64_t capacity,
                             const List<std::pair<uint64_t, uint64_t>> &items) {
  if (fuel <= 0) {
    return UINT64_C(0);
  } else {
    uint64_t f = fuel - 1;
    if (std::holds_alternative<
            typename List<std::pair<uint64_t, uint64_t>>::Nil>(items.v())) {
      return UINT64_C(0);
    } else {
      const auto &[a0, a1] =
          std::get<typename List<std::pair<uint64_t, uint64_t>>::Cons>(
              items.v());
      const uint64_t &weight = a0.first;
      const uint64_t &value = a0.second;
      if (capacity < weight) {
        return knapsack_fuel(f, capacity, *a1);
      } else {
        if (knapsack_fuel(f, capacity, *a1) <=
            (value +
             knapsack_fuel(
                 f,
                 (((capacity - weight) > capacity ? 0 : (capacity - weight))),
                 *a1))) {
          return (value + knapsack_fuel(f,
                                        (((capacity - weight) > capacity
                                              ? 0
                                              : (capacity - weight))),
                                        *a1));
        } else {
          return knapsack_fuel(f, capacity, *a1);
        }
      }
    }
  }
}

uint64_t
LoopifySearch::knapsack(uint64_t capacity,
                        const List<std::pair<uint64_t, uint64_t>> &items) {
  return knapsack_fuel(len_impl<std::pair<uint64_t, uint64_t>>(items), capacity,
                       items);
}

/// majority l finds majority element using Boyer-Moore algorithm.
/// Returns (candidate, count).
std::pair<uint64_t, uint64_t> LoopifySearch::majority(
    const List<uint64_t>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<uint64_t> *l;
  };

  /// _Cont_Cons: saves [a0], resumes after recursive call, then processes rest.
  struct _Cont_Cons {
    uint64_t a0;
  };

  using _Frame = std::variant<_Enter, _Cont_Cons>;
  std::pair<uint64_t, uint64_t> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l});
  /// Loopified majority: _Enter -> _Cont_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<uint64_t> &l = *_f.l;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
        _result = std::make_pair(UINT64_C(0), UINT64_C(0));
      } else {
        const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
        _stack.emplace_back(_Cont_Cons{a0});
        _stack.emplace_back(_Enter{a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Cont_Cons>(_frame));
      uint64_t a0 = _f.a0;
      const uint64_t &cand = _result.first;
      const uint64_t &count = _result.second;
      if (a0 == cand) {
        _result = std::make_pair(cand, (count + 1));
      } else {
        if (UINT64_C(0) < count) {
          _result = std::make_pair(
              cand,
              (((count - UINT64_C(1)) > count ? 0 : (count - UINT64_C(1)))));
        } else {
          _result = std::make_pair(a0, UINT64_C(1));
        }
      }
    }
  }
  return _result;
}

/// longest_increasing_subseq l finds a longest increasing subsequence (greedy).
List<uint64_t>
LoopifySearch::longest_increasing_subseq(const List<uint64_t> &l) {
  std::unique_ptr<List<uint64_t>> _head{};
  std::unique_ptr<List<uint64_t>> *_write = &_head;
  const List<uint64_t> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l->v())) {
      *_write = std::make_unique<List<uint64_t>>(List<uint64_t>::nil());
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename List<uint64_t>::Cons>(_loop_l->v());
      auto &&_sv0 = *a1;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(_sv0.v())) {
        *_write = std::make_unique<List<uint64_t>>(
            List<uint64_t>::cons(a0, List<uint64_t>::nil()));
        break;
      } else {
        const auto &[a00, a10] =
            std::get<typename List<uint64_t>::Cons>(_sv0.v());
        if (a0 < a00) {
          auto _cell = std::make_unique<List<uint64_t>>(
              typename List<uint64_t>::Cons(a0, nullptr));
          *_write = std::move(_cell);
          _write =
              &std::get<typename List<uint64_t>::Cons>((*_write)->v_mut()).a1;
          _loop_l = a1.get();
          continue;
        } else {
          _loop_l = a1.get();
          continue;
        }
      }
    }
  }
  return std::move(*_head);
}

/// Helper for binary search: get nth element.
uint64_t LoopifySearch::nth_impl(uint64_t n, const List<uint64_t> &l) {
  const List<uint64_t> *_loop_l = &l;
  uint64_t _loop_n = std::move(n);
  while (true) {
    if (_loop_n <= 0) {
      if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l->v())) {
        return UINT64_C(0);
      } else {
        const auto &[a0, a1] =
            std::get<typename List<uint64_t>::Cons>(_loop_l->v());
        return a0;
      }
    } else {
      uint64_t m = _loop_n - 1;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l->v())) {
        return UINT64_C(0);
      } else {
        const auto &[a00, a10] =
            std::get<typename List<uint64_t>::Cons>(_loop_l->v());
        _loop_l = a10.get();
        _loop_n = m;
      }
    }
  }
}

/// Helper for binary search: take first k elements.
List<uint64_t> LoopifySearch::take_impl(uint64_t k, const List<uint64_t> &l) {
  std::unique_ptr<List<uint64_t>> _head{};
  std::unique_ptr<List<uint64_t>> *_write = &_head;
  const List<uint64_t> *_loop_l = &l;
  uint64_t _loop_k = std::move(k);
  while (true) {
    if (_loop_k <= 0) {
      *_write = std::make_unique<List<uint64_t>>(List<uint64_t>::nil());
      break;
    } else {
      uint64_t m = _loop_k - 1;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l->v())) {
        *_write = std::make_unique<List<uint64_t>>(List<uint64_t>::nil());
        break;
      } else {
        const auto &[a0, a1] =
            std::get<typename List<uint64_t>::Cons>(_loop_l->v());
        auto _cell = std::make_unique<List<uint64_t>>(
            typename List<uint64_t>::Cons(a0, nullptr));
        *_write = std::move(_cell);
        _write =
            &std::get<typename List<uint64_t>::Cons>((*_write)->v_mut()).a1;
        _loop_l = a1.get();
        _loop_k = m;
        continue;
      }
    }
  }
  return std::move(*_head);
}

/// Helper for binary search: drop first k elements.
List<uint64_t> LoopifySearch::drop_impl(uint64_t k, List<uint64_t> l) {
  List<uint64_t> _loop_l = std::move(l);
  uint64_t _loop_k = std::move(k);
  while (true) {
    if (_loop_k <= 0) {
      return _loop_l;
    } else {
      uint64_t m = _loop_k - 1;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(
              _loop_l.v_mut())) {
        return List<uint64_t>::nil();
      } else {
        auto &[a0, a1] =
            std::get<typename List<uint64_t>::Cons>(_loop_l.v_mut());
        _loop_l = std::move(*a1);
        _loop_k = m;
      }
    }
  }
}

/// binary_search_fuel target sorted_list searches for target in sorted list.
/// Returns true if found.
bool LoopifySearch::binary_search_fuel(uint64_t fuel, uint64_t target,
                                       const List<uint64_t> &l) {
  List<uint64_t> _loop_l = l;
  uint64_t _loop_fuel = std::move(fuel);
  while (true) {
    if (_loop_fuel <= 0) {
      return false;
    } else {
      uint64_t f = _loop_fuel - 1;
      uint64_t n = len_impl<uint64_t>(_loop_l);
      if (n <= 0) {
        return false;
      } else {
        uint64_t _x = n - 1;
        uint64_t mid = (UINT64_C(2) ? n / UINT64_C(2) : 0);
        uint64_t mid_val = nth_impl(mid, _loop_l);
        if (target == mid_val) {
          return true;
        } else {
          if (target < mid_val) {
            _loop_l = take_impl(mid, _loop_l);
            _loop_fuel = f;
          } else {
            _loop_l = drop_impl((mid + 1), _loop_l);
            _loop_fuel = f;
          }
        }
      }
    }
  }
}

bool LoopifySearch::binary_search(uint64_t target, const List<uint64_t> &l) {
  return binary_search_fuel(len_impl<uint64_t>(l), target, l);
}

/// longest_run l finds the longest run of consecutive equal elements.
List<uint64_t> LoopifySearch::longest_run_aux(List<uint64_t> current_run,
                                              List<uint64_t> best_run,
                                              const List<uint64_t> &l) {
  const List<uint64_t> *_loop_l = &l;
  List<uint64_t> _loop_best_run = std::move(best_run);
  List<uint64_t> _loop_current_run = std::move(current_run);
  while (true) {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l->v())) {
      if (len_impl<uint64_t>(_loop_current_run) <=
          len_impl<uint64_t>(_loop_best_run)) {
        return _loop_best_run;
      } else {
        return _loop_current_run;
      }
    } else {
      const auto &[a0, a1] =
          std::get<typename List<uint64_t>::Cons>(_loop_l->v());
      auto &&_sv0 = *a1;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(_sv0.v())) {
        List<uint64_t> new_run =
            List<uint64_t>::cons(a0, std::move(_loop_current_run));
        if (len_impl<uint64_t>(new_run) <= len_impl<uint64_t>(_loop_best_run)) {
          return _loop_best_run;
        } else {
          return new_run;
        }
      } else {
        const auto &[a00, a10] =
            std::get<typename List<uint64_t>::Cons>(_sv0.v());
        if (a0 == a00) {
          _loop_l = a1.get();
          _loop_current_run =
              List<uint64_t>::cons(a0, std::move(_loop_current_run));
        } else {
          List<uint64_t> new_run =
              List<uint64_t>::cons(a0, std::move(_loop_current_run));
          List<uint64_t> new_best;
          if (len_impl<uint64_t>(new_run) <=
              len_impl<uint64_t>(_loop_best_run)) {
            new_best = _loop_best_run;
          } else {
            new_best = new_run;
          }
          _loop_l = a1.get();
          _loop_best_run = std::move(new_best);
          _loop_current_run = List<uint64_t>::nil();
        }
      }
    }
  }
}

List<uint64_t> LoopifySearch::longest_run(const List<uint64_t> &l) {
  return longest_run_aux(List<uint64_t>::nil(), List<uint64_t>::nil(), l);
}

/// collatz n computes Collatz sequence length (not the list).
uint64_t LoopifySearch::collatz_fuel(
    uint64_t fuel,
    uint64_t
        n) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    uint64_t n;
    uint64_t fuel;
  };

  /// _Resume1: resumes after recursive call with _result.
  struct _Resume1 {};

  /// _Resume2: resumes after recursive call with _result.
  struct _Resume2 {};

  using _Frame = std::variant<_Enter, _Resume1, _Resume2>;
  uint64_t _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{n, fuel});
  /// Loopified collatz_fuel: _Enter -> _Resume1 -> _Resume2.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      uint64_t n = _f.n;
      uint64_t fuel = _f.fuel;
      if (fuel <= 0) {
        _result = UINT64_C(0);
      } else {
        uint64_t f = fuel - 1;
        if (n == UINT64_C(1)) {
          _result = UINT64_C(0);
        } else {
          if ((UINT64_C(2) ? n % UINT64_C(2) : n) == UINT64_C(0)) {
            _stack.emplace_back(_Resume1{});
            _stack.emplace_back(_Enter{(UINT64_C(2) ? n / UINT64_C(2) : 0), f});
          } else {
            _stack.emplace_back(_Resume2{});
            _stack.emplace_back(_Enter{((UINT64_C(3) * n) + UINT64_C(1)), f});
          }
        }
      }
    } else if (std::holds_alternative<_Resume1>(_frame)) {
      auto _f = std::move(std::get<_Resume1>(_frame));
      _result = (_result + 1);
    } else {
      auto _f = std::move(std::get<_Resume2>(_frame));
      _result = (_result + 1);
    }
  }
  return _result;
}

uint64_t LoopifySearch::collatz(uint64_t n) {
  return collatz_fuel(UINT64_C(1000), n);
}

/// lis l simple longest increasing subsequence (greedy approach).
List<uint64_t> LoopifySearch::lis(const List<uint64_t> &l) {
  std::unique_ptr<List<uint64_t>> _head{};
  std::unique_ptr<List<uint64_t>> *_write = &_head;
  const List<uint64_t> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l->v())) {
      *_write = std::make_unique<List<uint64_t>>(List<uint64_t>::nil());
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename List<uint64_t>::Cons>(_loop_l->v());
      auto &&_sv0 = *a1;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(_sv0.v())) {
        *_write = std::make_unique<List<uint64_t>>(
            List<uint64_t>::cons(a0, List<uint64_t>::nil()));
        break;
      } else {
        const auto &[a00, a10] =
            std::get<typename List<uint64_t>::Cons>(_sv0.v());
        if (a0 < a00) {
          auto _cell = std::make_unique<List<uint64_t>>(
              typename List<uint64_t>::Cons(a0, nullptr));
          *_write = std::move(_cell);
          _write =
              &std::get<typename List<uint64_t>::Cons>((*_write)->v_mut()).a1;
          _loop_l = a1.get();
          continue;
        } else {
          _loop_l = a1.get();
          continue;
        }
      }
    }
  }
  return std::move(*_head);
}

/// subset_sum target l checks if any subset sums to target.
bool LoopifySearch::subset_sum_fuel(uint64_t fuel, uint64_t target,
                                    const List<uint64_t> &l) {
  if (fuel <= 0) {
    return false;
  } else {
    uint64_t f = fuel - 1;
    if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
      return target == UINT64_C(0);
    } else {
      const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
      bool without = subset_sum_fuel(f, target, *a1);
      if (without) {
        return true;
      } else {
        if (a0 <= target) {
          return subset_sum_fuel(
              f, (((target - a0) > target ? 0 : (target - a0))), *a1);
        } else {
          return false;
        }
      }
    }
  }
}

bool LoopifySearch::subset_sum(uint64_t target, const List<uint64_t> &l) {
  return subset_sum_fuel((len_impl<uint64_t>(l) + 1), target, l);
}

/// sieve l removes multiples (simplified sieve of Eratosthenes).
List<uint64_t> LoopifySearch::sieve_fuel(uint64_t fuel, List<uint64_t> l) {
  std::unique_ptr<List<uint64_t>> _head{};
  std::unique_ptr<List<uint64_t>> *_write = &_head;
  List<uint64_t> _loop_l = std::move(l);
  uint64_t _loop_fuel = std::move(fuel);
  while (true) {
    if (_loop_fuel <= 0) {
      *_write = std::make_unique<List<uint64_t>>(std::move(_loop_l));
      break;
    } else {
      uint64_t f = _loop_fuel - 1;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(
              _loop_l.v_mut())) {
        *_write = std::make_unique<List<uint64_t>>(List<uint64_t>::nil());
        break;
      } else {
        auto &[a0, a1] =
            std::get<typename List<uint64_t>::Cons>(_loop_l.v_mut());
        const List<uint64_t> &a1_value = *a1;
        auto _cell = std::make_unique<List<uint64_t>>(
            typename List<uint64_t>::Cons(a0, nullptr));
        *_write = std::move(_cell);
        _write =
            &std::get<typename List<uint64_t>::Cons>((*_write)->v_mut()).a1;
        _loop_l = filter_impl(
            [=](uint64_t y) mutable {
              return !((a0 ? y % a0 : y) == UINT64_C(0));
            },
            a1_value);
        _loop_fuel = f;
        continue;
      }
    }
  }
  return std::move(*_head);
}

List<uint64_t> LoopifySearch::sieve(const List<uint64_t> &l) {
  return sieve_fuel(len_impl<uint64_t>(l), l);
}

/// Helper: check if element is in list.
bool LoopifySearch::elem_impl(uint64_t x, const List<uint64_t> &l) {
  const List<uint64_t> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l->v())) {
      return false;
    } else {
      const auto &[a0, a1] =
          std::get<typename List<uint64_t>::Cons>(_loop_l->v());
      if (x == a0) {
        return true;
      } else {
        _loop_l = a1.get();
      }
    }
  }
}

/// nub l removes duplicates from list.
List<uint64_t> LoopifySearch::nub_fuel(uint64_t fuel, List<uint64_t> l) {
  std::unique_ptr<List<uint64_t>> _head{};
  std::unique_ptr<List<uint64_t>> *_write = &_head;
  List<uint64_t> _loop_l = std::move(l);
  uint64_t _loop_fuel = std::move(fuel);
  while (true) {
    if (_loop_fuel <= 0) {
      *_write = std::make_unique<List<uint64_t>>(std::move(_loop_l));
      break;
    } else {
      uint64_t f = _loop_fuel - 1;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(
              _loop_l.v_mut())) {
        *_write = std::make_unique<List<uint64_t>>(List<uint64_t>::nil());
        break;
      } else {
        auto &[a0, a1] =
            std::get<typename List<uint64_t>::Cons>(_loop_l.v_mut());
        if (elem_impl(a0, *a1)) {
          _loop_l = std::move(*a1);
          _loop_fuel = f;
          continue;
        } else {
          auto _cell = std::make_unique<List<uint64_t>>(
              typename List<uint64_t>::Cons(std::move(a0), nullptr));
          *_write = std::move(_cell);
          _write =
              &std::get<typename List<uint64_t>::Cons>((*_write)->v_mut()).a1;
          _loop_l = std::move(*a1);
          _loop_fuel = f;
          continue;
        }
      }
    }
  }
  return std::move(*_head);
}

List<uint64_t> LoopifySearch::nub(const List<uint64_t> &l) {
  return nub_fuel(len_impl<uint64_t>(l), l);
}

/// remove_duplicates l removes all duplicate elements.
List<uint64_t> LoopifySearch::remove_duplicates_fuel(uint64_t fuel,
                                                     List<uint64_t> l) {
  std::unique_ptr<List<uint64_t>> _head{};
  std::unique_ptr<List<uint64_t>> *_write = &_head;
  List<uint64_t> _loop_l = std::move(l);
  uint64_t _loop_fuel = std::move(fuel);
  while (true) {
    if (_loop_fuel <= 0) {
      *_write = std::make_unique<List<uint64_t>>(std::move(_loop_l));
      break;
    } else {
      uint64_t f = _loop_fuel - 1;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(
              _loop_l.v_mut())) {
        *_write = std::make_unique<List<uint64_t>>(List<uint64_t>::nil());
        break;
      } else {
        auto &[a0, a1] =
            std::get<typename List<uint64_t>::Cons>(_loop_l.v_mut());
        const List<uint64_t> &a1_value = *a1;
        if (elem_impl(a0, a1_value)) {
          _loop_l = a1_value;
          _loop_fuel = f;
          continue;
        } else {
          auto _cell = std::make_unique<List<uint64_t>>(
              typename List<uint64_t>::Cons(a0, nullptr));
          *_write = std::move(_cell);
          _write =
              &std::get<typename List<uint64_t>::Cons>((*_write)->v_mut()).a1;
          _loop_l = filter_impl([=](uint64_t y) mutable { return !(a0 == y); },
                                a1_value);
          _loop_fuel = f;
          continue;
        }
      }
    }
  }
  return std::move(*_head);
}

List<uint64_t> LoopifySearch::remove_duplicates(const List<uint64_t> &l) {
  return remove_duplicates_fuel(len_impl<uint64_t>(l), l);
}

/// quicksort l sorts list using quicksort with filter-based partitioning.
List<uint64_t> LoopifySearch::quicksort_fuel(
    uint64_t fuel,
    List<uint64_t>
        l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    List<uint64_t> l;
    uint64_t fuel;
  };

  /// _After_Cons: saves [smaller, f, a0], dispatches next recursive call.
  struct _After_Cons {
    List<uint64_t> smaller;
    uint64_t f;
    uint64_t a0;
  };

  /// _Combine_Cons: receives partial results, combines with _result from final
  /// call.
  struct _Combine_Cons {
    List<uint64_t> _result;
    uint64_t a0;
  };

  using _Frame = std::variant<_Enter, _After_Cons, _Combine_Cons>;
  List<uint64_t> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{l, fuel});
  /// Loopified quicksort_fuel: _Enter -> _After_Cons -> _Combine_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      List<uint64_t> l = std::move(_f.l);
      uint64_t fuel = _f.fuel;
      if (fuel <= 0) {
        _result = std::move(l);
      } else {
        uint64_t f = fuel - 1;
        if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v_mut())) {
          _result = List<uint64_t>::nil();
        } else {
          auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v_mut());
          const List<uint64_t> &a1_value = *a1;
          List<uint64_t> smaller =
              filter_impl([=](uint64_t y) mutable { return y < a0; }, a1_value);
          List<uint64_t> greater = filter_impl(
              [=](uint64_t y) mutable { return a0 <= y; }, a1_value);
          _stack.emplace_back(
              _After_Cons{std::move(smaller), f, std::move(a0)});
          _stack.emplace_back(_Enter{std::move(greater), f});
        }
      }
    } else if (std::holds_alternative<_After_Cons>(_frame)) {
      auto _f = std::move(std::get<_After_Cons>(_frame));
      _stack.emplace_back(_Combine_Cons{std::move(_result), _f.a0});
      _stack.emplace_back(_Enter{std::move(_f.smaller), _f.f});
    } else {
      auto _f = std::move(std::get<_Combine_Cons>(_frame));
      _result = _result.app(List<uint64_t>::cons(_f.a0, _f._result));
    }
  }
  return _result;
}

List<uint64_t> LoopifySearch::quicksort(const List<uint64_t> &l) {
  return quicksort_fuel(len_impl<uint64_t>(l), l);
}

/// Helper: split list into two roughly equal parts.
std::pair<List<uint64_t>, List<uint64_t>> LoopifySearch::split_list(
    const List<uint64_t>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<uint64_t> *l;
  };

  /// _Cont_Cons: saves [a0, a00], resumes after recursive call, then processes
  /// rest.
  struct _Cont_Cons {
    uint64_t a0;
    uint64_t a00;
  };

  using _Frame = std::variant<_Enter, _Cont_Cons>;
  std::pair<List<uint64_t>, List<uint64_t>> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l});
  /// Loopified split_list: _Enter -> _Cont_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<uint64_t> &l = *_f.l;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
        _result = std::make_pair(List<uint64_t>::nil(), List<uint64_t>::nil());
      } else {
        const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
        auto &&_sv0 = *a1;
        if (std::holds_alternative<typename List<uint64_t>::Nil>(_sv0.v())) {
          _result =
              std::make_pair(List<uint64_t>::cons(a0, List<uint64_t>::nil()),
                             List<uint64_t>::nil());
        } else {
          const auto &[a00, a10] =
              std::get<typename List<uint64_t>::Cons>(_sv0.v());
          _stack.emplace_back(_Cont_Cons{a0, a00});
          _stack.emplace_back(_Enter{a10.get()});
        }
      }
    } else {
      auto _f = std::move(std::get<_Cont_Cons>(_frame));
      uint64_t a0 = _f.a0;
      uint64_t a00 = _f.a00;
      const List<uint64_t> &a = _result.first;
      const List<uint64_t> &b = _result.second;
      _result = std::make_pair(List<uint64_t>::cons(a0, a),
                               List<uint64_t>::cons(a00, b));
    }
  }
  return _result;
}

/// Helper: merge two sorted lists with fuel.
List<uint64_t> LoopifySearch::merge_sorted_fuel(uint64_t fuel,
                                                List<uint64_t> l1,
                                                List<uint64_t> l2) {
  std::unique_ptr<List<uint64_t>> _head{};
  std::unique_ptr<List<uint64_t>> *_write = &_head;
  List<uint64_t> _loop_l2 = std::move(l2);
  List<uint64_t> _loop_l1 = std::move(l1);
  uint64_t _loop_fuel = std::move(fuel);
  while (true) {
    if (_loop_fuel <= 0) {
      *_write = std::make_unique<List<uint64_t>>(
          std::move(_loop_l1).app(std::move(_loop_l2)));
      break;
    } else {
      uint64_t f = _loop_fuel - 1;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(
              _loop_l1.v_mut())) {
        *_write = std::make_unique<List<uint64_t>>(std::move(_loop_l2));
        break;
      } else {
        auto &[a0, a1] =
            std::get<typename List<uint64_t>::Cons>(_loop_l1.v_mut());
        if (std::holds_alternative<typename List<uint64_t>::Nil>(
                _loop_l2.v_mut())) {
          *_write = std::make_unique<List<uint64_t>>(_loop_l1);
          break;
        } else {
          auto &[a00, a10] =
              std::get<typename List<uint64_t>::Cons>(_loop_l2.v_mut());
          if (a0 <= a00) {
            auto _cell = std::make_unique<List<uint64_t>>(
                typename List<uint64_t>::Cons(std::move(a0), nullptr));
            *_write = std::move(_cell);
            _write =
                &std::get<typename List<uint64_t>::Cons>((*_write)->v_mut()).a1;
            _loop_l1 = std::move(*a1);
            _loop_fuel = f;
            continue;
          } else {
            auto _cell = std::make_unique<List<uint64_t>>(
                typename List<uint64_t>::Cons(std::move(a00), nullptr));
            *_write = std::move(_cell);
            _write =
                &std::get<typename List<uint64_t>::Cons>((*_write)->v_mut()).a1;
            _loop_l2 = std::move(*a10);
            _loop_fuel = f;
            continue;
          }
        }
      }
    }
  }
  return std::move(*_head);
}

List<uint64_t> LoopifySearch::merge_sorted(const List<uint64_t> &l1,
                                           const List<uint64_t> &l2) {
  return merge_sorted_fuel((len_impl<uint64_t>(l1) + len_impl<uint64_t>(l2)),
                           l1, l2);
}

/// merge_sort l sorts list using merge sort.
List<uint64_t> LoopifySearch::merge_sort_fuel(
    uint64_t fuel,
    List<uint64_t>
        l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    List<uint64_t> l;
    uint64_t fuel;
  };

  /// _After_a: saves [a, f], dispatches next recursive call.
  struct _After_a {
    List<uint64_t> a;
    uint64_t f;
  };

  /// _Combine_a: receives partial results, combines with _result from final
  /// call.
  struct _Combine_a {
    List<uint64_t> _result;
  };

  using _Frame = std::variant<_Enter, _After_a, _Combine_a>;
  List<uint64_t> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{l, fuel});
  /// Loopified merge_sort_fuel: _Enter -> _After_a -> _Combine_a.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      List<uint64_t> l = std::move(_f.l);
      uint64_t fuel = _f.fuel;
      if (fuel <= 0) {
        _result = std::move(l);
      } else {
        uint64_t f = fuel - 1;
        if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v_mut())) {
          _result = List<uint64_t>::nil();
        } else {
          auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v_mut());
          auto &&_sv = *a1;
          if (std::holds_alternative<typename List<uint64_t>::Nil>(_sv.v())) {
            _result = std::move(l);
          } else {
            auto _cs = split_list(l);
            const List<uint64_t> &a = _cs.first;
            const List<uint64_t> &b = _cs.second;
            _stack.emplace_back(_After_a{a, f});
            _stack.emplace_back(_Enter{b, f});
          }
        }
      }
    } else if (std::holds_alternative<_After_a>(_frame)) {
      auto _f = std::move(std::get<_After_a>(_frame));
      _stack.emplace_back(_Combine_a{std::move(_result)});
      _stack.emplace_back(_Enter{std::move(_f.a), _f.f});
    } else {
      auto _f = std::move(std::get<_Combine_a>(_frame));
      _result = merge_sorted(_result, _f._result);
    }
  }
  return _result;
}

List<uint64_t> LoopifySearch::merge_sort(const List<uint64_t> &l) {
  return merge_sort_fuel(len_impl<uint64_t>(l), l);
}

/// Helper: remove first occurrence of x from list.
List<uint64_t> LoopifySearch::remove_first(uint64_t x,
                                           const List<uint64_t> &l) {
  std::unique_ptr<List<uint64_t>> _head{};
  std::unique_ptr<List<uint64_t>> *_write = &_head;
  const List<uint64_t> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l->v())) {
      *_write = std::make_unique<List<uint64_t>>(List<uint64_t>::nil());
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename List<uint64_t>::Cons>(_loop_l->v());
      if (x == a0) {
        *_write = std::make_unique<List<uint64_t>>(*a1);
        break;
      } else {
        auto _cell = std::make_unique<List<uint64_t>>(
            typename List<uint64_t>::Cons(a0, nullptr));
        *_write = std::move(_cell);
        _write =
            &std::get<typename List<uint64_t>::Cons>((*_write)->v_mut()).a1;
        _loop_l = a1.get();
        continue;
      }
    }
  }
  return std::move(*_head);
}

/// Helper: map function that prepends element to each list.
List<List<uint64_t>> LoopifySearch::map_cons(uint64_t x,
                                             const List<List<uint64_t>> &lsts) {
  std::unique_ptr<List<List<uint64_t>>> _head{};
  std::unique_ptr<List<List<uint64_t>>> *_write = &_head;
  const List<List<uint64_t>> *_loop_lsts = &lsts;
  while (true) {
    if (std::holds_alternative<typename List<List<uint64_t>>::Nil>(
            _loop_lsts->v())) {
      *_write =
          std::make_unique<List<List<uint64_t>>>(List<List<uint64_t>>::nil());
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename List<List<uint64_t>>::Cons>(_loop_lsts->v());
      auto _cell = std::make_unique<List<List<uint64_t>>>(
          typename List<List<uint64_t>>::Cons(List<uint64_t>::cons(x, a0),
                                              nullptr));
      *_write = std::move(_cell);
      _write =
          &std::get<typename List<List<uint64_t>>::Cons>((*_write)->v_mut()).a1;
      _loop_lsts = a1.get();
      continue;
    }
  }
  return std::move(*_head);
}

/// perms_choices_fuel fuel choices orig generates permutations by iterating
/// over choices.  Single self-recursive function for full loopification.
/// Match on remaining is hoisted out of let-binding.
List<List<uint64_t>> LoopifySearch::perms_choices_fuel(
    uint64_t fuel, const List<uint64_t> &choices,
    const List<uint64_t> &
        orig) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    List<uint64_t> orig;
    List<uint64_t> choices;
    uint64_t fuel;
  };

  /// _After_Cons: saves [remaining_0, remaining_1, f, a0], dispatches next
  /// recursive call.
  struct _After_Cons {
    List<uint64_t> remaining_0;
    List<uint64_t> remaining_1;
    uint64_t f;
    uint64_t a0;
  };

  /// _Combine_Cons: receives partial results, combines with _result from final
  /// call.
  struct _Combine_Cons {
    List<List<uint64_t>> _result;
    uint64_t a0;
  };

  /// _Resume_Nil: saves [_s0], resumes after recursive call with _result.
  struct _Resume_Nil {
    decltype(map_cons(
        std::declval<uint64_t &>(),
        List<List<uint64_t>>::cons(List<uint64_t>::nil(),
                                   List<List<uint64_t>>::nil()))) _s0;
  };

  using _Frame = std::variant<_Enter, _After_Cons, _Combine_Cons, _Resume_Nil>;
  List<List<uint64_t>> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{orig, choices, fuel});
  /// Loopified perms_choices_fuel: _Enter -> _After_Cons -> _Combine_Cons ->
  /// _Resume_Nil.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<uint64_t> &orig = _f.orig;
      const List<uint64_t> &choices = _f.choices;
      uint64_t fuel = _f.fuel;
      if (fuel <= 0) {
        _result = List<List<uint64_t>>::nil();
      } else {
        uint64_t f = fuel - 1;
        if (std::holds_alternative<typename List<uint64_t>::Nil>(choices.v())) {
          _result = List<List<uint64_t>>::nil();
        } else {
          const auto &[a0, a1] =
              std::get<typename List<uint64_t>::Cons>(choices.v());
          List<uint64_t> remaining = remove_first(a0, orig);
          if (std::holds_alternative<typename List<uint64_t>::Nil>(
                  remaining.v_mut())) {
            _stack.emplace_back(_Resume_Nil{map_cons(
                a0, List<List<uint64_t>>::cons(List<uint64_t>::nil(),
                                               List<List<uint64_t>>::nil()))});
            _stack.emplace_back(_Enter{orig, std::move(*a1), f});
          } else {
            _stack.emplace_back(_After_Cons{remaining, remaining, f, a0});
            _stack.emplace_back(_Enter{orig, std::move(*a1), f});
          }
        }
      }
    } else if (std::holds_alternative<_After_Cons>(_frame)) {
      auto _f = std::move(std::get<_After_Cons>(_frame));
      _stack.emplace_back(_Combine_Cons{std::move(_result), _f.a0});
      _stack.emplace_back(
          _Enter{std::move(_f.remaining_0), std::move(_f.remaining_1), _f.f});
    } else if (std::holds_alternative<_Combine_Cons>(_frame)) {
      auto _f = std::move(std::get<_Combine_Cons>(_frame));
      _result = map_cons(_f.a0, _result).app(_f._result);
    } else {
      auto _f = std::move(std::get<_Resume_Nil>(_frame));
      _result = _f._s0.app(_result);
    }
  }
  return _result;
}

/// permutations_fuel fuel l generates all permutations of list.
List<List<uint64_t>> LoopifySearch::permutations_fuel(uint64_t fuel,
                                                      const List<uint64_t> &l) {
  if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
    return List<List<uint64_t>>::cons(List<uint64_t>::nil(),
                                      List<List<uint64_t>>::nil());
  } else {
    return perms_choices_fuel(fuel, l, l);
  }
}

List<List<uint64_t>> LoopifySearch::permutations(const List<uint64_t> &l) {
  return permutations_fuel((len_impl<uint64_t>(l) + 1), l);
}

/// linear_search x l finds index of first occurrence of x.
std::optional<uint64_t>
LoopifySearch::linear_search_aux(uint64_t x, const List<uint64_t> &l,
                                 uint64_t idx) {
  uint64_t _loop_idx = std::move(idx);
  const List<uint64_t> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l->v())) {
      return std::optional<uint64_t>();
    } else {
      const auto &[a0, a1] =
          std::get<typename List<uint64_t>::Cons>(_loop_l->v());
      if (x == a0) {
        return std::make_optional<uint64_t>(_loop_idx);
      } else {
        _loop_idx = (_loop_idx + 1);
        _loop_l = a1.get();
      }
    }
  }
}

std::optional<uint64_t> LoopifySearch::linear_search(uint64_t x,
                                                     const List<uint64_t> &l) {
  return linear_search_aux(x, l, UINT64_C(0));
}

/// all_indices x l finds all indices where x occurs.
List<uint64_t> LoopifySearch::all_indices_aux(uint64_t x,
                                              const List<uint64_t> &l,
                                              uint64_t idx) {
  std::unique_ptr<List<uint64_t>> _head{};
  std::unique_ptr<List<uint64_t>> *_write = &_head;
  uint64_t _loop_idx = std::move(idx);
  const List<uint64_t> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l->v())) {
      *_write = std::make_unique<List<uint64_t>>(List<uint64_t>::nil());
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename List<uint64_t>::Cons>(_loop_l->v());
      if (x == a0) {
        auto _cell = std::make_unique<List<uint64_t>>(
            typename List<uint64_t>::Cons(_loop_idx, nullptr));
        *_write = std::move(_cell);
        _write =
            &std::get<typename List<uint64_t>::Cons>((*_write)->v_mut()).a1;
        _loop_idx = (_loop_idx + 1);
        _loop_l = a1.get();
        continue;
      } else {
        _loop_idx = (_loop_idx + 1);
        _loop_l = a1.get();
        continue;
      }
    }
  }
  return std::move(*_head);
}

List<uint64_t> LoopifySearch::all_indices(uint64_t x, const List<uint64_t> &l) {
  return all_indices_aux(x, l, UINT64_C(0));
}

/// min_element l finds minimum element in list.
uint64_t LoopifySearch::min_element(
    const List<uint64_t>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<uint64_t> *l;
  };

  /// _Cont_Cons: saves [a0], resumes after recursive call, then processes rest.
  struct _Cont_Cons {
    uint64_t a0;
  };

  using _Frame = std::variant<_Enter, _Cont_Cons>;
  uint64_t _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l});
  /// Loopified min_element: _Enter -> _Cont_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<uint64_t> &l = *_f.l;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
        auto &&_sv = *a1;
        if (std::holds_alternative<typename List<uint64_t>::Nil>(_sv.v())) {
          _result = std::move(a0);
        } else {
          _stack.emplace_back(_Cont_Cons{a0});
          _stack.emplace_back(_Enter{a1.get()});
        }
      }
    } else {
      auto _f = std::move(std::get<_Cont_Cons>(_frame));
      uint64_t a0 = _f.a0;
      uint64_t min_rest = _result;
      if (a0 <= min_rest) {
        _result = std::move(a0);
      } else {
        _result = std::move(min_rest);
      }
    }
  }
  return _result;
}
