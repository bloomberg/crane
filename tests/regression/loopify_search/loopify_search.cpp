#include "loopify_search.h"

/// Consolidated search and optimization algorithms.
/// knapsack capacity items solves 0/1 knapsack problem.
/// Items are (weight, value) pairs.
uint64_t LoopifySearch::knapsack_fuel(
    uint64_t fuel, uint64_t capacity,
    const List<std::pair<uint64_t, uint64_t>>
        &items) { /// CraneEnter: captures varying parameters for each recursive
                  /// call.

  struct CraneEnter {
    const List<std::pair<uint64_t, uint64_t>> *items;
    uint64_t capacity;
    uint64_t fuel;
  };

  /// CraneCont1: saves [a1, capacity, f, value, weight], resumes after
  /// recursive call, then processes rest.
  struct CraneCont1 {
    const List<std::pair<uint64_t, uint64_t>> *a1;
    uint64_t capacity;
    uint64_t f;
    uint64_t value;
    uint64_t weight;
  };

  /// CraneCont2: saves [_tmp3, a1, capacity, f, value, weight], resumes after
  /// recursive call, then processes rest.
  struct CraneCont2 {
    uint64_t _tmp3;
    const List<std::pair<uint64_t, uint64_t>> *a1;
    uint64_t capacity;
    uint64_t f;
    uint64_t value;
    uint64_t weight;
  };

  /// CraneCont3: saves [value], resumes after recursive call, then processes
  /// rest.
  struct CraneCont3 {
    uint64_t value;
  };

  using CraneFrame =
      std::variant<CraneEnter, CraneCont1, CraneCont2, CraneCont3>;
  uint64_t _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{&items, capacity, fuel});
  /// Loopified knapsack_fuel: CraneEnter -> CraneCont1 -> CraneCont2 ->
  /// CraneCont3.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      const List<std::pair<uint64_t, uint64_t>> &items = *_f.items;
      uint64_t capacity = _f.capacity;
      uint64_t fuel = _f.fuel;
      if (fuel <= 0) {
        _result = UINT64_C(0);
      } else {
        uint64_t f = fuel - 1;
        if (std::holds_alternative<
                typename List<std::pair<uint64_t, uint64_t>>::Nil>(items.v())) {
          _result = UINT64_C(0);
        } else {
          const auto &[a0, a1] =
              std::get<typename List<std::pair<uint64_t, uint64_t>>::Cons>(
                  items.v());
          const auto &[weight, value] = a0;
          if (capacity < weight) {
            _stack.emplace_back(CraneEnter{crane_raw(a1), capacity, f});
          } else {
            _stack.emplace_back(
                CraneCont1{crane_raw(a1), capacity, f, value, weight});
            _stack.emplace_back(CraneEnter{crane_raw(a1), capacity, f});
          }
        }
      }
    } else if (std::holds_alternative<CraneCont1>(_frame)) {
      auto _f = std::move(std::get<CraneCont1>(_frame));
      const List<std::pair<uint64_t, uint64_t>> &a1 = *_f.a1;
      uint64_t capacity = _f.capacity;
      uint64_t f = _f.f;
      uint64_t value = _f.value;
      uint64_t weight = _f.weight;
      _stack.emplace_back(
          CraneCont2{std::move(_result), &a1, capacity, f, value, weight});
      _stack.emplace_back(CraneEnter{
          &a1, (((capacity - weight) > capacity ? 0 : (capacity - weight))),
          f});
    } else if (std::holds_alternative<CraneCont2>(_frame)) {
      auto _f = std::move(std::get<CraneCont2>(_frame));
      const List<std::pair<uint64_t, uint64_t>> &a1 = *_f.a1;
      uint64_t capacity = _f.capacity;
      uint64_t f = _f.f;
      uint64_t value = _f.value;
      uint64_t weight = _f.weight;
      uint64_t _tmp3 = _f._tmp3;
      uint64_t _tmp2 = std::move(_result);
      if (_tmp3 <= (value + _tmp2)) {
        _stack.emplace_back(CraneCont3{value});
        _stack.emplace_back(CraneEnter{
            &a1, (((capacity - weight) > capacity ? 0 : (capacity - weight))),
            f});
      } else {
        _stack.emplace_back(CraneEnter{&a1, capacity, f});
      }
    } else {
      auto _f = std::move(std::get<CraneCont3>(_frame));
      uint64_t value = _f.value;
      _result = (value + std::move(_result));
    }
  }
  return _result;
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
    const List<uint64_t> &l) { /// CraneEnter: captures varying parameters for
                               /// each recursive call.

  struct CraneEnter {
    const List<uint64_t> *l;
  };

  /// CraneCont_Cons: saves [a0], resumes after recursive call, then processes
  /// rest.
  struct CraneCont_Cons {
    uint64_t a0;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont_Cons>;
  std::pair<uint64_t, uint64_t> _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{&l});
  /// Loopified majority: CraneEnter -> CraneCont_Cons.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      const List<uint64_t> &l = *_f.l;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
        _result = std::make_pair(UINT64_C(0), UINT64_C(0));
      } else {
        const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
        _stack.emplace_back(CraneCont_Cons{a0});
        _stack.emplace_back(CraneEnter{crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<CraneCont_Cons>(_frame));
      uint64_t a0 = _f.a0;
      auto [cand, count] = std::move(_result);
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
  std::optional<List<uint64_t>> _root{};
  std::shared_ptr<List<uint64_t>> *_write = nullptr;
  const List<uint64_t> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l->v())) {
      auto _value = List<uint64_t>::nil();
      (_write ? *(*_write = std::make_shared<List<uint64_t>>(std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename List<uint64_t>::Cons>(_loop_l->v());
      auto &&_sv0 = *a1;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(_sv0.v())) {
        auto _value = List<uint64_t>::cons(a0, List<uint64_t>::nil());
        (_write
             ? *(*_write = std::make_shared<List<uint64_t>>(std::move(_value)))
             : _root.emplace(std::move(_value)));
        break;
      } else {
        const auto &[a00, a10] =
            std::get<typename List<uint64_t>::Cons>(_sv0.v());
        if (a0 < a00) {
          auto _cell = typename List<uint64_t>::Cons(a0, nullptr);
          List<uint64_t> &_node =
              (_write ? *(*_write = std::make_shared<List<uint64_t>>(
                              std::move(_cell)))
                      : _root.emplace(std::move(_cell)));
          _write = &std::get<typename List<uint64_t>::Cons>(_node.v_mut()).l;
          _loop_l = crane_raw(a1);
          continue;
        } else {
          _loop_l = crane_raw(a1);
          continue;
        }
      }
    }
  }
  return std::move(*_root);
}

/// Helper for binary search: get nth element.
uint64_t LoopifySearch::nth_impl(uint64_t n, const List<uint64_t> &l) {
  const List<uint64_t> *_loop_l = &l;
  uint64_t _loop_n = n;
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
        _loop_l = crane_raw(a10);
        _loop_n = m;
      }
    }
  }
}

/// Helper for binary search: take first k elements.
List<uint64_t> LoopifySearch::take_impl(uint64_t k, const List<uint64_t> &l) {
  std::optional<List<uint64_t>> _root{};
  std::shared_ptr<List<uint64_t>> *_write = nullptr;
  const List<uint64_t> *_loop_l = &l;
  uint64_t _loop_k = k;
  while (true) {
    if (_loop_k <= 0) {
      auto _value = List<uint64_t>::nil();
      (_write ? *(*_write = std::make_shared<List<uint64_t>>(std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      uint64_t m = _loop_k - 1;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l->v())) {
        auto _value = List<uint64_t>::nil();
        (_write
             ? *(*_write = std::make_shared<List<uint64_t>>(std::move(_value)))
             : _root.emplace(std::move(_value)));
        break;
      } else {
        const auto &[a0, a1] =
            std::get<typename List<uint64_t>::Cons>(_loop_l->v());
        auto _cell = typename List<uint64_t>::Cons(a0, nullptr);
        List<uint64_t> &_node =
            (_write ? *(*_write =
                            std::make_shared<List<uint64_t>>(std::move(_cell)))
                    : _root.emplace(std::move(_cell)));
        _write = &std::get<typename List<uint64_t>::Cons>(_node.v_mut()).l;
        _loop_l = crane_raw(a1);
        _loop_k = m;
        continue;
      }
    }
  }
  return std::move(*_root);
}

/// Helper for binary search: drop first k elements.
List<uint64_t> LoopifySearch::drop_impl(uint64_t k, List<uint64_t> l) {
  List<uint64_t> _loop_l = std::move(l);
  uint64_t _loop_k = k;
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
        _loop_l = List<uint64_t>(*a1);
        _loop_k = m;
      }
    }
  }
}

/// binary_search_fuel target sorted_list searches for target in sorted list.
/// Returns true if found.
bool LoopifySearch::binary_search_fuel(uint64_t fuel, uint64_t target,
                                       List<uint64_t> l) {
  List<uint64_t> _loop_l = std::move(l);
  uint64_t _loop_fuel = fuel;
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
            _loop_l = take_impl(mid, std::move(_loop_l));
            _loop_fuel = f;
          } else {
            _loop_l = drop_impl((mid + 1), std::move(_loop_l));
            _loop_fuel = f;
          }
        }
      }
    }
  }
}

bool LoopifySearch::binary_search(uint64_t target, List<uint64_t> l) {
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
          _loop_l = crane_raw(a1);
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
          _loop_l = crane_raw(a1);
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
    uint64_t fuel, uint64_t n) { /// CraneEnter: captures varying parameters for
                                 /// each recursive call.

  struct CraneEnter {
    uint64_t n;
    uint64_t fuel;
  };

  /// CraneCont1: resumes after recursive call, then processes rest.
  struct CraneCont1 {};

  /// CraneCont2: resumes after recursive call, then processes rest.
  struct CraneCont2 {};

  using CraneFrame = std::variant<CraneEnter, CraneCont1, CraneCont2>;
  uint64_t _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{n, fuel});
  /// Loopified collatz_fuel: CraneEnter -> CraneCont1 -> CraneCont2.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
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
            _stack.emplace_back(CraneCont1{});
            _stack.emplace_back(
                CraneEnter{(UINT64_C(2) ? n / UINT64_C(2) : 0), f});
          } else {
            _stack.emplace_back(CraneCont2{});
            _stack.emplace_back(
                CraneEnter{((UINT64_C(3) * n) + UINT64_C(1)), f});
          }
        }
      }
    } else if (std::holds_alternative<CraneCont1>(_frame)) {
      auto _f = std::move(std::get<CraneCont1>(_frame));
      _result = (std::move(_result) + 1);
    } else {
      auto _f = std::move(std::get<CraneCont2>(_frame));
      _result = (std::move(_result) + 1);
    }
  }
  return _result;
}

uint64_t LoopifySearch::collatz(uint64_t n) {
  return collatz_fuel(UINT64_C(1000), n);
}

/// lis l simple longest increasing subsequence (greedy approach).
List<uint64_t> LoopifySearch::lis(const List<uint64_t> &l) {
  return longest_increasing_subseq(l);
}

/// subset_sum target l checks if any subset sums to target.
bool LoopifySearch::subset_sum_fuel(
    uint64_t fuel, uint64_t target,
    const List<uint64_t> &l) { /// CraneEnter: captures varying parameters for
                               /// each recursive call.

  struct CraneEnter {
    const List<uint64_t> *l;
    uint64_t target;
    uint64_t fuel;
  };

  /// CraneCont_Cons: saves [a0, a1, f, target], resumes after recursive call,
  /// then processes rest.
  struct CraneCont_Cons {
    uint64_t a0;
    const List<uint64_t> *a1;
    uint64_t f;
    uint64_t target;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont_Cons>;
  bool _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{&l, target, fuel});
  /// Loopified subset_sum_fuel: CraneEnter -> CraneCont_Cons.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      const List<uint64_t> &l = *_f.l;
      uint64_t target = _f.target;
      uint64_t fuel = _f.fuel;
      if (fuel <= 0) {
        _result = false;
      } else {
        uint64_t f = fuel - 1;
        if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
          _result = target == UINT64_C(0);
        } else {
          const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
          _stack.emplace_back(CraneCont_Cons{a0, crane_raw(a1), f, target});
          _stack.emplace_back(CraneEnter{crane_raw(a1), target, f});
        }
      }
    } else {
      auto _f = std::move(std::get<CraneCont_Cons>(_frame));
      uint64_t a0 = _f.a0;
      const List<uint64_t> &a1 = *_f.a1;
      uint64_t f = _f.f;
      uint64_t target = _f.target;
      bool without = std::move(_result);
      if (without) {
        _result = true;
      } else {
        if (a0 <= target) {
          _stack.emplace_back(CraneEnter{
              &a1, (((target - a0) > target ? 0 : (target - a0))), f});
        } else {
          _result = false;
        }
      }
    }
  }
  return _result;
}

bool LoopifySearch::subset_sum(uint64_t target, const List<uint64_t> &l) {
  return subset_sum_fuel((len_impl<uint64_t>(l) + 1), target, l);
}

/// sieve l removes multiples (simplified sieve of Eratosthenes).
List<uint64_t> LoopifySearch::sieve_fuel(uint64_t fuel, List<uint64_t> l) {
  std::optional<List<uint64_t>> _root{};
  std::shared_ptr<List<uint64_t>> *_write = nullptr;
  List<uint64_t> _loop_l = std::move(l);
  uint64_t _loop_fuel = fuel;
  while (true) {
    if (_loop_fuel <= 0) {
      auto _value = std::move(_loop_l);
      (_write ? *(*_write = std::make_shared<List<uint64_t>>(std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      uint64_t f = _loop_fuel - 1;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(
              _loop_l.v_mut())) {
        auto _value = List<uint64_t>::nil();
        (_write
             ? *(*_write = std::make_shared<List<uint64_t>>(std::move(_value)))
             : _root.emplace(std::move(_value)));
        break;
      } else {
        auto &[a0, a1] =
            std::get<typename List<uint64_t>::Cons>(_loop_l.v_mut());
        const List<uint64_t> &a1_value = *a1;
        auto _cell = typename List<uint64_t>::Cons(std::move(a0), nullptr);
        List<uint64_t> &_node =
            (_write ? *(*_write =
                            std::make_shared<List<uint64_t>>(std::move(_cell)))
                    : _root.emplace(std::move(_cell)));
        _write = &std::get<typename List<uint64_t>::Cons>(_node.v_mut()).l;
        _loop_l = filter_impl(
            [=](uint64_t y) { return !((a0 ? y % a0 : y) == UINT64_C(0)); },
            a1_value);
        _loop_fuel = f;
        continue;
      }
    }
  }
  return std::move(*_root);
}

List<uint64_t> LoopifySearch::sieve(List<uint64_t> l) {
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
        _loop_l = crane_raw(a1);
      }
    }
  }
}

/// nub l removes duplicates from list.
List<uint64_t> LoopifySearch::nub_fuel(uint64_t fuel, List<uint64_t> l) {
  std::optional<List<uint64_t>> _root{};
  std::shared_ptr<List<uint64_t>> *_write = nullptr;
  List<uint64_t> _loop_l = std::move(l);
  uint64_t _loop_fuel = fuel;
  while (true) {
    if (_loop_fuel <= 0) {
      auto _value = std::move(_loop_l);
      (_write ? *(*_write = std::make_shared<List<uint64_t>>(std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      uint64_t f = _loop_fuel - 1;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(
              _loop_l.v_mut())) {
        auto _value = List<uint64_t>::nil();
        (_write
             ? *(*_write = std::make_shared<List<uint64_t>>(std::move(_value)))
             : _root.emplace(std::move(_value)));
        break;
      } else {
        auto &[a0, a1] =
            std::get<typename List<uint64_t>::Cons>(_loop_l.v_mut());
        if (elem_impl(a0, *a1)) {
          _loop_l = List<uint64_t>(*a1);
          _loop_fuel = f;
          continue;
        } else {
          auto _cell = typename List<uint64_t>::Cons(std::move(a0), nullptr);
          List<uint64_t> &_node =
              (_write ? *(*_write = std::make_shared<List<uint64_t>>(
                              std::move(_cell)))
                      : _root.emplace(std::move(_cell)));
          _write = &std::get<typename List<uint64_t>::Cons>(_node.v_mut()).l;
          _loop_l = List<uint64_t>(*a1);
          _loop_fuel = f;
          continue;
        }
      }
    }
  }
  return std::move(*_root);
}

List<uint64_t> LoopifySearch::nub(List<uint64_t> l) {
  return nub_fuel(len_impl<uint64_t>(l), l);
}

/// remove_duplicates l removes all duplicate elements.
List<uint64_t> LoopifySearch::remove_duplicates_fuel(uint64_t fuel,
                                                     List<uint64_t> l) {
  std::optional<List<uint64_t>> _root{};
  std::shared_ptr<List<uint64_t>> *_write = nullptr;
  List<uint64_t> _loop_l = std::move(l);
  uint64_t _loop_fuel = fuel;
  while (true) {
    if (_loop_fuel <= 0) {
      auto _value = std::move(_loop_l);
      (_write ? *(*_write = std::make_shared<List<uint64_t>>(std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      uint64_t f = _loop_fuel - 1;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(
              _loop_l.v_mut())) {
        auto _value = List<uint64_t>::nil();
        (_write
             ? *(*_write = std::make_shared<List<uint64_t>>(std::move(_value)))
             : _root.emplace(std::move(_value)));
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
          auto _cell = typename List<uint64_t>::Cons(std::move(a0), nullptr);
          List<uint64_t> &_node =
              (_write ? *(*_write = std::make_shared<List<uint64_t>>(
                              std::move(_cell)))
                      : _root.emplace(std::move(_cell)));
          _write = &std::get<typename List<uint64_t>::Cons>(_node.v_mut()).l;
          _loop_l =
              filter_impl([=](uint64_t y) { return !(a0 == y); }, a1_value);
          _loop_fuel = f;
          continue;
        }
      }
    }
  }
  return std::move(*_root);
}

List<uint64_t> LoopifySearch::remove_duplicates(List<uint64_t> l) {
  return remove_duplicates_fuel(len_impl<uint64_t>(l), l);
}

/// quicksort l sorts list using quicksort with filter-based partitioning.
List<uint64_t> LoopifySearch::quicksort_fuel(
    uint64_t fuel, List<uint64_t> l) { /// CraneEnter: captures varying
                                       /// parameters for each recursive call.

  struct CraneEnter {
    List<uint64_t> l;
    uint64_t fuel;
  };

  /// CraneCont_Cons: saves [a0, f, greater], resumes after recursive call, then
  /// processes rest.
  struct CraneCont_Cons {
    uint64_t a0;
    uint64_t f;
    List<uint64_t> greater;
  };

  /// CraneCont_Cons_1: saves [_tmp2, a0], resumes after recursive call, then
  /// processes rest.
  struct CraneCont_Cons_1 {
    List<uint64_t> _tmp2;
    uint64_t a0;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont_Cons, CraneCont_Cons_1>;
  List<uint64_t> _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{std::move(l), fuel});
  /// Loopified quicksort_fuel: CraneEnter -> CraneCont_Cons ->
  /// CraneCont_Cons_1.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
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
              filter_impl([=](uint64_t y) { return y < a0; }, a1_value);
          List<uint64_t> greater =
              filter_impl([=](uint64_t y) { return a0 <= y; }, a1_value);
          _stack.emplace_back(CraneCont_Cons{a0, f, std::move(greater)});
          _stack.emplace_back(CraneEnter{std::move(smaller), f});
        }
      }
    } else if (std::holds_alternative<CraneCont_Cons>(_frame)) {
      auto _f = std::move(std::get<CraneCont_Cons>(_frame));
      uint64_t a0 = _f.a0;
      uint64_t f = _f.f;
      List<uint64_t> greater = std::move(_f.greater);
      _stack.emplace_back(CraneCont_Cons_1{std::move(_result), a0});
      _stack.emplace_back(CraneEnter{std::move(greater), f});
    } else {
      auto _f = std::move(std::get<CraneCont_Cons_1>(_frame));
      uint64_t a0 = _f.a0;
      _result = std::move(_f._tmp2).app(
          List<uint64_t>::cons(std::move(a0), std::move(_result)));
    }
  }
  return _result;
}

List<uint64_t> LoopifySearch::quicksort(List<uint64_t> l) {
  return quicksort_fuel(len_impl<uint64_t>(l), l);
}

/// Helper: split list into two roughly equal parts.
std::pair<List<uint64_t>, List<uint64_t>> LoopifySearch::split_list(
    const List<uint64_t> &l) { /// CraneEnter: captures varying parameters for
                               /// each recursive call.

  struct CraneEnter {
    const List<uint64_t> *l;
  };

  /// CraneCont_Cons: saves [a0, a00], resumes after recursive call, then
  /// processes rest.
  struct CraneCont_Cons {
    uint64_t a0;
    uint64_t a00;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont_Cons>;
  std::pair<List<uint64_t>, List<uint64_t>> _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{&l});
  /// Loopified split_list: CraneEnter -> CraneCont_Cons.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
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
          _stack.emplace_back(CraneCont_Cons{a0, a00});
          _stack.emplace_back(CraneEnter{crane_raw(a10)});
        }
      }
    } else {
      auto _f = std::move(std::get<CraneCont_Cons>(_frame));
      uint64_t a0 = _f.a0;
      uint64_t a00 = _f.a00;
      auto [a, b] = std::move(_result);
      _result = std::make_pair(List<uint64_t>::cons(a0, std::move(a)),
                               List<uint64_t>::cons(a00, std::move(b)));
    }
  }
  return _result;
}

/// Helper: merge two sorted lists with fuel.
List<uint64_t> LoopifySearch::merge_sorted_fuel(uint64_t fuel,
                                                List<uint64_t> l1,
                                                List<uint64_t> l2) {
  std::optional<List<uint64_t>> _root{};
  std::shared_ptr<List<uint64_t>> *_write = nullptr;
  List<uint64_t> _loop_l2 = std::move(l2);
  List<uint64_t> _loop_l1 = std::move(l1);
  uint64_t _loop_fuel = fuel;
  while (true) {
    if (_loop_fuel <= 0) {
      auto _value = std::move(_loop_l1).app(std::move(_loop_l2));
      (_write ? *(*_write = std::make_shared<List<uint64_t>>(std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      uint64_t f = _loop_fuel - 1;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(
              _loop_l1.v_mut())) {
        auto _value = std::move(_loop_l2);
        (_write
             ? *(*_write = std::make_shared<List<uint64_t>>(std::move(_value)))
             : _root.emplace(std::move(_value)));
        break;
      } else {
        auto &[a0, a1] =
            std::get<typename List<uint64_t>::Cons>(_loop_l1.v_mut());
        if (std::holds_alternative<typename List<uint64_t>::Nil>(
                _loop_l2.v_mut())) {
          auto _value = _loop_l1;
          (_write ? *(*_write =
                          std::make_shared<List<uint64_t>>(std::move(_value)))
                  : _root.emplace(std::move(_value)));
          break;
        } else {
          auto &[a00, a10] =
              std::get<typename List<uint64_t>::Cons>(_loop_l2.v_mut());
          if (a0 <= a00) {
            auto _cell = typename List<uint64_t>::Cons(a0, nullptr);
            List<uint64_t> &_node =
                (_write ? *(*_write = std::make_shared<List<uint64_t>>(
                                std::move(_cell)))
                        : _root.emplace(std::move(_cell)));
            _write = &std::get<typename List<uint64_t>::Cons>(_node.v_mut()).l;
            _loop_l1 = List<uint64_t>(*a1);
            _loop_fuel = f;
            continue;
          } else {
            auto _cell = typename List<uint64_t>::Cons(a00, nullptr);
            List<uint64_t> &_node =
                (_write ? *(*_write = std::make_shared<List<uint64_t>>(
                                std::move(_cell)))
                        : _root.emplace(std::move(_cell)));
            _write = &std::get<typename List<uint64_t>::Cons>(_node.v_mut()).l;
            _loop_l2 = List<uint64_t>(*a10);
            _loop_fuel = f;
            continue;
          }
        }
      }
    }
  }
  return std::move(*_root);
}

List<uint64_t> LoopifySearch::merge_sorted(List<uint64_t> l1,
                                           List<uint64_t> l2) {
  return merge_sorted_fuel((len_impl<uint64_t>(l1) + len_impl<uint64_t>(l2)),
                           l1, l2);
}

/// merge_sort l sorts list using merge sort.
List<uint64_t> LoopifySearch::merge_sort_fuel(
    uint64_t fuel, List<uint64_t> l) { /// CraneEnter: captures varying
                                       /// parameters for each recursive call.

  struct CraneEnter {
    List<uint64_t> l;
    uint64_t fuel;
  };

  /// CraneCont_a: saves [b, f], resumes after recursive call, then processes
  /// rest.
  struct CraneCont_a {
    List<uint64_t> b;
    uint64_t f;
  };

  /// CraneCont_a_1: saves [_tmp2], resumes after recursive call, then processes
  /// rest.
  struct CraneCont_a_1 {
    List<uint64_t> _tmp2;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont_a, CraneCont_a_1>;
  List<uint64_t> _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{std::move(l), fuel});
  /// Loopified merge_sort_fuel: CraneEnter -> CraneCont_a -> CraneCont_a_1.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
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
            auto [a, b] = split_list(l);
            _stack.emplace_back(CraneCont_a{b, f});
            _stack.emplace_back(CraneEnter{std::move(a), f});
          }
        }
      }
    } else if (std::holds_alternative<CraneCont_a>(_frame)) {
      auto _f = std::move(std::get<CraneCont_a>(_frame));
      List<uint64_t> b = std::move(_f.b);
      uint64_t f = _f.f;
      _stack.emplace_back(CraneCont_a_1{std::move(_result)});
      _stack.emplace_back(CraneEnter{std::move(b), f});
    } else {
      auto _f = std::move(std::get<CraneCont_a_1>(_frame));
      _result = merge_sorted(std::move(_f._tmp2), std::move(_result));
    }
  }
  return _result;
}

List<uint64_t> LoopifySearch::merge_sort(List<uint64_t> l) {
  return merge_sort_fuel(len_impl<uint64_t>(l), l);
}

/// Helper: remove first occurrence of x from list.
List<uint64_t> LoopifySearch::remove_first(uint64_t x,
                                           const List<uint64_t> &l) {
  std::optional<List<uint64_t>> _root{};
  std::shared_ptr<List<uint64_t>> *_write = nullptr;
  const List<uint64_t> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l->v())) {
      auto _value = List<uint64_t>::nil();
      (_write ? *(*_write = std::make_shared<List<uint64_t>>(std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename List<uint64_t>::Cons>(_loop_l->v());
      if (x == a0) {
        auto _value = *a1;
        (_write
             ? *(*_write = std::make_shared<List<uint64_t>>(std::move(_value)))
             : _root.emplace(std::move(_value)));
        break;
      } else {
        auto _cell = typename List<uint64_t>::Cons(a0, nullptr);
        List<uint64_t> &_node =
            (_write ? *(*_write =
                            std::make_shared<List<uint64_t>>(std::move(_cell)))
                    : _root.emplace(std::move(_cell)));
        _write = &std::get<typename List<uint64_t>::Cons>(_node.v_mut()).l;
        _loop_l = crane_raw(a1);
        continue;
      }
    }
  }
  return std::move(*_root);
}

/// Helper: map function that prepends element to each list.
List<List<uint64_t>> LoopifySearch::map_cons(uint64_t x,
                                             const List<List<uint64_t>> &lsts) {
  std::optional<List<List<uint64_t>>> _root{};
  std::shared_ptr<List<List<uint64_t>>> *_write = nullptr;
  const List<List<uint64_t>> *_loop_lsts = &lsts;
  while (true) {
    if (std::holds_alternative<typename List<List<uint64_t>>::Nil>(
            _loop_lsts->v())) {
      auto _value = List<List<uint64_t>>::nil();
      (_write ? *(*_write =
                      std::make_shared<List<List<uint64_t>>>(std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename List<List<uint64_t>>::Cons>(_loop_lsts->v());
      auto _cell = typename List<List<uint64_t>>::Cons(
          List<uint64_t>::cons(x, a0), nullptr);
      List<List<uint64_t>> &_node =
          (_write ? *(*_write = std::make_shared<List<List<uint64_t>>>(
                          std::move(_cell)))
                  : _root.emplace(std::move(_cell)));
      _write = &std::get<typename List<List<uint64_t>>::Cons>(_node.v_mut()).l;
      _loop_lsts = crane_raw(a1);
      continue;
    }
  }
  return std::move(*_root);
}

/// perms_choices_fuel fuel choices orig generates permutations by iterating
/// over choices.  Single self-recursive function for full loopification.
/// Match on remaining is hoisted out of let-binding.
List<List<uint64_t>> LoopifySearch::perms_choices_fuel(
    uint64_t fuel, const List<uint64_t> &choices,
    const List<uint64_t> &orig) { /// CraneEnter: captures varying parameters
                                  /// for each recursive call.

  struct CraneEnter {
    List<uint64_t> orig;
    List<uint64_t> choices;
    uint64_t fuel;
  };

  /// CraneCont_Cons: saves [a0, a1, f, orig], resumes after recursive call,
  /// then processes rest.
  struct CraneCont_Cons {
    uint64_t a0;
    std::shared_ptr<List<uint64_t>> a1;
    uint64_t f;
    List<uint64_t> orig;
  };

  /// CraneCont_Cons_1: saves [_tmp3, a0], resumes after recursive call, then
  /// processes rest.
  struct CraneCont_Cons_1 {
    List<List<uint64_t>> _tmp3;
    uint64_t a0;
  };

  /// CraneCont_Nil: saves [a0], resumes after recursive call, then processes
  /// rest.
  struct CraneCont_Nil {
    uint64_t a0;
  };

  using CraneFrame =
      std::variant<CraneEnter, CraneCont_Cons, CraneCont_Cons_1, CraneCont_Nil>;
  List<List<uint64_t>> _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{orig, choices, fuel});
  /// Loopified perms_choices_fuel: CraneEnter -> CraneCont_Cons ->
  /// CraneCont_Cons_1 -> CraneCont_Nil.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      const List<uint64_t> &orig = std::move(_f.orig);
      const List<uint64_t> &choices = std::move(_f.choices);
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
            _stack.emplace_back(CraneCont_Nil{a0});
            _stack.emplace_back(CraneEnter{orig, *a1, f});
          } else {
            _stack.emplace_back(CraneCont_Cons{a0, a1, f, orig});
            _stack.emplace_back(CraneEnter{remaining, remaining, f});
          }
        }
      }
    } else if (std::holds_alternative<CraneCont_Cons>(_frame)) {
      auto _f = std::move(std::get<CraneCont_Cons>(_frame));
      uint64_t a0 = _f.a0;
      std::shared_ptr<List<uint64_t>> a1 = std::move(_f.a1);
      uint64_t f = _f.f;
      const List<uint64_t> &orig = std::move(_f.orig);
      _stack.emplace_back(CraneCont_Cons_1{std::move(_result), a0});
      _stack.emplace_back(CraneEnter{orig, *a1, f});
    } else if (std::holds_alternative<CraneCont_Cons_1>(_frame)) {
      auto _f = std::move(std::get<CraneCont_Cons_1>(_frame));
      uint64_t a0 = _f.a0;
      _result = map_cons(a0, std::move(_f._tmp3)).app(std::move(_result));
    } else {
      auto _f = std::move(std::get<CraneCont_Nil>(_frame));
      uint64_t a0 = _f.a0;
      _result =
          map_cons(a0, List<List<uint64_t>>::cons(List<uint64_t>::nil(),
                                                  List<List<uint64_t>>::nil()))
              .app(std::move(_result));
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
  uint64_t _loop_idx = idx;
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
        _loop_l = crane_raw(a1);
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
  std::optional<List<uint64_t>> _root{};
  std::shared_ptr<List<uint64_t>> *_write = nullptr;
  uint64_t _loop_idx = idx;
  const List<uint64_t> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l->v())) {
      auto _value = List<uint64_t>::nil();
      (_write ? *(*_write = std::make_shared<List<uint64_t>>(std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename List<uint64_t>::Cons>(_loop_l->v());
      if (x == a0) {
        auto _cell = typename List<uint64_t>::Cons(_loop_idx, nullptr);
        List<uint64_t> &_node =
            (_write ? *(*_write =
                            std::make_shared<List<uint64_t>>(std::move(_cell)))
                    : _root.emplace(std::move(_cell)));
        _write = &std::get<typename List<uint64_t>::Cons>(_node.v_mut()).l;
        _loop_idx = (_loop_idx + 1);
        _loop_l = crane_raw(a1);
        continue;
      } else {
        _loop_idx = (_loop_idx + 1);
        _loop_l = crane_raw(a1);
        continue;
      }
    }
  }
  return std::move(*_root);
}

List<uint64_t> LoopifySearch::all_indices(uint64_t x, const List<uint64_t> &l) {
  return all_indices_aux(x, l, UINT64_C(0));
}

/// min_element l finds minimum element in list.
uint64_t LoopifySearch::min_element(
    const List<uint64_t> &l) { /// CraneEnter: captures varying parameters for
                               /// each recursive call.

  struct CraneEnter {
    const List<uint64_t> *l;
  };

  /// CraneCont_Cons: saves [a0], resumes after recursive call, then processes
  /// rest.
  struct CraneCont_Cons {
    uint64_t a0;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont_Cons>;
  uint64_t _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{&l});
  /// Loopified min_element: CraneEnter -> CraneCont_Cons.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      const List<uint64_t> &l = *_f.l;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
        auto &&_sv = *a1;
        if (std::holds_alternative<typename List<uint64_t>::Nil>(_sv.v())) {
          _result = std::move(a0);
        } else {
          _stack.emplace_back(CraneCont_Cons{a0});
          _stack.emplace_back(CraneEnter{crane_raw(a1)});
        }
      }
    } else {
      auto _f = std::move(std::get<CraneCont_Cons>(_frame));
      uint64_t a0 = _f.a0;
      uint64_t min_rest = std::move(_result);
      if (a0 <= min_rest) {
        _result = std::move(a0);
      } else {
        _result = std::move(min_rest);
      }
    }
  }
  return _result;
}
