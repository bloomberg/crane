#include "loopify_search_opt.h"

List<uint64_t> LoopifySearchOpt::lis(const List<uint64_t> &l) {
  // Builds the result front to back: _write points at the empty tail the next
  // cell fills.
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
        (_write ? *(*_write =
                        std::make_shared<List<uint64_t>>(std::move(_value)))
                : _root.emplace(std::move(_value)));
        break;
      } else {
        const auto &[a00, _] =
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

List<uint64_t>
LoopifySearchOpt::longest_run_fuel(uint64_t fuel, const List<uint64_t> &current,
                                   List<uint64_t> best,
                                   const List<uint64_t> &l) {
  // Loop replaces the tail recursion: each recursive call updates the loop
  // variables.
  const List<uint64_t> *_loop_l = &l;
  List<uint64_t> _loop_best = std::move(best);
  List<uint64_t> _loop_current = current;
  uint64_t _loop_fuel = fuel;
  while (true) {
    if (_loop_fuel <= 0) {
      return _loop_best;
    } else {
      uint64_t fuel_ = _loop_fuel - 1;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l->v())) {
        uint64_t len_curr = _loop_current.length();
        uint64_t len_best = _loop_best.length();
        if (len_best < len_curr) {
          return _loop_current;
        } else {
          return _loop_best;
        }
      } else {
        const auto &[a0, a1] =
            std::get<typename List<uint64_t>::Cons>(_loop_l->v());
        if (std::holds_alternative<typename List<uint64_t>::Nil>(
                _loop_current.v())) {
          _loop_l = crane_raw(a1);
          _loop_current = List<uint64_t>::cons(a0, List<uint64_t>::nil());
          _loop_fuel = fuel_;
        } else {
          const auto &[a00, _] =
              std::get<typename List<uint64_t>::Cons>(_loop_current.v());
          if (a0 == a00) {
            _loop_l = crane_raw(a1);
            _loop_current = List<uint64_t>::cons(a0, std::move(_loop_current));
            _loop_fuel = fuel_;
          } else {
            uint64_t len_curr = _loop_current.length();
            uint64_t len_best = _loop_best.length();
            List<uint64_t> new_best;
            if (len_best < len_curr) {
              new_best = _loop_current;
            } else {
              new_best = std::move(_loop_best);
            }
            _loop_l = crane_raw(a1);
            _loop_best = std::move(new_best);
            _loop_current = List<uint64_t>::cons(a0, List<uint64_t>::nil());
            _loop_fuel = fuel_;
          }
        }
      }
    }
  }
}

List<uint64_t> LoopifySearchOpt::longest_run(const List<uint64_t> &l) {
  return longest_run_fuel(l.length(), List<uint64_t>::nil(),
                          List<uint64_t>::nil(), l);
}

uint64_t LoopifySearchOpt::knapsack_fuel(
    uint64_t fuel, uint64_t capacity,
    const List<std::pair<uint64_t, uint64_t>> &items) {
  // Explicit stack replaces the non-tail recursion of knapsack_fuel: _call
  // frames are pending calls, _after frames resume a caller.
  struct _call {
    const List<std::pair<uint64_t, uint64_t>> *items;
    uint64_t capacity;
    uint64_t fuel;
  };

  struct _after_knapsack_fuel_in_false {
    uint64_t capacity;
    uint64_t fuel_;
    const List<std::pair<uint64_t, uint64_t>> *a1;
    uint64_t weight;
    uint64_t value;
  };

  struct _after_knapsack_fuel_in_false_2 {
    uint64_t value;
    uint64_t _tmp2;
  };

  using _frame = std::variant<_call, _after_knapsack_fuel_in_false,
                              _after_knapsack_fuel_in_false_2>;
  uint64_t _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&items, capacity, fuel});
  while (!_stack.empty()) {
    _frame _popped = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      const List<std::pair<uint64_t, uint64_t>> &items = *_f.items;
      uint64_t capacity = _f.capacity;
      uint64_t fuel = _f.fuel;
      if (fuel <= 0) {
        _result = UINT64_C(0);
      } else {
        uint64_t fuel_ = fuel - 1;
        if (std::holds_alternative<
                typename List<std::pair<uint64_t, uint64_t>>::Nil>(items.v())) {
          _result = UINT64_C(0);
        } else {
          const auto &[a0, a1] =
              std::get<typename List<std::pair<uint64_t, uint64_t>>::Cons>(
                  items.v());
          const auto &[weight, value] = a0;
          if (capacity < weight) {
            _stack.emplace_back(_call{crane_raw(a1), capacity, fuel_});
          } else {
            _stack.emplace_back(_after_knapsack_fuel_in_false{
                capacity, fuel_, crane_raw(a1), weight, value});
            _stack.emplace_back(_call{crane_raw(a1), capacity, fuel_});
          }
        }
      }
    } else if (std::holds_alternative<_after_knapsack_fuel_in_false>(_popped)) {
      auto _f = std::move(std::get<_after_knapsack_fuel_in_false>(_popped));
      uint64_t capacity = _f.capacity;
      uint64_t fuel_ = _f.fuel_;
      const List<std::pair<uint64_t, uint64_t>> &a1 = *_f.a1;
      uint64_t weight = _f.weight;
      uint64_t value = _f.value;
      _stack.emplace_back(
          _after_knapsack_fuel_in_false_2{value, std::move(_result)});
      _stack.emplace_back(_call{
          &a1, (((capacity - weight) > capacity ? 0 : (capacity - weight))),
          fuel_});
    } else {
      auto _f = std::move(std::get<_after_knapsack_fuel_in_false_2>(_popped));
      uint64_t value = _f.value;
      _result = std::max(_f._tmp2, (value + std::move(_result)));
    }
  }
  return _result;
}

uint64_t
LoopifySearchOpt::knapsack(uint64_t capacity,
                           const List<std::pair<uint64_t, uint64_t>> &items) {
  return knapsack_fuel((items.length() * capacity), capacity, items);
}

bool LoopifySearchOpt::subset_sum_fuel(uint64_t fuel, uint64_t target,
                                       const List<uint64_t> &l) {
  // Explicit stack replaces the non-tail recursion of subset_sum_fuel: _call
  // frames are pending calls, _after frames resume a caller.
  struct _call {
    const List<uint64_t> *l;
    uint64_t target;
    uint64_t fuel;
  };

  struct _after_subset_sum_fuel_in_false {
    uint64_t target;
    uint64_t fuel_;
    uint64_t a0;
    const List<uint64_t> *a1;
  };

  struct _after_subset_sum_fuel_in_false_2 {
    bool _tmp2;
  };

  using _frame = std::variant<_call, _after_subset_sum_fuel_in_false,
                              _after_subset_sum_fuel_in_false_2>;
  bool _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&l, target, fuel});
  while (!_stack.empty()) {
    _frame _popped = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      const List<uint64_t> &l = *_f.l;
      uint64_t target = _f.target;
      uint64_t fuel = _f.fuel;
      if (fuel <= 0) {
        _result = false;
      } else {
        uint64_t fuel_ = fuel - 1;
        if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
          _result = target == UINT64_C(0);
        } else {
          const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
          if (target < a0) {
            _stack.emplace_back(_call{crane_raw(a1), target, fuel_});
          } else {
            _stack.emplace_back(_after_subset_sum_fuel_in_false{
                target, fuel_, a0, crane_raw(a1)});
            _stack.emplace_back(_call{crane_raw(a1), target, fuel_});
          }
        }
      }
    } else if (std::holds_alternative<_after_subset_sum_fuel_in_false>(_popped)) {
      auto _f = std::move(std::get<_after_subset_sum_fuel_in_false>(_popped));
      uint64_t target = _f.target;
      uint64_t fuel_ = _f.fuel_;
      uint64_t a0 = _f.a0;
      const List<uint64_t> &a1 = *_f.a1;
      _stack.emplace_back(_after_subset_sum_fuel_in_false_2{std::move(_result)});
      _stack.emplace_back(
          _call{&a1, (((target - a0) > target ? 0 : (target - a0))), fuel_});
    } else {
      auto _f = std::move(std::get<_after_subset_sum_fuel_in_false_2>(_popped));
      _result = (_f._tmp2 || std::move(_result));
    }
  }
  return _result;
}

bool LoopifySearchOpt::subset_sum(uint64_t target, const List<uint64_t> &l) {
  return subset_sum_fuel((l.length() * target), target, l);
}

std::pair<uint64_t, uint64_t>
LoopifySearchOpt::majority(const List<uint64_t> &l) {
  // Explicit stack replaces the non-tail recursion of majority: _call frames
  // are pending calls, _after frames resume a caller.
  struct _call {
    const List<uint64_t> *l;
  };

  struct _after_majority_in_Cons {
    uint64_t a0;
  };

  using _frame = std::variant<_call, _after_majority_in_Cons>;
  std::pair<uint64_t, uint64_t> _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&l});
  while (!_stack.empty()) {
    _frame _popped = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      const List<uint64_t> &l = *_f.l;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
        _result = std::make_pair(UINT64_C(0), UINT64_C(0));
      } else {
        const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
        _stack.emplace_back(_after_majority_in_Cons{a0});
        _stack.emplace_back(_call{crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<_after_majority_in_Cons>(_popped));
      uint64_t a0 = _f.a0;
      std::pair<uint64_t, uint64_t> _tmp1 = std::move(_result);
      const auto &[cand, count] = _tmp1;
      if (a0 == cand) {
        _result = std::make_pair(cand, (count + UINT64_C(1)));
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

bool LoopifySearchOpt::binary_search_fuel(uint64_t fuel, uint64_t target,
                                          const List<uint64_t> &l) {
  // Loop replaces the tail recursion: each recursive call updates the loop
  // variables.
  List<uint64_t> _loop_l = l;
  uint64_t _loop_fuel = fuel;
  while (true) {
    if (_loop_fuel <= 0) {
      return false;
    } else {
      uint64_t fuel_ = _loop_fuel - 1;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l.v())) {
        return false;
      } else {
        uint64_t len = _loop_l.length();
        if (len <= UINT64_C(1)) {
          if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l.v())) {
            return false;
          } else {
            const auto &[a00, a10] =
                std::get<typename List<uint64_t>::Cons>(_loop_l.v());
            auto &&_sv = *a10;
            if (std::holds_alternative<typename List<uint64_t>::Nil>(_sv.v())) {
              return a00 == target;
            } else {
              return false;
            }
          }
        } else {
          uint64_t mid = (UINT64_C(2) ? len / UINT64_C(2) : 0);
          uint64_t mid_val;
          auto nth = [](uint64_t n, const List<uint64_t> &xs) -> uint64_t {
            // Loop replaces the tail recursion: each recursive call updates the
            // loop variables.
            const List<uint64_t> *_loop_xs = &xs;
            uint64_t _loop_n = n;
            while (true) {
              if (_loop_n <= 0) {
                if (std::holds_alternative<typename List<uint64_t>::Nil>(
                        _loop_xs->v())) {
                  return UINT64_C(0);
                } else {
                  const auto &[a01, _] =
                      std::get<typename List<uint64_t>::Cons>(_loop_xs->v());
                  return std::move(a01);
                }
              } else {
                uint64_t n_ = _loop_n - 1;
                if (std::holds_alternative<typename List<uint64_t>::Nil>(
                        _loop_xs->v())) {
                  return UINT64_C(0);
                } else {
                  const auto &[_, a12] =
                      std::get<typename List<uint64_t>::Cons>(_loop_xs->v());
                  _loop_xs = crane_raw(a12);
                  _loop_n = n_;
                }
              }
            }
          };
          mid_val = nth(mid, _loop_l);
          List<uint64_t> left;
          auto take =
              [&](uint64_t n, const List<uint64_t> &xs) -> List<uint64_t> {
                // Explicit stack replaces the non-tail recursion of take: _call
                // frames are pending calls, _after frames resume a caller.
                struct _call {
                  const List<uint64_t> *xs;
                  uint64_t n;
                };

                struct _after_take_in_Cons {
                  uint64_t a03;
                };

                using _frame = std::variant<_call, _after_take_in_Cons>;
                List<uint64_t> _result{};
                crane::small_vector<_frame> _stack;
                _stack.emplace_back(_call{&xs, n});
                while (!_stack.empty()) {
                  _frame _popped = std::move(_stack.back());
                  _stack.pop_back();
                  if (std::holds_alternative<_call>(_popped)) {
                    auto _f = std::move(std::get<_call>(_popped));
                    const List<uint64_t> &xs = *_f.xs;
                    uint64_t n = _f.n;
                    if (n <= 0) {
                      _result = List<uint64_t>::nil();
                    } else {
                      uint64_t n_ = n - 1;
                      if (std::holds_alternative<typename List<uint64_t>::Nil>(
                              xs.v())) {
                        _result = List<uint64_t>::nil();
                      } else {
                        const auto &[a03, a13] =
                            std::get<typename List<uint64_t>::Cons>(xs.v());
                        _stack.emplace_back(_after_take_in_Cons{a03});
                        _stack.emplace_back(_call{crane_raw(a13), n_});
                      }
                    }
                  } else {
                    auto _f = std::move(std::get<_after_take_in_Cons>(_popped));
                    uint64_t a03 = _f.a03;
                    _result = List<uint64_t>::cons(a03, std::move(_result));
                  }
                }
                return _result;
              };
          left = take(mid, _loop_l);
          List<uint64_t> right;
          auto drop =
              [](uint64_t n, const List<uint64_t> &xs) -> List<uint64_t> {
                // Loop replaces the tail recursion: each recursive call updates
                // the loop variables.
                const List<uint64_t> *_loop_xs = &xs;
                uint64_t _loop_n = n;
                while (true) {
                  if (_loop_n <= 0) {
                    return *_loop_xs;
                  } else {
                    uint64_t n_ = _loop_n - 1;
                    if (std::holds_alternative<typename List<uint64_t>::Nil>(
                            _loop_xs->v())) {
                      return List<uint64_t>::nil();
                    } else {
                      const auto &[_, a14] = std::get<
                          typename List<uint64_t>::Cons>(_loop_xs->v());
                      _loop_xs = crane_raw(a14);
                      _loop_n = n_;
                    }
                  }
                }
              };
          right = drop((mid + UINT64_C(1)), _loop_l);
          if (target < mid_val) {
            _loop_l = std::move(left);
            _loop_fuel = fuel_;
          } else {
            if (mid_val < target) {
              _loop_l = std::move(right);
              _loop_fuel = fuel_;
            } else {
              return true;
            }
          }
        }
      }
    }
  }
}

bool LoopifySearchOpt::binary_search(uint64_t target, const List<uint64_t> &l) {
  return binary_search_fuel(l.length(), target, l);
}
