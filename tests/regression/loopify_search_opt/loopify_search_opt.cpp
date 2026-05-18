#include "loopify_search_opt.h"

List<uint64_t> LoopifySearchOpt::lis(const List<uint64_t> &l) {
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
              &std::get<typename List<uint64_t>::Cons>((*_write)->v_mut()).l;
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

List<uint64_t> LoopifySearchOpt::longest_run_fuel(uint64_t fuel,
                                                  List<uint64_t> current,
                                                  List<uint64_t> best,
                                                  const List<uint64_t> &l) {
  const List<uint64_t> *_loop_l = &l;
  List<uint64_t> _loop_best = std::move(best);
  List<uint64_t> _loop_current = std::move(current);
  uint64_t _loop_fuel = std::move(fuel);
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
                _loop_current.v_mut())) {
          _loop_l = a1.get();
          _loop_current = List<uint64_t>::cons(a0, List<uint64_t>::nil());
          _loop_fuel = fuel_;
        } else {
          auto &[a00, a10] =
              std::get<typename List<uint64_t>::Cons>(_loop_current.v_mut());
          if (a0 == std::move(a00)) {
            _loop_l = a1.get();
            _loop_current = List<uint64_t>::cons(a0, _loop_current);
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
            _loop_l = a1.get();
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
    const List<std::pair<uint64_t, uint64_t>>
        &items) { /// _Enter: captures varying parameters for each recursive
                  /// call.

  struct _Enter {
    const List<std::pair<uint64_t, uint64_t>> *items;
    uint64_t capacity;
    uint64_t fuel;
  };

  /// _After2: saves [a1, capacity, fuel_, value], dispatches next recursive
  /// call.
  struct _After2 {
    const List<std::pair<uint64_t, uint64_t>> *a1;
    uint64_t capacity;
    uint64_t fuel_;
    uint64_t value;
  };

  /// _Combine1: receives partial results, combines with _result from final
  /// call.
  struct _Combine1 {
    uint64_t _result;
    uint64_t value;
  };

  using _Frame = std::variant<_Enter, _After2, _Combine1>;
  uint64_t _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&items, capacity, fuel});
  /// Loopified knapsack_fuel: _Enter -> _After2 -> _Combine1.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
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
          const uint64_t &weight = a0.first;
          const uint64_t &value = a0.second;
          if (capacity < weight) {
            _stack.emplace_back(_Enter{a1.get(), capacity, fuel_});
          } else {
            _stack.emplace_back(_After2{a1.get(), capacity, fuel_, value});
            _stack.emplace_back(_Enter{
                a1.get(),
                (((capacity - weight) > capacity ? 0 : (capacity - weight))),
                fuel_});
          }
        }
      }
    } else if (std::holds_alternative<_After2>(_frame)) {
      auto _f = std::move(std::get<_After2>(_frame));
      _stack.emplace_back(_Combine1{_result, _f.value});
      _stack.emplace_back(_Enter{_f.a1, _f.capacity, _f.fuel_});
    } else {
      auto _f = std::move(std::get<_Combine1>(_frame));
      _result = std::max(_result, (_f.value + _f._result));
    }
  }
  return _result;
}

uint64_t
LoopifySearchOpt::knapsack(uint64_t capacity,
                           const List<std::pair<uint64_t, uint64_t>> &items) {
  return knapsack_fuel((items.length() * capacity), capacity, items);
}

bool LoopifySearchOpt::subset_sum_fuel(
    uint64_t fuel, uint64_t target,
    const List<uint64_t>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<uint64_t> *l;
    uint64_t target;
    uint64_t fuel;
  };

  /// _After2: saves [a1, target, fuel_], dispatches next recursive call.
  struct _After2 {
    const List<uint64_t> *a1;
    uint64_t target;
    uint64_t fuel_;
  };

  /// _Combine1: receives partial results, combines with _result from final
  /// call.
  struct _Combine1 {
    bool _result;
  };

  using _Frame = std::variant<_Enter, _After2, _Combine1>;
  bool _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l, target, fuel});
  /// Loopified subset_sum_fuel: _Enter -> _After2 -> _Combine1.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
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
            _stack.emplace_back(_Enter{a1.get(), target, fuel_});
          } else {
            _stack.emplace_back(_After2{a1.get(), target, fuel_});
            _stack.emplace_back(
                _Enter{a1.get(), (((target - a0) > target ? 0 : (target - a0))),
                       fuel_});
          }
        }
      }
    } else if (std::holds_alternative<_After2>(_frame)) {
      auto _f = std::move(std::get<_After2>(_frame));
      _stack.emplace_back(_Combine1{_result});
      _stack.emplace_back(_Enter{_f.a1, _f.target, _f.fuel_});
    } else {
      auto _f = std::move(std::get<_Combine1>(_frame));
      _result = (_result || _f._result);
    }
  }
  return _result;
}

bool LoopifySearchOpt::subset_sum(uint64_t target, const List<uint64_t> &l) {
  return subset_sum_fuel((l.length() * target), target, l);
}

std::pair<uint64_t, uint64_t> LoopifySearchOpt::majority(
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
  List<uint64_t> _loop_l = l;
  uint64_t _loop_fuel = std::move(fuel);
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
          if (std::holds_alternative<typename List<uint64_t>::Nil>(
                  _loop_l.v())) {
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
          auto nth_impl = [](auto &_self_nth, uint64_t n,
                             const List<uint64_t> &xs) -> uint64_t {
            if (n <= 0) {
              if (std::holds_alternative<typename List<uint64_t>::Nil>(
                      xs.v())) {
                return UINT64_C(0);
              } else {
                const auto &[a01, a11] =
                    std::get<typename List<uint64_t>::Cons>(xs.v());
                return a01;
              }
            } else {
              uint64_t n_ = n - 1;
              if (std::holds_alternative<typename List<uint64_t>::Nil>(
                      xs.v())) {
                return UINT64_C(0);
              } else {
                const auto &[a02, a12] =
                    std::get<typename List<uint64_t>::Cons>(xs.v());
                return _self_nth(_self_nth, n_, *a12);
              }
            }
          };
          auto nth = [&](uint64_t n, const List<uint64_t> &xs) -> uint64_t {
            return nth_impl(nth_impl, n, xs);
          };
          mid_val = nth(mid, _loop_l);
          List<uint64_t> left;
          auto take_impl = [](auto &_self_take, uint64_t n,
                              const List<uint64_t> &xs) -> List<uint64_t> {
            if (n <= 0) {
              return List<uint64_t>::nil();
            } else {
              uint64_t n_ = n - 1;
              if (std::holds_alternative<typename List<uint64_t>::Nil>(
                      xs.v())) {
                return List<uint64_t>::nil();
              } else {
                const auto &[a03, a13] =
                    std::get<typename List<uint64_t>::Cons>(xs.v());
                return List<uint64_t>::cons(a03,
                                            _self_take(_self_take, n_, *a13));
              }
            }
          };
          auto take = [&](uint64_t n,
                          const List<uint64_t> &xs) -> List<uint64_t> {
            return take_impl(take_impl, n, xs);
          };
          left = take(mid, _loop_l);
          List<uint64_t> right;
          auto drop_impl = [](auto &_self_drop, uint64_t n,
                              List<uint64_t> xs) -> List<uint64_t> {
            if (n <= 0) {
              return xs;
            } else {
              uint64_t n_ = n - 1;
              if (std::holds_alternative<typename List<uint64_t>::Nil>(
                      xs.v_mut())) {
                return List<uint64_t>::nil();
              } else {
                auto &[a04, a14] =
                    std::get<typename List<uint64_t>::Cons>(xs.v_mut());
                return _self_drop(_self_drop, n_, *a14);
              }
            }
          };
          auto drop = [&](uint64_t n, List<uint64_t> xs) -> List<uint64_t> {
            return drop_impl(drop_impl, n, xs);
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
