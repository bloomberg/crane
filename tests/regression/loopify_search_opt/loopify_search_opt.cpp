#include <loopify_search_opt.h>

List<unsigned int> LoopifySearchOpt::lis(const List<unsigned int> &l) {
  std::unique_ptr<List<unsigned int>> _head{};
  std::unique_ptr<List<unsigned int>> *_write = &_head;
  const List<unsigned int> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(
            _loop_l->v())) {
      *(_write) =
          std::make_unique<List<unsigned int>>(List<unsigned int>::nil());
      break;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<unsigned int>::Cons>(_loop_l->v());
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
          _loop_l = d_a1.get();
          continue;
        } else {
          _loop_l = d_a1.get();
          continue;
        }
      }
    }
  }
  return std::move(*(_head));
}

List<unsigned int> LoopifySearchOpt::longest_run_fuel(
    const unsigned int fuel, List<unsigned int> current,
    List<unsigned int> best, const List<unsigned int> &l) {
  List<unsigned int> _result;
  const List<unsigned int> *_loop_l = &l;
  List<unsigned int> _loop_best = std::move(best);
  List<unsigned int> _loop_current = std::move(current);
  unsigned int _loop_fuel = fuel;
  while (true) {
    if (_loop_fuel <= 0) {
      _result = std::move(_loop_best);
      break;
    } else {
      unsigned int fuel_ = _loop_fuel - 1;
      if (std::holds_alternative<typename List<unsigned int>::Nil>(
              _loop_l->v())) {
        unsigned int len_curr = _loop_current.length();
        unsigned int len_best = _loop_best.length();
        if (len_best < len_curr) {
          _result = std::move(_loop_current);
          break;
        } else {
          _result = std::move(_loop_best);
          break;
        }
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<unsigned int>::Cons>(_loop_l->v());
        if (std::holds_alternative<typename List<unsigned int>::Nil>(
                _loop_current.v_mut())) {
          _loop_l = d_a1.get();
          _loop_current =
              List<unsigned int>::cons(d_a0, List<unsigned int>::nil());
          _loop_fuel = fuel_;
        } else {
          auto &[d_a00, d_a10] = std::get<typename List<unsigned int>::Cons>(
              _loop_current.v_mut());
          if (d_a0 == d_a00) {
            _loop_l = d_a1.get();
            _loop_current = List<unsigned int>::cons(d_a0, _loop_current);
            _loop_fuel = fuel_;
          } else {
            unsigned int len_curr = _loop_current.length();
            unsigned int len_best = _loop_best.length();
            List<unsigned int> new_best;
            if (len_best < len_curr) {
              new_best = _loop_current;
            } else {
              new_best = std::move(_loop_best);
            }
            _loop_l = d_a1.get();
            _loop_best = std::move(new_best);
            _loop_current =
                List<unsigned int>::cons(d_a0, List<unsigned int>::nil());
            _loop_fuel = fuel_;
          }
        }
      }
    }
  }
  return _result;
}

List<unsigned int> LoopifySearchOpt::longest_run(const List<unsigned int> &l) {
  return longest_run_fuel(l.length(), List<unsigned int>::nil(),
                          List<unsigned int>::nil(), l);
}

unsigned int LoopifySearchOpt::knapsack_fuel(
    const unsigned int fuel, const unsigned int capacity,
    const List<std::pair<unsigned int, unsigned int>>
        &items) { /// _Enter: captures varying parameters for each recursive
                  /// call.

  struct _Enter {
    const List<std::pair<unsigned int, unsigned int>> *items;
    unsigned int capacity;
    unsigned int fuel;
  };

  /// _After2: saves [d_a1, capacity, fuel_, value], dispatches next recursive
  /// call.
  struct _After2 {
    const List<std::pair<unsigned int, unsigned int>> *d_a1;
    unsigned int capacity;
    unsigned int fuel_;
    unsigned int value;
  };

  /// _Combine1: receives partial results, combines with _result from final
  /// call.
  struct _Combine1 {
    unsigned int _result;
    unsigned int value;
  };

  using _Frame = std::variant<_Enter, _After2, _Combine1>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{&items, capacity, fuel});
  /// Loopified knapsack_fuel: _Enter -> _After2 -> _Combine1.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<std::pair<unsigned int, unsigned int>> &items = *(_f.items);
      const unsigned int capacity = _f.capacity;
      const unsigned int fuel = _f.fuel;
      if (fuel <= 0) {
        _result = 0u;
      } else {
        unsigned int fuel_ = fuel - 1;
        if (std::holds_alternative<
                typename List<std::pair<unsigned int, unsigned int>>::Nil>(
                items.v())) {
          _result = 0u;
        } else {
          const auto &[d_a0, d_a1] = std::get<
              typename List<std::pair<unsigned int, unsigned int>>::Cons>(
              items.v());
          const unsigned int &weight = d_a0.first;
          const unsigned int &value = d_a0.second;
          if (capacity < weight) {
            _stack.emplace_back(_Enter{d_a1.get(), capacity, fuel_});
          } else {
            _stack.emplace_back(_After2{d_a1.get(), capacity, fuel_, value});
            _stack.emplace_back(_Enter{
                d_a1.get(),
                (((capacity - weight) > capacity ? 0 : (capacity - weight))),
                fuel_});
          }
        }
      }
    } else if (std::holds_alternative<_After2>(_frame)) {
      auto _f = std::move(std::get<_After2>(_frame));
      _stack.emplace_back(_Combine1{_result, _f.value});
      _stack.emplace_back(_Enter{_f.d_a1, _f.capacity, _f.fuel_});
    } else {
      auto _f = std::move(std::get<_Combine1>(_frame));
      _result = std::max(_result, (_f.value + _f._result));
    }
  }
  return _result;
}

unsigned int LoopifySearchOpt::knapsack(
    const unsigned int capacity,
    const List<std::pair<unsigned int, unsigned int>> &items) {
  return knapsack_fuel((items.length() * capacity), capacity, items);
}

bool LoopifySearchOpt::subset_sum_fuel(
    const unsigned int fuel, const unsigned int target,
    const List<unsigned int>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<unsigned int> *l;
    unsigned int target;
    unsigned int fuel;
  };

  /// _After2: saves [d_a1, target, fuel_], dispatches next recursive call.
  struct _After2 {
    const List<unsigned int> *d_a1;
    unsigned int target;
    unsigned int fuel_;
  };

  /// _Combine1: receives partial results, combines with _result from final
  /// call.
  struct _Combine1 {
    bool _result;
  };

  using _Frame = std::variant<_Enter, _After2, _Combine1>;
  bool _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{&l, target, fuel});
  /// Loopified subset_sum_fuel: _Enter -> _After2 -> _Combine1.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<unsigned int> &l = *(_f.l);
      const unsigned int target = _f.target;
      const unsigned int fuel = _f.fuel;
      if (fuel <= 0) {
        _result = false;
      } else {
        unsigned int fuel_ = fuel - 1;
        if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
          _result = target == 0u;
        } else {
          const auto &[d_a0, d_a1] =
              std::get<typename List<unsigned int>::Cons>(l.v());
          if (target < d_a0) {
            _stack.emplace_back(_Enter{d_a1.get(), target, fuel_});
          } else {
            _stack.emplace_back(_After2{d_a1.get(), target, fuel_});
            _stack.emplace_back(_Enter{
                d_a1.get(), (((target - d_a0) > target ? 0 : (target - d_a0))),
                fuel_});
          }
        }
      }
    } else if (std::holds_alternative<_After2>(_frame)) {
      auto _f = std::move(std::get<_After2>(_frame));
      _stack.emplace_back(_Combine1{_result});
      _stack.emplace_back(_Enter{_f.d_a1, _f.target, _f.fuel_});
    } else {
      auto _f = std::move(std::get<_Combine1>(_frame));
      _result = (_result || _f._result);
    }
  }
  return _result;
}

bool LoopifySearchOpt::subset_sum(const unsigned int target,
                                  const List<unsigned int> &l) {
  return subset_sum_fuel((l.length() * target), target, l);
}

std::pair<unsigned int, unsigned int> LoopifySearchOpt::majority(
    const List<unsigned int>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<unsigned int> *l;
  };

  /// _Cont_Cons: saves [d_a0], resumes after recursive call, then processes
  /// rest.
  struct _Cont_Cons {
    unsigned int d_a0;
  };

  using _Frame = std::variant<_Enter, _Cont_Cons>;
  std::pair<unsigned int, unsigned int> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{&l});
  /// Loopified majority: _Enter -> _Cont_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<unsigned int> &l = *(_f.l);
      if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
        _result = std::make_pair(0u, 0u);
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<unsigned int>::Cons>(l.v());
        _stack.emplace_back(_Cont_Cons{d_a0});
        _stack.emplace_back(_Enter{d_a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Cont_Cons>(_frame));
      unsigned int d_a0 = _f.d_a0;
      const unsigned int &cand = _result.first;
      const unsigned int &count = _result.second;
      if (d_a0 == cand) {
        _result = std::make_pair(cand, (count + 1u));
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

bool LoopifySearchOpt::binary_search_fuel(const unsigned int fuel,
                                          const unsigned int target,
                                          const List<unsigned int> &l) {
  bool _result;
  List<unsigned int> _loop_l = l;
  unsigned int _loop_fuel = fuel;
  while (true) {
    if (_loop_fuel <= 0) {
      _result = false;
      break;
    } else {
      unsigned int fuel_ = _loop_fuel - 1;
      if (std::holds_alternative<typename List<unsigned int>::Nil>(
              _loop_l.v())) {
        _result = false;
        break;
      } else {
        unsigned int len = _loop_l.length();
        if (len <= 1u) {
          if (std::holds_alternative<typename List<unsigned int>::Nil>(
                  _loop_l.v())) {
            _result = false;
            break;
          } else {
            const auto &[d_a00, d_a10] =
                std::get<typename List<unsigned int>::Cons>(_loop_l.v());
            auto &&_sv = *(d_a10);
            if (std::holds_alternative<typename List<unsigned int>::Nil>(
                    _sv.v())) {
              _result = d_a00 == target;
              break;
            } else {
              _result = false;
              break;
            }
          }
        } else {
          unsigned int mid = (2u ? len / 2u : 0);
          unsigned int mid_val;
          std::function<unsigned int(unsigned int, List<unsigned int>)> nth;
          nth = [](unsigned int n, List<unsigned int> xs) -> unsigned int {
            unsigned int _result;
            List<unsigned int> _loop_xs = std::move(xs);
            unsigned int _loop_n = std::move(n);
            while (true) {
              if (_loop_n <= 0) {
                if (std::holds_alternative<typename List<unsigned int>::Nil>(
                        _loop_xs.v())) {
                  _result = 0u;
                  break;
                } else {
                  const auto &[d_a01, d_a11] =
                      std::get<typename List<unsigned int>::Cons>(_loop_xs.v());
                  _result = d_a01;
                  break;
                }
              } else {
                unsigned int n_ = _loop_n - 1;
                if (std::holds_alternative<typename List<unsigned int>::Nil>(
                        _loop_xs.v())) {
                  _result = 0u;
                  break;
                } else {
                  const auto &[d_a02, d_a12] =
                      std::get<typename List<unsigned int>::Cons>(_loop_xs.v());
                  _loop_xs = std::move(*(d_a12));
                  _loop_n = n_;
                }
              }
            }
            return _result;
          };
          mid_val = nth(mid, _loop_l);
          List<unsigned int> left;
          std::function<List<unsigned int>(unsigned int, List<unsigned int>)>
              take;
          take = [&](unsigned int n,
                     List<unsigned int> xs) -> List<unsigned int> {
            /// _Enter: captures varying parameters for each recursive call.
            struct _Enter {
              List<unsigned int> xs;
              unsigned int n;
            };
            /// _Resume_Cons: saves [d_a03], resumes after recursive call with
            /// _result.
            struct _Resume_Cons {
              unsigned int d_a03;
            };
            using _Frame = std::variant<_Enter, _Resume_Cons>;
            List<unsigned int> _result{};
            std::vector<_Frame> _stack;
            _stack.reserve(16);
            _stack.emplace_back(_Enter{xs, n});
            /// Loopified take: _Enter -> _Resume_Cons.
            while (!_stack.empty()) {
              _Frame _frame = std::move(_stack.back());
              _stack.pop_back();
              if (std::holds_alternative<_Enter>(_frame)) {
                auto _f = std::move(std::get<_Enter>(_frame));
                List<unsigned int> xs = std::move(_f.xs);
                unsigned int n = _f.n;
                if (n <= 0) {
                  _result = List<unsigned int>::nil();
                } else {
                  unsigned int n_ = n - 1;
                  if (std::holds_alternative<typename List<unsigned int>::Nil>(
                          xs.v_mut())) {
                    _result = List<unsigned int>::nil();
                  } else {
                    auto &[d_a03, d_a13] =
                        std::get<typename List<unsigned int>::Cons>(xs.v_mut());
                    _stack.emplace_back(_Resume_Cons{d_a03});
                    _stack.emplace_back(_Enter{std::move(*(d_a13)), n_});
                  }
                }
              } else {
                auto _f = std::move(std::get<_Resume_Cons>(_frame));
                _result = List<unsigned int>::cons(_f.d_a03, _result);
              }
            }
            return _result;
          };
          left = take(mid, _loop_l);
          List<unsigned int> right;
          std::function<List<unsigned int>(unsigned int, List<unsigned int>)>
              drop;
          drop = [](unsigned int n,
                    List<unsigned int> xs) -> List<unsigned int> {
            List<unsigned int> _result;
            List<unsigned int> _loop_xs = std::move(xs);
            unsigned int _loop_n = std::move(n);
            while (true) {
              if (_loop_n <= 0) {
                _result = _loop_xs;
                break;
              } else {
                unsigned int n_ = _loop_n - 1;
                if (std::holds_alternative<typename List<unsigned int>::Nil>(
                        _loop_xs.v_mut())) {
                  _result = List<unsigned int>::nil();
                  break;
                } else {
                  auto &[d_a04, d_a14] =
                      std::get<typename List<unsigned int>::Cons>(
                          _loop_xs.v_mut());
                  _loop_xs = std::move(*(d_a14));
                  _loop_n = n_;
                }
              }
            }
            return _result;
          };
          right = drop((mid + 1u), _loop_l);
          if (target < mid_val) {
            _loop_l = std::move(left);
            _loop_fuel = fuel_;
          } else {
            if (mid_val < target) {
              _loop_l = std::move(right);
              _loop_fuel = fuel_;
            } else {
              _result = true;
              break;
            }
          }
        }
      }
    }
  }
  return _result;
}

bool LoopifySearchOpt::binary_search(const unsigned int target,
                                     const List<unsigned int> &l) {
  return binary_search_fuel(l.length(), target, l);
}
