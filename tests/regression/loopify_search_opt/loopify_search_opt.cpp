#include <loopify_search_opt.h>

#include <algorithm>
#include <functional>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

std::shared_ptr<List<unsigned int>>
LoopifySearchOpt::lis(const std::shared_ptr<List<unsigned int>> &l) {
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
      const auto &[d_a0, d_a1] =
          std::get<typename List<unsigned int>::Cons>(_loop_l->v());
      if (std::holds_alternative<typename List<unsigned int>::Nil>(d_a1->v())) {
        if (_last) {
          std::get<typename List<unsigned int>::Cons>(_last->v_mut()).d_a1 =
              List<unsigned int>::cons(d_a0, List<unsigned int>::nil());
        } else {
          _head = List<unsigned int>::cons(d_a0, List<unsigned int>::nil());
        }
        _continue = false;
      } else {
        const auto &[d_a00, d_a10] =
            std::get<typename List<unsigned int>::Cons>(d_a1->v());
        if (d_a0 < d_a00) {
          auto _cell = List<unsigned int>::cons(d_a0, nullptr);
          if (_last) {
            std::get<typename List<unsigned int>::Cons>(_last->v_mut()).d_a1 =
                _cell;
          } else {
            _head = _cell;
          }
          _last = _cell;
          _loop_l = d_a1;
          continue;
        } else {
          _loop_l = d_a1;
          continue;
        }
      }
    }
  }
  return _head;
}

std::shared_ptr<List<unsigned int>> LoopifySearchOpt::longest_run_fuel(
    const unsigned int fuel, std::shared_ptr<List<unsigned int>> current,
    std::shared_ptr<List<unsigned int>> best,
    const std::shared_ptr<List<unsigned int>> &l) {
  std::shared_ptr<List<unsigned int>> _result;
  std::shared_ptr<List<unsigned int>> _loop_l = l;
  std::shared_ptr<List<unsigned int>> _loop_best = best;
  std::shared_ptr<List<unsigned int>> _loop_current = current;
  unsigned int _loop_fuel = fuel;
  bool _continue = true;
  while (_continue) {
    if (_loop_fuel <= 0) {
      _result = std::move(_loop_best);
      _continue = false;
    } else {
      unsigned int fuel_ = _loop_fuel - 1;
      if (std::holds_alternative<typename List<unsigned int>::Nil>(
              _loop_l->v())) {
        unsigned int len_curr = _loop_current->length();
        unsigned int len_best = _loop_best->length();
        if (len_best < len_curr) {
          _result = std::move(_loop_current);
          _continue = false;
        } else {
          _result = std::move(_loop_best);
          _continue = false;
        }
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<unsigned int>::Cons>(_loop_l->v());
        if (std::holds_alternative<typename List<unsigned int>::Nil>(
                _loop_current->v())) {
          std::shared_ptr<List<unsigned int>> _next_l = d_a1;
          std::shared_ptr<List<unsigned int>> _next_best =
              std::move(_loop_best);
          std::shared_ptr<List<unsigned int>> _next_current =
              List<unsigned int>::cons(d_a0, List<unsigned int>::nil());
          unsigned int _next_fuel = fuel_;
          _loop_l = std::move(_next_l);
          _loop_best = std::move(_next_best);
          _loop_current = std::move(_next_current);
          _loop_fuel = std::move(_next_fuel);
        } else {
          const auto &[d_a00, d_a10] =
              std::get<typename List<unsigned int>::Cons>(_loop_current->v());
          if (d_a0 == d_a00) {
            std::shared_ptr<List<unsigned int>> _next_l = d_a1;
            std::shared_ptr<List<unsigned int>> _next_best =
                std::move(_loop_best);
            std::shared_ptr<List<unsigned int>> _next_current =
                List<unsigned int>::cons(d_a0, _loop_current);
            unsigned int _next_fuel = fuel_;
            _loop_l = std::move(_next_l);
            _loop_best = std::move(_next_best);
            _loop_current = std::move(_next_current);
            _loop_fuel = std::move(_next_fuel);
          } else {
            unsigned int len_curr = _loop_current->length();
            unsigned int len_best = _loop_best->length();
            std::shared_ptr<List<unsigned int>> new_best;
            if (len_best < len_curr) {
              new_best = std::move(_loop_current);
            } else {
              new_best = std::move(_loop_best);
            }
            std::shared_ptr<List<unsigned int>> _next_l = d_a1;
            std::shared_ptr<List<unsigned int>> _next_best =
                std::move(new_best);
            std::shared_ptr<List<unsigned int>> _next_current =
                List<unsigned int>::cons(d_a0, List<unsigned int>::nil());
            unsigned int _next_fuel = fuel_;
            _loop_l = std::move(_next_l);
            _loop_best = std::move(_next_best);
            _loop_current = std::move(_next_current);
            _loop_fuel = std::move(_next_fuel);
          }
        }
      }
    }
  }
  return _result;
}

std::shared_ptr<List<unsigned int>>
LoopifySearchOpt::longest_run(const std::shared_ptr<List<unsigned int>> &l) {
  return longest_run_fuel(l->length(), List<unsigned int>::nil(),
                          List<unsigned int>::nil(), l);
}

__attribute__((pure)) unsigned int LoopifySearchOpt::knapsack_fuel(
    const unsigned int fuel, const unsigned int capacity,
    const std::shared_ptr<List<std::pair<unsigned int, unsigned int>>> &items) {
  struct _Enter {
    const std::shared_ptr<List<std::pair<unsigned int, unsigned int>>> items;
    const unsigned int capacity;
    const unsigned int fuel;
  };

  struct _Call1 {
    std::shared_ptr<List<std::pair<unsigned int, unsigned int>>> _s0;
    const unsigned int _s1;
    unsigned int _s2;
    unsigned int _s3;
  };

  struct _Call2 {
    unsigned int _s0;
    unsigned int _s1;
  };

  using _Frame = std::variant<_Enter, _Call1, _Call2>;
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
        unsigned int fuel_ = fuel - 1;
        if (std::holds_alternative<
                typename List<std::pair<unsigned int, unsigned int>>::Nil>(
                items->v())) {
          _result = 0u;
        } else {
          const auto &[d_a0, d_a1] = std::get<
              typename List<std::pair<unsigned int, unsigned int>>::Cons>(
              items->v());
          const unsigned int &weight = d_a0.first;
          const unsigned int &value = d_a0.second;
          if (capacity < weight) {
            _stack.emplace_back(_Enter{d_a1, capacity, fuel_});
          } else {
            _stack.emplace_back(_Call1{d_a1, capacity, fuel_, value});
            _stack.emplace_back(_Enter{
                d_a1,
                (((capacity - weight) > capacity ? 0 : (capacity - weight))),
                fuel_});
          }
        }
      }
    } else if (std::holds_alternative<_Call1>(_frame)) {
      const auto &_f = std::get<_Call1>(_frame);
      _stack.emplace_back(_Call2{_result, _f._s3});
      _stack.emplace_back(_Enter{_f._s0, _f._s1, _f._s2});
    } else {
      const auto &_f = std::get<_Call2>(_frame);
      _result = std::max(_result, (_f._s1 + _f._s0));
    }
  }
  return _result;
}

__attribute__((pure)) unsigned int LoopifySearchOpt::knapsack(
    const unsigned int capacity,
    const std::shared_ptr<List<std::pair<unsigned int, unsigned int>>> &items) {
  return knapsack_fuel((items->length() * capacity), capacity, items);
}

__attribute__((pure)) bool LoopifySearchOpt::subset_sum_fuel(
    const unsigned int fuel, const unsigned int target,
    const std::shared_ptr<List<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<List<unsigned int>> l;
    const unsigned int target;
    const unsigned int fuel;
  };

  struct _Call1 {
    std::shared_ptr<List<unsigned int>> _s0;
    const unsigned int _s1;
    unsigned int _s2;
  };

  struct _Call2 {
    bool _s0;
  };

  using _Frame = std::variant<_Enter, _Call1, _Call2>;
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
        unsigned int fuel_ = fuel - 1;
        if (std::holds_alternative<typename List<unsigned int>::Nil>(l->v())) {
          _result = target == 0u;
        } else {
          const auto &[d_a0, d_a1] =
              std::get<typename List<unsigned int>::Cons>(l->v());
          if (target < d_a0) {
            _stack.emplace_back(_Enter{d_a1, target, fuel_});
          } else {
            _stack.emplace_back(_Call1{d_a1, target, fuel_});
            _stack.emplace_back(
                _Enter{d_a1, (((target - d_a0) > target ? 0 : (target - d_a0))),
                       fuel_});
          }
        }
      }
    } else if (std::holds_alternative<_Call1>(_frame)) {
      const auto &_f = std::get<_Call1>(_frame);
      _stack.emplace_back(_Call2{_result});
      _stack.emplace_back(_Enter{_f._s0, _f._s1, _f._s2});
    } else {
      const auto &_f = std::get<_Call2>(_frame);
      _result = (_result || _f._s0);
    }
  }
  return _result;
}

__attribute__((pure)) bool
LoopifySearchOpt::subset_sum(const unsigned int target,
                             const std::shared_ptr<List<unsigned int>> &l) {
  return subset_sum_fuel((l->length() * target), target, l);
}

__attribute__((pure)) std::pair<unsigned int, unsigned int>
LoopifySearchOpt::majority(const std::shared_ptr<List<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<List<unsigned int>> l;
  };

  struct _Call1 {
    unsigned int _s0;
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
        const auto &[d_a0, d_a1] =
            std::get<typename List<unsigned int>::Cons>(l->v());
        _stack.emplace_back(_Call1{d_a0});
        _stack.emplace_back(_Enter{d_a1});
      }
    } else {
      const auto &_f = std::get<_Call1>(_frame);
      unsigned int d_a0 = _f._s0;
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

__attribute__((pure)) bool LoopifySearchOpt::binary_search_fuel(
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
      unsigned int fuel_ = _loop_fuel - 1;
      if (std::holds_alternative<typename List<unsigned int>::Nil>(
              _loop_l->v())) {
        _result = false;
        _continue = false;
      } else {
        unsigned int len = _loop_l->length();
        if (len <= 1u) {
          if (std::holds_alternative<typename List<unsigned int>::Nil>(
                  _loop_l->v())) {
            _result = false;
            _continue = false;
          } else {
            const auto &[d_a00, d_a10] =
                std::get<typename List<unsigned int>::Cons>(_loop_l->v());
            if (std::holds_alternative<typename List<unsigned int>::Nil>(
                    d_a10->v())) {
              _result = d_a00 == target;
              _continue = false;
            } else {
              _result = false;
              _continue = false;
            }
          }
        } else {
          unsigned int mid = (2u ? len / 2u : 0);
          unsigned int mid_val;
          std::function<unsigned int(unsigned int,
                                     std::shared_ptr<List<unsigned int>>)>
              nth;
          nth = [](unsigned int n,
                   std::shared_ptr<List<unsigned int>> xs) -> unsigned int {
            unsigned int _result;
            std::shared_ptr<List<unsigned int>> _loop_xs = xs;
            unsigned int _loop_n = n;
            bool _continue = true;
            while (_continue) {
              if (_loop_n <= 0) {
                if (std::holds_alternative<typename List<unsigned int>::Nil>(
                        _loop_xs->v())) {
                  _result = 0u;
                  _continue = false;
                } else {
                  const auto &[d_a01, d_a11] =
                      std::get<typename List<unsigned int>::Cons>(
                          _loop_xs->v());
                  _result = d_a01;
                  _continue = false;
                }
              } else {
                unsigned int n_ = _loop_n - 1;
                if (std::holds_alternative<typename List<unsigned int>::Nil>(
                        _loop_xs->v())) {
                  _result = 0u;
                  _continue = false;
                } else {
                  const auto &[d_a02, d_a12] =
                      std::get<typename List<unsigned int>::Cons>(
                          _loop_xs->v());
                  std::shared_ptr<List<unsigned int>> _next_xs = d_a12;
                  unsigned int _next_n = n_;
                  _loop_xs = std::move(_next_xs);
                  _loop_n = std::move(_next_n);
                }
              }
            }
            return _result;
          };
          mid_val = nth(mid, _loop_l);
          std::shared_ptr<List<unsigned int>> left;
          std::function<std::shared_ptr<List<unsigned int>>(
              unsigned int, std::shared_ptr<List<unsigned int>>)>
              take;
          take = [&](unsigned int n, std::shared_ptr<List<unsigned int>> xs)
              -> std::shared_ptr<List<unsigned int>> {
            struct _Enter {
              std::shared_ptr<List<unsigned int>> xs;
              unsigned int n;
            };
            struct _Call1 {
              unsigned int _s0;
            };
            using _Frame = std::variant<_Enter, _Call1>;
            std::shared_ptr<List<unsigned int>> _result{};
            std::vector<_Frame> _stack;
            _stack.emplace_back(_Enter{xs, n});
            while (!_stack.empty()) {
              _Frame _frame = std::move(_stack.back());
              _stack.pop_back();
              if (std::holds_alternative<_Enter>(_frame)) {
                const auto &_f = std::get<_Enter>(_frame);
                std::shared_ptr<List<unsigned int>> xs = _f.xs;
                unsigned int n = _f.n;
                if (n <= 0) {
                  _result = List<unsigned int>::nil();
                } else {
                  unsigned int n_ = n - 1;
                  if (std::holds_alternative<typename List<unsigned int>::Nil>(
                          xs->v())) {
                    _result = List<unsigned int>::nil();
                  } else {
                    const auto &[d_a03, d_a13] =
                        std::get<typename List<unsigned int>::Cons>(xs->v());
                    _stack.emplace_back(_Call1{d_a03});
                    _stack.emplace_back(_Enter{d_a13, n_});
                  }
                }
              } else {
                const auto &_f = std::get<_Call1>(_frame);
                _result = List<unsigned int>::cons(_f._s0, _result);
              }
            }
            return _result;
          };
          left = take(mid, _loop_l);
          std::shared_ptr<List<unsigned int>> right;
          std::function<std::shared_ptr<List<unsigned int>>(
              unsigned int, std::shared_ptr<List<unsigned int>>)>
              drop;
          drop = [](unsigned int n, std::shared_ptr<List<unsigned int>> xs)
              -> std::shared_ptr<List<unsigned int>> {
            std::shared_ptr<List<unsigned int>> _result;
            std::shared_ptr<List<unsigned int>> _loop_xs = xs;
            unsigned int _loop_n = n;
            bool _continue = true;
            while (_continue) {
              if (_loop_n <= 0) {
                _result = _loop_xs;
                _continue = false;
              } else {
                unsigned int n_ = _loop_n - 1;
                if (std::holds_alternative<typename List<unsigned int>::Nil>(
                        _loop_xs->v()) &&
                    _loop_xs.use_count() == 1) {
                  _result = _loop_xs;
                  _continue = false;
                } else if (std::holds_alternative<
                               typename List<unsigned int>::Nil>(
                               _loop_xs->v())) {
                  _result = List<unsigned int>::nil();
                  _continue = false;
                } else {
                  const auto &[d_a04, d_a14] =
                      std::get<typename List<unsigned int>::Cons>(
                          _loop_xs->v());
                  std::shared_ptr<List<unsigned int>> _next_xs = d_a14;
                  unsigned int _next_n = n_;
                  _loop_xs = std::move(_next_xs);
                  _loop_n = std::move(_next_n);
                }
              }
            }
            return _result;
          };
          right = drop((mid + 1u), _loop_l);
          if (target < mid_val) {
            std::shared_ptr<List<unsigned int>> _next_l = std::move(left);
            unsigned int _next_fuel = fuel_;
            _loop_l = std::move(_next_l);
            _loop_fuel = std::move(_next_fuel);
          } else {
            if (mid_val < target) {
              std::shared_ptr<List<unsigned int>> _next_l = std::move(right);
              unsigned int _next_fuel = fuel_;
              _loop_l = std::move(_next_l);
              _loop_fuel = std::move(_next_fuel);
            } else {
              _result = true;
              _continue = false;
            }
          }
        }
      }
    }
  }
  return _result;
}

__attribute__((pure)) bool
LoopifySearchOpt::binary_search(const unsigned int target,
                                const std::shared_ptr<List<unsigned int>> &l) {
  return binary_search_fuel(l->length(), target, l);
}
