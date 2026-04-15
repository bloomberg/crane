#include <loopify_sorting.h>

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

/// Consolidated UNIQUE sorting algorithms and related operations.
std::shared_ptr<List<unsigned int>>
LoopifySorting::insert(const unsigned int x,
                       std::shared_ptr<List<unsigned int>> l) {
  std::shared_ptr<List<unsigned int>> _head{};
  std::shared_ptr<List<unsigned int>> _last{};
  std::shared_ptr<List<unsigned int>> _loop_l = l;
  bool _continue = true;
  while (_continue) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(
            _loop_l->v())) {
      if (_last) {
        std::get<typename List<unsigned int>::Cons>(_last->v_mut()).d_a1 =
            List<unsigned int>::cons(x, List<unsigned int>::nil());
      } else {
        _head = List<unsigned int>::cons(x, List<unsigned int>::nil());
      }
      _continue = false;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<unsigned int>::Cons>(_loop_l->v());
      if (x <= d_a0) {
        if (_last) {
          std::get<typename List<unsigned int>::Cons>(_last->v_mut()).d_a1 =
              List<unsigned int>::cons(x, _loop_l);
        } else {
          _head = List<unsigned int>::cons(x, _loop_l);
        }
        _continue = false;
      } else {
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
      }
    }
  }
  return _head;
}

std::shared_ptr<List<unsigned int>>
LoopifySorting::insertion_sort(const std::shared_ptr<List<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<List<unsigned int>> l;
  };

  struct _Call1 {
    unsigned int _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::shared_ptr<List<unsigned int>> _result{};
  std::vector<_Frame> _stack;
  _stack.emplace_back(_Enter{l});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      const auto &_f = std::get<_Enter>(_frame);
      const std::shared_ptr<List<unsigned int>> l = _f.l;
      if (std::holds_alternative<typename List<unsigned int>::Nil>(l->v())) {
        _result = List<unsigned int>::nil();
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<unsigned int>::Cons>(l->v());
        _stack.emplace_back(_Call1{d_a0});
        _stack.emplace_back(_Enter{d_a1});
      }
    } else {
      const auto &_f = std::get<_Call1>(_frame);
      _result = insert(_f._s0, _result);
    }
  }
  return _result;
}

std::shared_ptr<List<unsigned int>>
LoopifySorting::merge_fuel(const unsigned int fuel,
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
            List<unsigned int>::nil();
      } else {
        _head = List<unsigned int>::nil();
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
        const auto &[d_a0, d_a1] =
            std::get<typename List<unsigned int>::Cons>(_loop_l1->v());
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
          const auto &[d_a00, d_a10] =
              std::get<typename List<unsigned int>::Cons>(_loop_l2->v());
          if (d_a0 <= d_a00) {
            auto _cell = List<unsigned int>::cons(d_a0, nullptr);
            if (_last) {
              std::get<typename List<unsigned int>::Cons>(_last->v_mut()).d_a1 =
                  _cell;
            } else {
              _head = _cell;
            }
            _last = _cell;
            std::shared_ptr<List<unsigned int>> _next_l1 = d_a1;
            unsigned int _next_fuel = f;
            _loop_l1 = std::move(_next_l1);
            _loop_fuel = std::move(_next_fuel);
            continue;
          } else {
            auto _cell = List<unsigned int>::cons(d_a00, nullptr);
            if (_last) {
              std::get<typename List<unsigned int>::Cons>(_last->v_mut()).d_a1 =
                  _cell;
            } else {
              _head = _cell;
            }
            _last = _cell;
            std::shared_ptr<List<unsigned int>> _next_l2 = d_a10;
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
LoopifySorting::merge(const std::shared_ptr<List<unsigned int>> &l1,
                      const std::shared_ptr<List<unsigned int>> &l2) {
  return merge_fuel((len_impl<unsigned int>(l1) + len_impl<unsigned int>(l2)),
                    l1, l2);
}

std::shared_ptr<List<unsigned int>>
LoopifySorting::merge_sort_fuel(const unsigned int fuel,
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
          const auto &[d_a0, d_a1] =
              std::get<typename List<unsigned int>::Cons>(l->v());
          if (std::holds_alternative<typename List<unsigned int>::Nil>(
                  d_a1->v())) {
            _result = std::move(l);
          } else {
            auto _cs = split<unsigned int>(l);
            const std::shared_ptr<List<unsigned int>> &l1 = _cs.first;
            const std::shared_ptr<List<unsigned int>> &l2 = _cs.second;
            _stack.emplace_back(_Call1{l1, f});
            _stack.emplace_back(_Enter{l2, f});
          }
        }
      }
    } else if (std::holds_alternative<_Call1>(_frame)) {
      const auto &_f = std::get<_Call1>(_frame);
      _stack.emplace_back(_Call2{_result});
      _stack.emplace_back(_Enter{_f._s0, _f._s1});
    } else {
      const auto &_f = std::get<_Call2>(_frame);
      _result = merge(_result, _f._s0);
    }
  }
  return _result;
}

std::shared_ptr<List<unsigned int>>
LoopifySorting::merge_sort(const std::shared_ptr<List<unsigned int>> &l) {
  return merge_sort_fuel(len_impl<unsigned int>(l), l);
}

__attribute__((pure)) std::pair<std::shared_ptr<List<unsigned int>>,
                                std::shared_ptr<List<unsigned int>>>
LoopifySorting::partition(const unsigned int pivot,
                          const std::shared_ptr<List<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<List<unsigned int>> l;
  };

  struct _Call1 {
    const unsigned int _s0;
    unsigned int _s1;
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
        const auto &[d_a0, d_a1] =
            std::get<typename List<unsigned int>::Cons>(l->v());
        _stack.emplace_back(_Call1{pivot, d_a0});
        _stack.emplace_back(_Enter{d_a1});
      }
    } else {
      const auto &_f = std::get<_Call1>(_frame);
      const unsigned int pivot = _f._s0;
      unsigned int d_a0 = _f._s1;
      const std::shared_ptr<List<unsigned int>> &lo = _result.first;
      const std::shared_ptr<List<unsigned int>> &hi = _result.second;
      if (d_a0 <= pivot) {
        _result = std::make_pair(List<unsigned int>::cons(d_a0, lo), hi);
      } else {
        _result = std::make_pair(lo, List<unsigned int>::cons(d_a0, hi));
      }
    }
  }
  return _result;
}

std::shared_ptr<List<unsigned int>>
LoopifySorting::quicksort_fuel(const unsigned int fuel,
                               std::shared_ptr<List<unsigned int>> l) {
  struct _Enter {
    std::shared_ptr<List<unsigned int>> l;
    const unsigned int fuel;
  };

  struct _Call1 {
    std::shared_ptr<List<unsigned int>> _s0;
    unsigned int _s1;
    unsigned int _s2;
  };

  struct _Call2 {
    std::shared_ptr<List<unsigned int>> _s0;
    unsigned int _s1;
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
          const auto &[d_a0, d_a1] =
              std::get<typename List<unsigned int>::Cons>(l->v());
          auto _cs = partition(d_a0, d_a1);
          const std::shared_ptr<List<unsigned int>> &lo = _cs.first;
          const std::shared_ptr<List<unsigned int>> &hi = _cs.second;
          _stack.emplace_back(_Call1{lo, f, d_a0});
          _stack.emplace_back(_Enter{hi, f});
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
LoopifySorting::quicksort(const std::shared_ptr<List<unsigned int>> &l) {
  return quicksort_fuel(len_impl<unsigned int>(l), l);
}

__attribute__((pure)) bool
LoopifySorting::is_sorted_aux(const unsigned int prev,
                              const std::shared_ptr<List<unsigned int>> &l) {
  bool _result;
  std::shared_ptr<List<unsigned int>> _loop_l = l;
  unsigned int _loop_prev = prev;
  bool _continue = true;
  while (_continue) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(
            _loop_l->v())) {
      _result = true;
      _continue = false;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<unsigned int>::Cons>(_loop_l->v());
      if (_loop_prev <= d_a0) {
        std::shared_ptr<List<unsigned int>> _next_l = d_a1;
        unsigned int _next_prev = d_a0;
        _loop_l = std::move(_next_l);
        _loop_prev = std::move(_next_prev);
      } else {
        _result = false;
        _continue = false;
      }
    }
  }
  return _result;
}

__attribute__((pure)) bool
LoopifySorting::is_sorted(const std::shared_ptr<List<unsigned int>> &l) {
  if (std::holds_alternative<typename List<unsigned int>::Nil>(l->v())) {
    return true;
  } else {
    const auto &[d_a0, d_a1] =
        std::get<typename List<unsigned int>::Cons>(l->v());
    return is_sorted_aux(d_a0, d_a1);
  }
}

/// remove_duplicates removes consecutive duplicates from sorted list.
std::shared_ptr<List<unsigned int>> LoopifySorting::remove_duplicates(
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
        if (d_a0 == d_a00) {
          _loop_l = d_a1;
          continue;
        } else {
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
        }
      }
    }
  }
  return _head;
}

/// uniq_sorted variant that preserves order.
std::shared_ptr<List<unsigned int>>
LoopifySorting::uniq_sorted_aux(const unsigned int prev, const bool seen,
                                const std::shared_ptr<List<unsigned int>> &l) {
  std::shared_ptr<List<unsigned int>> _head{};
  std::shared_ptr<List<unsigned int>> _last{};
  std::shared_ptr<List<unsigned int>> _loop_l = l;
  bool _loop_seen = seen;
  unsigned int _loop_prev = prev;
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
      if (_loop_seen) {
        if (_loop_prev == d_a0) {
          std::shared_ptr<List<unsigned int>> _next_l = d_a1;
          bool _next_seen = true;
          unsigned int _next_prev = d_a0;
          _loop_l = std::move(_next_l);
          _loop_seen = std::move(_next_seen);
          _loop_prev = std::move(_next_prev);
          continue;
        } else {
          auto _cell = List<unsigned int>::cons(d_a0, nullptr);
          if (_last) {
            std::get<typename List<unsigned int>::Cons>(_last->v_mut()).d_a1 =
                _cell;
          } else {
            _head = _cell;
          }
          _last = _cell;
          std::shared_ptr<List<unsigned int>> _next_l = d_a1;
          bool _next_seen = true;
          unsigned int _next_prev = d_a0;
          _loop_l = std::move(_next_l);
          _loop_seen = std::move(_next_seen);
          _loop_prev = std::move(_next_prev);
          continue;
        }
      } else {
        auto _cell = List<unsigned int>::cons(d_a0, nullptr);
        if (_last) {
          std::get<typename List<unsigned int>::Cons>(_last->v_mut()).d_a1 =
              _cell;
        } else {
          _head = _cell;
        }
        _last = _cell;
        std::shared_ptr<List<unsigned int>> _next_l = d_a1;
        bool _next_seen = true;
        unsigned int _next_prev = d_a0;
        _loop_l = std::move(_next_l);
        _loop_seen = std::move(_next_seen);
        _loop_prev = std::move(_next_prev);
        continue;
      }
    }
  }
  return _head;
}

std::shared_ptr<List<unsigned int>>
LoopifySorting::uniq_sorted(const std::shared_ptr<List<unsigned int>> &l) {
  return uniq_sorted_aux(0u, false, l);
}
