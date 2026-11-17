#include "loopify_sorting.h"

/// Consolidated UNIQUE sorting algorithms and related operations.
List<uint64_t> LoopifySorting::insert(uint64_t x, const List<uint64_t> &l) {
  // Builds the result front to back: _write points at the empty tail the next
  // cell fills.
  std::optional<List<uint64_t>> _root{};
  std::shared_ptr<List<uint64_t>> *_write = nullptr;
  const List<uint64_t> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l->v())) {
      auto _value = List<uint64_t>::cons(x, List<uint64_t>::nil());
      (_write ? *(*_write = std::make_shared<List<uint64_t>>(std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename List<uint64_t>::Cons>(_loop_l->v());
      if (x <= a0) {
        auto _value = List<uint64_t>::cons(x, *_loop_l);
        (_write ? *(*_write =
                        std::make_shared<List<uint64_t>>(std::move(_value)))
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

List<uint64_t> LoopifySorting::insertion_sort(const List<uint64_t> &l) {
  // Explicit stack replaces the non-tail recursion of insertion_sort: _call
  // frames are pending calls, _after frames resume a caller.
  struct _call {
    const List<uint64_t> *l;
  };

  struct _after_insertion_sort_in_Cons {
    uint64_t a0;
  };

  using _frame = std::variant<_call, _after_insertion_sort_in_Cons>;
  List<uint64_t> _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&l});
  while (!_stack.empty()) {
    _frame _popped = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      const List<uint64_t> &l = *_f.l;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
        _result = List<uint64_t>::nil();
      } else {
        const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
        _stack.emplace_back(_after_insertion_sort_in_Cons{a0});
        _stack.emplace_back(_call{crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<_after_insertion_sort_in_Cons>(_popped));
      uint64_t a0 = _f.a0;
      _result = insert(a0, std::move(_result));
    }
  }
  return _result;
}

List<uint64_t>
LoopifySorting::merge_fuel(uint64_t fuel, const List<uint64_t> &l1,
                           const List<uint64_t> &l2) {
  // Builds the result front to back: _write points at the empty tail the next
  // cell fills.
  std::optional<List<uint64_t>> _root{};
  std::shared_ptr<List<uint64_t>> *_write = nullptr;
  const List<uint64_t> *_loop_l2 = &l2;
  const List<uint64_t> *_loop_l1 = &l1;
  uint64_t _loop_fuel = fuel;
  while (true) {
    if (_loop_fuel <= 0) {
      auto _value = List<uint64_t>::nil();
      (_write ? *(*_write = std::make_shared<List<uint64_t>>(std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      uint64_t f = _loop_fuel - 1;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l1->v())) {
        auto _value = *_loop_l2;
        (_write ? *(*_write =
                        std::make_shared<List<uint64_t>>(std::move(_value)))
                : _root.emplace(std::move(_value)));
        break;
      } else {
        const auto &[a0, a1] =
            std::get<typename List<uint64_t>::Cons>(_loop_l1->v());
        if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l2->v())) {
          auto _value = *_loop_l1;
          (_write ? *(*_write =
                          std::make_shared<List<uint64_t>>(std::move(_value)))
                  : _root.emplace(std::move(_value)));
          break;
        } else {
          const auto &[a00, a10] =
              std::get<typename List<uint64_t>::Cons>(_loop_l2->v());
          if (a0 <= a00) {
            auto _cell = typename List<uint64_t>::Cons(a0, nullptr);
            List<uint64_t> &_node =
                (_write ? *(*_write = std::make_shared<List<uint64_t>>(
                                std::move(_cell)))
                        : _root.emplace(std::move(_cell)));
            _write = &std::get<typename List<uint64_t>::Cons>(_node.v_mut()).l;
            _loop_l2 = &*_loop_l2;
            _loop_l1 = crane_raw(a1);
            _loop_fuel = f;
            continue;
          } else {
            auto _cell = typename List<uint64_t>::Cons(a00, nullptr);
            List<uint64_t> &_node =
                (_write ? *(*_write = std::make_shared<List<uint64_t>>(
                                std::move(_cell)))
                        : _root.emplace(std::move(_cell)));
            _write = &std::get<typename List<uint64_t>::Cons>(_node.v_mut()).l;
            _loop_l2 = crane_raw(a10);
            _loop_l1 = &*_loop_l1;
            _loop_fuel = f;
            continue;
          }
        }
      }
    }
  }
  return std::move(*_root);
}

List<uint64_t> LoopifySorting::merge(const List<uint64_t> &l1,
                                     const List<uint64_t> &l2) {
  return merge_fuel((len_impl<uint64_t>(l1) + len_impl<uint64_t>(l2)), l1, l2);
}

List<uint64_t> LoopifySorting::merge_sort_fuel(uint64_t fuel,
                                               const List<uint64_t> &l) {
  // Explicit stack replaces the non-tail recursion of merge_sort_fuel: _call
  // frames are pending calls, _after frames resume a caller.
  struct _call {
    List<uint64_t> l;
    uint64_t fuel;
  };

  struct _after_merge_sort_fuel_in_pair {
    uint64_t f;
    List<uint64_t> l2;
  };

  struct _after_merge_sort_fuel_in_pair_2 {
    List<uint64_t> _tmp2;
  };

  using _frame = std::variant<_call, _after_merge_sort_fuel_in_pair,
                              _after_merge_sort_fuel_in_pair_2>;
  List<uint64_t> _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{l, fuel});
  while (!_stack.empty()) {
    _frame _popped = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      List<uint64_t> l = std::move(_f.l);
      uint64_t fuel = _f.fuel;
      if (fuel <= 0) {
        _result = std::move(l);
      } else {
        uint64_t f = fuel - 1;
        if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
          _result = List<uint64_t>::nil();
        } else {
          const auto &[_, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
          auto &&_sv = *a1;
          if (std::holds_alternative<typename List<uint64_t>::Nil>(_sv.v())) {
            _result = std::move(l);
          } else {
            auto [l1, l2] = split<uint64_t>(l);
            _stack.emplace_back(
                _after_merge_sort_fuel_in_pair{f, std::move(l2)});
            _stack.emplace_back(_call{std::move(l1), f});
          }
        }
      }
    } else if (std::holds_alternative<_after_merge_sort_fuel_in_pair>(_popped)) {
      auto _f = std::move(std::get<_after_merge_sort_fuel_in_pair>(_popped));
      uint64_t f = _f.f;
      List<uint64_t> l2 = std::move(_f.l2);
      _stack.emplace_back(_after_merge_sort_fuel_in_pair_2{std::move(_result)});
      _stack.emplace_back(_call{std::move(l2), f});
    } else {
      auto _f = std::move(std::get<_after_merge_sort_fuel_in_pair_2>(_popped));
      _result = merge(std::move(_f._tmp2), std::move(_result));
    }
  }
  return _result;
}

List<uint64_t> LoopifySorting::merge_sort(const List<uint64_t> &l) {
  return merge_sort_fuel(len_impl<uint64_t>(l), l);
}

std::pair<List<uint64_t>, List<uint64_t>>
LoopifySorting::partition(uint64_t pivot, const List<uint64_t> &l) {
  // Explicit stack replaces the non-tail recursion of partition: _call frames
  // are pending calls, _after frames resume a caller.
  struct _call {
    const List<uint64_t> *l;
  };

  struct _after_partition_in_Cons {
    uint64_t a0;
  };

  using _frame = std::variant<_call, _after_partition_in_Cons>;
  std::pair<List<uint64_t>, List<uint64_t>> _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&l});
  while (!_stack.empty()) {
    _frame _popped = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      const List<uint64_t> &l = *_f.l;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
        _result = std::make_pair(List<uint64_t>::nil(), List<uint64_t>::nil());
      } else {
        const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
        _stack.emplace_back(_after_partition_in_Cons{a0});
        _stack.emplace_back(_call{crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<_after_partition_in_Cons>(_popped));
      uint64_t a0 = _f.a0;
      auto [lo, hi] = std::move(_result);
      if (a0 <= pivot) {
        _result = std::make_pair(List<uint64_t>::cons(a0, std::move(lo)),
                                 std::move(hi));
      } else {
        _result = std::make_pair(std::move(lo),
                                 List<uint64_t>::cons(a0, std::move(hi)));
      }
    }
  }
  return _result;
}

List<uint64_t> LoopifySorting::quicksort_fuel(uint64_t fuel,
                                              const List<uint64_t> &l) {
  // Explicit stack replaces the non-tail recursion of quicksort_fuel: _call
  // frames are pending calls, _after frames resume a caller.
  struct _call {
    List<uint64_t> l;
    uint64_t fuel;
  };

  struct _after_quicksort_fuel_in_pair {
    uint64_t f;
    uint64_t a0;
    List<uint64_t> hi;
  };

  struct _after_quicksort_fuel_in_pair_2 {
    uint64_t a0;
    List<uint64_t> _tmp2;
  };

  using _frame = std::variant<_call, _after_quicksort_fuel_in_pair,
                              _after_quicksort_fuel_in_pair_2>;
  List<uint64_t> _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{l, fuel});
  while (!_stack.empty()) {
    _frame _popped = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      List<uint64_t> l = std::move(_f.l);
      uint64_t fuel = _f.fuel;
      if (fuel <= 0) {
        _result = std::move(l);
      } else {
        uint64_t f = fuel - 1;
        if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
          _result = List<uint64_t>::nil();
        } else {
          const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
          auto [lo, hi] = partition(a0, *a1);
          _stack.emplace_back(
              _after_quicksort_fuel_in_pair{f, a0, std::move(hi)});
          _stack.emplace_back(_call{std::move(lo), f});
        }
      }
    } else if (std::holds_alternative<_after_quicksort_fuel_in_pair>(_popped)) {
      auto _f = std::move(std::get<_after_quicksort_fuel_in_pair>(_popped));
      uint64_t f = _f.f;
      uint64_t a0 = _f.a0;
      List<uint64_t> hi = std::move(_f.hi);
      _stack.emplace_back(
          _after_quicksort_fuel_in_pair_2{a0, std::move(_result)});
      _stack.emplace_back(_call{std::move(hi), f});
    } else {
      auto _f = std::move(std::get<_after_quicksort_fuel_in_pair_2>(_popped));
      uint64_t a0 = _f.a0;
      _result = _f._tmp2.app(List<uint64_t>::cons(a0, std::move(_result)));
    }
  }
  return _result;
}

List<uint64_t> LoopifySorting::quicksort(const List<uint64_t> &l) {
  return quicksort_fuel(len_impl<uint64_t>(l), l);
}

bool LoopifySorting::is_sorted_aux(uint64_t prev, const List<uint64_t> &l) {
  // Loop replaces the tail recursion: each recursive call updates the loop
  // variables.
  const List<uint64_t> *_loop_l = &l;
  uint64_t _loop_prev = prev;
  while (true) {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l->v())) {
      return true;
    } else {
      const auto &[a0, a1] =
          std::get<typename List<uint64_t>::Cons>(_loop_l->v());
      if (_loop_prev <= a0) {
        _loop_l = crane_raw(a1);
        _loop_prev = a0;
      } else {
        return false;
      }
    }
  }
}

bool LoopifySorting::is_sorted(const List<uint64_t> &l) {
  if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
    return true;
  } else {
    const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
    return is_sorted_aux(a0, *a1);
  }
}

/// remove_duplicates removes consecutive duplicates from sorted list.
List<uint64_t> LoopifySorting::remove_duplicates(const List<uint64_t> &l) {
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
        if (a0 == a00) {
          _loop_l = crane_raw(a1);
          continue;
        } else {
          auto _cell = typename List<uint64_t>::Cons(a0, nullptr);
          List<uint64_t> &_node =
              (_write ? *(*_write = std::make_shared<List<uint64_t>>(
                              std::move(_cell)))
                      : _root.emplace(std::move(_cell)));
          _write = &std::get<typename List<uint64_t>::Cons>(_node.v_mut()).l;
          _loop_l = crane_raw(a1);
          continue;
        }
      }
    }
  }
  return std::move(*_root);
}

/// uniq_sorted variant that preserves order.
List<uint64_t> LoopifySorting::uniq_sorted_aux(uint64_t prev, bool seen,
                                               const List<uint64_t> &l) {
  // Builds the result front to back: _write points at the empty tail the next
  // cell fills.
  std::optional<List<uint64_t>> _root{};
  std::shared_ptr<List<uint64_t>> *_write = nullptr;
  const List<uint64_t> *_loop_l = &l;
  bool _loop_seen = seen;
  uint64_t _loop_prev = prev;
  while (true) {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l->v())) {
      auto _value = List<uint64_t>::nil();
      (_write ? *(*_write = std::make_shared<List<uint64_t>>(std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename List<uint64_t>::Cons>(_loop_l->v());
      if (_loop_seen) {
        if (_loop_prev == a0) {
          _loop_l = crane_raw(a1);
          _loop_seen = true;
          _loop_prev = a0;
          continue;
        } else {
          auto _cell = typename List<uint64_t>::Cons(a0, nullptr);
          List<uint64_t> &_node =
              (_write ? *(*_write = std::make_shared<List<uint64_t>>(
                              std::move(_cell)))
                      : _root.emplace(std::move(_cell)));
          _write = &std::get<typename List<uint64_t>::Cons>(_node.v_mut()).l;
          _loop_l = crane_raw(a1);
          _loop_seen = true;
          _loop_prev = a0;
          continue;
        }
      } else {
        auto _cell = typename List<uint64_t>::Cons(a0, nullptr);
        List<uint64_t> &_node =
            (_write ? *(*_write =
                            std::make_shared<List<uint64_t>>(std::move(_cell)))
                    : _root.emplace(std::move(_cell)));
        _write = &std::get<typename List<uint64_t>::Cons>(_node.v_mut()).l;
        _loop_l = crane_raw(a1);
        _loop_seen = true;
        _loop_prev = a0;
        continue;
      }
    }
  }
  return std::move(*_root);
}

List<uint64_t> LoopifySorting::uniq_sorted(const List<uint64_t> &l) {
  return uniq_sorted_aux(UINT64_C(0), false, l);
}
