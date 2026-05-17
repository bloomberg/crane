#include "loopify_sorting.h"

/// Consolidated UNIQUE sorting algorithms and related operations.
List<unsigned int> LoopifySorting::insert(unsigned int x,
                                          List<unsigned int> l) {
  std::unique_ptr<List<unsigned int>> _head{};
  std::unique_ptr<List<unsigned int>> *_write = &_head;
  List<unsigned int> _loop_l = std::move(l);
  while (true) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(
            _loop_l.v_mut())) {
      *_write = std::make_unique<List<unsigned int>>(
          List<unsigned int>::cons(x, List<unsigned int>::nil()));
      break;
    } else {
      auto &[a0, a1] =
          std::get<typename List<unsigned int>::Cons>(_loop_l.v_mut());
      if (x <= a0) {
        *_write = std::make_unique<List<unsigned int>>(
            List<unsigned int>::cons(x, _loop_l));
        break;
      } else {
        auto _cell = std::make_unique<List<unsigned int>>(
            typename List<unsigned int>::Cons(std::move(a0), nullptr));
        *_write = std::move(_cell);
        _write =
            &std::get<typename List<unsigned int>::Cons>((*_write)->v_mut()).a1;
        _loop_l = std::move(*a1);
        continue;
      }
    }
  }
  return std::move(*_head);
}

List<unsigned int> LoopifySorting::insertion_sort(
    const List<unsigned int>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<unsigned int> *l;
  };

  /// _Resume_Cons: saves [a0], resumes after recursive call with _result.
  struct _Resume_Cons {
    unsigned int a0;
  };

  using _Frame = std::variant<_Enter, _Resume_Cons>;
  List<unsigned int> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l});
  /// Loopified insertion_sort: _Enter -> _Resume_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<unsigned int> &l = *_f.l;
      if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
        _result = List<unsigned int>::nil();
      } else {
        const auto &[a0, a1] =
            std::get<typename List<unsigned int>::Cons>(l.v());
        _stack.emplace_back(_Resume_Cons{a0});
        _stack.emplace_back(_Enter{a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Resume_Cons>(_frame));
      _result = insert(_f.a0, _result);
    }
  }
  return _result;
}

List<unsigned int> LoopifySorting::merge_fuel(unsigned int fuel,
                                              List<unsigned int> l1,
                                              List<unsigned int> l2) {
  std::unique_ptr<List<unsigned int>> _head{};
  std::unique_ptr<List<unsigned int>> *_write = &_head;
  List<unsigned int> _loop_l2 = std::move(l2);
  List<unsigned int> _loop_l1 = std::move(l1);
  unsigned int _loop_fuel = std::move(fuel);
  while (true) {
    if (_loop_fuel <= 0) {
      *_write = std::make_unique<List<unsigned int>>(List<unsigned int>::nil());
      break;
    } else {
      unsigned int f = _loop_fuel - 1;
      if (std::holds_alternative<typename List<unsigned int>::Nil>(
              _loop_l1.v_mut())) {
        *_write = std::make_unique<List<unsigned int>>(std::move(_loop_l2));
        break;
      } else {
        auto &[a0, a1] =
            std::get<typename List<unsigned int>::Cons>(_loop_l1.v_mut());
        if (std::holds_alternative<typename List<unsigned int>::Nil>(
                _loop_l2.v_mut())) {
          *_write = std::make_unique<List<unsigned int>>(_loop_l1);
          break;
        } else {
          auto &[a00, a10] =
              std::get<typename List<unsigned int>::Cons>(_loop_l2.v_mut());
          if (a0 <= a00) {
            auto _cell = std::make_unique<List<unsigned int>>(
                typename List<unsigned int>::Cons(std::move(a0), nullptr));
            *_write = std::move(_cell);
            _write =
                &std::get<typename List<unsigned int>::Cons>((*_write)->v_mut())
                     .a1;
            _loop_l1 = std::move(*a1);
            _loop_fuel = f;
            continue;
          } else {
            auto _cell = std::make_unique<List<unsigned int>>(
                typename List<unsigned int>::Cons(std::move(a00), nullptr));
            *_write = std::move(_cell);
            _write =
                &std::get<typename List<unsigned int>::Cons>((*_write)->v_mut())
                     .a1;
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

List<unsigned int> LoopifySorting::merge(const List<unsigned int> &l1,
                                         const List<unsigned int> &l2) {
  return merge_fuel((len_impl<unsigned int>(l1) + len_impl<unsigned int>(l2)),
                    l1, l2);
}

List<unsigned int> LoopifySorting::merge_sort_fuel(
    unsigned int fuel,
    List<unsigned int>
        l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    List<unsigned int> l;
    unsigned int fuel;
  };

  /// _After_l1: saves [l1, f], dispatches next recursive call.
  struct _After_l1 {
    List<unsigned int> l1;
    unsigned int f;
  };

  /// _Combine_l1: receives partial results, combines with _result from final
  /// call.
  struct _Combine_l1 {
    List<unsigned int> _result;
  };

  using _Frame = std::variant<_Enter, _After_l1, _Combine_l1>;
  List<unsigned int> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{l, fuel});
  /// Loopified merge_sort_fuel: _Enter -> _After_l1 -> _Combine_l1.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      List<unsigned int> l = std::move(_f.l);
      unsigned int fuel = _f.fuel;
      if (fuel <= 0) {
        _result = std::move(l);
      } else {
        unsigned int f = fuel - 1;
        if (std::holds_alternative<typename List<unsigned int>::Nil>(
                l.v_mut())) {
          _result = List<unsigned int>::nil();
        } else {
          auto &[a0, a1] =
              std::get<typename List<unsigned int>::Cons>(l.v_mut());
          auto &&_sv = *a1;
          if (std::holds_alternative<typename List<unsigned int>::Nil>(
                  _sv.v())) {
            _result = l;
          } else {
            auto _cs = split<unsigned int>(l);
            const List<unsigned int> &l1 = _cs.first;
            const List<unsigned int> &l2 = _cs.second;
            _stack.emplace_back(_After_l1{l1, f});
            _stack.emplace_back(_Enter{l2, f});
          }
        }
      }
    } else if (std::holds_alternative<_After_l1>(_frame)) {
      auto _f = std::move(std::get<_After_l1>(_frame));
      _stack.emplace_back(_Combine_l1{std::move(_result)});
      _stack.emplace_back(_Enter{std::move(_f.l1), _f.f});
    } else {
      auto _f = std::move(std::get<_Combine_l1>(_frame));
      _result = merge(_result, _f._result);
    }
  }
  return _result;
}

List<unsigned int> LoopifySorting::merge_sort(const List<unsigned int> &l) {
  return merge_sort_fuel(len_impl<unsigned int>(l), l);
}

std::pair<List<unsigned int>, List<unsigned int>> LoopifySorting::partition(
    unsigned int pivot,
    const List<unsigned int>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<unsigned int> *l;
  };

  /// _Cont_Cons: saves [a0, pivot], resumes after recursive call, then
  /// processes rest.
  struct _Cont_Cons {
    unsigned int a0;
    unsigned int pivot;
  };

  using _Frame = std::variant<_Enter, _Cont_Cons>;
  std::pair<List<unsigned int>, List<unsigned int>> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l});
  /// Loopified partition: _Enter -> _Cont_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<unsigned int> &l = *_f.l;
      if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
        _result = std::make_pair(List<unsigned int>::nil(),
                                 List<unsigned int>::nil());
      } else {
        const auto &[a0, a1] =
            std::get<typename List<unsigned int>::Cons>(l.v());
        _stack.emplace_back(_Cont_Cons{a0, pivot});
        _stack.emplace_back(_Enter{a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Cont_Cons>(_frame));
      unsigned int a0 = _f.a0;
      unsigned int pivot = _f.pivot;
      const List<unsigned int> &lo = _result.first;
      const List<unsigned int> &hi = _result.second;
      if (a0 <= pivot) {
        _result = std::make_pair(List<unsigned int>::cons(a0, lo), hi);
      } else {
        _result = std::make_pair(lo, List<unsigned int>::cons(a0, hi));
      }
    }
  }
  return _result;
}

List<unsigned int> LoopifySorting::quicksort_fuel(
    unsigned int fuel,
    List<unsigned int>
        l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    List<unsigned int> l;
    unsigned int fuel;
  };

  /// _After_lo: saves [lo, f, a0], dispatches next recursive call.
  struct _After_lo {
    List<unsigned int> lo;
    unsigned int f;
    unsigned int a0;
  };

  /// _Combine_lo: receives partial results, combines with _result from final
  /// call.
  struct _Combine_lo {
    List<unsigned int> _result;
    unsigned int a0;
  };

  using _Frame = std::variant<_Enter, _After_lo, _Combine_lo>;
  List<unsigned int> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{l, fuel});
  /// Loopified quicksort_fuel: _Enter -> _After_lo -> _Combine_lo.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      List<unsigned int> l = std::move(_f.l);
      unsigned int fuel = _f.fuel;
      if (fuel <= 0) {
        _result = std::move(l);
      } else {
        unsigned int f = fuel - 1;
        if (std::holds_alternative<typename List<unsigned int>::Nil>(
                l.v_mut())) {
          _result = List<unsigned int>::nil();
        } else {
          auto &[a0, a1] =
              std::get<typename List<unsigned int>::Cons>(l.v_mut());
          auto _cs = partition(a0, *a1);
          const List<unsigned int> &lo = _cs.first;
          const List<unsigned int> &hi = _cs.second;
          _stack.emplace_back(_After_lo{lo, f, std::move(a0)});
          _stack.emplace_back(_Enter{hi, f});
        }
      }
    } else if (std::holds_alternative<_After_lo>(_frame)) {
      auto _f = std::move(std::get<_After_lo>(_frame));
      _stack.emplace_back(_Combine_lo{std::move(_result), _f.a0});
      _stack.emplace_back(_Enter{std::move(_f.lo), _f.f});
    } else {
      auto _f = std::move(std::get<_Combine_lo>(_frame));
      _result = _result.app(List<unsigned int>::cons(_f.a0, _f._result));
    }
  }
  return _result;
}

List<unsigned int> LoopifySorting::quicksort(const List<unsigned int> &l) {
  return quicksort_fuel(len_impl<unsigned int>(l), l);
}

bool LoopifySorting::is_sorted_aux(unsigned int prev,
                                   const List<unsigned int> &l) {
  bool _result;
  const List<unsigned int> *_loop_l = &l;
  unsigned int _loop_prev = std::move(prev);
  while (true) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(
            _loop_l->v())) {
      _result = true;
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename List<unsigned int>::Cons>(_loop_l->v());
      if (_loop_prev <= a0) {
        _loop_l = a1.get();
        _loop_prev = a0;
      } else {
        _result = false;
        break;
      }
    }
  }
  return _result;
}

bool LoopifySorting::is_sorted(const List<unsigned int> &l) {
  if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
    return true;
  } else {
    const auto &[a0, a1] = std::get<typename List<unsigned int>::Cons>(l.v());
    return is_sorted_aux(a0, *a1);
  }
}

/// remove_duplicates removes consecutive duplicates from sorted list.
List<unsigned int>
LoopifySorting::remove_duplicates(const List<unsigned int> &l) {
  std::unique_ptr<List<unsigned int>> _head{};
  std::unique_ptr<List<unsigned int>> *_write = &_head;
  const List<unsigned int> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(
            _loop_l->v())) {
      *_write = std::make_unique<List<unsigned int>>(List<unsigned int>::nil());
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename List<unsigned int>::Cons>(_loop_l->v());
      auto &&_sv0 = *a1;
      if (std::holds_alternative<typename List<unsigned int>::Nil>(_sv0.v())) {
        *_write = std::make_unique<List<unsigned int>>(
            List<unsigned int>::cons(a0, List<unsigned int>::nil()));
        break;
      } else {
        const auto &[a00, a10] =
            std::get<typename List<unsigned int>::Cons>(_sv0.v());
        if (a0 == a00) {
          _loop_l = a1.get();
          continue;
        } else {
          auto _cell = std::make_unique<List<unsigned int>>(
              typename List<unsigned int>::Cons(a0, nullptr));
          *_write = std::move(_cell);
          _write =
              &std::get<typename List<unsigned int>::Cons>((*_write)->v_mut())
                   .a1;
          _loop_l = a1.get();
          continue;
        }
      }
    }
  }
  return std::move(*_head);
}

/// uniq_sorted variant that preserves order.
List<unsigned int>
LoopifySorting::uniq_sorted_aux(unsigned int prev, bool seen,
                                const List<unsigned int> &l) {
  std::unique_ptr<List<unsigned int>> _head{};
  std::unique_ptr<List<unsigned int>> *_write = &_head;
  const List<unsigned int> *_loop_l = &l;
  bool _loop_seen = std::move(seen);
  unsigned int _loop_prev = std::move(prev);
  while (true) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(
            _loop_l->v())) {
      *_write = std::make_unique<List<unsigned int>>(List<unsigned int>::nil());
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename List<unsigned int>::Cons>(_loop_l->v());
      if (_loop_seen) {
        if (_loop_prev == a0) {
          _loop_l = a1.get();
          _loop_seen = true;
          _loop_prev = a0;
          continue;
        } else {
          auto _cell = std::make_unique<List<unsigned int>>(
              typename List<unsigned int>::Cons(a0, nullptr));
          *_write = std::move(_cell);
          _write =
              &std::get<typename List<unsigned int>::Cons>((*_write)->v_mut())
                   .a1;
          _loop_l = a1.get();
          _loop_seen = true;
          _loop_prev = a0;
          continue;
        }
      } else {
        auto _cell = std::make_unique<List<unsigned int>>(
            typename List<unsigned int>::Cons(a0, nullptr));
        *_write = std::move(_cell);
        _write =
            &std::get<typename List<unsigned int>::Cons>((*_write)->v_mut()).a1;
        _loop_l = a1.get();
        _loop_seen = true;
        _loop_prev = a0;
        continue;
      }
    }
  }
  return std::move(*_head);
}

List<unsigned int> LoopifySorting::uniq_sorted(const List<unsigned int> &l) {
  return uniq_sorted_aux(0u, false, l);
}
