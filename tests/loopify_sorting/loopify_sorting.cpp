#include "loopify_sorting.h"

List<uint64_t> LoopifySorting::insert(uint64_t x, List<uint64_t> l) {
  std::shared_ptr<List<uint64_t>> _head{};
  std::shared_ptr<List<uint64_t>> *_write = &_head;
  List<uint64_t> _loop_l = std::move(l);
  while (true) {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l.v_mut())) {
      *_write = std::make_shared<List<uint64_t>>(
          List<uint64_t>::cons(x, List<uint64_t>::nil()));
      break;
    } else {
      auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(_loop_l.v_mut());
      if (x <= a0) {
        *_write =
            std::make_shared<List<uint64_t>>(List<uint64_t>::cons(x, _loop_l));
        break;
      } else {
        auto _cell = std::make_shared<List<uint64_t>>(
            typename List<uint64_t>::Cons(a0, nullptr));
        *_write = std::move(_cell);
        _write = &std::get<typename List<uint64_t>::Cons>((*_write)->v_mut()).l;
        _loop_l = List<uint64_t>(*a1);
        continue;
      }
    }
  }
  return std::move(*_head);
}

List<uint64_t> LoopifySorting::insertion_sort(
    const List<uint64_t>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<uint64_t> *l;
  };

  /// _Resume_Cons: saves [a0], resumes after recursive call with _result.
  struct _Resume_Cons {
    uint64_t a0;
  };

  using _Frame = std::variant<_Enter, _Resume_Cons>;
  List<uint64_t> _result{};
  crane::small_vector<_Frame> _stack;
  _stack.emplace_back(_Enter{&l});
  /// Loopified insertion_sort: _Enter -> _Resume_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<uint64_t> &l = *_f.l;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
        _result = List<uint64_t>::nil();
      } else {
        const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
        _stack.emplace_back(_Resume_Cons{a0});
        _stack.emplace_back(_Enter{crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<_Resume_Cons>(_frame));
      _result = insert(_f.a0, std::move(_result));
    }
  }
  return _result;
}

List<uint64_t> LoopifySorting::merge_fuel(uint64_t fuel, List<uint64_t> l1,
                                          List<uint64_t> l2) {
  std::shared_ptr<List<uint64_t>> _head{};
  std::shared_ptr<List<uint64_t>> *_write = &_head;
  List<uint64_t> _loop_l2 = std::move(l2);
  List<uint64_t> _loop_l1 = std::move(l1);
  uint64_t _loop_fuel = std::move(fuel);
  while (true) {
    if (_loop_fuel <= 0) {
      *_write = std::make_shared<List<uint64_t>>(List<uint64_t>::nil());
      break;
    } else {
      uint64_t f = _loop_fuel - 1;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(
              _loop_l1.v_mut())) {
        *_write = std::make_shared<List<uint64_t>>(std::move(_loop_l2));
        break;
      } else {
        auto &[a0, a1] =
            std::get<typename List<uint64_t>::Cons>(_loop_l1.v_mut());
        if (std::holds_alternative<typename List<uint64_t>::Nil>(
                _loop_l2.v_mut())) {
          *_write = std::make_shared<List<uint64_t>>(_loop_l1);
          break;
        } else {
          auto &[a00, a10] =
              std::get<typename List<uint64_t>::Cons>(_loop_l2.v_mut());
          if (a0 <= a00) {
            auto _cell = std::make_shared<List<uint64_t>>(
                typename List<uint64_t>::Cons(a0, nullptr));
            *_write = std::move(_cell);
            _write =
                &std::get<typename List<uint64_t>::Cons>((*_write)->v_mut()).l;
            _loop_l1 = List<uint64_t>(*a1);
            _loop_fuel = f;
            continue;
          } else {
            auto _cell = std::make_shared<List<uint64_t>>(
                typename List<uint64_t>::Cons(a00, nullptr));
            *_write = std::move(_cell);
            _write =
                &std::get<typename List<uint64_t>::Cons>((*_write)->v_mut()).l;
            _loop_l2 = List<uint64_t>(*a10);
            _loop_fuel = f;
            continue;
          }
        }
      }
    }
  }
  return std::move(*_head);
}

List<uint64_t> LoopifySorting::merge(const List<uint64_t> &l1,
                                     const List<uint64_t> &l2) {
  return merge_fuel((len_impl<uint64_t>(l1) + len_impl<uint64_t>(l2)), l1, l2);
}

List<uint64_t> LoopifySorting::merge_sort_fuel(
    uint64_t fuel,
    List<uint64_t>
        l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    List<uint64_t> l;
    uint64_t fuel;
  };

  /// _After_l1: saves [l1, f], dispatches next recursive call.
  struct _After_l1 {
    List<uint64_t> l1;
    uint64_t f;
  };

  /// _Combine_l1: receives partial results, combines with _result from final
  /// call.
  struct _Combine_l1 {
    List<uint64_t> _result;
  };

  using _Frame = std::variant<_Enter, _After_l1, _Combine_l1>;
  List<uint64_t> _result{};
  crane::small_vector<_Frame> _stack;
  _stack.emplace_back(_Enter{std::move(l), fuel});
  /// Loopified merge_sort_fuel: _Enter -> _After_l1 -> _Combine_l1.
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
            auto [l1, l2] = split<uint64_t>(l);
            _stack.emplace_back(_After_l1{std::move(l1), f});
            _stack.emplace_back(_Enter{std::move(l2), f});
          }
        }
      }
    } else if (std::holds_alternative<_After_l1>(_frame)) {
      auto _f = std::move(std::get<_After_l1>(_frame));
      _stack.emplace_back(_Combine_l1{std::move(_result)});
      _stack.emplace_back(_Enter{std::move(_f.l1), _f.f});
    } else {
      auto _f = std::move(std::get<_Combine_l1>(_frame));
      _result = merge(std::move(_result), std::move(_f._result));
    }
  }
  return _result;
}

List<uint64_t> LoopifySorting::merge_sort(const List<uint64_t> &l) {
  return merge_sort_fuel(len_impl<uint64_t>(l), l);
}

std::pair<List<uint64_t>, List<uint64_t>> LoopifySorting::partition(
    uint64_t pivot,
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
  std::pair<List<uint64_t>, List<uint64_t>> _result{};
  crane::small_vector<_Frame> _stack;
  _stack.emplace_back(_Enter{&l});
  /// Loopified partition: _Enter -> _Cont_Cons.
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
        _stack.emplace_back(_Cont_Cons{a0});
        _stack.emplace_back(_Enter{crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<_Cont_Cons>(_frame));
      uint64_t a0 = _f.a0;
      std::pair<List<uint64_t>, List<uint64_t>> _rc1 = std::move(_result);
      auto [lo, hi] = _rc1;
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

List<uint64_t> LoopifySorting::quicksort_fuel(
    uint64_t fuel,
    List<uint64_t>
        l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    List<uint64_t> l;
    uint64_t fuel;
  };

  /// _After_lo: saves [lo, f, a0], dispatches next recursive call.
  struct _After_lo {
    List<uint64_t> lo;
    uint64_t f;
    uint64_t a0;
  };

  /// _Combine_lo: receives partial results, combines with _result from final
  /// call.
  struct _Combine_lo {
    List<uint64_t> _result;
    uint64_t a0;
  };

  using _Frame = std::variant<_Enter, _After_lo, _Combine_lo>;
  List<uint64_t> _result{};
  crane::small_vector<_Frame> _stack;
  _stack.emplace_back(_Enter{std::move(l), fuel});
  /// Loopified quicksort_fuel: _Enter -> _After_lo -> _Combine_lo.
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
          auto [lo, hi] = partition(a0, *a1);
          _stack.emplace_back(_After_lo{std::move(lo), f, std::move(a0)});
          _stack.emplace_back(_Enter{std::move(hi), f});
        }
      }
    } else if (std::holds_alternative<_After_lo>(_frame)) {
      auto _f = std::move(std::get<_After_lo>(_frame));
      _stack.emplace_back(_Combine_lo{std::move(_result), _f.a0});
      _stack.emplace_back(_Enter{std::move(_f.lo), _f.f});
    } else {
      auto _f = std::move(std::get<_Combine_lo>(_frame));
      _result = std::move(_result).app(
          List<uint64_t>::cons(_f.a0, std::move(_f._result)));
    }
  }
  return _result;
}

List<uint64_t> LoopifySorting::quicksort(const List<uint64_t> &l) {
  return quicksort_fuel(len_impl<uint64_t>(l), l);
}

bool LoopifySorting::is_sorted_aux(uint64_t prev, const List<uint64_t> &l) {
  const List<uint64_t> *_loop_l = &l;
  uint64_t _loop_prev = std::move(prev);
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

List<uint64_t> LoopifySorting::remove_duplicates(const List<uint64_t> &l) {
  std::shared_ptr<List<uint64_t>> _head{};
  std::shared_ptr<List<uint64_t>> *_write = &_head;
  const List<uint64_t> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l->v())) {
      *_write = std::make_shared<List<uint64_t>>(List<uint64_t>::nil());
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename List<uint64_t>::Cons>(_loop_l->v());
      auto &&_sv0 = *a1;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(_sv0.v())) {
        *_write = std::make_shared<List<uint64_t>>(
            List<uint64_t>::cons(a0, List<uint64_t>::nil()));
        break;
      } else {
        const auto &[a00, a10] =
            std::get<typename List<uint64_t>::Cons>(_sv0.v());
        if (a0 == a00) {
          _loop_l = crane_raw(a1);
          continue;
        } else {
          auto _cell = std::make_shared<List<uint64_t>>(
              typename List<uint64_t>::Cons(a0, nullptr));
          *_write = std::move(_cell);
          _write =
              &std::get<typename List<uint64_t>::Cons>((*_write)->v_mut()).l;
          _loop_l = crane_raw(a1);
          continue;
        }
      }
    }
  }
  return std::move(*_head);
}

List<uint64_t> LoopifySorting::uniq_sorted_aux(uint64_t prev, bool seen,
                                               const List<uint64_t> &l) {
  std::shared_ptr<List<uint64_t>> _head{};
  std::shared_ptr<List<uint64_t>> *_write = &_head;
  const List<uint64_t> *_loop_l = &l;
  bool _loop_seen = std::move(seen);
  uint64_t _loop_prev = std::move(prev);
  while (true) {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l->v())) {
      *_write = std::make_shared<List<uint64_t>>(List<uint64_t>::nil());
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
          auto _cell = std::make_shared<List<uint64_t>>(
              typename List<uint64_t>::Cons(a0, nullptr));
          *_write = std::move(_cell);
          _write =
              &std::get<typename List<uint64_t>::Cons>((*_write)->v_mut()).l;
          _loop_l = crane_raw(a1);
          _loop_seen = true;
          _loop_prev = a0;
          continue;
        }
      } else {
        auto _cell = std::make_shared<List<uint64_t>>(
            typename List<uint64_t>::Cons(a0, nullptr));
        *_write = std::move(_cell);
        _write = &std::get<typename List<uint64_t>::Cons>((*_write)->v_mut()).l;
        _loop_l = crane_raw(a1);
        _loop_seen = true;
        _loop_prev = a0;
        continue;
      }
    }
  }
  return std::move(*_head);
}

List<uint64_t> LoopifySorting::uniq_sorted(const List<uint64_t> &l) {
  return uniq_sorted_aux(UINT64_C(0), false, l);
}
