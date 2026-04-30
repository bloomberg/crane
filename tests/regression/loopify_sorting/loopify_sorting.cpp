#include <loopify_sorting.h>

/// Consolidated UNIQUE sorting algorithms and related operations.
List<unsigned int> LoopifySorting::insert(unsigned int x,
                                          List<unsigned int> l) {
  std::unique_ptr<List<unsigned int>> _head{};
  std::unique_ptr<List<unsigned int>> *_write = &_head;
  List<unsigned int> _loop_l = std::move(l);
  while (true) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(
            _loop_l.v_mut())) {
      *(_write) = std::make_unique<List<unsigned int>>(
          List<unsigned int>::cons(x, List<unsigned int>::nil()));
      break;
    } else {
      auto &[d_a0, d_a1] =
          std::get<typename List<unsigned int>::Cons>(_loop_l.v_mut());
      if (x <= d_a0) {
        *(_write) = std::make_unique<List<unsigned int>>(
            List<unsigned int>::cons(x, _loop_l));
        break;
      } else {
        auto _cell = std::make_unique<List<unsigned int>>(
            typename List<unsigned int>::Cons(d_a0, nullptr));
        *(_write) = std::move(_cell);
        _write =
            &std::get<typename List<unsigned int>::Cons>((*_write)->v_mut())
                 .d_a1;
        _loop_l = std::move(*(d_a1));
        continue;
      }
    }
  }
  return std::move(*(_head));
}

List<unsigned int> LoopifySorting::insertion_sort(const List<unsigned int> &l) {
  struct _Enter {
    const List<unsigned int> *l;
  };

  struct _Call1 {
    unsigned int _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  List<unsigned int> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{&l});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<unsigned int> &l = *(_f.l);
      if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
        _result = List<unsigned int>::nil();
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<unsigned int>::Cons>(l.v());
        _stack.emplace_back(_Call1{d_a0});
        _stack.emplace_back(_Enter{d_a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Call1>(_frame));
      _result = insert(_f._s0, _result);
    }
  }
  return _result;
}

List<unsigned int> LoopifySorting::merge_fuel(const unsigned int &fuel,
                                              List<unsigned int> l1,
                                              List<unsigned int> l2) {
  std::unique_ptr<List<unsigned int>> _head{};
  std::unique_ptr<List<unsigned int>> *_write = &_head;
  List<unsigned int> _loop_l2 = std::move(l2);
  List<unsigned int> _loop_l1 = std::move(l1);
  unsigned int _loop_fuel = fuel;
  while (true) {
    if (_loop_fuel <= 0) {
      *(_write) =
          std::make_unique<List<unsigned int>>(List<unsigned int>::nil());
      break;
    } else {
      unsigned int f = _loop_fuel - 1;
      if (std::holds_alternative<typename List<unsigned int>::Nil>(
              _loop_l1.v_mut())) {
        *(_write) = std::make_unique<List<unsigned int>>(std::move(_loop_l2));
        break;
      } else {
        auto &[d_a0, d_a1] =
            std::get<typename List<unsigned int>::Cons>(_loop_l1.v_mut());
        if (std::holds_alternative<typename List<unsigned int>::Nil>(
                _loop_l2.v_mut())) {
          *(_write) = std::make_unique<List<unsigned int>>(_loop_l1);
          break;
        } else {
          auto &[d_a00, d_a10] =
              std::get<typename List<unsigned int>::Cons>(_loop_l2.v_mut());
          if (d_a0 <= d_a00) {
            auto _cell = std::make_unique<List<unsigned int>>(
                typename List<unsigned int>::Cons(d_a0, nullptr));
            *(_write) = std::move(_cell);
            _write =
                &std::get<typename List<unsigned int>::Cons>((*_write)->v_mut())
                     .d_a1;
            List<unsigned int> _next_l1 = std::move(*(d_a1));
            unsigned int _next_fuel = f;
            _loop_l1 = std::move(_next_l1);
            _loop_fuel = std::move(_next_fuel);
            continue;
          } else {
            auto _cell = std::make_unique<List<unsigned int>>(
                typename List<unsigned int>::Cons(d_a00, nullptr));
            *(_write) = std::move(_cell);
            _write =
                &std::get<typename List<unsigned int>::Cons>((*_write)->v_mut())
                     .d_a1;
            List<unsigned int> _next_l2 = std::move(*(d_a10));
            unsigned int _next_fuel = f;
            _loop_l2 = std::move(_next_l2);
            _loop_fuel = std::move(_next_fuel);
            continue;
          }
        }
      }
    }
  }
  return std::move(*(_head));
}

List<unsigned int> LoopifySorting::merge(const List<unsigned int> &l1,
                                         const List<unsigned int> &l2) {
  return merge_fuel((len_impl<unsigned int>(l1) + len_impl<unsigned int>(l2)),
                    l1, l2);
}

List<unsigned int> LoopifySorting::merge_sort_fuel(const unsigned int &fuel,
                                                   List<unsigned int> l) {
  struct _Enter {
    List<unsigned int> l;
    unsigned int fuel;
  };

  struct _Call1 {
    List<unsigned int> _s0;
    unsigned int _s1;
  };

  struct _Call2 {
    List<unsigned int> _s0;
  };

  using _Frame = std::variant<_Enter, _Call1, _Call2>;
  List<unsigned int> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{l, fuel});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      List<unsigned int> l = std::move(_f.l);
      const unsigned int &fuel = _f.fuel;
      if (fuel <= 0) {
        _result = std::move(l);
      } else {
        unsigned int f = fuel - 1;
        if (std::holds_alternative<typename List<unsigned int>::Nil>(
                l.v_mut())) {
          _result = List<unsigned int>::nil();
        } else {
          auto &[d_a0, d_a1] =
              std::get<typename List<unsigned int>::Cons>(l.v_mut());
          auto &&_sv = *(d_a1);
          if (std::holds_alternative<typename List<unsigned int>::Nil>(
                  _sv.v())) {
            _result = l;
          } else {
            auto _cs = split<unsigned int>(l);
            const List<unsigned int> &l1 = _cs.first;
            const List<unsigned int> &l2 = _cs.second;
            _stack.emplace_back(_Call1{l1, f});
            _stack.emplace_back(_Enter{l2, f});
          }
        }
      }
    } else if (std::holds_alternative<_Call1>(_frame)) {
      auto _f = std::move(std::get<_Call1>(_frame));
      _stack.emplace_back(_Call2{std::move(_result)});
      _stack.emplace_back(_Enter{std::move(_f._s0), _f._s1});
    } else {
      auto _f = std::move(std::get<_Call2>(_frame));
      _result = merge(_result, _f._s0);
    }
  }
  return _result;
}

List<unsigned int> LoopifySorting::merge_sort(const List<unsigned int> &l) {
  return merge_sort_fuel(len_impl<unsigned int>(l), l);
}

std::pair<List<unsigned int>, List<unsigned int>>
LoopifySorting::partition(const unsigned int &pivot,
                          const List<unsigned int> &l) {
  struct _Enter {
    const List<unsigned int> *l;
  };

  struct _Call1 {
    unsigned int _s0;
    unsigned int _s1;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::pair<List<unsigned int>, List<unsigned int>> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{&l});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<unsigned int> &l = *(_f.l);
      if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
        _result = std::make_pair(List<unsigned int>::nil(),
                                 List<unsigned int>::nil());
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<unsigned int>::Cons>(l.v());
        _stack.emplace_back(_Call1{d_a0, pivot});
        _stack.emplace_back(_Enter{d_a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Call1>(_frame));
      unsigned int d_a0 = std::move(_f._s0);
      const unsigned int &pivot = _f._s1;
      const List<unsigned int> &lo = _result.first;
      const List<unsigned int> &hi = _result.second;
      if (d_a0 <= pivot) {
        _result = std::make_pair(List<unsigned int>::cons(d_a0, lo), hi);
      } else {
        _result = std::make_pair(lo, List<unsigned int>::cons(d_a0, hi));
      }
    }
  }
  return _result;
}

List<unsigned int> LoopifySorting::quicksort_fuel(const unsigned int &fuel,
                                                  List<unsigned int> l) {
  struct _Enter {
    List<unsigned int> l;
    unsigned int fuel;
  };

  struct _Call1 {
    List<unsigned int> _s0;
    unsigned int _s1;
    unsigned int _s2;
  };

  struct _Call2 {
    List<unsigned int> _s0;
    unsigned int _s1;
  };

  using _Frame = std::variant<_Enter, _Call1, _Call2>;
  List<unsigned int> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{l, fuel});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      List<unsigned int> l = std::move(_f.l);
      const unsigned int &fuel = _f.fuel;
      if (fuel <= 0) {
        _result = std::move(l);
      } else {
        unsigned int f = fuel - 1;
        if (std::holds_alternative<typename List<unsigned int>::Nil>(
                l.v_mut())) {
          _result = List<unsigned int>::nil();
        } else {
          auto &[d_a0, d_a1] =
              std::get<typename List<unsigned int>::Cons>(l.v_mut());
          auto _cs = partition(d_a0, *(d_a1));
          const List<unsigned int> &lo = _cs.first;
          const List<unsigned int> &hi = _cs.second;
          _stack.emplace_back(_Call1{lo, f, d_a0});
          _stack.emplace_back(_Enter{hi, f});
        }
      }
    } else if (std::holds_alternative<_Call1>(_frame)) {
      auto _f = std::move(std::get<_Call1>(_frame));
      _stack.emplace_back(_Call2{std::move(_result), _f._s2});
      _stack.emplace_back(_Enter{std::move(_f._s0), _f._s1});
    } else {
      auto _f = std::move(std::get<_Call2>(_frame));
      _result = _result.app(List<unsigned int>::cons(_f._s1, _f._s0));
    }
  }
  return _result;
}

List<unsigned int> LoopifySorting::quicksort(const List<unsigned int> &l) {
  return quicksort_fuel(len_impl<unsigned int>(l), l);
}

bool LoopifySorting::is_sorted_aux(const unsigned int &prev,
                                   const List<unsigned int> &l) {
  bool _result;
  const List<unsigned int> *_loop_l = &l;
  unsigned int _loop_prev = prev;
  while (true) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(
            _loop_l->v())) {
      _result = true;
      break;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<unsigned int>::Cons>(_loop_l->v());
      if (_loop_prev <= d_a0) {
        const List<unsigned int> *_next_l = d_a1.get();
        unsigned int _next_prev = d_a0;
        _loop_l = _next_l;
        _loop_prev = std::move(_next_prev);
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
    const auto &[d_a0, d_a1] =
        std::get<typename List<unsigned int>::Cons>(l.v());
    return is_sorted_aux(d_a0, *(d_a1));
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
        if (d_a0 == d_a00) {
          _loop_l = d_a1.get();
          continue;
        } else {
          auto _cell = std::make_unique<List<unsigned int>>(
              typename List<unsigned int>::Cons(d_a0, nullptr));
          *(_write) = std::move(_cell);
          _write =
              &std::get<typename List<unsigned int>::Cons>((*_write)->v_mut())
                   .d_a1;
          _loop_l = d_a1.get();
          continue;
        }
      }
    }
  }
  return std::move(*(_head));
}

/// uniq_sorted variant that preserves order.
List<unsigned int>
LoopifySorting::uniq_sorted_aux(const unsigned int &prev, const bool &seen,
                                const List<unsigned int> &l) {
  std::unique_ptr<List<unsigned int>> _head{};
  std::unique_ptr<List<unsigned int>> *_write = &_head;
  const List<unsigned int> *_loop_l = &l;
  bool _loop_seen = seen;
  unsigned int _loop_prev = prev;
  while (true) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(
            _loop_l->v())) {
      *(_write) =
          std::make_unique<List<unsigned int>>(List<unsigned int>::nil());
      break;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<unsigned int>::Cons>(_loop_l->v());
      if (_loop_seen) {
        if (_loop_prev == d_a0) {
          const List<unsigned int> *_next_l = d_a1.get();
          bool _next_seen = true;
          unsigned int _next_prev = d_a0;
          _loop_l = _next_l;
          _loop_seen = std::move(_next_seen);
          _loop_prev = std::move(_next_prev);
          continue;
        } else {
          auto _cell = std::make_unique<List<unsigned int>>(
              typename List<unsigned int>::Cons(d_a0, nullptr));
          *(_write) = std::move(_cell);
          _write =
              &std::get<typename List<unsigned int>::Cons>((*_write)->v_mut())
                   .d_a1;
          const List<unsigned int> *_next_l = d_a1.get();
          bool _next_seen = true;
          unsigned int _next_prev = d_a0;
          _loop_l = _next_l;
          _loop_seen = std::move(_next_seen);
          _loop_prev = std::move(_next_prev);
          continue;
        }
      } else {
        auto _cell = std::make_unique<List<unsigned int>>(
            typename List<unsigned int>::Cons(d_a0, nullptr));
        *(_write) = std::move(_cell);
        _write =
            &std::get<typename List<unsigned int>::Cons>((*_write)->v_mut())
                 .d_a1;
        const List<unsigned int> *_next_l = d_a1.get();
        bool _next_seen = true;
        unsigned int _next_prev = d_a0;
        _loop_l = _next_l;
        _loop_seen = std::move(_next_seen);
        _loop_prev = std::move(_next_prev);
        continue;
      }
    }
  }
  return std::move(*(_head));
}

List<unsigned int> LoopifySorting::uniq_sorted(const List<unsigned int> &l) {
  return uniq_sorted_aux(0u, false, l);
}
