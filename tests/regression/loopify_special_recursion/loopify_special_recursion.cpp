#include <loopify_special_recursion.h>

List<unsigned int>
LoopifySpecialRecursion::process_twice_fuel(const unsigned int fuel,
                                            const List<unsigned int> &l) {
  struct _Enter {
    List<unsigned int> l;
    unsigned int fuel;
  };

  /// Continuation: saves [d_a0, fuel_] across recursive call, then processes
  /// rest.
  struct _Cont1 {
    unsigned int d_a0;
    unsigned int fuel_;
  };

  /// Continuation: saves [d_a0] across recursive call, then processes rest.
  struct _Cont2 {
    unsigned int d_a0;
  };

  using _Frame = std::variant<_Enter, _Cont1, _Cont2>;
  List<unsigned int> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{l, fuel});
  /// Frame dispatch: _Enter, _Cont1, _Cont2.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<unsigned int> &l = _f.l;
      const unsigned int fuel = _f.fuel;
      if (fuel <= 0) {
        _result = List<unsigned int>::nil();
      } else {
        unsigned int fuel_ = fuel - 1;
        if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
          _result = List<unsigned int>::nil();
        } else {
          const auto &[d_a0, d_a1] =
              std::get<typename List<unsigned int>::Cons>(l.v());
          _stack.emplace_back(_Cont1{d_a0, fuel_});
          _stack.emplace_back(_Enter{std::move(*(d_a1)), fuel_});
        }
      }
    } else if (std::holds_alternative<_Cont1>(_frame)) {
      auto _f = std::move(std::get<_Cont1>(_frame));
      unsigned int d_a0 = _f.d_a0;
      unsigned int fuel_ = _f.fuel_;
      List<unsigned int> first = _result;
      _stack.emplace_back(_Cont2{d_a0});
      _stack.emplace_back(_Enter{std::move(first), fuel_});
    } else {
      auto _f = std::move(std::get<_Cont2>(_frame));
      unsigned int d_a0 = _f.d_a0;
      List<unsigned int> second = _result;
      _result = List<unsigned int>::cons(d_a0, std::move(second));
    }
  }
  return _result;
}

List<unsigned int>
LoopifySpecialRecursion::process_twice(const List<unsigned int> &l) {
  return process_twice_fuel((l.length() * l.length()), l);
}

List<unsigned int>
LoopifySpecialRecursion::double_append(const List<unsigned int> &l1,
                                       List<unsigned int> l2) {
  struct _Enter {
    List<unsigned int> l2;
    const List<unsigned int> *l1;
  };

  /// Continuation: saves [d_a0] across recursive call, then processes rest.
  struct _Cont1 {
    unsigned int d_a0;
  };

  using _Frame = std::variant<_Enter, _Cont1>;
  List<unsigned int> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{l2, &l1});
  /// Frame dispatch: _Enter, _Cont1.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      List<unsigned int> l2 = std::move(_f.l2);
      const List<unsigned int> &l1 = *(_f.l1);
      if (std::holds_alternative<typename List<unsigned int>::Nil>(l1.v())) {
        _result = std::move(l2);
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<unsigned int>::Cons>(l1.v());
        _stack.emplace_back(_Cont1{d_a0});
        _stack.emplace_back(_Enter{std::move(l2), d_a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Cont1>(_frame));
      unsigned int d_a0 = _f.d_a0;
      List<unsigned int> rest = _result;
      _result = List<unsigned int>::cons(d_a0, rest.app(rest));
    }
  }
  return _result;
}

List<unsigned int>
LoopifySpecialRecursion::remove_if_sum_even(const List<unsigned int> &l) {
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
      unsigned int next_val = [&]() {
        auto &&_sv0 = *(d_a1);
        if (std::holds_alternative<typename List<unsigned int>::Nil>(
                _sv0.v())) {
          return 0u;
        } else {
          const auto &[d_a00, d_a10] =
              std::get<typename List<unsigned int>::Cons>(_sv0.v());
          return d_a00;
        }
      }();
      if ((2u ? (d_a0 + next_val) % 2u : (d_a0 + next_val)) == 0u) {
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
  return std::move(*(_head));
}

List<unsigned int>
LoopifySpecialRecursion::reverse_insert(const unsigned int x,
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
      if (d_a0 < x) {
        auto _cell = std::make_unique<List<unsigned int>>(
            typename List<unsigned int>::Cons(d_a0, nullptr));
        *(_write) = std::move(_cell);
        _write =
            &std::get<typename List<unsigned int>::Cons>((*_write)->v_mut())
                 .d_a1;
        _loop_l = std::move(*(d_a1));
        continue;
      } else {
        *(_write) = std::make_unique<List<unsigned int>>(
            List<unsigned int>::cons(x, _loop_l));
        break;
      }
    }
  }
  return std::move(*(_head));
}

List<unsigned int> LoopifySpecialRecursion::collect_sorted(
    const LoopifySpecialRecursion::tree &t) {
  struct _Enter {
    const LoopifySpecialRecursion::tree *t;
  };

  /// Intermediate: saves [_s0, d_a1], dispatches next recursive call.
  struct _After2 {
    const LoopifySpecialRecursion::tree *_s0;
    unsigned int d_a1;
  };

  /// Combiner: receives first result, combines with second recursive call.
  struct _Combine1 {
    List<unsigned int> _result;
    unsigned int d_a1;
  };

  using _Frame = std::variant<_Enter, _After2, _Combine1>;
  List<unsigned int> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{&t});
  /// Frame dispatch: _Enter, _After2, _Combine1.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const LoopifySpecialRecursion::tree &t = *(_f.t);
      if (std::holds_alternative<typename LoopifySpecialRecursion::tree::Leaf>(
              t.v())) {
        _result = List<unsigned int>::nil();
      } else {
        const auto &[d_a0, d_a1, d_a2] =
            std::get<typename LoopifySpecialRecursion::tree::Node>(t.v());
        _stack.emplace_back(_After2{d_a0.get(), d_a1});
        _stack.emplace_back(_Enter{d_a2.get()});
      }
    } else if (std::holds_alternative<_After2>(_frame)) {
      auto _f = std::move(std::get<_After2>(_frame));
      _stack.emplace_back(_Combine1{std::move(_result), _f.d_a1});
      _stack.emplace_back(_Enter{_f._s0});
    } else {
      auto _f = std::move(std::get<_Combine1>(_frame));
      _result = _result.app(List<unsigned int>::cons(_f.d_a1, _f._result));
    }
  }
  return _result;
}

unsigned int
LoopifySpecialRecursion::sum_odd_indices_aux(const List<unsigned int> &l,
                                             const unsigned int idx) {
  struct _Enter {
    unsigned int idx;
    const List<unsigned int> *l;
  };

  /// Continuation: saves [d_a0] across recursive call.
  struct _Resume1 {
    unsigned int d_a0;
  };

  using _Frame = std::variant<_Enter, _Resume1>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{idx, &l});
  /// Frame dispatch: _Enter, _Resume1.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const unsigned int idx = _f.idx;
      const List<unsigned int> &l = *(_f.l);
      if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
        _result = 0u;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<unsigned int>::Cons>(l.v());
        if ((2u ? idx % 2u : idx) == 1u) {
          _stack.emplace_back(_Resume1{d_a0});
          _stack.emplace_back(_Enter{(idx + 1u), d_a1.get()});
        } else {
          _stack.emplace_back(_Enter{(idx + 1u), d_a1.get()});
        }
      }
    } else {
      auto _f = std::move(std::get<_Resume1>(_frame));
      _result = (_f.d_a0 + _result);
    }
  }
  return _result;
}

unsigned int
LoopifySpecialRecursion::sum_odd_indices(const List<unsigned int> &l) {
  return sum_odd_indices_aux(l, 0u);
}

unsigned int
LoopifySpecialRecursion::categorize_by(const unsigned int k,
                                       const List<unsigned int> &l) {
  struct _Enter {
    const List<unsigned int> *l;
  };

  /// Continuation: saves [_s0] across recursive call.
  struct _Resume1 {
    decltype(3u) _s0;
  };

  /// Continuation: saves [_s0] across recursive call.
  struct _Resume2 {
    decltype(2u) _s0;
  };

  /// Continuation: saves [_s0] across recursive call.
  struct _Resume3 {
    decltype(1u) _s0;
  };

  using _Frame = std::variant<_Enter, _Resume1, _Resume2, _Resume3>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{&l});
  /// Frame dispatch: _Enter, _Resume1, _Resume2, _Resume3.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<unsigned int> &l = *(_f.l);
      if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
        _result = 0u;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<unsigned int>::Cons>(l.v());
        if (k < d_a0) {
          _stack.emplace_back(_Resume1{3u});
          _stack.emplace_back(_Enter{d_a1.get()});
        } else {
          if (d_a0 == k) {
            _stack.emplace_back(_Resume2{2u});
            _stack.emplace_back(_Enter{d_a1.get()});
          } else {
            _stack.emplace_back(_Resume3{1u});
            _stack.emplace_back(_Enter{d_a1.get()});
          }
        }
      }
    } else if (std::holds_alternative<_Resume1>(_frame)) {
      auto _f = std::move(std::get<_Resume1>(_frame));
      _result = (_f._s0 + _result);
    } else if (std::holds_alternative<_Resume2>(_frame)) {
      auto _f = std::move(std::get<_Resume2>(_frame));
      _result = (_f._s0 + _result);
    } else {
      auto _f = std::move(std::get<_Resume3>(_frame));
      _result = (_f._s0 + _result);
    }
  }
  return _result;
}

List<unsigned int>
LoopifySpecialRecursion::between(const unsigned int lo, const unsigned int hi,
                                 const List<unsigned int> &l) {
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
      if (lo <= d_a0) {
        if (d_a0 <= hi) {
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
      } else {
        _loop_l = d_a1.get();
        continue;
      }
    }
  }
  return std::move(*(_head));
}

List<unsigned int>
LoopifySpecialRecursion::merge_levels(const List<List<unsigned int>> &ll) {
  struct _Enter {
    const List<List<unsigned int>> *ll;
  };

  /// Continuation: saves [d_a0] across recursive call.
  struct _Resume1 {
    List<unsigned int> d_a0;
  };

  using _Frame = std::variant<_Enter, _Resume1>;
  List<unsigned int> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{&ll});
  /// Frame dispatch: _Enter, _Resume1.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<List<unsigned int>> &ll = *(_f.ll);
      if (std::holds_alternative<typename List<List<unsigned int>>::Nil>(
              ll.v())) {
        _result = List<unsigned int>::nil();
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<List<unsigned int>>::Cons>(ll.v());
        _stack.emplace_back(_Resume1{d_a0});
        _stack.emplace_back(_Enter{d_a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Resume1>(_frame));
      _result = _f.d_a0.app(_result);
    }
  }
  return _result;
}
