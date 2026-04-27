#include <loopify_special_recursion.h>

__attribute__((pure)) List<unsigned int>
LoopifySpecialRecursion::process_twice_fuel(const unsigned int &fuel,
                                            const List<unsigned int> &l) {
  struct _Enter {
    const List<unsigned int> l;
    const unsigned int fuel;
  };

  struct _Call1 {
    unsigned int _s0;
    unsigned int _s1;
  };

  struct _Call2 {
    unsigned int _s0;
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
      const List<unsigned int> l = _f.l;
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
          _stack.emplace_back(_Call1{d_a0, fuel_});
          _stack.emplace_back(_Enter{*(d_a1), fuel_});
        }
      }
    } else if (std::holds_alternative<_Call1>(_frame)) {
      auto _f = std::move(std::get<_Call1>(_frame));
      unsigned int d_a0 = _f._s0;
      unsigned int fuel_ = _f._s1;
      List<unsigned int> first = _result;
      _stack.emplace_back(_Call2{d_a0});
      _stack.emplace_back(_Enter{first, fuel_});
    } else {
      auto _f = std::move(std::get<_Call2>(_frame));
      unsigned int d_a0 = _f._s0;
      List<unsigned int> second = _result;
      _result = List<unsigned int>::cons(d_a0, second);
    }
  }
  return _result;
}

__attribute__((pure)) List<unsigned int>
LoopifySpecialRecursion::process_twice(const List<unsigned int> &l) {
  return process_twice_fuel((l.length() * l.length()), l);
}

__attribute__((pure)) List<unsigned int>
LoopifySpecialRecursion::double_append(const List<unsigned int> &l1,
                                       List<unsigned int> l2) {
  struct _Enter {
    const List<unsigned int> l1;
  };

  struct _Call1 {
    unsigned int _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  List<unsigned int> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{l1});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<unsigned int> l1 = _f.l1;
      if (std::holds_alternative<typename List<unsigned int>::Nil>(l1.v())) {
        _result = l2;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<unsigned int>::Cons>(l1.v());
        _stack.emplace_back(_Call1{d_a0});
        _stack.emplace_back(_Enter{*(d_a1)});
      }
    } else {
      auto _f = std::move(std::get<_Call1>(_frame));
      unsigned int d_a0 = _f._s0;
      List<unsigned int> rest = _result;
      _result = List<unsigned int>::cons(d_a0, rest.app(rest));
    }
  }
  return _result;
}

__attribute__((pure)) List<unsigned int>
LoopifySpecialRecursion::remove_if_sum_even(const List<unsigned int> &l) {
  std::unique_ptr<List<unsigned int>> _head{};
  std::unique_ptr<List<unsigned int>> *_write = &_head;
  List<unsigned int> _loop_l = l;
  while (true) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(_loop_l.v())) {
      *(_write) =
          std::make_unique<List<unsigned int>>(List<unsigned int>::nil());
      break;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<unsigned int>::Cons>(_loop_l.v());
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
        _loop_l = *(d_a1);
        continue;
      } else {
        auto _cell = std::make_unique<List<unsigned int>>(
            typename List<unsigned int>::Cons(d_a0, nullptr));
        *(_write) = std::move(_cell);
        _write =
            &std::get<typename List<unsigned int>::Cons>((*_write)->v_mut())
                 .d_a1;
        _loop_l = *(d_a1);
        continue;
      }
    }
  }
  return std::move(*(_head));
}

__attribute__((pure)) List<unsigned int>
LoopifySpecialRecursion::reverse_insert(unsigned int x, List<unsigned int> l) {
  std::unique_ptr<List<unsigned int>> _head{};
  std::unique_ptr<List<unsigned int>> *_write = &_head;
  List<unsigned int> _loop_l = std::move(l);
  while (true) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(_loop_l.v())) {
      *(_write) = std::make_unique<List<unsigned int>>(
          List<unsigned int>::cons(x, List<unsigned int>::nil()));
      break;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<unsigned int>::Cons>(_loop_l.v());
      if (d_a0 < x) {
        auto _cell = std::make_unique<List<unsigned int>>(
            typename List<unsigned int>::Cons(d_a0, nullptr));
        *(_write) = std::move(_cell);
        _write =
            &std::get<typename List<unsigned int>::Cons>((*_write)->v_mut())
                 .d_a1;
        _loop_l = *(d_a1);
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

__attribute__((pure)) List<unsigned int>
LoopifySpecialRecursion::collect_sorted(
    const LoopifySpecialRecursion::tree &t) {
  struct _Enter {
    const LoopifySpecialRecursion::tree t;
  };

  struct _Call1 {
    LoopifySpecialRecursion::tree _s0;
    unsigned int _s1;
  };

  struct _Call2 {
    List<unsigned int> _s0;
    unsigned int _s1;
  };

  using _Frame = std::variant<_Enter, _Call1, _Call2>;
  List<unsigned int> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{t});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const LoopifySpecialRecursion::tree t = _f.t;
      if (std::holds_alternative<typename LoopifySpecialRecursion::tree::Leaf>(
              t.v())) {
        _result = List<unsigned int>::nil();
      } else {
        const auto &[d_a0, d_a1, d_a2] =
            std::get<typename LoopifySpecialRecursion::tree::Node>(t.v());
        _stack.emplace_back(_Call1{*(d_a0), d_a1});
        _stack.emplace_back(_Enter{*(d_a2)});
      }
    } else if (std::holds_alternative<_Call1>(_frame)) {
      auto _f = std::move(std::get<_Call1>(_frame));
      _stack.emplace_back(_Call2{_result, _f._s1});
      _stack.emplace_back(_Enter{_f._s0});
    } else {
      auto _f = std::move(std::get<_Call2>(_frame));
      _result = _result.app(List<unsigned int>::cons(_f._s1, _f._s0));
    }
  }
  return _result;
}

__attribute__((pure)) unsigned int
LoopifySpecialRecursion::sum_odd_indices_aux(const List<unsigned int> &l,
                                             const unsigned int &idx) {
  struct _Enter {
    const unsigned int idx;
    const List<unsigned int> l;
  };

  struct _Call1 {
    unsigned int _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{idx, l});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const unsigned int idx = _f.idx;
      const List<unsigned int> l = _f.l;
      if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
        _result = 0u;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<unsigned int>::Cons>(l.v());
        if ((2u ? idx % 2u : idx) == 1u) {
          _stack.emplace_back(_Call1{d_a0});
          _stack.emplace_back(_Enter{(idx + 1u), *(d_a1)});
        } else {
          _stack.emplace_back(_Enter{(idx + 1u), *(d_a1)});
        }
      }
    } else {
      auto _f = std::move(std::get<_Call1>(_frame));
      _result = (_f._s0 + _result);
    }
  }
  return _result;
}

__attribute__((pure)) unsigned int
LoopifySpecialRecursion::sum_odd_indices(const List<unsigned int> &l) {
  return sum_odd_indices_aux(l, 0u);
}

__attribute__((pure)) unsigned int
LoopifySpecialRecursion::categorize_by(const unsigned int &k,
                                       const List<unsigned int> &l) {
  struct _Enter {
    const List<unsigned int> l;
  };

  struct _Call1 {
    decltype(3u) _s0;
  };

  struct _Call2 {
    decltype(2u) _s0;
  };

  struct _Call3 {
    decltype(1u) _s0;
  };

  using _Frame = std::variant<_Enter, _Call1, _Call2, _Call3>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{l});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<unsigned int> l = _f.l;
      if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
        _result = 0u;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<unsigned int>::Cons>(l.v());
        if (k < d_a0) {
          _stack.emplace_back(_Call1{3u});
          _stack.emplace_back(_Enter{*(d_a1)});
        } else {
          if (d_a0 == k) {
            _stack.emplace_back(_Call2{2u});
            _stack.emplace_back(_Enter{*(d_a1)});
          } else {
            _stack.emplace_back(_Call3{1u});
            _stack.emplace_back(_Enter{*(d_a1)});
          }
        }
      }
    } else if (std::holds_alternative<_Call1>(_frame)) {
      auto _f = std::move(std::get<_Call1>(_frame));
      _result = (_f._s0 + _result);
    } else if (std::holds_alternative<_Call2>(_frame)) {
      auto _f = std::move(std::get<_Call2>(_frame));
      _result = (_f._s0 + _result);
    } else {
      auto _f = std::move(std::get<_Call3>(_frame));
      _result = (_f._s0 + _result);
    }
  }
  return _result;
}

__attribute__((pure)) List<unsigned int>
LoopifySpecialRecursion::between(const unsigned int &lo, const unsigned int &hi,
                                 const List<unsigned int> &l) {
  std::unique_ptr<List<unsigned int>> _head{};
  std::unique_ptr<List<unsigned int>> *_write = &_head;
  List<unsigned int> _loop_l = l;
  while (true) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(_loop_l.v())) {
      *(_write) =
          std::make_unique<List<unsigned int>>(List<unsigned int>::nil());
      break;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<unsigned int>::Cons>(_loop_l.v());
      if (lo <= d_a0) {
        if (d_a0 <= hi) {
          auto _cell = std::make_unique<List<unsigned int>>(
              typename List<unsigned int>::Cons(d_a0, nullptr));
          *(_write) = std::move(_cell);
          _write =
              &std::get<typename List<unsigned int>::Cons>((*_write)->v_mut())
                   .d_a1;
          _loop_l = *(d_a1);
          continue;
        } else {
          _loop_l = *(d_a1);
          continue;
        }
      } else {
        _loop_l = *(d_a1);
        continue;
      }
    }
  }
  return std::move(*(_head));
}

__attribute__((pure)) List<unsigned int>
LoopifySpecialRecursion::merge_levels(const List<List<unsigned int>> &ll) {
  struct _Enter {
    const List<List<unsigned int>> ll;
  };

  struct _Call1 {
    List<unsigned int> _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  List<unsigned int> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{ll});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<List<unsigned int>> ll = _f.ll;
      if (std::holds_alternative<typename List<List<unsigned int>>::Nil>(
              ll.v())) {
        _result = List<unsigned int>::nil();
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<List<unsigned int>>::Cons>(ll.v());
        _stack.emplace_back(_Call1{d_a0});
        _stack.emplace_back(_Enter{*(d_a1)});
      }
    } else {
      auto _f = std::move(std::get<_Call1>(_frame));
      _result = _f._s0.app(_result);
    }
  }
  return _result;
}
