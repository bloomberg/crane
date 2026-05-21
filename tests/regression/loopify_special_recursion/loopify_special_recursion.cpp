#include "loopify_special_recursion.h"

List<uint64_t> LoopifySpecialRecursion::process_twice_fuel(
    uint64_t fuel,
    const List<uint64_t>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    List<uint64_t> l;
    uint64_t fuel;
  };

  /// _Cont_Cons: saves [a0, fuel_], resumes after recursive call, then
  /// processes rest.
  struct _Cont_Cons {
    uint64_t a0;
    uint64_t fuel_;
  };

  /// _Cont_Cons_1: saves [a0], resumes after recursive call, then processes
  /// rest.
  struct _Cont_Cons_1 {
    uint64_t a0;
  };

  using _Frame = std::variant<_Enter, _Cont_Cons, _Cont_Cons_1>;
  List<uint64_t> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{l, fuel});
  /// Loopified process_twice_fuel: _Enter -> _Cont_Cons -> _Cont_Cons_1.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<uint64_t> &l = _f.l;
      uint64_t fuel = _f.fuel;
      if (fuel <= 0) {
        _result = List<uint64_t>::nil();
      } else {
        uint64_t fuel_ = fuel - 1;
        if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
          _result = List<uint64_t>::nil();
        } else {
          const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
          _stack.emplace_back(_Cont_Cons{a0, fuel_});
          _stack.emplace_back(_Enter{std::move(*a1), fuel_});
        }
      }
    } else if (std::holds_alternative<_Cont_Cons>(_frame)) {
      auto _f = std::move(std::get<_Cont_Cons>(_frame));
      uint64_t a0 = _f.a0;
      uint64_t fuel_ = _f.fuel_;
      List<uint64_t> first = _result;
      _stack.emplace_back(_Cont_Cons_1{a0});
      _stack.emplace_back(_Enter{std::move(first), fuel_});
    } else {
      auto _f = std::move(std::get<_Cont_Cons_1>(_frame));
      uint64_t a0 = _f.a0;
      List<uint64_t> second = _result;
      _result = List<uint64_t>::cons(a0, std::move(second));
    }
  }
  return _result;
}

List<uint64_t> LoopifySpecialRecursion::process_twice(const List<uint64_t> &l) {
  return process_twice_fuel((l.length() * l.length()), l);
}

List<uint64_t> LoopifySpecialRecursion::double_append(
    const List<uint64_t> &l1,
    List<uint64_t>
        l2) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    List<uint64_t> l2;
    const List<uint64_t> *l1;
  };

  /// _Cont_Cons: saves [a0], resumes after recursive call, then processes rest.
  struct _Cont_Cons {
    uint64_t a0;
  };

  using _Frame = std::variant<_Enter, _Cont_Cons>;
  List<uint64_t> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{l2, &l1});
  /// Loopified double_append: _Enter -> _Cont_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      List<uint64_t> l2 = std::move(_f.l2);
      const List<uint64_t> &l1 = *_f.l1;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(l1.v())) {
        _result = std::move(l2);
      } else {
        const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l1.v());
        _stack.emplace_back(_Cont_Cons{a0});
        _stack.emplace_back(_Enter{std::move(l2), a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Cont_Cons>(_frame));
      uint64_t a0 = _f.a0;
      List<uint64_t> rest = _result;
      _result = List<uint64_t>::cons(a0, rest.app(rest));
    }
  }
  return _result;
}

List<uint64_t>
LoopifySpecialRecursion::remove_if_sum_even(const List<uint64_t> &l) {
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
      uint64_t next_val = [&]() {
        auto &&_sv0 = *a1;
        if (std::holds_alternative<typename List<uint64_t>::Nil>(_sv0.v())) {
          return UINT64_C(0);
        } else {
          const auto &[a00, a10] =
              std::get<typename List<uint64_t>::Cons>(_sv0.v());
          return a00;
        }
      }();
      if ((UINT64_C(2) ? (a0 + next_val) % UINT64_C(2) : (a0 + next_val)) ==
          UINT64_C(0)) {
        _loop_l = a1.get();
        continue;
      } else {
        auto _cell = std::make_shared<List<uint64_t>>(
            typename List<uint64_t>::Cons(a0, nullptr));
        *_write = std::move(_cell);
        _write = &std::get<typename List<uint64_t>::Cons>((*_write)->v_mut()).l;
        _loop_l = a1.get();
        continue;
      }
    }
  }
  return std::move(*_head);
}

List<uint64_t> LoopifySpecialRecursion::reverse_insert(uint64_t x,
                                                       List<uint64_t> l) {
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
      if (a0 < x) {
        auto _cell = std::make_shared<List<uint64_t>>(
            typename List<uint64_t>::Cons(std::move(a0), nullptr));
        *_write = std::move(_cell);
        _write = &std::get<typename List<uint64_t>::Cons>((*_write)->v_mut()).l;
        _loop_l = std::move(*a1);
        continue;
      } else {
        *_write =
            std::make_shared<List<uint64_t>>(List<uint64_t>::cons(x, _loop_l));
        break;
      }
    }
  }
  return std::move(*_head);
}

List<uint64_t> LoopifySpecialRecursion::collect_sorted(
    const LoopifySpecialRecursion::tree
        &t) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const LoopifySpecialRecursion::tree *t;
  };

  /// _After_Node: saves [a0, a1], dispatches next recursive call.
  struct _After_Node {
    const LoopifySpecialRecursion::tree *a0;
    uint64_t a1;
  };

  /// _Combine_Node: receives partial results, combines with _result from final
  /// call.
  struct _Combine_Node {
    List<uint64_t> _result;
    uint64_t a1;
  };

  using _Frame = std::variant<_Enter, _After_Node, _Combine_Node>;
  List<uint64_t> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&t});
  /// Loopified collect_sorted: _Enter -> _After_Node -> _Combine_Node.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const LoopifySpecialRecursion::tree &t = *_f.t;
      if (std::holds_alternative<typename LoopifySpecialRecursion::tree::Leaf>(
              t.v())) {
        _result = List<uint64_t>::nil();
      } else {
        const auto &[a0, a1, a2] =
            std::get<typename LoopifySpecialRecursion::tree::Node>(t.v());
        _stack.emplace_back(_After_Node{a0.get(), a1});
        _stack.emplace_back(_Enter{a2.get()});
      }
    } else if (std::holds_alternative<_After_Node>(_frame)) {
      auto _f = std::move(std::get<_After_Node>(_frame));
      _stack.emplace_back(_Combine_Node{std::move(_result), _f.a1});
      _stack.emplace_back(_Enter{_f.a0});
    } else {
      auto _f = std::move(std::get<_Combine_Node>(_frame));
      _result = std::move(_result).app(
          List<uint64_t>::cons(_f.a1, std::move(_f._result)));
    }
  }
  return _result;
}

uint64_t LoopifySpecialRecursion::sum_odd_indices_aux(
    const List<uint64_t> &l,
    uint64_t
        idx) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    uint64_t idx;
    const List<uint64_t> *l;
  };

  /// _Resume1: saves [a0], resumes after recursive call with _result.
  struct _Resume1 {
    uint64_t a0;
  };

  using _Frame = std::variant<_Enter, _Resume1>;
  uint64_t _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{idx, &l});
  /// Loopified sum_odd_indices_aux: _Enter -> _Resume1.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      uint64_t idx = _f.idx;
      const List<uint64_t> &l = *_f.l;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
        if ((UINT64_C(2) ? idx % UINT64_C(2) : idx) == UINT64_C(1)) {
          _stack.emplace_back(_Resume1{a0});
          _stack.emplace_back(_Enter{(idx + UINT64_C(1)), a1.get()});
        } else {
          _stack.emplace_back(_Enter{(idx + UINT64_C(1)), a1.get()});
        }
      }
    } else {
      auto _f = std::move(std::get<_Resume1>(_frame));
      _result = (_f.a0 + _result);
    }
  }
  return _result;
}

uint64_t LoopifySpecialRecursion::sum_odd_indices(const List<uint64_t> &l) {
  return sum_odd_indices_aux(l, UINT64_C(0));
}

uint64_t LoopifySpecialRecursion::categorize_by(
    uint64_t k,
    const List<uint64_t>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<uint64_t> *l;
  };

  /// _Resume1: saves [_s0], resumes after recursive call with _result.
  struct _Resume1 {
    decltype(UINT64_C(3)) _s0;
  };

  /// _Resume2: saves [_s0], resumes after recursive call with _result.
  struct _Resume2 {
    decltype(UINT64_C(2)) _s0;
  };

  /// _Resume3: saves [_s0], resumes after recursive call with _result.
  struct _Resume3 {
    decltype(UINT64_C(1)) _s0;
  };

  using _Frame = std::variant<_Enter, _Resume1, _Resume2, _Resume3>;
  uint64_t _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l});
  /// Loopified categorize_by: _Enter -> _Resume1 -> _Resume2 -> _Resume3.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<uint64_t> &l = *_f.l;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
        if (k < a0) {
          _stack.emplace_back(_Resume1{UINT64_C(3)});
          _stack.emplace_back(_Enter{a1.get()});
        } else {
          if (a0 == k) {
            _stack.emplace_back(_Resume2{UINT64_C(2)});
            _stack.emplace_back(_Enter{a1.get()});
          } else {
            _stack.emplace_back(_Resume3{UINT64_C(1)});
            _stack.emplace_back(_Enter{a1.get()});
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

List<uint64_t> LoopifySpecialRecursion::between(uint64_t lo, uint64_t hi,
                                                const List<uint64_t> &l) {
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
      if (lo <= a0) {
        if (a0 <= hi) {
          auto _cell = std::make_shared<List<uint64_t>>(
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
      } else {
        _loop_l = a1.get();
        continue;
      }
    }
  }
  return std::move(*_head);
}

List<uint64_t> LoopifySpecialRecursion::merge_levels(
    const List<List<uint64_t>>
        &ll) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<List<uint64_t>> *ll;
  };

  /// _Resume_Cons: saves [a0], resumes after recursive call with _result.
  struct _Resume_Cons {
    List<uint64_t> a0;
  };

  using _Frame = std::variant<_Enter, _Resume_Cons>;
  List<uint64_t> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&ll});
  /// Loopified merge_levels: _Enter -> _Resume_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<List<uint64_t>> &ll = *_f.ll;
      if (std::holds_alternative<typename List<List<uint64_t>>::Nil>(ll.v())) {
        _result = List<uint64_t>::nil();
      } else {
        const auto &[a0, a1] =
            std::get<typename List<List<uint64_t>>::Cons>(ll.v());
        _stack.emplace_back(_Resume_Cons{a0});
        _stack.emplace_back(_Enter{a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Resume_Cons>(_frame));
      _result = _f.a0.app(_result);
    }
  }
  return _result;
}
