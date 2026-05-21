#include "loopify_grouping.h"

List<List<uint64_t>>
LoopifyGrouping::prepend_to_groups(uint64_t x, bool same,
                                   List<List<uint64_t>> groups) {
  if (same) {
    if (std::holds_alternative<typename List<List<uint64_t>>::Nil>(
            groups.v_mut())) {
      return List<List<uint64_t>>::cons(
          List<uint64_t>::cons(x, List<uint64_t>::nil()),
          List<List<uint64_t>>::nil());
    } else {
      auto &[a0, a1] =
          std::get<typename List<List<uint64_t>>::Cons>(groups.v_mut());
      return List<List<uint64_t>>::cons(List<uint64_t>::cons(x, std::move(a0)),
                                        *a1);
    }
  } else {
    return List<List<uint64_t>>::cons(
        List<uint64_t>::cons(x, List<uint64_t>::nil()), std::move(groups));
  }
}

List<List<uint64_t>> LoopifyGrouping::group_fuel(
    uint64_t fuel,
    const List<uint64_t>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    List<uint64_t> l;
    uint64_t fuel;
  };

  /// _Cont_Cons: saves [a0, a00], resumes after recursive call, then processes
  /// rest.
  struct _Cont_Cons {
    uint64_t a0;
    uint64_t a00;
  };

  using _Frame = std::variant<_Enter, _Cont_Cons>;
  List<List<uint64_t>> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{l, fuel});
  /// Loopified group_fuel: _Enter -> _Cont_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<uint64_t> &l = _f.l;
      uint64_t fuel = _f.fuel;
      if (fuel <= 0) {
        _result = List<List<uint64_t>>::nil();
      } else {
        uint64_t fuel_ = fuel - 1;
        if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
          _result = List<List<uint64_t>>::nil();
        } else {
          const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
          auto &&_sv0 = *a1;
          if (std::holds_alternative<typename List<uint64_t>::Nil>(_sv0.v())) {
            _result = List<List<uint64_t>>::cons(
                List<uint64_t>::cons(a0, List<uint64_t>::nil()),
                List<List<uint64_t>>::nil());
          } else {
            const auto &[a00, a10] =
                std::get<typename List<uint64_t>::Cons>(_sv0.v());
            _stack.emplace_back(_Cont_Cons{a0, a00});
            _stack.emplace_back(_Enter{List<uint64_t>::cons(a00, *a10), fuel_});
          }
        }
      }
    } else {
      auto _f = std::move(std::get<_Cont_Cons>(_frame));
      uint64_t a0 = _f.a0;
      uint64_t a00 = _f.a00;
      List<List<uint64_t>> rec_result = _result;
      _result = prepend_to_groups(a0, a0 == a00, std::move(rec_result));
    }
  }
  return _result;
}

List<List<uint64_t>> LoopifyGrouping::group(const List<uint64_t> &l) {
  return group_fuel(l.length(), l);
}

bool LoopifyGrouping::elem(uint64_t x, const List<uint64_t> &l) {
  const List<uint64_t> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l->v())) {
      return false;
    } else {
      const auto &[a0, a1] =
          std::get<typename List<uint64_t>::Cons>(_loop_l->v());
      if (x == a0) {
        return true;
      } else {
        _loop_l = a1.get();
      }
    }
  }
}

List<uint64_t> LoopifyGrouping::nub(
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
  List<uint64_t> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l});
  /// Loopified nub: _Enter -> _Cont_Cons.
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
        _stack.emplace_back(_Cont_Cons{a0});
        _stack.emplace_back(_Enter{a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Cont_Cons>(_frame));
      uint64_t a0 = _f.a0;
      List<uint64_t> rest = _result;
      if (elem(a0, rest)) {
        _result = std::move(rest);
      } else {
        _result = List<uint64_t>::cons(a0, std::move(rest));
      }
    }
  }
  return _result;
}

List<uint64_t> LoopifyGrouping::remove_elem(uint64_t x,
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
      if (x == a0) {
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

std::pair<std::pair<List<uint64_t>, List<uint64_t>>, List<uint64_t>>
LoopifyGrouping::partition3(
    uint64_t pivot,
    const List<uint64_t>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<uint64_t> *l;
  };

  /// _Cont_Cons: saves [a0, pivot], resumes after recursive call, then
  /// processes rest.
  struct _Cont_Cons {
    uint64_t a0;
    uint64_t pivot;
  };

  using _Frame = std::variant<_Enter, _Cont_Cons>;
  std::pair<std::pair<List<uint64_t>, List<uint64_t>>, List<uint64_t>>
      _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l});
  /// Loopified partition3: _Enter -> _Cont_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<uint64_t> &l = *_f.l;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
        _result = std::make_pair(
            std::make_pair(List<uint64_t>::nil(), List<uint64_t>::nil()),
            List<uint64_t>::nil());
      } else {
        const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
        _stack.emplace_back(_Cont_Cons{a0, pivot});
        _stack.emplace_back(_Enter{a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Cont_Cons>(_frame));
      uint64_t a0 = _f.a0;
      uint64_t pivot = _f.pivot;
      const std::pair<List<uint64_t>, List<uint64_t>> &p = _result.first;
      const List<uint64_t> &greater = _result.second;
      const List<uint64_t> &less = p.first;
      const List<uint64_t> &equal = p.second;
      if (a0 < pivot) {
        _result = std::make_pair(
            std::make_pair(List<uint64_t>::cons(a0, less), equal), greater);
      } else {
        if (pivot < a0) {
          _result = std::make_pair(std::make_pair(less, equal),
                                   List<uint64_t>::cons(a0, greater));
        } else {
          _result = std::make_pair(
              std::make_pair(less, List<uint64_t>::cons(a0, equal)), greater);
        }
      }
    }
  }
  return _result;
}

uint64_t LoopifyGrouping::count_elem(
    uint64_t x,
    const List<uint64_t>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<uint64_t> *l;
  };

  /// _Resume1: saves [_s0], resumes after recursive call with _result.
  struct _Resume1 {
    decltype(UINT64_C(1)) _s0;
  };

  using _Frame = std::variant<_Enter, _Resume1>;
  uint64_t _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l});
  /// Loopified count_elem: _Enter -> _Resume1.
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
        if (x == a0) {
          _stack.emplace_back(_Resume1{UINT64_C(1)});
          _stack.emplace_back(_Enter{a1.get()});
        } else {
          _stack.emplace_back(_Enter{a1.get()});
        }
      }
    } else {
      auto _f = std::move(std::get<_Resume1>(_frame));
      _result = (_f._s0 + _result);
    }
  }
  return _result;
}

List<std::pair<uint64_t, uint64_t>>
LoopifyGrouping::group_pairs(const List<uint64_t> &l) {
  std::shared_ptr<List<std::pair<uint64_t, uint64_t>>> _head{};
  std::shared_ptr<List<std::pair<uint64_t, uint64_t>>> *_write = &_head;
  const List<uint64_t> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l->v())) {
      *_write = std::make_shared<List<std::pair<uint64_t, uint64_t>>>(
          List<std::pair<uint64_t, uint64_t>>::nil());
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename List<uint64_t>::Cons>(_loop_l->v());
      auto &&_sv = *a1;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(_sv.v())) {
        *_write = std::make_shared<List<std::pair<uint64_t, uint64_t>>>(
            List<std::pair<uint64_t, uint64_t>>::nil());
        break;
      } else {
        auto &&_sv1 = *a1;
        if (std::holds_alternative<typename List<uint64_t>::Nil>(_sv1.v())) {
          *_write = std::make_shared<List<std::pair<uint64_t, uint64_t>>>(
              List<std::pair<uint64_t, uint64_t>>::nil());
          break;
        } else {
          const auto &[a01, a11] =
              std::get<typename List<uint64_t>::Cons>(_sv1.v());
          auto _cell = std::make_shared<List<std::pair<uint64_t, uint64_t>>>(
              typename List<std::pair<uint64_t, uint64_t>>::Cons(
                  std::make_pair(a0, a01), nullptr));
          *_write = std::move(_cell);
          _write =
              &std::get<typename List<std::pair<uint64_t, uint64_t>>::Cons>(
                   (*_write)->v_mut())
                   .l;
          _loop_l = a11.get();
          continue;
        }
      }
    }
  }
  return std::move(*_head);
}
