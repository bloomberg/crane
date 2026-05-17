#include "loopify_grouping.h"

List<List<unsigned int>>
LoopifyGrouping::prepend_to_groups(unsigned int x, bool same,
                                   List<List<unsigned int>> groups) {
  if (same) {
    if (std::holds_alternative<typename List<List<unsigned int>>::Nil>(
            groups.v_mut())) {
      return List<List<unsigned int>>::cons(
          List<unsigned int>::cons(x, List<unsigned int>::nil()),
          List<List<unsigned int>>::nil());
    } else {
      auto &[a0, a1] =
          std::get<typename List<List<unsigned int>>::Cons>(groups.v_mut());
      return List<List<unsigned int>>::cons(
          List<unsigned int>::cons(x, std::move(a0)), *a1);
    }
  } else {
    return List<List<unsigned int>>::cons(
        List<unsigned int>::cons(x, List<unsigned int>::nil()),
        std::move(groups));
  }
}

List<List<unsigned int>> LoopifyGrouping::group_fuel(
    unsigned int fuel,
    const List<unsigned int>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    List<unsigned int> l;
    unsigned int fuel;
  };

  /// _Cont_Cons: saves [a0, a00], resumes after recursive call, then processes
  /// rest.
  struct _Cont_Cons {
    unsigned int a0;
    unsigned int a00;
  };

  using _Frame = std::variant<_Enter, _Cont_Cons>;
  List<List<unsigned int>> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{l, fuel});
  /// Loopified group_fuel: _Enter -> _Cont_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<unsigned int> &l = _f.l;
      unsigned int fuel = _f.fuel;
      if (fuel <= 0) {
        _result = List<List<unsigned int>>::nil();
      } else {
        unsigned int fuel_ = fuel - 1;
        if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
          _result = List<List<unsigned int>>::nil();
        } else {
          const auto &[a0, a1] =
              std::get<typename List<unsigned int>::Cons>(l.v());
          auto &&_sv0 = *a1;
          if (std::holds_alternative<typename List<unsigned int>::Nil>(
                  _sv0.v())) {
            _result = List<List<unsigned int>>::cons(
                List<unsigned int>::cons(a0, List<unsigned int>::nil()),
                List<List<unsigned int>>::nil());
          } else {
            const auto &[a00, a10] =
                std::get<typename List<unsigned int>::Cons>(_sv0.v());
            _stack.emplace_back(_Cont_Cons{a0, a00});
            _stack.emplace_back(
                _Enter{List<unsigned int>::cons(a00, *a10), fuel_});
          }
        }
      }
    } else {
      auto _f = std::move(std::get<_Cont_Cons>(_frame));
      unsigned int a0 = _f.a0;
      unsigned int a00 = _f.a00;
      List<List<unsigned int>> rec_result = _result;
      _result = prepend_to_groups(a0, a0 == a00, std::move(rec_result));
    }
  }
  return _result;
}

List<List<unsigned int>> LoopifyGrouping::group(const List<unsigned int> &l) {
  return group_fuel(l.length(), l);
}

bool LoopifyGrouping::elem(unsigned int x, const List<unsigned int> &l) {
  bool _result;
  const List<unsigned int> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(
            _loop_l->v())) {
      _result = false;
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename List<unsigned int>::Cons>(_loop_l->v());
      if (x == a0) {
        _result = true;
        break;
      } else {
        _loop_l = a1.get();
      }
    }
  }
  return _result;
}

List<unsigned int> LoopifyGrouping::nub(
    const List<unsigned int>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<unsigned int> *l;
  };

  /// _Cont_Cons: saves [a0], resumes after recursive call, then processes rest.
  struct _Cont_Cons {
    unsigned int a0;
  };

  using _Frame = std::variant<_Enter, _Cont_Cons>;
  List<unsigned int> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l});
  /// Loopified nub: _Enter -> _Cont_Cons.
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
        _stack.emplace_back(_Cont_Cons{a0});
        _stack.emplace_back(_Enter{a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Cont_Cons>(_frame));
      unsigned int a0 = _f.a0;
      List<unsigned int> rest = _result;
      if (elem(a0, rest)) {
        _result = std::move(rest);
      } else {
        _result = List<unsigned int>::cons(a0, std::move(rest));
      }
    }
  }
  return _result;
}

List<unsigned int> LoopifyGrouping::remove_elem(unsigned int x,
                                                const List<unsigned int> &l) {
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
      if (x == a0) {
        _loop_l = a1.get();
        continue;
      } else {
        auto _cell = std::make_unique<List<unsigned int>>(
            typename List<unsigned int>::Cons(a0, nullptr));
        *_write = std::move(_cell);
        _write =
            &std::get<typename List<unsigned int>::Cons>((*_write)->v_mut()).a1;
        _loop_l = a1.get();
        continue;
      }
    }
  }
  return std::move(*_head);
}

std::pair<std::pair<List<unsigned int>, List<unsigned int>>, List<unsigned int>>
LoopifyGrouping::partition3(
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
  std::pair<std::pair<List<unsigned int>, List<unsigned int>>,
            List<unsigned int>>
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
      const List<unsigned int> &l = *_f.l;
      if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
        _result = std::make_pair(std::make_pair(List<unsigned int>::nil(),
                                                List<unsigned int>::nil()),
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
      const std::pair<List<unsigned int>, List<unsigned int>> &p =
          _result.first;
      const List<unsigned int> &greater = _result.second;
      const List<unsigned int> &less = p.first;
      const List<unsigned int> &equal = p.second;
      if (a0 < pivot) {
        _result = std::make_pair(
            std::make_pair(List<unsigned int>::cons(a0, less), equal), greater);
      } else {
        if (pivot < a0) {
          _result = std::make_pair(std::make_pair(less, equal),
                                   List<unsigned int>::cons(a0, greater));
        } else {
          _result = std::make_pair(
              std::make_pair(less, List<unsigned int>::cons(a0, equal)),
              greater);
        }
      }
    }
  }
  return _result;
}

unsigned int LoopifyGrouping::count_elem(
    unsigned int x,
    const List<unsigned int>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<unsigned int> *l;
  };

  /// _Resume1: saves [_s0], resumes after recursive call with _result.
  struct _Resume1 {
    decltype(1u) _s0;
  };

  using _Frame = std::variant<_Enter, _Resume1>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l});
  /// Loopified count_elem: _Enter -> _Resume1.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<unsigned int> &l = *_f.l;
      if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
        _result = 0u;
      } else {
        const auto &[a0, a1] =
            std::get<typename List<unsigned int>::Cons>(l.v());
        if (x == a0) {
          _stack.emplace_back(_Resume1{1u});
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

List<std::pair<unsigned int, unsigned int>>
LoopifyGrouping::group_pairs(const List<unsigned int> &l) {
  std::unique_ptr<List<std::pair<unsigned int, unsigned int>>> _head{};
  std::unique_ptr<List<std::pair<unsigned int, unsigned int>>> *_write = &_head;
  const List<unsigned int> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(
            _loop_l->v())) {
      *_write = std::make_unique<List<std::pair<unsigned int, unsigned int>>>(
          List<std::pair<unsigned int, unsigned int>>::nil());
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename List<unsigned int>::Cons>(_loop_l->v());
      auto &&_sv = *a1;
      if (std::holds_alternative<typename List<unsigned int>::Nil>(_sv.v())) {
        *_write = std::make_unique<List<std::pair<unsigned int, unsigned int>>>(
            List<std::pair<unsigned int, unsigned int>>::nil());
        break;
      } else {
        auto &&_sv1 = *a1;
        if (std::holds_alternative<typename List<unsigned int>::Nil>(
                _sv1.v())) {
          *_write =
              std::make_unique<List<std::pair<unsigned int, unsigned int>>>(
                  List<std::pair<unsigned int, unsigned int>>::nil());
          break;
        } else {
          const auto &[a01, a11] =
              std::get<typename List<unsigned int>::Cons>(_sv1.v());
          auto _cell =
              std::make_unique<List<std::pair<unsigned int, unsigned int>>>(
                  typename List<std::pair<unsigned int, unsigned int>>::Cons(
                      std::make_pair(a0, a01), nullptr));
          *_write = std::move(_cell);
          _write =
              &std::get<
                   typename List<std::pair<unsigned int, unsigned int>>::Cons>(
                   (*_write)->v_mut())
                   .a1;
          _loop_l = a11.get();
          continue;
        }
      }
    }
  }
  return std::move(*_head);
}
