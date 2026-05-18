#include "loopify_comparators.h"

uint64_t LoopifyComparators::maximum_by(
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
  uint64_t _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l});
  /// Loopified maximum_by: _Enter -> _Cont_Cons.
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
        auto &&_sv = *a1;
        if (std::holds_alternative<typename List<uint64_t>::Nil>(_sv.v())) {
          _result = std::move(a0);
        } else {
          _stack.emplace_back(_Cont_Cons{a0});
          _stack.emplace_back(_Enter{a1.get()});
        }
      }
    } else {
      auto _f = std::move(std::get<_Cont_Cons>(_frame));
      uint64_t a0 = _f.a0;
      uint64_t m = _result;
      if (m < a0) {
        _result = std::move(a0);
      } else {
        _result = std::move(m);
      }
    }
  }
  return _result;
}

uint64_t LoopifyComparators::minimum_by(
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
  uint64_t _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l});
  /// Loopified minimum_by: _Enter -> _Cont_Cons.
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
        auto &&_sv = *a1;
        if (std::holds_alternative<typename List<uint64_t>::Nil>(_sv.v())) {
          _result = std::move(a0);
        } else {
          _stack.emplace_back(_Cont_Cons{a0});
          _stack.emplace_back(_Enter{a1.get()});
        }
      }
    } else {
      auto _f = std::move(std::get<_Cont_Cons>(_frame));
      uint64_t a0 = _f.a0;
      uint64_t m = _result;
      if (a0 < m) {
        _result = std::move(a0);
      } else {
        _result = std::move(m);
      }
    }
  }
  return _result;
}

List<uint64_t> LoopifyComparators::merge_by_fuel(uint64_t fuel,
                                                 List<uint64_t> l1,
                                                 List<uint64_t> l2) {
  std::unique_ptr<List<uint64_t>> _head{};
  std::unique_ptr<List<uint64_t>> *_write = &_head;
  List<uint64_t> _loop_l2 = std::move(l2);
  List<uint64_t> _loop_l1 = std::move(l1);
  uint64_t _loop_fuel = std::move(fuel);
  while (true) {
    if (_loop_fuel <= 0) {
      *_write = std::make_unique<List<uint64_t>>(List<uint64_t>::nil());
      break;
    } else {
      uint64_t fuel_ = _loop_fuel - 1;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(
              _loop_l1.v_mut())) {
        *_write = std::make_unique<List<uint64_t>>(std::move(_loop_l2));
        break;
      } else {
        auto &[a0, a1] =
            std::get<typename List<uint64_t>::Cons>(_loop_l1.v_mut());
        if (std::holds_alternative<typename List<uint64_t>::Nil>(
                _loop_l2.v_mut())) {
          *_write = std::make_unique<List<uint64_t>>(_loop_l1);
          break;
        } else {
          auto &[a00, a10] =
              std::get<typename List<uint64_t>::Cons>(_loop_l2.v_mut());
          if (a0 <= a00) {
            auto _cell = std::make_unique<List<uint64_t>>(
                typename List<uint64_t>::Cons(std::move(a0), nullptr));
            *_write = std::move(_cell);
            _write =
                &std::get<typename List<uint64_t>::Cons>((*_write)->v_mut()).l;
            _loop_l1 = std::move(*a1);
            _loop_fuel = fuel_;
            continue;
          } else {
            auto _cell = std::make_unique<List<uint64_t>>(
                typename List<uint64_t>::Cons(std::move(a00), nullptr));
            *_write = std::move(_cell);
            _write =
                &std::get<typename List<uint64_t>::Cons>((*_write)->v_mut()).l;
            _loop_l2 = std::move(*a10);
            _loop_fuel = fuel_;
            continue;
          }
        }
      }
    }
  }
  return std::move(*_head);
}

List<uint64_t> LoopifyComparators::merge_by(const List<uint64_t> &l1,
                                            const List<uint64_t> &l2) {
  uint64_t len1 = l1.length();
  uint64_t len2 = l2.length();
  return merge_by_fuel((len1 + len2), l1, l2);
}

List<uint64_t> LoopifyComparators::insert_sorted(uint64_t x, List<uint64_t> l) {
  std::unique_ptr<List<uint64_t>> _head{};
  std::unique_ptr<List<uint64_t>> *_write = &_head;
  List<uint64_t> _loop_l = std::move(l);
  while (true) {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l.v_mut())) {
      *_write = std::make_unique<List<uint64_t>>(
          List<uint64_t>::cons(x, List<uint64_t>::nil()));
      break;
    } else {
      auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(_loop_l.v_mut());
      if (x <= a0) {
        *_write =
            std::make_unique<List<uint64_t>>(List<uint64_t>::cons(x, _loop_l));
        break;
      } else {
        auto _cell = std::make_unique<List<uint64_t>>(
            typename List<uint64_t>::Cons(std::move(a0), nullptr));
        *_write = std::move(_cell);
        _write = &std::get<typename List<uint64_t>::Cons>((*_write)->v_mut()).l;
        _loop_l = std::move(*a1);
        continue;
      }
    }
  }
  return std::move(*_head);
}

List<uint64_t> LoopifyComparators::insertion_sort(
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
  std::vector<_Frame> _stack;
  _stack.reserve(8);
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
        _stack.emplace_back(_Enter{a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Resume_Cons>(_frame));
      _result = insert_sorted(_f.a0, _result);
    }
  }
  return _result;
}

bool LoopifyComparators::is_sorted_fuel(uint64_t fuel,
                                        const List<uint64_t> &l) {
  List<uint64_t> _loop_l = l;
  uint64_t _loop_fuel = std::move(fuel);
  while (true) {
    if (_loop_fuel <= 0) {
      return true;
    } else {
      uint64_t fuel_ = _loop_fuel - 1;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l.v())) {
        return true;
      } else {
        const auto &[a0, a1] =
            std::get<typename List<uint64_t>::Cons>(_loop_l.v());
        auto &&_sv0 = *a1;
        if (std::holds_alternative<typename List<uint64_t>::Nil>(_sv0.v())) {
          return true;
        } else {
          const auto &[a00, a10] =
              std::get<typename List<uint64_t>::Cons>(_sv0.v());
          if (a0 <= a00) {
            _loop_l = List<uint64_t>::cons(a00, *a10);
            _loop_fuel = fuel_;
          } else {
            return false;
          }
        }
      }
    }
  }
}

bool LoopifyComparators::is_sorted(const List<uint64_t> &l) {
  uint64_t len = l.length();
  return is_sorted_fuel(len, l);
}
