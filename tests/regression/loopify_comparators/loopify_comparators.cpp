#include "loopify_comparators.h"

unsigned int LoopifyComparators::maximum_by(
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
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l});
  /// Loopified maximum_by: _Enter -> _Cont_Cons.
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
        auto &&_sv = *a1;
        if (std::holds_alternative<typename List<unsigned int>::Nil>(_sv.v())) {
          _result = std::move(a0);
        } else {
          _stack.emplace_back(_Cont_Cons{a0});
          _stack.emplace_back(_Enter{a1.get()});
        }
      }
    } else {
      auto _f = std::move(std::get<_Cont_Cons>(_frame));
      unsigned int a0 = _f.a0;
      unsigned int m = _result;
      if (m < a0) {
        _result = std::move(a0);
      } else {
        _result = std::move(m);
      }
    }
  }
  return _result;
}

unsigned int LoopifyComparators::minimum_by(
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
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l});
  /// Loopified minimum_by: _Enter -> _Cont_Cons.
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
        auto &&_sv = *a1;
        if (std::holds_alternative<typename List<unsigned int>::Nil>(_sv.v())) {
          _result = std::move(a0);
        } else {
          _stack.emplace_back(_Cont_Cons{a0});
          _stack.emplace_back(_Enter{a1.get()});
        }
      }
    } else {
      auto _f = std::move(std::get<_Cont_Cons>(_frame));
      unsigned int a0 = _f.a0;
      unsigned int m = _result;
      if (a0 < m) {
        _result = std::move(a0);
      } else {
        _result = std::move(m);
      }
    }
  }
  return _result;
}

List<unsigned int> LoopifyComparators::merge_by_fuel(unsigned int fuel,
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
      unsigned int fuel_ = _loop_fuel - 1;
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
            _loop_fuel = fuel_;
            continue;
          } else {
            auto _cell = std::make_unique<List<unsigned int>>(
                typename List<unsigned int>::Cons(std::move(a00), nullptr));
            *_write = std::move(_cell);
            _write =
                &std::get<typename List<unsigned int>::Cons>((*_write)->v_mut())
                     .a1;
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

List<unsigned int> LoopifyComparators::merge_by(const List<unsigned int> &l1,
                                                const List<unsigned int> &l2) {
  unsigned int len1 = l1.length();
  unsigned int len2 = l2.length();
  return merge_by_fuel((len1 + len2), l1, l2);
}

List<unsigned int> LoopifyComparators::insert_sorted(unsigned int x,
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

List<unsigned int> LoopifyComparators::insertion_sort(
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
      _result = insert_sorted(_f.a0, _result);
    }
  }
  return _result;
}

bool LoopifyComparators::is_sorted_fuel(unsigned int fuel,
                                        const List<unsigned int> &l) {
  bool _result;
  List<unsigned int> _loop_l = l;
  unsigned int _loop_fuel = std::move(fuel);
  while (true) {
    if (_loop_fuel <= 0) {
      _result = true;
      break;
    } else {
      unsigned int fuel_ = _loop_fuel - 1;
      if (std::holds_alternative<typename List<unsigned int>::Nil>(
              _loop_l.v())) {
        _result = true;
        break;
      } else {
        const auto &[a0, a1] =
            std::get<typename List<unsigned int>::Cons>(_loop_l.v());
        auto &&_sv0 = *a1;
        if (std::holds_alternative<typename List<unsigned int>::Nil>(
                _sv0.v())) {
          _result = true;
          break;
        } else {
          const auto &[a00, a10] =
              std::get<typename List<unsigned int>::Cons>(_sv0.v());
          if (a0 <= a00) {
            _loop_l = List<unsigned int>::cons(a00, *a10);
            _loop_fuel = fuel_;
          } else {
            _result = false;
            break;
          }
        }
      }
    }
  }
  return _result;
}

bool LoopifyComparators::is_sorted(const List<unsigned int> &l) {
  unsigned int len = l.length();
  return is_sorted_fuel(len, l);
}
