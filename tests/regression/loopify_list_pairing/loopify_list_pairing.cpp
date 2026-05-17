#include "loopify_list_pairing.h"

std::pair<List<unsigned int>, List<unsigned int>> LoopifyListPairing::unzip(
    const List<std::pair<unsigned int, unsigned int>>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<std::pair<unsigned int, unsigned int>> *l;
  };

  /// _Cont_a: saves [a, b], resumes after recursive call, then processes rest.
  struct _Cont_a {
    unsigned int a;
    unsigned int b;
  };

  using _Frame = std::variant<_Enter, _Cont_a>;
  std::pair<List<unsigned int>, List<unsigned int>> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l});
  /// Loopified unzip: _Enter -> _Cont_a.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<std::pair<unsigned int, unsigned int>> &l = *_f.l;
      if (std::holds_alternative<
              typename List<std::pair<unsigned int, unsigned int>>::Nil>(
              l.v())) {
        _result = std::make_pair(List<unsigned int>::nil(),
                                 List<unsigned int>::nil());
      } else {
        const auto &[d_a0, d_a1] = std::get<
            typename List<std::pair<unsigned int, unsigned int>>::Cons>(l.v());
        const unsigned int &a = d_a0.first;
        const unsigned int &b = d_a0.second;
        _stack.emplace_back(_Cont_a{a, b});
        _stack.emplace_back(_Enter{d_a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Cont_a>(_frame));
      unsigned int a = _f.a;
      unsigned int b = _f.b;
      const List<unsigned int> &xs = _result.first;
      const List<unsigned int> &ys = _result.second;
      _result = std::make_pair(List<unsigned int>::cons(a, xs),
                               List<unsigned int>::cons(b, ys));
    }
  }
  return _result;
}

std::pair<List<unsigned int>, List<unsigned int>> LoopifyListPairing::swizzle(
    const List<unsigned int>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<unsigned int> *l;
  };

  /// _Cont_Cons: saves [d_a0], resumes after recursive call, then processes
  /// rest.
  struct _Cont_Cons {
    unsigned int d_a0;
  };

  using _Frame = std::variant<_Enter, _Cont_Cons>;
  std::pair<List<unsigned int>, List<unsigned int>> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l});
  /// Loopified swizzle: _Enter -> _Cont_Cons.
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
        const auto &[d_a0, d_a1] =
            std::get<typename List<unsigned int>::Cons>(l.v());
        _stack.emplace_back(_Cont_Cons{d_a0});
        _stack.emplace_back(_Enter{d_a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Cont_Cons>(_frame));
      unsigned int d_a0 = _f.d_a0;
      const List<unsigned int> &odds = _result.first;
      const List<unsigned int> &evens = _result.second;
      _result = std::make_pair(List<unsigned int>::cons(d_a0, evens), odds);
    }
  }
  return _result;
}

std::pair<List<unsigned int>, List<unsigned int>> LoopifyListPairing::partition(
    const List<unsigned int>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<unsigned int> *l;
  };

  /// _Cont_Cons: saves [d_a0], resumes after recursive call, then processes
  /// rest.
  struct _Cont_Cons {
    unsigned int d_a0;
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
        const auto &[d_a0, d_a1] =
            std::get<typename List<unsigned int>::Cons>(l.v());
        _stack.emplace_back(_Cont_Cons{d_a0});
        _stack.emplace_back(_Enter{d_a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Cont_Cons>(_frame));
      unsigned int d_a0 = _f.d_a0;
      const List<unsigned int> &yes = _result.first;
      const List<unsigned int> &no = _result.second;
      if ((2u ? d_a0 % 2u : d_a0) == 0u) {
        _result = std::make_pair(List<unsigned int>::cons(d_a0, yes), no);
      } else {
        _result = std::make_pair(yes, List<unsigned int>::cons(d_a0, no));
      }
    }
  }
  return _result;
}

List<std::pair<unsigned int, unsigned int>>
LoopifyListPairing::zip_longest_fuel(unsigned int fuel,
                                     const List<unsigned int> &l1,
                                     const List<unsigned int> &l2,
                                     unsigned int default0) {
  std::unique_ptr<List<std::pair<unsigned int, unsigned int>>> _head{};
  std::unique_ptr<List<std::pair<unsigned int, unsigned int>>> *_write = &_head;
  List<unsigned int> _loop_l2 = l2;
  List<unsigned int> _loop_l1 = l1;
  unsigned int _loop_fuel = std::move(fuel);
  while (true) {
    if (_loop_fuel <= 0) {
      *_write = std::make_unique<List<std::pair<unsigned int, unsigned int>>>(
          List<std::pair<unsigned int, unsigned int>>::nil());
      break;
    } else {
      unsigned int fuel_ = _loop_fuel - 1;
      if (std::holds_alternative<typename List<unsigned int>::Nil>(
              _loop_l1.v())) {
        if (std::holds_alternative<typename List<unsigned int>::Nil>(
                _loop_l2.v())) {
          *_write =
              std::make_unique<List<std::pair<unsigned int, unsigned int>>>(
                  List<std::pair<unsigned int, unsigned int>>::nil());
          break;
        } else {
          const auto &[d_a00, d_a10] =
              std::get<typename List<unsigned int>::Cons>(_loop_l2.v());
          auto _cell =
              std::make_unique<List<std::pair<unsigned int, unsigned int>>>(
                  typename List<std::pair<unsigned int, unsigned int>>::Cons(
                      std::make_pair(default0, d_a00), nullptr));
          *_write = std::move(_cell);
          _write =
              &std::get<
                   typename List<std::pair<unsigned int, unsigned int>>::Cons>(
                   (*_write)->v_mut())
                   .d_a1;
          _loop_l2 = std::move(*d_a10);
          _loop_l1 = List<unsigned int>::nil();
          _loop_fuel = fuel_;
          continue;
        }
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<unsigned int>::Cons>(_loop_l1.v());
        if (std::holds_alternative<typename List<unsigned int>::Nil>(
                _loop_l2.v())) {
          auto _cell =
              std::make_unique<List<std::pair<unsigned int, unsigned int>>>(
                  typename List<std::pair<unsigned int, unsigned int>>::Cons(
                      std::make_pair(d_a0, default0), nullptr));
          *_write = std::move(_cell);
          _write =
              &std::get<
                   typename List<std::pair<unsigned int, unsigned int>>::Cons>(
                   (*_write)->v_mut())
                   .d_a1;
          _loop_l2 = List<unsigned int>::nil();
          _loop_l1 = std::move(*d_a1);
          _loop_fuel = fuel_;
          continue;
        } else {
          const auto &[d_a00, d_a10] =
              std::get<typename List<unsigned int>::Cons>(_loop_l2.v());
          auto _cell =
              std::make_unique<List<std::pair<unsigned int, unsigned int>>>(
                  typename List<std::pair<unsigned int, unsigned int>>::Cons(
                      std::make_pair(d_a0, d_a00), nullptr));
          *_write = std::move(_cell);
          _write =
              &std::get<
                   typename List<std::pair<unsigned int, unsigned int>>::Cons>(
                   (*_write)->v_mut())
                   .d_a1;
          _loop_l2 = std::move(*d_a10);
          _loop_l1 = std::move(*d_a1);
          _loop_fuel = fuel_;
          continue;
        }
      }
    }
  }
  return std::move(*_head);
}

List<std::pair<unsigned int, unsigned int>>
LoopifyListPairing::zip_longest(const List<unsigned int> &l1,
                                const List<unsigned int> &l2,
                                unsigned int default0) {
  unsigned int len1 = l1.length();
  unsigned int len2 = l2.length();
  unsigned int maxlen;
  if (len1 < len2) {
    maxlen = len2;
  } else {
    maxlen = len1;
  }
  return zip_longest_fuel(maxlen, l1, l2, default0);
}

List<unsigned int> LoopifyListPairing::zipWith(const List<unsigned int> &l1,
                                               const List<unsigned int> &l2) {
  std::unique_ptr<List<unsigned int>> _head{};
  std::unique_ptr<List<unsigned int>> *_write = &_head;
  const List<unsigned int> *_loop_l2 = &l2;
  const List<unsigned int> *_loop_l1 = &l1;
  while (true) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(
            _loop_l1->v())) {
      *_write = std::make_unique<List<unsigned int>>(List<unsigned int>::nil());
      break;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<unsigned int>::Cons>(_loop_l1->v());
      if (std::holds_alternative<typename List<unsigned int>::Nil>(
              _loop_l2->v())) {
        *_write =
            std::make_unique<List<unsigned int>>(List<unsigned int>::nil());
        break;
      } else {
        const auto &[d_a00, d_a10] =
            std::get<typename List<unsigned int>::Cons>(_loop_l2->v());
        auto _cell = std::make_unique<List<unsigned int>>(
            typename List<unsigned int>::Cons((d_a0 + d_a00), nullptr));
        *_write = std::move(_cell);
        _write =
            &std::get<typename List<unsigned int>::Cons>((*_write)->v_mut())
                 .d_a1;
        _loop_l2 = d_a10.get();
        _loop_l1 = d_a1.get();
        continue;
      }
    }
  }
  return std::move(*_head);
}

std::pair<List<unsigned int>, List<unsigned int>>
LoopifyListPairing::split_even_odd(
    const List<unsigned int>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<unsigned int> *l;
  };

  /// _Cont_Cons: saves [d_a0], resumes after recursive call, then processes
  /// rest.
  struct _Cont_Cons {
    unsigned int d_a0;
  };

  using _Frame = std::variant<_Enter, _Cont_Cons>;
  std::pair<List<unsigned int>, List<unsigned int>> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l});
  /// Loopified split_even_odd: _Enter -> _Cont_Cons.
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
        const auto &[d_a0, d_a1] =
            std::get<typename List<unsigned int>::Cons>(l.v());
        _stack.emplace_back(_Cont_Cons{d_a0});
        _stack.emplace_back(_Enter{d_a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Cont_Cons>(_frame));
      unsigned int d_a0 = _f.d_a0;
      const List<unsigned int> &evens = _result.first;
      const List<unsigned int> &odds = _result.second;
      if ((2u ? d_a0 % 2u : d_a0) == 0u) {
        _result = std::make_pair(List<unsigned int>::cons(d_a0, evens), odds);
      } else {
        _result = std::make_pair(evens, List<unsigned int>::cons(d_a0, odds));
      }
    }
  }
  return _result;
}
