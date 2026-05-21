#include "loopify_list_pairing.h"

std::pair<List<uint64_t>, List<uint64_t>> LoopifyListPairing::unzip(
    const List<std::pair<uint64_t, uint64_t>>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<std::pair<uint64_t, uint64_t>> *l;
  };

  /// _Cont_a: saves [a, b], resumes after recursive call, then processes rest.
  struct _Cont_a {
    uint64_t a;
    uint64_t b;
  };

  using _Frame = std::variant<_Enter, _Cont_a>;
  std::pair<List<uint64_t>, List<uint64_t>> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l});
  /// Loopified unzip: _Enter -> _Cont_a.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<std::pair<uint64_t, uint64_t>> &l = *_f.l;
      if (std::holds_alternative<
              typename List<std::pair<uint64_t, uint64_t>>::Nil>(l.v())) {
        _result = std::make_pair(List<uint64_t>::nil(), List<uint64_t>::nil());
      } else {
        const auto &[a0, a1] =
            std::get<typename List<std::pair<uint64_t, uint64_t>>::Cons>(l.v());
        const uint64_t &a = a0.first;
        const uint64_t &b = a0.second;
        _stack.emplace_back(_Cont_a{a, b});
        _stack.emplace_back(_Enter{a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Cont_a>(_frame));
      uint64_t a = _f.a;
      uint64_t b = _f.b;
      const List<uint64_t> &xs = _result.first;
      const List<uint64_t> &ys = _result.second;
      _result = std::make_pair(List<uint64_t>::cons(a, xs),
                               List<uint64_t>::cons(b, ys));
    }
  }
  return _result;
}

std::pair<List<uint64_t>, List<uint64_t>> LoopifyListPairing::swizzle(
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
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l});
  /// Loopified swizzle: _Enter -> _Cont_Cons.
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
        _stack.emplace_back(_Enter{a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Cont_Cons>(_frame));
      uint64_t a0 = _f.a0;
      const List<uint64_t> &odds = _result.first;
      const List<uint64_t> &evens = _result.second;
      _result = std::make_pair(List<uint64_t>::cons(a0, evens), odds);
    }
  }
  return _result;
}

std::pair<List<uint64_t>, List<uint64_t>> LoopifyListPairing::partition(
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
  std::vector<_Frame> _stack;
  _stack.reserve(8);
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
        _stack.emplace_back(_Enter{a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Cont_Cons>(_frame));
      uint64_t a0 = _f.a0;
      const List<uint64_t> &yes = _result.first;
      const List<uint64_t> &no = _result.second;
      if ((UINT64_C(2) ? a0 % UINT64_C(2) : a0) == UINT64_C(0)) {
        _result = std::make_pair(List<uint64_t>::cons(a0, yes), no);
      } else {
        _result = std::make_pair(yes, List<uint64_t>::cons(a0, no));
      }
    }
  }
  return _result;
}

List<std::pair<uint64_t, uint64_t>>
LoopifyListPairing::zip_longest_fuel(uint64_t fuel, const List<uint64_t> &l1,
                                     const List<uint64_t> &l2,
                                     uint64_t default0) {
  std::shared_ptr<List<std::pair<uint64_t, uint64_t>>> _head{};
  std::shared_ptr<List<std::pair<uint64_t, uint64_t>>> *_write = &_head;
  List<uint64_t> _loop_l2 = l2;
  List<uint64_t> _loop_l1 = l1;
  uint64_t _loop_fuel = std::move(fuel);
  while (true) {
    if (_loop_fuel <= 0) {
      *_write = std::make_shared<List<std::pair<uint64_t, uint64_t>>>(
          List<std::pair<uint64_t, uint64_t>>::nil());
      break;
    } else {
      uint64_t fuel_ = _loop_fuel - 1;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l1.v())) {
        if (std::holds_alternative<typename List<uint64_t>::Nil>(
                _loop_l2.v())) {
          *_write = std::make_shared<List<std::pair<uint64_t, uint64_t>>>(
              List<std::pair<uint64_t, uint64_t>>::nil());
          break;
        } else {
          const auto &[a00, a10] =
              std::get<typename List<uint64_t>::Cons>(_loop_l2.v());
          auto _cell = std::make_shared<List<std::pair<uint64_t, uint64_t>>>(
              typename List<std::pair<uint64_t, uint64_t>>::Cons(
                  std::make_pair(default0, a00), nullptr));
          *_write = std::move(_cell);
          _write =
              &std::get<typename List<std::pair<uint64_t, uint64_t>>::Cons>(
                   (*_write)->v_mut())
                   .l;
          _loop_l2 = std::move(*a10);
          _loop_l1 = List<uint64_t>::nil();
          _loop_fuel = fuel_;
          continue;
        }
      } else {
        const auto &[a0, a1] =
            std::get<typename List<uint64_t>::Cons>(_loop_l1.v());
        if (std::holds_alternative<typename List<uint64_t>::Nil>(
                _loop_l2.v())) {
          auto _cell = std::make_shared<List<std::pair<uint64_t, uint64_t>>>(
              typename List<std::pair<uint64_t, uint64_t>>::Cons(
                  std::make_pair(a0, default0), nullptr));
          *_write = std::move(_cell);
          _write =
              &std::get<typename List<std::pair<uint64_t, uint64_t>>::Cons>(
                   (*_write)->v_mut())
                   .l;
          _loop_l2 = List<uint64_t>::nil();
          _loop_l1 = std::move(*a1);
          _loop_fuel = fuel_;
          continue;
        } else {
          const auto &[a00, a10] =
              std::get<typename List<uint64_t>::Cons>(_loop_l2.v());
          auto _cell = std::make_shared<List<std::pair<uint64_t, uint64_t>>>(
              typename List<std::pair<uint64_t, uint64_t>>::Cons(
                  std::make_pair(a0, a00), nullptr));
          *_write = std::move(_cell);
          _write =
              &std::get<typename List<std::pair<uint64_t, uint64_t>>::Cons>(
                   (*_write)->v_mut())
                   .l;
          _loop_l2 = std::move(*a10);
          _loop_l1 = std::move(*a1);
          _loop_fuel = fuel_;
          continue;
        }
      }
    }
  }
  return std::move(*_head);
}

List<std::pair<uint64_t, uint64_t>>
LoopifyListPairing::zip_longest(const List<uint64_t> &l1,
                                const List<uint64_t> &l2, uint64_t default0) {
  uint64_t len1 = l1.length();
  uint64_t len2 = l2.length();
  uint64_t maxlen;
  if (len1 < len2) {
    maxlen = len2;
  } else {
    maxlen = len1;
  }
  return zip_longest_fuel(maxlen, l1, l2, default0);
}

List<uint64_t> LoopifyListPairing::zipWith(const List<uint64_t> &l1,
                                           const List<uint64_t> &l2) {
  std::shared_ptr<List<uint64_t>> _head{};
  std::shared_ptr<List<uint64_t>> *_write = &_head;
  const List<uint64_t> *_loop_l2 = &l2;
  const List<uint64_t> *_loop_l1 = &l1;
  while (true) {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l1->v())) {
      *_write = std::make_shared<List<uint64_t>>(List<uint64_t>::nil());
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename List<uint64_t>::Cons>(_loop_l1->v());
      if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l2->v())) {
        *_write = std::make_shared<List<uint64_t>>(List<uint64_t>::nil());
        break;
      } else {
        const auto &[a00, a10] =
            std::get<typename List<uint64_t>::Cons>(_loop_l2->v());
        auto _cell = std::make_shared<List<uint64_t>>(
            typename List<uint64_t>::Cons((a0 + a00), nullptr));
        *_write = std::move(_cell);
        _write = &std::get<typename List<uint64_t>::Cons>((*_write)->v_mut()).l;
        _loop_l2 = a10.get();
        _loop_l1 = a1.get();
        continue;
      }
    }
  }
  return std::move(*_head);
}

std::pair<List<uint64_t>, List<uint64_t>> LoopifyListPairing::split_even_odd(
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
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l});
  /// Loopified split_even_odd: _Enter -> _Cont_Cons.
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
        _stack.emplace_back(_Enter{a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Cont_Cons>(_frame));
      uint64_t a0 = _f.a0;
      const List<uint64_t> &evens = _result.first;
      const List<uint64_t> &odds = _result.second;
      if ((UINT64_C(2) ? a0 % UINT64_C(2) : a0) == UINT64_C(0)) {
        _result = std::make_pair(List<uint64_t>::cons(a0, evens), odds);
      } else {
        _result = std::make_pair(evens, List<uint64_t>::cons(a0, odds));
      }
    }
  }
  return _result;
}
