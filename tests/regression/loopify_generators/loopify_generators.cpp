#include "loopify_generators.h"

/// Consolidated list generator functions.
/// cycle n l repeats the list n times: cycle 2 1,2 -> 1,2,1,2.
List<uint64_t> LoopifyGenerators::cycle(
    uint64_t n,
    const List<uint64_t>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    uint64_t n;
  };

  /// _Resume_m: saves [l], resumes after recursive call with _result.
  struct _Resume_m {
    List<uint64_t> l;
  };

  using _Frame = std::variant<_Enter, _Resume_m>;
  List<uint64_t> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{n});
  /// Loopified cycle: _Enter -> _Resume_m.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      uint64_t n = _f.n;
      if (n <= 0) {
        _result = List<uint64_t>::nil();
      } else {
        uint64_t m = n - 1;
        _stack.emplace_back(_Resume_m{l});
        _stack.emplace_back(_Enter{m});
      }
    } else {
      auto _f = std::move(std::get<_Resume_m>(_frame));
      _result = _f.l.app(_result);
    }
  }
  return _result;
}

/// zip_longest l1 l2 default zips, using default for missing elements.
List<std::pair<uint64_t, uint64_t>>
LoopifyGenerators::zip_longest_aux(const List<uint64_t> &l1,
                                   const List<uint64_t> &l2, uint64_t default0,
                                   uint64_t fuel) {
  std::shared_ptr<List<std::pair<uint64_t, uint64_t>>> _head{};
  std::shared_ptr<List<std::pair<uint64_t, uint64_t>>> *_write = &_head;
  uint64_t _loop_fuel = std::move(fuel);
  List<uint64_t> _loop_l2 = l2;
  List<uint64_t> _loop_l1 = l1;
  while (true) {
    if (_loop_fuel <= 0) {
      *_write = std::make_shared<List<std::pair<uint64_t, uint64_t>>>(
          List<std::pair<uint64_t, uint64_t>>::nil());
      break;
    } else {
      uint64_t f = _loop_fuel - 1;
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
          _loop_fuel = f;
          _loop_l2 = std::move(*a10);
          _loop_l1 = List<uint64_t>::nil();
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
          _loop_fuel = f;
          _loop_l2 = List<uint64_t>::nil();
          _loop_l1 = std::move(*a1);
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
          _loop_fuel = f;
          _loop_l2 = std::move(*a10);
          _loop_l1 = std::move(*a1);
          continue;
        }
      }
    }
  }
  return std::move(*_head);
}

uint64_t LoopifyGenerators::len_impl(
    const List<uint64_t>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<uint64_t> *l;
  };

  /// _Resume_Cons: resumes after recursive call with _result.
  struct _Resume_Cons {};

  using _Frame = std::variant<_Enter, _Resume_Cons>;
  uint64_t _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l});
  /// Loopified len_impl: _Enter -> _Resume_Cons.
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
        _stack.emplace_back(_Resume_Cons{});
        _stack.emplace_back(_Enter{a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Resume_Cons>(_frame));
      _result = (_result + 1);
    }
  }
  return _result;
}

List<std::pair<uint64_t, uint64_t>>
LoopifyGenerators::zip_longest(const List<uint64_t> &l1,
                               const List<uint64_t> &l2, uint64_t default0) {
  return zip_longest_aux(l1, l2, default0, (len_impl(l1) + len_impl(l2)));
}

/// build_list n builds tree-like list structure: build_list(4) -> 2,4,2.
List<uint64_t> LoopifyGenerators::build_list_fuel(
    uint64_t fuel,
    uint64_t
        n) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    uint64_t n;
    uint64_t fuel;
  };

  /// _Cont__x: saves [n_], resumes after recursive call, then processes rest.
  struct _Cont__x {
    uint64_t n_;
  };

  using _Frame = std::variant<_Enter, _Cont__x>;
  List<uint64_t> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{n, fuel});
  /// Loopified build_list_fuel: _Enter -> _Cont__x.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      uint64_t n = _f.n;
      uint64_t fuel = _f.fuel;
      if (fuel <= 0) {
        _result = List<uint64_t>::nil();
      } else {
        uint64_t f = fuel - 1;
        if (n <= 0) {
          _result = List<uint64_t>::nil();
        } else {
          uint64_t n_ = n - 1;
          if (n_ <= 0) {
            _result = List<uint64_t>::cons(UINT64_C(1), List<uint64_t>::nil());
          } else {
            uint64_t _x = n_ - 1;
            uint64_t half = (UINT64_C(2) ? n_ / UINT64_C(2) : 0);
            _stack.emplace_back(_Cont__x{n_});
            _stack.emplace_back(_Enter{half, f});
          }
        }
      }
    } else {
      auto _f = std::move(std::get<_Cont__x>(_frame));
      uint64_t n_ = _f.n_;
      List<uint64_t> half_result = _result;
      _result = half_result.app(List<uint64_t>::cons(n_, half_result));
    }
  }
  return _result;
}

List<uint64_t> LoopifyGenerators::build_list(uint64_t n) {
  return build_list_fuel(UINT64_C(100), n);
}

/// take n l returns first n elements.
List<uint64_t> LoopifyGenerators::take(uint64_t n, const List<uint64_t> &l) {
  std::shared_ptr<List<uint64_t>> _head{};
  std::shared_ptr<List<uint64_t>> *_write = &_head;
  const List<uint64_t> *_loop_l = &l;
  uint64_t _loop_n = std::move(n);
  while (true) {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l->v())) {
      *_write = std::make_shared<List<uint64_t>>(List<uint64_t>::nil());
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename List<uint64_t>::Cons>(_loop_l->v());
      if (_loop_n == UINT64_C(0)) {
        *_write = std::make_shared<List<uint64_t>>(List<uint64_t>::nil());
        break;
      } else {
        auto _cell = std::make_shared<List<uint64_t>>(
            typename List<uint64_t>::Cons(a0, nullptr));
        *_write = std::move(_cell);
        _write = &std::get<typename List<uint64_t>::Cons>((*_write)->v_mut()).l;
        _loop_l = a1.get();
        _loop_n =
            (((_loop_n - UINT64_C(1)) > _loop_n ? 0 : (_loop_n - UINT64_C(1))));
        continue;
      }
    }
  }
  return std::move(*_head);
}

/// repeat x n creates list with n copies of x.
List<uint64_t> LoopifyGenerators::repeat(uint64_t x, uint64_t n) {
  std::shared_ptr<List<uint64_t>> _head{};
  std::shared_ptr<List<uint64_t>> *_write = &_head;
  uint64_t _loop_n = std::move(n);
  while (true) {
    if (_loop_n <= 0) {
      *_write = std::make_shared<List<uint64_t>>(List<uint64_t>::nil());
      break;
    } else {
      uint64_t m = _loop_n - 1;
      auto _cell = std::make_shared<List<uint64_t>>(
          typename List<uint64_t>::Cons(x, nullptr));
      *_write = std::move(_cell);
      _write = &std::get<typename List<uint64_t>::Cons>((*_write)->v_mut()).l;
      _loop_n = m;
      continue;
    }
  }
  return std::move(*_head);
}

/// Helper: replicate single element n times.
List<uint64_t> LoopifyGenerators::replicate_single(uint64_t x, uint64_t n) {
  std::shared_ptr<List<uint64_t>> _head{};
  std::shared_ptr<List<uint64_t>> *_write = &_head;
  uint64_t _loop_n = std::move(n);
  while (true) {
    if (_loop_n <= 0) {
      *_write = std::make_shared<List<uint64_t>>(List<uint64_t>::nil());
      break;
    } else {
      uint64_t m = _loop_n - 1;
      auto _cell = std::make_shared<List<uint64_t>>(
          typename List<uint64_t>::Cons(x, nullptr));
      *_write = std::move(_cell);
      _write = &std::get<typename List<uint64_t>::Cons>((*_write)->v_mut()).l;
      _loop_n = m;
      continue;
    }
  }
  return std::move(*_head);
}

/// replicate_each n l replicates each element n times: replicate_each 2 1,2 ->
/// 1,1,2,2.
List<uint64_t> LoopifyGenerators::replicate_each(
    uint64_t n,
    const List<uint64_t>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<uint64_t> *l;
  };

  /// _Resume_Cons: saves [_s0], resumes after recursive call with _result.
  struct _Resume_Cons {
    decltype(replicate_single(std::declval<uint64_t &>(),
                              std::declval<uint64_t &>())) _s0;
  };

  using _Frame = std::variant<_Enter, _Resume_Cons>;
  List<uint64_t> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l});
  /// Loopified replicate_each: _Enter -> _Resume_Cons.
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
        _stack.emplace_back(_Resume_Cons{replicate_single(a0, n)});
        _stack.emplace_back(_Enter{a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Resume_Cons>(_frame));
      _result = _f._s0.app(_result);
    }
  }
  return _result;
}
