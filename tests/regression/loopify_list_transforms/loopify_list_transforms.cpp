#include "loopify_list_transforms.h"

List<std::pair<uint64_t, uint64_t>>
LoopifyListTransforms::run_length_encode(const List<uint64_t> &l) {
  if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
    return List<std::pair<uint64_t, uint64_t>>::nil();
  } else {
    const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
    auto &&_sv = *a1;
    if (std::holds_alternative<typename List<uint64_t>::Nil>(_sv.v())) {
      return List<std::pair<uint64_t, uint64_t>>::cons(
          std::make_pair(a0, UINT64_C(1)),
          List<std::pair<uint64_t, uint64_t>>::nil());
    } else {
      auto &&_sv1 = run_length_encode(*a1);
      if (std::holds_alternative<
              typename List<std::pair<uint64_t, uint64_t>>::Nil>(_sv1.v())) {
        return List<std::pair<uint64_t, uint64_t>>::cons(
            std::make_pair(a0, UINT64_C(1)),
            List<std::pair<uint64_t, uint64_t>>::nil());
      } else {
        const auto &[a01, a11] =
            std::get<typename List<std::pair<uint64_t, uint64_t>>::Cons>(
                _sv1.v());
        const uint64_t &y = a01.first;
        const uint64_t &n = a01.second;
        if (a0 == y) {
          return List<std::pair<uint64_t, uint64_t>>::cons(
              std::make_pair(y, (n + UINT64_C(1))), *a11);
        } else {
          return List<std::pair<uint64_t, uint64_t>>::cons(
              std::make_pair(a0, UINT64_C(1)),
              List<std::pair<uint64_t, uint64_t>>::cons(std::make_pair(y, n),
                                                        *a11));
        }
      }
    }
  }
}

List<uint64_t> LoopifyListTransforms::prefix_sums(uint64_t acc,
                                                  const List<uint64_t> &l) {
  std::unique_ptr<List<uint64_t>> _head{};
  std::unique_ptr<List<uint64_t>> *_write = &_head;
  const List<uint64_t> *_loop_l = &l;
  uint64_t _loop_acc = std::move(acc);
  while (true) {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l->v())) {
      *_write = std::make_unique<List<uint64_t>>(
          List<uint64_t>::cons(_loop_acc, List<uint64_t>::nil()));
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename List<uint64_t>::Cons>(_loop_l->v());
      auto _cell = std::make_unique<List<uint64_t>>(
          typename List<uint64_t>::Cons(_loop_acc, nullptr));
      *_write = std::move(_cell);
      _write = &std::get<typename List<uint64_t>::Cons>((*_write)->v_mut()).a1;
      _loop_l = a1.get();
      _loop_acc = (_loop_acc + a0);
      continue;
    }
  }
  return std::move(*_head);
}

List<std::pair<uint64_t, uint64_t>>
LoopifyListTransforms::sliding_pairs_fuel(uint64_t fuel,
                                          const List<uint64_t> &l) {
  std::unique_ptr<List<std::pair<uint64_t, uint64_t>>> _head{};
  std::unique_ptr<List<std::pair<uint64_t, uint64_t>>> *_write = &_head;
  const List<uint64_t> *_loop_l = &l;
  uint64_t _loop_fuel = std::move(fuel);
  while (true) {
    if (_loop_fuel <= 0) {
      *_write = std::make_unique<List<std::pair<uint64_t, uint64_t>>>(
          List<std::pair<uint64_t, uint64_t>>::nil());
      break;
    } else {
      uint64_t fuel_ = _loop_fuel - 1;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l->v())) {
        *_write = std::make_unique<List<std::pair<uint64_t, uint64_t>>>(
            List<std::pair<uint64_t, uint64_t>>::nil());
        break;
      } else {
        const auto &[a0, a1] =
            std::get<typename List<uint64_t>::Cons>(_loop_l->v());
        auto &&_sv0 = *a1;
        if (std::holds_alternative<typename List<uint64_t>::Nil>(_sv0.v())) {
          *_write = std::make_unique<List<std::pair<uint64_t, uint64_t>>>(
              List<std::pair<uint64_t, uint64_t>>::nil());
          break;
        } else {
          const auto &[a00, a10] =
              std::get<typename List<uint64_t>::Cons>(_sv0.v());
          auto _cell = std::make_unique<List<std::pair<uint64_t, uint64_t>>>(
              typename List<std::pair<uint64_t, uint64_t>>::Cons(
                  std::make_pair(a0, a00), nullptr));
          *_write = std::move(_cell);
          _write =
              &std::get<typename List<std::pair<uint64_t, uint64_t>>::Cons>(
                   (*_write)->v_mut())
                   .a1;
          _loop_l = a1.get();
          _loop_fuel = fuel_;
          continue;
        }
      }
    }
  }
  return std::move(*_head);
}

List<std::pair<uint64_t, uint64_t>>
LoopifyListTransforms::sliding_pairs(const List<uint64_t> &l) {
  uint64_t len = l.length();
  return sliding_pairs_fuel(len, l);
}

uint64_t LoopifyListTransforms::abs_diff(uint64_t x, uint64_t y) {
  if (y < x) {
    return (((x - y) > x ? 0 : (x - y)));
  } else {
    return (((y - x) > y ? 0 : (y - x)));
  }
}

List<uint64_t>
LoopifyListTransforms::differences_fuel(uint64_t fuel,
                                        const List<uint64_t> &l) {
  std::unique_ptr<List<uint64_t>> _head{};
  std::unique_ptr<List<uint64_t>> *_write = &_head;
  const List<uint64_t> *_loop_l = &l;
  uint64_t _loop_fuel = std::move(fuel);
  while (true) {
    if (_loop_fuel <= 0) {
      *_write = std::make_unique<List<uint64_t>>(List<uint64_t>::nil());
      break;
    } else {
      uint64_t fuel_ = _loop_fuel - 1;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l->v())) {
        *_write = std::make_unique<List<uint64_t>>(List<uint64_t>::nil());
        break;
      } else {
        const auto &[a0, a1] =
            std::get<typename List<uint64_t>::Cons>(_loop_l->v());
        auto &&_sv0 = *a1;
        if (std::holds_alternative<typename List<uint64_t>::Nil>(_sv0.v())) {
          *_write = std::make_unique<List<uint64_t>>(List<uint64_t>::nil());
          break;
        } else {
          const auto &[a00, a10] =
              std::get<typename List<uint64_t>::Cons>(_sv0.v());
          auto _cell = std::make_unique<List<uint64_t>>(
              typename List<uint64_t>::Cons(abs_diff(a0, a00), nullptr));
          *_write = std::move(_cell);
          _write =
              &std::get<typename List<uint64_t>::Cons>((*_write)->v_mut()).a1;
          _loop_l = a1.get();
          _loop_fuel = fuel_;
          continue;
        }
      }
    }
  }
  return std::move(*_head);
}

List<uint64_t> LoopifyListTransforms::differences(const List<uint64_t> &l) {
  uint64_t len = l.length();
  return differences_fuel(len, l);
}

List<uint64_t> LoopifyListTransforms::take(uint64_t n,
                                           const List<uint64_t> &l) {
  std::unique_ptr<List<uint64_t>> _head{};
  std::unique_ptr<List<uint64_t>> *_write = &_head;
  const List<uint64_t> *_loop_l = &l;
  uint64_t _loop_n = std::move(n);
  while (true) {
    if (_loop_n <= 0) {
      *_write = std::make_unique<List<uint64_t>>(List<uint64_t>::nil());
      break;
    } else {
      uint64_t n_ = _loop_n - 1;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l->v())) {
        *_write = std::make_unique<List<uint64_t>>(List<uint64_t>::nil());
        break;
      } else {
        const auto &[a0, a1] =
            std::get<typename List<uint64_t>::Cons>(_loop_l->v());
        auto _cell = std::make_unique<List<uint64_t>>(
            typename List<uint64_t>::Cons(a0, nullptr));
        *_write = std::move(_cell);
        _write =
            &std::get<typename List<uint64_t>::Cons>((*_write)->v_mut()).a1;
        _loop_l = a1.get();
        _loop_n = n_;
        continue;
      }
    }
  }
  return std::move(*_head);
}

List<uint64_t> LoopifyListTransforms::drop(uint64_t n, List<uint64_t> l) {
  List<uint64_t> _result;
  List<uint64_t> _loop_l = std::move(l);
  uint64_t _loop_n = std::move(n);
  while (true) {
    if (_loop_n <= 0) {
      _result = std::move(_loop_l);
      break;
    } else {
      uint64_t n_ = _loop_n - 1;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(
              _loop_l.v_mut())) {
        _result = List<uint64_t>::nil();
        break;
      } else {
        auto &[a0, a1] =
            std::get<typename List<uint64_t>::Cons>(_loop_l.v_mut());
        _loop_l = std::move(*a1);
        _loop_n = n_;
      }
    }
  }
  return _result;
}

List<List<uint64_t>>
LoopifyListTransforms::chunks_of_fuel(uint64_t fuel, uint64_t n,
                                      const List<uint64_t> &l) {
  std::unique_ptr<List<List<uint64_t>>> _head{};
  std::unique_ptr<List<List<uint64_t>>> *_write = &_head;
  List<uint64_t> _loop_l = l;
  uint64_t _loop_fuel = std::move(fuel);
  while (true) {
    if (_loop_fuel <= 0) {
      *_write =
          std::make_unique<List<List<uint64_t>>>(List<List<uint64_t>>::nil());
      break;
    } else {
      uint64_t fuel_ = _loop_fuel - 1;
      if (n <= UINT64_C(0)) {
        *_write =
            std::make_unique<List<List<uint64_t>>>(List<List<uint64_t>>::nil());
        break;
      } else {
        if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l.v())) {
          *_write = std::make_unique<List<List<uint64_t>>>(
              List<List<uint64_t>>::nil());
          break;
        } else {
          auto _cell = std::make_unique<List<List<uint64_t>>>(
              typename List<List<uint64_t>>::Cons(take(n, _loop_l), nullptr));
          *_write = std::move(_cell);
          _write =
              &std::get<typename List<List<uint64_t>>::Cons>((*_write)->v_mut())
                   .a1;
          _loop_l = drop(n, _loop_l);
          _loop_fuel = fuel_;
          continue;
        }
      }
    }
  }
  return std::move(*_head);
}

List<List<uint64_t>> LoopifyListTransforms::chunks_of(uint64_t n,
                                                      const List<uint64_t> &l) {
  uint64_t len = l.length();
  return chunks_of_fuel(len, n, l);
}

List<uint64_t> LoopifyListTransforms::rotate_left_fuel(uint64_t fuel,
                                                       uint64_t n,
                                                       List<uint64_t> l) {
  List<uint64_t> _result;
  List<uint64_t> _loop_l = std::move(l);
  uint64_t _loop_n = std::move(n);
  uint64_t _loop_fuel = std::move(fuel);
  while (true) {
    if (_loop_fuel <= 0) {
      _result = std::move(_loop_l);
      break;
    } else {
      uint64_t fuel_ = _loop_fuel - 1;
      if (_loop_n <= UINT64_C(0)) {
        _result = std::move(_loop_l);
        break;
      } else {
        if (std::holds_alternative<typename List<uint64_t>::Nil>(
                _loop_l.v_mut())) {
          _result = List<uint64_t>::nil();
          break;
        } else {
          auto &[a0, a1] =
              std::get<typename List<uint64_t>::Cons>(_loop_l.v_mut());
          List<uint64_t> rotated = (*a1).app(
              List<uint64_t>::cons(std::move(a0), List<uint64_t>::nil()));
          _loop_l = std::move(rotated);
          _loop_n = ((
              (_loop_n - UINT64_C(1)) > _loop_n ? 0 : (_loop_n - UINT64_C(1))));
          _loop_fuel = fuel_;
        }
      }
    }
  }
  return _result;
}

List<uint64_t> LoopifyListTransforms::rotate_left(uint64_t n,
                                                  const List<uint64_t> &l) {
  return rotate_left_fuel((n + UINT64_C(1)), n, l);
}

List<uint64_t>
LoopifyListTransforms::uniq_sorted_fuel(uint64_t fuel,
                                        const List<uint64_t> &l) {
  std::unique_ptr<List<uint64_t>> _head{};
  std::unique_ptr<List<uint64_t>> *_write = &_head;
  const List<uint64_t> *_loop_l = &l;
  uint64_t _loop_fuel = std::move(fuel);
  while (true) {
    if (_loop_fuel <= 0) {
      *_write = std::make_unique<List<uint64_t>>(List<uint64_t>::nil());
      break;
    } else {
      uint64_t fuel_ = _loop_fuel - 1;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l->v())) {
        *_write = std::make_unique<List<uint64_t>>(List<uint64_t>::nil());
        break;
      } else {
        const auto &[a0, a1] =
            std::get<typename List<uint64_t>::Cons>(_loop_l->v());
        auto &&_sv0 = *a1;
        if (std::holds_alternative<typename List<uint64_t>::Nil>(_sv0.v())) {
          *_write = std::make_unique<List<uint64_t>>(
              List<uint64_t>::cons(a0, List<uint64_t>::nil()));
          break;
        } else {
          const auto &[a00, a10] =
              std::get<typename List<uint64_t>::Cons>(_sv0.v());
          if (a0 == a00) {
            _loop_l = a1.get();
            _loop_fuel = fuel_;
            continue;
          } else {
            auto _cell = std::make_unique<List<uint64_t>>(
                typename List<uint64_t>::Cons(a0, nullptr));
            *_write = std::move(_cell);
            _write =
                &std::get<typename List<uint64_t>::Cons>((*_write)->v_mut()).a1;
            _loop_l = a1.get();
            _loop_fuel = fuel_;
            continue;
          }
        }
      }
    }
  }
  return std::move(*_head);
}

List<uint64_t> LoopifyListTransforms::uniq_sorted(const List<uint64_t> &l) {
  uint64_t len = l.length();
  return uniq_sorted_fuel(len, l);
}

uint64_t LoopifyListTransforms::step_sum(
    const List<uint64_t>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<uint64_t> *l;
  };

  /// _Resume_Cons: saves [contribution], resumes after recursive call with
  /// _result.
  struct _Resume_Cons {
    uint64_t contribution;
  };

  using _Frame = std::variant<_Enter, _Resume_Cons>;
  uint64_t _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l});
  /// Loopified step_sum: _Enter -> _Resume_Cons.
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
        uint64_t contribution;
        if ((UINT64_C(2) ? a0 % UINT64_C(2) : a0) == UINT64_C(0)) {
          contribution = a0;
        } else {
          contribution = (a0 * UINT64_C(2));
        }
        _stack.emplace_back(_Resume_Cons{contribution});
        _stack.emplace_back(_Enter{a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Resume_Cons>(_frame));
      _result = (_f.contribution + _result);
    }
  }
  return _result;
}
