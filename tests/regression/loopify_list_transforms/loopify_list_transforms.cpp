#include "loopify_list_transforms.h"

List<std::pair<uint64_t, uint64_t>>
LoopifyListTransforms::run_length_encode(const List<uint64_t> &l) {
  // Explicit stack replaces the non-tail recursion of run_length_encode: _call
  // frames are pending calls, _after frames resume a caller.
  struct _call {
    const List<uint64_t> *l;
  };

  struct _after_run_length_encode_in_Cons {
    uint64_t a0;
  };

  using _frame = std::variant<_call, _after_run_length_encode_in_Cons>;
  List<std::pair<uint64_t, uint64_t>> _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&l});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const List<uint64_t> &l = *_f.l;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
        _result = List<std::pair<uint64_t, uint64_t>>::nil();
      } else {
        const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
        auto &&_sv = *a1;
        if (std::holds_alternative<typename List<uint64_t>::Nil>(_sv.v())) {
          _result = List<std::pair<uint64_t, uint64_t>>::cons(
              std::make_pair(a0, UINT64_C(1)),
              List<std::pair<uint64_t, uint64_t>>::nil());
        } else {
          _stack.emplace_back(_after_run_length_encode_in_Cons{a0});
          _stack.emplace_back(_call{crane_raw(a1)});
        }
      }
    } else {
      auto _f = std::move(std::get<_after_run_length_encode_in_Cons>(_popped));
      _stack.pop_back();
      uint64_t a0 = _f.a0;
      List<std::pair<uint64_t, uint64_t>> _tmp1 = std::move(_result);
      if (std::holds_alternative<
              typename List<std::pair<uint64_t, uint64_t>>::Nil>(_tmp1.v_mut())) {
        _result = List<std::pair<uint64_t, uint64_t>>::cons(
            std::make_pair(a0, UINT64_C(1)),
            List<std::pair<uint64_t, uint64_t>>::nil());
      } else {
        auto &[a01, a11] =
            std::get<typename List<std::pair<uint64_t, uint64_t>>::Cons>(
                _tmp1.v_mut());
        auto [y, n] = std::move(a01);
        if (a0 == y) {
          _result = List<std::pair<uint64_t, uint64_t>>::cons(
              std::make_pair(y, (n + UINT64_C(1))), crane::shared_child(a11));
        } else {
          _result = List<std::pair<uint64_t, uint64_t>>::cons(
              std::make_pair(a0, UINT64_C(1)),
              List<std::pair<uint64_t, uint64_t>>::cons(
                  std::make_pair(y, n), crane::shared_child(a11)));
        }
      }
    }
  }
  return _result;
}

List<uint64_t> LoopifyListTransforms::prefix_sums(uint64_t acc,
                                                  const List<uint64_t> &l) {
  // Builds the result front to back: _write points at the empty tail the next
  // cell fills.
  std::optional<List<uint64_t>> _root{};
  std::shared_ptr<List<uint64_t>> *_write = nullptr;
  const List<uint64_t> *_loop_l = &l;
  uint64_t _loop_acc = acc;
  while (true) {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l->v())) {
      auto _value = List<uint64_t>::cons(_loop_acc, List<uint64_t>::nil());
      (_write ? *(*_write = std::make_shared<List<uint64_t>>(std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename List<uint64_t>::Cons>(_loop_l->v());
      auto _cell = typename List<uint64_t>::Cons(_loop_acc, nullptr);
      List<uint64_t> &_node =
          (_write ? *(*_write =
                          std::make_shared<List<uint64_t>>(std::move(_cell)))
                  : _root.emplace(std::move(_cell)));
      _write = &std::get<typename List<uint64_t>::Cons>(_node.v_mut()).l;
      _loop_l = crane_raw(a1);
      _loop_acc = (_loop_acc + a0);
      continue;
    }
  }
  return std::move(*_root);
}

List<std::pair<uint64_t, uint64_t>>
LoopifyListTransforms::sliding_pairs_fuel(uint64_t fuel,
                                          const List<uint64_t> &l) {
  // Builds the result front to back: _write points at the empty tail the next
  // cell fills.
  std::optional<List<std::pair<uint64_t, uint64_t>>> _root{};
  std::shared_ptr<List<std::pair<uint64_t, uint64_t>>> *_write = nullptr;
  const List<uint64_t> *_loop_l = &l;
  uint64_t _loop_fuel = fuel;
  while (true) {
    if (_loop_fuel <= 0) {
      auto _value = List<std::pair<uint64_t, uint64_t>>::nil();
      (_write ? *(*_write =
                      std::make_shared<List<std::pair<uint64_t, uint64_t>>>(
                          std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      uint64_t fuel_ = _loop_fuel - 1;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l->v())) {
        auto _value = List<std::pair<uint64_t, uint64_t>>::nil();
        (_write ? *(*_write =
                        std::make_shared<List<std::pair<uint64_t, uint64_t>>>(
                            std::move(_value)))
                : _root.emplace(std::move(_value)));
        break;
      } else {
        const auto &[a0, a1] =
            std::get<typename List<uint64_t>::Cons>(_loop_l->v());
        auto &&_sv0 = *a1;
        if (std::holds_alternative<typename List<uint64_t>::Nil>(_sv0.v())) {
          auto _value = List<std::pair<uint64_t, uint64_t>>::nil();
          (_write ? *(*_write =
                          std::make_shared<List<std::pair<uint64_t, uint64_t>>>(
                              std::move(_value)))
                  : _root.emplace(std::move(_value)));
          break;
        } else {
          const auto &[a00, _] =
              std::get<typename List<uint64_t>::Cons>(_sv0.v());
          auto _cell = typename List<std::pair<uint64_t, uint64_t>>::Cons(
              std::make_pair(a0, a00), nullptr);
          List<std::pair<uint64_t, uint64_t>> &_node =
              (_write ? *(*_write = std::make_shared<
                              List<std::pair<uint64_t, uint64_t>>>(
                              std::move(_cell)))
                      : _root.emplace(std::move(_cell)));
          _write =
              &std::get<typename List<std::pair<uint64_t, uint64_t>>::Cons>(
                  _node.v_mut())
                  .l;
          _loop_l = crane_raw(a1);
          _loop_fuel = fuel_;
          continue;
        }
      }
    }
  }
  return std::move(*_root);
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
  // Builds the result front to back: _write points at the empty tail the next
  // cell fills.
  std::optional<List<uint64_t>> _root{};
  std::shared_ptr<List<uint64_t>> *_write = nullptr;
  const List<uint64_t> *_loop_l = &l;
  uint64_t _loop_fuel = fuel;
  while (true) {
    if (_loop_fuel <= 0) {
      auto _value = List<uint64_t>::nil();
      (_write ? *(*_write = std::make_shared<List<uint64_t>>(std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      uint64_t fuel_ = _loop_fuel - 1;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l->v())) {
        auto _value = List<uint64_t>::nil();
        (_write ? *(*_write =
                        std::make_shared<List<uint64_t>>(std::move(_value)))
                : _root.emplace(std::move(_value)));
        break;
      } else {
        const auto &[a0, a1] =
            std::get<typename List<uint64_t>::Cons>(_loop_l->v());
        auto &&_sv0 = *a1;
        if (std::holds_alternative<typename List<uint64_t>::Nil>(_sv0.v())) {
          auto _value = List<uint64_t>::nil();
          (_write ? *(*_write =
                          std::make_shared<List<uint64_t>>(std::move(_value)))
                  : _root.emplace(std::move(_value)));
          break;
        } else {
          const auto &[a00, _] =
              std::get<typename List<uint64_t>::Cons>(_sv0.v());
          auto _cell =
              typename List<uint64_t>::Cons(abs_diff(a0, a00), nullptr);
          List<uint64_t> &_node =
              (_write ? *(*_write = std::make_shared<List<uint64_t>>(
                              std::move(_cell)))
                      : _root.emplace(std::move(_cell)));
          _write = &std::get<typename List<uint64_t>::Cons>(_node.v_mut()).l;
          _loop_l = crane_raw(a1);
          _loop_fuel = fuel_;
          continue;
        }
      }
    }
  }
  return std::move(*_root);
}

List<uint64_t> LoopifyListTransforms::differences(const List<uint64_t> &l) {
  uint64_t len = l.length();
  return differences_fuel(len, l);
}

List<uint64_t> LoopifyListTransforms::take(uint64_t n,
                                           const List<uint64_t> &l) {
  // Builds the result front to back: _write points at the empty tail the next
  // cell fills.
  std::optional<List<uint64_t>> _root{};
  std::shared_ptr<List<uint64_t>> *_write = nullptr;
  const List<uint64_t> *_loop_l = &l;
  uint64_t _loop_n = n;
  while (true) {
    if (_loop_n <= 0) {
      auto _value = List<uint64_t>::nil();
      (_write ? *(*_write = std::make_shared<List<uint64_t>>(std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      uint64_t n_ = _loop_n - 1;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l->v())) {
        auto _value = List<uint64_t>::nil();
        (_write ? *(*_write =
                        std::make_shared<List<uint64_t>>(std::move(_value)))
                : _root.emplace(std::move(_value)));
        break;
      } else {
        const auto &[a0, a1] =
            std::get<typename List<uint64_t>::Cons>(_loop_l->v());
        auto _cell = typename List<uint64_t>::Cons(a0, nullptr);
        List<uint64_t> &_node =
            (_write ? *(*_write =
                            std::make_shared<List<uint64_t>>(std::move(_cell)))
                    : _root.emplace(std::move(_cell)));
        _write = &std::get<typename List<uint64_t>::Cons>(_node.v_mut()).l;
        _loop_l = crane_raw(a1);
        _loop_n = n_;
        continue;
      }
    }
  }
  return std::move(*_root);
}

List<uint64_t> LoopifyListTransforms::drop(uint64_t n,
                                           const List<uint64_t> &l) {
  // Loop replaces the tail recursion: each recursive call updates the loop
  // variables.
  const List<uint64_t> *_loop_l = &l;
  uint64_t _loop_n = n;
  while (true) {
    if (_loop_n <= 0) {
      return *_loop_l;
    } else {
      uint64_t n_ = _loop_n - 1;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l->v())) {
        return List<uint64_t>::nil();
      } else {
        const auto &[_, a1] =
            std::get<typename List<uint64_t>::Cons>(_loop_l->v());
        _loop_l = crane_raw(a1);
        _loop_n = n_;
      }
    }
  }
}

List<List<uint64_t>>
LoopifyListTransforms::chunks_of_fuel(uint64_t fuel, uint64_t n,
                                      const List<uint64_t> &l) {
  // Builds the result front to back: _write points at the empty tail the next
  // cell fills.
  std::optional<List<List<uint64_t>>> _root{};
  std::shared_ptr<List<List<uint64_t>>> *_write = nullptr;
  List<uint64_t> _loop_l = l;
  uint64_t _loop_fuel = fuel;
  while (true) {
    if (_loop_fuel <= 0) {
      auto _value = List<List<uint64_t>>::nil();
      (_write ? *(*_write =
                      std::make_shared<List<List<uint64_t>>>(std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      uint64_t fuel_ = _loop_fuel - 1;
      if (n <= UINT64_C(0)) {
        auto _value = List<List<uint64_t>>::nil();
        (_write ? *(*_write = std::make_shared<List<List<uint64_t>>>(
                        std::move(_value)))
                : _root.emplace(std::move(_value)));
        break;
      } else {
        if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l.v())) {
          auto _value = List<List<uint64_t>>::nil();
          (_write ? *(*_write = std::make_shared<List<List<uint64_t>>>(
                          std::move(_value)))
                  : _root.emplace(std::move(_value)));
          break;
        } else {
          auto _cell =
              typename List<List<uint64_t>>::Cons(take(n, _loop_l), nullptr);
          List<List<uint64_t>> &_node =
              (_write ? *(*_write = std::make_shared<List<List<uint64_t>>>(
                              std::move(_cell)))
                      : _root.emplace(std::move(_cell)));
          _write =
              &std::get<typename List<List<uint64_t>>::Cons>(_node.v_mut()).l;
          _loop_l = drop(n, _loop_l);
          _loop_fuel = fuel_;
          continue;
        }
      }
    }
  }
  return std::move(*_root);
}

List<List<uint64_t>> LoopifyListTransforms::chunks_of(uint64_t n,
                                                      const List<uint64_t> &l) {
  uint64_t len = l.length();
  return chunks_of_fuel(len, n, l);
}

List<uint64_t>
LoopifyListTransforms::rotate_left_fuel(uint64_t fuel, uint64_t n,
                                        const List<uint64_t> &l) {
  // Loop replaces the tail recursion: each recursive call updates the loop
  // variables.
  List<uint64_t> _loop_l = l;
  uint64_t _loop_n = n;
  uint64_t _loop_fuel = fuel;
  while (true) {
    if (_loop_fuel <= 0) {
      return _loop_l;
    } else {
      uint64_t fuel_ = _loop_fuel - 1;
      if (_loop_n <= UINT64_C(0)) {
        return _loop_l;
      } else {
        if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l.v())) {
          return List<uint64_t>::nil();
        } else {
          const auto &[a0, a1] =
              std::get<typename List<uint64_t>::Cons>(_loop_l.v());
          List<uint64_t> rotated =
              a1->app(List<uint64_t>::cons(a0, List<uint64_t>::nil()));
          _loop_l = std::move(rotated);
          _loop_n =
              (((_loop_n - UINT64_C(1)) > _loop_n ? 0
                                                  : (_loop_n - UINT64_C(1))));
          _loop_fuel = fuel_;
        }
      }
    }
  }
}

List<uint64_t> LoopifyListTransforms::rotate_left(uint64_t n,
                                                  const List<uint64_t> &l) {
  return rotate_left_fuel((n + UINT64_C(1)), n, l);
}

List<uint64_t>
LoopifyListTransforms::uniq_sorted_fuel(uint64_t fuel,
                                        const List<uint64_t> &l) {
  // Builds the result front to back: _write points at the empty tail the next
  // cell fills.
  std::optional<List<uint64_t>> _root{};
  std::shared_ptr<List<uint64_t>> *_write = nullptr;
  const List<uint64_t> *_loop_l = &l;
  uint64_t _loop_fuel = fuel;
  while (true) {
    if (_loop_fuel <= 0) {
      auto _value = List<uint64_t>::nil();
      (_write ? *(*_write = std::make_shared<List<uint64_t>>(std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      uint64_t fuel_ = _loop_fuel - 1;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l->v())) {
        auto _value = List<uint64_t>::nil();
        (_write ? *(*_write =
                        std::make_shared<List<uint64_t>>(std::move(_value)))
                : _root.emplace(std::move(_value)));
        break;
      } else {
        const auto &[a0, a1] =
            std::get<typename List<uint64_t>::Cons>(_loop_l->v());
        auto &&_sv0 = *a1;
        if (std::holds_alternative<typename List<uint64_t>::Nil>(_sv0.v())) {
          auto _value = List<uint64_t>::cons(a0, List<uint64_t>::nil());
          (_write ? *(*_write =
                          std::make_shared<List<uint64_t>>(std::move(_value)))
                  : _root.emplace(std::move(_value)));
          break;
        } else {
          const auto &[a00, _] =
              std::get<typename List<uint64_t>::Cons>(_sv0.v());
          if (a0 == a00) {
            _loop_l = crane_raw(a1);
            _loop_fuel = fuel_;
            continue;
          } else {
            auto _cell = typename List<uint64_t>::Cons(a0, nullptr);
            List<uint64_t> &_node =
                (_write ? *(*_write = std::make_shared<List<uint64_t>>(
                                std::move(_cell)))
                        : _root.emplace(std::move(_cell)));
            _write = &std::get<typename List<uint64_t>::Cons>(_node.v_mut()).l;
            _loop_l = crane_raw(a1);
            _loop_fuel = fuel_;
            continue;
          }
        }
      }
    }
  }
  return std::move(*_root);
}

List<uint64_t> LoopifyListTransforms::uniq_sorted(const List<uint64_t> &l) {
  uint64_t len = l.length();
  return uniq_sorted_fuel(len, l);
}

uint64_t LoopifyListTransforms::step_sum(const List<uint64_t> &l) {
  // Explicit stack replaces the non-tail recursion of step_sum: _call frames
  // are pending calls, _after frames resume a caller.
  struct _call {
    const List<uint64_t> *l;
  };

  struct _after_step_sum_in_Cons {
    uint64_t contribution;
  };

  using _frame = std::variant<_call, _after_step_sum_in_Cons>;
  uint64_t _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&l});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
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
        _stack.emplace_back(_after_step_sum_in_Cons{contribution});
        _stack.emplace_back(_call{crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<_after_step_sum_in_Cons>(_popped));
      _stack.pop_back();
      uint64_t contribution = _f.contribution;
      _result = (contribution + std::move(_result));
    }
  }
  return _result;
}
