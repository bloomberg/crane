#include "loopify_strings.h"

List<uint64_t> LoopifyStrings::append(const List<uint64_t> &l1,
                                      List<uint64_t> l2) {
  // Builds the result front to back: _write points at the empty tail the next
  // cell fills.
  std::optional<List<uint64_t>> _root{};
  std::shared_ptr<List<uint64_t>> *_write = nullptr;
  const List<uint64_t> *_loop_l1 = &l1;
  while (true) {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l1->v())) {
      auto _value = std::move(l2);
      (_write ? *(*_write = std::make_shared<List<uint64_t>>(std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename List<uint64_t>::Cons>(_loop_l1->v());
      auto _cell = typename List<uint64_t>::Cons(a0, nullptr);
      List<uint64_t> &_node =
          (_write ? *(*_write =
                          std::make_shared<List<uint64_t>>(std::move(_cell)))
                  : _root.emplace(std::move(_cell)));
      _write = &std::get<typename List<uint64_t>::Cons>(_node.v_mut()).l;
      _loop_l1 = crane_raw(a1);
      continue;
    }
  }
  return std::move(*_root);
}

List<uint64_t> LoopifyStrings::join_with(uint64_t sep,
                                         const List<uint64_t> &l) {
  // Builds the result front to back: _write points at the empty tail the next
  // cell fills.
  std::optional<List<uint64_t>> _root{};
  std::shared_ptr<List<uint64_t>> *_write = nullptr;
  const List<uint64_t> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l->v())) {
      auto _value = List<uint64_t>::nil();
      (_write ? *(*_write = std::make_shared<List<uint64_t>>(std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename List<uint64_t>::Cons>(_loop_l->v());
      auto &&_sv = *a1;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(_sv.v())) {
        auto _value = List<uint64_t>::cons(a0, List<uint64_t>::nil());
        (_write ? *(*_write =
                        std::make_shared<List<uint64_t>>(std::move(_value)))
                : _root.emplace(std::move(_value)));
        break;
      } else {
        auto _cell1 = std::make_shared<List<uint64_t>>(
            typename List<uint64_t>::Cons(sep, nullptr));
        auto _cell = typename List<uint64_t>::Cons(a0, std::move(_cell1));
        List<uint64_t> &_node =
            (_write ? *(*_write =
                            std::make_shared<List<uint64_t>>(std::move(_cell)))
                    : _root.emplace(std::move(_cell)));
        _write =
            &std::get<typename List<uint64_t>::Cons>(std::get<
                typename List<uint64_t>::Cons>(_node.v_mut()).l->v_mut())
                .l;
        _loop_l = crane_raw(a1);
        continue;
      }
    }
  }
  return std::move(*_root);
}

List<uint64_t> LoopifyStrings::repeat_string(const List<uint64_t> &s,
                                             uint64_t n) {
  // Explicit stack replaces the non-tail recursion of repeat_string: _call
  // frames are pending calls, _after frames resume a caller.
  struct _call {
    uint64_t n;
  };

  struct _after_repeat_string_in_S {};

  using _frame = std::variant<_call, _after_repeat_string_in_S>;
  List<uint64_t> _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{n});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      uint64_t n = _f.n;
      if (n <= 0) {
        _result = List<uint64_t>::nil();
      } else {
        uint64_t n_ = n - 1;
        _stack.emplace_back(_after_repeat_string_in_S{});
        _stack.emplace_back(_call{n_});
      }
    } else {
      auto _f = std::move(std::get<_after_repeat_string_in_S>(_popped));
      _stack.pop_back();
      _result = append(s, std::move(_result));
    }
  }
  return _result;
}

List<uint64_t>
LoopifyStrings::repeat_with_sep(List<uint64_t> s, const List<uint64_t> &sep,
                                uint64_t n) {
  // Explicit stack replaces the non-tail recursion of repeat_with_sep: _call
  // frames are pending calls, _after frames resume a caller.
  struct _call {
    uint64_t n;
  };

  struct _after_repeat_with_sep_in_S {};

  using _frame = std::variant<_call, _after_repeat_with_sep_in_S>;
  List<uint64_t> _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{n});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      uint64_t n = _f.n;
      if (n <= 0) {
        _result = List<uint64_t>::nil();
      } else {
        uint64_t n_ = n - 1;
        if (n_ <= 0) {
          _result = s;
        } else {
          uint64_t _x = n_ - 1;
          _stack.emplace_back(_after_repeat_with_sep_in_S{});
          _stack.emplace_back(_call{n_});
        }
      }
    } else {
      auto _f = std::move(std::get<_after_repeat_with_sep_in_S>(_popped));
      _stack.pop_back();
      _result = append(s, append(sep, std::move(_result)));
    }
  }
  return _result;
}

List<uint64_t>
LoopifyStrings::string_chain_fuel(uint64_t fuel, const List<uint64_t> &s,
                                  uint64_t n, const List<uint64_t> &sep,
                                  List<uint64_t> end_marker) {
  // Explicit stack replaces the non-tail recursion of string_chain_fuel: _call
  // frames are pending calls, _after frames resume a caller.
  struct _call {
    uint64_t n;
    uint64_t fuel;
  };

  struct _after_string_chain_fuel_in_false {};

  using _frame = std::variant<_call, _after_string_chain_fuel_in_false>;
  List<uint64_t> _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{n, fuel});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      uint64_t n = _f.n;
      uint64_t fuel = _f.fuel;
      if (fuel <= 0) {
        _result = List<uint64_t>::nil();
      } else {
        uint64_t fuel_ = fuel - 1;
        if (n <= UINT64_C(0)) {
          _result = List<uint64_t>::nil();
        } else {
          _stack.emplace_back(_after_string_chain_fuel_in_false{});
          _stack.emplace_back(
              _call{(((n - UINT64_C(1)) > n ? 0 : (n - UINT64_C(1)))), fuel_});
        }
      }
    } else {
      auto _f = std::move(std::get<_after_string_chain_fuel_in_false>(_popped));
      _stack.pop_back();
      _result = append(s, append(sep, append(std::move(_result), end_marker)));
    }
  }
  return _result;
}

List<uint64_t> LoopifyStrings::string_chain(const List<uint64_t> &s, uint64_t n,
                                            const List<uint64_t> &sep,
                                            List<uint64_t> end_marker) {
  return string_chain_fuel(n, s, n, sep, std::move(end_marker));
}

List<uint64_t> LoopifyStrings::reverse(const List<uint64_t> &l) {
  // Explicit stack replaces the non-tail recursion of reverse: _call frames are
  // pending calls, _after frames resume a caller.
  struct _call {
    const List<uint64_t> *l;
  };

  struct _after_reverse_in_Cons {
    uint64_t a0;
  };

  using _frame = std::variant<_call, _after_reverse_in_Cons>;
  List<uint64_t> _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&l});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const List<uint64_t> &l = *_f.l;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
        _result = List<uint64_t>::nil();
      } else {
        const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
        _stack.emplace_back(_after_reverse_in_Cons{a0});
        _stack.emplace_back(_call{crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<_after_reverse_in_Cons>(_popped));
      _stack.pop_back();
      uint64_t a0 = _f.a0;
      _result = append(std::move(_result),
                       List<uint64_t>::cons(a0, List<uint64_t>::nil()));
    }
  }
  return _result;
}

bool LoopifyStrings::list_eq(const List<uint64_t> &l1,
                             const List<uint64_t> &l2) {
  // Explicit stack replaces the non-tail recursion of list_eq: _call frames are
  // pending calls, _after frames resume a caller.
  struct _call {
    const List<uint64_t> *l2;
    const List<uint64_t> *l1;
  };

  struct _after_list_eq_in_Cons {
    uint64_t a0;
    uint64_t a00;
  };

  using _frame = std::variant<_call, _after_list_eq_in_Cons>;
  bool _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&l2, &l1});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const List<uint64_t> &l2 = *_f.l2;
      const List<uint64_t> &l1 = *_f.l1;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(l1.v())) {
        if (std::holds_alternative<typename List<uint64_t>::Nil>(l2.v())) {
          _result = true;
        } else {
          _result = false;
        }
      } else {
        const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l1.v());
        if (std::holds_alternative<typename List<uint64_t>::Nil>(l2.v())) {
          _result = false;
        } else {
          const auto &[a00, a10] =
              std::get<typename List<uint64_t>::Cons>(l2.v());
          _stack.emplace_back(_after_list_eq_in_Cons{a0, a00});
          _stack.emplace_back(_call{crane_raw(a10), crane_raw(a1)});
        }
      }
    } else {
      auto _f = std::move(std::get<_after_list_eq_in_Cons>(_popped));
      _stack.pop_back();
      uint64_t a0 = _f.a0;
      uint64_t a00 = _f.a00;
      _result = (a0 == a00 && _result);
    }
  }
  return _result;
}

bool LoopifyStrings::is_palindrome(const List<uint64_t> &l) {
  return list_eq(l, reverse(l));
}

List<uint64_t> LoopifyStrings::intersperse(uint64_t sep,
                                           const List<uint64_t> &l) {
  return join_with(sep, l);
}

List<uint64_t> LoopifyStrings::intercalate(const List<uint64_t> &sep,
                                           const List<List<uint64_t>> &ll) {
  // Explicit stack replaces the non-tail recursion of intercalate: _call frames
  // are pending calls, _after frames resume a caller.
  struct _call {
    const List<List<uint64_t>> *ll;
  };

  struct _after_intercalate_in_Cons {
    List<uint64_t> a0;
  };

  using _frame = std::variant<_call, _after_intercalate_in_Cons>;
  List<uint64_t> _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&ll});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const List<List<uint64_t>> &ll = *_f.ll;
      if (std::holds_alternative<typename List<List<uint64_t>>::Nil>(ll.v())) {
        _result = List<uint64_t>::nil();
      } else {
        const auto &[a0, a1] =
            std::get<typename List<List<uint64_t>>::Cons>(ll.v());
        auto &&_sv = *a1;
        if (std::holds_alternative<typename List<List<uint64_t>>::Nil>(_sv.v())) {
          _result = std::move(a0);
        } else {
          _stack.emplace_back(_after_intercalate_in_Cons{a0});
          _stack.emplace_back(_call{crane_raw(a1)});
        }
      }
    } else {
      auto _f = std::move(std::get<_after_intercalate_in_Cons>(_popped));
      _stack.pop_back();
      List<uint64_t> a0 = std::move(_f.a0);
      _result = append(std::move(a0), append(sep, std::move(_result)));
    }
  }
  return _result;
}

List<uint64_t> LoopifyStrings::replicate(uint64_t n, uint64_t x) {
  // Builds the result front to back: _write points at the empty tail the next
  // cell fills.
  std::optional<List<uint64_t>> _root{};
  std::shared_ptr<List<uint64_t>> *_write = nullptr;
  while (true) {
    if (n <= 0) {
      auto _value = List<uint64_t>::nil();
      (_write ? *(*_write = std::make_shared<List<uint64_t>>(std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      uint64_t n_ = n - 1;
      auto _cell = typename List<uint64_t>::Cons(x, nullptr);
      List<uint64_t> &_node =
          (_write ? *(*_write =
                          std::make_shared<List<uint64_t>>(std::move(_cell)))
                  : _root.emplace(std::move(_cell)));
      _write = &std::get<typename List<uint64_t>::Cons>(_node.v_mut()).l;
      n = n_;
      continue;
    }
  }
  return std::move(*_root);
}

List<std::pair<uint64_t, uint64_t>>
LoopifyStrings::run_length_aux(uint64_t current, uint64_t count,
                               const List<uint64_t> &l) {
  // Builds the result front to back: _write points at the empty tail the next
  // cell fills.
  std::optional<List<std::pair<uint64_t, uint64_t>>> _root{};
  std::shared_ptr<List<std::pair<uint64_t, uint64_t>>> *_write = nullptr;
  const List<uint64_t> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l->v())) {
      if (count == UINT64_C(0)) {
        auto _value = List<std::pair<uint64_t, uint64_t>>::nil();
        (_write ? *(*_write =
                        std::make_shared<List<std::pair<uint64_t, uint64_t>>>(
                            std::move(_value)))
                : _root.emplace(std::move(_value)));
        break;
      } else {
        auto _value = List<std::pair<uint64_t, uint64_t>>::cons(
            std::make_pair(current, count),
            List<std::pair<uint64_t, uint64_t>>::nil());
        (_write ? *(*_write =
                        std::make_shared<List<std::pair<uint64_t, uint64_t>>>(
                            std::move(_value)))
                : _root.emplace(std::move(_value)));
        break;
      }
    } else {
      const auto &[a0, a1] =
          std::get<typename List<uint64_t>::Cons>(_loop_l->v());
      if (a0 == current) {
        _loop_l = crane_raw(a1);
        count = (count + UINT64_C(1));
        continue;
      } else if (count == UINT64_C(0)) {
        _loop_l = crane_raw(a1);
        count = UINT64_C(1);
        current = a0;
        continue;
      } else {
        auto _cell = typename List<std::pair<uint64_t, uint64_t>>::Cons(
            std::make_pair(current, count), nullptr);
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
        count = UINT64_C(1);
        current = a0;
        continue;
      }
    }
  }
  return std::move(*_root);
}

List<std::pair<uint64_t, uint64_t>>
LoopifyStrings::run_length_encode(const List<uint64_t> &l) {
  if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
    return List<std::pair<uint64_t, uint64_t>>::nil();
  } else {
    const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
    return run_length_aux(a0, UINT64_C(1), *a1);
  }
}
