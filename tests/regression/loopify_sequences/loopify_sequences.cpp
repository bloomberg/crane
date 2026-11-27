#include "loopify_sequences.h"

/// alternate_sum sign acc l alternating sum with sign flip.
uint64_t LoopifySequences::alternate_sum(uint64_t sign, uint64_t acc,
                                         const List<uint64_t> &l) {
  // Loop replaces the tail recursion: each recursive call updates the loop
  // variables.
  const List<uint64_t> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l->v())) {
      return acc;
    } else {
      const auto &[a0, a1] =
          std::get<typename List<uint64_t>::Cons>(_loop_l->v());
      uint64_t new_acc;
      if (sign == UINT64_C(1)) {
        new_acc = acc + a0;
      } else {
        new_acc = (acc - a0 > acc ? 0 : acc - a0);
      }
      uint64_t new_sign;
      if (sign == UINT64_C(1)) {
        new_sign = UINT64_C(0);
      } else {
        new_sign = UINT64_C(1);
      }
      _loop_l = crane_raw(a1);
      acc = new_acc;
      sign = new_sign;
    }
  }
}

/// collatz_list n generates collatz sequence.
List<uint64_t> LoopifySequences::collatz_list_fuel(uint64_t fuel, uint64_t n) {
  // Explicit stack replaces the non-tail recursion of collatz_list_fuel: _call
  // frames are pending calls, _after frames resume a caller.
  struct _call {
    uint64_t n;
    uint64_t fuel;
  };

  struct _after_collatz_list_fuel_in_false {
    uint64_t n;
  };

  struct _after_collatz_list_fuel_in_true {
    uint64_t n;
  };

  using _frame = std::variant<_call, _after_collatz_list_fuel_in_false,
                              _after_collatz_list_fuel_in_true>;
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
        uint64_t f = fuel - 1;
        if (n == UINT64_C(1)) {
          _result = List<uint64_t>::cons(UINT64_C(1), List<uint64_t>::nil());
        } else if ((UINT64_C(2) ? n % UINT64_C(2) : n) == UINT64_C(0)) {
          _stack.emplace_back(_after_collatz_list_fuel_in_true{n});
          _stack.emplace_back(_call{(UINT64_C(2) ? n / UINT64_C(2) : 0), f});
        } else {
          _stack.emplace_back(_after_collatz_list_fuel_in_false{n});
          _stack.emplace_back(_call{UINT64_C(3) * n + UINT64_C(1), f});
        }
      }
    } else if (
            std::holds_alternative<_after_collatz_list_fuel_in_false>(_popped)) {
      auto _f = std::move(std::get<_after_collatz_list_fuel_in_false>(_popped));
      _stack.pop_back();
      uint64_t n = _f.n;
      _result = List<uint64_t>::cons(n, std::move(_result));
    } else {
      auto _f = std::move(std::get<_after_collatz_list_fuel_in_true>(_popped));
      _stack.pop_back();
      uint64_t n = _f.n;
      _result = List<uint64_t>::cons(n, std::move(_result));
    }
  }
  return _result;
}

List<uint64_t> LoopifySequences::collatz_list(uint64_t n) {
  return collatz_list_fuel(UINT64_C(1000), n);
}

/// run_sum l running sum (scanl for addition).
List<uint64_t> LoopifySequences::run_sum_aux(uint64_t acc,
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
      uint64_t new_acc = acc + a0;
      auto _cell = typename List<uint64_t>::Cons(new_acc, nullptr);
      List<uint64_t> &_node =
          (_write ? *(*_write =
                          std::make_shared<List<uint64_t>>(std::move(_cell)))
                  : _root.emplace(std::move(_cell)));
      _write = &std::get<typename List<uint64_t>::Cons>(_node.v_mut()).l;
      _loop_l = crane_raw(a1);
      acc = new_acc;
      continue;
    }
  }
  return std::move(*_root);
}

List<uint64_t> LoopifySequences::run_sum(const List<uint64_t> &l) {
  return List<uint64_t>::cons(UINT64_C(0), run_sum_aux(UINT64_C(0), l));
}

/// rotate_left n l rotates list left by n positions.
List<uint64_t> LoopifySequences::rotate_left_fuel(uint64_t fuel, uint64_t n,
                                                  const List<uint64_t> &l) {
  // Loop replaces the tail recursion: each recursive call updates the loop
  // variables.
  List<uint64_t> _loop_l = l;
  while (true) {
    if (fuel <= 0) {
      return _loop_l;
    } else {
      uint64_t f = fuel - 1;
      if (n == UINT64_C(0)) {
        return _loop_l;
      } else {
        if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l.v())) {
          return List<uint64_t>::nil();
        } else {
          const auto &[a0, a1] =
              std::get<typename List<uint64_t>::Cons>(_loop_l.v());
          _loop_l = a1->app(List<uint64_t>::cons(a0, List<uint64_t>::nil()));
          n = (n - UINT64_C(1) > n ? 0 : n - UINT64_C(1));
          fuel = f;
        }
      }
    }
  }
}

List<uint64_t> LoopifySequences::rotate_left(uint64_t n,
                                             const List<uint64_t> &l) {
  return rotate_left_fuel(UINT64_C(100), n, l);
}

/// sum_acc acc l sum with accumulator.
uint64_t LoopifySequences::sum_acc(uint64_t acc, const List<uint64_t> &l) {
  // Loop replaces the tail recursion: each recursive call updates the loop
  // variables.
  const List<uint64_t> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l->v())) {
      return acc;
    } else {
      const auto &[a0, a1] =
          std::get<typename List<uint64_t>::Cons>(_loop_l->v());
      _loop_l = crane_raw(a1);
      acc = acc + a0;
    }
  }
}

/// repeat_string s n repeats string n times (using list as string).
List<uint64_t> LoopifySequences::repeat_string(const List<uint64_t> &s,
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
        uint64_t m = n - 1;
        _stack.emplace_back(_after_repeat_string_in_S{});
        _stack.emplace_back(_call{m});
      }
    } else {
      auto _f = std::move(std::get<_after_repeat_string_in_S>(_popped));
      _stack.pop_back();
      _result = s.app(std::move(_result));
    }
  }
  return _result;
}

/// repeat_with_sep s sep n repeats with separator.
List<uint64_t>
LoopifySequences::repeat_with_sep(List<uint64_t> s, const List<uint64_t> &sep,
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
        uint64_t m = n - 1;
        if (m <= 0) {
          _result = s;
        } else {
          uint64_t _x = m - 1;
          _stack.emplace_back(_after_repeat_with_sep_in_S{});
          _stack.emplace_back(_call{m});
        }
      }
    } else {
      auto _f = std::move(std::get<_after_repeat_with_sep_in_S>(_popped));
      _stack.pop_back();
      _result = s.app(sep.app(std::move(_result)));
    }
  }
  return _result;
}

/// string_chain s n recursive string chain: s-chain(s, n-1)-end.
List<uint64_t>
LoopifySequences::string_chain_fuel(uint64_t fuel, const List<uint64_t> &s,
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
        uint64_t f = fuel - 1;
        if (n <= UINT64_C(0)) {
          _result = List<uint64_t>::nil();
        } else {
          _stack.emplace_back(_after_string_chain_fuel_in_false{});
          _stack.emplace_back(
              _call{(n - UINT64_C(1) > n ? 0 : n - UINT64_C(1)), f});
        }
      }
    } else {
      auto _f = std::move(std::get<_after_string_chain_fuel_in_false>(_popped));
      _stack.pop_back();
      _result = s.app(sep.app(_result.app(sep.app(end_marker))));
    }
  }
  return _result;
}

List<uint64_t>
LoopifySequences::string_chain(const List<uint64_t> &s, uint64_t n,
                               const List<uint64_t> &sep,
                               List<uint64_t> end_marker) {
  return string_chain_fuel(UINT64_C(1000), s, n, sep, std::move(end_marker));
}

/// split_by_sign l base pos neg splits list based on base threshold.
std::pair<List<uint64_t>, List<uint64_t>>
LoopifySequences::split_by_sign(const List<uint64_t> &l, uint64_t base,
                                const List<uint64_t> &pos,
                                const List<uint64_t> &neg) {
  // Loop replaces the tail recursion: each recursive call updates the loop
  // variables.
  List<uint64_t> _loop_neg = neg;
  List<uint64_t> _loop_pos = pos;
  const List<uint64_t> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l->v())) {
      return std::make_pair(_loop_pos, _loop_neg);
    } else {
      const auto &[a0, a1] =
          std::get<typename List<uint64_t>::Cons>(_loop_l->v());
      if (base <= a0) {
        _loop_pos = List<uint64_t>::cons(a0, std::move(_loop_pos));
      } else {
        _loop_neg = List<uint64_t>::cons(a0, std::move(_loop_neg));
      }
      _loop_l = crane_raw(a1);
    }
  }
}

/// differences l computes differences between consecutive elements.
List<uint64_t> LoopifySequences::differences(const List<uint64_t> &l) {
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
        auto _cell = typename List<uint64_t>::Cons(
            (a00 - a0 > a00 ? 0 : a00 - a0), nullptr);
        List<uint64_t> &_node =
            (_write ? *(*_write =
                            std::make_shared<List<uint64_t>>(std::move(_cell)))
                    : _root.emplace(std::move(_cell)));
        _write = &std::get<typename List<uint64_t>::Cons>(_node.v_mut()).l;
        _loop_l = crane_raw(a1);
        continue;
      }
    }
  }
  return std::move(*_root);
}

/// replace_at idx value l replaces element at index with value.
List<uint64_t> LoopifySequences::replace_at(uint64_t idx, uint64_t value,
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
      if (idx == UINT64_C(0)) {
        auto _value = List<uint64_t>::cons(value, crane::shared_child(a1));
        (_write ? *(*_write =
                        std::make_shared<List<uint64_t>>(std::move(_value)))
                : _root.emplace(std::move(_value)));
        break;
      } else {
        auto _cell = typename List<uint64_t>::Cons(a0, nullptr);
        List<uint64_t> &_node =
            (_write ? *(*_write =
                            std::make_shared<List<uint64_t>>(std::move(_cell)))
                    : _root.emplace(std::move(_cell)));
        _write = &std::get<typename List<uint64_t>::Cons>(_node.v_mut()).l;
        _loop_l = crane_raw(a1);
        idx = (idx - UINT64_C(1) > idx ? 0 : idx - UINT64_C(1));
        continue;
      }
    }
  }
  return std::move(*_root);
}

/// cycle n l repeats list n times.
List<uint64_t> LoopifySequences::cycle(uint64_t n, const List<uint64_t> &l) {
  // Explicit stack replaces the non-tail recursion of cycle: _call frames are
  // pending calls, _after frames resume a caller.
  struct _call {
    uint64_t n;
  };

  struct _after_cycle_in_Cons {};

  using _frame = std::variant<_call, _after_cycle_in_Cons>;
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
        uint64_t m = n - 1;
        if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
          _result = List<uint64_t>::nil();
        } else {
          _stack.emplace_back(_after_cycle_in_Cons{});
          _stack.emplace_back(_call{m});
        }
      }
    } else {
      auto _f = std::move(std::get<_after_cycle_in_Cons>(_popped));
      _stack.pop_back();
      _result = l.app(std::move(_result));
    }
  }
  return _result;
}

/// Helper: get first element.
uint64_t LoopifySequences::first_elem(const List<uint64_t> &l) {
  if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
    return UINT64_C(0);
  } else {
    const auto &[a0, _] = std::get<typename List<uint64_t>::Cons>(l.v());
    return a0;
  }
}

/// Helper: get last element.
uint64_t LoopifySequences::last_elem(const List<uint64_t> &l) {
  // Loop replaces the tail recursion: each recursive call updates the loop
  // variables.
  const List<uint64_t> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l->v())) {
      return UINT64_C(0);
    } else {
      const auto &[a0, a1] =
          std::get<typename List<uint64_t>::Cons>(_loop_l->v());
      auto &&_sv = *a1;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(_sv.v())) {
        return a0;
      } else {
        _loop_l = crane_raw(a1);
      }
    }
  }
}

/// Helper: remove first element.
List<uint64_t> LoopifySequences::tail_list(const List<uint64_t> &l) {
  if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
    return List<uint64_t>::nil();
  } else {
    const auto &[_, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
    return *a1;
  }
}

/// Helper: remove last element.
List<uint64_t> LoopifySequences::init_list(const List<uint64_t> &l) {
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
        auto _value = List<uint64_t>::nil();
        (_write ? *(*_write =
                        std::make_shared<List<uint64_t>>(std::move(_value)))
                : _root.emplace(std::move(_value)));
        break;
      } else {
        auto _cell = typename List<uint64_t>::Cons(a0, nullptr);
        List<uint64_t> &_node =
            (_write ? *(*_write =
                            std::make_shared<List<uint64_t>>(std::move(_cell)))
                    : _root.emplace(std::move(_cell)));
        _write = &std::get<typename List<uint64_t>::Cons>(_node.v_mut()).l;
        _loop_l = crane_raw(a1);
        continue;
      }
    }
  }
  return std::move(*_root);
}

/// is_palindrome s checks if list is a palindrome.
bool LoopifySequences::is_palindrome_fuel(uint64_t fuel,
                                          const List<uint64_t> &s) {
  // Loop replaces the tail recursion: each recursive call updates the loop
  // variables.
  List<uint64_t> _loop_s = s;
  while (true) {
    if (fuel <= 0) {
      return true;
    } else {
      uint64_t f = fuel - 1;
      uint64_t n = _loop_s.length();
      if (n <= 0) {
        return true;
      } else {
        uint64_t n0 = n - 1;
        if (n0 <= 0) {
          return true;
        } else {
          uint64_t _x = n0 - 1;
          if (first_elem(_loop_s) == last_elem(_loop_s)) {
            _loop_s = init_list(tail_list(std::move(_loop_s)));
            fuel = f;
          } else {
            return false;
          }
        }
      }
    }
  }
}

bool LoopifySequences::is_palindrome(const List<uint64_t> &s) {
  return is_palindrome_fuel(UINT64_C(1000), s);
}

/// string_subsequences s generates all subsequences treating list as string.
List<List<uint64_t>>
LoopifySequences::string_subsequences(const List<uint64_t> &s) {
  // Explicit stack replaces the non-tail recursion of string_subsequences:
  // _call frames are pending calls, _after frames resume a caller.
  struct _call {
    const List<uint64_t> *s;
  };

  struct _after_string_subsequences_in_Cons {
    uint64_t a0;
  };

  using _frame = std::variant<_call, _after_string_subsequences_in_Cons>;
  List<List<uint64_t>> _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&s});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const List<uint64_t> &s = *_f.s;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(s.v())) {
        _result = List<List<uint64_t>>::cons(List<uint64_t>::nil(),
                                             List<List<uint64_t>>::nil());
      } else {
        const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(s.v());
        _stack.emplace_back(_after_string_subsequences_in_Cons{a0});
        _stack.emplace_back(_call{crane_raw(a1)});
      }
    } else {
      auto _f =
          std::move(std::get<_after_string_subsequences_in_Cons>(_popped));
      _stack.pop_back();
      uint64_t a0 = _f.a0;
      List<List<uint64_t>> sub_rest = std::move(_result);
      auto map_prepend_c =
          [&](const List<List<uint64_t>> &lsts) -> List<List<uint64_t>> {
            // Explicit stack replaces the non-tail recursion of map_prepend_c:
            // _call frames are pending calls, _after frames resume a caller.
            struct _call {
              const List<List<uint64_t>> *lsts;
            };

            struct _after_map_prepend_c_in_Cons {
              List<uint64_t> a00;
            };

            using _frame = std::variant<_call, _after_map_prepend_c_in_Cons>;
            List<List<uint64_t>> _result{};
            crane::small_vector<_frame> _stack;
            _stack.emplace_back(_call{&lsts});
            while (!_stack.empty()) {
              _frame &_popped = _stack.back();
              if (std::holds_alternative<_call>(_popped)) {
                auto _f = std::move(std::get<_call>(_popped));
                _stack.pop_back();
                const List<List<uint64_t>> &lsts = *_f.lsts;
                if (std::holds_alternative<typename List<List<uint64_t>>::Nil>(
                        lsts.v())) {
                  _result = List<List<uint64_t>>::nil();
                } else {
                  const auto &[a00, a10] =
                      std::get<typename List<List<uint64_t>>::Cons>(lsts.v());
                  _stack.emplace_back(_after_map_prepend_c_in_Cons{a00});
                  _stack.emplace_back(_call{crane_raw(a10)});
                }
              } else {
                auto _f =
                    std::move(std::get<_after_map_prepend_c_in_Cons>(_popped));
                _stack.pop_back();
                List<uint64_t> a00 = std::move(_f.a00);
                _result = List<List<uint64_t>>::cons(
                    List<uint64_t>::cons(a0, std::move(a00)),
                    std::move(_result));
              }
            }
            return _result;
          };
      _result = sub_rest.app(map_prepend_c(sub_rest));
    }
  }
  return _result;
}

/// run_length_groups l groups consecutive runs into sublist lengths.
List<uint64_t>
LoopifySequences::run_length_groups_aux(uint64_t prev, uint64_t count,
                                        const List<uint64_t> &l) {
  // Builds the result front to back: _write points at the empty tail the next
  // cell fills.
  std::optional<List<uint64_t>> _root{};
  std::shared_ptr<List<uint64_t>> *_write = nullptr;
  const List<uint64_t> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l->v())) {
      if (count == UINT64_C(0)) {
        auto _value = List<uint64_t>::nil();
        (_write ? *(*_write =
                        std::make_shared<List<uint64_t>>(std::move(_value)))
                : _root.emplace(std::move(_value)));
        break;
      } else {
        auto _value = List<uint64_t>::cons(count, List<uint64_t>::nil());
        (_write ? *(*_write =
                        std::make_shared<List<uint64_t>>(std::move(_value)))
                : _root.emplace(std::move(_value)));
        break;
      }
    } else {
      const auto &[a0, a1] =
          std::get<typename List<uint64_t>::Cons>(_loop_l->v());
      if (prev == a0) {
        _loop_l = crane_raw(a1);
        count = (count + 1);
        prev = a0;
        continue;
      } else if (count == UINT64_C(0)) {
        _loop_l = crane_raw(a1);
        count = UINT64_C(1);
        prev = a0;
        continue;
      } else {
        auto _cell = typename List<uint64_t>::Cons(count, nullptr);
        List<uint64_t> &_node =
            (_write ? *(*_write =
                            std::make_shared<List<uint64_t>>(std::move(_cell)))
                    : _root.emplace(std::move(_cell)));
        _write = &std::get<typename List<uint64_t>::Cons>(_node.v_mut()).l;
        _loop_l = crane_raw(a1);
        count = UINT64_C(1);
        prev = a0;
        continue;
      }
    }
  }
  return std::move(*_root);
}

List<uint64_t> LoopifySequences::run_length_groups(const List<uint64_t> &l) {
  if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
    return List<uint64_t>::nil();
  } else {
    const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
    return run_length_groups_aux(a0, UINT64_C(1), *a1);
  }
}

/// is_prefix_of l1 l2 checks if l1 is a prefix of l2.
bool LoopifySequences::is_prefix_of(const List<uint64_t> &l1,
                                    const List<uint64_t> &l2) {
  // Loop replaces the tail recursion: each recursive call updates the loop
  // variables.
  const List<uint64_t> *_loop_l2 = &l2;
  const List<uint64_t> *_loop_l1 = &l1;
  while (true) {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l1->v())) {
      return true;
    } else {
      const auto &[a0, a1] =
          std::get<typename List<uint64_t>::Cons>(_loop_l1->v());
      if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l2->v())) {
        return false;
      } else {
        const auto &[a00, a10] =
            std::get<typename List<uint64_t>::Cons>(_loop_l2->v());
        if (a0 == a00) {
          _loop_l2 = crane_raw(a10);
          _loop_l1 = crane_raw(a1);
        } else {
          return false;
        }
      }
    }
  }
}

/// lis l longest increasing subsequence (greedy, not optimal).
List<uint64_t> LoopifySequences::lis(const List<uint64_t> &l) {
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
      auto &&_sv0 = *a1;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(_sv0.v())) {
        auto _value = *_loop_l;
        (_write ? *(*_write =
                        std::make_shared<List<uint64_t>>(std::move(_value)))
                : _root.emplace(std::move(_value)));
        break;
      } else {
        const auto &[a00, _] =
            std::get<typename List<uint64_t>::Cons>(_sv0.v());
        if (a0 < a00) {
          auto _cell = typename List<uint64_t>::Cons(a0, nullptr);
          List<uint64_t> &_node =
              (_write ? *(*_write = std::make_shared<List<uint64_t>>(
                              std::move(_cell)))
                      : _root.emplace(std::move(_cell)));
          _write = &std::get<typename List<uint64_t>::Cons>(_node.v_mut()).l;
          _loop_l = crane_raw(a1);
          continue;
        } else {
          _loop_l = crane_raw(a1);
          continue;
        }
      }
    }
  }
  return std::move(*_root);
}

/// Helper: check if element is in list.
bool LoopifySequences::elem(uint64_t x, const List<uint64_t> &l) {
  // Explicit stack replaces the non-tail recursion of elem: _call frames are
  // pending calls, _after frames resume a caller.
  struct _call {
    const List<uint64_t> *l;
  };

  struct _after_elem_in_Cons {
    uint64_t a0;
  };

  using _frame = std::variant<_call, _after_elem_in_Cons>;
  bool _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&l});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const List<uint64_t> &l = *_f.l;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
        _result = false;
      } else {
        const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
        _stack.emplace_back(_after_elem_in_Cons{a0});
        _stack.emplace_back(_call{crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<_after_elem_in_Cons>(_popped));
      _stack.pop_back();
      uint64_t a0 = _f.a0;
      _result = ((x == a0) || _result);
    }
  }
  return _result;
}

/// Helper: filter list.
List<uint64_t> LoopifySequences::filter_ne(uint64_t x,
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
      if (x == a0) {
        _loop_l = crane_raw(a1);
        continue;
      } else {
        auto _cell = typename List<uint64_t>::Cons(a0, nullptr);
        List<uint64_t> &_node =
            (_write ? *(*_write =
                            std::make_shared<List<uint64_t>>(std::move(_cell)))
                    : _root.emplace(std::move(_cell)));
        _write = &std::get<typename List<uint64_t>::Cons>(_node.v_mut()).l;
        _loop_l = crane_raw(a1);
        continue;
      }
    }
  }
  return std::move(*_root);
}

/// nub l removes duplicates from list.
List<uint64_t> LoopifySequences::nub_fuel(uint64_t fuel,
                                          const List<uint64_t> &l) {
  // Builds the result front to back: _write points at the empty tail the next
  // cell fills.
  std::optional<List<uint64_t>> _root{};
  std::shared_ptr<List<uint64_t>> *_write = nullptr;
  List<uint64_t> _loop_l = l;
  while (true) {
    if (fuel <= 0) {
      auto _value = List<uint64_t>::nil();
      (_write ? *(*_write = std::make_shared<List<uint64_t>>(std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      uint64_t f = fuel - 1;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l.v())) {
        auto _value = List<uint64_t>::nil();
        (_write ? *(*_write =
                        std::make_shared<List<uint64_t>>(std::move(_value)))
                : _root.emplace(std::move(_value)));
        break;
      } else {
        const auto &[a0, a1] =
            std::get<typename List<uint64_t>::Cons>(_loop_l.v());
        auto _cell = typename List<uint64_t>::Cons(a0, nullptr);
        List<uint64_t> &_node =
            (_write ? *(*_write =
                            std::make_shared<List<uint64_t>>(std::move(_cell)))
                    : _root.emplace(std::move(_cell)));
        _write = &std::get<typename List<uint64_t>::Cons>(_node.v_mut()).l;
        _loop_l = filter_ne(a0, *a1);
        fuel = f;
        continue;
      }
    }
  }
  return std::move(*_root);
}

List<uint64_t> LoopifySequences::nub(const List<uint64_t> &l) {
  return nub_fuel(l.length(), l);
}

/// group l groups consecutive equal elements.
List<List<uint64_t>> LoopifySequences::group_fuel(uint64_t fuel,
                                                  const List<uint64_t> &l) {
  // Explicit stack replaces the non-tail recursion of group_fuel: _call frames
  // are pending calls, _after frames resume a caller.
  struct _call {
    const List<uint64_t> *l;
    uint64_t fuel;
  };

  struct _after_group_fuel_in_false {
    uint64_t a0;
  };

  struct _after_group_fuel_in_true {
    uint64_t a0;
  };

  using _frame = std::variant<_call, _after_group_fuel_in_false,
                              _after_group_fuel_in_true>;
  List<List<uint64_t>> _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&l, fuel});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const List<uint64_t> &l = *_f.l;
      uint64_t fuel = _f.fuel;
      if (fuel <= 0) {
        _result = List<List<uint64_t>>::nil();
      } else {
        uint64_t f = fuel - 1;
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
            const auto &[a00, _] =
                std::get<typename List<uint64_t>::Cons>(_sv0.v());
            if (a0 == a00) {
              _stack.emplace_back(_after_group_fuel_in_true{a0});
            } else {
              _stack.emplace_back(_after_group_fuel_in_false{a0});
            }
            _stack.emplace_back(_call{crane_raw(a1), f});
          }
        }
      }
    } else if (std::holds_alternative<_after_group_fuel_in_false>(_popped)) {
      auto _f = std::move(std::get<_after_group_fuel_in_false>(_popped));
      _stack.pop_back();
      uint64_t a0 = _f.a0;
      _result = List<List<uint64_t>>::cons(
          List<uint64_t>::cons(a0, List<uint64_t>::nil()), std::move(_result));
    } else {
      auto _f = std::move(std::get<_after_group_fuel_in_true>(_popped));
      _stack.pop_back();
      uint64_t a0 = _f.a0;
      List<List<uint64_t>> _tmp1 = std::move(_result);
      if (std::holds_alternative<typename List<List<uint64_t>>::Nil>(
              _tmp1.v_mut())) {
        _result = List<List<uint64_t>>::cons(
            List<uint64_t>::cons(a0, List<uint64_t>::nil()),
            List<List<uint64_t>>::nil());
      } else {
        auto &[a01, a11] =
            std::get<typename List<List<uint64_t>>::Cons>(_tmp1.v_mut());
        _result = List<List<uint64_t>>::cons(
            List<uint64_t>::cons(a0, std::move(a01)), crane::shared_child(a11));
      }
    }
  }
  return _result;
}

List<List<uint64_t>> LoopifySequences::group(const List<uint64_t> &l) {
  return group_fuel(l.length(), l);
}

/// Helper: get head with default.
uint64_t LoopifySequences::head_or(uint64_t default0, const List<uint64_t> &l) {
  if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
    return default0;
  } else {
    const auto &[a0, _] = std::get<typename List<uint64_t>::Cons>(l.v());
    return a0;
  }
}

/// remove_if_sum_even l removes elements where sum with next is even.
List<uint64_t> LoopifySequences::remove_if_sum_even(const List<uint64_t> &l) {
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
      uint64_t next = head_or(UINT64_C(0), *a1);
      if ((UINT64_C(2) ? (a0 + next) % UINT64_C(2) : a0 + next) ==
          UINT64_C(0)) {
        _loop_l = crane_raw(a1);
        continue;
      } else {
        auto _cell = typename List<uint64_t>::Cons(a0, nullptr);
        List<uint64_t> &_node =
            (_write ? *(*_write =
                            std::make_shared<List<uint64_t>>(std::move(_cell)))
                    : _root.emplace(std::move(_cell)));
        _write = &std::get<typename List<uint64_t>::Cons>(_node.v_mut()).l;
        _loop_l = crane_raw(a1);
        continue;
      }
    }
  }
  return std::move(*_root);
}

/// run_length_encode l encodes consecutive runs: 1,1,2,2,2 -> (1,2),(2,3).
List<std::pair<uint64_t, uint64_t>>
LoopifySequences::run_length_encode_fuel(uint64_t fuel,
                                         const List<uint64_t> &l) {
  // Explicit stack replaces the non-tail recursion of run_length_encode_fuel:
  // _call frames are pending calls, _after frames resume a caller.
  struct _call {
    const List<uint64_t> *l;
    uint64_t fuel;
  };

  struct _after_run_length_encode_fuel_in_Cons {
    uint64_t a0;
  };

  using _frame = std::variant<_call, _after_run_length_encode_fuel_in_Cons>;
  List<std::pair<uint64_t, uint64_t>> _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&l, fuel});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const List<uint64_t> &l = *_f.l;
      uint64_t fuel = _f.fuel;
      if (fuel <= 0) {
        _result = List<std::pair<uint64_t, uint64_t>>::nil();
      } else {
        uint64_t f = fuel - 1;
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
            _stack.emplace_back(_after_run_length_encode_fuel_in_Cons{a0});
            _stack.emplace_back(_call{crane_raw(a1), f});
          }
        }
      }
    } else {
      auto _f =
          std::move(std::get<_after_run_length_encode_fuel_in_Cons>(_popped));
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
              std::make_pair(y, (n + 1)), crane::shared_child(a11));
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

List<std::pair<uint64_t, uint64_t>>
LoopifySequences::run_length_encode(const List<uint64_t> &l) {
  return run_length_encode_fuel(l.length(), l);
}

/// between lo hi l filters elements in range lo, hi.
List<uint64_t> LoopifySequences::between(uint64_t lo, uint64_t hi,
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
      if (((lo <= a0) && (a0 <= hi))) {
        auto _cell = typename List<uint64_t>::Cons(a0, nullptr);
        List<uint64_t> &_node =
            (_write ? *(*_write =
                            std::make_shared<List<uint64_t>>(std::move(_cell)))
                    : _root.emplace(std::move(_cell)));
        _write = &std::get<typename List<uint64_t>::Cons>(_node.v_mut()).l;
        _loop_l = crane_raw(a1);
        continue;
      } else {
        _loop_l = crane_raw(a1);
        continue;
      }
    }
  }
  return std::move(*_root);
}
