#include "loopify_list_pairing.h"

std::pair<List<uint64_t>, List<uint64_t>>
LoopifyListPairing::unzip(const List<std::pair<uint64_t, uint64_t>> &l) {
  // Explicit stack replaces the non-tail recursion of unzip: _call frames are
  // pending calls, _after frames resume a caller.
  struct _call {
    const List<std::pair<uint64_t, uint64_t>> *l;
  };

  struct _after_unzip_in_pair {
    uint64_t a;
    uint64_t b;
  };

  using _frame = std::variant<_call, _after_unzip_in_pair>;
  std::pair<List<uint64_t>, List<uint64_t>> _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&l});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const List<std::pair<uint64_t, uint64_t>> &l = *_f.l;
      if (std::holds_alternative<
              typename List<std::pair<uint64_t, uint64_t>>::Nil>(l.v())) {
        _result = std::make_pair(List<uint64_t>::nil(), List<uint64_t>::nil());
      } else {
        const auto &[a0, a1] =
            std::get<typename List<std::pair<uint64_t, uint64_t>>::Cons>(l.v());
        const auto &[a, b] = a0;
        _stack.emplace_back(_after_unzip_in_pair{a, b});
        _stack.emplace_back(_call{crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<_after_unzip_in_pair>(_popped));
      _stack.pop_back();
      uint64_t a = _f.a;
      uint64_t b = _f.b;
      auto [xs, ys] = std::move(_result);
      _result = std::make_pair(List<uint64_t>::cons(a, std::move(xs)),
                               List<uint64_t>::cons(b, std::move(ys)));
    }
  }
  return _result;
}

std::pair<List<uint64_t>, List<uint64_t>>
LoopifyListPairing::swizzle(const List<uint64_t> &l) {
  // Explicit stack replaces the non-tail recursion of swizzle: _call frames are
  // pending calls, _after frames resume a caller.
  struct _call {
    const List<uint64_t> *l;
  };

  struct _after_swizzle_in_Cons {
    uint64_t a0;
  };

  using _frame = std::variant<_call, _after_swizzle_in_Cons>;
  std::pair<List<uint64_t>, List<uint64_t>> _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&l});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const List<uint64_t> &l = *_f.l;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
        _result = std::make_pair(List<uint64_t>::nil(), List<uint64_t>::nil());
      } else {
        const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
        _stack.emplace_back(_after_swizzle_in_Cons{a0});
        _stack.emplace_back(_call{crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<_after_swizzle_in_Cons>(_popped));
      _stack.pop_back();
      uint64_t a0 = _f.a0;
      auto [odds, evens] = std::move(_result);
      _result = std::make_pair(List<uint64_t>::cons(a0, std::move(evens)),
                               std::move(odds));
    }
  }
  return _result;
}

std::pair<List<uint64_t>, List<uint64_t>>
LoopifyListPairing::partition(const List<uint64_t> &l) {
  // Explicit stack replaces the non-tail recursion of partition: _call frames
  // are pending calls, _after frames resume a caller.
  struct _call {
    const List<uint64_t> *l;
  };

  struct _after_partition_in_Cons {
    uint64_t a0;
  };

  using _frame = std::variant<_call, _after_partition_in_Cons>;
  std::pair<List<uint64_t>, List<uint64_t>> _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&l});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const List<uint64_t> &l = *_f.l;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
        _result = std::make_pair(List<uint64_t>::nil(), List<uint64_t>::nil());
      } else {
        const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
        _stack.emplace_back(_after_partition_in_Cons{a0});
        _stack.emplace_back(_call{crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<_after_partition_in_Cons>(_popped));
      _stack.pop_back();
      uint64_t a0 = _f.a0;
      auto [yes, no] = std::move(_result);
      if ((UINT64_C(2) ? a0 % UINT64_C(2) : a0) == UINT64_C(0)) {
        _result = std::make_pair(List<uint64_t>::cons(a0, std::move(yes)),
                                 std::move(no));
      } else {
        _result = std::make_pair(std::move(yes),
                                 List<uint64_t>::cons(a0, std::move(no)));
      }
    }
  }
  return _result;
}

List<std::pair<uint64_t, uint64_t>>
LoopifyListPairing::zip_longest_fuel(uint64_t fuel, const List<uint64_t> &l1,
                                     const List<uint64_t> &l2,
                                     uint64_t default0) {
  // Builds the result front to back: _write points at the empty tail the next
  // cell fills.
  std::optional<List<std::pair<uint64_t, uint64_t>>> _root{};
  std::shared_ptr<List<std::pair<uint64_t, uint64_t>>> *_write = nullptr;
  List<uint64_t> _loop_l2 = l2;
  List<uint64_t> _loop_l1 = l1;
  while (true) {
    if (fuel <= 0) {
      auto _value = List<std::pair<uint64_t, uint64_t>>::nil();
      (_write ? *(*_write =
                      std::make_shared<List<std::pair<uint64_t, uint64_t>>>(
                          std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      uint64_t fuel_ = fuel - 1;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l1.v())) {
        if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l2.v())) {
          auto _value = List<std::pair<uint64_t, uint64_t>>::nil();
          (_write ? *(*_write =
                          std::make_shared<List<std::pair<uint64_t, uint64_t>>>(
                              std::move(_value)))
                  : _root.emplace(std::move(_value)));
          break;
        } else {
          const auto &[a00, a10] =
              std::get<typename List<uint64_t>::Cons>(_loop_l2.v());
          auto _cell = typename List<std::pair<uint64_t, uint64_t>>::Cons(
              std::make_pair(default0, a00), nullptr);
          List<std::pair<uint64_t, uint64_t>> &_node =
              (_write ? *(*_write = std::make_shared<
                              List<std::pair<uint64_t, uint64_t>>>(
                              std::move(_cell)))
                      : _root.emplace(std::move(_cell)));
          _write =
              &std::get<typename List<std::pair<uint64_t, uint64_t>>::Cons>(
                  _node.v_mut())
                  .l;
          _loop_l2 = List<uint64_t>(*a10);
          _loop_l1 = List<uint64_t>::nil();
          fuel = fuel_;
          continue;
        }
      } else {
        const auto &[a0, a1] =
            std::get<typename List<uint64_t>::Cons>(_loop_l1.v());
        if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l2.v())) {
          auto _cell = typename List<std::pair<uint64_t, uint64_t>>::Cons(
              std::make_pair(a0, default0), nullptr);
          List<std::pair<uint64_t, uint64_t>> &_node =
              (_write ? *(*_write = std::make_shared<
                              List<std::pair<uint64_t, uint64_t>>>(
                              std::move(_cell)))
                      : _root.emplace(std::move(_cell)));
          _write =
              &std::get<typename List<std::pair<uint64_t, uint64_t>>::Cons>(
                  _node.v_mut())
                  .l;
          _loop_l2 = List<uint64_t>::nil();
          _loop_l1 = List<uint64_t>(*a1);
          fuel = fuel_;
          continue;
        } else {
          const auto &[a00, a10] =
              std::get<typename List<uint64_t>::Cons>(_loop_l2.v());
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
          _loop_l2 = List<uint64_t>(*a10);
          _loop_l1 = List<uint64_t>(*a1);
          fuel = fuel_;
          continue;
        }
      }
    }
  }
  return std::move(*_root);
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
  // Builds the result front to back: _write points at the empty tail the next
  // cell fills.
  std::optional<List<uint64_t>> _root{};
  std::shared_ptr<List<uint64_t>> *_write = nullptr;
  const List<uint64_t> *_loop_l2 = &l2;
  const List<uint64_t> *_loop_l1 = &l1;
  while (true) {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l1->v())) {
      auto _value = List<uint64_t>::nil();
      (_write ? *(*_write = std::make_shared<List<uint64_t>>(std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename List<uint64_t>::Cons>(_loop_l1->v());
      if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l2->v())) {
        auto _value = List<uint64_t>::nil();
        (_write ? *(*_write =
                        std::make_shared<List<uint64_t>>(std::move(_value)))
                : _root.emplace(std::move(_value)));
        break;
      } else {
        const auto &[a00, a10] =
            std::get<typename List<uint64_t>::Cons>(_loop_l2->v());
        auto _cell = typename List<uint64_t>::Cons(a0 + a00, nullptr);
        List<uint64_t> &_node =
            (_write ? *(*_write =
                            std::make_shared<List<uint64_t>>(std::move(_cell)))
                    : _root.emplace(std::move(_cell)));
        _write = &std::get<typename List<uint64_t>::Cons>(_node.v_mut()).l;
        _loop_l2 = crane_raw(a10);
        _loop_l1 = crane_raw(a1);
        continue;
      }
    }
  }
  return std::move(*_root);
}

std::pair<List<uint64_t>, List<uint64_t>>
LoopifyListPairing::split_even_odd(const List<uint64_t> &l) {
  return partition(l);
}
