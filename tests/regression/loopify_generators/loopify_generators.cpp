#include "loopify_generators.h"

/// Consolidated list generator functions.
/// cycle n l repeats the list n times: cycle 2 1,2 -> 1,2,1,2.
List<uint64_t> LoopifyGenerators::cycle(uint64_t n, const List<uint64_t> &l) {
  // Explicit stack replaces the non-tail recursion of cycle: _call frames are
  // pending calls, _after frames resume a caller.
  struct _call {
    uint64_t n;
  };

  struct _after_cycle_in_S {};

  using _frame = std::variant<_call, _after_cycle_in_S>;
  List<uint64_t> _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{n});
  while (!_stack.empty()) {
    _frame _popped = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      uint64_t n = _f.n;
      if (n <= 0) {
        _result = List<uint64_t>::nil();
      } else {
        uint64_t m = n - 1;
        _stack.emplace_back(_after_cycle_in_S{});
        _stack.emplace_back(_call{m});
      }
    } else {
      auto _f = std::move(std::get<_after_cycle_in_S>(_popped));
      _result = l.app(std::move(_result));
    }
  }
  return _result;
}

/// zip_longest l1 l2 default zips, using default for missing elements.
List<std::pair<uint64_t, uint64_t>>
LoopifyGenerators::zip_longest_aux(const List<uint64_t> &l1,
                                   const List<uint64_t> &l2, uint64_t default0,
                                   uint64_t fuel) {
  // Builds the result front to back: _write points at the empty tail the next
  // cell fills.
  std::optional<List<std::pair<uint64_t, uint64_t>>> _root{};
  std::shared_ptr<List<std::pair<uint64_t, uint64_t>>> *_write = nullptr;
  uint64_t _loop_fuel = fuel;
  List<uint64_t> _loop_l2 = l2;
  List<uint64_t> _loop_l1 = l1;
  while (true) {
    if (_loop_fuel <= 0) {
      auto _value = List<std::pair<uint64_t, uint64_t>>::nil();
      (_write ? *(*_write =
                      std::make_shared<List<std::pair<uint64_t, uint64_t>>>(
                          std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      uint64_t f = _loop_fuel - 1;
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
          _loop_fuel = f;
          _loop_l2 = List<uint64_t>(*a10);
          _loop_l1 = List<uint64_t>::nil();
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
          _loop_fuel = f;
          _loop_l2 = List<uint64_t>::nil();
          _loop_l1 = List<uint64_t>(*a1);
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
          _loop_fuel = f;
          _loop_l2 = List<uint64_t>(*a10);
          _loop_l1 = List<uint64_t>(*a1);
          continue;
        }
      }
    }
  }
  return std::move(*_root);
}

uint64_t LoopifyGenerators::len_impl(const List<uint64_t> &l) {
  // Explicit stack replaces the non-tail recursion of len_impl: _call frames
  // are pending calls, _after frames resume a caller.
  struct _call {
    const List<uint64_t> *l;
  };

  struct _after_len_impl_in_Cons {};

  using _frame = std::variant<_call, _after_len_impl_in_Cons>;
  uint64_t _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&l});
  while (!_stack.empty()) {
    _frame _popped = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      const List<uint64_t> &l = *_f.l;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[_, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
        _stack.emplace_back(_after_len_impl_in_Cons{});
        _stack.emplace_back(_call{crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<_after_len_impl_in_Cons>(_popped));
      _result = (std::move(_result) + 1);
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
List<uint64_t> LoopifyGenerators::build_list_fuel(uint64_t fuel, uint64_t n) {
  // Explicit stack replaces the non-tail recursion of build_list_fuel: _call
  // frames are pending calls, _after frames resume a caller.
  struct _call {
    uint64_t n;
    uint64_t fuel;
  };

  struct _after_build_list_fuel_in_S {
    uint64_t n_;
  };

  using _frame = std::variant<_call, _after_build_list_fuel_in_S>;
  List<uint64_t> _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{n, fuel});
  while (!_stack.empty()) {
    _frame _popped = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
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
            _stack.emplace_back(_after_build_list_fuel_in_S{n_});
            _stack.emplace_back(_call{half, f});
          }
        }
      }
    } else {
      auto _f = std::move(std::get<_after_build_list_fuel_in_S>(_popped));
      uint64_t n_ = _f.n_;
      List<uint64_t> half_result = std::move(_result);
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
  // Builds the result front to back: _write points at the empty tail the next
  // cell fills.
  std::optional<List<uint64_t>> _root{};
  std::shared_ptr<List<uint64_t>> *_write = nullptr;
  const List<uint64_t> *_loop_l = &l;
  uint64_t _loop_n = n;
  while (true) {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l->v())) {
      auto _value = List<uint64_t>::nil();
      (_write ? *(*_write = std::make_shared<List<uint64_t>>(std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename List<uint64_t>::Cons>(_loop_l->v());
      if (_loop_n == UINT64_C(0)) {
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
        _loop_n =
            (((_loop_n - UINT64_C(1)) > _loop_n ? 0 : (_loop_n - UINT64_C(1))));
        continue;
      }
    }
  }
  return std::move(*_root);
}

/// repeat x n creates list with n copies of x.
List<uint64_t> LoopifyGenerators::repeat(uint64_t x, uint64_t n) {
  // Builds the result front to back: _write points at the empty tail the next
  // cell fills.
  std::optional<List<uint64_t>> _root{};
  std::shared_ptr<List<uint64_t>> *_write = nullptr;
  uint64_t _loop_n = n;
  while (true) {
    if (_loop_n <= 0) {
      auto _value = List<uint64_t>::nil();
      (_write ? *(*_write = std::make_shared<List<uint64_t>>(std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      uint64_t m = _loop_n - 1;
      auto _cell = typename List<uint64_t>::Cons(x, nullptr);
      List<uint64_t> &_node =
          (_write ? *(*_write =
                          std::make_shared<List<uint64_t>>(std::move(_cell)))
                  : _root.emplace(std::move(_cell)));
      _write = &std::get<typename List<uint64_t>::Cons>(_node.v_mut()).l;
      _loop_n = m;
      continue;
    }
  }
  return std::move(*_root);
}

/// Helper: replicate single element n times.
List<uint64_t> LoopifyGenerators::replicate_single(uint64_t x, uint64_t n) {
  return repeat(x, n);
}

/// replicate_each n l replicates each element n times: replicate_each 2 1,2 ->
/// 1,1,2,2.
List<uint64_t> LoopifyGenerators::replicate_each(uint64_t n,
                                                 const List<uint64_t> &l) {
  // Explicit stack replaces the non-tail recursion of replicate_each: _call
  // frames are pending calls, _after frames resume a caller.
  struct _call {
    const List<uint64_t> *l;
  };

  struct _after_replicate_each_in_Cons {
    uint64_t a0;
  };

  using _frame = std::variant<_call, _after_replicate_each_in_Cons>;
  List<uint64_t> _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&l});
  while (!_stack.empty()) {
    _frame _popped = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      const List<uint64_t> &l = *_f.l;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
        _result = List<uint64_t>::nil();
      } else {
        const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
        _stack.emplace_back(_after_replicate_each_in_Cons{a0});
        _stack.emplace_back(_call{crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<_after_replicate_each_in_Cons>(_popped));
      uint64_t a0 = _f.a0;
      _result = replicate_single(a0, n).app(std::move(_result));
    }
  }
  return _result;
}
