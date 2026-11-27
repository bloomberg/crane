#include "loopify_list_generators.h"

List<uint64_t> LoopifyListGenerators::cycle_fuel(uint64_t fuel, uint64_t n,
                                                 const List<uint64_t> &l) {
  // Explicit stack replaces the non-tail recursion of cycle_fuel: _call frames
  // are pending calls, _after frames resume a caller.
  struct _call {
    uint64_t n;
    uint64_t fuel;
  };

  struct _after_cycle_fuel_in_Cons {};

  using _frame = std::variant<_call, _after_cycle_fuel_in_Cons>;
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
        if (n <= 0) {
          _result = List<uint64_t>::nil();
        } else {
          uint64_t n_ = n - 1;
          if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
            _result = List<uint64_t>::nil();
          } else {
            _stack.emplace_back(_after_cycle_fuel_in_Cons{});
            _stack.emplace_back(_call{n_, fuel_});
          }
        }
      }
    } else {
      auto _f = std::move(std::get<_after_cycle_fuel_in_Cons>(_popped));
      _stack.pop_back();
      _result = l.app(std::move(_result));
    }
  }
  return _result;
}

List<uint64_t> LoopifyListGenerators::cycle(uint64_t n,
                                            const List<uint64_t> &l) {
  return cycle_fuel((n * l.length()), n, l);
}

List<uint64_t> LoopifyListGenerators::range(uint64_t start, uint64_t count) {
  // Builds the result front to back: _write points at the empty tail the next
  // cell fills.
  std::optional<List<uint64_t>> _root{};
  std::shared_ptr<List<uint64_t>> *_write = nullptr;
  while (true) {
    if (count <= 0) {
      auto _value = List<uint64_t>::nil();
      (_write ? *(*_write = std::make_shared<List<uint64_t>>(std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      uint64_t count_ = count - 1;
      auto _cell = typename List<uint64_t>::Cons(start, nullptr);
      List<uint64_t> &_node =
          (_write ? *(*_write =
                          std::make_shared<List<uint64_t>>(std::move(_cell)))
                  : _root.emplace(std::move(_cell)));
      _write = &std::get<typename List<uint64_t>::Cons>(_node.v_mut()).l;
      count = count_;
      start = (start + UINT64_C(1));
      continue;
    }
  }
  return std::move(*_root);
}

List<uint64_t> LoopifyListGenerators::replicate_elem(uint64_t n, uint64_t x) {
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

List<uint64_t> LoopifyListGenerators::replicate_each(uint64_t n,
                                                     const List<uint64_t> &l) {
  // Explicit stack replaces the non-tail recursion of replicate_each: _call
  // frames are pending calls, _after frames resume a caller.
  struct _call {
    const List<uint64_t> *l;
  };

  struct _after_replicate_each_in_Cons {
    List<uint64_t> reps;
  };

  using _frame = std::variant<_call, _after_replicate_each_in_Cons>;
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
        List<uint64_t> reps = replicate_elem(n, a0);
        _stack.emplace_back(_after_replicate_each_in_Cons{std::move(reps)});
        _stack.emplace_back(_call{crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<_after_replicate_each_in_Cons>(_popped));
      _stack.pop_back();
      List<uint64_t> reps = std::move(_f.reps);
      _result = reps.app(std::move(_result));
    }
  }
  return _result;
}

List<std::pair<uint64_t, uint64_t>>
LoopifyListGenerators::enumerate_aux(uint64_t idx, const List<uint64_t> &l) {
  // Builds the result front to back: _write points at the empty tail the next
  // cell fills.
  std::optional<List<std::pair<uint64_t, uint64_t>>> _root{};
  std::shared_ptr<List<std::pair<uint64_t, uint64_t>>> *_write = nullptr;
  const List<uint64_t> *_loop_l = &l;
  while (true) {
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
      auto _cell = typename List<std::pair<uint64_t, uint64_t>>::Cons(
          std::make_pair(idx, a0), nullptr);
      List<std::pair<uint64_t, uint64_t>> &_node = (
          _write ? *(*_write =
                         std::make_shared<List<std::pair<uint64_t, uint64_t>>>(
                             std::move(_cell)))
                 : _root.emplace(std::move(_cell)));
      _write =
          &std::get<typename List<std::pair<uint64_t, uint64_t>>::Cons>(
              _node.v_mut())
              .l;
      _loop_l = crane_raw(a1);
      idx = (idx + UINT64_C(1));
      continue;
    }
  }
  return std::move(*_root);
}

List<std::pair<uint64_t, uint64_t>>
LoopifyListGenerators::enumerate(const List<uint64_t> &l) {
  return enumerate_aux(UINT64_C(0), l);
}
