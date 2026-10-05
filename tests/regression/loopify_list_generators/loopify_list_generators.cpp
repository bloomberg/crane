#include "loopify_list_generators.h"

List<uint64_t> LoopifyListGenerators::cycle_fuel(
    uint64_t fuel, uint64_t n,
    const List<uint64_t> &l) { /// CraneEnter: captures varying parameters for
                               /// each recursive call.

  struct CraneEnter {
    uint64_t n;
    uint64_t fuel;
  };

  /// CraneCont_Cons: resumes after recursive call, then processes rest.
  struct CraneCont_Cons {};

  using CraneFrame = std::variant<CraneEnter, CraneCont_Cons>;
  List<uint64_t> _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{n, fuel});
  /// Loopified cycle_fuel: CraneEnter -> CraneCont_Cons.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
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
            _stack.emplace_back(CraneCont_Cons{});
            _stack.emplace_back(CraneEnter{n_, fuel_});
          }
        }
      }
    } else {
      auto _f = std::move(std::get<CraneCont_Cons>(_frame));
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
  std::optional<List<uint64_t>> _root{};
  std::shared_ptr<List<uint64_t>> *_write = nullptr;
  uint64_t _loop_count = count;
  uint64_t _loop_start = start;
  while (true) {
    if (_loop_count <= 0) {
      auto _value = List<uint64_t>::nil();
      (_write ? *(*_write = std::make_shared<List<uint64_t>>(std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      uint64_t count_ = _loop_count - 1;
      auto _cell = typename List<uint64_t>::Cons(_loop_start, nullptr);
      List<uint64_t> &_node =
          (_write
               ? *(*_write = std::make_shared<List<uint64_t>>(std::move(_cell)))
               : _root.emplace(std::move(_cell)));
      _write = &std::get<typename List<uint64_t>::Cons>(_node.v_mut()).l;
      _loop_count = count_;
      _loop_start = (_loop_start + UINT64_C(1));
      continue;
    }
  }
  return std::move(*_root);
}

List<uint64_t> LoopifyListGenerators::replicate_elem(uint64_t n, uint64_t x) {
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
      uint64_t n_ = _loop_n - 1;
      auto _cell = typename List<uint64_t>::Cons(x, nullptr);
      List<uint64_t> &_node =
          (_write
               ? *(*_write = std::make_shared<List<uint64_t>>(std::move(_cell)))
               : _root.emplace(std::move(_cell)));
      _write = &std::get<typename List<uint64_t>::Cons>(_node.v_mut()).l;
      _loop_n = n_;
      continue;
    }
  }
  return std::move(*_root);
}

List<uint64_t> LoopifyListGenerators::replicate_each(
    uint64_t n,
    const List<uint64_t> &l) { /// CraneEnter: captures varying parameters for
                               /// each recursive call.

  struct CraneEnter {
    const List<uint64_t> *l;
  };

  /// CraneCont_Cons: saves [reps], resumes after recursive call, then processes
  /// rest.
  struct CraneCont_Cons {
    List<uint64_t> reps;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont_Cons>;
  List<uint64_t> _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{&l});
  /// Loopified replicate_each: CraneEnter -> CraneCont_Cons.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      const List<uint64_t> &l = *_f.l;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
        _result = List<uint64_t>::nil();
      } else {
        const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
        List<uint64_t> reps = replicate_elem(n, a0);
        _stack.emplace_back(CraneCont_Cons{std::move(reps)});
        _stack.emplace_back(CraneEnter{crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<CraneCont_Cons>(_frame));
      List<uint64_t> reps = std::move(_f.reps);
      _result = std::move(reps).app(std::move(_result));
    }
  }
  return _result;
}

List<std::pair<uint64_t, uint64_t>>
LoopifyListGenerators::enumerate_aux(uint64_t idx, const List<uint64_t> &l) {
  std::optional<List<std::pair<uint64_t, uint64_t>>> _root{};
  std::shared_ptr<List<std::pair<uint64_t, uint64_t>>> *_write = nullptr;
  const List<uint64_t> *_loop_l = &l;
  uint64_t _loop_idx = idx;
  while (true) {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l->v())) {
      auto _value = List<std::pair<uint64_t, uint64_t>>::nil();
      (_write
           ? *(*_write = std::make_shared<List<std::pair<uint64_t, uint64_t>>>(
                   std::move(_value)))
           : _root.emplace(std::move(_value)));
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename List<uint64_t>::Cons>(_loop_l->v());
      auto _cell = typename List<std::pair<uint64_t, uint64_t>>::Cons(
          std::make_pair(_loop_idx, a0), nullptr);
      List<std::pair<uint64_t, uint64_t>> &_node =
          (_write ? *(*_write =
                          std::make_shared<List<std::pair<uint64_t, uint64_t>>>(
                              std::move(_cell)))
                  : _root.emplace(std::move(_cell)));
      _write = &std::get<typename List<std::pair<uint64_t, uint64_t>>::Cons>(
                    _node.v_mut())
                    .l;
      _loop_l = crane_raw(a1);
      _loop_idx = (_loop_idx + UINT64_C(1));
      continue;
    }
  }
  return std::move(*_root);
}

List<std::pair<uint64_t, uint64_t>>
LoopifyListGenerators::enumerate(const List<uint64_t> &l) {
  return enumerate_aux(UINT64_C(0), l);
}
