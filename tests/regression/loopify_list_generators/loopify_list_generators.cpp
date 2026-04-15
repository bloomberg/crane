#include <loopify_list_generators.h>

#include <functional>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

std::shared_ptr<List<unsigned int>> LoopifyListGenerators::cycle_fuel(
    const unsigned int fuel, const unsigned int n,
    const std::shared_ptr<List<unsigned int>> &l) {
  struct _Enter {
    const unsigned int n;
    const unsigned int fuel;
  };

  struct _Call1 {
    const std::shared_ptr<List<unsigned int>> _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::shared_ptr<List<unsigned int>> _result{};
  std::vector<_Frame> _stack;
  _stack.emplace_back(_Enter{n, fuel});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      const auto &_f = std::get<_Enter>(_frame);
      const unsigned int n = _f.n;
      const unsigned int fuel = _f.fuel;
      if (fuel <= 0) {
        _result = List<unsigned int>::nil();
      } else {
        unsigned int fuel_ = fuel - 1;
        if (n <= 0) {
          _result = List<unsigned int>::nil();
        } else {
          unsigned int n_ = n - 1;
          if (std::holds_alternative<typename List<unsigned int>::Nil>(
                  l->v())) {
            _result = List<unsigned int>::nil();
          } else {
            _stack.emplace_back(_Call1{l});
            _stack.emplace_back(_Enter{n_, fuel_});
          }
        }
      }
    } else {
      const auto &_f = std::get<_Call1>(_frame);
      _result = _f._s0->app(_result);
    }
  }
  return _result;
}

std::shared_ptr<List<unsigned int>>
LoopifyListGenerators::cycle(const unsigned int n,
                             const std::shared_ptr<List<unsigned int>> &l) {
  return cycle_fuel((n * l->length()), n, l);
}

std::shared_ptr<List<unsigned int>>
LoopifyListGenerators::range(const unsigned int start,
                             const unsigned int count) {
  std::shared_ptr<List<unsigned int>> _head{};
  std::shared_ptr<List<unsigned int>> _last{};
  unsigned int _loop_count = count;
  unsigned int _loop_start = start;
  bool _continue = true;
  while (_continue) {
    if (_loop_count <= 0) {
      if (_last) {
        std::get<typename List<unsigned int>::Cons>(_last->v_mut()).d_a1 =
            List<unsigned int>::nil();
      } else {
        _head = List<unsigned int>::nil();
      }
      _continue = false;
    } else {
      unsigned int count_ = _loop_count - 1;
      auto _cell = List<unsigned int>::cons(_loop_start, nullptr);
      if (_last) {
        std::get<typename List<unsigned int>::Cons>(_last->v_mut()).d_a1 =
            _cell;
      } else {
        _head = _cell;
      }
      _last = _cell;
      unsigned int _next_count = count_;
      unsigned int _next_start = (_loop_start + 1u);
      _loop_count = std::move(_next_count);
      _loop_start = std::move(_next_start);
      continue;
    }
  }
  return _head;
}

std::shared_ptr<List<unsigned int>>
LoopifyListGenerators::replicate_elem(const unsigned int n,
                                      const unsigned int x) {
  std::shared_ptr<List<unsigned int>> _head{};
  std::shared_ptr<List<unsigned int>> _last{};
  unsigned int _loop_n = n;
  bool _continue = true;
  while (_continue) {
    if (_loop_n <= 0) {
      if (_last) {
        std::get<typename List<unsigned int>::Cons>(_last->v_mut()).d_a1 =
            List<unsigned int>::nil();
      } else {
        _head = List<unsigned int>::nil();
      }
      _continue = false;
    } else {
      unsigned int n_ = _loop_n - 1;
      auto _cell = List<unsigned int>::cons(x, nullptr);
      if (_last) {
        std::get<typename List<unsigned int>::Cons>(_last->v_mut()).d_a1 =
            _cell;
      } else {
        _head = _cell;
      }
      _last = _cell;
      _loop_n = n_;
      continue;
    }
  }
  return _head;
}

std::shared_ptr<List<unsigned int>> LoopifyListGenerators::replicate_each(
    const unsigned int n, const std::shared_ptr<List<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<List<unsigned int>> l;
  };

  struct _Call1 {
    std::shared_ptr<List<unsigned int>> _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::shared_ptr<List<unsigned int>> _result{};
  std::vector<_Frame> _stack;
  _stack.emplace_back(_Enter{l});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      const auto &_f = std::get<_Enter>(_frame);
      const std::shared_ptr<List<unsigned int>> l = _f.l;
      if (std::holds_alternative<typename List<unsigned int>::Nil>(l->v())) {
        _result = List<unsigned int>::nil();
      } else {
        const auto &_m =
            *std::get_if<typename List<unsigned int>::Cons>(&l->v());
        std::shared_ptr<List<unsigned int>> reps = replicate_elem(n, _m.d_a0);
        _stack.emplace_back(_Call1{std::move(reps)});
        _stack.emplace_back(_Enter{_m.d_a1});
      }
    } else {
      const auto &_f = std::get<_Call1>(_frame);
      _result = _f._s0->app(_result);
    }
  }
  return _result;
}

std::shared_ptr<List<std::pair<unsigned int, unsigned int>>>
LoopifyListGenerators::enumerate_aux(
    const unsigned int idx, const std::shared_ptr<List<unsigned int>> &l) {
  std::shared_ptr<List<std::pair<unsigned int, unsigned int>>> _head{};
  std::shared_ptr<List<std::pair<unsigned int, unsigned int>>> _last{};
  std::shared_ptr<List<unsigned int>> _loop_l = l;
  unsigned int _loop_idx = idx;
  bool _continue = true;
  while (_continue) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(
            _loop_l->v())) {
      if (_last) {
        std::get<typename List<std::pair<unsigned int, unsigned int>>::Cons>(
            _last->v_mut())
            .d_a1 = List<std::pair<unsigned int, unsigned int>>::nil();
      } else {
        _head = List<std::pair<unsigned int, unsigned int>>::nil();
      }
      _continue = false;
    } else {
      const auto &_m =
          *std::get_if<typename List<unsigned int>::Cons>(&_loop_l->v());
      auto _cell = List<std::pair<unsigned int, unsigned int>>::cons(
          std::make_pair(_loop_idx, _m.d_a0), nullptr);
      if (_last) {
        std::get<typename List<std::pair<unsigned int, unsigned int>>::Cons>(
            _last->v_mut())
            .d_a1 = _cell;
      } else {
        _head = _cell;
      }
      _last = _cell;
      std::shared_ptr<List<unsigned int>> _next_l = _m.d_a1;
      unsigned int _next_idx = (_loop_idx + 1u);
      _loop_l = std::move(_next_l);
      _loop_idx = std::move(_next_idx);
      continue;
    }
  }
  return _head;
}

std::shared_ptr<List<std::pair<unsigned int, unsigned int>>>
LoopifyListGenerators::enumerate(const std::shared_ptr<List<unsigned int>> &l) {
  return enumerate_aux(0u, l);
}
