#include <loopify_structures.h>

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

/// Nested and complex data structures.
/// Helper: sum all elements in a list of nested structures.
/// Handles both tree and list levels in one function for full loopification.
__attribute__((pure)) unsigned int LoopifyStructures::sum_nested_list_fuel(
    const unsigned int &fuel, const List<LoopifyStructures::nested> &l) {
  struct _Enter {
    const List<LoopifyStructures::nested> l;
    const unsigned int fuel;
  };

  struct _Call1 {
    unsigned int _s0;
  };

  struct _Call2 {
    decltype(clone_as_value<List<LoopifyStructures::nested>>(
        std::declval<List<std::unique_ptr<LoopifyStructures::nested>> &>()))
        _s0;
    unsigned int _s1;
  };

  struct _Call3 {
    unsigned int _s0;
  };

  using _Frame = std::variant<_Enter, _Call1, _Call2, _Call3>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{l, fuel});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<LoopifyStructures::nested> l = _f.l;
      const unsigned int fuel = _f.fuel;
      if (fuel <= 0) {
        _result = 0u;
      } else {
        unsigned int f = fuel - 1;
        if (std::holds_alternative<
                typename List<LoopifyStructures::nested>::Nil>(l.v())) {
          _result = 0u;
        } else {
          const auto &[d_a0, d_a1] =
              std::get<typename List<LoopifyStructures::nested>::Cons>(l.v());
          if (std::holds_alternative<typename LoopifyStructures::nested::Elem>(
                  d_a0.v())) {
            const auto &[d_a00] =
                std::get<typename LoopifyStructures::nested::Elem>(d_a0.v());
            _stack.emplace_back(_Call1{d_a00});
            _stack.emplace_back(_Enter{*(d_a1), f});
          } else {
            const auto &[d_a00] =
                std::get<typename LoopifyStructures::nested::NList>(d_a0.v());
            _stack.emplace_back(_Call2{
                clone_as_value<List<LoopifyStructures::nested>>(d_a00), f});
            _stack.emplace_back(_Enter{*(d_a1), f});
          }
        }
      }
    } else if (std::holds_alternative<_Call1>(_frame)) {
      auto _f = std::move(std::get<_Call1>(_frame));
      _result = (_f._s0 + _result);
    } else if (std::holds_alternative<_Call2>(_frame)) {
      auto _f = std::move(std::get<_Call2>(_frame));
      _stack.emplace_back(_Call3{_result});
      _stack.emplace_back(_Enter{_f._s0, _f._s1});
    } else {
      auto _f = std::move(std::get<_Call3>(_frame));
      _result = (_result + _f._s0);
    }
  }
  return _result;
}

/// Helper: compute max depth among a list of nested structures.
__attribute__((pure)) unsigned int LoopifyStructures::depth_nested_list_fuel(
    const unsigned int &fuel, const List<LoopifyStructures::nested> &l) {
  struct _Enter {
    const List<LoopifyStructures::nested> l;
    const unsigned int fuel;
  };

  struct _Call1 {};

  struct _Call2 {
    std::unique_ptr<List<LoopifyStructures::nested>> _s0;
    unsigned int _s1;
  };

  struct _Call3 {
    unsigned int _s0;
  };

  using _Frame = std::variant<_Enter, _Call1, _Call2, _Call3>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{l, fuel});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<LoopifyStructures::nested> l = _f.l;
      const unsigned int fuel = _f.fuel;
      if (fuel <= 0) {
        _result = 0u;
      } else {
        unsigned int f = fuel - 1;
        if (std::holds_alternative<
                typename List<LoopifyStructures::nested>::Nil>(l.v())) {
          _result = 0u;
        } else {
          const auto &[d_a0, d_a1] =
              std::get<typename List<LoopifyStructures::nested>::Cons>(l.v());
          if (std::holds_alternative<typename LoopifyStructures::nested::Elem>(
                  d_a0.v())) {
            _stack.emplace_back(_Call1{});
            _stack.emplace_back(_Enter{*(d_a1), f});
          } else {
            const auto &[d_a00] =
                std::get<typename LoopifyStructures::nested::NList>(d_a0.v());
            _stack.emplace_back(
                _Call2{std::make_unique<List<LoopifyStructures::nested>>(
                           d_a1->clone()),
                       f});
            _stack.emplace_back(_Enter{
                clone_as_value<List<LoopifyStructures::nested>>(d_a00), f});
          }
        }
      }
    } else if (std::holds_alternative<_Call1>(_frame)) {
      auto _f = std::move(std::get<_Call1>(_frame));
      unsigned int rest_max = _result;
      if (0u <= rest_max) {
        _result = rest_max;
      } else {
        _result = 0u;
      }
    } else if (std::holds_alternative<_Call2>(_frame)) {
      auto _f = std::move(std::get<_Call2>(_frame));
      std::unique_ptr<List<LoopifyStructures::nested>> d_a1 = std::move(_f._s0);
      unsigned int f = _f._s1;
      unsigned int d = (_result + 1);
      _stack.emplace_back(_Call3{d});
      _stack.emplace_back(_Enter{*(d_a1), f});
    } else {
      auto _f = std::move(std::get<_Call3>(_frame));
      unsigned int d = _f._s0;
      unsigned int rest_max = _result;
      if (d <= rest_max) {
        _result = rest_max;
      } else {
        _result = d;
      }
    }
  }
  return _result;
}

/// Helper: flatten a list of nested structures to a flat list of nats.
__attribute__((pure)) List<unsigned int>
LoopifyStructures::flatten_nested_list_fuel(
    const unsigned int &fuel, const List<LoopifyStructures::nested> &l) {
  struct _Enter {
    const List<LoopifyStructures::nested> l;
    const unsigned int fuel;
  };

  struct _Call1 {
    unsigned int _s0;
  };

  struct _Call2 {
    decltype(clone_as_value<List<LoopifyStructures::nested>>(
        std::declval<List<std::unique_ptr<LoopifyStructures::nested>> &>()))
        _s0;
    unsigned int _s1;
  };

  struct _Call3 {
    List<unsigned int> _s0;
  };

  using _Frame = std::variant<_Enter, _Call1, _Call2, _Call3>;
  List<unsigned int> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{l, fuel});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<LoopifyStructures::nested> l = _f.l;
      const unsigned int fuel = _f.fuel;
      if (fuel <= 0) {
        _result = List<unsigned int>::nil();
      } else {
        unsigned int f = fuel - 1;
        if (std::holds_alternative<
                typename List<LoopifyStructures::nested>::Nil>(l.v())) {
          _result = List<unsigned int>::nil();
        } else {
          const auto &[d_a0, d_a1] =
              std::get<typename List<LoopifyStructures::nested>::Cons>(l.v());
          if (std::holds_alternative<typename LoopifyStructures::nested::Elem>(
                  d_a0.v())) {
            const auto &[d_a00] =
                std::get<typename LoopifyStructures::nested::Elem>(d_a0.v());
            _stack.emplace_back(_Call1{d_a00});
            _stack.emplace_back(_Enter{*(d_a1), f});
          } else {
            const auto &[d_a00] =
                std::get<typename LoopifyStructures::nested::NList>(d_a0.v());
            _stack.emplace_back(_Call2{
                clone_as_value<List<LoopifyStructures::nested>>(d_a00), f});
            _stack.emplace_back(_Enter{*(d_a1), f});
          }
        }
      }
    } else if (std::holds_alternative<_Call1>(_frame)) {
      auto _f = std::move(std::get<_Call1>(_frame));
      _result = List<unsigned int>::cons(_f._s0, _result);
    } else if (std::holds_alternative<_Call2>(_frame)) {
      auto _f = std::move(std::get<_Call2>(_frame));
      _stack.emplace_back(_Call3{_result});
      _stack.emplace_back(_Enter{_f._s0, _f._s1});
    } else {
      auto _f = std::move(std::get<_Call3>(_frame));
      _result = _result.app(_f._s0);
    }
  }
  return _result;
}

/// find_first_some l finds first Some value in list of options.
__attribute__((pure)) std::optional<unsigned int>
LoopifyStructures::find_first_some(const List<std::optional<unsigned int>> &l) {
  std::optional<unsigned int> _result;
  List<std::optional<unsigned int>> _loop_l = l;
  while (true) {
    if (std::holds_alternative<typename List<std::optional<unsigned int>>::Nil>(
            _loop_l.v())) {
      _result = std::optional<unsigned int>();
      break;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<std::optional<unsigned int>>::Cons>(
              _loop_l.v());
      if (d_a0.has_value()) {
        const unsigned int &v = *d_a0;
        _result = std::make_optional<unsigned int>(v);
        break;
      } else {
        _loop_l = *(d_a1);
      }
    }
  }
  return _result;
}
