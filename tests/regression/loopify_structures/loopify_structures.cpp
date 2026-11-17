#include "loopify_structures.h"

/// Nested and complex data structures.
/// Helper: sum all elements in a list of nested structures.
/// Handles both tree and list levels in one function for full loopification.
uint64_t LoopifyStructures::sum_nested_list_fuel(
    uint64_t fuel, const List<LoopifyStructures::nested> &l) {
  // Explicit stack replaces the non-tail recursion of sum_nested_list_fuel:
  // _call frames are pending calls, _after frames resume a caller.
  struct _call {
    const List<LoopifyStructures::nested> *l;
    uint64_t fuel;
  };

  struct _after_sum_nested_list_fuel_in_Elem {
    uint64_t a00;
  };

  struct _after_sum_nested_list_fuel_in_NList {
    uint64_t f;
    const List<LoopifyStructures::nested> *a1;
  };

  struct _after_sum_nested_list_fuel_in_NList_2 {
    uint64_t _tmp3;
  };

  using _frame = std::variant<_call, _after_sum_nested_list_fuel_in_Elem,
                              _after_sum_nested_list_fuel_in_NList,
                              _after_sum_nested_list_fuel_in_NList_2>;
  uint64_t _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&l, fuel});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const List<LoopifyStructures::nested> &l = *_f.l;
      uint64_t fuel = _f.fuel;
      if (fuel <= 0) {
        _result = UINT64_C(0);
      } else {
        uint64_t f = fuel - 1;
        if (std::holds_alternative<
                typename List<LoopifyStructures::nested>::Nil>(l.v())) {
          _result = UINT64_C(0);
        } else {
          const auto &[a0, a1] =
              std::get<typename List<LoopifyStructures::nested>::Cons>(l.v());
          if (std::holds_alternative<typename LoopifyStructures::nested::Elem>(
                  a0.v())) {
            const auto &[a00] =
                std::get<typename LoopifyStructures::nested::Elem>(a0.v());
            _stack.emplace_back(_after_sum_nested_list_fuel_in_Elem{a00});
            _stack.emplace_back(_call{crane_raw(a1), f});
          } else {
            const auto &[a00] =
                std::get<typename LoopifyStructures::nested::NList>(a0.v());
            _stack.emplace_back(
                _after_sum_nested_list_fuel_in_NList{f, crane_raw(a1)});
            _stack.emplace_back(_call{crane_raw(a00), f});
          }
        }
      }
    } else if (std::holds_alternative<_after_sum_nested_list_fuel_in_Elem>(
                   _popped)) {
      auto _f =
          std::move(std::get<_after_sum_nested_list_fuel_in_Elem>(_popped));
      _stack.pop_back();
      uint64_t a00 = _f.a00;
      _result = (a00 + std::move(_result));
    } else if (std::holds_alternative<_after_sum_nested_list_fuel_in_NList>(
                   _popped)) {
      auto _f =
          std::move(std::get<_after_sum_nested_list_fuel_in_NList>(_popped));
      _stack.pop_back();
      uint64_t f = _f.f;
      const List<LoopifyStructures::nested> &a1 = *_f.a1;
      _stack.emplace_back(
          _after_sum_nested_list_fuel_in_NList_2{std::move(_result)});
      _stack.emplace_back(_call{&a1, f});
    } else {
      auto _f =
          std::move(std::get<_after_sum_nested_list_fuel_in_NList_2>(_popped));
      _stack.pop_back();
      _result = (_f._tmp3 + std::move(_result));
    }
  }
  return _result;
}

/// Helper: compute max depth among a list of nested structures.
uint64_t LoopifyStructures::depth_nested_list_fuel(
    uint64_t fuel, const List<LoopifyStructures::nested> &l) {
  // Explicit stack replaces the non-tail recursion of depth_nested_list_fuel:
  // _call frames are pending calls, _after frames resume a caller.
  struct _call {
    const List<LoopifyStructures::nested> *l;
    uint64_t fuel;
  };

  struct _after_depth_nested_list_fuel_in_Elem {};

  struct _after_depth_nested_list_fuel_in_NList {
    uint64_t f;
    const List<LoopifyStructures::nested> *a1;
  };

  struct _after_depth_nested_list_fuel_in_NList_2 {
    uint64_t d;
  };

  using _frame = std::variant<_call, _after_depth_nested_list_fuel_in_Elem,
                              _after_depth_nested_list_fuel_in_NList,
                              _after_depth_nested_list_fuel_in_NList_2>;
  uint64_t _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&l, fuel});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const List<LoopifyStructures::nested> &l = *_f.l;
      uint64_t fuel = _f.fuel;
      if (fuel <= 0) {
        _result = UINT64_C(0);
      } else {
        uint64_t f = fuel - 1;
        if (std::holds_alternative<
                typename List<LoopifyStructures::nested>::Nil>(l.v())) {
          _result = UINT64_C(0);
        } else {
          const auto &[a0, a1] =
              std::get<typename List<LoopifyStructures::nested>::Cons>(l.v());
          if (std::holds_alternative<typename LoopifyStructures::nested::Elem>(
                  a0.v())) {
            _stack.emplace_back(_after_depth_nested_list_fuel_in_Elem{});
            _stack.emplace_back(_call{crane_raw(a1), f});
          } else {
            const auto &[a00] =
                std::get<typename LoopifyStructures::nested::NList>(a0.v());
            _stack.emplace_back(
                _after_depth_nested_list_fuel_in_NList{f, crane_raw(a1)});
            _stack.emplace_back(_call{crane_raw(a00), f});
          }
        }
      }
    } else if (std::holds_alternative<_after_depth_nested_list_fuel_in_Elem>(
                   _popped)) {
      auto _f =
          std::move(std::get<_after_depth_nested_list_fuel_in_Elem>(_popped));
      _stack.pop_back();
      uint64_t rest_max = std::move(_result);
      if (UINT64_C(0) <= rest_max) {
        _result = std::move(rest_max);
      } else {
        _result = UINT64_C(0);
      }
    } else if (std::holds_alternative<_after_depth_nested_list_fuel_in_NList>(
                   _popped)) {
      auto _f =
          std::move(std::get<_after_depth_nested_list_fuel_in_NList>(_popped));
      _stack.pop_back();
      uint64_t f = _f.f;
      const List<LoopifyStructures::nested> &a1 = *_f.a1;
      uint64_t d = (std::move(_result) + 1);
      _stack.emplace_back(_after_depth_nested_list_fuel_in_NList_2{d});
      _stack.emplace_back(_call{&a1, f});
    } else {
      auto _f = std::move(
          std::get<_after_depth_nested_list_fuel_in_NList_2>(_popped));
      _stack.pop_back();
      uint64_t d = _f.d;
      uint64_t rest_max = std::move(_result);
      if (d <= rest_max) {
        _result = std::move(rest_max);
      } else {
        _result = std::move(d);
      }
    }
  }
  return _result;
}

/// Helper: flatten a list of nested structures to a flat list of nats.
List<uint64_t> LoopifyStructures::flatten_nested_list_fuel(
    uint64_t fuel, const List<LoopifyStructures::nested> &l) {
  // Explicit stack replaces the non-tail recursion of flatten_nested_list_fuel:
  // _call frames are pending calls, _after frames resume a caller.
  struct _call {
    const List<LoopifyStructures::nested> *l;
    uint64_t fuel;
  };

  struct _after_flatten_nested_list_fuel_in_Elem {
    uint64_t a00;
  };

  struct _after_flatten_nested_list_fuel_in_NList {
    uint64_t f;
    const List<LoopifyStructures::nested> *a1;
  };

  struct _after_flatten_nested_list_fuel_in_NList_2 {
    List<uint64_t> _tmp3;
  };

  using _frame = std::variant<_call, _after_flatten_nested_list_fuel_in_Elem,
                              _after_flatten_nested_list_fuel_in_NList,
                              _after_flatten_nested_list_fuel_in_NList_2>;
  List<uint64_t> _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&l, fuel});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const List<LoopifyStructures::nested> &l = *_f.l;
      uint64_t fuel = _f.fuel;
      if (fuel <= 0) {
        _result = List<uint64_t>::nil();
      } else {
        uint64_t f = fuel - 1;
        if (std::holds_alternative<
                typename List<LoopifyStructures::nested>::Nil>(l.v())) {
          _result = List<uint64_t>::nil();
        } else {
          const auto &[a0, a1] =
              std::get<typename List<LoopifyStructures::nested>::Cons>(l.v());
          if (std::holds_alternative<typename LoopifyStructures::nested::Elem>(
                  a0.v())) {
            const auto &[a00] =
                std::get<typename LoopifyStructures::nested::Elem>(a0.v());
            _stack.emplace_back(_after_flatten_nested_list_fuel_in_Elem{a00});
            _stack.emplace_back(_call{crane_raw(a1), f});
          } else {
            const auto &[a00] =
                std::get<typename LoopifyStructures::nested::NList>(a0.v());
            _stack.emplace_back(
                _after_flatten_nested_list_fuel_in_NList{f, crane_raw(a1)});
            _stack.emplace_back(_call{crane_raw(a00), f});
          }
        }
      }
    } else if (std::holds_alternative<_after_flatten_nested_list_fuel_in_Elem>(
                   _popped)) {
      auto _f =
          std::move(std::get<_after_flatten_nested_list_fuel_in_Elem>(_popped));
      _stack.pop_back();
      uint64_t a00 = _f.a00;
      _result = List<uint64_t>::cons(a00, std::move(_result));
    } else if (std::holds_alternative<_after_flatten_nested_list_fuel_in_NList>(
                   _popped)) {
      auto _f = std::move(
          std::get<_after_flatten_nested_list_fuel_in_NList>(_popped));
      _stack.pop_back();
      uint64_t f = _f.f;
      const List<LoopifyStructures::nested> &a1 = *_f.a1;
      _stack.emplace_back(
          _after_flatten_nested_list_fuel_in_NList_2{std::move(_result)});
      _stack.emplace_back(_call{&a1, f});
    } else {
      auto _f = std::move(
          std::get<_after_flatten_nested_list_fuel_in_NList_2>(_popped));
      _stack.pop_back();
      _result = _f._tmp3.app(std::move(_result));
    }
  }
  return _result;
}

/// find_first_some l finds first Some value in list of options.
std::optional<uint64_t>
LoopifyStructures::find_first_some(const List<std::optional<uint64_t>> &l) {
  // Loop replaces the tail recursion: each recursive call updates the loop
  // variables.
  const List<std::optional<uint64_t>> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<typename List<std::optional<uint64_t>>::Nil>(
            _loop_l->v())) {
      return std::optional<uint64_t>();
    } else {
      const auto &[a0, a1] =
          std::get<typename List<std::optional<uint64_t>>::Cons>(_loop_l->v());
      if (a0.has_value()) {
        const uint64_t &v = *a0;
        return std::make_optional<uint64_t>(v);
      } else {
        _loop_l = crane_raw(a1);
      }
    }
  }
}
