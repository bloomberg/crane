#include "loopify_structures.h"

/// Nested and complex data structures.
/// Helper: sum all elements in a list of nested structures.
/// Handles both tree and list levels in one function for full loopification.
uint64_t LoopifyStructures::sum_nested_list_fuel(
    uint64_t fuel,
    const List<LoopifyStructures::nested>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<LoopifyStructures::nested> *l;
    uint64_t fuel;
  };

  /// _After_NList: saves [a00, f], dispatches next recursive call.
  struct _After_NList {
    const List<LoopifyStructures::nested> *a00;
    uint64_t f;
  };

  /// _Combine_NList: receives partial results, combines with _result from final
  /// call.
  struct _Combine_NList {
    uint64_t _result;
  };

  /// _Resume_Elem: saves [a00], resumes after recursive call with _result.
  struct _Resume_Elem {
    uint64_t a00;
  };

  using _Frame =
      std::variant<_Enter, _After_NList, _Combine_NList, _Resume_Elem>;
  uint64_t _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l, fuel});
  /// Loopified sum_nested_list_fuel: _Enter -> _After_NList -> _Combine_NList
  /// -> _Resume_Elem.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
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
            _stack.emplace_back(_Resume_Elem{a00});
            _stack.emplace_back(_Enter{a1.get(), f});
          } else {
            const auto &[a00] =
                std::get<typename LoopifyStructures::nested::NList>(a0.v());
            _stack.emplace_back(_After_NList{a00.get(), f});
            _stack.emplace_back(_Enter{a1.get(), f});
          }
        }
      }
    } else if (std::holds_alternative<_After_NList>(_frame)) {
      auto _f = std::move(std::get<_After_NList>(_frame));
      _stack.emplace_back(_Combine_NList{_result});
      _stack.emplace_back(_Enter{_f.a00, _f.f});
    } else if (std::holds_alternative<_Combine_NList>(_frame)) {
      auto _f = std::move(std::get<_Combine_NList>(_frame));
      _result = (_result + _f._result);
    } else {
      auto _f = std::move(std::get<_Resume_Elem>(_frame));
      _result = (_f.a00 + _result);
    }
  }
  return _result;
}

/// Helper: compute max depth among a list of nested structures.
uint64_t LoopifyStructures::depth_nested_list_fuel(
    uint64_t fuel, const List<LoopifyStructures::nested> &l) {
  if (fuel <= 0) {
    return UINT64_C(0);
  } else {
    uint64_t f = fuel - 1;
    if (std::holds_alternative<typename List<LoopifyStructures::nested>::Nil>(
            l.v())) {
      return UINT64_C(0);
    } else {
      const auto &[a0, a1] =
          std::get<typename List<LoopifyStructures::nested>::Cons>(l.v());
      if (std::holds_alternative<typename LoopifyStructures::nested::Elem>(
              a0.v())) {
        uint64_t rest_max = depth_nested_list_fuel(f, *a1);
        if (UINT64_C(0) <= rest_max) {
          return rest_max;
        } else {
          return UINT64_C(0);
        }
      } else {
        const auto &[a00] =
            std::get<typename LoopifyStructures::nested::NList>(a0.v());
        uint64_t d = (depth_nested_list_fuel(f, *a00) + 1);
        uint64_t rest_max = depth_nested_list_fuel(f, *a1);
        if (d <= rest_max) {
          return rest_max;
        } else {
          return d;
        }
      }
    }
  }
}

/// Helper: flatten a list of nested structures to a flat list of nats.
List<uint64_t> LoopifyStructures::flatten_nested_list_fuel(
    uint64_t fuel,
    const List<LoopifyStructures::nested>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<LoopifyStructures::nested> *l;
    uint64_t fuel;
  };

  /// _After_NList: saves [a00, f], dispatches next recursive call.
  struct _After_NList {
    const List<LoopifyStructures::nested> *a00;
    uint64_t f;
  };

  /// _Combine_NList: receives partial results, combines with _result from final
  /// call.
  struct _Combine_NList {
    List<uint64_t> _result;
  };

  /// _Resume_Elem: saves [a00], resumes after recursive call with _result.
  struct _Resume_Elem {
    uint64_t a00;
  };

  using _Frame =
      std::variant<_Enter, _After_NList, _Combine_NList, _Resume_Elem>;
  List<uint64_t> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l, fuel});
  /// Loopified flatten_nested_list_fuel: _Enter -> _After_NList ->
  /// _Combine_NList -> _Resume_Elem.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
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
            _stack.emplace_back(_Resume_Elem{a00});
            _stack.emplace_back(_Enter{a1.get(), f});
          } else {
            const auto &[a00] =
                std::get<typename LoopifyStructures::nested::NList>(a0.v());
            _stack.emplace_back(_After_NList{a00.get(), f});
            _stack.emplace_back(_Enter{a1.get(), f});
          }
        }
      }
    } else if (std::holds_alternative<_After_NList>(_frame)) {
      auto _f = std::move(std::get<_After_NList>(_frame));
      _stack.emplace_back(_Combine_NList{std::move(_result)});
      _stack.emplace_back(_Enter{_f.a00, _f.f});
    } else if (std::holds_alternative<_Combine_NList>(_frame)) {
      auto _f = std::move(std::get<_Combine_NList>(_frame));
      _result = _result.app(_f._result);
    } else {
      auto _f = std::move(std::get<_Resume_Elem>(_frame));
      _result = List<uint64_t>::cons(_f.a00, _result);
    }
  }
  return _result;
}

/// find_first_some l finds first Some value in list of options.
std::optional<uint64_t>
LoopifyStructures::find_first_some(const List<std::optional<uint64_t>> &l) {
  std::optional<uint64_t> _result;
  const List<std::optional<uint64_t>> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<typename List<std::optional<uint64_t>>::Nil>(
            _loop_l->v())) {
      _result = std::optional<uint64_t>();
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename List<std::optional<uint64_t>>::Cons>(_loop_l->v());
      if (a0.has_value()) {
        const uint64_t &v = *a0;
        _result = std::make_optional<uint64_t>(v);
        break;
      } else {
        _loop_l = a1.get();
      }
    }
  }
  return _result;
}
