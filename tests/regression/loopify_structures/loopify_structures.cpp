#include <loopify_structures.h>

/// Nested and complex data structures.
/// Helper: sum all elements in a list of nested structures.
/// Handles both tree and list levels in one function for full loopification.
unsigned int LoopifyStructures::sum_nested_list_fuel(
    const unsigned int fuel,
    const List<LoopifyStructures::nested>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<LoopifyStructures::nested> *l;
    unsigned int fuel;
  };

  /// _After_NList: saves [d_a00, f], dispatches next recursive call.
  struct _After_NList {
    const List<LoopifyStructures::nested> *d_a00;
    unsigned int f;
  };

  /// _Combine_NList: receives partial results, combines with _result from final
  /// call.
  struct _Combine_NList {
    unsigned int _result;
  };

  /// _Resume_Elem: saves [d_a00], resumes after recursive call with _result.
  struct _Resume_Elem {
    unsigned int d_a00;
  };

  using _Frame =
      std::variant<_Enter, _After_NList, _Combine_NList, _Resume_Elem>;
  unsigned int _result{};
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
      const List<LoopifyStructures::nested> &l = *(_f.l);
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
            _stack.emplace_back(_Resume_Elem{d_a00});
            _stack.emplace_back(_Enter{d_a1.get(), f});
          } else {
            const auto &[d_a00] =
                std::get<typename LoopifyStructures::nested::NList>(d_a0.v());
            _stack.emplace_back(_After_NList{d_a00.get(), f});
            _stack.emplace_back(_Enter{d_a1.get(), f});
          }
        }
      }
    } else if (std::holds_alternative<_After_NList>(_frame)) {
      auto _f = std::move(std::get<_After_NList>(_frame));
      _stack.emplace_back(_Combine_NList{_result});
      _stack.emplace_back(_Enter{_f.d_a00, _f.f});
    } else if (std::holds_alternative<_Combine_NList>(_frame)) {
      auto _f = std::move(std::get<_Combine_NList>(_frame));
      _result = (_result + _f._result);
    } else {
      auto _f = std::move(std::get<_Resume_Elem>(_frame));
      _result = (_f.d_a00 + _result);
    }
  }
  return _result;
}

/// Helper: compute max depth among a list of nested structures.
unsigned int LoopifyStructures::depth_nested_list_fuel(
    const unsigned int fuel, const List<LoopifyStructures::nested> &l) {
  if (fuel <= 0) {
    return 0u;
  } else {
    unsigned int f = fuel - 1;
    if (std::holds_alternative<typename List<LoopifyStructures::nested>::Nil>(
            l.v())) {
      return 0u;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<LoopifyStructures::nested>::Cons>(l.v());
      if (std::holds_alternative<typename LoopifyStructures::nested::Elem>(
              d_a0.v())) {
        unsigned int rest_max = depth_nested_list_fuel(f, *(d_a1));
        if (0u <= rest_max) {
          return rest_max;
        } else {
          return 0u;
        }
      } else {
        const auto &[d_a00] =
            std::get<typename LoopifyStructures::nested::NList>(d_a0.v());
        unsigned int d = (depth_nested_list_fuel(f, *(d_a00)) + 1);
        unsigned int rest_max = depth_nested_list_fuel(f, *(d_a1));
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
List<unsigned int> LoopifyStructures::flatten_nested_list_fuel(
    const unsigned int fuel,
    const List<LoopifyStructures::nested>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<LoopifyStructures::nested> *l;
    unsigned int fuel;
  };

  /// _After_NList: saves [d_a00, f], dispatches next recursive call.
  struct _After_NList {
    const List<LoopifyStructures::nested> *d_a00;
    unsigned int f;
  };

  /// _Combine_NList: receives partial results, combines with _result from final
  /// call.
  struct _Combine_NList {
    List<unsigned int> _result;
  };

  /// _Resume_Elem: saves [d_a00], resumes after recursive call with _result.
  struct _Resume_Elem {
    unsigned int d_a00;
  };

  using _Frame =
      std::variant<_Enter, _After_NList, _Combine_NList, _Resume_Elem>;
  List<unsigned int> _result{};
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
      const List<LoopifyStructures::nested> &l = *(_f.l);
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
            _stack.emplace_back(_Resume_Elem{d_a00});
            _stack.emplace_back(_Enter{d_a1.get(), f});
          } else {
            const auto &[d_a00] =
                std::get<typename LoopifyStructures::nested::NList>(d_a0.v());
            _stack.emplace_back(_After_NList{d_a00.get(), f});
            _stack.emplace_back(_Enter{d_a1.get(), f});
          }
        }
      }
    } else if (std::holds_alternative<_After_NList>(_frame)) {
      auto _f = std::move(std::get<_After_NList>(_frame));
      _stack.emplace_back(_Combine_NList{std::move(_result)});
      _stack.emplace_back(_Enter{_f.d_a00, _f.f});
    } else if (std::holds_alternative<_Combine_NList>(_frame)) {
      auto _f = std::move(std::get<_Combine_NList>(_frame));
      _result = _result.app(_f._result);
    } else {
      auto _f = std::move(std::get<_Resume_Elem>(_frame));
      _result = List<unsigned int>::cons(_f.d_a00, _result);
    }
  }
  return _result;
}

/// find_first_some l finds first Some value in list of options.
std::optional<unsigned int>
LoopifyStructures::find_first_some(const List<std::optional<unsigned int>> &l) {
  std::optional<unsigned int> _result;
  const List<std::optional<unsigned int>> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<typename List<std::optional<unsigned int>>::Nil>(
            _loop_l->v())) {
      _result = std::optional<unsigned int>();
      break;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<std::optional<unsigned int>>::Cons>(
              _loop_l->v());
      if (d_a0.has_value()) {
        const unsigned int &v = *d_a0;
        _result = std::make_optional<unsigned int>(v);
        break;
      } else {
        _loop_l = d_a1.get();
      }
    }
  }
  return _result;
}
