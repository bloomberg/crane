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

  /// _Cont_Elem: saves [a00], resumes after recursive call, then processes
  /// rest.
  struct _Cont_Elem {
    uint64_t a00;
  };

  /// _Cont_NList: saves [a1, f], resumes after recursive call, then processes
  /// rest.
  struct _Cont_NList {
    const List<LoopifyStructures::nested> *a1;
    uint64_t f;
  };

  /// _Cont_NList_1: saves [r_], resumes after recursive call, then processes
  /// rest.
  struct _Cont_NList_1 {
    uint64_t r_;
  };

  using _Frame = std::variant<_Enter, _Cont_Elem, _Cont_NList, _Cont_NList_1>;
  uint64_t _result{};
  crane::small_vector<_Frame> _stack;
  _stack.emplace_back(_Enter{&l, fuel});
  /// Loopified sum_nested_list_fuel: _Enter -> _Cont_Elem -> _Cont_NList ->
  /// _Cont_NList_1.
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
            _stack.emplace_back(_Cont_Elem{a00});
            _stack.emplace_back(_Enter{crane_raw(a1), f});
          } else {
            const auto &[a00] =
                std::get<typename LoopifyStructures::nested::NList>(a0.v());
            _stack.emplace_back(_Cont_NList{crane_raw(a1), f});
            _stack.emplace_back(_Enter{crane_raw(a00), f});
          }
        }
      }
    } else if (std::holds_alternative<_Cont_Elem>(_frame)) {
      auto _f = std::move(std::get<_Cont_Elem>(_frame));
      uint64_t a00 = _f.a00;
      uint64_t r_ = std::move(_result);
      _result = (a00 + r_);
    } else if (std::holds_alternative<_Cont_NList>(_frame)) {
      auto _f = std::move(std::get<_Cont_NList>(_frame));
      const List<LoopifyStructures::nested> &a1 = *_f.a1;
      uint64_t f = _f.f;
      uint64_t r_ = std::move(_result);
      _stack.emplace_back(_Cont_NList_1{r_});
      _stack.emplace_back(_Enter{&a1, f});
    } else {
      auto _f = std::move(std::get<_Cont_NList_1>(_frame));
      uint64_t r_ = _f.r_;
      uint64_t r_0 = std::move(_result);
      _result = (r_ + r_0);
    }
  }
  return _result;
}

/// Helper: compute max depth among a list of nested structures.
uint64_t LoopifyStructures::depth_nested_list_fuel(
    uint64_t fuel,
    const List<LoopifyStructures::nested>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<LoopifyStructures::nested> *l;
    uint64_t fuel;
  };

  /// _Cont_Elem: resumes after recursive call, then processes rest.
  struct _Cont_Elem {};

  /// _Cont_NList: saves [a1, f], resumes after recursive call, then processes
  /// rest.
  struct _Cont_NList {
    const List<LoopifyStructures::nested> *a1;
    uint64_t f;
  };

  /// _Cont_NList_1: saves [d], resumes after recursive call, then processes
  /// rest.
  struct _Cont_NList_1 {
    uint64_t d;
  };

  using _Frame = std::variant<_Enter, _Cont_Elem, _Cont_NList, _Cont_NList_1>;
  uint64_t _result{};
  crane::small_vector<_Frame> _stack;
  _stack.emplace_back(_Enter{&l, fuel});
  /// Loopified depth_nested_list_fuel: _Enter -> _Cont_Elem -> _Cont_NList ->
  /// _Cont_NList_1.
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
            _stack.emplace_back(_Cont_Elem{});
            _stack.emplace_back(_Enter{crane_raw(a1), f});
          } else {
            const auto &[a00] =
                std::get<typename LoopifyStructures::nested::NList>(a0.v());
            _stack.emplace_back(_Cont_NList{crane_raw(a1), f});
            _stack.emplace_back(_Enter{crane_raw(a00), f});
          }
        }
      }
    } else if (std::holds_alternative<_Cont_Elem>(_frame)) {
      auto _f = std::move(std::get<_Cont_Elem>(_frame));
      uint64_t rest_max = std::move(_result);
      if (UINT64_C(0) <= rest_max) {
        _result = std::move(rest_max);
      } else {
        _result = UINT64_C(0);
      }
    } else if (std::holds_alternative<_Cont_NList>(_frame)) {
      auto _f = std::move(std::get<_Cont_NList>(_frame));
      const List<LoopifyStructures::nested> &a1 = *_f.a1;
      uint64_t f = _f.f;
      uint64_t d = (std::move(_result) + 1);
      _stack.emplace_back(_Cont_NList_1{d});
      _stack.emplace_back(_Enter{&a1, f});
    } else {
      auto _f = std::move(std::get<_Cont_NList_1>(_frame));
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
    uint64_t fuel,
    const List<LoopifyStructures::nested>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<LoopifyStructures::nested> *l;
    uint64_t fuel;
  };

  /// _Cont_NList: saves [a1, f], resumes after recursive call, then processes
  /// rest.
  struct _Cont_NList {
    const List<LoopifyStructures::nested> *a1;
    uint64_t f;
  };

  /// _Cont_NList_1: saves [r_], resumes after recursive call, then processes
  /// rest.
  struct _Cont_NList_1 {
    List<uint64_t> r_;
  };

  /// _Resume_Elem: saves [a00], resumes after recursive call with _result.
  struct _Resume_Elem {
    uint64_t a00;
  };

  using _Frame = std::variant<_Enter, _Cont_NList, _Cont_NList_1, _Resume_Elem>;
  List<uint64_t> _result{};
  crane::small_vector<_Frame> _stack;
  _stack.emplace_back(_Enter{&l, fuel});
  /// Loopified flatten_nested_list_fuel: _Enter -> _Cont_NList -> _Cont_NList_1
  /// -> _Resume_Elem.
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
            _stack.emplace_back(_Enter{crane_raw(a1), f});
          } else {
            const auto &[a00] =
                std::get<typename LoopifyStructures::nested::NList>(a0.v());
            _stack.emplace_back(_Cont_NList{crane_raw(a1), f});
            _stack.emplace_back(_Enter{crane_raw(a00), f});
          }
        }
      }
    } else if (std::holds_alternative<_Cont_NList>(_frame)) {
      auto _f = std::move(std::get<_Cont_NList>(_frame));
      const List<LoopifyStructures::nested> &a1 = *_f.a1;
      uint64_t f = _f.f;
      List<uint64_t> r_ = std::move(_result);
      _stack.emplace_back(_Cont_NList_1{std::move(r_)});
      _stack.emplace_back(_Enter{&a1, f});
    } else if (std::holds_alternative<_Cont_NList_1>(_frame)) {
      auto _f = std::move(std::get<_Cont_NList_1>(_frame));
      List<uint64_t> r_ = std::move(_f.r_);
      List<uint64_t> r_0 = std::move(_result);
      _result = std::move(r_).app(std::move(r_0));
    } else {
      auto _f = std::move(std::get<_Resume_Elem>(_frame));
      _result = List<uint64_t>::cons(_f.a00, std::move(_result));
    }
  }
  return _result;
}

/// find_first_some l finds first Some value in list of options.
std::optional<uint64_t>
LoopifyStructures::find_first_some(const List<std::optional<uint64_t>> &l) {
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
