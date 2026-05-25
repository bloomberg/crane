#include "loopify_multi_recursion.h"

uint64_t LoopifyMultiRecursion::mixed_arith_fuel(
    uint64_t fuel,
    uint64_t
        n) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    uint64_t n;
    uint64_t fuel;
  };

  /// _After1: saves [_s0, fuel__0, _s2, fuel__1], dispatches next recursive
  /// call.
  struct _After1 {
    uint64_t _s0;
    uint64_t fuel__0;
    uint64_t _s2;
    uint64_t fuel__1;
  };

  /// _After2: saves [_result, _s1, fuel_], dispatches next recursive call.
  struct _After2 {
    uint64_t _result;
    uint64_t _s1;
    uint64_t fuel_;
  };

  /// _Combine3: receives partial results, combines with _result from final
  /// call.
  struct _Combine3 {
    uint64_t _result_0;
    uint64_t _result_1;
  };

  using _Frame = std::variant<_Enter, _After1, _After2, _Combine3>;
  uint64_t _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{n, fuel});
  /// Loopified mixed_arith_fuel: _Enter -> _After1 -> _After2 -> _Combine3.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      uint64_t n = _f.n;
      uint64_t fuel = _f.fuel;
      if (fuel <= 0) {
        _result = UINT64_C(1);
      } else {
        uint64_t fuel_ = fuel - 1;
        if (n <= UINT64_C(0)) {
          _result = UINT64_C(1);
        } else {
          if (n == UINT64_C(1)) {
            _result = UINT64_C(1);
          } else {
            if (n == UINT64_C(2)) {
              _result = UINT64_C(1);
            } else {
              _stack.emplace_back(_After1{
                  (((n - UINT64_C(2)) > n ? 0 : (n - UINT64_C(2)))), fuel_,
                  (((n - UINT64_C(1)) > n ? 0 : (n - UINT64_C(1)))), fuel_});
              _stack.emplace_back(_Enter{
                  (((n - UINT64_C(3)) > n ? 0 : (n - UINT64_C(3)))), fuel_});
            }
          }
        }
      }
    } else if (std::holds_alternative<_After1>(_frame)) {
      auto _f = std::move(std::get<_After1>(_frame));
      _stack.emplace_back(_After2{_result, _f._s2, _f.fuel__1});
      _stack.emplace_back(_Enter{_f._s0, _f.fuel__0});
    } else if (std::holds_alternative<_After2>(_frame)) {
      auto _f = std::move(std::get<_After2>(_frame));
      _stack.emplace_back(_Combine3{_f._result, _result});
      _stack.emplace_back(_Enter{_f._s1, _f.fuel_});
    } else {
      auto _f = std::move(std::get<_Combine3>(_frame));
      _result = ((_result * _f._result_1) + _f._result_0);
    }
  }
  return _result;
}

uint64_t LoopifyMultiRecursion::mixed_arith(uint64_t n) {
  return mixed_arith_fuel((n * UINT64_C(3)), n);
}

bool LoopifyMultiRecursion::bool_or_chain_fuel(
    uint64_t fuel, uint64_t n,
    uint64_t target) { /// _Enter: captures varying parameters for each
                       /// recursive call.

  struct _Enter {
    uint64_t n;
    uint64_t fuel;
  };

  /// _After2: saves [_s0, fuel_, _s2], dispatches next recursive call.
  struct _After2 {
    std::decay_t<decltype((
        ((std::declval<uint64_t &>() - UINT64_C(1)) > std::declval<uint64_t &>()
             ? 0
             : (std::declval<uint64_t &>() - UINT64_C(1)))))>
        _s0;
    uint64_t fuel_;
    std::decay_t<decltype(std::declval<uint64_t &>() ==
                          std::declval<uint64_t &>())>
        _s2;
  };

  /// _Combine1: receives partial results, combines with _result from final
  /// call.
  struct _Combine1 {
    bool _result;
    std::decay_t<decltype(std::declval<uint64_t &>() ==
                          std::declval<uint64_t &>())>
        _s1;
  };

  using _Frame = std::variant<_Enter, _After2, _Combine1>;
  bool _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{n, fuel});
  /// Loopified bool_or_chain_fuel: _Enter -> _After2 -> _Combine1.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      uint64_t n = _f.n;
      uint64_t fuel = _f.fuel;
      if (fuel <= 0) {
        _result = false;
      } else {
        uint64_t fuel_ = fuel - 1;
        if (n <= UINT64_C(0)) {
          _result = false;
        } else {
          _stack.emplace_back(
              _After2{(((n - UINT64_C(1)) > n ? 0 : (n - UINT64_C(1)))), fuel_,
                      n == target});
          _stack.emplace_back(
              _Enter{(((n - UINT64_C(2)) > n ? 0 : (n - UINT64_C(2)))), fuel_});
        }
      }
    } else if (std::holds_alternative<_After2>(_frame)) {
      auto _f = std::move(std::get<_After2>(_frame));
      _stack.emplace_back(_Combine1{_result, _f._s2});
      _stack.emplace_back(_Enter{_f._s0, _f.fuel_});
    } else {
      auto _f = std::move(std::get<_Combine1>(_frame));
      _result = ((_f._s1 || std::move(_result)) || std::move(_f._result));
    }
  }
  return _result;
}

uint64_t LoopifyMultiRecursion::bool_or_chain(uint64_t n, uint64_t target) {
  if (bool_or_chain_fuel((n * UINT64_C(2)), n, target)) {
    return UINT64_C(1);
  } else {
    return UINT64_C(0);
  }
}

bool LoopifyMultiRecursion::bool_and_chain_fuel(
    uint64_t fuel,
    uint64_t
        n) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    uint64_t n;
    uint64_t fuel;
  };

  /// _After2: saves [_s0, fuel_], dispatches next recursive call.
  struct _After2 {
    std::decay_t<decltype((
        ((std::declval<uint64_t &>() - UINT64_C(1)) > std::declval<uint64_t &>()
             ? 0
             : (std::declval<uint64_t &>() - UINT64_C(1)))))>
        _s0;
    uint64_t fuel_;
  };

  /// _Combine1: receives partial results, combines with _result from final
  /// call.
  struct _Combine1 {
    bool _result;
  };

  using _Frame = std::variant<_Enter, _After2, _Combine1>;
  bool _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{n, fuel});
  /// Loopified bool_and_chain_fuel: _Enter -> _After2 -> _Combine1.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      uint64_t n = _f.n;
      uint64_t fuel = _f.fuel;
      if (fuel <= 0) {
        _result = true;
      } else {
        uint64_t fuel_ = fuel - 1;
        if (n <= UINT64_C(2)) {
          _result = true;
        } else {
          _stack.emplace_back(_After2{
              (((n - UINT64_C(1)) > n ? 0 : (n - UINT64_C(1)))), fuel_});
          _stack.emplace_back(
              _Enter{(((n - UINT64_C(2)) > n ? 0 : (n - UINT64_C(2)))), fuel_});
        }
      }
    } else if (std::holds_alternative<_After2>(_frame)) {
      auto _f = std::move(std::get<_After2>(_frame));
      _stack.emplace_back(_Combine1{_result});
      _stack.emplace_back(_Enter{_f._s0, _f.fuel_});
    } else {
      auto _f = std::move(std::get<_Combine1>(_frame));
      _result = (std::move(_result) && std::move(_f._result));
    }
  }
  return _result;
}

uint64_t LoopifyMultiRecursion::bool_and_chain(uint64_t n) {
  if (bool_and_chain_fuel((n * UINT64_C(2)), n)) {
    return UINT64_C(1);
  } else {
    return UINT64_C(0);
  }
}

uint64_t LoopifyMultiRecursion::quad_count_leaves(
    const LoopifyMultiRecursion::quadtree
        &t) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const LoopifyMultiRecursion::quadtree *t;
  };

  /// _After_QQuad: saves [a2, a1, a0], dispatches next recursive call.
  struct _After_QQuad {
    const LoopifyMultiRecursion::quadtree *a2;
    const LoopifyMultiRecursion::quadtree *a1;
    const LoopifyMultiRecursion::quadtree *a0;
  };

  /// _After_QQuad_1: saves [_result, a1, a0], dispatches next recursive call.
  struct _After_QQuad_1 {
    uint64_t _result;
    const LoopifyMultiRecursion::quadtree *a1;
    const LoopifyMultiRecursion::quadtree *a0;
  };

  /// _After_QQuad_2: saves [_result_0, _result_1, a0], dispatches next
  /// recursive call.
  struct _After_QQuad_2 {
    uint64_t _result_0;
    uint64_t _result_1;
    const LoopifyMultiRecursion::quadtree *a0;
  };

  /// _Combine_QQuad: receives partial results, combines with _result from final
  /// call.
  struct _Combine_QQuad {
    uint64_t _result_0;
    uint64_t _result_1;
    uint64_t _result_2;
  };

  using _Frame = std::variant<_Enter, _After_QQuad, _After_QQuad_1,
                              _After_QQuad_2, _Combine_QQuad>;
  uint64_t _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&t});
  /// Loopified quad_count_leaves: _Enter -> _After_QQuad -> _After_QQuad_1 ->
  /// _After_QQuad_2 -> _Combine_QQuad.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const LoopifyMultiRecursion::quadtree &t = *_f.t;
      if (std::holds_alternative<
              typename LoopifyMultiRecursion::quadtree::QLeaf>(t.v())) {
        _result = UINT64_C(1);
      } else {
        const auto &[a0, a1, a2, a3] =
            std::get<typename LoopifyMultiRecursion::quadtree::QQuad>(t.v());
        _stack.emplace_back(_After_QQuad{a2.get(), a1.get(), a0.get()});
        _stack.emplace_back(_Enter{a3.get()});
      }
    } else if (std::holds_alternative<_After_QQuad>(_frame)) {
      auto _f = std::move(std::get<_After_QQuad>(_frame));
      _stack.emplace_back(_After_QQuad_1{_result, _f.a1, _f.a0});
      _stack.emplace_back(_Enter{_f.a2});
    } else if (std::holds_alternative<_After_QQuad_1>(_frame)) {
      auto _f = std::move(std::get<_After_QQuad_1>(_frame));
      _stack.emplace_back(_After_QQuad_2{_f._result, _result, _f.a0});
      _stack.emplace_back(_Enter{_f.a1});
    } else if (std::holds_alternative<_After_QQuad_2>(_frame)) {
      auto _f = std::move(std::get<_After_QQuad_2>(_frame));
      _stack.emplace_back(_Combine_QQuad{_f._result_0, _f._result_1, _result});
      _stack.emplace_back(_Enter{_f.a0});
    } else {
      auto _f = std::move(std::get<_Combine_QQuad>(_frame));
      _result = (((_result + _f._result_2) + _f._result_1) + _f._result_0);
    }
  }
  return _result;
}

uint64_t LoopifyMultiRecursion::quad_depth(
    const LoopifyMultiRecursion::quadtree
        &t) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const LoopifyMultiRecursion::quadtree *t;
  };

  /// _After_QQuad: saves [a2, a1, a0, _s3], dispatches next recursive call.
  struct _After_QQuad {
    const LoopifyMultiRecursion::quadtree *a2;
    const LoopifyMultiRecursion::quadtree *a1;
    const LoopifyMultiRecursion::quadtree *a0;
    std::decay_t<decltype(UINT64_C(1))> _s3;
  };

  /// _After_QQuad_1: saves [_result, a1, a0, _s3], dispatches next recursive
  /// call.
  struct _After_QQuad_1 {
    uint64_t _result;
    const LoopifyMultiRecursion::quadtree *a1;
    const LoopifyMultiRecursion::quadtree *a0;
    std::decay_t<decltype(UINT64_C(1))> _s3;
  };

  /// _After_QQuad_2: saves [_result_0, _result_1, a0, _s3], dispatches next
  /// recursive call.
  struct _After_QQuad_2 {
    uint64_t _result_0;
    uint64_t _result_1;
    const LoopifyMultiRecursion::quadtree *a0;
    std::decay_t<decltype(UINT64_C(1))> _s3;
  };

  /// _Combine_QQuad: receives partial results, combines with _result from final
  /// call.
  struct _Combine_QQuad {
    uint64_t _result_0;
    uint64_t _result_1;
    uint64_t _result_2;
    std::decay_t<decltype(UINT64_C(1))> _s3;
  };

  using _Frame = std::variant<_Enter, _After_QQuad, _After_QQuad_1,
                              _After_QQuad_2, _Combine_QQuad>;
  uint64_t _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&t});
  /// Loopified quad_depth: _Enter -> _After_QQuad -> _After_QQuad_1 ->
  /// _After_QQuad_2 -> _Combine_QQuad.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const LoopifyMultiRecursion::quadtree &t = *_f.t;
      if (std::holds_alternative<
              typename LoopifyMultiRecursion::quadtree::QLeaf>(t.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1, a2, a3] =
            std::get<typename LoopifyMultiRecursion::quadtree::QQuad>(t.v());
        _stack.emplace_back(
            _After_QQuad{a2.get(), a1.get(), a0.get(), UINT64_C(1)});
        _stack.emplace_back(_Enter{a3.get()});
      }
    } else if (std::holds_alternative<_After_QQuad>(_frame)) {
      auto _f = std::move(std::get<_After_QQuad>(_frame));
      _stack.emplace_back(_After_QQuad_1{_result, _f.a1, _f.a0, _f._s3});
      _stack.emplace_back(_Enter{_f.a2});
    } else if (std::holds_alternative<_After_QQuad_1>(_frame)) {
      auto _f = std::move(std::get<_After_QQuad_1>(_frame));
      _stack.emplace_back(_After_QQuad_2{_f._result, _result, _f.a0, _f._s3});
      _stack.emplace_back(_Enter{_f.a1});
    } else if (std::holds_alternative<_After_QQuad_2>(_frame)) {
      auto _f = std::move(std::get<_After_QQuad_2>(_frame));
      _stack.emplace_back(
          _Combine_QQuad{_f._result_0, _f._result_1, _result, _f._s3});
      _stack.emplace_back(_Enter{_f.a0});
    } else {
      auto _f = std::move(std::get<_Combine_QQuad>(_frame));
      _result = (_f._s3 + std::max(std::max(_result, _f._result_2),
                                   std::max(_f._result_1, _f._result_0)));
    }
  }
  return _result;
}

uint64_t LoopifyMultiRecursion::hofstadter_q_fuel(
    uint64_t fuel,
    uint64_t
        n) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    uint64_t n;
    uint64_t fuel;
  };

  /// _After4: saves [_s0, fuel_], dispatches next recursive call.
  struct _After4 {
    std::decay_t<decltype((
        ((std::declval<uint64_t &>() - std::declval<uint64_t &>()) >
                 std::declval<uint64_t &>()
             ? 0
             : (std::declval<uint64_t &>() - std::declval<uint64_t &>()))))>
        _s0;
    uint64_t fuel_;
  };

  /// _Combine3: receives partial results, combines with _result from final
  /// call.
  struct _Combine3 {
    uint64_t _result;
  };

  /// _Cont1: saves [fuel_, n], resumes after recursive call, then processes
  /// rest.
  struct _Cont1 {
    uint64_t fuel_;
    uint64_t n;
  };

  /// _Cont2: saves [fuel_, n, q1], resumes after recursive call, then processes
  /// rest.
  struct _Cont2 {
    uint64_t fuel_;
    uint64_t n;
    uint64_t q1;
  };

  using _Frame = std::variant<_Enter, _After4, _Combine3, _Cont1, _Cont2>;
  uint64_t _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{n, fuel});
  /// Loopified hofstadter_q_fuel: _Enter -> _After4 -> _Combine3 -> _Cont1 ->
  /// _Cont2.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      uint64_t n = _f.n;
      uint64_t fuel = _f.fuel;
      if (fuel <= 0) {
        _result = UINT64_C(1);
      } else {
        uint64_t fuel_ = fuel - 1;
        if (n <= UINT64_C(0)) {
          _result = UINT64_C(0);
        } else {
          if (n == UINT64_C(1)) {
            _result = UINT64_C(1);
          } else {
            if (n == UINT64_C(2)) {
              _result = UINT64_C(1);
            } else {
              _stack.emplace_back(_Cont1{fuel_, n});
              _stack.emplace_back(_Enter{
                  (((n - UINT64_C(1)) > n ? 0 : (n - UINT64_C(1)))), fuel_});
            }
          }
        }
      }
    } else if (std::holds_alternative<_After4>(_frame)) {
      auto _f = std::move(std::get<_After4>(_frame));
      _stack.emplace_back(_Combine3{_result});
      _stack.emplace_back(_Enter{_f._s0, _f.fuel_});
    } else if (std::holds_alternative<_Combine3>(_frame)) {
      auto _f = std::move(std::get<_Combine3>(_frame));
      _result = (std::move(_result) + std::move(_f._result));
    } else if (std::holds_alternative<_Cont1>(_frame)) {
      auto _f = std::move(std::get<_Cont1>(_frame));
      uint64_t fuel_ = _f.fuel_;
      uint64_t n = _f.n;
      uint64_t q1 = _result;
      _stack.emplace_back(_Cont2{fuel_, n, q1});
      _stack.emplace_back(
          _Enter{(((n - UINT64_C(2)) > n ? 0 : (n - UINT64_C(2)))), fuel_});
    } else {
      auto _f = std::move(std::get<_Cont2>(_frame));
      uint64_t fuel_ = _f.fuel_;
      uint64_t n = _f.n;
      uint64_t q1 = _f.q1;
      uint64_t q2 = _result;
      _stack.emplace_back(_After4{(((n - q1) > n ? 0 : (n - q1))), fuel_});
      _stack.emplace_back(_Enter{(((n - q2) > n ? 0 : (n - q2))), fuel_});
    }
  }
  return _result;
}

uint64_t LoopifyMultiRecursion::hofstadter_q(uint64_t n) {
  return hofstadter_q_fuel(((n * n) + UINT64_C(1)), n);
}
