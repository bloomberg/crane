#include <loopify_multi_recursion.h>

unsigned int LoopifyMultiRecursion::mixed_arith_fuel(
    const unsigned int fuel,
    const unsigned int
        n) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    unsigned int n;
    unsigned int fuel;
  };

  /// _After1: saves [_s0, fuel__0, _s2, fuel__1], dispatches next recursive
  /// call.
  struct _After1 {
    unsigned int _s0;
    unsigned int fuel__0;
    unsigned int _s2;
    unsigned int fuel__1;
  };

  /// _After2: saves [_result, _s1, fuel_], dispatches next recursive call.
  struct _After2 {
    unsigned int _result;
    unsigned int _s1;
    unsigned int fuel_;
  };

  /// _Combine3: receives partial results, combines with _result from final
  /// call.
  struct _Combine3 {
    unsigned int _result_0;
    unsigned int _result_1;
  };

  using _Frame = std::variant<_Enter, _After1, _After2, _Combine3>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{n, fuel});
  /// Loopified mixed_arith_fuel: _Enter -> _After1 -> _After2 -> _Combine3.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const unsigned int n = _f.n;
      const unsigned int fuel = _f.fuel;
      if (fuel <= 0) {
        _result = 1u;
      } else {
        unsigned int fuel_ = fuel - 1;
        if (n <= 0u) {
          _result = 1u;
        } else {
          if (n == 1u) {
            _result = 1u;
          } else {
            if (n == 2u) {
              _result = 1u;
            } else {
              _stack.emplace_back(
                  _After1{(((n - 2u) > n ? 0 : (n - 2u))), fuel_,
                          (((n - 1u) > n ? 0 : (n - 1u))), fuel_});
              _stack.emplace_back(
                  _Enter{(((n - 3u) > n ? 0 : (n - 3u))), fuel_});
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

unsigned int LoopifyMultiRecursion::mixed_arith(const unsigned int n) {
  return mixed_arith_fuel((n * 3u), n);
}

bool LoopifyMultiRecursion::bool_or_chain_fuel(
    const unsigned int fuel, const unsigned int n,
    const unsigned int target) { /// _Enter: captures varying parameters for
                                 /// each recursive call.

  struct _Enter {
    unsigned int n;
    unsigned int fuel;
  };

  /// _After2: saves [_s0, fuel_, _s2], dispatches next recursive call.
  struct _After2 {
    decltype((((std::declval<const unsigned int &>() - 1u) >
                       std::declval<const unsigned int &>()
                   ? 0
                   : (std::declval<const unsigned int &>() - 1u)))) _s0;
    unsigned int fuel_;
    decltype(std::declval<const unsigned int &>() ==
             std::declval<const unsigned int &>()) _s2;
  };

  /// _Combine1: receives partial results, combines with _result from final
  /// call.
  struct _Combine1 {
    bool _result;
    decltype(std::declval<const unsigned int &>() ==
             std::declval<const unsigned int &>()) _s1;
  };

  using _Frame = std::variant<_Enter, _After2, _Combine1>;
  bool _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{n, fuel});
  /// Loopified bool_or_chain_fuel: _Enter -> _After2 -> _Combine1.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const unsigned int n = _f.n;
      const unsigned int fuel = _f.fuel;
      if (fuel <= 0) {
        _result = false;
      } else {
        unsigned int fuel_ = fuel - 1;
        if (n <= 0u) {
          _result = false;
        } else {
          _stack.emplace_back(
              _After2{(((n - 1u) > n ? 0 : (n - 1u))), fuel_, n == target});
          _stack.emplace_back(_Enter{(((n - 2u) > n ? 0 : (n - 2u))), fuel_});
        }
      }
    } else if (std::holds_alternative<_After2>(_frame)) {
      auto _f = std::move(std::get<_After2>(_frame));
      _stack.emplace_back(_Combine1{_result, _f._s2});
      _stack.emplace_back(_Enter{_f._s0, _f.fuel_});
    } else {
      auto _f = std::move(std::get<_Combine1>(_frame));
      _result = ((_f._s1 || _result) || _f._result);
    }
  }
  return _result;
}

unsigned int LoopifyMultiRecursion::bool_or_chain(const unsigned int n,
                                                  const unsigned int target) {
  if (bool_or_chain_fuel((n * 2u), n, target)) {
    return 1u;
  } else {
    return 0u;
  }
}

bool LoopifyMultiRecursion::bool_and_chain_fuel(
    const unsigned int fuel,
    const unsigned int
        n) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    unsigned int n;
    unsigned int fuel;
  };

  /// _After2: saves [_s0, fuel_], dispatches next recursive call.
  struct _After2 {
    decltype((((std::declval<const unsigned int &>() - 1u) >
                       std::declval<const unsigned int &>()
                   ? 0
                   : (std::declval<const unsigned int &>() - 1u)))) _s0;
    unsigned int fuel_;
  };

  /// _Combine1: receives partial results, combines with _result from final
  /// call.
  struct _Combine1 {
    bool _result;
  };

  using _Frame = std::variant<_Enter, _After2, _Combine1>;
  bool _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{n, fuel});
  /// Loopified bool_and_chain_fuel: _Enter -> _After2 -> _Combine1.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const unsigned int n = _f.n;
      const unsigned int fuel = _f.fuel;
      if (fuel <= 0) {
        _result = true;
      } else {
        unsigned int fuel_ = fuel - 1;
        if (n <= 2u) {
          _result = true;
        } else {
          _stack.emplace_back(_After2{(((n - 1u) > n ? 0 : (n - 1u))), fuel_});
          _stack.emplace_back(_Enter{(((n - 2u) > n ? 0 : (n - 2u))), fuel_});
        }
      }
    } else if (std::holds_alternative<_After2>(_frame)) {
      auto _f = std::move(std::get<_After2>(_frame));
      _stack.emplace_back(_Combine1{_result});
      _stack.emplace_back(_Enter{_f._s0, _f.fuel_});
    } else {
      auto _f = std::move(std::get<_Combine1>(_frame));
      _result = (_result && _f._result);
    }
  }
  return _result;
}

unsigned int LoopifyMultiRecursion::bool_and_chain(const unsigned int n) {
  if (bool_and_chain_fuel((n * 2u), n)) {
    return 1u;
  } else {
    return 0u;
  }
}

unsigned int LoopifyMultiRecursion::quad_count_leaves(
    const LoopifyMultiRecursion::quadtree
        &t) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const LoopifyMultiRecursion::quadtree *t;
  };

  /// _After_QQuad: saves [d_a2, d_a1, d_a0], dispatches next recursive call.
  struct _After_QQuad {
    const LoopifyMultiRecursion::quadtree *d_a2;
    const LoopifyMultiRecursion::quadtree *d_a1;
    const LoopifyMultiRecursion::quadtree *d_a0;
  };

  /// _After_QQuad_1: saves [_result, d_a1, d_a0], dispatches next recursive
  /// call.
  struct _After_QQuad_1 {
    unsigned int _result;
    const LoopifyMultiRecursion::quadtree *d_a1;
    const LoopifyMultiRecursion::quadtree *d_a0;
  };

  /// _After_QQuad_2: saves [_result_0, _result_1, d_a0], dispatches next
  /// recursive call.
  struct _After_QQuad_2 {
    unsigned int _result_0;
    unsigned int _result_1;
    const LoopifyMultiRecursion::quadtree *d_a0;
  };

  /// _Combine_QQuad: receives partial results, combines with _result from final
  /// call.
  struct _Combine_QQuad {
    unsigned int _result_0;
    unsigned int _result_1;
    unsigned int _result_2;
  };

  using _Frame = std::variant<_Enter, _After_QQuad, _After_QQuad_1,
                              _After_QQuad_2, _Combine_QQuad>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{&t});
  /// Loopified quad_count_leaves: _Enter -> _After_QQuad -> _After_QQuad_1 ->
  /// _After_QQuad_2 -> _Combine_QQuad.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const LoopifyMultiRecursion::quadtree &t = *(_f.t);
      if (std::holds_alternative<
              typename LoopifyMultiRecursion::quadtree::QLeaf>(t.v())) {
        _result = 1u;
      } else {
        const auto &[d_a0, d_a1, d_a2, d_a3] =
            std::get<typename LoopifyMultiRecursion::quadtree::QQuad>(t.v());
        _stack.emplace_back(_After_QQuad{d_a2.get(), d_a1.get(), d_a0.get()});
        _stack.emplace_back(_Enter{d_a3.get()});
      }
    } else if (std::holds_alternative<_After_QQuad>(_frame)) {
      auto _f = std::move(std::get<_After_QQuad>(_frame));
      _stack.emplace_back(_After_QQuad_1{_result, _f.d_a1, _f.d_a0});
      _stack.emplace_back(_Enter{_f.d_a2});
    } else if (std::holds_alternative<_After_QQuad_1>(_frame)) {
      auto _f = std::move(std::get<_After_QQuad_1>(_frame));
      _stack.emplace_back(_After_QQuad_2{_f._result, _result, _f.d_a0});
      _stack.emplace_back(_Enter{_f.d_a1});
    } else if (std::holds_alternative<_After_QQuad_2>(_frame)) {
      auto _f = std::move(std::get<_After_QQuad_2>(_frame));
      _stack.emplace_back(_Combine_QQuad{_f._result_0, _f._result_1, _result});
      _stack.emplace_back(_Enter{_f.d_a0});
    } else {
      auto _f = std::move(std::get<_Combine_QQuad>(_frame));
      _result = (((_result + _f._result_2) + _f._result_1) + _f._result_0);
    }
  }
  return _result;
}

unsigned int LoopifyMultiRecursion::quad_depth(
    const LoopifyMultiRecursion::quadtree
        &t) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const LoopifyMultiRecursion::quadtree *t;
  };

  /// _After_QQuad: saves [d_a2, d_a1, d_a0, _s3], dispatches next recursive
  /// call.
  struct _After_QQuad {
    const LoopifyMultiRecursion::quadtree *d_a2;
    const LoopifyMultiRecursion::quadtree *d_a1;
    const LoopifyMultiRecursion::quadtree *d_a0;
    decltype(1u) _s3;
  };

  /// _After_QQuad_1: saves [_result, d_a1, d_a0, _s3], dispatches next
  /// recursive call.
  struct _After_QQuad_1 {
    unsigned int _result;
    const LoopifyMultiRecursion::quadtree *d_a1;
    const LoopifyMultiRecursion::quadtree *d_a0;
    decltype(1u) _s3;
  };

  /// _After_QQuad_2: saves [_result_0, _result_1, d_a0, _s3], dispatches next
  /// recursive call.
  struct _After_QQuad_2 {
    unsigned int _result_0;
    unsigned int _result_1;
    const LoopifyMultiRecursion::quadtree *d_a0;
    decltype(1u) _s3;
  };

  /// _Combine_QQuad: receives partial results, combines with _result from final
  /// call.
  struct _Combine_QQuad {
    unsigned int _result_0;
    unsigned int _result_1;
    unsigned int _result_2;
    decltype(1u) _s3;
  };

  using _Frame = std::variant<_Enter, _After_QQuad, _After_QQuad_1,
                              _After_QQuad_2, _Combine_QQuad>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{&t});
  /// Loopified quad_depth: _Enter -> _After_QQuad -> _After_QQuad_1 ->
  /// _After_QQuad_2 -> _Combine_QQuad.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const LoopifyMultiRecursion::quadtree &t = *(_f.t);
      if (std::holds_alternative<
              typename LoopifyMultiRecursion::quadtree::QLeaf>(t.v())) {
        _result = 0u;
      } else {
        const auto &[d_a0, d_a1, d_a2, d_a3] =
            std::get<typename LoopifyMultiRecursion::quadtree::QQuad>(t.v());
        _stack.emplace_back(
            _After_QQuad{d_a2.get(), d_a1.get(), d_a0.get(), 1u});
        _stack.emplace_back(_Enter{d_a3.get()});
      }
    } else if (std::holds_alternative<_After_QQuad>(_frame)) {
      auto _f = std::move(std::get<_After_QQuad>(_frame));
      _stack.emplace_back(_After_QQuad_1{_result, _f.d_a1, _f.d_a0, _f._s3});
      _stack.emplace_back(_Enter{_f.d_a2});
    } else if (std::holds_alternative<_After_QQuad_1>(_frame)) {
      auto _f = std::move(std::get<_After_QQuad_1>(_frame));
      _stack.emplace_back(_After_QQuad_2{_f._result, _result, _f.d_a0, _f._s3});
      _stack.emplace_back(_Enter{_f.d_a1});
    } else if (std::holds_alternative<_After_QQuad_2>(_frame)) {
      auto _f = std::move(std::get<_After_QQuad_2>(_frame));
      _stack.emplace_back(
          _Combine_QQuad{_f._result_0, _f._result_1, _result, _f._s3});
      _stack.emplace_back(_Enter{_f.d_a0});
    } else {
      auto _f = std::move(std::get<_Combine_QQuad>(_frame));
      _result = (_f._s3 + std::max(std::max(_result, _f._result_2),
                                   std::max(_f._result_1, _f._result_0)));
    }
  }
  return _result;
}

unsigned int LoopifyMultiRecursion::hofstadter_q_fuel(
    const unsigned int fuel,
    const unsigned int
        n) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    unsigned int n;
    unsigned int fuel;
  };

  /// _After4: saves [_s0, fuel_], dispatches next recursive call.
  struct _After4 {
    decltype((
        ((std::declval<const unsigned int &>() -
          std::declval<unsigned int &>()) > std::declval<const unsigned int &>()
             ? 0
             : (std::declval<const unsigned int &>() -
                std::declval<unsigned int &>())))) _s0;
    unsigned int fuel_;
  };

  /// _Combine3: receives partial results, combines with _result from final
  /// call.
  struct _Combine3 {
    unsigned int _result;
  };

  /// _Cont1: saves [fuel_, n], resumes after recursive call, then processes
  /// rest.
  struct _Cont1 {
    unsigned int fuel_;
    unsigned int n;
  };

  /// _Cont2: saves [fuel_, n, q1], resumes after recursive call, then processes
  /// rest.
  struct _Cont2 {
    unsigned int fuel_;
    unsigned int n;
    unsigned int q1;
  };

  using _Frame = std::variant<_Enter, _After4, _Combine3, _Cont1, _Cont2>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{n, fuel});
  /// Loopified hofstadter_q_fuel: _Enter -> _After4 -> _Combine3 -> _Cont1 ->
  /// _Cont2.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const unsigned int n = _f.n;
      const unsigned int fuel = _f.fuel;
      if (fuel <= 0) {
        _result = 1u;
      } else {
        unsigned int fuel_ = fuel - 1;
        if (n <= 0u) {
          _result = 0u;
        } else {
          if (n == 1u) {
            _result = 1u;
          } else {
            if (n == 2u) {
              _result = 1u;
            } else {
              _stack.emplace_back(_Cont1{fuel_, n});
              _stack.emplace_back(
                  _Enter{(((n - 1u) > n ? 0 : (n - 1u))), fuel_});
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
      _result = (_result + _f._result);
    } else if (std::holds_alternative<_Cont1>(_frame)) {
      auto _f = std::move(std::get<_Cont1>(_frame));
      unsigned int fuel_ = _f.fuel_;
      const unsigned int n = _f.n;
      unsigned int q1 = _result;
      _stack.emplace_back(_Cont2{fuel_, n, q1});
      _stack.emplace_back(_Enter{(((n - 2u) > n ? 0 : (n - 2u))), fuel_});
    } else {
      auto _f = std::move(std::get<_Cont2>(_frame));
      unsigned int fuel_ = _f.fuel_;
      const unsigned int n = _f.n;
      unsigned int q1 = _f.q1;
      unsigned int q2 = _result;
      _stack.emplace_back(_After4{(((n - q1) > n ? 0 : (n - q1))), fuel_});
      _stack.emplace_back(_Enter{(((n - q2) > n ? 0 : (n - q2))), fuel_});
    }
  }
  return _result;
}

unsigned int LoopifyMultiRecursion::hofstadter_q(const unsigned int n) {
  return hofstadter_q_fuel(((n * n) + 1u), n);
}
