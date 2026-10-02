#include "loopify_multi_recursion.h"

uint64_t LoopifyMultiRecursion::mixed_arith_fuel(
    uint64_t fuel,
    uint64_t
        n) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    uint64_t n;
    uint64_t fuel;
  };

  /// _Cont1: saves [fuel_, n], resumes after recursive call, then processes
  /// rest.
  struct _Cont1 {
    uint64_t fuel_;
    uint64_t n;
  };

  /// _Cont2: saves [fuel_, n, r_], resumes after recursive call, then processes
  /// rest.
  struct _Cont2 {
    uint64_t fuel_;
    uint64_t n;
    uint64_t r_;
  };

  /// _Cont3: saves [r_, r_0], resumes after recursive call, then processes
  /// rest.
  struct _Cont3 {
    uint64_t r_;
    uint64_t r_0;
  };

  using _Frame = std::variant<_Enter, _Cont1, _Cont2, _Cont3>;
  uint64_t _result{};
  crane::small_vector<_Frame> _stack;
  _stack.emplace_back(_Enter{n, fuel});
  /// Loopified mixed_arith_fuel: _Enter -> _Cont1 -> _Cont2 -> _Cont3.
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
              _stack.emplace_back(_Cont1{fuel_, n});
              _stack.emplace_back(_Enter{
                  (((n - UINT64_C(1)) > n ? 0 : (n - UINT64_C(1)))), fuel_});
            }
          }
        }
      }
    } else if (std::holds_alternative<_Cont1>(_frame)) {
      auto _f = std::move(std::get<_Cont1>(_frame));
      uint64_t fuel_ = _f.fuel_;
      uint64_t n = _f.n;
      uint64_t r_ = std::move(_result);
      _stack.emplace_back(_Cont2{fuel_, n, r_});
      _stack.emplace_back(
          _Enter{(((n - UINT64_C(2)) > n ? 0 : (n - UINT64_C(2)))), fuel_});
    } else if (std::holds_alternative<_Cont2>(_frame)) {
      auto _f = std::move(std::get<_Cont2>(_frame));
      uint64_t fuel_ = _f.fuel_;
      uint64_t n = _f.n;
      uint64_t r_ = _f.r_;
      uint64_t r_0 = std::move(_result);
      _stack.emplace_back(_Cont3{r_, r_0});
      _stack.emplace_back(
          _Enter{(((n - UINT64_C(3)) > n ? 0 : (n - UINT64_C(3)))), fuel_});
    } else {
      auto _f = std::move(std::get<_Cont3>(_frame));
      uint64_t r_ = _f.r_;
      uint64_t r_0 = _f.r_0;
      uint64_t r_1 = std::move(_result);
      _result = ((r_ * r_0) + r_1);
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

  /// _Cont1: saves [fuel_, n], resumes after recursive call, then processes
  /// rest.
  struct _Cont1 {
    uint64_t fuel_;
    uint64_t n;
  };

  /// _Cont2: saves [n, r_], resumes after recursive call, then processes rest.
  struct _Cont2 {
    uint64_t n;
    bool r_;
  };

  using _Frame = std::variant<_Enter, _Cont1, _Cont2>;
  bool _result{};
  crane::small_vector<_Frame> _stack;
  _stack.emplace_back(_Enter{n, fuel});
  /// Loopified bool_or_chain_fuel: _Enter -> _Cont1 -> _Cont2.
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
          _stack.emplace_back(_Cont1{fuel_, n});
          _stack.emplace_back(
              _Enter{(((n - UINT64_C(1)) > n ? 0 : (n - UINT64_C(1)))), fuel_});
        }
      }
    } else if (std::holds_alternative<_Cont1>(_frame)) {
      auto _f = std::move(std::get<_Cont1>(_frame));
      uint64_t fuel_ = _f.fuel_;
      uint64_t n = _f.n;
      bool r_ = std::move(_result);
      _stack.emplace_back(_Cont2{n, r_});
      _stack.emplace_back(
          _Enter{(((n - UINT64_C(2)) > n ? 0 : (n - UINT64_C(2)))), fuel_});
    } else {
      auto _f = std::move(std::get<_Cont2>(_frame));
      uint64_t n = _f.n;
      bool r_ = _f.r_;
      bool r_0 = std::move(_result);
      _result = ((n == target || r_) || r_0);
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

  /// _Cont1: saves [fuel_, n], resumes after recursive call, then processes
  /// rest.
  struct _Cont1 {
    uint64_t fuel_;
    uint64_t n;
  };

  /// _Cont2: saves [r_], resumes after recursive call, then processes rest.
  struct _Cont2 {
    bool r_;
  };

  using _Frame = std::variant<_Enter, _Cont1, _Cont2>;
  bool _result{};
  crane::small_vector<_Frame> _stack;
  _stack.emplace_back(_Enter{n, fuel});
  /// Loopified bool_and_chain_fuel: _Enter -> _Cont1 -> _Cont2.
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
          _stack.emplace_back(_Cont1{fuel_, n});
          _stack.emplace_back(
              _Enter{(((n - UINT64_C(1)) > n ? 0 : (n - UINT64_C(1)))), fuel_});
        }
      }
    } else if (std::holds_alternative<_Cont1>(_frame)) {
      auto _f = std::move(std::get<_Cont1>(_frame));
      uint64_t fuel_ = _f.fuel_;
      uint64_t n = _f.n;
      bool r_ = std::move(_result);
      _stack.emplace_back(_Cont2{r_});
      _stack.emplace_back(
          _Enter{(((n - UINT64_C(2)) > n ? 0 : (n - UINT64_C(2)))), fuel_});
    } else {
      auto _f = std::move(std::get<_Cont2>(_frame));
      bool r_ = _f.r_;
      bool r_0 = std::move(_result);
      _result = (r_ && r_0);
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

  /// _Cont_QQuad: saves [a1, a2, a3], resumes after recursive call, then
  /// processes rest.
  struct _Cont_QQuad {
    const LoopifyMultiRecursion::quadtree *a1;
    const LoopifyMultiRecursion::quadtree *a2;
    const LoopifyMultiRecursion::quadtree *a3;
  };

  /// _Cont_QQuad_1: saves [a2, a3, r_], resumes after recursive call, then
  /// processes rest.
  struct _Cont_QQuad_1 {
    const LoopifyMultiRecursion::quadtree *a2;
    const LoopifyMultiRecursion::quadtree *a3;
    uint64_t r_;
  };

  /// _Cont_QQuad_2: saves [a3, r_, r_0], resumes after recursive call, then
  /// processes rest.
  struct _Cont_QQuad_2 {
    const LoopifyMultiRecursion::quadtree *a3;
    uint64_t r_;
    uint64_t r_0;
  };

  /// _Cont_QQuad_3: saves [r_, r_0, r_1], resumes after recursive call, then
  /// processes rest.
  struct _Cont_QQuad_3 {
    uint64_t r_;
    uint64_t r_0;
    uint64_t r_1;
  };

  using _Frame = std::variant<_Enter, _Cont_QQuad, _Cont_QQuad_1, _Cont_QQuad_2,
                              _Cont_QQuad_3>;
  uint64_t _result{};
  crane::small_vector<_Frame> _stack;
  _stack.emplace_back(_Enter{&t});
  /// Loopified quad_count_leaves: _Enter -> _Cont_QQuad -> _Cont_QQuad_1 ->
  /// _Cont_QQuad_2 -> _Cont_QQuad_3.
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
        _stack.emplace_back(
            _Cont_QQuad{crane_raw(a1), crane_raw(a2), crane_raw(a3)});
        _stack.emplace_back(_Enter{crane_raw(a0)});
      }
    } else if (std::holds_alternative<_Cont_QQuad>(_frame)) {
      auto _f = std::move(std::get<_Cont_QQuad>(_frame));
      const LoopifyMultiRecursion::quadtree &a1 = *_f.a1;
      const LoopifyMultiRecursion::quadtree &a2 = *_f.a2;
      const LoopifyMultiRecursion::quadtree &a3 = *_f.a3;
      uint64_t r_ = std::move(_result);
      _stack.emplace_back(_Cont_QQuad_1{&a2, &a3, r_});
      _stack.emplace_back(_Enter{&a1});
    } else if (std::holds_alternative<_Cont_QQuad_1>(_frame)) {
      auto _f = std::move(std::get<_Cont_QQuad_1>(_frame));
      const LoopifyMultiRecursion::quadtree &a2 = *_f.a2;
      const LoopifyMultiRecursion::quadtree &a3 = *_f.a3;
      uint64_t r_ = _f.r_;
      uint64_t r_0 = std::move(_result);
      _stack.emplace_back(_Cont_QQuad_2{&a3, r_, r_0});
      _stack.emplace_back(_Enter{&a2});
    } else if (std::holds_alternative<_Cont_QQuad_2>(_frame)) {
      auto _f = std::move(std::get<_Cont_QQuad_2>(_frame));
      const LoopifyMultiRecursion::quadtree &a3 = *_f.a3;
      uint64_t r_ = _f.r_;
      uint64_t r_0 = _f.r_0;
      uint64_t r_1 = std::move(_result);
      _stack.emplace_back(_Cont_QQuad_3{r_, r_0, r_1});
      _stack.emplace_back(_Enter{&a3});
    } else {
      auto _f = std::move(std::get<_Cont_QQuad_3>(_frame));
      uint64_t r_ = _f.r_;
      uint64_t r_0 = _f.r_0;
      uint64_t r_1 = _f.r_1;
      uint64_t r_2 = std::move(_result);
      _result = (((r_ + r_0) + r_1) + r_2);
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

  /// _Cont_QQuad: saves [a1, a2, a3], resumes after recursive call, then
  /// processes rest.
  struct _Cont_QQuad {
    const LoopifyMultiRecursion::quadtree *a1;
    const LoopifyMultiRecursion::quadtree *a2;
    const LoopifyMultiRecursion::quadtree *a3;
  };

  /// _Cont_QQuad_1: saves [a2, a3, r_], resumes after recursive call, then
  /// processes rest.
  struct _Cont_QQuad_1 {
    const LoopifyMultiRecursion::quadtree *a2;
    const LoopifyMultiRecursion::quadtree *a3;
    uint64_t r_;
  };

  /// _Cont_QQuad_2: saves [a3, r_, r_0], resumes after recursive call, then
  /// processes rest.
  struct _Cont_QQuad_2 {
    const LoopifyMultiRecursion::quadtree *a3;
    uint64_t r_;
    uint64_t r_0;
  };

  /// _Cont_QQuad_3: saves [r_, r_0, r_1], resumes after recursive call, then
  /// processes rest.
  struct _Cont_QQuad_3 {
    uint64_t r_;
    uint64_t r_0;
    uint64_t r_1;
  };

  using _Frame = std::variant<_Enter, _Cont_QQuad, _Cont_QQuad_1, _Cont_QQuad_2,
                              _Cont_QQuad_3>;
  uint64_t _result{};
  crane::small_vector<_Frame> _stack;
  _stack.emplace_back(_Enter{&t});
  /// Loopified quad_depth: _Enter -> _Cont_QQuad -> _Cont_QQuad_1 ->
  /// _Cont_QQuad_2 -> _Cont_QQuad_3.
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
            _Cont_QQuad{crane_raw(a1), crane_raw(a2), crane_raw(a3)});
        _stack.emplace_back(_Enter{crane_raw(a0)});
      }
    } else if (std::holds_alternative<_Cont_QQuad>(_frame)) {
      auto _f = std::move(std::get<_Cont_QQuad>(_frame));
      const LoopifyMultiRecursion::quadtree &a1 = *_f.a1;
      const LoopifyMultiRecursion::quadtree &a2 = *_f.a2;
      const LoopifyMultiRecursion::quadtree &a3 = *_f.a3;
      uint64_t r_ = std::move(_result);
      _stack.emplace_back(_Cont_QQuad_1{&a2, &a3, r_});
      _stack.emplace_back(_Enter{&a1});
    } else if (std::holds_alternative<_Cont_QQuad_1>(_frame)) {
      auto _f = std::move(std::get<_Cont_QQuad_1>(_frame));
      const LoopifyMultiRecursion::quadtree &a2 = *_f.a2;
      const LoopifyMultiRecursion::quadtree &a3 = *_f.a3;
      uint64_t r_ = _f.r_;
      uint64_t r_0 = std::move(_result);
      _stack.emplace_back(_Cont_QQuad_2{&a3, r_, r_0});
      _stack.emplace_back(_Enter{&a2});
    } else if (std::holds_alternative<_Cont_QQuad_2>(_frame)) {
      auto _f = std::move(std::get<_Cont_QQuad_2>(_frame));
      const LoopifyMultiRecursion::quadtree &a3 = *_f.a3;
      uint64_t r_ = _f.r_;
      uint64_t r_0 = _f.r_0;
      uint64_t r_1 = std::move(_result);
      _stack.emplace_back(_Cont_QQuad_3{r_, r_0, r_1});
      _stack.emplace_back(_Enter{&a3});
    } else {
      auto _f = std::move(std::get<_Cont_QQuad_3>(_frame));
      uint64_t r_ = _f.r_;
      uint64_t r_0 = _f.r_0;
      uint64_t r_1 = _f.r_1;
      uint64_t r_2 = std::move(_result);
      _result = (UINT64_C(1) + std::max(std::max(r_, r_0), std::max(r_1, r_2)));
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

  /// _Cont3: saves [fuel_, n, q2], resumes after recursive call, then processes
  /// rest.
  struct _Cont3 {
    uint64_t fuel_;
    uint64_t n;
    uint64_t q2;
  };

  /// _Cont4: saves [r_], resumes after recursive call, then processes rest.
  struct _Cont4 {
    uint64_t r_;
  };

  using _Frame = std::variant<_Enter, _Cont1, _Cont2, _Cont3, _Cont4>;
  uint64_t _result{};
  crane::small_vector<_Frame> _stack;
  _stack.emplace_back(_Enter{n, fuel});
  /// Loopified hofstadter_q_fuel: _Enter -> _Cont1 -> _Cont2 -> _Cont3 ->
  /// _Cont4.
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
    } else if (std::holds_alternative<_Cont1>(_frame)) {
      auto _f = std::move(std::get<_Cont1>(_frame));
      uint64_t fuel_ = _f.fuel_;
      uint64_t n = _f.n;
      uint64_t q1 = std::move(_result);
      _stack.emplace_back(_Cont2{fuel_, n, q1});
      _stack.emplace_back(
          _Enter{(((n - UINT64_C(2)) > n ? 0 : (n - UINT64_C(2)))), fuel_});
    } else if (std::holds_alternative<_Cont2>(_frame)) {
      auto _f = std::move(std::get<_Cont2>(_frame));
      uint64_t fuel_ = _f.fuel_;
      uint64_t n = _f.n;
      uint64_t q1 = _f.q1;
      uint64_t q2 = std::move(_result);
      _stack.emplace_back(_Cont3{fuel_, n, q2});
      _stack.emplace_back(_Enter{(((n - q1) > n ? 0 : (n - q1))), fuel_});
    } else if (std::holds_alternative<_Cont3>(_frame)) {
      auto _f = std::move(std::get<_Cont3>(_frame));
      uint64_t fuel_ = _f.fuel_;
      uint64_t n = _f.n;
      uint64_t q2 = _f.q2;
      uint64_t r_ = std::move(_result);
      _stack.emplace_back(_Cont4{r_});
      _stack.emplace_back(_Enter{(((n - q2) > n ? 0 : (n - q2))), fuel_});
    } else {
      auto _f = std::move(std::get<_Cont4>(_frame));
      uint64_t r_ = _f.r_;
      uint64_t r_0 = std::move(_result);
      _result = (r_ + r_0);
    }
  }
  return _result;
}

uint64_t LoopifyMultiRecursion::hofstadter_q(uint64_t n) {
  return hofstadter_q_fuel(((n * n) + UINT64_C(1)), n);
}
