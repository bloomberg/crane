#include "loopify_multi_recursion.h"

uint64_t LoopifyMultiRecursion::mixed_arith_fuel(uint64_t fuel, uint64_t n) {
  // Explicit stack replaces the non-tail recursion of mixed_arith_fuel: _call
  // frames are pending calls, _after frames resume a caller.
  struct _call {
    uint64_t n;
    uint64_t fuel;
  };

  struct _after_mixed_arith_fuel_in_false {
    uint64_t n;
    uint64_t fuel_;
  };

  struct _after_mixed_arith_fuel_in_false_2 {
    uint64_t n;
    uint64_t fuel_;
    uint64_t _tmp3;
  };

  struct _after_mixed_arith_fuel_in_false_3 {
    uint64_t _tmp3;
    uint64_t _tmp2;
  };

  using _frame = std::variant<_call, _after_mixed_arith_fuel_in_false,
                              _after_mixed_arith_fuel_in_false_2,
                              _after_mixed_arith_fuel_in_false_3>;
  uint64_t _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{n, fuel});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      uint64_t n = _f.n;
      uint64_t fuel = _f.fuel;
      if (fuel <= 0) {
        _result = UINT64_C(1);
      } else {
        uint64_t fuel_ = fuel - 1;
        if (n <= UINT64_C(0)) {
          _result = UINT64_C(1);
        } else if (n == UINT64_C(1)) {
          _result = UINT64_C(1);
        } else if (n == UINT64_C(2)) {
          _result = UINT64_C(1);
        } else {
          _stack.emplace_back(_after_mixed_arith_fuel_in_false{n, fuel_});
          _stack.emplace_back(
              _call{(n - UINT64_C(1) > n ? 0 : n - UINT64_C(1)), fuel_});
        }
      }
    } else if (
            std::holds_alternative<_after_mixed_arith_fuel_in_false>(_popped)) {
      auto _f = std::move(std::get<_after_mixed_arith_fuel_in_false>(_popped));
      _stack.pop_back();
      uint64_t n = _f.n;
      uint64_t fuel_ = _f.fuel_;
      _stack.emplace_back(_after_mixed_arith_fuel_in_false_2{n, fuel_,
                                                             _result});
      _stack.emplace_back(
          _call{(n - UINT64_C(2) > n ? 0 : n - UINT64_C(2)), fuel_});
    } else if (
            std::holds_alternative<_after_mixed_arith_fuel_in_false_2>(_popped)) {
      auto _f =
          std::move(std::get<_after_mixed_arith_fuel_in_false_2>(_popped));
      _stack.pop_back();
      uint64_t n = _f.n;
      uint64_t fuel_ = _f.fuel_;
      _stack.emplace_back(_after_mixed_arith_fuel_in_false_3{_f._tmp3,
                                                             _result});
      _stack.emplace_back(
          _call{(n - UINT64_C(3) > n ? 0 : n - UINT64_C(3)), fuel_});
    } else {
      auto _f =
          std::move(std::get<_after_mixed_arith_fuel_in_false_3>(_popped));
      _stack.pop_back();
      _result = _f._tmp3 * _f._tmp2 + _result;
    }
  }
  return _result;
}

uint64_t LoopifyMultiRecursion::mixed_arith(uint64_t n) {
  return mixed_arith_fuel(n * UINT64_C(3), n);
}

bool LoopifyMultiRecursion::bool_or_chain_fuel(uint64_t fuel, uint64_t n,
                                               uint64_t target) {
  // Explicit stack replaces the non-tail recursion of bool_or_chain_fuel: _call
  // frames are pending calls, _after frames resume a caller.
  struct _call {
    uint64_t n;
    uint64_t fuel;
  };

  struct _after_bool_or_chain_fuel_in_false {
    uint64_t n;
    uint64_t fuel_;
  };

  struct _after_bool_or_chain_fuel_in_false_2 {
    uint64_t n;
    bool _tmp2;
  };

  using _frame = std::variant<_call, _after_bool_or_chain_fuel_in_false,
                              _after_bool_or_chain_fuel_in_false_2>;
  bool _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{n, fuel});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      uint64_t n = _f.n;
      uint64_t fuel = _f.fuel;
      if (fuel <= 0) {
        _result = false;
      } else {
        uint64_t fuel_ = fuel - 1;
        if (n <= UINT64_C(0)) {
          _result = false;
        } else {
          _stack.emplace_back(_after_bool_or_chain_fuel_in_false{n, fuel_});
          _stack.emplace_back(
              _call{(n - UINT64_C(1) > n ? 0 : n - UINT64_C(1)), fuel_});
        }
      }
    } else if (
            std::holds_alternative<_after_bool_or_chain_fuel_in_false>(_popped)) {
      auto _f =
          std::move(std::get<_after_bool_or_chain_fuel_in_false>(_popped));
      _stack.pop_back();
      uint64_t n = _f.n;
      uint64_t fuel_ = _f.fuel_;
      _stack.emplace_back(_after_bool_or_chain_fuel_in_false_2{n, _result});
      _stack.emplace_back(
          _call{(n - UINT64_C(2) > n ? 0 : n - UINT64_C(2)), fuel_});
    } else {
      auto _f =
          std::move(std::get<_after_bool_or_chain_fuel_in_false_2>(_popped));
      _stack.pop_back();
      uint64_t n = _f.n;
      _result = (((n == target) || _f._tmp2) || _result);
    }
  }
  return _result;
}

uint64_t LoopifyMultiRecursion::bool_or_chain(uint64_t n, uint64_t target) {
  if (bool_or_chain_fuel(n * UINT64_C(2), n, target)) {
    return UINT64_C(1);
  } else {
    return UINT64_C(0);
  }
}

bool LoopifyMultiRecursion::bool_and_chain_fuel(uint64_t fuel, uint64_t n) {
  // Explicit stack replaces the non-tail recursion of bool_and_chain_fuel:
  // _call frames are pending calls, _after frames resume a caller.
  struct _call {
    uint64_t n;
    uint64_t fuel;
  };

  struct _after_bool_and_chain_fuel_in_false {
    uint64_t n;
    uint64_t fuel_;
  };

  struct _after_bool_and_chain_fuel_in_false_2 {
    bool _tmp2;
  };

  using _frame = std::variant<_call, _after_bool_and_chain_fuel_in_false,
                              _after_bool_and_chain_fuel_in_false_2>;
  bool _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{n, fuel});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      uint64_t n = _f.n;
      uint64_t fuel = _f.fuel;
      if (fuel <= 0) {
        _result = true;
      } else {
        uint64_t fuel_ = fuel - 1;
        if (n <= UINT64_C(2)) {
          _result = true;
        } else {
          _stack.emplace_back(_after_bool_and_chain_fuel_in_false{n, fuel_});
          _stack.emplace_back(
              _call{(n - UINT64_C(1) > n ? 0 : n - UINT64_C(1)), fuel_});
        }
      }
    } else if (std::holds_alternative<_after_bool_and_chain_fuel_in_false>(
                   _popped)) {
      auto _f =
          std::move(std::get<_after_bool_and_chain_fuel_in_false>(_popped));
      _stack.pop_back();
      uint64_t n = _f.n;
      uint64_t fuel_ = _f.fuel_;
      _stack.emplace_back(_after_bool_and_chain_fuel_in_false_2{_result});
      _stack.emplace_back(
          _call{(n - UINT64_C(2) > n ? 0 : n - UINT64_C(2)), fuel_});
    } else {
      auto _f =
          std::move(std::get<_after_bool_and_chain_fuel_in_false_2>(_popped));
      _stack.pop_back();
      _result = (_f._tmp2 && _result);
    }
  }
  return _result;
}

uint64_t LoopifyMultiRecursion::bool_and_chain(uint64_t n) {
  if (bool_and_chain_fuel(n * UINT64_C(2), n)) {
    return UINT64_C(1);
  } else {
    return UINT64_C(0);
  }
}

uint64_t LoopifyMultiRecursion::quad_count_leaves(
    const LoopifyMultiRecursion::quadtree &t) {
  // Explicit stack replaces the non-tail recursion of quad_count_leaves: _call
  // frames are pending calls, _after frames resume a caller.
  struct _call {
    const LoopifyMultiRecursion::quadtree *t;
  };

  struct _after_quad_count_leaves_in_QQuad {
    const LoopifyMultiRecursion::quadtree *a1;
    const LoopifyMultiRecursion::quadtree *a2;
    const LoopifyMultiRecursion::quadtree *a3;
  };

  struct _after_quad_count_leaves_in_QQuad_2 {
    const LoopifyMultiRecursion::quadtree *a2;
    const LoopifyMultiRecursion::quadtree *a3;
    uint64_t _tmp4;
  };

  struct _after_quad_count_leaves_in_QQuad_3 {
    const LoopifyMultiRecursion::quadtree *a3;
    uint64_t _tmp4;
    uint64_t _tmp3;
  };

  struct _after_quad_count_leaves_in_QQuad_4 {
    uint64_t _tmp4;
    uint64_t _tmp3;
    uint64_t _tmp2;
  };

  using _frame = std::variant<_call, _after_quad_count_leaves_in_QQuad,
                              _after_quad_count_leaves_in_QQuad_2,
                              _after_quad_count_leaves_in_QQuad_3,
                              _after_quad_count_leaves_in_QQuad_4>;
  uint64_t _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&t});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const LoopifyMultiRecursion::quadtree &t = *_f.t;
      if (std::holds_alternative<
              typename LoopifyMultiRecursion::quadtree::QLeaf>(t.v())) {
        _result = UINT64_C(1);
      } else {
        const auto &[a0, a1, a2, a3] =
            std::get<typename LoopifyMultiRecursion::quadtree::QQuad>(t.v());
        _stack.emplace_back(_after_quad_count_leaves_in_QQuad{
            crane_raw(a1), crane_raw(a2), crane_raw(a3)});
        _stack.emplace_back(_call{crane_raw(a0)});
      }
    } else if (
            std::holds_alternative<_after_quad_count_leaves_in_QQuad>(_popped)) {
      auto _f = std::move(std::get<_after_quad_count_leaves_in_QQuad>(_popped));
      _stack.pop_back();
      const LoopifyMultiRecursion::quadtree &a1 = *_f.a1;
      const LoopifyMultiRecursion::quadtree &a2 = *_f.a2;
      const LoopifyMultiRecursion::quadtree &a3 = *_f.a3;
      _stack.emplace_back(
          _after_quad_count_leaves_in_QQuad_2{&a2, &a3, _result});
      _stack.emplace_back(_call{&a1});
    } else if (std::holds_alternative<_after_quad_count_leaves_in_QQuad_2>(
                   _popped)) {
      auto _f =
          std::move(std::get<_after_quad_count_leaves_in_QQuad_2>(_popped));
      _stack.pop_back();
      const LoopifyMultiRecursion::quadtree &a2 = *_f.a2;
      const LoopifyMultiRecursion::quadtree &a3 = *_f.a3;
      _stack.emplace_back(
          _after_quad_count_leaves_in_QQuad_3{&a3, _f._tmp4, _result});
      _stack.emplace_back(_call{&a2});
    } else if (std::holds_alternative<_after_quad_count_leaves_in_QQuad_3>(
                   _popped)) {
      auto _f =
          std::move(std::get<_after_quad_count_leaves_in_QQuad_3>(_popped));
      _stack.pop_back();
      const LoopifyMultiRecursion::quadtree &a3 = *_f.a3;
      _stack.emplace_back(
          _after_quad_count_leaves_in_QQuad_4{_f._tmp4, _f._tmp3, _result});
      _stack.emplace_back(_call{&a3});
    } else {
      auto _f =
          std::move(std::get<_after_quad_count_leaves_in_QQuad_4>(_popped));
      _stack.pop_back();
      _result = _f._tmp4 + _f._tmp3 + _f._tmp2 + _result;
    }
  }
  return _result;
}

uint64_t
LoopifyMultiRecursion::quad_depth(const LoopifyMultiRecursion::quadtree &t) {
  // Explicit stack replaces the non-tail recursion of quad_depth: _call frames
  // are pending calls, _after frames resume a caller.
  struct _call {
    const LoopifyMultiRecursion::quadtree *t;
  };

  struct _after_quad_depth_in_QQuad {
    const LoopifyMultiRecursion::quadtree *a1;
    const LoopifyMultiRecursion::quadtree *a2;
    const LoopifyMultiRecursion::quadtree *a3;
  };

  struct _after_quad_depth_in_QQuad_2 {
    const LoopifyMultiRecursion::quadtree *a2;
    const LoopifyMultiRecursion::quadtree *a3;
    uint64_t _tmp4;
  };

  struct _after_quad_depth_in_QQuad_3 {
    const LoopifyMultiRecursion::quadtree *a3;
    uint64_t _tmp4;
    uint64_t _tmp3;
  };

  struct _after_quad_depth_in_QQuad_4 {
    uint64_t _tmp4;
    uint64_t _tmp3;
    uint64_t _tmp2;
  };

  using _frame = std::variant<
      _call, _after_quad_depth_in_QQuad, _after_quad_depth_in_QQuad_2,
      _after_quad_depth_in_QQuad_3, _after_quad_depth_in_QQuad_4>;
  uint64_t _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&t});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const LoopifyMultiRecursion::quadtree &t = *_f.t;
      if (std::holds_alternative<
              typename LoopifyMultiRecursion::quadtree::QLeaf>(t.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1, a2, a3] =
            std::get<typename LoopifyMultiRecursion::quadtree::QQuad>(t.v());
        _stack.emplace_back(_after_quad_depth_in_QQuad{
            crane_raw(a1), crane_raw(a2), crane_raw(a3)});
        _stack.emplace_back(_call{crane_raw(a0)});
      }
    } else if (std::holds_alternative<_after_quad_depth_in_QQuad>(_popped)) {
      auto _f = std::move(std::get<_after_quad_depth_in_QQuad>(_popped));
      _stack.pop_back();
      const LoopifyMultiRecursion::quadtree &a1 = *_f.a1;
      const LoopifyMultiRecursion::quadtree &a2 = *_f.a2;
      const LoopifyMultiRecursion::quadtree &a3 = *_f.a3;
      _stack.emplace_back(_after_quad_depth_in_QQuad_2{&a2, &a3, _result});
      _stack.emplace_back(_call{&a1});
    } else if (std::holds_alternative<_after_quad_depth_in_QQuad_2>(_popped)) {
      auto _f = std::move(std::get<_after_quad_depth_in_QQuad_2>(_popped));
      _stack.pop_back();
      const LoopifyMultiRecursion::quadtree &a2 = *_f.a2;
      const LoopifyMultiRecursion::quadtree &a3 = *_f.a3;
      _stack.emplace_back(_after_quad_depth_in_QQuad_3{&a3, _f._tmp4, _result});
      _stack.emplace_back(_call{&a2});
    } else if (std::holds_alternative<_after_quad_depth_in_QQuad_3>(_popped)) {
      auto _f = std::move(std::get<_after_quad_depth_in_QQuad_3>(_popped));
      _stack.pop_back();
      const LoopifyMultiRecursion::quadtree &a3 = *_f.a3;
      _stack.emplace_back(
          _after_quad_depth_in_QQuad_4{_f._tmp4, _f._tmp3, _result});
      _stack.emplace_back(_call{&a3});
    } else {
      auto _f = std::move(std::get<_after_quad_depth_in_QQuad_4>(_popped));
      _stack.pop_back();
      _result = UINT64_C(1) + std::max(std::max(_f._tmp4, _f._tmp3),
                                       std::max(_f._tmp2, _result));
    }
  }
  return _result;
}

uint64_t LoopifyMultiRecursion::hofstadter_q_fuel(uint64_t fuel, uint64_t n) {
  // Explicit stack replaces the non-tail recursion of hofstadter_q_fuel: _call
  // frames are pending calls, _after frames resume a caller.
  struct _call {
    uint64_t n;
    uint64_t fuel;
  };

  struct _after_hofstadter_q_fuel_in_false {
    uint64_t n;
    uint64_t fuel_;
  };

  struct _after_hofstadter_q_fuel_in_false_2 {
    uint64_t n;
    uint64_t fuel_;
    uint64_t q1;
  };

  struct _after_hofstadter_q_fuel_in_false_3 {
    uint64_t n;
    uint64_t fuel_;
    uint64_t q2;
  };

  struct _after_hofstadter_q_fuel_in_false_4 {
    uint64_t _tmp2;
  };

  using _frame = std::variant<_call, _after_hofstadter_q_fuel_in_false,
                              _after_hofstadter_q_fuel_in_false_2,
                              _after_hofstadter_q_fuel_in_false_3,
                              _after_hofstadter_q_fuel_in_false_4>;
  uint64_t _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{n, fuel});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      uint64_t n = _f.n;
      uint64_t fuel = _f.fuel;
      if (fuel <= 0) {
        _result = UINT64_C(1);
      } else {
        uint64_t fuel_ = fuel - 1;
        if (n <= UINT64_C(0)) {
          _result = UINT64_C(0);
        } else if (n == UINT64_C(1)) {
          _result = UINT64_C(1);
        } else if (n == UINT64_C(2)) {
          _result = UINT64_C(1);
        } else {
          _stack.emplace_back(_after_hofstadter_q_fuel_in_false{n, fuel_});
          _stack.emplace_back(
              _call{(n - UINT64_C(1) > n ? 0 : n - UINT64_C(1)), fuel_});
        }
      }
    } else if (
            std::holds_alternative<_after_hofstadter_q_fuel_in_false>(_popped)) {
      auto _f = std::move(std::get<_after_hofstadter_q_fuel_in_false>(_popped));
      _stack.pop_back();
      uint64_t n = _f.n;
      uint64_t fuel_ = _f.fuel_;
      uint64_t q1 = _result;
      _stack.emplace_back(_after_hofstadter_q_fuel_in_false_2{n, fuel_, q1});
      _stack.emplace_back(
          _call{(n - UINT64_C(2) > n ? 0 : n - UINT64_C(2)), fuel_});
    } else if (std::holds_alternative<_after_hofstadter_q_fuel_in_false_2>(
                   _popped)) {
      auto _f =
          std::move(std::get<_after_hofstadter_q_fuel_in_false_2>(_popped));
      _stack.pop_back();
      uint64_t n = _f.n;
      uint64_t fuel_ = _f.fuel_;
      uint64_t q1 = _f.q1;
      uint64_t q2 = _result;
      _stack.emplace_back(_after_hofstadter_q_fuel_in_false_3{n, fuel_, q2});
      _stack.emplace_back(_call{(n - q1 > n ? 0 : n - q1), fuel_});
    } else if (std::holds_alternative<_after_hofstadter_q_fuel_in_false_3>(
                   _popped)) {
      auto _f =
          std::move(std::get<_after_hofstadter_q_fuel_in_false_3>(_popped));
      _stack.pop_back();
      uint64_t n = _f.n;
      uint64_t fuel_ = _f.fuel_;
      uint64_t q2 = _f.q2;
      _stack.emplace_back(_after_hofstadter_q_fuel_in_false_4{_result});
      _stack.emplace_back(_call{(n - q2 > n ? 0 : n - q2), fuel_});
    } else {
      auto _f =
          std::move(std::get<_after_hofstadter_q_fuel_in_false_4>(_popped));
      _stack.pop_back();
      _result = _f._tmp2 + _result;
    }
  }
  return _result;
}

uint64_t LoopifyMultiRecursion::hofstadter_q(uint64_t n) {
  return hofstadter_q_fuel(n * n + UINT64_C(1), n);
}
