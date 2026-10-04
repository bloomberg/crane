#include "loopify_multi_recursion.h"

uint64_t LoopifyMultiRecursion::mixed_arith_fuel(
    uint64_t fuel, uint64_t n) { /// CraneEnter: captures varying parameters for
                                 /// each recursive call.

  struct CraneEnter {
    uint64_t n;
    uint64_t fuel;
  };

  /// CraneCont1: saves [fuel_, n], resumes after recursive call, then processes
  /// rest.
  struct CraneCont1 {
    uint64_t fuel_;
    uint64_t n;
  };

  /// CraneCont2: saves [_tmp3, fuel_, n], resumes after recursive call, then
  /// processes rest.
  struct CraneCont2 {
    uint64_t _tmp3;
    uint64_t fuel_;
    uint64_t n;
  };

  /// CraneCont3: saves [_tmp2, _tmp3], resumes after recursive call, then
  /// processes rest.
  struct CraneCont3 {
    uint64_t _tmp2;
    uint64_t _tmp3;
  };

  using CraneFrame =
      std::variant<CraneEnter, CraneCont1, CraneCont2, CraneCont3>;
  uint64_t _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{n, fuel});
  /// Loopified mixed_arith_fuel: CraneEnter -> CraneCont1 -> CraneCont2 ->
  /// CraneCont3.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
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
              _stack.emplace_back(CraneCont1{fuel_, n});
              _stack.emplace_back(CraneEnter{
                  (((n - UINT64_C(1)) > n ? 0 : (n - UINT64_C(1)))), fuel_});
            }
          }
        }
      }
    } else if (std::holds_alternative<CraneCont1>(_frame)) {
      auto _f = std::move(std::get<CraneCont1>(_frame));
      uint64_t fuel_ = _f.fuel_;
      uint64_t n = _f.n;
      _stack.emplace_back(CraneCont2{std::move(_result), fuel_, n});
      _stack.emplace_back(
          CraneEnter{(((n - UINT64_C(2)) > n ? 0 : (n - UINT64_C(2)))), fuel_});
    } else if (std::holds_alternative<CraneCont2>(_frame)) {
      auto _f = std::move(std::get<CraneCont2>(_frame));
      uint64_t fuel_ = _f.fuel_;
      uint64_t n = _f.n;
      _stack.emplace_back(CraneCont3{std::move(_result), _f._tmp3});
      _stack.emplace_back(
          CraneEnter{(((n - UINT64_C(3)) > n ? 0 : (n - UINT64_C(3)))), fuel_});
    } else {
      auto _f = std::move(std::get<CraneCont3>(_frame));
      _result = ((_f._tmp3 * _f._tmp2) + std::move(_result));
    }
  }
  return _result;
}

uint64_t LoopifyMultiRecursion::mixed_arith(uint64_t n) {
  return mixed_arith_fuel((n * UINT64_C(3)), n);
}

bool LoopifyMultiRecursion::bool_or_chain_fuel(
    uint64_t fuel, uint64_t n,
    uint64_t target) { /// CraneEnter: captures varying parameters for each
                       /// recursive call.

  struct CraneEnter {
    uint64_t n;
    uint64_t fuel;
  };

  /// CraneCont1: saves [fuel_, n], resumes after recursive call, then processes
  /// rest.
  struct CraneCont1 {
    uint64_t fuel_;
    uint64_t n;
  };

  /// CraneCont2: saves [_tmp2, n], resumes after recursive call, then processes
  /// rest.
  struct CraneCont2 {
    bool _tmp2;
    uint64_t n;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont1, CraneCont2>;
  bool _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{n, fuel});
  /// Loopified bool_or_chain_fuel: CraneEnter -> CraneCont1 -> CraneCont2.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      uint64_t n = _f.n;
      uint64_t fuel = _f.fuel;
      if (fuel <= 0) {
        _result = false;
      } else {
        uint64_t fuel_ = fuel - 1;
        if (n <= UINT64_C(0)) {
          _result = false;
        } else {
          _stack.emplace_back(CraneCont1{fuel_, n});
          _stack.emplace_back(CraneEnter{
              (((n - UINT64_C(1)) > n ? 0 : (n - UINT64_C(1)))), fuel_});
        }
      }
    } else if (std::holds_alternative<CraneCont1>(_frame)) {
      auto _f = std::move(std::get<CraneCont1>(_frame));
      uint64_t fuel_ = _f.fuel_;
      uint64_t n = _f.n;
      _stack.emplace_back(CraneCont2{std::move(_result), n});
      _stack.emplace_back(
          CraneEnter{(((n - UINT64_C(2)) > n ? 0 : (n - UINT64_C(2)))), fuel_});
    } else {
      auto _f = std::move(std::get<CraneCont2>(_frame));
      uint64_t n = _f.n;
      _result = ((n == target || _f._tmp2) || std::move(_result));
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
    uint64_t fuel, uint64_t n) { /// CraneEnter: captures varying parameters for
                                 /// each recursive call.

  struct CraneEnter {
    uint64_t n;
    uint64_t fuel;
  };

  /// CraneCont1: saves [fuel_, n], resumes after recursive call, then processes
  /// rest.
  struct CraneCont1 {
    uint64_t fuel_;
    uint64_t n;
  };

  /// CraneCont2: saves [_tmp2], resumes after recursive call, then processes
  /// rest.
  struct CraneCont2 {
    bool _tmp2;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont1, CraneCont2>;
  bool _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{n, fuel});
  /// Loopified bool_and_chain_fuel: CraneEnter -> CraneCont1 -> CraneCont2.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      uint64_t n = _f.n;
      uint64_t fuel = _f.fuel;
      if (fuel <= 0) {
        _result = true;
      } else {
        uint64_t fuel_ = fuel - 1;
        if (n <= UINT64_C(2)) {
          _result = true;
        } else {
          _stack.emplace_back(CraneCont1{fuel_, n});
          _stack.emplace_back(CraneEnter{
              (((n - UINT64_C(1)) > n ? 0 : (n - UINT64_C(1)))), fuel_});
        }
      }
    } else if (std::holds_alternative<CraneCont1>(_frame)) {
      auto _f = std::move(std::get<CraneCont1>(_frame));
      uint64_t fuel_ = _f.fuel_;
      uint64_t n = _f.n;
      _stack.emplace_back(CraneCont2{std::move(_result)});
      _stack.emplace_back(
          CraneEnter{(((n - UINT64_C(2)) > n ? 0 : (n - UINT64_C(2)))), fuel_});
    } else {
      auto _f = std::move(std::get<CraneCont2>(_frame));
      _result = (_f._tmp2 && std::move(_result));
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
        &t) { /// CraneEnter: captures varying parameters for each recursive
              /// call.

  struct CraneEnter {
    const LoopifyMultiRecursion::quadtree *t;
  };

  /// CraneCont_QQuad: saves [a1, a2, a3], resumes after recursive call, then
  /// processes rest.
  struct CraneCont_QQuad {
    const LoopifyMultiRecursion::quadtree *a1;
    const LoopifyMultiRecursion::quadtree *a2;
    const LoopifyMultiRecursion::quadtree *a3;
  };

  /// CraneCont_QQuad_1: saves [_tmp4, a2, a3], resumes after recursive call,
  /// then processes rest.
  struct CraneCont_QQuad_1 {
    uint64_t _tmp4;
    const LoopifyMultiRecursion::quadtree *a2;
    const LoopifyMultiRecursion::quadtree *a3;
  };

  /// CraneCont_QQuad_2: saves [_tmp3, _tmp4, a3], resumes after recursive call,
  /// then processes rest.
  struct CraneCont_QQuad_2 {
    uint64_t _tmp3;
    uint64_t _tmp4;
    const LoopifyMultiRecursion::quadtree *a3;
  };

  /// CraneCont_QQuad_3: saves [_tmp2, _tmp3, _tmp4], resumes after recursive
  /// call, then processes rest.
  struct CraneCont_QQuad_3 {
    uint64_t _tmp2;
    uint64_t _tmp3;
    uint64_t _tmp4;
  };

  using CraneFrame =
      std::variant<CraneEnter, CraneCont_QQuad, CraneCont_QQuad_1,
                   CraneCont_QQuad_2, CraneCont_QQuad_3>;
  uint64_t _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{&t});
  /// Loopified quad_count_leaves: CraneEnter -> CraneCont_QQuad ->
  /// CraneCont_QQuad_1 -> CraneCont_QQuad_2 -> CraneCont_QQuad_3.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      const LoopifyMultiRecursion::quadtree &t = *_f.t;
      if (std::holds_alternative<
              typename LoopifyMultiRecursion::quadtree::QLeaf>(t.v())) {
        _result = UINT64_C(1);
      } else {
        const auto &[a0, a1, a2, a3] =
            std::get<typename LoopifyMultiRecursion::quadtree::QQuad>(t.v());
        _stack.emplace_back(
            CraneCont_QQuad{crane_raw(a1), crane_raw(a2), crane_raw(a3)});
        _stack.emplace_back(CraneEnter{crane_raw(a0)});
      }
    } else if (std::holds_alternative<CraneCont_QQuad>(_frame)) {
      auto _f = std::move(std::get<CraneCont_QQuad>(_frame));
      const LoopifyMultiRecursion::quadtree &a1 = *_f.a1;
      const LoopifyMultiRecursion::quadtree &a2 = *_f.a2;
      const LoopifyMultiRecursion::quadtree &a3 = *_f.a3;
      _stack.emplace_back(CraneCont_QQuad_1{std::move(_result), &a2, &a3});
      _stack.emplace_back(CraneEnter{&a1});
    } else if (std::holds_alternative<CraneCont_QQuad_1>(_frame)) {
      auto _f = std::move(std::get<CraneCont_QQuad_1>(_frame));
      const LoopifyMultiRecursion::quadtree &a2 = *_f.a2;
      const LoopifyMultiRecursion::quadtree &a3 = *_f.a3;
      _stack.emplace_back(CraneCont_QQuad_2{std::move(_result), _f._tmp4, &a3});
      _stack.emplace_back(CraneEnter{&a2});
    } else if (std::holds_alternative<CraneCont_QQuad_2>(_frame)) {
      auto _f = std::move(std::get<CraneCont_QQuad_2>(_frame));
      const LoopifyMultiRecursion::quadtree &a3 = *_f.a3;
      _stack.emplace_back(
          CraneCont_QQuad_3{std::move(_result), _f._tmp3, _f._tmp4});
      _stack.emplace_back(CraneEnter{&a3});
    } else {
      auto _f = std::move(std::get<CraneCont_QQuad_3>(_frame));
      _result = (((_f._tmp4 + _f._tmp3) + _f._tmp2) + std::move(_result));
    }
  }
  return _result;
}

uint64_t LoopifyMultiRecursion::quad_depth(
    const LoopifyMultiRecursion::quadtree
        &t) { /// CraneEnter: captures varying parameters for each recursive
              /// call.

  struct CraneEnter {
    const LoopifyMultiRecursion::quadtree *t;
  };

  /// CraneCont_QQuad: saves [a1, a2, a3], resumes after recursive call, then
  /// processes rest.
  struct CraneCont_QQuad {
    const LoopifyMultiRecursion::quadtree *a1;
    const LoopifyMultiRecursion::quadtree *a2;
    const LoopifyMultiRecursion::quadtree *a3;
  };

  /// CraneCont_QQuad_1: saves [_tmp4, a2, a3], resumes after recursive call,
  /// then processes rest.
  struct CraneCont_QQuad_1 {
    uint64_t _tmp4;
    const LoopifyMultiRecursion::quadtree *a2;
    const LoopifyMultiRecursion::quadtree *a3;
  };

  /// CraneCont_QQuad_2: saves [_tmp3, _tmp4, a3], resumes after recursive call,
  /// then processes rest.
  struct CraneCont_QQuad_2 {
    uint64_t _tmp3;
    uint64_t _tmp4;
    const LoopifyMultiRecursion::quadtree *a3;
  };

  /// CraneCont_QQuad_3: saves [_tmp2, _tmp3, _tmp4], resumes after recursive
  /// call, then processes rest.
  struct CraneCont_QQuad_3 {
    uint64_t _tmp2;
    uint64_t _tmp3;
    uint64_t _tmp4;
  };

  using CraneFrame =
      std::variant<CraneEnter, CraneCont_QQuad, CraneCont_QQuad_1,
                   CraneCont_QQuad_2, CraneCont_QQuad_3>;
  uint64_t _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{&t});
  /// Loopified quad_depth: CraneEnter -> CraneCont_QQuad -> CraneCont_QQuad_1
  /// -> CraneCont_QQuad_2 -> CraneCont_QQuad_3.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      const LoopifyMultiRecursion::quadtree &t = *_f.t;
      if (std::holds_alternative<
              typename LoopifyMultiRecursion::quadtree::QLeaf>(t.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1, a2, a3] =
            std::get<typename LoopifyMultiRecursion::quadtree::QQuad>(t.v());
        _stack.emplace_back(
            CraneCont_QQuad{crane_raw(a1), crane_raw(a2), crane_raw(a3)});
        _stack.emplace_back(CraneEnter{crane_raw(a0)});
      }
    } else if (std::holds_alternative<CraneCont_QQuad>(_frame)) {
      auto _f = std::move(std::get<CraneCont_QQuad>(_frame));
      const LoopifyMultiRecursion::quadtree &a1 = *_f.a1;
      const LoopifyMultiRecursion::quadtree &a2 = *_f.a2;
      const LoopifyMultiRecursion::quadtree &a3 = *_f.a3;
      _stack.emplace_back(CraneCont_QQuad_1{std::move(_result), &a2, &a3});
      _stack.emplace_back(CraneEnter{&a1});
    } else if (std::holds_alternative<CraneCont_QQuad_1>(_frame)) {
      auto _f = std::move(std::get<CraneCont_QQuad_1>(_frame));
      const LoopifyMultiRecursion::quadtree &a2 = *_f.a2;
      const LoopifyMultiRecursion::quadtree &a3 = *_f.a3;
      _stack.emplace_back(CraneCont_QQuad_2{std::move(_result), _f._tmp4, &a3});
      _stack.emplace_back(CraneEnter{&a2});
    } else if (std::holds_alternative<CraneCont_QQuad_2>(_frame)) {
      auto _f = std::move(std::get<CraneCont_QQuad_2>(_frame));
      const LoopifyMultiRecursion::quadtree &a3 = *_f.a3;
      _stack.emplace_back(
          CraneCont_QQuad_3{std::move(_result), _f._tmp3, _f._tmp4});
      _stack.emplace_back(CraneEnter{&a3});
    } else {
      auto _f = std::move(std::get<CraneCont_QQuad_3>(_frame));
      _result =
          (UINT64_C(1) + std::max(std::max(_f._tmp4, _f._tmp3),
                                  std::max(_f._tmp2, std::move(_result))));
    }
  }
  return _result;
}

uint64_t LoopifyMultiRecursion::hofstadter_q_fuel(
    uint64_t fuel, uint64_t n) { /// CraneEnter: captures varying parameters for
                                 /// each recursive call.

  struct CraneEnter {
    uint64_t n;
    uint64_t fuel;
  };

  /// CraneCont1: saves [fuel_, n], resumes after recursive call, then processes
  /// rest.
  struct CraneCont1 {
    uint64_t fuel_;
    uint64_t n;
  };

  /// CraneCont2: saves [fuel_, n, q1], resumes after recursive call, then
  /// processes rest.
  struct CraneCont2 {
    uint64_t fuel_;
    uint64_t n;
    uint64_t q1;
  };

  /// CraneCont3: saves [fuel_, n, q2], resumes after recursive call, then
  /// processes rest.
  struct CraneCont3 {
    uint64_t fuel_;
    uint64_t n;
    uint64_t q2;
  };

  /// CraneCont4: saves [_tmp2], resumes after recursive call, then processes
  /// rest.
  struct CraneCont4 {
    uint64_t _tmp2;
  };

  using CraneFrame =
      std::variant<CraneEnter, CraneCont1, CraneCont2, CraneCont3, CraneCont4>;
  uint64_t _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{n, fuel});
  /// Loopified hofstadter_q_fuel: CraneEnter -> CraneCont1 -> CraneCont2 ->
  /// CraneCont3 -> CraneCont4.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
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
              _stack.emplace_back(CraneCont1{fuel_, n});
              _stack.emplace_back(CraneEnter{
                  (((n - UINT64_C(1)) > n ? 0 : (n - UINT64_C(1)))), fuel_});
            }
          }
        }
      }
    } else if (std::holds_alternative<CraneCont1>(_frame)) {
      auto _f = std::move(std::get<CraneCont1>(_frame));
      uint64_t fuel_ = _f.fuel_;
      uint64_t n = _f.n;
      uint64_t q1 = std::move(_result);
      _stack.emplace_back(CraneCont2{fuel_, n, q1});
      _stack.emplace_back(
          CraneEnter{(((n - UINT64_C(2)) > n ? 0 : (n - UINT64_C(2)))), fuel_});
    } else if (std::holds_alternative<CraneCont2>(_frame)) {
      auto _f = std::move(std::get<CraneCont2>(_frame));
      uint64_t fuel_ = _f.fuel_;
      uint64_t n = _f.n;
      uint64_t q1 = _f.q1;
      uint64_t q2 = std::move(_result);
      _stack.emplace_back(CraneCont3{fuel_, n, q2});
      _stack.emplace_back(CraneEnter{(((n - q1) > n ? 0 : (n - q1))), fuel_});
    } else if (std::holds_alternative<CraneCont3>(_frame)) {
      auto _f = std::move(std::get<CraneCont3>(_frame));
      uint64_t fuel_ = _f.fuel_;
      uint64_t n = _f.n;
      uint64_t q2 = _f.q2;
      _stack.emplace_back(CraneCont4{std::move(_result)});
      _stack.emplace_back(CraneEnter{(((n - q2) > n ? 0 : (n - q2))), fuel_});
    } else {
      auto _f = std::move(std::get<CraneCont4>(_frame));
      _result = (_f._tmp2 + std::move(_result));
    }
  }
  return _result;
}

uint64_t LoopifyMultiRecursion::hofstadter_q(uint64_t n) {
  return hofstadter_q_fuel(((n * n) + UINT64_C(1)), n);
}
