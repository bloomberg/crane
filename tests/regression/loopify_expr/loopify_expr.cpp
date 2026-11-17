#include "loopify_expr.h"

/// sum_shapes l sums values from shapes using unified pattern.
/// Tests or-pattern style matching in Coq.
uint64_t LoopifyExpr::sum_shapes(const List<LoopifyExpr::shape> &l) {
  // Explicit stack replaces the non-tail recursion of sum_shapes: _call frames
  // are pending calls, _after frames resume a caller.
  struct _call {
    const List<LoopifyExpr::shape> *l;
  };

  struct _after_sum_shapes_in_Cons {
    uint64_t val;
  };

  using _frame = std::variant<_call, _after_sum_shapes_in_Cons>;
  uint64_t _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&l});
  while (!_stack.empty()) {
    _frame _popped = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      const List<LoopifyExpr::shape> &l = *_f.l;
      if (std::holds_alternative<typename List<LoopifyExpr::shape>::Nil>(l.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] =
            std::get<typename List<LoopifyExpr::shape>::Cons>(l.v());
        uint64_t val = [&]() {
          if (std::holds_alternative<typename LoopifyExpr::shape::Circle>(
                  a0.v())) {
            const auto &[a00] =
                std::get<typename LoopifyExpr::shape::Circle>(a0.v());
            return a00;
          } else if (
              std::holds_alternative<typename LoopifyExpr::shape::Square>(
                  a0.v())) {
            const auto &[a00] =
                std::get<typename LoopifyExpr::shape::Square>(a0.v());
            return a00;
          } else {
            const auto &[a00] =
                std::get<typename LoopifyExpr::shape::Triangle>(a0.v());
            return a00;
          }
        }();
        _stack.emplace_back(_after_sum_shapes_in_Cons{val});
        _stack.emplace_back(_call{crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<_after_sum_shapes_in_Cons>(_popped));
      uint64_t val = _f.val;
      _result = (val + std::move(_result));
    }
  }
  return _result;
}

/// count_by_shape l counts shapes: (circles, squares, triangles).
std::pair<std::pair<uint64_t, uint64_t>, uint64_t>
LoopifyExpr::count_by_shape(const List<LoopifyExpr::shape> &l) {
  // Explicit stack replaces the non-tail recursion of count_by_shape: _call
  // frames are pending calls, _after frames resume a caller.
  struct _call {
    const List<LoopifyExpr::shape> *l;
  };

  struct _after_count_by_shape_in_Cons {
    LoopifyExpr::shape a0;
  };

  using _frame = std::variant<_call, _after_count_by_shape_in_Cons>;
  std::pair<std::pair<uint64_t, uint64_t>, uint64_t> _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&l});
  while (!_stack.empty()) {
    _frame _popped = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      const List<LoopifyExpr::shape> &l = *_f.l;
      if (std::holds_alternative<typename List<LoopifyExpr::shape>::Nil>(l.v())) {
        _result = std::make_pair(std::make_pair(UINT64_C(0), UINT64_C(0)),
                                 UINT64_C(0));
      } else {
        const auto &[a0, a1] =
            std::get<typename List<LoopifyExpr::shape>::Cons>(l.v());
        _stack.emplace_back(_after_count_by_shape_in_Cons{a0});
        _stack.emplace_back(_call{crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<_after_count_by_shape_in_Cons>(_popped));
      LoopifyExpr::shape a0 = std::move(_f.a0);
      std::pair<std::pair<uint64_t, uint64_t>, uint64_t> _tmp1 =
          std::move(_result);
      const auto &[p, t] = _tmp1;
      const auto &[c, sq] = p;
      if (std::holds_alternative<typename LoopifyExpr::shape::Circle>(
              a0.v_mut())) {
        _result = std::make_pair(std::make_pair((c + 1), sq), t);
      } else if (std::holds_alternative<typename LoopifyExpr::shape::Square>(
                     a0.v_mut())) {
        _result = std::make_pair(std::make_pair(c, (sq + 1)), t);
      } else {
        _result = std::make_pair(std::make_pair(c, sq), (t + 1));
      }
    }
  }
  return _result;
}
