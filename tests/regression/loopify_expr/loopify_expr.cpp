#include <loopify_expr.h>

#include <algorithm>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

/// sum_shapes l sums values from shapes using unified pattern.
/// Tests or-pattern style matching in Coq.
__attribute__((pure)) unsigned int LoopifyExpr::sum_shapes(
    const std::shared_ptr<List<std::shared_ptr<LoopifyExpr::shape>>> &l) {
  struct _Enter {
    const std::shared_ptr<List<std::shared_ptr<LoopifyExpr::shape>>> l;
  };

  struct _Call1 {
    unsigned int _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.emplace_back(_Enter{l});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      const auto &_f = std::get<_Enter>(_frame);
      const std::shared_ptr<List<std::shared_ptr<LoopifyExpr::shape>>> l = _f.l;
      if (std::holds_alternative<
              typename List<std::shared_ptr<LoopifyExpr::shape>>::Nil>(
              l->v())) {
        _result = 0u;
      } else {
        const auto &_m = *std::get_if<
            typename List<std::shared_ptr<LoopifyExpr::shape>>::Cons>(&l->v());
        unsigned int val = [&]() {
          auto &&_sv0 = _m.d_a0;
          if (std::holds_alternative<typename LoopifyExpr::shape::Circle>(
                  _sv0->v())) {
            const auto &_m0 =
                *std::get_if<typename LoopifyExpr::shape::Circle>(&_sv0->v());
            return _m0.d_a0;
          } else if (std::holds_alternative<
                         typename LoopifyExpr::shape::Square>(_sv0->v())) {
            const auto &_m0 =
                *std::get_if<typename LoopifyExpr::shape::Square>(&_sv0->v());
            return _m0.d_a0;
          } else {
            const auto &_m0 =
                *std::get_if<typename LoopifyExpr::shape::Triangle>(&_sv0->v());
            return _m0.d_a0;
          }
        }();
        _stack.emplace_back(_Call1{val});
        _stack.emplace_back(_Enter{_m.d_a1});
      }
    } else {
      const auto &_f = std::get<_Call1>(_frame);
      _result = (_f._s0 + _result);
    }
  }
  return _result;
}

/// count_by_shape l counts shapes: (circles, squares, triangles).
__attribute__((pure))
std::pair<std::pair<unsigned int, unsigned int>, unsigned int>
LoopifyExpr::count_by_shape(
    const std::shared_ptr<List<std::shared_ptr<LoopifyExpr::shape>>> &l) {
  struct _Enter {
    const std::shared_ptr<List<std::shared_ptr<LoopifyExpr::shape>>> l;
  };

  struct _Call1 {
    const typename List<std::shared_ptr<LoopifyExpr::shape>>::Cons _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::pair<std::pair<unsigned int, unsigned int>, unsigned int> _result{};
  std::vector<_Frame> _stack;
  _stack.emplace_back(_Enter{l});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      const auto &_f = std::get<_Enter>(_frame);
      const std::shared_ptr<List<std::shared_ptr<LoopifyExpr::shape>>> l = _f.l;
      if (std::holds_alternative<
              typename List<std::shared_ptr<LoopifyExpr::shape>>::Nil>(
              l->v())) {
        _result = std::make_pair(std::make_pair(0u, 0u), 0u);
      } else {
        const auto &_m = *std::get_if<
            typename List<std::shared_ptr<LoopifyExpr::shape>>::Cons>(&l->v());
        _stack.emplace_back(_Call1{_m});
        _stack.emplace_back(_Enter{_m.d_a1});
      }
    } else {
      const auto &_f = std::get<_Call1>(_frame);
      const typename List<std::shared_ptr<LoopifyExpr::shape>>::Cons _m =
          _f._s0;
      const std::pair<unsigned int, unsigned int> &p = _result.first;
      const unsigned int &t = _result.second;
      const unsigned int &c = p.first;
      const unsigned int &sq = p.second;
      auto &&_sv = _m.d_a0;
      if (std::holds_alternative<typename LoopifyExpr::shape::Circle>(
              _sv->v())) {
        _result = std::make_pair(std::make_pair((c + 1), sq), t);
      } else if (std::holds_alternative<typename LoopifyExpr::shape::Square>(
                     _sv->v())) {
        _result = std::make_pair(std::make_pair(c, (sq + 1)), t);
      } else {
        _result = std::make_pair(std::make_pair(c, sq), (t + 1));
      }
    }
  }
  return _result;
}
