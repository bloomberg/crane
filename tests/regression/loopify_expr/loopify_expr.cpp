#include <loopify_expr.h>

/// sum_shapes l sums values from shapes using unified pattern.
/// Tests or-pattern style matching in Coq.
__attribute__((pure)) unsigned int
LoopifyExpr::sum_shapes(const List<LoopifyExpr::shape> &l) {
  struct _Enter {
    const List<LoopifyExpr::shape> *l;
  };

  struct _Call1 {
    unsigned int _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{&l});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<LoopifyExpr::shape> &l = *(_f.l);
      if (std::holds_alternative<typename List<LoopifyExpr::shape>::Nil>(
              l.v())) {
        _result = 0u;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<LoopifyExpr::shape>::Cons>(l.v());
        unsigned int val = [&]() {
          if (std::holds_alternative<typename LoopifyExpr::shape::Circle>(
                  d_a0.v())) {
            const auto &[d_a00] =
                std::get<typename LoopifyExpr::shape::Circle>(d_a0.v());
            return d_a00;
          } else if (std::holds_alternative<
                         typename LoopifyExpr::shape::Square>(d_a0.v())) {
            const auto &[d_a00] =
                std::get<typename LoopifyExpr::shape::Square>(d_a0.v());
            return d_a00;
          } else {
            const auto &[d_a00] =
                std::get<typename LoopifyExpr::shape::Triangle>(d_a0.v());
            return d_a00;
          }
        }();
        _stack.emplace_back(_Call1{val});
        _stack.emplace_back(_Enter{d_a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Call1>(_frame));
      _result = (_f._s0 + _result);
    }
  }
  return _result;
}

/// count_by_shape l counts shapes: (circles, squares, triangles).
__attribute__((pure))
std::pair<std::pair<unsigned int, unsigned int>, unsigned int>
LoopifyExpr::count_by_shape(const List<LoopifyExpr::shape> &l) {
  struct _Enter {
    const List<LoopifyExpr::shape> *l;
  };

  struct _Call1 {
    LoopifyExpr::shape _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::pair<std::pair<unsigned int, unsigned int>, unsigned int> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{&l});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<LoopifyExpr::shape> &l = *(_f.l);
      if (std::holds_alternative<typename List<LoopifyExpr::shape>::Nil>(
              l.v())) {
        _result = std::make_pair(std::make_pair(0u, 0u), 0u);
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<LoopifyExpr::shape>::Cons>(l.v());
        _stack.emplace_back(_Call1{d_a0});
        _stack.emplace_back(_Enter{d_a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Call1>(_frame));
      LoopifyExpr::shape d_a0 = _f._s0;
      const std::pair<unsigned int, unsigned int> &p = _result.first;
      const unsigned int &t = _result.second;
      const unsigned int &c = p.first;
      const unsigned int &sq = p.second;
      if (std::holds_alternative<typename LoopifyExpr::shape::Circle>(
              d_a0.v())) {
        _result = std::make_pair(std::make_pair((c + 1), sq), t);
      } else if (std::holds_alternative<typename LoopifyExpr::shape::Square>(
                     d_a0.v())) {
        _result = std::make_pair(std::make_pair(c, (sq + 1)), t);
      } else {
        _result = std::make_pair(std::make_pair(c, sq), (t + 1));
      }
    }
  }
  return _result;
}
