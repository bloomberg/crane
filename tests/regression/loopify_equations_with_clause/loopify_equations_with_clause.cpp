#include "loopify_equations_with_clause.h"

uint64_t LoopifyEquationsWithClause::zeros(const List<uint64_t> &x) {
  // Explicit stack replaces the non-tail recursion of zeros: _call frames are
  // pending calls, _after frames resume a caller.
  struct _call {
    const List<uint64_t> *x;
  };

  struct _after_zeros_in_true {};

  using _frame = std::variant<_call, _after_zeros_in_true>;
  uint64_t _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&x});
  while (!_stack.empty()) {
    _frame _popped = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      const List<uint64_t> &x = *_f.x;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(x.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(x.v());
        if (a0 == UINT64_C(0)) {
          _stack.emplace_back(_after_zeros_in_true{});
          _stack.emplace_back(_call{crane_raw(a1)});
        } else {
          _stack.emplace_back(_call{crane_raw(a1)});
        }
      }
    } else {
      auto _f = std::move(std::get<_after_zeros_in_true>(_popped));
      _result = (std::move(_result) + 1);
    }
  }
  return _result;
}

uint64_t
LoopifyEquationsWithClause::zeros_unfold_clause_2(uint64_t, bool refine,
                                                  const List<uint64_t> &xs) {
  if (refine) {
    return (zeros(xs) + 1);
  } else {
    return zeros(xs);
  }
}

uint64_t LoopifyEquationsWithClause::zeros_unfold(const List<uint64_t> &l) {
  if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
    return UINT64_C(0);
  } else {
    const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
    return zeros_unfold_clause_2(a0, a0 == UINT64_C(0), *a1);
  }
}

LoopifyEquationsWithClause::zeros_graph
LoopifyEquationsWithClause::zeros_graph_correct(const List<uint64_t> &x) {
  if (std::holds_alternative<typename List<uint64_t>::Nil>(x.v())) {
    return zeros_graph::zeros_graph_equation_1();
  } else {
    const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(x.v());
    return zeros_graph::zeros_graph_refinement_2(a0, *a1, [&]() {
      bool refine = a0 == UINT64_C(0);
      if (refine) {
        return zeros_clause_2_graph::zeros_clause_2_graph_equation_1(
            a0, *a1, zeros_graph_correct(*a1));
      } else {
        return zeros_clause_2_graph::zeros_clause_2_graph_equation_2(
            a0, *a1, zeros_graph_correct(*a1));
      }
    }());
  }
}

uint64_t LoopifyEquationsWithClause::plain(const List<uint64_t> &x) {
  // Explicit stack replaces the non-tail recursion of plain: _call frames are
  // pending calls, _after frames resume a caller.
  struct _call {
    const List<uint64_t> *x;
  };

  struct _after_plain_in_Cons {
    uint64_t a0;
  };

  using _frame = std::variant<_call, _after_plain_in_Cons>;
  uint64_t _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&x});
  while (!_stack.empty()) {
    _frame _popped = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      const List<uint64_t> &x = *_f.x;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(x.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(x.v());
        _stack.emplace_back(_after_plain_in_Cons{a0});
        _stack.emplace_back(_call{crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<_after_plain_in_Cons>(_popped));
      uint64_t a0 = _f.a0;
      _result = (a0 + std::move(_result));
    }
  }
  return _result;
}

uint64_t LoopifyEquationsWithClause::plain_unfold(const List<uint64_t> &l) {
  if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
    return UINT64_C(0);
  } else {
    const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
    return (a0 + plain(*a1));
  }
}

LoopifyEquationsWithClause::plain_graph
LoopifyEquationsWithClause::plain_graph_correct(const List<uint64_t> &x) {
  // Builds the result front to back: _write points at the empty tail the next
  // cell fills.
  std::optional<LoopifyEquationsWithClause::plain_graph> _root{};
  std::shared_ptr<LoopifyEquationsWithClause::plain_graph> *_write = nullptr;
  const List<uint64_t> *_loop_x = &x;
  while (true) {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_x->v())) {
      auto _value = plain_graph::plain_graph_equation_1();
      (_write ? *(*_write =
                      std::make_shared<LoopifyEquationsWithClause::plain_graph>(
                          std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename List<uint64_t>::Cons>(_loop_x->v());
      auto _cell =
          typename LoopifyEquationsWithClause::plain_graph::Plain_graph_equation_2(
              a0, *a1, nullptr);
      LoopifyEquationsWithClause::plain_graph &_node =
          (_write ? *(*_write = std::make_shared<
                          LoopifyEquationsWithClause::plain_graph>(
                          std::move(_cell)))
                  : _root.emplace(std::move(_cell)));
      _write =
          &std::get<
              typename LoopifyEquationsWithClause::plain_graph::Plain_graph_equation_2>(
              _node.v_mut())
              .hind;
      _loop_x = crane_raw(a1);
      continue;
    }
  }
  return std::move(*_root);
}
