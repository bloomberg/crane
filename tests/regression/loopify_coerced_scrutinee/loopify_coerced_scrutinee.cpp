#include "loopify_coerced_scrutinee.h"

/// A recursive call matched through a coercion is bound before the match,
/// as one matched directly is.
///
/// In a type-indexed evaluator if eval c then ... reads the call through a
/// coercion to bool, since eval returns its index erased.  Normalize left
/// anything under a coercion where it stood, so the plan had no point to
/// resume at, and Loopify bound the call itself, in a variable the plan knew
/// nothing of.  Normalize now binds it; the continuation casts the result of
/// the call it re-enters by.
crane::obj
LoopifyCoercedScrutinee::eval(const LoopifyCoercedScrutinee::expr &e) {
  // Explicit stack replaces the non-tail recursion of eval: _call frames are
  // pending calls, _after frames resume a caller.
  struct _call {
    const LoopifyCoercedScrutinee::expr *e;
  };

  struct _after_eval_in_Iszero {};

  struct _after_eval_in_Ite {
    const LoopifyCoercedScrutinee::expr *a1;
    const LoopifyCoercedScrutinee::expr *a2;
  };

  using _frame = std::variant<_call, _after_eval_in_Iszero, _after_eval_in_Ite>;
  crane::obj _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&e});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const LoopifyCoercedScrutinee::expr &e = *_f.e;
      if (std::holds_alternative<typename LoopifyCoercedScrutinee::expr::Lit>(
              e.v())) {
        const auto &[a0] =
            std::get<typename LoopifyCoercedScrutinee::expr::Lit>(e.v());
        _result = std::move(a0);
      } else if (
          std::holds_alternative<typename LoopifyCoercedScrutinee::expr::Bl>(
              e.v())) {
        const auto &[a0] =
            std::get<typename LoopifyCoercedScrutinee::expr::Bl>(e.v());
        _result = std::move(a0);
      } else if (
          std::holds_alternative<typename LoopifyCoercedScrutinee::expr::Ite>(
              e.v())) {
        const auto &[a, a1, a2] =
            std::get<typename LoopifyCoercedScrutinee::expr::Ite>(e.v());
        _stack.emplace_back(_after_eval_in_Ite{crane_raw(a1), crane_raw(a2)});
        _stack.emplace_back(_call{crane_raw(a)});
      } else {
        const auto &[a0] =
            std::get<typename LoopifyCoercedScrutinee::expr::Iszero>(e.v());
        _stack.emplace_back(_after_eval_in_Iszero{});
        _stack.emplace_back(_call{crane_raw(a0)});
      }
    } else if (std::holds_alternative<_after_eval_in_Iszero>(_popped)) {
      auto _f = std::move(std::get<_after_eval_in_Iszero>(_popped));
      _stack.pop_back();
      _result = crane::any_cast<uint64_t>(std::move(_result)) == UINT64_C(0);
    } else {
      auto _f = std::move(std::get<_after_eval_in_Ite>(_popped));
      _stack.pop_back();
      const LoopifyCoercedScrutinee::expr &a1 = *_f.a1;
      const LoopifyCoercedScrutinee::expr &a2 = *_f.a2;
      if (crane::any_cast<bool>(std::move(_result))) {
        _stack.emplace_back(_call{&a1});
      } else {
        _stack.emplace_back(_call{&a2});
      }
    }
  }
  return _result;
}

/// n conditionals, each taking its else branch until the innermost.
LoopifyCoercedScrutinee::expr LoopifyCoercedScrutinee::nest(uint64_t n) {
  // Builds the result front to back: _write points at the empty tail the next
  // cell fills.
  std::optional<LoopifyCoercedScrutinee::expr> _root{};
  std::shared_ptr<LoopifyCoercedScrutinee::expr> *_write = nullptr;
  while (true) {
    if (n <= 0) {
      auto _value = expr::lit(UINT64_C(7));
      (_write ? *(*_write = std::make_shared<LoopifyCoercedScrutinee::expr>(
                      std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      uint64_t m = n - 1;
      auto _cell = typename LoopifyCoercedScrutinee::expr::Ite(
          std::make_shared<LoopifyCoercedScrutinee::expr>(
              expr::iszero(expr::lit((m + 1)))),
          std::make_shared<LoopifyCoercedScrutinee::expr>(
              expr::lit(UINT64_C(1))),
          nullptr);
      LoopifyCoercedScrutinee::expr &_node =
          (_write ? *(*_write = std::make_shared<LoopifyCoercedScrutinee::expr>(
                          std::move(_cell)))
                  : _root.emplace(std::move(_cell)));
      _write =
          &std::get<typename LoopifyCoercedScrutinee::expr::Ite>(_node.v_mut()).a2;
      n = m;
      continue;
    }
  }
  return std::move(*_root);
}
