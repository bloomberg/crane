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
