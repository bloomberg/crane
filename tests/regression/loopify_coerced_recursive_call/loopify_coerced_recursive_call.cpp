#include "loopify_coerced_recursive_call.h"

/// Recursive calls under a coercion, in a function Loopify lowers to a
/// machine with a stack of frames.
///
/// A type-indexed evaluator reads a recursive result at the type its
/// branch gives it, through a coercion: S (eval x), fst (eval p),
/// if eval c.  Normalize bound only the last, and the others stayed
/// ordinary C++ calls inside eval's machine, each running a machine of
/// its own: a succE chain a hundred thousand deep exhausted the stack.
/// Normalize now binds a call under a coercion like any other, the
/// coercion kept around the temporary.  eval returns its result boxed;
/// the temporary of eval x is declared at nat and cast where it is
/// bound, while that of eval p, at the A * B that fstE hides and no
/// C++ type spells, stays the box the coercion opens.
crane::obj
LoopifyCoercedRecursiveCall::eval(const LoopifyCoercedRecursiveCall::expr &e) {
  // Explicit stack replaces the non-tail recursion of eval: _call frames are
  // pending calls, _after frames resume a caller.
  struct _call {
    const LoopifyCoercedRecursiveCall::expr *e;
  };

  struct _after_eval_in_FstE {};

  struct _after_eval_in_Ite {
    const LoopifyCoercedRecursiveCall::expr *a1;
    const LoopifyCoercedRecursiveCall::expr *a2;
  };

  struct _after_eval_in_PairE {
    const LoopifyCoercedRecursiveCall::expr *b;
  };

  struct _after_eval_in_PairE_2 {
    crane::obj _tmp4;
  };

  struct _after_eval_in_SuccE {};

  using _frame = std::variant<_call, _after_eval_in_FstE, _after_eval_in_Ite,
                              _after_eval_in_PairE, _after_eval_in_PairE_2,
                              _after_eval_in_SuccE>;
  crane::obj _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&e});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const LoopifyCoercedRecursiveCall::expr &e = *_f.e;
      if (std::holds_alternative<
              typename LoopifyCoercedRecursiveCall::expr::Lit>(e.v())) {
        const auto &[a0] =
            std::get<typename LoopifyCoercedRecursiveCall::expr::Lit>(e.v());
        _result = std::move(a0);
      } else if (std::holds_alternative<
                     typename LoopifyCoercedRecursiveCall::expr::Bl>(e.v())) {
        const auto &[a0] =
            std::get<typename LoopifyCoercedRecursiveCall::expr::Bl>(e.v());
        _result = std::move(a0);
      } else if (std::holds_alternative<
                     typename LoopifyCoercedRecursiveCall::expr::SuccE>(e.v())) {
        const auto &[a0] =
            std::get<typename LoopifyCoercedRecursiveCall::expr::SuccE>(e.v());
        _stack.emplace_back(_after_eval_in_SuccE{});
        _stack.emplace_back(_call{crane_raw(a0)});
      } else if (std::holds_alternative<
                     typename LoopifyCoercedRecursiveCall::expr::Ite>(e.v())) {
        const auto &[a, a1, a2] =
            std::get<typename LoopifyCoercedRecursiveCall::expr::Ite>(e.v());
        _stack.emplace_back(_after_eval_in_Ite{crane_raw(a1), crane_raw(a2)});
        _stack.emplace_back(_call{crane_raw(a)});
      } else if (std::holds_alternative<
                     typename LoopifyCoercedRecursiveCall::expr::PairE>(e.v())) {
        const auto &[a, b] =
            std::get<typename LoopifyCoercedRecursiveCall::expr::PairE>(e.v());
        _stack.emplace_back(_after_eval_in_PairE{crane_raw(b)});
        _stack.emplace_back(_call{crane_raw(a)});
      } else {
        const auto &[a] =
            std::get<typename LoopifyCoercedRecursiveCall::expr::FstE>(e.v());
        _stack.emplace_back(_after_eval_in_FstE{});
        _stack.emplace_back(_call{crane_raw(a)});
      }
    } else if (std::holds_alternative<_after_eval_in_FstE>(_popped)) {
      auto _f = std::move(std::get<_after_eval_in_FstE>(_popped));
      _stack.pop_back();
      _result =
          crane::any_cast<std::pair<crane::obj, crane::obj>>(std::move(_result)).first;
    } else if (std::holds_alternative<_after_eval_in_Ite>(_popped)) {
      auto _f = std::move(std::get<_after_eval_in_Ite>(_popped));
      _stack.pop_back();
      const LoopifyCoercedRecursiveCall::expr &a1 = *_f.a1;
      const LoopifyCoercedRecursiveCall::expr &a2 = *_f.a2;
      if (crane::any_cast<bool>(std::move(_result))) {
        _stack.emplace_back(_call{&a1});
      } else {
        _stack.emplace_back(_call{&a2});
      }
    } else if (std::holds_alternative<_after_eval_in_PairE>(_popped)) {
      auto _f = std::move(std::get<_after_eval_in_PairE>(_popped));
      _stack.pop_back();
      const LoopifyCoercedRecursiveCall::expr &b = *_f.b;
      _stack.emplace_back(_after_eval_in_PairE_2{std::move(_result)});
      _stack.emplace_back(_call{&b});
    } else if (std::holds_alternative<_after_eval_in_PairE_2>(_popped)) {
      auto _f = std::move(std::get<_after_eval_in_PairE_2>(_popped));
      _stack.pop_back();
      _result = std::make_pair(crane::obj(std::move(_f._tmp4)),
                               crane::obj(std::move(_result)));
    } else {
      auto _f = std::move(std::get<_after_eval_in_SuccE>(_popped));
      _stack.pop_back();
      _result = (crane::any_cast<uint64_t>(std::move(_result)) + 1);
    }
  }
  return _result;
}
