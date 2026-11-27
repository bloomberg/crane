#include "loopify_existential_recursive_call.h"

/// Recursive calls at a constructor's existential types, read at the
/// function's own result type, in a function Loopify lowers to a machine
/// with a stack of frames.
///
/// In (eval x, eval y) each call is at a type pairE hides, which no
/// C++ type spells, so only the box eval returns can hold its value.
/// The pair reads it at eval's own result type A, and translation read
/// a boxed temporary at A by casting it to eval's template parameter,
/// which in a machine is the outermost call's: a bool component would
/// have been cast to the nat of the whole.  So Normalize left these calls
/// in place, ordinary C++ calls inside eval's machine, and a
/// fstE/pairE nest a hundred thousand deep exhausted the stack.  Such a
/// temporary now stays the box, and the calls are bound and resumed like
/// any other.  (fst (eval p) reads its call through a coercion into a
/// pair: see regression/loopify_coerced_recursive_call.)
crane::obj LoopifyExistentialRecursiveCall::eval(
    const LoopifyExistentialRecursiveCall::expr &e) {
  // Explicit stack replaces the non-tail recursion of eval: _call frames are
  // pending calls, _after frames resume a caller.
  struct _call {
    const LoopifyExistentialRecursiveCall::expr *e;
  };

  struct _after_eval_in_FstE {};

  struct _after_eval_in_Ite {
    const LoopifyExistentialRecursiveCall::expr *a1;
    const LoopifyExistentialRecursiveCall::expr *a2;
  };

  struct _after_eval_in_PairE {
    const LoopifyExistentialRecursiveCall::expr *b;
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
      const LoopifyExistentialRecursiveCall::expr &e = *_f.e;
      if (std::holds_alternative<
              typename LoopifyExistentialRecursiveCall::expr::Lit>(e.v())) {
        const auto &[a0] = std::get<
            typename LoopifyExistentialRecursiveCall::expr::Lit>(e.v());
        _result = std::move(a0);
      } else if (std::holds_alternative<
                     typename LoopifyExistentialRecursiveCall::expr::Bl>(e.v())) {
        const auto &[a0] =
            std::get<typename LoopifyExistentialRecursiveCall::expr::Bl>(e.v());
        _result = std::move(a0);
      } else if (
          std::holds_alternative<
              typename LoopifyExistentialRecursiveCall::expr::SuccE>(e.v())) {
        const auto &[a0] =
            std::get<typename LoopifyExistentialRecursiveCall::expr::SuccE>(
                e.v());
        _stack.emplace_back(_after_eval_in_SuccE{});
        _stack.emplace_back(_call{crane_raw(a0)});
      } else if (
          std::holds_alternative<
              typename LoopifyExistentialRecursiveCall::expr::Ite>(e.v())) {
        const auto &[a, a1, a2] = std::get<
            typename LoopifyExistentialRecursiveCall::expr::Ite>(e.v());
        _stack.emplace_back(_after_eval_in_Ite{crane_raw(a1), crane_raw(a2)});
        _stack.emplace_back(_call{crane_raw(a)});
      } else if (
          std::holds_alternative<
              typename LoopifyExistentialRecursiveCall::expr::PairE>(e.v())) {
        const auto &[a, b] =
            std::get<typename LoopifyExistentialRecursiveCall::expr::PairE>(
                e.v());
        _stack.emplace_back(_after_eval_in_PairE{crane_raw(b)});
        _stack.emplace_back(_call{crane_raw(a)});
      } else {
        const auto &[a] =
            std::get<typename LoopifyExistentialRecursiveCall::expr::FstE>(
                e.v());
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
      const LoopifyExistentialRecursiveCall::expr &a1 = *_f.a1;
      const LoopifyExistentialRecursiveCall::expr &a2 = *_f.a2;
      if (crane::any_cast<bool>(std::move(_result))) {
        _stack.emplace_back(_call{&a1});
      } else {
        _stack.emplace_back(_call{&a2});
      }
    } else if (std::holds_alternative<_after_eval_in_PairE>(_popped)) {
      auto _f = std::move(std::get<_after_eval_in_PairE>(_popped));
      _stack.pop_back();
      const LoopifyExistentialRecursiveCall::expr &b = *_f.b;
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
