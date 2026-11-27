#include "loopify_reuse_bool_qualified.h"

/// Codegen bug: the generated C++ does not compile.
///
/// With Loopify + Reuse + NonAtomicRc all on, the TMC loop emits a
/// reuse-uniqueness latch
///
/// LoopifyReuseBoolQualified::bool _uniq = true;   <-- qualified bool
///
/// inside the extracted module's namespace, so clang rejects it with
/// "expected unqualified-id" and every later use of _uniq is an
/// undeclared identifier.
///
/// Root cause: src/loopify.ml:3406 declares the latch with
/// Tid (Id.of_string "bool", []). Tid is the *user-defined* type
/// constructor, so the printer prefixes it with the current module
/// namespace; a builtin needs a raw type instead.
///
/// Any TMC-shaped fixpoint triggers it. All three options are required:
/// dropping Set Crane Reuse. removes the latch and the file compiles.
LoopifyReuseBoolQualified::lst
LoopifyReuseBoolQualified::build(uint64_t n,
                                 LoopifyReuseBoolQualified::lst acc) {
  // Loop replaces the tail recursion: each recursive call updates the loop
  // variables.
  LoopifyReuseBoolQualified::lst _loop_acc = std::move(acc);
  while (true) {
    if (n <= 0) {
      return _loop_acc;
    } else {
      uint64_t m = n - 1;
      uint64_t _next_n = m;
      _loop_acc = lst::cons(n, std::move(_loop_acc));
      n = _next_n;
    }
  }
}

uint64_t
LoopifyReuseBoolQualified::sum(const LoopifyReuseBoolQualified::lst &l) {
  // Explicit stack replaces the non-tail recursion of sum: _call frames are
  // pending calls, _after frames resume a caller.
  struct _call {
    const LoopifyReuseBoolQualified::lst *l;
  };

  struct _after_sum_in_Cons {
    uint64_t a0;
  };

  using _frame = std::variant<_call, _after_sum_in_Cons>;
  uint64_t _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&l});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const LoopifyReuseBoolQualified::lst &l = *_f.l;
      if (std::holds_alternative<typename LoopifyReuseBoolQualified::lst::Nil>(
              l.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] =
            std::get<typename LoopifyReuseBoolQualified::lst::Cons>(l.v());
        _stack.emplace_back(_after_sum_in_Cons{a0});
        _stack.emplace_back(_call{crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<_after_sum_in_Cons>(_popped));
      _stack.pop_back();
      uint64_t a0 = _f.a0;
      _result = a0 + _result;
    }
  }
  return _result;
}

LoopifyReuseBoolQualified::lst
LoopifyReuseBoolQualified::incr(LoopifyReuseBoolQualified::lst l) {
  // Builds the result front to back: _write points at the empty tail the next
  // cell fills. The input's cells are reused in place while uniquely owned.
  crane::rc<LoopifyReuseBoolQualified::lst> _head{};
  crane::rc<LoopifyReuseBoolQualified::lst> *_write = &_head;
  crane::rc<LoopifyReuseBoolQualified::lst> _own =
      crane::rc<LoopifyReuseBoolQualified::lst>();
  bool _uniq = true;
  const LoopifyReuseBoolQualified::lst *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<typename LoopifyReuseBoolQualified::lst::Nil>(
            _loop_l->v())) {
      *_write = crane::make_rc<LoopifyReuseBoolQualified::lst>(lst::nil());
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename LoopifyReuseBoolQualified::lst::Cons>(_loop_l->v());
      auto _rs = crane::reuse_step(_own, _uniq, a1);
      *_write = crane::make_rc_reusing_unchecked(
          std::move(_rs.token), typename LoopifyReuseBoolQualified::lst::Cons(
                                    a0 + UINT64_C(1), nullptr));
      _write =
          &std::get<typename LoopifyReuseBoolQualified::lst::Cons>(
              (*_write)->v_mut())
              .a1;
      _own = std::move(_rs.next);
      _loop_l = _own.get();
      continue;
    }
  }
  return std::move(*_head);
}

uint64_t LoopifyReuseBoolQualified::go(uint64_t n) {
  return sum(incr(build(n, lst::nil())));
}
