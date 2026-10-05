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
  LoopifyReuseBoolQualified::lst _loop_acc = std::move(acc);
  uint64_t _loop_n = n;
  while (true) {
    if (_loop_n <= 0) {
      return _loop_acc;
    } else {
      uint64_t m = _loop_n - 1;
      uint64_t _next_n = m;
      _loop_acc = lst::cons(_loop_n, std::move(_loop_acc));
      _loop_n = _next_n;
    }
  }
}

uint64_t
LoopifyReuseBoolQualified::sum(const LoopifyReuseBoolQualified::lst &l) {
  {
    const LoopifyReuseBoolQualified::lst &_lc1_l0 = l;
    uint64_t _lc1_acc = UINT64_C(0);
    uint64_t _lc1_loop_acc = _lc1_acc;
    const LoopifyReuseBoolQualified::lst *_lc1_loop_l0 = &_lc1_l0;
    while (true) {
      if (std::holds_alternative<typename LoopifyReuseBoolQualified::lst::Nil>(
              _lc1_loop_l0->v())) {
        return _lc1_loop_acc;
      } else {
        const auto &[a0, a1] =
            std::get<typename LoopifyReuseBoolQualified::lst::Cons>(
                _lc1_loop_l0->v());
        _lc1_loop_acc = (_lc1_loop_acc + a0);
        _lc1_loop_l0 = crane_raw(a1);
      }
    }
  }
}

LoopifyReuseBoolQualified::lst
LoopifyReuseBoolQualified::incr(LoopifyReuseBoolQualified::lst l) {
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
      auto _cell = crane::make_rc_reusing_unchecked(
          std::move(_rs.token), typename LoopifyReuseBoolQualified::lst::Cons(
                                    (a0 + UINT64_C(1)), nullptr));
      *_write = std::move(_cell);
      _write = &std::get<typename LoopifyReuseBoolQualified::lst::Cons>(
                    (*_write)->v_mut())
                    .a1;
      _own = std::move(std::move(_rs.next));
      _loop_l = _own.get();
      continue;
    }
  }
  return std::move(*_head);
}

uint64_t LoopifyReuseBoolQualified::go(uint64_t n) {
  return sum(incr(build(n, lst::nil())));
}
