#include "loopify_frame_ptr_escape.h"

/// KNOWN BUG: use-after-free in a loopified *non-tail* recursive function.
///
/// walk is not tail recursive, so loopification builds an explicit frame
/// stack. Within one _Enter frame, the two list parameters again get
/// different representations:
///
/// struct _Enter { const lst *acc; lst l; uint64_t n; };
///
/// acc is a raw pointer (it is always passed a sub-field), l is owned by
/// value (it is sometimes given a freshly built value). The recursive call
/// pushes
///
/// _stack.emplace_back(_Enter{
/// crane_raw(a1), // points INTO this frame's l
/// lst::cons(m + 1, lst::cons(m, lst::nil())),      // fresh l for the callee
/// m});
///
/// The acc pointer aliases a cell owned by the *current* iteration's
/// _f.l. _f is a loop-body local, so it is destroyed at the end of the
/// iteration, dropping the last reference to that cell. The frame just pushed
/// keeps the now-dangling pointer and dereferences it later via hd acc.
///
/// Expected: go 4 = 15 (checked with Compute in Rocq).
/// Actual:   14, plus an ASan heap-use-after-free.
///
/// Without Set Crane Loopify the same file extracts to correct code.
uint64_t LoopifyFramePtrEscape::hd(const LoopifyFramePtrEscape::lst &l) {
  if (std::holds_alternative<typename LoopifyFramePtrEscape::lst::Nil>(l.v())) {
    return UINT64_C(0);
  } else {
    const auto &[a0, _] =
        std::get<typename LoopifyFramePtrEscape::lst::Cons>(l.v());
    return a0;
  }
}

uint64_t LoopifyFramePtrEscape::walk(uint64_t n,
                                     const LoopifyFramePtrEscape::lst &l,
                                     const LoopifyFramePtrEscape::lst &acc) {
  // Explicit stack replaces the non-tail recursion of walk: _call frames are
  // pending calls, _after frames resume a caller.
  struct _call {
    LoopifyFramePtrEscape::lst acc;
    LoopifyFramePtrEscape::lst l;
    uint64_t n;
  };

  struct _after_walk_in_Cons {
    uint64_t a0;
  };

  using _frame = std::variant<_call, _after_walk_in_Cons>;
  uint64_t _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{acc, l, n});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      LoopifyFramePtrEscape::lst acc = std::move(_f.acc);
      const LoopifyFramePtrEscape::lst &l = _f.l;
      uint64_t n = _f.n;
      if (n <= 0) {
        _result = hd(std::move(acc));
      } else {
        uint64_t m = n - 1;
        if (std::holds_alternative<typename LoopifyFramePtrEscape::lst::Nil>(
                l.v())) {
          _result = UINT64_C(0);
        } else {
          const auto &[a0, a1] =
              std::get<typename LoopifyFramePtrEscape::lst::Cons>(l.v());
          _stack.emplace_back(_after_walk_in_Cons{a0});
          _stack.emplace_back(
              _call{*a1, lst::cons((m + 1), lst::cons(m, lst::nil())), m});
        }
      }
    } else {
      auto _f = std::move(std::get<_after_walk_in_Cons>(_popped));
      _stack.pop_back();
      uint64_t a0 = _f.a0;
      _result = (a0 + std::move(_result));
    }
  }
  return _result;
}

uint64_t LoopifyFramePtrEscape::go(uint64_t n) {
  return walk(n, lst::cons(UINT64_C(5), lst::cons(UINT64_C(7), lst::nil())),
              lst::nil());
}
