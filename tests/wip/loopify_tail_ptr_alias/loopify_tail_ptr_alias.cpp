#include "loopify_tail_ptr_alias.h"

/// KNOWN BUG: use-after-free in a loopified tail-recursive function.
///
/// rot is tail recursive in two list arguments. Loopification picks a
/// different representation for each loop variable:
///
/// - acc is only ever passed on as a sub-field of the scrutinee, so it
/// becomes a raw pointer:      const lst *_loop_acc
/// - l is sometimes given a freshly built value, so it becomes an owning
/// value:                      lst _loop_l
///
/// The generated loop body is
///
/// const auto &a0, a1 = std::get<Cons>(_loop_l.v());
/// const lst *_next_acc = crane_raw(a1);                 // points INTO _loop_l
/// _loop_s = _loop_s + hd(deref _loop_acc);
/// _loop_l = lst::cons(0, lst::cons(m, lst::nil()));     // frees the old
/// _loop_l _loop_acc = _next_acc;                                // now
/// dangling
///
/// _next_acc aliases the tail cell owned by _loop_l. Overwriting
/// _loop_l drops the last shared_ptr to that cell, so the pointer
/// published into _loop_acc is dangling before the next iteration reads it
/// through hd.
///
/// Expected: go 6 = 21 (checked with Compute in Rocq).
/// Actual:   7, plus an ASan heap-use-after-free.
///
/// Without Set Crane Loopify the same file extracts to correct code.
uint64_t LoopifyTailPtrAlias::hd(const LoopifyTailPtrAlias::lst &l) {
  if (std::holds_alternative<typename LoopifyTailPtrAlias::lst::Nil>(l.v())) {
    return UINT64_C(0);
  } else {
    const auto &[a0, a1] =
        std::get<typename LoopifyTailPtrAlias::lst::Cons>(l.v());
    return a0;
  }
}

uint64_t LoopifyTailPtrAlias::rot(uint64_t n, const LoopifyTailPtrAlias::lst &l,
                                  const LoopifyTailPtrAlias::lst &acc,
                                  uint64_t s) {
  uint64_t _loop_s = std::move(s);
  const LoopifyTailPtrAlias::lst *_loop_acc = &acc;
  LoopifyTailPtrAlias::lst _loop_l = l;
  uint64_t _loop_n = std::move(n);
  while (true) {
    if (_loop_n <= 0) {
      return _loop_s;
    } else {
      uint64_t m = _loop_n - 1;
      if (std::holds_alternative<typename LoopifyTailPtrAlias::lst::Nil>(
              _loop_l.v())) {
        return _loop_s;
      } else {
        const auto &[a0, a1] =
            std::get<typename LoopifyTailPtrAlias::lst::Cons>(_loop_l.v());
        if (a0 <= 0) {
          const LoopifyTailPtrAlias::lst *_next_acc = crane_raw(a1);
          _loop_s = (_loop_s + hd(*_loop_acc));
          _loop_l = lst::cons(UINT64_C(0), lst::cons(m, lst::nil()));
          _loop_n = m;
          _loop_acc = _next_acc;
        } else {
          uint64_t _x = a0 - 1;
          return _loop_s;
        }
      }
    }
  }
}

uint64_t LoopifyTailPtrAlias::go(uint64_t n) {
  return rot(n, lst::cons(UINT64_C(0), lst::cons(UINT64_C(7), lst::nil())),
             lst::nil(), UINT64_C(0));
}
