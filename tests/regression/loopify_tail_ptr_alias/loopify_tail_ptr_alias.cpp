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
/// _loop_l = lst::cons(0, lst::cons(m, lst::nil())); // frees the old _loop_l
/// _loop_acc = _next_acc;                                // now dangling
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
    const auto &[a0, _] =
        std::get<typename LoopifyTailPtrAlias::lst::Cons>(l.v());
    return a0;
  }
}

uint64_t LoopifyTailPtrAlias::rot(uint64_t n, const LoopifyTailPtrAlias::lst &l,
                                  const LoopifyTailPtrAlias::lst &acc,
                                  uint64_t s) {
  // Loop replaces the tail recursion: each recursive call updates the loop
  // variables.
  LoopifyTailPtrAlias::lst _loop_acc = acc;
  LoopifyTailPtrAlias::lst _loop_l = l;
  while (true) {
    if (n <= 0) {
      return s;
    } else {
      uint64_t m = n - 1;
      if (std::holds_alternative<typename LoopifyTailPtrAlias::lst::Nil>(
              _loop_l.v())) {
        return s;
      } else {
        const auto &[a0, a1] =
            std::get<typename LoopifyTailPtrAlias::lst::Cons>(_loop_l.v());
        if (a0 <= 0) {
          LoopifyTailPtrAlias::lst _next_acc = LoopifyTailPtrAlias::lst(*a1);
          s = s + hd(_loop_acc);
          _loop_l = lst::cons(UINT64_C(0), lst::cons(m, lst::nil()));
          n = m;
          _loop_acc = std::move(_next_acc);
        } else {
          uint64_t _x = a0 - 1;
          return s;
        }
      }
    }
  }
}

uint64_t LoopifyTailPtrAlias::go(uint64_t n) {
  return rot(n, lst::cons(UINT64_C(0), lst::cons(UINT64_C(7), lst::nil())),
             lst::nil(), UINT64_C(0));
}
