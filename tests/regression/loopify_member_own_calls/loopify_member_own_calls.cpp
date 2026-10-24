#include "loopify_member_own_calls.h"

/// A member of a mutual group recurses by the calls of itself it makes once
/// Loopify has inlined its partners into it, not by every call between the
/// group's members.
///
/// ja calls its partner jb only through a partial application, a
/// closure, so nothing is inlined into it and its body calls nothing it
/// could loop on.  In the three-way cycle f1 -> f2 -> f3 -> f1 each call is
/// an operand of +, so a partner's body runs in a lambda invoked in place
/// of its call, where the next partner is not inlined: f1's body never
/// calls f1.  The recursion plan used to give every member its group's
/// kind, here "not only tail calls", which the finished bodies contradicted
/// under CRANE_CHECK_IR.
uint64_t LoopifyMemberOwnCalls::ja(uint64_t n) {
  if (n <= 0) {
    return UINT64_C(0);
  } else {
    uint64_t m = n - 1;
    return List<uint64_t>::cons(m,
                                List<uint64_t>::cons(m, List<uint64_t>::nil()))
        .template map<uint64_t>(
            [=](uint64_t _x0) -> uint64_t { return jb(m, _x0); })
        .template fold_left<uint64_t>(
            [](uint64_t _x0, uint64_t _x1) -> uint64_t { return (_x0 + _x1); },
            UINT64_C(0));
  }
}

uint64_t LoopifyMemberOwnCalls::jb(uint64_t n, uint64_t x) {
  if (n <= 0) {
    return x;
  } else {
    uint64_t m = n - 1;
    return (x + ja(m));
  }
}

uint64_t LoopifyMemberOwnCalls::f1(uint64_t n) {
  if (n <= 0) {
    return UINT64_C(0);
  } else {
    uint64_t n_ = n - 1;
    return (UINT64_C(1) + f2(n_));
  }
}

uint64_t LoopifyMemberOwnCalls::f2(uint64_t n) {
  if (n <= 0) {
    return UINT64_C(0);
  } else {
    uint64_t n_ = n - 1;
    return (UINT64_C(2) + f3(n_));
  }
}

uint64_t LoopifyMemberOwnCalls::f3(uint64_t n) {
  if (n <= 0) {
    return UINT64_C(0);
  } else {
    uint64_t n_ = n - 1;
    return (UINT64_C(3) + f1(n_));
  }
}
