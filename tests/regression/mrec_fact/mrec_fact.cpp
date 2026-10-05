#include "mrec_fact.h"

/// Factorial through coq-itree's mrec: each recursive call is an event
/// interp_mrec answers by running the body again.  interp_mrec passes
/// iter its step as a lambda, so it is the specialized interpreter that
/// runs here.
Itree<crane::obj, uint64_t> MrecFact::fact(uint64_t n) {
  return Recursion::template mrec<MrecFact::call, crane::obj, uint64_t>(
      [](const MrecFact::call &a0)
          -> Itree<Sum1<MrecFact::call, crane::obj, crane::obj>, crane::obj> {
        return body<crane::obj>(crane_convert<MrecFact::call>(a0));
      },
      call::fact(n));
}

crane::obj Function::Id_IFun(crane::obj e) { return e; }
