#include "functor_param_custom_list.h"

/// A functor's parameter type inside a custom-mapped type: R.String is
/// list R.Sigma, and list is a custom.  Extraction carried the type
/// argument R.Sigma among the custom's term arguments too, and the
/// custom's conversion read it as a value -- a callee no callable plan
/// exists for, an anomaly once a missing plan became one.  From ParseALot,
/// whose Matcher parameter R.Ty.Sigma stopped its extraction.
bool FunctorParamCustomList::Digits::ok(uint64_t n) { return n < UINT64_C(10); }

bool FunctorParamCustomList::all_digits(const std::deque<uint64_t> &x0_) {
  return DigitsImpl::all_ok(x0_);
}
