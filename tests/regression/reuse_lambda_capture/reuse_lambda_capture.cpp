#include "reuse_lambda_capture.h"

uint64_t ReuseLambdaCapture::length(const ReuseLambdaCapture::mylist &l) {
  if (std::holds_alternative<typename ReuseLambdaCapture::mylist::Mycons>(
          l.v())) {
    const auto &[a0, a1] =
        std::get<typename ReuseLambdaCapture::mylist::Mycons>(l.v());
    return (UINT64_C(1) + length(*a1));
  } else {
    return UINT64_C(0);
  }
}

/// BUG: reuse fires, then length l inside the lambda accesses
/// moved-from fields of l.
///
/// The reuse path does:
/// auto x  = std::move(_rf.d_a0);
/// auto xs = std::move(_rf.d_a1);   // _rf.d_a1 is now null
/// _rf.d_a0 = x + 1;
/// _rf.d_a1 = map(lambda, xs);      // lambda calls length(l)
/// // l is the same object as _rf
/// // l.d_a1 is null -> crash
/// return _rf;
ReuseLambdaCapture::mylist
ReuseLambdaCapture::add_length_to_each(ReuseLambdaCapture::mylist l, bool b) {
  if (b) {
    if (std::holds_alternative<typename ReuseLambdaCapture::mylist::Mycons>(
            l.v_mut())) {
      auto &[a0, a1] =
          std::get<typename ReuseLambdaCapture::mylist::Mycons>(l.v_mut());
      const ReuseLambdaCapture::mylist &a1_value = *a1;
      return mylist::mycons(
          (std::move(a0) + UINT64_C(1)),
          map([=](uint64_t x) mutable { return (x + length(l)); }, a1_value));
    } else {
      return mylist::mynil();
    }
  } else {
    return l;
  }
}
