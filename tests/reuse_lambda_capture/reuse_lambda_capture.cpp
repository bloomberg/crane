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

ReuseLambdaCapture::mylist
ReuseLambdaCapture::add_length_to_each(ReuseLambdaCapture::mylist l, bool b) {
  if (b) {
    if (std::holds_alternative<typename ReuseLambdaCapture::mylist::Mycons>(
            l.v_mut())) {
      auto &[a0, a1] =
          std::get<typename ReuseLambdaCapture::mylist::Mycons>(l.v_mut());
      const ReuseLambdaCapture::mylist &a1_value = *a1;
      return mylist::mycons(
          (a0 + UINT64_C(1)),
          map([=](uint64_t x) mutable { return (x + length(l)); }, a1_value));
    } else {
      return mylist::mynil();
    }
  } else {
    return l;
  }
}
