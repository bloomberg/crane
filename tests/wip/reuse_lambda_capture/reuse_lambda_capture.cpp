#include <reuse_lambda_capture.h>

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

__attribute__((pure)) unsigned int ReuseLambdaCapture::length(
    const std::shared_ptr<ReuseLambdaCapture::mylist> &l) {
  if (std::holds_alternative<typename ReuseLambdaCapture::mylist::Mycons>(
          l->v())) {
    const auto &[d_a0, d_a1] =
        std::get<typename ReuseLambdaCapture::mylist::Mycons>(l->v());
    return (1u + length(d_a1));
  } else {
    return 0u;
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
std::shared_ptr<ReuseLambdaCapture::mylist>
ReuseLambdaCapture::add_length_to_each(
    std::shared_ptr<ReuseLambdaCapture::mylist> l, const bool b) {
  if (b) {
    if (std::holds_alternative<typename ReuseLambdaCapture::mylist::Mycons>(
            l->v())) {
      if (l.use_count() == 1) {
        auto &_rf =
            std::get<typename ReuseLambdaCapture::mylist::Mycons>(l->v_mut());
        unsigned int h = std::move(_rf.d_a0);
        std::shared_ptr<ReuseLambdaCapture::mylist> t = std::move(_rf.d_a1);
        _rf.d_a0 = (h + 1u);
        _rf.d_a1 = map(
            [=](const unsigned int x) mutable { return (x + length(l)); }, t);
        return l;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename ReuseLambdaCapture::mylist::Mycons>(l->v());
        return mylist::mycons(
            (d_a0 + 1u),
            map([=](const unsigned int x) mutable { return (x + length(l)); },
                d_a1));
      }

    } else {
      return mylist::mynil();
    }
  } else {
    return l;
  }
}
