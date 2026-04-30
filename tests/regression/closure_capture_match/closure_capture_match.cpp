#include <closure_capture_match.h>

ClosureCaptureMatch::fn_box
ClosureCaptureMatch::box_from_match(const ClosureCaptureMatch::tree &t) {
  if (std::holds_alternative<typename ClosureCaptureMatch::tree::Leaf>(t.v())) {
    return fn_box::box([](unsigned int x) { return x; });
  } else {
    const auto &[d_a0, d_a1, d_a2] =
        std::get<typename ClosureCaptureMatch::tree::Node>(t.v());
    return fn_box::box(
        [=](const unsigned int &x) mutable { return (d_a1 + x); });
  }
}
