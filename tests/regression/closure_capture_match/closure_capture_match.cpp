#include <closure_capture_match.h>

#include <functional>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

std::shared_ptr<ClosureCaptureMatch::fn_box>
ClosureCaptureMatch::box_from_match(
    const std::shared_ptr<ClosureCaptureMatch::tree> &t) {
  if (std::holds_alternative<typename ClosureCaptureMatch::tree::Leaf>(
          t->v())) {
    return fn_box::box([](const unsigned int x) { return x; });
  } else {
    const auto &_m =
        *std::get_if<typename ClosureCaptureMatch::tree::Node>(&t->v());
    return fn_box::box(
        [=](const unsigned int x) mutable { return (_m.d_a1 + x); });
  }
}
