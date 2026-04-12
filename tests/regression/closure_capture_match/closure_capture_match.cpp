#include <closure_capture_match.h>

#include <functional>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

std::shared_ptr<ClosureCaptureMatch::fn_box>
ClosureCaptureMatch::box_from_match(
    const std::shared_ptr<ClosureCaptureMatch::tree> &t) {
  return std::visit(
      Overloaded{[](const typename ClosureCaptureMatch::tree::Leaf &)
                     -> std::shared_ptr<ClosureCaptureMatch::fn_box> {
                   return fn_box::box([](unsigned int x) { return x; });
                 },
                 [](const typename ClosureCaptureMatch::tree::Node &_args)
                     -> std::shared_ptr<ClosureCaptureMatch::fn_box> {
                   return fn_box::box([=](unsigned int x) mutable {
                     return (_args.d_a1 + x);
                   });
                 }},
      t->v());
}
