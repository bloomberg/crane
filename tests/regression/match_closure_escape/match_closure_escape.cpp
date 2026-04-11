#include <match_closure_escape.h>

#include <functional>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

/// BUG TRIGGER: match_arm_box
/// The partial application sum_values l inside a match arm creates a
/// & lambda capturing the match-bound variable _args (from std::visit).
/// This lambda is stored in a Box constructor argument.
/// return_captures_by_value does NOT handle lambdas inside constructor args.
/// When the visit lambda returns, _args goes out of scope, and the Box
/// holds a dangling reference to a destroyed shared_ptr.
std::shared_ptr<MatchClosureEscape::fn_box> MatchClosureEscape::match_arm_box(
    const std::shared_ptr<MatchClosureEscape::tree> &t) {
  return std::visit(
      Overloaded{[](const typename MatchClosureEscape::tree::Leaf)
                     -> std::shared_ptr<MatchClosureEscape::fn_box> {
                   return fn_box::box([](unsigned int x) { return x; });
                 },
                 [](const typename MatchClosureEscape::tree::Node _args)
                     -> std::shared_ptr<MatchClosureEscape::fn_box> {
                   return fn_box::box(
                       [=](unsigned int _x0) mutable -> unsigned int {
                         return _args.d_a0->sum_values(_x0);
                       });
                 }},
      t->v());
}
