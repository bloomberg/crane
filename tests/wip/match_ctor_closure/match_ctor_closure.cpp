#include <match_ctor_closure.h>

#include <functional>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

/// BUG HYPOTHESIS: Match arm stores a partial application (closure)
/// in a constructor. The lambda captures a PATTERN VARIABLE (_args.d_a0)
/// by & reference. When the visit lambda returns, _args is destroyed
/// but the fn_box retains the closure with a dangling reference.
std::shared_ptr<MatchCtorClosure::fn_box> MatchCtorClosure::match_and_box(
    const std::shared_ptr<MatchCtorClosure::tree> &t) {
  return std::visit(
      Overloaded{[](const typename MatchCtorClosure::tree::Leaf _args)
                     -> std::shared_ptr<MatchCtorClosure::fn_box> {
                   return fn_box::box([](unsigned int x) { return x; });
                 },
                 [](const typename MatchCtorClosure::tree::Node _args)
                     -> std::shared_ptr<MatchCtorClosure::fn_box> {
                   return fn_box::box([&](unsigned int _x0) -> unsigned int {
                     return _args.d_a0->sum_values(_x0);
                   });
                 }},
      t->v());
}
