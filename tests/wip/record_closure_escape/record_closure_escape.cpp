#include <record_closure_escape.h>

#include <functional>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

__attribute__((pure)) unsigned int RecordClosureEscape::sum_values(
    const std::shared_ptr<RecordClosureEscape::tree> &t, const unsigned int x) {
  return std::visit(
      Overloaded{
          [&](const typename RecordClosureEscape::tree::Leaf _args)
              -> unsigned int { return std::move(x); },
          [&](const typename RecordClosureEscape::tree::Node _args)
              -> unsigned int {
            return std::visit(
                Overloaded{
                    [&](const typename RecordClosureEscape::tree::Leaf _args0)
                        -> unsigned int { return (_args.d_a1 + std::move(x)); },
                    [&](const typename RecordClosureEscape::tree::Node _args0)
                        -> unsigned int {
                      return std::visit(
                          Overloaded{
                              [&](const typename RecordClosureEscape::tree::Leaf
                                      _args1) -> unsigned int {
                                return (_args0.d_a1 + std::move(x));
                              },
                              [&](const typename RecordClosureEscape::tree::Node
                                      _args1) -> unsigned int {
                                return (
                                    ((_args0.d_a1 + _args1.d_a1) + _args.d_a1) +
                                    std::move(x));
                              }},
                          _args.d_a2->v());
                    }},
                _args.d_a0->v());
          }},
      t->v());
}

/// BUG: Partial application stored in a record field.
/// The record constructor mk_fn_record stores the & lambda.
/// return_captures_by_value doesn't handle lambdas inside
/// record constructor arguments.
std::shared_ptr<RecordClosureEscape::fn_record>
RecordClosureEscape::record_escape(
    std::shared_ptr<RecordClosureEscape::tree> t) {
  return std::make_shared<RecordClosureEscape::fn_record>(fn_record{
      [&](unsigned int _x0) -> unsigned int { return sum_values(t, _x0); },
      42u});
}

__attribute__((pure)) unsigned int RecordClosureEscape::use_record(
    const std::shared_ptr<RecordClosureEscape::fn_record> &r) {
  return r->fn_field(r->val_field);
}
