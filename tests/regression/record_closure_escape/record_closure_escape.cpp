#include <record_closure_escape.h>

#include <functional>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

__attribute__((pure)) unsigned int RecordClosureEscape::sum_values(
    const std::shared_ptr<RecordClosureEscape::tree> &t, const unsigned int x) {
  if (std::holds_alternative<typename RecordClosureEscape::tree::Leaf>(
          t->v())) {
    return x;
  } else {
    const auto &[d_a0, d_a1, d_a2] =
        std::get<typename RecordClosureEscape::tree::Node>(t->v());
    if (std::holds_alternative<typename RecordClosureEscape::tree::Leaf>(
            d_a0->v())) {
      return (d_a1 + x);
    } else {
      const auto &[d_a00, d_a10, d_a20] =
          std::get<typename RecordClosureEscape::tree::Node>(d_a0->v());
      if (std::holds_alternative<typename RecordClosureEscape::tree::Leaf>(
              d_a2->v())) {
        return (d_a10 + x);
      } else {
        const auto &[d_a01, d_a11, d_a21] =
            std::get<typename RecordClosureEscape::tree::Node>(d_a2->v());
        return (((d_a10 + d_a11) + d_a1) + x);
      }
    }
  }
}

/// BUG: Partial application stored in a record field.
/// The record constructor mk_fn_record stores the & lambda.
/// return_captures_by_value doesn't handle lambdas inside
/// record constructor arguments.
std::shared_ptr<RecordClosureEscape::fn_record>
RecordClosureEscape::record_escape(
    std::shared_ptr<RecordClosureEscape::tree> t) {
  return std::make_shared<RecordClosureEscape::fn_record>(
      fn_record{[=](unsigned int _x0) mutable -> unsigned int {
                  return sum_values(t, _x0);
                },
                42u});
}

__attribute__((pure)) unsigned int RecordClosureEscape::use_record(
    const std::shared_ptr<RecordClosureEscape::fn_record> &r) {
  return r->fn_field(r->val_field);
}
