#include <record_closure_escape.h>

#include <functional>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

__attribute__((pure)) unsigned int
RecordClosureEscape::sum_values(const RecordClosureEscape::tree &t,
                                unsigned int x) {
  if (std::holds_alternative<typename RecordClosureEscape::tree::Leaf>(t.v())) {
    return x;
  } else {
    const auto &[d_a0, d_a1, d_a2] =
        std::get<typename RecordClosureEscape::tree::Node>(t.v());
    auto &&_sv0 = *(d_a0);
    if (std::holds_alternative<typename RecordClosureEscape::tree::Leaf>(
            _sv0.v())) {
      return (d_a1 + x);
    } else {
      const auto &[d_a00, d_a10, d_a20] =
          std::get<typename RecordClosureEscape::tree::Node>(_sv0.v());
      auto &&_sv1 = *(d_a2);
      if (std::holds_alternative<typename RecordClosureEscape::tree::Leaf>(
              _sv1.v())) {
        return (d_a10 + x);
      } else {
        const auto &[d_a01, d_a11, d_a21] =
            std::get<typename RecordClosureEscape::tree::Node>(_sv1.v());
        return (((d_a10 + d_a11) + d_a1) + x);
      }
    }
  }
}

/// BUG: Partial application stored in a record field.
/// The record constructor mk_fn_record stores the & lambda.
/// return_captures_by_value doesn't handle lambdas inside
/// record constructor arguments.
__attribute__((pure)) RecordClosureEscape::fn_record
RecordClosureEscape::record_escape(RecordClosureEscape::tree t) {
  return fn_record{[=](unsigned int _x0) mutable -> unsigned int {
                     return sum_values(t, _x0);
                   },
                   42u};
}

__attribute__((pure)) unsigned int
RecordClosureEscape::use_record(const RecordClosureEscape::fn_record &r) {
  return r.fn_field(r.val_field);
}
