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
    const auto &_m =
        *std::get_if<typename RecordClosureEscape::tree::Node>(&t->v());
    auto &&_sv0 = _m.d_a0;
    if (std::holds_alternative<typename RecordClosureEscape::tree::Leaf>(
            _sv0->v())) {
      return (_m.d_a1 + x);
    } else {
      const auto &_m0 =
          *std::get_if<typename RecordClosureEscape::tree::Node>(&_sv0->v());
      auto &&_sv1 = _m.d_a2;
      if (std::holds_alternative<typename RecordClosureEscape::tree::Leaf>(
              _sv1->v())) {
        return (_m0.d_a1 + x);
      } else {
        const auto &_m1 =
            *std::get_if<typename RecordClosureEscape::tree::Node>(&_sv1->v());
        return (((_m0.d_a1 + _m1.d_a1) + _m.d_a1) + x);
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
