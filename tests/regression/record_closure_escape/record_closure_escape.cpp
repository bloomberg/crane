#include "record_closure_escape.h"

uint64_t RecordClosureEscape::sum_values(const RecordClosureEscape::tree &t,
                                         uint64_t x) {
  if (std::holds_alternative<typename RecordClosureEscape::tree::Leaf>(t.v())) {
    return x;
  } else {
    const auto &[a0, a1, a2] =
        std::get<typename RecordClosureEscape::tree::Node>(t.v());
    auto &&_sv0 = *a0;
    if (std::holds_alternative<typename RecordClosureEscape::tree::Leaf>(
            _sv0.v())) {
      return (a1 + x);
    } else {
      const auto &[a00, a10, a20] =
          std::get<typename RecordClosureEscape::tree::Node>(_sv0.v());
      auto &&_sv1 = *a2;
      if (std::holds_alternative<typename RecordClosureEscape::tree::Leaf>(
              _sv1.v())) {
        return (a10 + x);
      } else {
        const auto &[a01, a11, a21] =
            std::get<typename RecordClosureEscape::tree::Node>(_sv1.v());
        return (((a10 + a11) + a1) + x);
      }
    }
  }
}

/// BUG: Partial application stored in a record field.
/// The record constructor mk_fn_record stores the & lambda.
/// return_captures_by_value doesn't handle lambdas inside
/// record constructor arguments.
RecordClosureEscape::fn_record
RecordClosureEscape::record_escape(RecordClosureEscape::tree t) {
  return fn_record{
      [=](uint64_t _x0) mutable -> uint64_t { return sum_values(t, _x0); },
      UINT64_C(42)};
}

uint64_t
RecordClosureEscape::use_record(const RecordClosureEscape::fn_record &r) {
  return r.fn_field(r.val_field);
}
