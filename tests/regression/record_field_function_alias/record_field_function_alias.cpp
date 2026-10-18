#include "record_field_function_alias.h"

bool RecordFieldFunctionAlias::apply_run(
    const RecordFieldFunctionAlias::holder &h0, const Nat &n) {
  return h0.run(n);
}

bool RecordFieldFunctionAlias::apply_same(
    const RecordFieldFunctionAlias::holder &h0, const Nat &a, const Nat &b) {
  return h0.same(a, b);
}

bool RecordFieldFunctionAlias::apply_test(
    const RecordFieldFunctionAlias::Box &b, const Nat &n) {
  return b.test(n);
}
