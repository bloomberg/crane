#include "type_field_record_in_expression.h"

uint64_t
TypeFieldRecordInExpression::get(const TypeFieldRecordInExpression::alg &a) {
  return a.f(a.unit_);
}
