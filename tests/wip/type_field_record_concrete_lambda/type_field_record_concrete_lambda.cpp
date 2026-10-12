#include "type_field_record_concrete_lambda.h"

uint64_t TypeFieldRecordConcreteLambda::run(
    const TypeFieldRecordConcreteLambda::alg &a) {
  return a.toN(a.z);
}
