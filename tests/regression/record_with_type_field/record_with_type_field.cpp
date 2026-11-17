#include "record_with_type_field.h"

/// A record with a Type field used as data is demoted from a concept to a
/// struct with erased (std::any) fields, but its literal is still built from
/// un-erased lambdas, so the initialiser does not convert.
RecordWithTypeField::ty
RecordWithTypeField::fold3(const RecordWithTypeField::alg &a,
                           RecordWithTypeField::ty x) {
  return a.op(x, a.op(x, a.unit_));
}
