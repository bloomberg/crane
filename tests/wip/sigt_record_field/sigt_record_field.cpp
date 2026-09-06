#include "sigt_record_field.h"

/// The field payload is declared at the erased shape SigT<std::any,
/// std::any>, but each producer builds the existT at its concrete
/// instantiation -- SigT<std::any, List<std::any>> for b2 -- so the
/// aggregate initialiser does not match the field it initialises.
uint64_t SigtRecordField::peek(const SigtRecordField::boxed &b) {
  return b.size;
}
