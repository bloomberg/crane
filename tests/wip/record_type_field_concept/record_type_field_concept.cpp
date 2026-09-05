#include "record_type_field_concept.h"

uint64_t RecordTypeFieldConcept::read(const RecordTypeFieldConcept::dyn &d) {
  return d.dshow(d.dval);
}
