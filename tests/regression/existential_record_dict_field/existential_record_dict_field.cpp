#include "existential_record_dict_field.h"

uint64_t
ExistentialRecordDictField::shp(const ExistentialRecordDictField::packed &p) {
  return p.dict.sh(p.val);
}
