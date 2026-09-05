#include "record_field_named_list.h"

uint64_t RecordFieldNamedList::weigh(const RecordFieldNamedList::point &p) {
  return ((p.size + p.list.length()) + p.count);
}
