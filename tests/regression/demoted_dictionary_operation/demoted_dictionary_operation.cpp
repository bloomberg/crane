#include "demoted_dictionary_operation.h"

DemotedDictionaryOperation::Tag<uint64_t>
DemotedDictionaryOperation::tag_of(uint64_t n) {
  return Tag<uint64_t>{n};
}
