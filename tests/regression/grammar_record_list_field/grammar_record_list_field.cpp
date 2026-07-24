#include "grammar_record_list_field.h"

uint64_t num_entries(std::monostate) {
  return static_cast<uint64_t>(entries.size());
}
