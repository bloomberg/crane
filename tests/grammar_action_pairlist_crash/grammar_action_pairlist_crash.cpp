#include "grammar_action_pairlist_crash.h"

uint64_t num_entries(std::monostate) {
  return static_cast<uint64_t>(entries.size());
}
