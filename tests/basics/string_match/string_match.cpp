#include "string_match.h"

bool StringMatch::is_empty(std::string_view s) {
  return static_cast<int64_t>(s.size()) == INT64_C(0);
}
