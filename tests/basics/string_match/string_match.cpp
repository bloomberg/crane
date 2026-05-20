#include "string_match.h"

bool StringMatch::is_empty(std::string s) {
  return static_cast<int64_t>(s.length()) == INT64_C(0);
}
