#include "string_match.h"

bool StringMatch::is_empty(std::string s) {
  return static_cast<int64_t>(s.length()) == int64_t(0);
}
