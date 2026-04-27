#include <string_match.h>

__attribute__((pure)) bool StringMatch::is_empty(const std::string s) {
  return s.length() == int64_t(0);
}
