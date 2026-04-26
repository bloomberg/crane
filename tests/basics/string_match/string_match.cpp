#include <string_match.h>

#include <cstdint>
#include <memory>
#include <optional>
#include <string>
#include <type_traits>

__attribute__((pure)) bool StringMatch::is_empty(const std::string s) {
  return s.length() == int64_t(0);
}
