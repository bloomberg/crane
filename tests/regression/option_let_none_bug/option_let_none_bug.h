#ifndef INCLUDED_OPTION_LET_NONE_BUG
#define INCLUDED_OPTION_LET_NONE_BUG

#include <memory>
#include <optional>
#include <type_traits>

struct OptionLetNoneBug {
  static inline const std::optional<bool> bug = std::optional<bool>();
};

#endif // INCLUDED_OPTION_LET_NONE_BUG
