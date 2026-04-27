#ifndef INCLUDED_OPTION_LET_NONE_BUG
#define INCLUDED_OPTION_LET_NONE_BUG

#include <memory>
#include <optional>
#include <type_traits>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

struct OptionLetNoneBug {
  static inline const std::optional<bool> bug = std::optional<bool>();
};

#endif // INCLUDED_OPTION_LET_NONE_BUG
