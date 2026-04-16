#ifndef INCLUDED_ENV
#define INCLUDED_ENV

#include <cstdlib>
#include <memory>
#include <optional>
#include <string>
#include <type_traits>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

struct Env {
  static std::optional<std::string> set_and_get(const std::string name,
                                                const std::string value);
  static std::optional<std::string> set_unset_get(const std::string name,
                                                  const std::string value);
  static std::optional<std::string> get_missing(const std::string name);
};

#endif // INCLUDED_ENV
