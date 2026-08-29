#ifndef INCLUDED_ENV
#define INCLUDED_ENV

#include <cstdlib>
#include <memory>
#include <optional>
#include <string>
#include <variant>

struct Env {
  static std::optional<std::string> set_and_get(std::string name,
                                                std::string value);
  static std::optional<std::string> set_unset_get(std::string name,
                                                  std::string value);
  static std::optional<std::string> get_missing(std::string name);
};

#endif // INCLUDED_ENV
