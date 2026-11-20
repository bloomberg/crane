#pragma once

#include <cstdlib>
#include <memory>
#include <optional>
#include <string>
#include <string_view>
#include <variant>

struct Env {
  static std::optional<std::string> set_and_get(const std::string &name,
                                                const std::string &value);
  static std::optional<std::string> set_unset_get(const std::string &name,
                                                  const std::string &value);
  static std::optional<std::string> get_missing(const std::string &name);
};
