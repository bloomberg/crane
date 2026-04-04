#include <env.h>

#include <cstdlib>
#include <memory>
#include <optional>
#include <string>
#include <type_traits>
#include <variant>

std::optional<std::string> Env::set_and_get(const std::string name,
                                            const std::string value) {
  setenv(name.c_str(), value.c_str(), 1);
  return [&]() -> std::optional<std::string> {
    auto *v = std::getenv(name.c_str());
    return v ? std::optional<std::string>(v) : std::optional<std::string>();
  }();
}

std::optional<std::string> Env::set_unset_get(const std::string name,
                                              const std::string value) {
  setenv(name.c_str(), value.c_str(), 1);
  unsetenv(name.c_str());
  return [&]() -> std::optional<std::string> {
    auto *v = std::getenv(name.c_str());
    return v ? std::optional<std::string>(v) : std::optional<std::string>();
  }();
}

std::optional<std::string> Env::get_missing(const std::string name) {
  return [&]() -> std::optional<std::string> {
    auto *v = std::getenv(name.c_str());
    return v ? std::optional<std::string>(v) : std::optional<std::string>();
  }();
}
