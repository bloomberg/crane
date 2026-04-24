#include <effect_complex_return.h>

#include <chrono>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <memory>
#include <optional>
#include <string>
#include <type_traits>
#include <utility>
#include <variant>

/// 1. Effect returning a pair
std::pair<std::string, std::string> EffectComplexReturn::read_pair() {
  std::string a;
  std::getline(std::cin, a);
  std::string b;
  std::getline(std::cin, b);
  return std::make_pair(a, b);
}

/// 2. Effect returning an option
std::optional<std::string>
EffectComplexReturn::maybe_read(const bool &do_read) {
  if (do_read) {
    std::string line;
    std::getline(std::cin, line);
    return std::make_optional<std::string>(line);
  } else {
    return std::optional<std::string>();
  }
}

/// 3. Void effect followed by value effect
std::string EffectComplexReturn::print_then_read(const std::string prompt) {
  std::cout << prompt << '\n';
  return []() -> std::string {
    std::string _r;
    std::getline(std::cin, _r);
    return _r;
  }();
}

/// 4. Multiple effects with different return types
std::pair<int64_t, std::string>
EffectComplexReturn::mixed_effects(const std::string name) {
  int64_t t = static_cast<int64_t>(
      std::chrono::duration_cast<std::chrono::milliseconds>(
          std::chrono::system_clock::now().time_since_epoch())
          .count());
  std::optional<std::string> mv = [&]() -> std::optional<std::string> {
    auto *v = std::getenv(name.c_str());
    return v ? std::optional<std::string>(v) : std::optional<std::string>();
  }();
  if (mv.has_value()) {
    const std::string &v = *mv;
    std::cout << v << '\n';
    return std::make_pair(t, v);
  } else {
    std::string line;
    std::getline(std::cin, line);
    return std::make_pair(t, line);
  }
}

/// 5. Clock effect in arithmetic
int64_t EffectComplexReturn::elapsed_ms() {
  int64_t t1 = static_cast<int64_t>(
      std::chrono::duration_cast<std::chrono::milliseconds>(
          std::chrono::steady_clock::now().time_since_epoch())
          .count());
  int64_t t2 = static_cast<int64_t>(
      std::chrono::duration_cast<std::chrono::milliseconds>(
          std::chrono::steady_clock::now().time_since_epoch())
          .count());
  return ((t2 - t1) & 0x7FFFFFFFFFFFFFFFLL);
}

/// 6. Effect result used to build a list
List<std::string> EffectComplexReturn::read_n(const unsigned int &n) {
  if (n <= 0) {
    return List<std::string>::nil();
  } else {
    unsigned int n0 = n - 1;
    if (n0 <= 0) {
      std::string x;
      std::getline(std::cin, x);
      return List<std::string>::cons(x, List<std::string>::nil());
    } else {
      unsigned int n1 = n0 - 1;
      if (n1 <= 0) {
        std::string x;
        std::getline(std::cin, x);
        std::string y;
        std::getline(std::cin, y);
        return List<std::string>::cons(
            x, List<std::string>::cons(y, List<std::string>::nil()));
      } else {
        unsigned int _x = n1 - 1;
        return List<std::string>::nil();
      }
    }
  }
}

/// 7. Env effect result used in conditional
std::string EffectComplexReturn::env_or_prompt(const std::string name) {
  std::optional<std::string> mv = [&]() -> std::optional<std::string> {
    auto *v = std::getenv(name.c_str());
    return v ? std::optional<std::string>(v) : std::optional<std::string>();
  }();
  if (mv.has_value()) {
    const std::string &v = *mv;
    return v;
  } else {
    std::cout << "Enter "s + name + ":"s << '\n';
    return []() -> std::string {
      std::string _r;
      std::getline(std::cin, _r);
      return _r;
    }();
  }
}
