#include <effect_deep_compose.h>

#include <chrono>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <memory>
#include <optional>
#include <string>
#include <type_traits>
#include <variant>

/// 1. Function using all three effects
int64_t EffectDeepCompose::timed_env_op(const std::string name,
                                        const std::string value) {
  int64_t t1 = static_cast<int64_t>(
      std::chrono::duration_cast<std::chrono::milliseconds>(
          std::chrono::steady_clock::now().time_since_epoch())
          .count());
  setenv(name.c_str(), value.c_str(), 1);
  std::cout << "env set"s << '\n';
  int64_t t2 = static_cast<int64_t>(
      std::chrono::duration_cast<std::chrono::milliseconds>(
          std::chrono::steady_clock::now().time_since_epoch())
          .count());
  return ((t2 - t1) & 0x7FFFFFFFFFFFFFFFLL);
}

/// 2. Function using only console from inside bigE
void EffectDeepCompose::just_greet() {
  std::cout << "hello from bigE"s << '\n';
  return;
}

/// 3. Function using env + console but not clock
void EffectDeepCompose::env_with_log(const std::string name,
                                     const std::string value) {
  std::cout << "setting env..."s << '\n';
  setenv(name.c_str(), value.c_str(), 1);
  std::cout << "done"s << '\n';
  return;
}

/// 4. Read env, print result
void EffectDeepCompose::show_env(const std::string name) {
  std::optional<std::string> mv = [&]() -> std::optional<std::string> {
    auto *v = std::getenv(name.c_str());
    return v ? std::optional<std::string>(v) : std::optional<std::string>();
  }();
  if (mv.has_value()) {
    const std::string &v = *mv;
    std::cout << v << '\n';
    return;
  } else {
    std::cout << "not set"s << '\n';
    return;
  }
}

/// 5. Conditional clock read
int64_t EffectDeepCompose::maybe_time(const bool measure) {
  if (measure) {
    return static_cast<int64_t>(
        std::chrono::duration_cast<std::chrono::milliseconds>(
            std::chrono::steady_clock::now().time_since_epoch())
            .count());
  } else {
    return int64_t(0);
  }
}

/// 6. Recursive function over all three effects
void EffectDeepCompose::repeat_n(const unsigned int n) {
  if (n <= 0) {
    return;
  } else {
    unsigned int n_ = n - 1;
    int64_t _x = static_cast<int64_t>(
        std::chrono::duration_cast<std::chrono::milliseconds>(
            std::chrono::steady_clock::now().time_since_epoch())
            .count());
    std::cout << "tick"s << '\n';
    repeat_n(n_);
    return;
  }
}
