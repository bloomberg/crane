#include <effect_bind_action.h>

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

/// 1. Bool match inside bind action: one branch block template
std::string EffectBindAction::conditional_read(const bool use_stdin) {
  return [&]() -> std::string {
    if (use_stdin) {
      return []() -> std::string {
        std::string _r;
        std::getline(std::cin, _r);
        return _r;
      }();
    } else {
      return "default";
    }
  }();
}

/// 2. Bool match where both branches are effects
int64_t EffectBindAction::conditional_effect(const bool flag) {
  return [&]() -> int64_t {
    if (flag) {
      return static_cast<int64_t>(
          std::chrono::duration_cast<std::chrono::milliseconds>(
              std::chrono::steady_clock::now().time_since_epoch())
              .count());
    } else {
      return int64_t(0);
    }
  }();
}

/// 3. Option match inside bind: conditional effect based on env
std::string EffectBindAction::maybe_override(const std::string name,
                                             const std::string default0) {
  std::optional<std::string> r = [&]() -> std::optional<std::string> {
    auto *v = std::getenv(name.c_str());
    return v ? std::optional<std::string>(v) : std::optional<std::string>();
  }();
  return [&]() -> std::string {
    if (r.has_value()) {
      const std::string &v = *r;
      return v;
    } else {
      return default0;
    }
  }();
}

/// 4. Nested: effect result used in another conditional effect
std::pair<int64_t, int64_t>
EffectBindAction::timed_if_needed(const bool measure) {
  int64_t t1 = [&]() -> int64_t {
    if (measure) {
      return static_cast<int64_t>(
          std::chrono::duration_cast<std::chrono::milliseconds>(
              std::chrono::steady_clock::now().time_since_epoch())
              .count());
    } else {
      return int64_t(0);
    }
  }();
  int64_t t2 = [&]() -> int64_t {
    if (measure) {
      return static_cast<int64_t>(
          std::chrono::duration_cast<std::chrono::milliseconds>(
              std::chrono::steady_clock::now().time_since_epoch())
              .count());
    } else {
      return int64_t(0);
    }
  }();
  return std::make_pair(t1, t2);
}

/// 5. Block template get_line, then conditional print
std::string EffectBindAction::echo_if(const bool flag) {
  std::string line;
  std::getline(std::cin, line);
  [&]() -> void {
    if (flag) {
      std::cout << line << '\n';
      return;
    } else {
      return;
    }
  }();
  return line;
}

/// 6. Effect action that's a function application (not inlined)
std::string EffectBindAction::helper(const std::string s) {
  std::cout << s << '\n';
  return s;
}

std::string EffectBindAction::use_helper(const bool flag) {
  return [&]() -> std::string {
    if (flag) {
      return helper("yes");
    } else {
      return helper("no");
    }
  }();
}

/// 7. Let-binding of a match result, then use in effect
std::string EffectBindAction::let_match_then_effect(const unsigned int n) {
  std::string msg;
  if (n <= 0) {
    msg = "zero";
  } else {
    unsigned int _x = n - 1;
    msg = "other";
  }
  std::cout << msg << '\n';
  return msg;
}

/// 8. Discard result of conditional effect
unsigned int EffectBindAction::discard_conditional(const bool flag) {
  [&]() -> void {
    if (flag) {
      std::cout << "flagged"s << '\n';
      return;
    } else {
      return;
    }
  }();
  return 42u;
}
