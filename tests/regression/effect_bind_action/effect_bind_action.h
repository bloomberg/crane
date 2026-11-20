#pragma once

#include <chrono>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <memory>
#include <optional>
#include <string>
#include <string_view>
#include <utility>
#include <variant>

struct EffectBindAction {
  /// 1. Bool match inside bind action: one branch block template
  static std::string conditional_read(bool use_stdin);
  /// 2. Bool match where both branches are effects
  static int64_t conditional_effect(bool flag);
  /// 3. Option match inside bind: conditional effect based on env
  static std::string maybe_override(const std::string &name,
                                    const std::string &default0);
  /// 4. Nested: effect result used in another conditional effect
  static std::pair<int64_t, int64_t> timed_if_needed(bool measure);
  /// 5. Block template get_line, then conditional print
  static std::string echo_if(bool flag);
  /// 6. Effect action that's a function application (not inlined)
  static std::string helper(const std::string &s);
  static std::string use_helper(bool flag);
  /// 7. Let-binding of a match result, then use in effect
  static std::string let_match_then_effect(uint64_t n);
  /// 8. Discard result of conditional effect
  static uint64_t discard_conditional(bool flag);
};
