#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

struct EncodeClbBytesInRange {
  enum class instruction { CLB };

  template <typename T1>
  static T1 instruction_rect(const T1 f, const instruction i) {
    return [&](void) {
      switch (i) {
      case instruction::CLB: {
        return f;
      }
      }
    }();
  }

  template <typename T1>
  static T1 instruction_rec(const T1 f, const instruction i) {
    return [&](void) {
      switch (i) {
      case instruction::CLB: {
        return f;
      }
      }
    }();
  }

  static std::pair<unsigned int, unsigned int> encode(const instruction i);

  static bool pair_in_range(const std::pair<unsigned int, unsigned int> p);

  static inline const bool t = pair_in_range(encode(instruction::CLB));
};
