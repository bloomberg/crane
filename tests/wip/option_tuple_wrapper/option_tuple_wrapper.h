#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

struct OptionTupleWrapper {
  struct Node {
    enum class shadow { TagA, TagB };

    template <typename T1>
    static T1 shadow_rect(const T1 f, const T1 f0, const shadow s) {
      return [&](void) {
        switch (s) {
        case shadow::TagA: {
          return f;
        }
        case shadow::TagB: {
          return f0;
        }
        }
      }();
    }

    template <typename T1>
    static T1 shadow_rec(const T1 f, const T1 f0, const shadow s) {
      return [&](void) {
        switch (s) {
        case shadow::TagA: {
          return f;
        }
        case shadow::TagB: {
          return f0;
        }
        }
      }();
    }
  };

  static Node::shadow pick(const bool b);

  static inline const Node::shadow t = pick(true);
};
