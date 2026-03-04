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

struct ShadowQualNode {
  struct Node {
    enum class shadow { Tag };

    template <typename T1> static T1 shadow_rect(const T1 f, const shadow s) {
      return [&](void) {
        switch (s) {
        case shadow::Tag: {
          return f;
        }
        }
      }();
    }

    template <typename T1> static T1 shadow_rec(const T1 f, const shadow s) {
      return [&](void) {
        switch (s) {
        case shadow::Tag: {
          return f;
        }
        }
      }();
    }
  };

  static Node::shadow id(const Node::shadow x);

  static inline const Node::shadow t = id(Node::shadow::Tag);
};
