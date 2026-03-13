#ifndef INCLUDED_SHADOW_QUAL_NODE
#define INCLUDED_SHADOW_QUAL_NODE

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
    enum class Shadow { e_TAG };

    template <typename T1> static T1 shadow_rect(const T1 f, const Shadow s) {
      return [&](void) {
        switch (s) {
        case Shadow::e_TAG: {
          return f;
        }
        }
      }();
    }

    template <typename T1> static T1 shadow_rec(const T1 f, const Shadow s) {
      return [&](void) {
        switch (s) {
        case Shadow::e_TAG: {
          return f;
        }
        }
      }();
    }
  };

  __attribute__((pure)) static Node::Shadow id(const Node::Shadow x);
  static inline const Node::Shadow t = id(Node::Shadow::e_TAG);
};

#endif // INCLUDED_SHADOW_QUAL_NODE
