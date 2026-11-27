#pragma once

#include <utility>

struct ShadowQualNode {
  struct Node {
    enum class Shadow { TAG };

    template <typename T1> static T1 shadow_rect(T1 f) { return f; }

    template <typename T1> static T1 shadow_rec(T1 f) {
      return shadow_rect<T1>(std::move(f));
    }
  };

  static Node::Shadow id();
  static inline const Node::Shadow t = id();
};
