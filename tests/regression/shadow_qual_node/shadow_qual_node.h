#ifndef INCLUDED_SHADOW_QUAL_NODE
#define INCLUDED_SHADOW_QUAL_NODE

#include <memory>
#include <optional>
#include <type_traits>

struct ShadowQualNode {
  struct Node {
    enum class Shadow { e_TAG };

    template <typename T1> static T1 shadow_rect(T1 f, const Shadow) {
      return f;
    }

    template <typename T1> static T1 shadow_rec(T1 f, const Shadow) {
      return f;
    }
  };

  static Node::Shadow id(const Node::Shadow x);
  static inline const Node::Shadow t = id(Node::Shadow::e_TAG);
};

#endif // INCLUDED_SHADOW_QUAL_NODE
