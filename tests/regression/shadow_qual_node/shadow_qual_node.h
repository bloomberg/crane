#ifndef INCLUDED_SHADOW_QUAL_NODE
#define INCLUDED_SHADOW_QUAL_NODE

struct ShadowQualNode {
  struct Node {
    enum class Shadow { TAG };

    template <typename T1> static T1 shadow_rect(T1 f, Shadow) { return f; }

    template <typename T1> static T1 shadow_rec(T1 f, Shadow) { return f; }
  };

  static Node::Shadow id(Node::Shadow x);
  static inline const Node::Shadow t = id(Node::Shadow::TAG);
};

#endif // INCLUDED_SHADOW_QUAL_NODE
