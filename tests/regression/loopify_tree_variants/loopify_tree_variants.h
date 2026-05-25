#ifndef INCLUDED_LOOPIFY_TREE_VARIANTS
#define INCLUDED_LOOPIFY_TREE_VARIANTS

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

struct LoopifyTreeVariants {
  struct ternary {
    // TYPES
    struct TLeaf {};

    struct TNode {
      std::shared_ptr<ternary> a0;
      uint64_t a1;
      std::shared_ptr<ternary> a2;
      std::shared_ptr<ternary> a3;
    };

    using variant_t = std::variant<TLeaf, TNode>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    ternary() {}

    explicit ternary(TLeaf _v) : v_(_v) {}

    explicit ternary(TNode _v) : v_(std::move(_v)) {}

    static ternary tleaf() { return ternary(TLeaf{}); }

    static ternary tnode(ternary a0, uint64_t a1, ternary a2, ternary a3) {
      return ternary(TNode{std::make_shared<ternary>(std::move(a0)), a1,
                           std::make_shared<ternary>(std::move(a2)),
                           std::make_shared<ternary>(std::move(a3))});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    uint64_t ternary_count() const {
      if (std::holds_alternative<typename ternary::TLeaf>(this->v())) {
        return UINT64_C(0);
      } else {
        const auto &[a0, a1, a2, a3] =
            std::get<typename ternary::TNode>(this->v());
        return (((UINT64_C(1) + a0->ternary_count()) + a2->ternary_count()) +
                a3->ternary_count());
      }
    }

    uint64_t ternary_sum() const {
      if (std::holds_alternative<typename ternary::TLeaf>(this->v())) {
        return UINT64_C(0);
      } else {
        const auto &[a0, a1, a2, a3] =
            std::get<typename ternary::TNode>(this->v());
        return (((a0->ternary_sum() + a1) + a2->ternary_sum()) +
                a3->ternary_sum());
      }
    }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, ternary &, T1 &, uint64_t &,
                                     ternary &, T1 &, ternary &, T1 &>
    T1 ternary_rec(T1 f, F1 &&f0) const {
      if (std::holds_alternative<typename ternary::TLeaf>(this->v())) {
        return f;
      } else {
        const auto &[a0, a1, a2, a3] =
            std::get<typename ternary::TNode>(this->v());
        return f0(*a0, a0->template ternary_rec<T1>(f, f0), a1, *a2,
                  a2->template ternary_rec<T1>(f, f0), *a3,
                  a3->template ternary_rec<T1>(f, f0));
      }
    }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, ternary &, T1 &, uint64_t &,
                                     ternary &, T1 &, ternary &, T1 &>
    T1 ternary_rect(T1 f, F1 &&f0) const {
      if (std::holds_alternative<typename ternary::TLeaf>(this->v())) {
        return f;
      } else {
        const auto &[a0, a1, a2, a3] =
            std::get<typename ternary::TNode>(this->v());
        return f0(*a0, a0->template ternary_rect<T1>(f, f0), a1, *a2,
                  a2->template ternary_rect<T1>(f, f0), *a3,
                  a3->template ternary_rect<T1>(f, f0));
      }
    }
  };

  struct quadtree {
    // TYPES
    struct QLeaf {
      uint64_t a0;
    };

    struct Quad {
      std::shared_ptr<quadtree> a0;
      std::shared_ptr<quadtree> a1;
      std::shared_ptr<quadtree> a2;
      std::shared_ptr<quadtree> a3;
    };

    using variant_t = std::variant<QLeaf, Quad>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    quadtree() {}

    explicit quadtree(QLeaf _v) : v_(std::move(_v)) {}

    explicit quadtree(Quad _v) : v_(std::move(_v)) {}

    static quadtree qleaf(uint64_t a0) { return quadtree(QLeaf{a0}); }

    static quadtree quad(quadtree a0, quadtree a1, quadtree a2, quadtree a3) {
      return quadtree(Quad{std::make_shared<quadtree>(std::move(a0)),
                           std::make_shared<quadtree>(std::move(a1)),
                           std::make_shared<quadtree>(std::move(a2)),
                           std::make_shared<quadtree>(std::move(a3))});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    uint64_t quad_sum() const {
      if (std::holds_alternative<typename quadtree::QLeaf>(this->v())) {
        const auto &[a0] = std::get<typename quadtree::QLeaf>(this->v());
        return a0;
      } else {
        const auto &[a0, a1, a2, a3] =
            std::get<typename quadtree::Quad>(this->v());
        return (((a0->quad_sum() + a1->quad_sum()) + a2->quad_sum()) +
                a3->quad_sum());
      }
    }

    template <typename T1, typename F0, typename F1>
      requires std::is_invocable_r_v<T1, F0 &, uint64_t &> &&
               std::is_invocable_r_v<T1, F1 &, quadtree &, T1 &, quadtree &,
                                     T1 &, quadtree &, T1 &, quadtree &, T1 &>
    T1 quadtree_rec(F0 &&f, F1 &&f0) const {
      if (std::holds_alternative<typename quadtree::QLeaf>(this->v())) {
        const auto &[a0] = std::get<typename quadtree::QLeaf>(this->v());
        return f(a0);
      } else {
        const auto &[a0, a1, a2, a3] =
            std::get<typename quadtree::Quad>(this->v());
        return f0(*a0, a0->template quadtree_rec<T1>(f, f0), *a1,
                  a1->template quadtree_rec<T1>(f, f0), *a2,
                  a2->template quadtree_rec<T1>(f, f0), *a3,
                  a3->template quadtree_rec<T1>(f, f0));
      }
    }

    template <typename T1, typename F0, typename F1>
      requires std::is_invocable_r_v<T1, F0 &, uint64_t &> &&
               std::is_invocable_r_v<T1, F1 &, quadtree &, T1 &, quadtree &,
                                     T1 &, quadtree &, T1 &, quadtree &, T1 &>
    T1 quadtree_rect(F0 &&f, F1 &&f0) const {
      if (std::holds_alternative<typename quadtree::QLeaf>(this->v())) {
        const auto &[a0] = std::get<typename quadtree::QLeaf>(this->v());
        return f(a0);
      } else {
        const auto &[a0, a1, a2, a3] =
            std::get<typename quadtree::Quad>(this->v());
        return f0(*a0, a0->template quadtree_rect<T1>(f, f0), *a1,
                  a1->template quadtree_rect<T1>(f, f0), *a2,
                  a2->template quadtree_rect<T1>(f, f0), *a3,
                  a3->template quadtree_rect<T1>(f, f0));
      }
    }
  };

  struct leaf_tree {
    // TYPES
    struct LLeaf {
      uint64_t a0;
    };

    struct LNode {
      std::shared_ptr<leaf_tree> a0;
      std::shared_ptr<leaf_tree> a1;
    };

    using variant_t = std::variant<LLeaf, LNode>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    leaf_tree() {}

    explicit leaf_tree(LLeaf _v) : v_(std::move(_v)) {}

    explicit leaf_tree(LNode _v) : v_(std::move(_v)) {}

    static leaf_tree lleaf(uint64_t a0) { return leaf_tree(LLeaf{a0}); }

    static leaf_tree lnode(leaf_tree a0, leaf_tree a1) {
      return leaf_tree(LNode{std::make_shared<leaf_tree>(std::move(a0)),
                             std::make_shared<leaf_tree>(std::move(a1))});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    uint64_t leaf_tree_max() const {
      if (std::holds_alternative<typename leaf_tree::LLeaf>(this->v())) {
        const auto &[a0] = std::get<typename leaf_tree::LLeaf>(this->v());
        return a0;
      } else {
        const auto &[a0, a1] = std::get<typename leaf_tree::LNode>(this->v());
        uint64_t lmax = a0->leaf_tree_max();
        uint64_t rmax = a1->leaf_tree_max();
        if (lmax < rmax) {
          return rmax;
        } else {
          return lmax;
        }
      }
    }

    uint64_t leaf_tree_sum() const {
      if (std::holds_alternative<typename leaf_tree::LLeaf>(this->v())) {
        const auto &[a0] = std::get<typename leaf_tree::LLeaf>(this->v());
        return a0;
      } else {
        const auto &[a0, a1] = std::get<typename leaf_tree::LNode>(this->v());
        return (a0->leaf_tree_sum() + a1->leaf_tree_sum());
      }
    }

    template <typename T1, typename F0, typename F1>
      requires std::is_invocable_r_v<T1, F0 &, uint64_t &> &&
               std::is_invocable_r_v<T1, F1 &, leaf_tree &, T1 &, leaf_tree &,
                                     T1 &>
    T1 leaf_tree_rec(F0 &&f, F1 &&f0) const {
      if (std::holds_alternative<typename leaf_tree::LLeaf>(this->v())) {
        const auto &[a0] = std::get<typename leaf_tree::LLeaf>(this->v());
        return f(a0);
      } else {
        const auto &[a0, a1] = std::get<typename leaf_tree::LNode>(this->v());
        return f0(*a0, a0->template leaf_tree_rec<T1>(f, f0), *a1,
                  a1->template leaf_tree_rec<T1>(f, f0));
      }
    }

    template <typename T1, typename F0, typename F1>
      requires std::is_invocable_r_v<T1, F0 &, uint64_t &> &&
               std::is_invocable_r_v<T1, F1 &, leaf_tree &, T1 &, leaf_tree &,
                                     T1 &>
    T1 leaf_tree_rect(F0 &&f, F1 &&f0) const {
      if (std::holds_alternative<typename leaf_tree::LLeaf>(this->v())) {
        const auto &[a0] = std::get<typename leaf_tree::LLeaf>(this->v());
        return f(a0);
      } else {
        const auto &[a0, a1] = std::get<typename leaf_tree::LNode>(this->v());
        return f0(*a0, a0->template leaf_tree_rect<T1>(f, f0), *a1,
                  a1->template leaf_tree_rect<T1>(f, f0));
      }
    }
  };
};

#endif // INCLUDED_LOOPIFY_TREE_VARIANTS
