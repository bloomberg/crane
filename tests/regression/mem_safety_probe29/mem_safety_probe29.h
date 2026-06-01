#ifndef INCLUDED_MEM_SAFETY_PROBE29
#define INCLUDED_MEM_SAFETY_PROBE29

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

struct MemSafetyProbe29 {
  /// An inner tree type — value type with recursive children.
  struct inner {
    // TYPES
    struct ILeaf {};

    struct INode {
      std::shared_ptr<inner> a0;
      uint64_t a1;
      std::shared_ptr<inner> a2;
    };

    using variant_t = std::variant<ILeaf, INode>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    inner() {}

    explicit inner(ILeaf _v) : v_(_v) {}

    explicit inner(INode _v) : v_(std::move(_v)) {}

    static inner ileaf() { return inner(ILeaf{}); }

    static inner inode(inner a0, uint64_t a1, inner a2) {
      return inner(INode{std::make_shared<inner>(std::move(a0)), a1,
                         std::make_shared<inner>(std::move(a2))});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    /// TEST 3: Transform outer tree — rebuild with modified inner values.
    inner double_inner() const {
      if (std::holds_alternative<typename inner::ILeaf>(this->v())) {
        return inner::ileaf();
      } else {
        const auto &[a0, a1, a2] = std::get<typename inner::INode>(this->v());
        return inner::inode(a0->double_inner(), (a1 * UINT64_C(2)),
                            a2->double_inner());
      }
    }

    uint64_t inner_sum() const {
      if (std::holds_alternative<typename inner::ILeaf>(this->v())) {
        return UINT64_C(0);
      } else {
        const auto &[a0, a1, a2] = std::get<typename inner::INode>(this->v());
        return ((a0->inner_sum() + a1) + a2->inner_sum());
      }
    }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, inner &, T1 &, uint64_t &,
                                     inner &, T1 &>
    T1 inner_rec(T1 f, F1 &&f0) const {
      if (std::holds_alternative<typename inner::ILeaf>(this->v())) {
        return f;
      } else {
        const auto &[a0, a1, a2] = std::get<typename inner::INode>(this->v());
        return f0(*a0, a0->template inner_rec<T1>(f, f0), a1, *a2,
                  a2->template inner_rec<T1>(f, f0));
      }
    }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, inner &, T1 &, uint64_t &,
                                     inner &, T1 &>
    T1 inner_rect(T1 f, F1 &&f0) const {
      if (std::holds_alternative<typename inner::ILeaf>(this->v())) {
        return f;
      } else {
        const auto &[a0, a1, a2] = std::get<typename inner::INode>(this->v());
        return f0(*a0, a0->template inner_rect<T1>(f, f0), a1, *a2,
                  a2->template inner_rect<T1>(f, f0));
      }
    }
  };

  /// An outer tree type with an inner tree as a non-recursive field.
  struct outer {
    // TYPES
    struct OLeaf {};

    struct ONode {
      std::shared_ptr<outer> a0;
      inner a1;
      std::shared_ptr<outer> a2;
    };

    using variant_t = std::variant<OLeaf, ONode>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    outer() {}

    explicit outer(OLeaf _v) : v_(_v) {}

    explicit outer(ONode _v) : v_(std::move(_v)) {}

    static outer oleaf() { return outer(OLeaf{}); }

    static outer onode(outer a0, inner a1, outer a2) {
      return outer(ONode{std::make_shared<outer>(std::move(a0)), std::move(a1),
                         std::make_shared<outer>(std::move(a2))});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    /// TEST 6: Dup outer tree — use outer value twice.
    std::pair<outer, outer> dup_outer() const {
      return std::make_pair(*this, *this);
    }

    outer transform_outer() const {
      if (std::holds_alternative<typename outer::OLeaf>(this->v())) {
        return outer::oleaf();
      } else {
        const auto &[a0, a1, a2] = std::get<typename outer::ONode>(this->v());
        return outer::onode(a0->transform_outer(), a1.double_inner(),
                            a2->transform_outer());
      }
    }

    uint64_t outer_sum() const {
      if (std::holds_alternative<typename outer::OLeaf>(this->v())) {
        return UINT64_C(0);
      } else {
        const auto &[a0, a1, a2] = std::get<typename outer::ONode>(this->v());
        return ((a0->outer_sum() + a1.inner_sum()) + a2->outer_sum());
      }
    }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, outer &, T1 &, inner &, outer &,
                                     T1 &>
    T1 outer_rec(T1 f, F1 &&f0) const {
      if (std::holds_alternative<typename outer::OLeaf>(this->v())) {
        return f;
      } else {
        const auto &[a0, a1, a2] = std::get<typename outer::ONode>(this->v());
        return f0(*a0, a0->template outer_rec<T1>(f, f0), a1, *a2,
                  a2->template outer_rec<T1>(f, f0));
      }
    }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, outer &, T1 &, inner &, outer &,
                                     T1 &>
    T1 outer_rect(T1 f, F1 &&f0) const {
      if (std::holds_alternative<typename outer::OLeaf>(this->v())) {
        return f;
      } else {
        const auto &[a0, a1, a2] = std::get<typename outer::ONode>(this->v());
        return f0(*a0, a0->template outer_rect<T1>(f, f0), a1, *a2,
                  a2->template outer_rect<T1>(f, f0));
      }
    }
  };

  /// An expression type with varying constructor arities.
  struct expr {
    // TYPES
    struct Lit {
      uint64_t a0;
    };

    struct Neg {
      std::shared_ptr<expr> a0;
    };

    struct Add {
      std::shared_ptr<expr> a0;
      std::shared_ptr<expr> a1;
    };

    struct Mul {
      std::shared_ptr<expr> a0;
      std::shared_ptr<expr> a1;
    };

    using variant_t = std::variant<Lit, Neg, Add, Mul>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    expr() {}

    explicit expr(Lit _v) : v_(std::move(_v)) {}

    explicit expr(Neg _v) : v_(std::move(_v)) {}

    explicit expr(Add _v) : v_(std::move(_v)) {}

    explicit expr(Mul _v) : v_(std::move(_v)) {}

    static expr lit(uint64_t a0) { return expr(Lit{a0}); }

    static expr neg(expr a0) {
      return expr(Neg{std::make_shared<expr>(std::move(a0))});
    }

    static expr add(expr a0, expr a1) {
      return expr(Add{std::make_shared<expr>(std::move(a0)),
                      std::make_shared<expr>(std::move(a1))});
    }

    static expr mul(expr a0, expr a1) {
      return expr(Mul{std::make_shared<expr>(std::move(a0)),
                      std::make_shared<expr>(std::move(a1))});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    /// TEST 8: Mixed operations — build outer from expr eval results,
    /// then transform. Cross-type interaction.
    inner expr_to_inner() const {
      if (std::holds_alternative<typename expr::Lit>(this->v())) {
        const auto &[a0] = std::get<typename expr::Lit>(this->v());
        return inner::inode(inner::ileaf(), a0, inner::ileaf());
      } else if (std::holds_alternative<typename expr::Neg>(this->v())) {
        const auto &[a0] = std::get<typename expr::Neg>(this->v());
        return a0->expr_to_inner();
      } else if (std::holds_alternative<typename expr::Add>(this->v())) {
        const auto &[a0, a1] = std::get<typename expr::Add>(this->v());
        return inner::inode(a0->expr_to_inner(), UINT64_C(0),
                            a1->expr_to_inner());
      } else {
        const auto &[a0, a1] = std::get<typename expr::Mul>(this->v());
        return inner::inode(a0->expr_to_inner(), UINT64_C(1),
                            a1->expr_to_inner());
      }
    }

    /// TEST 7: Map over expr tree — rebuild with transformed values.
    expr double_expr() const {
      if (std::holds_alternative<typename expr::Lit>(this->v())) {
        const auto &[a0] = std::get<typename expr::Lit>(this->v());
        return expr::lit((a0 * UINT64_C(2)));
      } else if (std::holds_alternative<typename expr::Neg>(this->v())) {
        const auto &[a0] = std::get<typename expr::Neg>(this->v());
        return expr::neg(a0->double_expr());
      } else if (std::holds_alternative<typename expr::Add>(this->v())) {
        const auto &[a0, a1] = std::get<typename expr::Add>(this->v());
        return expr::add(a0->double_expr(), a1->double_expr());
      } else {
        const auto &[a0, a1] = std::get<typename expr::Mul>(this->v());
        return expr::mul(a0->double_expr(), a1->double_expr());
      }
    }

    uint64_t eval_expr() const {
      if (std::holds_alternative<typename expr::Lit>(this->v())) {
        const auto &[a0] = std::get<typename expr::Lit>(this->v());
        return a0;
      } else if (std::holds_alternative<typename expr::Neg>(this->v())) {
        const auto &[a0] = std::get<typename expr::Neg>(this->v());
        return a0->eval_expr();
      } else if (std::holds_alternative<typename expr::Add>(this->v())) {
        const auto &[a0, a1] = std::get<typename expr::Add>(this->v());
        return (a0->eval_expr() + a1->eval_expr());
      } else {
        const auto &[a0, a1] = std::get<typename expr::Mul>(this->v());
        return (a0->eval_expr() * a1->eval_expr());
      }
    }

    template <typename T1, typename F0, typename F1, typename F2, typename F3>
      requires std::is_invocable_r_v<T1, F0 &, uint64_t &> &&
               std::is_invocable_r_v<T1, F1 &, expr &, T1 &> &&
               std::is_invocable_r_v<T1, F2 &, expr &, T1 &, expr &, T1 &> &&
               std::is_invocable_r_v<T1, F3 &, expr &, T1 &, expr &, T1 &>
    T1 expr_rec(F0 &&f, F1 &&f0, F2 &&f1, F3 &&f2) const {
      if (std::holds_alternative<typename expr::Lit>(this->v())) {
        const auto &[a0] = std::get<typename expr::Lit>(this->v());
        return f(a0);
      } else if (std::holds_alternative<typename expr::Neg>(this->v())) {
        const auto &[a0] = std::get<typename expr::Neg>(this->v());
        return f0(*a0, a0->template expr_rec<T1>(f, f0, f1, f2));
      } else if (std::holds_alternative<typename expr::Add>(this->v())) {
        const auto &[a0, a1] = std::get<typename expr::Add>(this->v());
        return f1(*a0, a0->template expr_rec<T1>(f, f0, f1, f2), *a1,
                  a1->template expr_rec<T1>(f, f0, f1, f2));
      } else {
        const auto &[a0, a1] = std::get<typename expr::Mul>(this->v());
        return f2(*a0, a0->template expr_rec<T1>(f, f0, f1, f2), *a1,
                  a1->template expr_rec<T1>(f, f0, f1, f2));
      }
    }

    template <typename T1, typename F0, typename F1, typename F2, typename F3>
      requires std::is_invocable_r_v<T1, F0 &, uint64_t &> &&
               std::is_invocable_r_v<T1, F1 &, expr &, T1 &> &&
               std::is_invocable_r_v<T1, F2 &, expr &, T1 &, expr &, T1 &> &&
               std::is_invocable_r_v<T1, F3 &, expr &, T1 &, expr &, T1 &>
    T1 expr_rect(F0 &&f, F1 &&f0, F2 &&f1, F3 &&f2) const {
      if (std::holds_alternative<typename expr::Lit>(this->v())) {
        const auto &[a0] = std::get<typename expr::Lit>(this->v());
        return f(a0);
      } else if (std::holds_alternative<typename expr::Neg>(this->v())) {
        const auto &[a0] = std::get<typename expr::Neg>(this->v());
        return f0(*a0, a0->template expr_rect<T1>(f, f0, f1, f2));
      } else if (std::holds_alternative<typename expr::Add>(this->v())) {
        const auto &[a0, a1] = std::get<typename expr::Add>(this->v());
        return f1(*a0, a0->template expr_rect<T1>(f, f0, f1, f2), *a1,
                  a1->template expr_rect<T1>(f, f0, f1, f2));
      } else {
        const auto &[a0, a1] = std::get<typename expr::Mul>(this->v());
        return f2(*a0, a0->template expr_rect<T1>(f, f0, f1, f2), *a1,
                  a1->template expr_rect<T1>(f, f0, f1, f2));
      }
    }
  };

  /// A three-child tree.
  struct tree3 {
    // TYPES
    struct T3Leaf {};

    struct T3Node {
      std::shared_ptr<tree3> a0;
      std::shared_ptr<tree3> a1;
      std::shared_ptr<tree3> a2;
      uint64_t a3;
    };

    using variant_t = std::variant<T3Leaf, T3Node>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    tree3() {}

    explicit tree3(T3Leaf _v) : v_(_v) {}

    explicit tree3(T3Node _v) : v_(std::move(_v)) {}

    static tree3 t3leaf() { return tree3(T3Leaf{}); }

    static tree3 t3node(tree3 a0, tree3 a1, tree3 a2, uint64_t a3) {
      return tree3(T3Node{std::make_shared<tree3>(std::move(a0)),
                          std::make_shared<tree3>(std::move(a1)),
                          std::make_shared<tree3>(std::move(a2)), a3});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    uint64_t tree3_sum() const {
      if (std::holds_alternative<typename tree3::T3Leaf>(this->v())) {
        return UINT64_C(0);
      } else {
        const auto &[a0, a1, a2, a3] =
            std::get<typename tree3::T3Node>(this->v());
        return (((a0->tree3_sum() + a1->tree3_sum()) + a2->tree3_sum()) + a3);
      }
    }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, tree3 &, T1 &, tree3 &, T1 &,
                                     tree3 &, T1 &, uint64_t &>
    T1 tree3_rec(T1 f, F1 &&f0) const {
      if (std::holds_alternative<typename tree3::T3Leaf>(this->v())) {
        return f;
      } else {
        const auto &[a0, a1, a2, a3] =
            std::get<typename tree3::T3Node>(this->v());
        return f0(*a0, a0->template tree3_rec<T1>(f, f0), *a1,
                  a1->template tree3_rec<T1>(f, f0), *a2,
                  a2->template tree3_rec<T1>(f, f0), a3);
      }
    }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, tree3 &, T1 &, tree3 &, T1 &,
                                     tree3 &, T1 &, uint64_t &>
    T1 tree3_rect(T1 f, F1 &&f0) const {
      if (std::holds_alternative<typename tree3::T3Leaf>(this->v())) {
        return f;
      } else {
        const auto &[a0, a1, a2, a3] =
            std::get<typename tree3::T3Node>(this->v());
        return f0(*a0, a0->template tree3_rect<T1>(f, f0), *a1,
                  a1->template tree3_rect<T1>(f, f0), *a2,
                  a2->template tree3_rect<T1>(f, f0), a3);
      }
    }
  };

  /// TEST 1: Build and sum an outer tree with inner tree values.
  /// Tests nested value-type clone/destructor interaction.
  static inline const uint64_t test_outer_basic = []() {
    outer o = outer::onode(
        outer::onode(outer::oleaf(),
                     inner::inode(inner::ileaf(), UINT64_C(10), inner::ileaf()),
                     outer::oleaf()),
        inner::inode(inner::inode(inner::ileaf(), UINT64_C(1), inner::ileaf()),
                     UINT64_C(2),
                     inner::inode(inner::ileaf(), UINT64_C(3), inner::ileaf())),
        outer::onode(outer::oleaf(),
                     inner::inode(inner::ileaf(), UINT64_C(20), inner::ileaf()),
                     outer::oleaf()));
    return std::move(o).outer_sum();
  }();
  /// TEST 2: Dup pattern — use inner tree twice in outer construction.
  static outer dup_inner(inner i);
  static inline const uint64_t test_dup_inner = []() {
    inner i = inner::inode(
        inner::inode(inner::ileaf(), UINT64_C(5), inner::ileaf()), UINT64_C(10),
        inner::inode(inner::ileaf(), UINT64_C(15), inner::ileaf()));
    return dup_inner(std::move(i)).outer_sum();
  }();
  static inline const uint64_t test_transform = []() {
    outer o = outer::onode(
        outer::oleaf(),
        inner::inode(inner::ileaf(), UINT64_C(5), inner::ileaf()),
        outer::onode(outer::oleaf(),
                     inner::inode(inner::ileaf(), UINT64_C(10), inner::ileaf()),
                     outer::oleaf()));
    return std::move(o).transform_outer().outer_sum();
  }();
  /// TEST 4: Build and evaluate a complex expression tree.
  static inline const uint64_t test_expr = []() {
    expr e = expr::add(
        expr::mul(expr::add(expr::lit(UINT64_C(2)), expr::lit(UINT64_C(3))),
                  expr::lit(UINT64_C(4))),
        expr::neg(expr::add(expr::lit(UINT64_C(10)), expr::lit(UINT64_C(5)))));
    return std::move(e).eval_expr();
  }();
  /// TEST 5: Deep 3-child tree to stress clone/destructor.
  static tree3 build_tree3(uint64_t n);
  static inline const uint64_t test_tree3 =
      build_tree3(UINT64_C(4)).tree3_sum();
  static inline const uint64_t test_dup_outer = []() {
    outer o =
        outer::onode(outer::oleaf(),
                     inner::inode(inner::ileaf(), UINT64_C(42), inner::ileaf()),
                     outer::oleaf());
    std::pair<outer, outer> p = std::move(o).dup_outer();
    return (p.first.outer_sum() + p.second.outer_sum());
  }();
  static inline const uint64_t test_double_expr =
      expr::add(expr::lit(UINT64_C(5)),
                expr::mul(expr::lit(UINT64_C(3)), expr::lit(UINT64_C(7))))
          .double_expr()
          .eval_expr();

  static inline const uint64_t test_cross_type = []() {
    expr e =
        expr::add(expr::lit(UINT64_C(5)),
                  expr::mul(expr::lit(UINT64_C(3)), expr::lit(UINT64_C(7))));
    inner i = std::move(e).expr_to_inner();
    outer o = outer::onode(outer::oleaf(), i, outer::oleaf());
    return (std::move(o).outer_sum() + std::move(i).inner_sum());
  }();
};

#endif // INCLUDED_MEM_SAFETY_PROBE29
