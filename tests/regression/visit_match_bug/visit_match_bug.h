#ifndef INCLUDED_VISIT_MATCH_BUG
#define INCLUDED_VISIT_MATCH_BUG

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

struct VisitMatchBug {
  struct Tree {
    // TYPES
    struct Leaf {
      uint64_t a0;
    };

    struct Node {
      std::shared_ptr<Tree> a0;
      uint64_t a1;
      std::shared_ptr<Tree> a2;
    };

    using variant_t = std::variant<Leaf, Node>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    Tree() {}

    explicit Tree(Leaf _v) : v_(std::move(_v)) {}

    explicit Tree(Node _v) : v_(std::move(_v)) {}

    static Tree leaf(uint64_t a0) { return Tree(Leaf{a0}); }

    static Tree node(Tree a0, uint64_t a1, Tree a2) {
      return Tree(Node{std::make_shared<Tree>(std::move(a0)), a1,
                       std::make_shared<Tree>(std::move(a2))});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename F0, typename F1>
    requires std::is_invocable_r_v<T1, F0 &, uint64_t &> &&
             std::is_invocable_r_v<T1, F1 &, Tree &, T1 &, uint64_t &, Tree &,
                                   T1 &>
  static T1 Tree_rect(F0 &&f, F1 &&f0, const Tree &t) {
    if (std::holds_alternative<typename Tree::Leaf>(t.v())) {
      const auto &[a0] = std::get<typename Tree::Leaf>(t.v());
      return f(a0);
    } else {
      const auto &[a0, a1, a2] = std::get<typename Tree::Node>(t.v());
      return f0(*a0, Tree_rect<T1>(f, f0, *a0), a1, *a2,
                Tree_rect<T1>(f, f0, *a2));
    }
  }

  template <typename T1, typename F0, typename F1>
    requires std::is_invocable_r_v<T1, F0 &, uint64_t &> &&
             std::is_invocable_r_v<T1, F1 &, Tree &, T1 &, uint64_t &, Tree &,
                                   T1 &>
  static T1 Tree_rec(F0 &&f, F1 &&f0, const Tree &t) {
    if (std::holds_alternative<typename Tree::Leaf>(t.v())) {
      const auto &[a0] = std::get<typename Tree::Leaf>(t.v());
      return f(a0);
    } else {
      const auto &[a0, a1, a2] = std::get<typename Tree::Node>(t.v());
      return f0(*a0, Tree_rec<T1>(f, f0, *a0), a1, *a2,
                Tree_rec<T1>(f, f0, *a2));
    }
  }

  static Tree consume(Tree t);
  static uint64_t match_after_consume(const Tree &t);
  static uint64_t match_last_use(const Tree &t);
  static uint64_t nested_match_consume(const Tree &t);
  static uint64_t chain_then_match(const Tree &t1);

  struct State {
    uint64_t value;
    uint64_t data;

    // ACCESSORS
    State clone() const { return State{this->value, this->data}; }
  };

  static uint64_t match_extract_field(const State &s);
  static uint64_t match_extract_two(const State &s);
  static uint64_t match_nested(const State &s);
  static uint64_t match_in_tail(const State &s);
  static uint64_t match_in_expr(const State &s);
};

#endif // INCLUDED_VISIT_MATCH_BUG
