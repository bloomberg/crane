#ifndef INCLUDED_NAME_CLASH_MATCH_MATCH
#define INCLUDED_NAME_CLASH_MATCH_MATCH

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

struct NameClashMatchMatch {
  /// Test: match on the result of another match, both non-trivial.
  /// The inner match creates an IIFE, the outer match also creates an IIFE.
  /// Both might generate _sv/_m variable names that could clash.
  struct tree {
    // TYPES
    struct Leaf {};

    struct Node {
      std::shared_ptr<tree> d_a0;
      unsigned int d_a1;
      std::shared_ptr<tree> d_a2;
    };

    using variant_t = std::variant<Leaf, Node>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    explicit tree(Leaf _v) : d_v_(_v) {}

    explicit tree(Node _v) : d_v_(std::move(_v)) {}

    static std::shared_ptr<tree> leaf() {
      return std::make_shared<tree>(Leaf{});
    }

    static std::shared_ptr<tree> node(const std::shared_ptr<tree> &a0,
                                      unsigned int a1,
                                      const std::shared_ptr<tree> &a2) {
      return std::make_shared<tree>(Node{a0, std::move(a1), a2});
    }

    static std::shared_ptr<tree> node(std::shared_ptr<tree> &&a0,
                                      unsigned int a1,
                                      std::shared_ptr<tree> &&a2) {
      return std::make_shared<tree>(
          Node{std::move(a0), std::move(a1), std::move(a2)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, MapsTo<T1, std::shared_ptr<tree>, T1, unsigned int,
                                std::shared_ptr<tree>, T1>
                             F1>
  static T1 tree_rect(const T1 f, F1 &&f0, const std::shared_ptr<tree> &t) {
    if (std::holds_alternative<typename tree::Leaf>(t->v())) {
      return f;
    } else {
      const auto &[d_a0, d_a1, d_a2] = std::get<typename tree::Node>(t->v());
      return f0(d_a0, tree_rect<T1>(f, f0, d_a0), d_a1, d_a2,
                tree_rect<T1>(f, f0, d_a2));
    }
  }

  template <typename T1, MapsTo<T1, std::shared_ptr<tree>, T1, unsigned int,
                                std::shared_ptr<tree>, T1>
                             F1>
  static T1 tree_rec(const T1 f, F1 &&f0, const std::shared_ptr<tree> &t) {
    if (std::holds_alternative<typename tree::Leaf>(t->v())) {
      return f;
    } else {
      const auto &[d_a0, d_a1, d_a2] = std::get<typename tree::Node>(t->v());
      return f0(d_a0, tree_rec<T1>(f, f0, d_a0), d_a1, d_a2,
                tree_rec<T1>(f, f0, d_a2));
    }
  }
  /// Returns a subtree based on a direction.
  enum class Dir { e_GOLEFT, e_GORIGHT };

  template <typename T1>
  static T1 dir_rect(const T1 f, const T1 f0, const Dir d) {
    switch (d) {
    case Dir::e_GOLEFT: {
      return f;
    }
    case Dir::e_GORIGHT: {
      return f0;
    }
    default:
      std::unreachable();
    }
  }

  template <typename T1>
  static T1 dir_rec(const T1 f, const T1 f0, const Dir d) {
    switch (d) {
    case Dir::e_GOLEFT: {
      return f;
    }
    case Dir::e_GORIGHT: {
      return f0;
    }
    default:
      std::unreachable();
    }
  }

  static std::shared_ptr<tree> choose_subtree(const Dir d,
                                              const std::shared_ptr<tree> &t);
  /// Match on the result of choose_subtree (which itself contains a match).
  __attribute__((pure)) static unsigned int
  subtree_value(const Dir d, const std::shared_ptr<tree> &t);
  /// Inline match-on-match: both matches are expressions.
  __attribute__((pure)) static unsigned int
  inline_match_match(const Dir d, const std::shared_ptr<tree> &t);
  /// Two matches on the same scrutinee.
  __attribute__((pure)) static unsigned int
  double_match(const std::shared_ptr<tree> &t);

  /// Match where the scrutinee is a function call that returns an inductive,
  /// and the result is used in another match.
  __attribute__((pure)) static unsigned int
  chained(const std::shared_ptr<tree> &t);
};

#endif // INCLUDED_NAME_CLASH_MATCH_MATCH
