#ifndef INCLUDED_NAME_CLASH_MATCH_MATCH
#define INCLUDED_NAME_CLASH_MATCH_MATCH

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

struct NameClashMatchMatch {
  /// Test: match on the result of another match, both non-trivial.
  /// The inner match creates an IIFE, the outer match also creates an IIFE.
  /// Both might generate _sv/_m variable names that could clash.
  struct tree {
    // TYPES
    struct Leaf {};

    struct Node {
      std::shared_ptr<tree> a0;
      uint64_t a1;
      std::shared_ptr<tree> a2;
    };

    using variant_t = std::variant<Leaf, Node>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    tree() {}

    explicit tree(Leaf _v) : v_(_v) {}

    explicit tree(Node _v) : v_(std::move(_v)) {}

    static tree leaf() { return tree(Leaf{}); }

    static tree node(tree a0, uint64_t a1, tree a2) {
      return tree(Node{std::make_shared<tree>(std::move(a0)), a1,
                       std::make_shared<tree>(std::move(a2))});
    }

    // MANIPULATORS
    ~tree() {
      std::vector<std::shared_ptr<tree>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<Node>(&_v)) {
          if (_alt->a0) {
            _stack.push_back(std::move(_alt->a0));
          }
          if (_alt->a2) {
            _stack.push_back(std::move(_alt->a2));
          }
        }
      };
      _drain(v_mut());
      while (!_stack.empty()) {
        auto _cur = std::move(_stack.back());
        _stack.pop_back();
        if (_cur.use_count() == 1) {
          _drain(_cur->v_mut());
        }
      }
    }

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename F1>
    requires std::is_invocable_r_v<T1, F1 &, tree &, T1 &, uint64_t &, tree &,
                                   T1 &>
  static T1 tree_rect(T1 f, F1 &&f0, const tree &t) {
    if (std::holds_alternative<typename tree::Leaf>(t.v())) {
      return f;
    } else {
      const auto &[a0, a1, a2] = std::get<typename tree::Node>(t.v());
      return f0(*a0, tree_rect<T1>(f, f0, *a0), a1, *a2,
                tree_rect<T1>(f, f0, *a2));
    }
  }

  template <typename T1, typename F1>
    requires std::is_invocable_r_v<T1, F1 &, tree &, T1 &, uint64_t &, tree &,
                                   T1 &>
  static T1 tree_rec(T1 f, F1 &&f0, const tree &t) {
    if (std::holds_alternative<typename tree::Leaf>(t.v())) {
      return f;
    } else {
      const auto &[a0, a1, a2] = std::get<typename tree::Node>(t.v());
      return f0(*a0, tree_rec<T1>(f, f0, *a0), a1, *a2,
                tree_rec<T1>(f, f0, *a2));
    }
  }
  /// Returns a subtree based on a direction.
  enum class Dir { GOLEFT, GORIGHT };

  template <typename T1> static T1 dir_rect(T1 f, T1 f0, Dir d) {
    switch (d) {
    case Dir::GOLEFT: {
      return f;
    }
    case Dir::GORIGHT: {
      return f0;
    }
    default:
      std::unreachable();
    }
  }

  template <typename T1> static T1 dir_rec(T1 f, T1 f0, Dir d) {
    switch (d) {
    case Dir::GOLEFT: {
      return f;
    }
    case Dir::GORIGHT: {
      return f0;
    }
    default:
      std::unreachable();
    }
  }

  static tree choose_subtree(Dir d, const tree &t);
  /// Match on the result of choose_subtree (which itself contains a match).
  static uint64_t subtree_value(Dir d, const tree &t);
  /// Inline match-on-match: both matches are expressions.
  static uint64_t inline_match_match(Dir d, const tree &t);
  /// Two matches on the same scrutinee.
  static uint64_t double_match(const tree &t);
  /// Match where the scrutinee is a function call that returns an inductive,
  /// and the result is used in another match.
  static uint64_t chained(const tree &t);
};

#endif // INCLUDED_NAME_CLASH_MATCH_MATCH
