#ifndef INCLUDED_REUSE_MOVE_SHADOW
#define INCLUDED_REUSE_MOVE_SHADOW

#include "small_vector.h"
#include <atomic>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

struct ReuseMoveShadow {
  struct tree {
    // TYPES
    struct Node {
      uint64_t a0;
      std::shared_ptr<tree> a1;
      std::shared_ptr<tree> a2;
    };

    struct Leaf {};

    using variant_t = std::variant<Node, Leaf>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    tree() {}

    explicit tree(Node _v) : v_(std::move(_v)) {}

    explicit tree(Leaf _v) : v_(_v) {}

    static tree node(uint64_t a0, tree a1, tree a2) {
      return tree(Node{a0, std::make_shared<tree>(std::move(a1)),
                       std::make_shared<tree>(std::move(a2))});
    }

    static tree leaf() { return tree(Leaf{}); }

    // MANIPULATORS
    ~tree() {
      crane::small_vector<std::shared_ptr<tree>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<Node>(&_v)) {
          if (_alt->a1) {
            _stack.push_back(std::move(_alt->a1));
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
          std::atomic_thread_fence(std::memory_order_acquire);
          _drain(_cur->v_mut());
        }
      }
    }

    tree(const tree &) = default;
    tree &operator=(const tree &) = default;
    tree(tree &&) noexcept = default;
    tree &operator=(tree &&) noexcept = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, uint64_t &, tree &, T1 &, tree &,
                                   T1 &>
  static T1 tree_rect(F0 &&f, T1 f0, const tree &t) {
    if (std::holds_alternative<typename tree::Node>(t.v())) {
      const auto &[a0, a1, a2] = std::get<typename tree::Node>(t.v());
      return f(a0, *a1, tree_rect<T1>(f, f0, *a1), *a2,
               tree_rect<T1>(f, f0, *a2));
    } else {
      return f0;
    }
  }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, uint64_t &, tree &, T1 &, tree &,
                                   T1 &>
  static T1 tree_rec(F0 &&f, T1 f0, const tree &t) {
    if (std::holds_alternative<typename tree::Node>(t.v())) {
      const auto &[a0, a1, a2] = std::get<typename tree::Node>(t.v());
      return f(a0, *a1, tree_rec<T1>(f, f0, *a1), *a2,
               tree_rec<T1>(f, f0, *a2));
    } else {
      return f0;
    }
  }

  static uint64_t tree_sum(const tree &t);
  static tree dup_left(tree t, bool b);
  static inline const uint64_t test1 = tree_sum(
      dup_left(tree::node(UINT64_C(10),
                          tree::node(UINT64_C(1), tree::leaf(), tree::leaf()),
                          tree::node(UINT64_C(2), tree::leaf(), tree::leaf())),
               true));
  static inline const uint64_t test2 = tree_sum(dup_left(
      tree::node(UINT64_C(5),
                 tree::node(UINT64_C(3),
                            tree::node(UINT64_C(4), tree::leaf(), tree::leaf()),
                            tree::leaf()),
                 tree::leaf()),
      true));
  static inline const uint64_t test3 = []() {
    tree t = tree::node(UINT64_C(7),
                        tree::node(UINT64_C(8), tree::leaf(), tree::leaf()),
                        tree::node(UINT64_C(9), tree::leaf(), tree::leaf()));
    return (tree_sum(dup_left(t, true)) + tree_sum(t));
  }();
};

#endif // INCLUDED_REUSE_MOVE_SHADOW
