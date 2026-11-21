#pragma once

#include <cstdint>
#include <utility>
#define CRANE_NON_ATOMIC_RC 1
#define CRANE_SINGLE_THREADED 1
#include "crane_variant.h"
#include "rc.h"
#include "shared_block.h"
#include "shared_variant.h"

struct ImmortalStickyCount {
  struct tree {
    // TYPES
    struct Leaf {};

    struct Node {
      crane::shared_box<tree> a0;
      uint64_t a1;
      crane::shared_box<tree> a2;
    };

    using variant_t = crane::shared_variant<Leaf, Node>;

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
      return tree(Node{crane::shared_box<tree>::make(std::move(a0)), a1,
                       crane::shared_box<tree>::make(std::move(a2))});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename F1>
  static T1 tree_rect(T1 f, F1 &&f0, const tree &t) {
    if (crane::holds_alternative<typename tree::Leaf>(t.v())) {
      return f;
    } else {
      const auto &[a0, a1, a2] = crane::get<typename tree::Node>(t.v());
      return f0(*a0, tree_rect<T1>(f, f0, *a0), a1, *a2,
                tree_rect<T1>(f, f0, *a2));
    }
  }

  template <typename T1, typename F1>
  static T1 tree_rec(T1 f, F1 &&f0, const tree &t) {
    return tree_rect<T1>(std::move(f), f0, t);
  }

  static tree full(uint64_t d);
  static uint64_t size(const tree &t);
  [[gnu::used]] static inline const tree table =
      crane::immortal(full(UINT64_C(4)));
  /// Built at run time: counted.
  static tree fresh(uint64_t x0_);
  /// n uses of the global, each a copy.
  static uint64_t sizes(uint64_t n, uint64_t acc);
};
