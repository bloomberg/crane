#pragma once

#include "crane_fn.h"
#include "small_vector.h"
#include <atomic>
#include <cstdint>
#include <memory>
#include <optional>
#include <utility>
#include <variant>

#include "crane_bake.h"
extern const crane::bake::image crane_baked_node_3a59f1e24d86;
extern const crane::bake::image crane_baked_num_31b926459d9a;

struct BakeStdOptional {
  struct tree {
    // TYPES
    struct Leaf {};

    struct Node {
      std::shared_ptr<tree> l;
      uint64_t x;
      std::shared_ptr<tree> r;
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

    static tree node(crane::shared_child_slot<tree> l, uint64_t x,
                     crane::shared_child_slot<tree> r) {
      return tree(Node{l.take(), x, r.take()});
    }

    // MANIPULATORS
    ~tree() {
      // Release the children this node alone owns in a loop, not recursively,
      // so a deep value cannot overflow the stack.
      if (std::holds_alternative<Leaf>(v_mut())) {
        return;
      }
      if (auto *_alt = std::get_if<Node>(&v_mut())) {
        if (!((_alt->l && _alt->l.use_count() == 1) ||
              (_alt->r && _alt->r.use_count() == 1))) {
          return;
        }
      }
      crane::small_vector<std::shared_ptr<tree>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<Node>(&_v)) {
          if (_alt->l && _alt->l.use_count() == 1) {
            _stack.push_back(std::move(_alt->l));
          }
          if (_alt->r && _alt->r.use_count() == 1) {
            _stack.push_back(std::move(_alt->r));
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
    tree(tree &&) = default;
    tree &operator=(tree &&) = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename F1>
  static T1 tree_rect(T1 f, F1 &&f0, const tree &t) {
    if (std::holds_alternative<typename tree::Leaf>(t.v())) {
      return f;
    } else {
      const auto &[l0, x0, r0] = std::get<typename tree::Node>(t.v());
      return f0(*l0, tree_rect<T1>(f, f0, *l0), x0, *r0,
                tree_rect<T1>(f, f0, *r0));
    }
  }

  template <typename T1, typename F1>
  static T1 tree_rec(T1 f, F1 &&f0, const tree &t) {
    return tree_rect<T1>(std::move(f), f0, t);
  }

  static inline const std::optional<uint64_t> num =
      crane::bake::value{crane_baked_num_31b926459d9a};
  static inline const std::optional<tree> node =
      crane::bake::value{crane_baked_node_3a59f1e24d86};
  static inline const uint64_t num_value = []() -> uint64_t {
    if (num.has_value()) {
      const uint64_t &n = *num;
      return n;
    } else {
      return UINT64_C(0);
    }
  }();
  static inline const uint64_t node_value = []() -> uint64_t {
    if (node.has_value()) {
      const tree &t = *node;
      if (std::holds_alternative<typename tree::Leaf>(t.v())) {
        return UINT64_C(0);
      } else {
        const auto &[_, x0, _] = std::get<typename tree::Node>(t.v());
        return x0;
      }
    } else {
      return UINT64_C(0);
    }
  }();
};
