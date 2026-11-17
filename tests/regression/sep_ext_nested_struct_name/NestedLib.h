#ifndef INCLUDED_NESTEDLIB
#define INCLUDED_NESTEDLIB

#include "small_vector.h"
#include <atomic>
#include <cstdint>
#include <memory>
#include <utility>
#include <variant>

namespace NestedLib {
struct Sub {
  struct Tree {
    // TYPES
    struct Leaf {};

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

    explicit Tree(Leaf _v) : v_(_v) {}

    explicit Tree(Node _v) : v_(std::move(_v)) {}

    static Tree leaf() { return Tree(Leaf{}); }

    static Tree node(Tree a0, uint64_t a1, Tree a2) {
      return Tree(Node{std::make_shared<Tree>(std::move(a0)), a1,
                       std::make_shared<Tree>(std::move(a2))});
    }

    // MANIPULATORS
    ~Tree() {
      // Release the children this node alone owns in a loop, not recursively,
      // so a deep value cannot overflow the stack.
      if (std::holds_alternative<Leaf>(v_mut())) {
        return;
      }
      if (auto *_alt = std::get_if<Node>(&v_mut())) {
        if (!((_alt->a0 && _alt->a0.use_count() == 1) ||
              (_alt->a2 && _alt->a2.use_count() == 1))) {
          return;
        }
      }
      crane::small_vector<std::shared_ptr<Tree>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<Node>(&_v)) {
          if (_alt->a0 && _alt->a0.use_count() == 1) {
            _stack.push_back(std::move(_alt->a0));
          }
          if (_alt->a2 && _alt->a2.use_count() == 1) {
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

    Tree(const Tree &) = default;
    Tree &operator=(const Tree &) = default;
    Tree(Tree &&) = default;
    Tree &operator=(Tree &&) = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  static uint64_t size(const Tree &t);
};
} // namespace NestedLib

#endif // INCLUDED_NESTEDLIB
