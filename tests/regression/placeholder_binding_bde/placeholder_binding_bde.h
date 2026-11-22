#pragma once

#include "small_vector.h"
#include <atomic>
#include <bsl_concepts.h>
#include <bsl_functional.h>
#include <bsl_iostream.h>
#include <bsl_memory.h>
#include <bsl_stdexcept.h>
#include <bsl_string.h>
#include <bsl_type_traits.h>
#include <bsl_variant.h>
#include <bsl_vector.h>
#include <utility>

using namespace BloombergLP;
template <class From, class To>
concept convertible_to = bsl::is_convertible<From, To>::value;

template <class T, class U>
concept same_as = bsl::is_same<T, U>::value && bsl::is_same<U, T>::value;

struct PlaceholderBindingBde {
  struct tree {
    // TYPES
    struct Leaf {};

    struct Node {
      bsl::shared_ptr<tree> d_l;
      unsigned int d_x;
      bsl::shared_ptr<tree> d_r;
    };

    using variant_t = bsl::variant<Leaf, Node>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    tree() {}

    explicit tree(Leaf _v) : d_v_(_v) {}

    explicit tree(Node _v) : d_v_(bsl::move(_v)) {}

    static tree leaf() { return tree(Leaf{}); }

    static tree node(tree l, unsigned int x, tree r) {
      return tree(Node{bsl::make_shared<tree>(bsl::move(l)), x,
                       bsl::make_shared<tree>(bsl::move(r))});
    }

    // MANIPULATORS
    ~tree() {
      // Release the children this node alone owns in a loop, not recursively,
      // so a deep value cannot overflow the stack.
      if (bsl::holds_alternative<Leaf>(v_mut())) {
        return;
      }
      if (auto *_alt = bsl::get_if<Node>(&v_mut())) {
        if (!((_alt->d_l && _alt->d_l.use_count() == 1) ||
              (_alt->d_r && _alt->d_r.use_count() == 1))) {
          return;
        }
      }
      crane::small_vector<bsl::shared_ptr<tree>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = bsl::get_if<Node>(&_v)) {
          if (_alt->d_l && _alt->d_l.use_count() == 1) {
            _stack.push_back(bsl::move(_alt->d_l));
          }
          if (_alt->d_r && _alt->d_r.use_count() == 1) {
            _stack.push_back(bsl::move(_alt->d_r));
          }
        }
      };
      _drain(v_mut());
      while (!_stack.empty()) {
        auto _cur = bsl::move(_stack.back());
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

    inline variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    const variant_t &v() const { return d_v_; }
  };

  template <typename T1, typename F1>
  static T1 tree_rect(T1 f, F1 &&f0, const tree &t) {
    if (bsl::holds_alternative<typename tree::Leaf>(t.v())) {
      return f;
    } else {
      const auto &[d_l, d_x, d_r] = bsl::get<typename tree::Node>(t.v());
      return f0(*d_l, tree_rect<T1>(f, f0, *d_l), d_x, *d_r,
                tree_rect<T1>(f, f0, *d_r));
    }
  }

  template <typename T1, typename F1>
  static T1 tree_rec(T1 f, F1 &&f0, const tree &t) {
    return tree_rect<T1>(bsl::move(f), f0, t);
  }

  static unsigned int middle(const tree &t);
  static inline const unsigned int result =
      middle(tree::node(tree::leaf(), 7u, tree::leaf()));
};
