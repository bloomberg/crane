#ifndef INCLUDED_CPS_CLOSURE_CHAIN
#define INCLUDED_CPS_CLOSURE_CHAIN

#include "small_vector.h"
#include <atomic>
#include <functional>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

struct CpsClosureChain {
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
      crane::small_vector<std::shared_ptr<tree>> _stack = {};
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

  static uint64_t tree_sum_cps(const tree &t,
                               std::function<uint64_t(uint64_t)> k) {
    if (std::holds_alternative<typename tree::Leaf>(t.v())) {
      return k(UINT64_C(0));
    } else {
      const auto &[a0, a1, a2] = std::get<typename tree::Node>(t.v());
      const tree &a0_value = *a0;
      const tree &a2_value = *a2;
      return tree_sum_cps(a0_value, [=](uint64_t left_sum) mutable {
        return tree_sum_cps(a2_value, [=](uint64_t right_sum) mutable {
          return k(((left_sum + a1) + right_sum));
        });
      });
    }
  }

  static uint64_t tree_sum(const tree &t);
  static tree build_left(uint64_t n);
  static tree build_right(uint64_t n);
  static tree build_balanced(uint64_t n);
  static inline const uint64_t test_left = tree_sum(build_left(UINT64_C(5)));
  static inline const uint64_t test_right = tree_sum(build_right(UINT64_C(5)));
  static inline const uint64_t test_balanced =
      tree_sum(build_balanced(UINT64_C(3)));

  template <typename F2>
    requires std::is_invocable_r_v<uint64_t, F2 &, uint64_t &, uint64_t &,
                                   uint64_t &>
  static uint64_t tree_fold_cps(const tree &t, uint64_t base, F2 &&combine,
                                std::function<uint64_t(uint64_t)> k) {
    if (std::holds_alternative<typename tree::Leaf>(t.v())) {
      return k(base);
    } else {
      const auto &[a0, a1, a2] = std::get<typename tree::Node>(t.v());
      const tree &a0_value = *a0;
      const tree &a2_value = *a2;
      return tree_fold_cps(
          a0_value, base, combine, [=](uint64_t left_result) mutable {
            return tree_fold_cps(
                a2_value, base, combine, [=](uint64_t right_result) mutable {
                  return k(combine(left_result, a1, right_result));
                });
          });
    }
  }

  static inline const uint64_t test_fold = tree_fold_cps(
      tree::node(tree::node(tree::leaf(), UINT64_C(2), tree::leaf()),
                 UINT64_C(3),
                 tree::node(tree::leaf(), UINT64_C(4), tree::leaf())),
      UINT64_C(1),
      [](uint64_t l, uint64_t n, uint64_t r) { return ((l + n) + r); },
      [](uint64_t x) { return x; });
  static inline const std::pair<uint64_t, uint64_t> test_pair = []() {
    tree t = build_left(UINT64_C(4));
    uint64_t s = tree_sum(t);
    uint64_t f = tree_fold_cps(
        std::move(t), UINT64_C(0),
        [](uint64_t l, uint64_t n, uint64_t r) { return ((l + n) + r); },
        [](uint64_t x) { return x; });
    return std::make_pair(s, f);
  }();
};

#endif // INCLUDED_CPS_CLOSURE_CHAIN
