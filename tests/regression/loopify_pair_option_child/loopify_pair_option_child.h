#ifndef INCLUDED_LOOPIFY_PAIR_OPTION_CHILD
#define INCLUDED_LOOPIFY_PAIR_OPTION_CHILD

#include "crane_fn.h"
#include "small_vector.h"
#include <atomic>
#include <cstdint>
#include <memory>
#include <optional>
#include <utility>
#include <variant>

struct LoopifyPairOptionChild {
  struct tree {
    // TYPES
    struct Leaf {};

    struct Node {
      std::shared_ptr<tree> a0;
      std::shared_ptr<std::pair<uint64_t, std::optional<tree>>> a1;
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

    static tree node(tree a0, std::pair<uint64_t, std::optional<tree>> a1) {
      return tree(Node{
          std::make_shared<tree>(std::move(a0)),
          std::make_shared<std::pair<uint64_t, std::optional<tree>>>(
              std::move(a1))});
    }

    // MANIPULATORS
    ~tree() {
      // Release the children this node alone owns in a loop, not recursively,
      // so a deep value cannot overflow the stack.
      if (std::holds_alternative<Leaf>(v_mut())) {
        return;
      }
      crane::small_vector<std::shared_ptr<tree>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<Node>(&_v)) {
          if (_alt->a0 && _alt->a0.use_count() == 1) {
            _stack.push_back(std::move(_alt->a0));
          }
          if (_alt->a1 && _alt->a1.use_count() == 1) {
            std::atomic_thread_fence(std::memory_order_acquire);
            if (_alt->a1->second.has_value()) {
              _stack.push_back(
                  std::make_shared<tree>(std::move(*_alt->a1->second)));
            }
            _alt->a1.reset();
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
    // Explicit stack replaces the non-tail recursion of tree_rect: _call frames
    // are pending calls, _after frames resume a caller.
    struct _call {
      const tree *t;
    };

    struct _after_tree_rect_in_Node {
      std::shared_ptr<tree> a0;
      std::shared_ptr<std::pair<uint64_t, std::optional<tree>>> a1;
    };

    using _frame = std::variant<_call, _after_tree_rect_in_Node>;
    T1 _result{};
    crane::small_vector<_frame> _stack;
    _stack.emplace_back(_call{&t});
    while (!_stack.empty()) {
      _frame &_popped = _stack.back();
      if (std::holds_alternative<_call>(_popped)) {
        auto _f = std::move(std::get<_call>(_popped));
        _stack.pop_back();
        const tree &t = *_f.t;
        if (std::holds_alternative<typename tree::Leaf>(t.v())) {
          _result = f;
        } else {
          const auto &[a0, a1] = std::get<typename tree::Node>(t.v());
          _stack.emplace_back(_after_tree_rect_in_Node{a0, a1});
          _stack.emplace_back(_call{crane_raw(a0)});
        }
      } else {
        auto _f = std::move(std::get<_after_tree_rect_in_Node>(_popped));
        _stack.pop_back();
        std::shared_ptr<tree> a0 = std::move(_f.a0);
        std::shared_ptr<std::pair<uint64_t, std::optional<tree>>> a1 =
            std::move(_f.a1);
        _result = f0(*a0, std::move(_result), *a1);
      }
    }
    return _result;
  }

  template <typename T1, typename F1>
  static T1 tree_rec(T1 f, F1 &&f0, const tree &t) {
    return tree_rect<T1>(std::move(f), f0, t);
  }

  static uint64_t sum(const tree &t);
  static inline const uint64_t result =
      sum(tree::node(
          tree::leaf(),
          std::make_pair(
              UINT64_C(1),
              std::make_optional<tree>(tree::node(
                  tree::leaf(),
                  std::make_pair(UINT64_C(2), std::optional<tree>()))))));
};

#endif // INCLUDED_LOOPIFY_PAIR_OPTION_CHILD
