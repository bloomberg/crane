#ifndef INCLUDED_METHOD_PARTIAL_APP
#define INCLUDED_METHOD_PARTIAL_APP

#include "crane_fn.h"
#include "fn.h"
#include "small_vector.h"
#include <atomic>
#include <cstdint>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

struct MethodPartialApp {
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

    static tree node(crane::shared_child_slot<tree> a0, uint64_t a1,
                     crane::shared_child_slot<tree> a2) {
      return tree(Node{a0.take(), a1, a2.take()});
    }

    // MANIPULATORS
    ~tree() {
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
      crane::small_vector<std::shared_ptr<tree>> _stack = {};
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

    tree(const tree &) = default;
    tree &operator=(const tree &) = default;
    tree(tree &&) = default;
    tree &operator=(tree &&) = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    /// add_to_sum: methodified on first arg (tree).
    /// Takes a tree and a nat, returns the tree's sum plus the nat.
    uint64_t add_to_sum(uint64_t x) const { return (this->tree_sum() + x); }

    uint64_t tree_sum() const {
      const tree *_self = this;

      // Explicit stack replaces the non-tail recursion of tree_sum: _call
      // frames are pending calls, _after frames resume a caller.
      struct _call {
        const tree *_self;
      };

      struct _after_tree_sum_in_Node {
        uint64_t a1;
        const tree *a2;
      };

      struct _after_tree_sum_in_Node_2 {
        uint64_t a1;
        uint64_t _tmp2;
      };

      using _frame = std::variant<_call, _after_tree_sum_in_Node,
                                  _after_tree_sum_in_Node_2>;
      uint64_t _result{};
      crane::small_vector<_frame> _stack;
      _stack.emplace_back(_call{_self});
      while (!_stack.empty()) {
        _frame &_popped = _stack.back();
        if (std::holds_alternative<_call>(_popped)) {
          auto _f = std::move(std::get<_call>(_popped));
          _stack.pop_back();
          const tree *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename tree::Leaf>(_sv.v())) {
            _result = UINT64_C(0);
          } else {
            const auto &[a0, a1, a2] = std::get<typename tree::Node>(_sv.v());
            _stack.emplace_back(_after_tree_sum_in_Node{a1, crane_raw(a2)});
            _stack.emplace_back(_call{crane_raw(a0)});
          }
        } else if (std::holds_alternative<_after_tree_sum_in_Node>(_popped)) {
          auto _f = std::move(std::get<_after_tree_sum_in_Node>(_popped));
          _stack.pop_back();
          uint64_t a1 = _f.a1;
          const tree &a2 = *_f.a2;
          _stack.emplace_back(_after_tree_sum_in_Node_2{a1,
                                                        std::move(_result)});
          _stack.emplace_back(_call{_f.a2});
        } else {
          auto _f = std::move(std::get<_after_tree_sum_in_Node_2>(_popped));
          _stack.pop_back();
          uint64_t a1 = _f.a1;
          _result = ((_f._tmp2 + a1) + std::move(_result));
        }
      }
      return _result;
    }

    template <typename T1, typename F1> T1 tree_rec(T1 f, F1 &&f0) const {
      return this->template tree_rect<T1>(std::move(f), f0);
    }

    template <typename T1, typename F1> T1 tree_rect(T1 f, F1 &&f0) const {
      const tree *_self = this;

      // Explicit stack replaces the non-tail recursion of tree_rect: _call
      // frames are pending calls, _after frames resume a caller.
      struct _call {
        const tree *_self;
      };

      struct _after_tree_rect_in_Node {
        std::shared_ptr<tree> a0;
        uint64_t a1;
        const tree *a2;
      };

      struct _after_tree_rect_in_Node_2 {
        std::shared_ptr<tree> a0;
        uint64_t a1;
        const tree *a2;
        T1 _tmp2;
      };

      using _frame = std::variant<_call, _after_tree_rect_in_Node,
                                  _after_tree_rect_in_Node_2>;
      T1 _result{};
      crane::small_vector<_frame> _stack;
      _stack.emplace_back(_call{_self});
      while (!_stack.empty()) {
        _frame &_popped = _stack.back();
        if (std::holds_alternative<_call>(_popped)) {
          auto _f = std::move(std::get<_call>(_popped));
          _stack.pop_back();
          const tree *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename tree::Leaf>(_sv.v())) {
            _result = f;
          } else {
            const auto &[a0, a1, a2] = std::get<typename tree::Node>(_sv.v());
            _stack.emplace_back(_after_tree_rect_in_Node{a0, a1,
                                                         crane_raw(a2)});
            _stack.emplace_back(_call{crane_raw(a0)});
          }
        } else if (std::holds_alternative<_after_tree_rect_in_Node>(_popped)) {
          auto _f = std::move(std::get<_after_tree_rect_in_Node>(_popped));
          _stack.pop_back();
          std::shared_ptr<tree> a0 = std::move(_f.a0);
          uint64_t a1 = _f.a1;
          const tree &a2 = *_f.a2;
          _stack.emplace_back(_after_tree_rect_in_Node_2{std::move(a0), a1, &a2,
                                                         std::move(_result)});
          _stack.emplace_back(_call{_f.a2});
        } else {
          auto _f = std::move(std::get<_after_tree_rect_in_Node_2>(_popped));
          _stack.pop_back();
          std::shared_ptr<tree> a0 = std::move(_f.a0);
          uint64_t a1 = _f.a1;
          const tree &a2 = *_f.a2;
          _result = f0(*a0, std::move(_f._tmp2), a1, a2, std::move(_result));
        }
      }
      return _result;
    }
  };

  /// Direct partial app stored in let, called twice.
  static inline const uint64_t method_partial_bug = []() {
    return []() {
      tree t = tree::node(tree::node(tree::leaf(), UINT64_C(10), tree::leaf()),
                          UINT64_C(20),
                          tree::node(tree::leaf(), UINT64_C(30), tree::leaf()));
      crane::fn<uint64_t(uint64_t)> f =
          [=, t = std::move(t)](uint64_t _x0) -> uint64_t {
            return t.add_to_sum(_x0);
          };
      return (f(UINT64_C(5)) + f(UINT64_C(10)));
    }();
  }();

  /// Partial app stored in a constructor.
  struct box {
    // DATA
    crane::fn<uint64_t(uint64_t)> a0;

    // ACCESSORS
    box clone() const { return {a0}; }

    // CREATORS
    static box box0(crane::fn<uint64_t(uint64_t)> a0) {
      return {std::move(a0)};
    }

    template <typename T1, typename F0> T1 box_rec(F0 &&f) const {
      return this->template box_rect<T1>(f);
    }

    template <typename T1, typename F0>
      requires std::is_invocable_r_v<T1, F0 &,
                                     const crane::fn<uint64_t(uint64_t)> &>
    T1 box_rect(F0 &&f) const {
      const auto &[a0] = *this;
      return f(a0);
    }
  };

  static inline const uint64_t method_partial_box = []() {
    return []() {
      tree t = tree::node(tree::node(tree::leaf(), UINT64_C(10), tree::leaf()),
                          UINT64_C(20),
                          tree::node(tree::leaf(), UINT64_C(30), tree::leaf()));
      box b = box::box0([=, t = std::move(t)](uint64_t _x0) -> uint64_t {
        return t.add_to_sum(_x0);
      });
      auto &[a0] = b;
      return (a0(UINT64_C(5)) + a0(UINT64_C(10)));
    }();
  }();
  /// Two partial apps from different trees.
  static inline const uint64_t method_partial_two = []() {
    return []() {
      tree t1 = tree::node(tree::leaf(), UINT64_C(10), tree::leaf());
      tree t2 = tree::node(tree::leaf(), UINT64_C(20), tree::leaf());
      crane::fn<uint64_t(uint64_t)> f1 =
          [&](uint64_t _x0) -> uint64_t { return t1.add_to_sum(_x0); };
      crane::fn<uint64_t(uint64_t)> f2 =
          [&](uint64_t _x0) -> uint64_t { return t2.add_to_sum(_x0); };
      return (f1(UINT64_C(0)) + f2(UINT64_C(0)));
    }();
  }();
};

#endif // INCLUDED_METHOD_PARTIAL_APP
