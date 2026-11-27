#pragma once

#include "crane_fn.h"
#include "obj.h"
#include "small_vector.h"
#include <atomic>
#include <cstdint>
#include <memory>
#include <stdexcept>
#include <utility>
#include <variant>

struct LoopifyFilterFnRef {
  /// A binary tree with elements at nodes.
  template <typename A> struct tree {
    // TYPES
    struct Leaf {};

    struct Node {
      std::shared_ptr<tree<A>> a0;
      A a1;
      std::shared_ptr<tree<A>> a2;
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

    template <typename CraneU>
    tree(const tree<CraneU> &_other)
        : v_([&]() -> variant_t {
            if (std::holds_alternative<typename tree<CraneU>::Leaf>(_other.v())) {
              return Leaf{};
            } else {
              const auto &[a0, a1, a2] =
                  std::get<typename tree<CraneU>::Node>(_other.v());
              return Node{
                  (a0 ? std::make_shared<tree<A>>(crane_convert<tree<A>>(*a0))
                      : nullptr),
                  [&]() -> A {
                    if constexpr (crane_convertible<A, const CraneU &>) {
                      return crane_convert<A>(a1);
                    } else {
                      throw std::logic_error("unreachable: inactive "
                                             "constructor field at this "
                                             "instantiation");
                    }
                  }(),
                  (a2 ? std::make_shared<tree<A>>(crane_convert<tree<A>>(*a2))
                      : nullptr)};
            }
          }()) {}

    static tree<A> leaf() { return tree<A>(Leaf{}); }

    static tree<A> node(crane::shared_child_slot<tree<A>> a0, A a1,
                        crane::shared_child_slot<tree<A>> a2) {
      return tree<A>(Node{a0.take(), std::move(a1), a2.take()});
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
      crane::small_vector<std::shared_ptr<tree<A>>> _stack = {};
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
  };

  template <typename T1, typename T2, typename F1>
  static T2 tree_rect(T2 f, F1 &&f0, const tree<T1> &t) {
    // Explicit stack replaces the non-tail recursion of tree_rect: _call frames
    // are pending calls, _after frames resume a caller.
    struct _call {
      const tree<T1> *t;
    };

    struct _after_tree_rect_in_Node {
      std::shared_ptr<tree<T1>> a0;
      T1 a1;
      const tree<T1> *a2;
    };

    struct _after_tree_rect_in_Node_2 {
      std::shared_ptr<tree<T1>> a0;
      T1 a1;
      const tree<T1> *a2;
      T2 _tmp2;
    };

    using _frame = std::variant<_call, _after_tree_rect_in_Node,
                                _after_tree_rect_in_Node_2>;
    T2 _result{};
    crane::small_vector<_frame> _stack;
    _stack.emplace_back(_call{&t});
    while (!_stack.empty()) {
      _frame &_popped = _stack.back();
      if (std::holds_alternative<_call>(_popped)) {
        auto _f = std::move(std::get<_call>(_popped));
        _stack.pop_back();
        const tree<T1> &t = *_f.t;
        if (std::holds_alternative<typename tree<T1>::Leaf>(t.v())) {
          _result = f;
        } else {
          const auto &[a0, a1, a2] = std::get<typename tree<T1>::Node>(t.v());
          _stack.emplace_back(_after_tree_rect_in_Node{a0, a1, crane_raw(a2)});
          _stack.emplace_back(_call{crane_raw(a0)});
        }
      } else if (std::holds_alternative<_after_tree_rect_in_Node>(_popped)) {
        auto _f = std::move(std::get<_after_tree_rect_in_Node>(_popped));
        _stack.pop_back();
        std::shared_ptr<tree<T1>> a0 = std::move(_f.a0);
        auto a1 = std::move(_f.a1);
        const tree<T1> &a2 = *_f.a2;
        _stack.emplace_back(_after_tree_rect_in_Node_2{
            std::move(a0), std::move(a1), &a2, std::move(_result)});
        _stack.emplace_back(_call{&a2});
      } else {
        auto _f = std::move(std::get<_after_tree_rect_in_Node_2>(_popped));
        _stack.pop_back();
        std::shared_ptr<tree<T1>> a0 = std::move(_f.a0);
        auto a1 = std::move(_f.a1);
        const tree<T1> &a2 = *_f.a2;
        _result = f0(*a0, std::move(_f._tmp2), a1, a2, std::move(_result));
      }
    }
    return _result;
  }

  template <typename T1, typename T2, typename F1>
  static T2 tree_rec(T2 f, F1 &&f0, const tree<T1> &t) {
    return tree_rect<T1, T2>(std::move(f), f0, t);
  }

  /// Recursive filter: takes a predicate f and recurses on both subtrees.
  /// When loopified, f is stored in continuation frame structs.
  /// If f is passed as a function reference (e.g. a named function),
  /// the template parameter F0 deduces to a reference type, and the
  /// generated frame struct field F0 f becomes ill-formed with std::move.
  template <typename T1, typename F0>
  static tree<T1> filter(F0 &&f, const tree<T1> &t) {
    // Explicit stack replaces the non-tail recursion of filter: _call frames
    // are pending calls, _after frames resume a caller.
    struct _call {
      const tree<T1> *t;
    };

    struct _after_filter_in_Node {
      T1 a1;
      const tree<T1> *a2;
    };

    struct _after_filter_in_Node_2 {
      T1 a1;
      tree<T1> l_;
    };

    using _frame =
        std::variant<_call, _after_filter_in_Node, _after_filter_in_Node_2>;
    tree<T1> _result{};
    crane::small_vector<_frame> _stack;
    _stack.emplace_back(_call{&t});
    while (!_stack.empty()) {
      _frame &_popped = _stack.back();
      if (std::holds_alternative<_call>(_popped)) {
        auto _f = std::move(std::get<_call>(_popped));
        _stack.pop_back();
        const tree<T1> &t = *_f.t;
        if (std::holds_alternative<typename tree<T1>::Leaf>(t.v())) {
          _result = tree<T1>::leaf();
        } else {
          const auto &[a0, a1, a2] = std::get<typename tree<T1>::Node>(t.v());
          _stack.emplace_back(_after_filter_in_Node{a1, crane_raw(a2)});
          _stack.emplace_back(_call{crane_raw(a0)});
        }
      } else if (std::holds_alternative<_after_filter_in_Node>(_popped)) {
        auto _f = std::move(std::get<_after_filter_in_Node>(_popped));
        _stack.pop_back();
        auto a1 = std::move(_f.a1);
        const tree<T1> &a2 = *_f.a2;
        _stack.emplace_back(
            _after_filter_in_Node_2{std::move(a1), std::move(_result)});
        _stack.emplace_back(_call{&a2});
      } else {
        auto _f = std::move(std::get<_after_filter_in_Node_2>(_popped));
        _stack.pop_back();
        auto a1 = std::move(_f.a1);
        tree<T1> l_ = std::move(_f.l_);
        tree<T1> r_ = std::move(_result);
        if (f(a1)) {
          _result = tree<T1>::node(std::move(l_), std::move(a1), std::move(r_));
        } else {
          _result = std::move(l_);
        }
      }
    }
    return _result;
  }

  /// A concrete predicate — will be passed as a function reference.
  static bool is_positive(uint64_t n);
  /// Entry point that calls filter with a named function.
  static inline const tree<uint64_t> test_filter = filter<uint64_t>(
      is_positive,
      tree<uint64_t>::node(
          tree<uint64_t>::node(tree<uint64_t>::leaf(), UINT64_C(0),
                               tree<uint64_t>::leaf()),
          UINT64_C(1), tree<uint64_t>::node(tree<uint64_t>::leaf(), UINT64_C(2),
                                            tree<uint64_t>::leaf())));
};
