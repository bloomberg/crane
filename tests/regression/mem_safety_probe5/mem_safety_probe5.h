#pragma once

#include "crane_fn.h"
#include "fn.h"
#include "obj.h"
#include "small_vector.h"
#include <atomic>
#include <cstdint>
#include <memory>
#include <optional>
#include <stdexcept>
#include <utility>
#include <variant>

struct MemSafetyProbe5 {
  /// These tests probe interactions between:
  /// - Closures that access nested fields of value types
  /// - Loopification storing closures in frames
  /// - The body_derefs_var override in cpp_print.ml
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

    /// TEST 4: Deep tree with closures at each level.
    uint64_t tree_size() const {
      const tree *_self = this;

      // Explicit stack replaces the non-tail recursion of tree_size: _call
      // frames are pending calls, _after frames resume a caller.
      struct _call {
        const tree *_self;
      };

      struct _after_tree_size_in_Node {
        const tree *a2;
      };

      struct _after_tree_size_in_Node_2 {
        uint64_t _tmp2;
      };

      using _frame = std::variant<_call, _after_tree_size_in_Node,
                                  _after_tree_size_in_Node_2>;
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
            const auto &[a0, _, a2] = std::get<typename tree::Node>(_sv.v());
            _stack.emplace_back(_after_tree_size_in_Node{crane_raw(a2)});
            _stack.emplace_back(_call{crane_raw(a0)});
          }
        } else if (std::holds_alternative<_after_tree_size_in_Node>(_popped)) {
          auto _f = std::move(std::get<_after_tree_size_in_Node>(_popped));
          _stack.pop_back();
          const tree &a2 = *_f.a2;
          _stack.emplace_back(_after_tree_size_in_Node_2{_result});
          _stack.emplace_back(_call{_f.a2});
        } else {
          auto _f = std::move(std::get<_after_tree_size_in_Node_2>(_popped));
          _stack.pop_back();
          _result = ((UINT64_C(1) + _f._tmp2) + _result);
        }
      }
      return _result;
    }

    /// TEST 3: Pair a partial app with its tree, use both after
    /// the tree might have been moved.
    uint64_t pair_and_apply() const {
      tree _self_val = *this;
      crane::fn<uint64_t(uint64_t)> f =
          [=, _self_val = std::move(_self_val)](uint64_t _x0) -> uint64_t {
            return _self_val.get_left_val(_x0);
          };
      uint64_t v = [&]() {
        if (std::holds_alternative<typename tree::Leaf>(this->v())) {
          return UINT64_C(0);
        } else {
          const auto &[_, a1, _] = std::get<typename tree::Node>(this->v());
          return a1;
        }
      }();
      return f(v);
    }

    /// A function that accesses a NESTED field — forces a
    /// dereference of a unique_ptr inside the lambda body.
    uint64_t get_left_val(uint64_t default0) const {
      if (std::holds_alternative<typename tree::Leaf>(this->v())) {
        return default0;
      } else {
        const auto &[a0, _, _] = std::get<typename tree::Node>(this->v());
        auto &&_sv0 = *a0;
        if (std::holds_alternative<typename tree::Leaf>(_sv0.v())) {
          return default0;
        } else {
          const auto &[_, a10, _] = std::get<typename tree::Node>(_sv0.v());
          return a10;
        }
      }
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

  template <typename A> struct mylist {
    // TYPES
    struct Mynil {};

    struct Mycons {
      A a0;
      std::shared_ptr<mylist<A>> a1;
    };

    using variant_t = std::variant<Mynil, Mycons>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    mylist() {}

    explicit mylist(Mynil _v) : v_(_v) {}

    explicit mylist(Mycons _v) : v_(std::move(_v)) {}

    template <typename CraneU>
    mylist(const mylist<CraneU> &_other)
        : v_([&]() -> variant_t {
            if (std::holds_alternative<typename mylist<CraneU>::Mynil>(
                    _other.v())) {
              return Mynil{};
            } else {
              const auto &[a0, a1] =
                  std::get<typename mylist<CraneU>::Mycons>(_other.v());
              return Mycons{
                  [&]() -> A {
                    if constexpr (crane_convertible<A, const CraneU &>) {
                      return crane_convert<A>(a0);
                    } else {
                      throw std::logic_error("unreachable: inactive "
                                             "constructor field at this "
                                             "instantiation");
                    }
                  }(),
                  (a1 ? std::make_shared<mylist<A>>(
                            crane_convert<mylist<A>>(*a1))
                      : nullptr)};
            }
          }()) {}

    static mylist<A> mynil() { return mylist<A>(Mynil{}); }

    static mylist<A> mycons(A a0, crane::shared_child_slot<mylist<A>> a1) {
      return mylist<A>(Mycons{std::move(a0), a1.take()});
    }

    // MANIPULATORS
    ~mylist() {
      // Release the children this node alone owns in a loop, not recursively,
      // so a deep value cannot overflow the stack.
      auto _next = [&](variant_t &_v) -> std::shared_ptr<mylist<A>> {
        if (auto *_alt = std::get_if<Mycons>(&_v)) {
          if (_alt->a1 && _alt->a1.use_count() == 1) {
            std::atomic_thread_fence(std::memory_order_acquire);
            return std::move(_alt->a1);
          }
        }
        return nullptr;
      };
      std::shared_ptr<mylist<A>> _cur = _next(v_mut());
      while (_cur) {
        _cur = _next(_cur->v_mut());
      }
    }

    mylist(const mylist &) = default;
    mylist &operator=(const mylist &) = default;
    mylist(mylist &&) = default;
    mylist &operator=(mylist &&) = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    template <typename T1, typename F1> T1 mylist_rec(T1 f, F1 &&f0) const {
      return this->template mylist_rect<T1>(std::move(f), f0);
    }

    template <typename T1, typename F1> T1 mylist_rect(T1 f, F1 &&f0) const {
      const mylist<A> *_self = this;

      // Explicit stack replaces the non-tail recursion of mylist_rect: _call
      // frames are pending calls, _after frames resume a caller.
      struct _call {
        const mylist<A> *_self;
      };

      struct _after_mylist_rect_in_Mycons {
        A a0;
        std::shared_ptr<mylist<A>> a1;
      };

      using _frame = std::variant<_call, _after_mylist_rect_in_Mycons>;
      T1 _result{};
      crane::small_vector<_frame> _stack;
      _stack.emplace_back(_call{_self});
      while (!_stack.empty()) {
        _frame &_popped = _stack.back();
        if (std::holds_alternative<_call>(_popped)) {
          auto _f = std::move(std::get<_call>(_popped));
          _stack.pop_back();
          const mylist<A> *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename mylist<A>::Mynil>(_sv.v())) {
            _result = f;
          } else {
            const auto &[a0, a1] =
                std::get<typename mylist<A>::Mycons>(_sv.v());
            _stack.emplace_back(_after_mylist_rect_in_Mycons{a0, a1});
            _stack.emplace_back(_call{crane_raw(a1)});
          }
        } else {
          auto _f = std::move(std::get<_after_mylist_rect_in_Mycons>(_popped));
          _stack.pop_back();
          auto a0 = std::move(_f.a0);
          std::shared_ptr<mylist<A>> a1 = std::move(_f.a1);
          _result = f0(a0, *a1, std::move(_result));
        }
      }
      return _result;
    }
  };

  /// TEST 1: Partial app of get_left_val, applied to recursive result.
  /// The closure body accesses nested tree structure.
  static uint64_t sum_left_vals(const mylist<tree> &l);
  static inline const uint64_t test_sum_left =
      sum_left_vals(mylist<tree>::mycons(
          tree::node(tree::node(tree::leaf(), UINT64_C(10), tree::leaf()),
                     UINT64_C(20), tree::leaf()),
          mylist<tree>::mycons(
              tree::node(tree::node(tree::leaf(), UINT64_C(30), tree::leaf()),
                         UINT64_C(40), tree::leaf()),
              mylist<tree>::mycons(
                  tree::node(tree::leaf(), UINT64_C(50), tree::leaf()),
                  mylist<tree>::mynil()))));
  /// TEST 2: Build a list of partial apps from trees, then apply all.
  /// Each partial app captures a tree with nested structure.
  static mylist<crane::fn<uint64_t(uint64_t)>>
  build_getters(const mylist<tree> &l);
  static uint64_t apply_all(const mylist<crane::fn<uint64_t(uint64_t)>> &l,
                            uint64_t x);
  static inline const uint64_t test_build_apply = []() {
    mylist<tree> trees = mylist<tree>::mycons(
        tree::node(tree::node(tree::leaf(), UINT64_C(10), tree::leaf()),
                   UINT64_C(20), tree::leaf()),
        mylist<tree>::mycons(
            tree::node(tree::node(tree::leaf(), UINT64_C(30), tree::leaf()),
                       UINT64_C(40), tree::leaf()),
            mylist<tree>::mycons(
                tree::node(tree::leaf(), UINT64_C(50), tree::leaf()),
                mylist<tree>::mynil())));
    mylist<crane::fn<uint64_t(uint64_t)>> getters =
        build_getters(std::move(trees));
    return apply_all(std::move(getters), UINT64_C(0));
  }();
  static inline const uint64_t test_pair_apply =
      tree::node(tree::node(tree::leaf(), UINT64_C(10), tree::leaf()),
                 UINT64_C(20), tree::leaf())
          .pair_and_apply();
  static mylist<crane::fn<uint64_t(uint64_t)>>
  collect_left_vals(tree t, mylist<crane::fn<uint64_t(uint64_t)>> acc);
  static inline const uint64_t test_collect = []() {
    tree t = tree::node(
        tree::node(tree::node(tree::leaf(), UINT64_C(5), tree::leaf()),
                   UINT64_C(10), tree::leaf()),
        UINT64_C(15),
        tree::node(tree::leaf(), UINT64_C(20),
                   tree::node(tree::leaf(), UINT64_C(25), tree::leaf())));
    mylist<crane::fn<uint64_t(uint64_t)>> fns = collect_left_vals(
        std::move(t), mylist<crane::fn<uint64_t(uint64_t)>>::mynil());
    return apply_all(std::move(fns), UINT64_C(0));
  }();
  /// TEST 6: Stress test with very large list of trees.
  static mylist<tree> make_tree_list(uint64_t n);
  static uint64_t sum_getters(const mylist<crane::fn<uint64_t(uint64_t)>> &l,
                              uint64_t x);
  static inline const uint64_t test_stress = []() {
    mylist<tree> trees = make_tree_list(UINT64_C(50));
    mylist<crane::fn<uint64_t(uint64_t)>> getters =
        build_getters(std::move(trees));
    return sum_getters(std::move(getters), UINT64_C(0));
  }();
};
