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

struct MemSafetyProbe16 {
  /// Probe 16: Focused on finding RUNTIME memory safety bugs.
  ///
  /// Attack vectors:
  /// 1. Higher-order functions that STORE closures in data structures
  /// then invoke them after the original scope ends
  /// 2. Partial application chains where each link captures a value
  /// that may have been moved
  /// 3. Functions that return closures from match branches where
  /// the closure captures match bindings from an OWNED match
  /// 4. fold/map patterns that build closure lists
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

    /// TEST 8: Higher-order map: apply a function to each element
    /// of a tree, building a new tree of closures.
    tree tree_map_val() const {
      const tree *_self = this;

      // Explicit stack replaces the non-tail recursion of tree_map_val: _call
      // frames are pending calls, _after frames resume a caller.
      struct _call {
        const tree *_self;
      };

      struct _after_tree_map_val_in_Node {
        uint64_t a1;
        const tree *a2;
      };

      struct _after_tree_map_val_in_Node_2 {
        uint64_t a1;
        tree _tmp2;
      };

      using _frame = std::variant<_call, _after_tree_map_val_in_Node,
                                  _after_tree_map_val_in_Node_2>;
      tree _result{};
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
            _result = tree::leaf();
          } else {
            const auto &[a0, a1, a2] = std::get<typename tree::Node>(_sv.v());
            _stack.emplace_back(_after_tree_map_val_in_Node{a1, crane_raw(a2)});
            _stack.emplace_back(_call{crane_raw(a0)});
          }
        } else if (std::holds_alternative<_after_tree_map_val_in_Node>(_popped)) {
          auto _f = std::move(std::get<_after_tree_map_val_in_Node>(_popped));
          _stack.pop_back();
          uint64_t a1 = _f.a1;
          const tree &a2 = *_f.a2;
          _stack.emplace_back(
              _after_tree_map_val_in_Node_2{a1, std::move(_result)});
          _stack.emplace_back(_call{_f.a2});
        } else {
          auto _f = std::move(std::get<_after_tree_map_val_in_Node_2>(_popped));
          _stack.pop_back();
          uint64_t a1 = _f.a1;
          _result = tree::node(std::move(_f._tmp2), a1 + UINT64_C(1),
                               std::move(_result));
        }
      }
      return _result;
    }

    /// TEST 6: Non-recursive closure from a deeply nested match.
    uint64_t deep_nested_closure(uint64_t n) const {
      if (std::holds_alternative<typename tree::Leaf>(this->v())) {
        return n;
      } else {
        const auto &[a0, a1, a2] = std::get<typename tree::Node>(this->v());
        auto &&_sv0 = *a0;
        if (std::holds_alternative<typename tree::Leaf>(_sv0.v())) {
          return a1 + a2->tree_sum() + n;
        } else {
          const auto &[a00, a10, a20] = std::get<typename tree::Node>(_sv0.v());
          auto &&_sv1 = *a2;
          if (std::holds_alternative<typename tree::Leaf>(_sv1.v())) {
            return a00->tree_sum() + a10 + a20->tree_sum() + a1 + n;
          } else {
            const auto &[a01, a11, a21] =
                std::get<typename tree::Node>(_sv1.v());
            return a00->tree_sum() + a10 + a20->tree_sum() + a1 +
                   a01->tree_sum() + a11 + a21->tree_sum() + n;
          }
        }
      }
    }

    /// TEST 5: A function that takes TWO trees and returns a closure
    /// capturing both. Tests double ownership.
    uint64_t pair_closure(const tree &t2, uint64_t n) const {
      return this->tree_sum() + t2.tree_sum() + n;
    }

    /// TEST 1: Store a closure derived from a tree in a list,
    /// then invoke it after the tree goes out of scope.
    /// The closure should capture by value.
    uint64_t make_summer(uint64_t n) const { return this->tree_sum() + n; }

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
          _stack.emplace_back(_after_tree_sum_in_Node_2{a1, _result});
          _stack.emplace_back(_call{_f.a2});
        } else {
          auto _f = std::move(std::get<_after_tree_sum_in_Node_2>(_popped));
          _stack.pop_back();
          uint64_t a1 = _f.a1;
          _result = _f._tmp2 + a1 + _result;
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

    uint64_t length() const {
      const mylist<A> *_self = this;

      // Explicit stack replaces the non-tail recursion of length: _call frames
      // are pending calls, _after frames resume a caller.
      struct _call {
        const mylist<A> *_self;
      };

      struct _after_length_in_Mycons {};

      using _frame = std::variant<_call, _after_length_in_Mycons>;
      uint64_t _result{};
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
            _result = UINT64_C(0);
          } else {
            const auto &[_, a1] = std::get<typename mylist<A>::Mycons>(_sv.v());
            _stack.emplace_back(_after_length_in_Mycons{});
            _stack.emplace_back(_call{crane_raw(a1)});
          }
        } else {
          auto _f = std::move(std::get<_after_length_in_Mycons>(_popped));
          _stack.pop_back();
          _result = UINT64_C(1) + _result;
        }
      }
      return _result;
    }

    mylist<A> myapp(mylist<A> l2) const {
      // Builds the result front to back: _write points at the empty tail the
      // next cell fills.
      std::optional<mylist<A>> _root{};
      std::shared_ptr<mylist<A>> *_write = nullptr;
      const mylist<A> *_loop_self = this;
      while (true) {
        auto &&_sv = *_loop_self;
        if (std::holds_alternative<typename mylist<A>::Mynil>(_sv.v())) {
          auto _value = std::move(l2);
          (_write ? *(*_write = std::make_shared<mylist<A>>(std::move(_value)))
                  : _root.emplace(std::move(_value)));
          break;
        } else {
          const auto &[a0, a1] = std::get<typename mylist<A>::Mycons>(_sv.v());
          auto _cell = typename mylist<A>::Mycons(a0, nullptr);
          mylist<A> &_node = (_write ? *(*_write = std::make_shared<mylist<A>>(
                                             std::move(_cell)))
                                     : _root.emplace(std::move(_cell)));
          _write = &std::get<typename mylist<A>::Mycons>(_node.v_mut()).a1;
          _loop_self = crane_raw(a1);
          continue;
        }
      }
      return std::move(*_root);
    }

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

  static uint64_t sum_list(const mylist<uint64_t> &l);
  static mylist<crane::fn<uint64_t(uint64_t)>>
  build_summers(const mylist<tree> &trees);
  static uint64_t apply_fns(const mylist<crane::fn<uint64_t(uint64_t)>> &fns,
                            uint64_t x);
  static inline const uint64_t test_store_closures = []() {
    mylist<tree> trees =
        mylist<tree>::mycons(
            tree::node(tree::leaf(), UINT64_C(10), tree::leaf()),
            mylist<tree>::mycons(
                tree::node(tree::leaf(), UINT64_C(20), tree::leaf()),
                mylist<tree>::mycons(
                    tree::node(tree::leaf(), UINT64_C(30), tree::leaf()),
                    mylist<tree>::mynil())));
    mylist<crane::fn<uint64_t(uint64_t)>> fns = build_summers(std::move(trees));
    return apply_fns(std::move(fns), UINT64_C(0));
  }();
  /// TEST 2: Fold that accumulates a function by composing closures.
  /// Each step captures the tree from the current list element.
  static uint64_t compose_summers(const mylist<tree> &trees,
                                  const crane::fn<uint64_t(uint64_t)> &acc,
                                  uint64_t x0_);
  static inline const uint64_t test_compose = []() {
    mylist<tree> trees =
        mylist<tree>::mycons(
            tree::node(tree::leaf(), UINT64_C(5), tree::leaf()),
            mylist<tree>::mycons(
                tree::node(tree::leaf(), UINT64_C(10), tree::leaf()),
                mylist<tree>::mycons(
                    tree::node(tree::leaf(), UINT64_C(15), tree::leaf()),
                    mylist<tree>::mynil())));
    return compose_summers(
        std::move(trees),
        [](uint64_t n) { return n; },
        UINT64_C(0));
  }();
  /// TEST 3: Build a list of closures where each closure captures
  /// the SAME tree at different levels.
  /// Tests whether the tree is properly cloned for each closure.
  static mylist<crane::fn<uint64_t(uint64_t)>> multi_capture_tree(tree t,
                                                                  uint64_t n);
  static inline const uint64_t test_multi_capture = []() {
    tree t = tree::node(tree::node(tree::leaf(), UINT64_C(3), tree::leaf()),
                        UINT64_C(7),
                        tree::node(tree::leaf(), UINT64_C(11), tree::leaf()));
    mylist<crane::fn<uint64_t(uint64_t)>> fns =
        multi_capture_tree(std::move(t), UINT64_C(3));
    return apply_fns(std::move(fns), UINT64_C(0));
  }();
  /// TEST 4: Return a closure from inside a NESTED match.
  /// The closure captures bindings from BOTH match levels.
  static uint64_t nested_match_closure(const tree &t, const mylist<uint64_t> &l,
                                       uint64_t n);
  static inline const uint64_t test_nested_match = []() {
    tree t = tree::node(tree::node(tree::leaf(), UINT64_C(5), tree::leaf()),
                        UINT64_C(10),
                        tree::node(tree::leaf(), UINT64_C(15), tree::leaf()));
    mylist<uint64_t> l = mylist<uint64_t>::mycons(
        UINT64_C(7),
        mylist<uint64_t>::mycons(UINT64_C(99), mylist<uint64_t>::mynil()));
    return nested_match_closure(std::move(t), std::move(l), UINT64_C(3));
  }();
  static inline const uint64_t test_pair_closure = []() {
    return []() {
      tree t1 = tree::node(tree::leaf(), UINT64_C(100), tree::leaf());
      tree t2 = tree::node(tree::node(tree::leaf(), UINT64_C(50), tree::leaf()),
                           UINT64_C(25), tree::leaf());
      crane::fn<uint64_t(uint64_t)> f =
          [=, t1 = std::move(t1), t2 = std::move(t2)](uint64_t _x0) -> uint64_t {
            return t1.pair_closure(std::move(t2), _x0);
          };
      return f(UINT64_C(0)) + f(UINT64_C(0));
    }();
  }();
  static inline const uint64_t test_deep_nested = []() {
    tree t = tree::node(
        tree::node(tree::node(tree::leaf(), UINT64_C(1), tree::leaf()),
                   UINT64_C(2),
                   tree::node(tree::leaf(), UINT64_C(3), tree::leaf())),
        UINT64_C(10),
        tree::node(tree::node(tree::leaf(), UINT64_C(4), tree::leaf()),
                   UINT64_C(5),
                   tree::node(tree::leaf(), UINT64_C(6), tree::leaf())));
    return t.deep_nested_closure(UINT64_C(0));
  }();
  /// TEST 7: Map + apply pattern: build closures from tree children,
  /// apply them to values from another list.
  static mylist<uint64_t>
  zip_apply(const mylist<crane::fn<uint64_t(uint64_t)>> &fns,
            const mylist<uint64_t> &vals);
  static inline const uint64_t test_zip_apply = []() {
    mylist<tree> trees =
        mylist<tree>::mycons(
            tree::node(tree::leaf(), UINT64_C(10), tree::leaf()),
            mylist<tree>::mycons(
                tree::node(tree::leaf(), UINT64_C(20), tree::leaf()),
                mylist<tree>::mynil()));
    mylist<crane::fn<uint64_t(uint64_t)>> fns = build_summers(std::move(trees));
    mylist<uint64_t> vals = mylist<uint64_t>::mycons(
        UINT64_C(1),
        mylist<uint64_t>::mycons(UINT64_C(2), mylist<uint64_t>::mynil()));
    mylist<uint64_t> results = zip_apply(std::move(fns), std::move(vals));
    return sum_list(std::move(results));
  }();
  static inline const uint64_t test_tree_map = []() {
    tree t = tree::node(tree::node(tree::leaf(), UINT64_C(1), tree::leaf()),
                        UINT64_C(2),
                        tree::node(tree::leaf(), UINT64_C(3), tree::leaf()));
    return t.tree_map_val().tree_sum();
  }();
  /// TEST 9: CPS-style flattening where each step builds a continuation
  /// that captures tree structure.
  static mylist<uint64_t>
  flatten_cps_aux(const tree &t,
                  const crane::fn<mylist<uint64_t>(mylist<uint64_t>)> &k);
  static mylist<uint64_t> flatten_cps(const tree &t);
  static inline const uint64_t test_flatten_cps = []() {
    tree t = tree::node(tree::node(tree::leaf(), UINT64_C(1), tree::leaf()),
                        UINT64_C(2),
                        tree::node(tree::leaf(), UINT64_C(3), tree::leaf()));
    return sum_list(flatten_cps(std::move(t)));
  }();
};
