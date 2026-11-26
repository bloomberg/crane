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

struct MemSafetyProbe25 {
  /// Probe 25: Closure capture of match-bound value-type variables.
  ///
  /// Attack vector: When a function matches on a value type and returns
  /// a closure from inside the match branch, the closure captures
  /// structured-binding references (d_a0, d_a1, d_a2). After IIFE
  /// inlining, return_captures_by_value may miss the lambda inside
  /// the Smatch branches, leaving & capture. The closure then holds
  /// dangling references to the function's local structured bindings.
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

    /// TEST 8: Option wrapping a closure from match.
    /// Exercises different code path for returning closures
    /// through an inductive constructor.
    std::optional<crane::fn<uint64_t(uint64_t)>>
    match_closure_opt(bool b) const {
      tree _self_val = *this;
      if (b) {
        return std::make_optional<crane::fn<uint64_t(uint64_t)>>(
            crane::fn<uint64_t(uint64_t)>([=, _self_val = std::move(_self_val)](
                uint64_t x)
                                               -> uint64_t {
              if (std::holds_alternative<typename tree::Leaf>(_self_val.v())) {
                return x;
              } else {
                const auto &[a0, a1, a2] =
                    std::get<typename tree::Node>(_self_val.v());
                return (((x + a0->tree_sum()) + a1) + a2->tree_sum());
              }
            }));
      } else {
        return std::optional<crane::fn<uint64_t(uint64_t)>>();
      }
    }

    /// TEST 7: Return closure from match that captures a tree child,
    /// then store it in a pair. Double-wrapping test.
    std::pair<crane::fn<uint64_t(uint64_t)>, uint64_t> match_then_pair() const {
      tree _self_val = *this;
      crane::fn<uint64_t(uint64_t)> f =
          [=, _self_val = std::move(_self_val)](uint64_t x) {
            if (std::holds_alternative<typename tree::Leaf>(_self_val.v())) {
              return x;
            } else {
              const auto &[a0, a1, _] =
                  std::get<typename tree::Node>(_self_val.v());
              return ((x + a0->tree_sum()) + a1);
            }
          };
      return std::make_pair(std::move(f), this->tree_sum());
    }

    /// TEST 5: Deep match — closure captures grandchild of tree.
    /// ll is child-of-child, accessed via two levels of unique_ptr deref.
    uint64_t deep_match_closure(uint64_t x) const {
      if (std::holds_alternative<typename tree::Leaf>(this->v())) {
        return x;
      } else {
        const auto &[a0, a1, _] = std::get<typename tree::Node>(this->v());
        auto &&_sv0 = *a0;
        if (std::holds_alternative<typename tree::Leaf>(_sv0.v())) {
          return (x + a1);
        } else {
          const auto &[a00, a10, _] = std::get<typename tree::Node>(_sv0.v());
          return (((x + a00->tree_sum()) + a10) + a1);
        }
      }
    }

    /// TEST 4: Nested match returning closure. Both match levels
    /// contribute captured variables to the closure.
    uint64_t nested_match_closure(const tree &t2, uint64_t x) const {
      if (std::holds_alternative<typename tree::Leaf>(this->v())) {
        return x;
      } else {
        const auto &[a0, a1, _] = std::get<typename tree::Node>(this->v());
        if (std::holds_alternative<typename tree::Leaf>(t2.v())) {
          return (x + a1);
        } else {
          const auto &[_, a10, a20] = std::get<typename tree::Node>(t2.v());
          return (((x + a0->tree_sum()) + a10) + a20->tree_sum());
        }
      }
    }

    /// TEST 3: Return PAIR of closures from match.
    /// Each closure captures different match-bound children.
    std::pair<crane::fn<uint64_t(uint64_t)>, crane::fn<uint64_t(uint64_t)>>
    pair_closures() const {
      if (std::holds_alternative<typename tree::Leaf>(this->v())) {
        return std::make_pair(
            crane::fn<uint64_t(uint64_t)>([](uint64_t x) { return x; }),
            crane::fn<uint64_t(uint64_t)>([](uint64_t x) { return x; }));
      } else {
        const auto &[a0, _, a2] = std::get<typename tree::Node>(this->v());
        const tree &a0_value = *a0;
        const tree &a2_value = *a2;
        return std::make_pair(
            crane::fn<uint64_t(uint64_t)>([=, a0_value = a0_value](uint64_t x) {
              return (x + a0_value.tree_sum());
            }),
            crane::fn<uint64_t(uint64_t)>([=, a2_value = a2_value](uint64_t x) {
              return (x + a2_value.tree_sum());
            }));
      }
    }

    /// TEST 2: Return closure from match branch — captures children.
    /// After IIFE inlining, the Smatch is at the top level, and
    /// return_captures_by_value may not traverse into it.
    uint64_t match_closure(uint64_t x) const {
      if (std::holds_alternative<typename tree::Leaf>(this->v())) {
        return x;
      } else {
        const auto &[a0, a1, a2] = std::get<typename tree::Node>(this->v());
        return (((x + a0->tree_sum()) + a1) + a2->tree_sum());
      }
    }

    /// TEST 1: Return closure that captures the whole tree parameter.
    /// The closure body calls tree_sum on t. If t is passed by const ref
    /// and the closure uses &, t's binding dangles when function returns.
    /// The test calls the closure AFTER the tree temporary is destroyed.
    uint64_t make_sum_fn(uint64_t x) const { return (x + this->tree_sum()); }

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
          _result = ((_f._tmp2 + a1) + _result);
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

  static inline const uint64_t test_make_sum_fn =
      tree::node(tree::node(tree::leaf(), UINT64_C(3), tree::leaf()),
                 UINT64_C(7),
                 tree::node(tree::leaf(), UINT64_C(11),
                            tree::leaf()))
          .make_sum_fn(UINT64_C(100));
  static inline const uint64_t test_match_closure =
      tree::node(tree::node(tree::leaf(), UINT64_C(3), tree::leaf()),
                 UINT64_C(7),
                 tree::node(tree::leaf(), UINT64_C(11),
                            tree::leaf()))
          .match_closure(UINT64_C(100));
  static inline const uint64_t test_pair_closures = []() {
    std::pair<crane::fn<uint64_t(uint64_t)>, crane::fn<uint64_t(uint64_t)>> p =
        tree::node(tree::node(tree::leaf(), UINT64_C(3), tree::leaf()),
                   UINT64_C(7),
                   tree::node(tree::leaf(), UINT64_C(11),
                              tree::leaf()))
            .pair_closures();
    return (p.first(UINT64_C(100)) + p.second(UINT64_C(200)));
  }();
  static inline const uint64_t test_nested_match_closure =
      tree::node(tree::node(tree::leaf(), UINT64_C(3), tree::leaf()),
                 UINT64_C(7),
                 tree::node(tree::leaf(), UINT64_C(11),
                            tree::leaf()))
          .nested_match_closure(tree::node(
          tree::node(tree::leaf(), UINT64_C(2), tree::leaf()), UINT64_C(5),
          tree::node(tree::leaf(), UINT64_C(8), tree::leaf())),
                                UINT64_C(100));
  static inline const uint64_t test_deep_match_closure =
      tree::node(
          tree::node(tree::node(tree::leaf(), UINT64_C(1), tree::leaf()),
                     UINT64_C(2),
                     tree::node(tree::leaf(), UINT64_C(3), tree::leaf())),
          UINT64_C(10), tree::leaf())
          .deep_match_closure(UINT64_C(100));

  /// TEST 6: Build a list of closures from recursive tree traversal.
  /// Each closure captures v from the current node.
  /// Tests whether closures stored in constructor fields are safe.
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

  static mylist<crane::fn<uint64_t(uint64_t)>> build_adders(const tree &t);
  static uint64_t apply_first(const mylist<crane::fn<uint64_t(uint64_t)>> &l,
                              uint64_t x);
  static inline const uint64_t test_build_adders = []() {
    mylist<crane::fn<uint64_t(uint64_t)>> adders =
        build_adders(tree::node(tree::leaf(), UINT64_C(42), tree::leaf()));
    return apply_first(std::move(adders), UINT64_C(100));
  }();
  static inline const uint64_t test_match_then_pair = []() {
    std::pair<crane::fn<uint64_t(uint64_t)>, uint64_t> p =
        tree::node(tree::node(tree::leaf(), UINT64_C(4), tree::leaf()),
                   UINT64_C(6),
                   tree::node(tree::leaf(), UINT64_C(9),
                              tree::leaf()))
            .match_then_pair();
    return (p.first(UINT64_C(100)) + p.second);
  }();
  static inline const uint64_t test_match_closure_opt = []() -> uint64_t {
    auto _cs =
        tree::node(tree::node(tree::leaf(), UINT64_C(2), tree::leaf()),
                   UINT64_C(5),
                   tree::node(tree::leaf(), UINT64_C(8),
                              tree::leaf()))
            .match_closure_opt(true);
    if (_cs.has_value()) {
      const crane::fn<uint64_t(uint64_t)> &f = *_cs;
      return f(UINT64_C(100));
    } else {
      return UINT64_C(0);
    }
  }();
};
