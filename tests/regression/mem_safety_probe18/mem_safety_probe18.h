#ifndef INCLUDED_MEM_SAFETY_PROBE18
#define INCLUDED_MEM_SAFETY_PROBE18

#include "crane_fn.h"
#include "fn.h"
#include "obj.h"
#include "small_vector.h"
#include <atomic>
#include <cstdint>
#include <memory>
#include <optional>
#include <stdexcept>
#include <type_traits>
#include <utility>
#include <variant>

struct MemSafetyProbe18 {
  /// Probe 18: Complex ownership handoff patterns.
  ///
  /// Attack vectors:
  /// 1. Functions where the SAME argument appears in multiple positions
  /// of a single constructor call (potential double-move)
  /// 2. let-binding a function of a value, then using the value AGAIN
  /// (ownership tracking across let-bindings)
  /// 3. Passing a closure to a higher-order function that calls it
  /// multiple times (std::function copy semantics)
  /// 4. Complex constructor nesting where tree values appear at
  /// multiple levels
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

    /// TEST 9: Triple-use of a tree: compute sum, build a new tree, compute sum
    /// again
    uint64_t triple_use() const {
      uint64_t s1 = this->tree_sum();
      tree t2 = tree::node(*this, s1, *this);
      uint64_t s2 = std::move(t2).tree_sum();
      return (s1 + s2);
    }

    /// TEST 7: Use a value type in a chain of let-bindings where
    /// each binding transforms the tree.
    uint64_t chain_transforms() const {
      tree t1 = tree::node(*this, UINT64_C(0), tree::leaf());
      tree t2 = tree::node(tree::leaf(), UINT64_C(0), std::move(t1));
      tree t3 = tree::node(std::move(t2), UINT64_C(0), *this);
      return std::move(t3).tree_sum();
    }

    /// TEST 4: Build a tree from a tree, using it at multiple levels.
    tree tree_from_tree() const {
      return tree::node(tree::node(*this, UINT64_C(0), tree::leaf()),
                        this->tree_sum(),
                        tree::node(tree::leaf(), UINT64_C(0), *this));
    }

    /// TEST 2: Let-bind tree_sum, then use the tree again.
    /// The tree should NOT be consumed by tree_sum.
    uint64_t let_reuse() const {
      uint64_t s = this->tree_sum();
      return (s + this->tree_sum());
    }

    /// TEST 1: Same tree used in TWO different positions of a single
    /// constructor. Tests whether the tree is properly cloned.
    tree dup_tree() const { return tree::node(*this, UINT64_C(0), *this); }

    uint64_t tree_sum() const {
      const tree *_self = this;

      /// CraneEnter: captures varying parameters for each recursive call.
      struct CraneEnter {
        const tree *_self;
      };

      /// CraneCont_Node: saves [a1, a2], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_Node {
        uint64_t a1;
        std::shared_ptr<tree> a2;
      };

      /// CraneCont_Node_1: saves [_tmp2, a1], resumes after recursive call,
      /// then processes rest.
      struct CraneCont_Node_1 {
        uint64_t _tmp2;
        uint64_t a1;
      };

      using CraneFrame =
          std::variant<CraneEnter, CraneCont_Node, CraneCont_Node_1>;
      uint64_t _result{};
      crane::small_vector<CraneFrame> _stack;
      _stack.emplace_back(CraneEnter{_self});
      /// Loopified tree_sum: CraneEnter -> CraneCont_Node -> CraneCont_Node_1.
      while (!_stack.empty()) {
        CraneFrame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<CraneEnter>(_frame)) {
          auto _f = std::move(std::get<CraneEnter>(_frame));
          const tree *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename tree::Leaf>(_sv.v())) {
            _result = UINT64_C(0);
          } else {
            const auto &[a0, a1, a2] = std::get<typename tree::Node>(_sv.v());
            _stack.emplace_back(CraneCont_Node{a1, a2});
            _stack.emplace_back(CraneEnter{crane_raw(a0)});
          }
        } else if (std::holds_alternative<CraneCont_Node>(_frame)) {
          auto _f = std::move(std::get<CraneCont_Node>(_frame));
          uint64_t a1 = _f.a1;
          std::shared_ptr<tree> a2 = std::move(_f.a2);
          _stack.emplace_back(CraneCont_Node_1{std::move(_result), a1});
          _stack.emplace_back(CraneEnter{crane_raw(a2)});
        } else {
          auto _f = std::move(std::get<CraneCont_Node_1>(_frame));
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

      /// CraneEnter: captures varying parameters for each recursive call.
      struct CraneEnter {
        const tree *_self;
      };

      /// CraneCont_Node: saves [a0, a1, a2], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_Node {
        std::shared_ptr<tree> a0;
        uint64_t a1;
        std::shared_ptr<tree> a2;
      };

      /// CraneCont_Node_1: saves [_tmp2, a0, a1, a2], resumes after recursive
      /// call, then processes rest.
      struct CraneCont_Node_1 {
        T1 _tmp2;
        std::shared_ptr<tree> a0;
        uint64_t a1;
        std::shared_ptr<tree> a2;
      };

      using CraneFrame =
          std::variant<CraneEnter, CraneCont_Node, CraneCont_Node_1>;
      T1 _result{};
      crane::small_vector<CraneFrame> _stack;
      _stack.emplace_back(CraneEnter{_self});
      /// Loopified tree_rect: CraneEnter -> CraneCont_Node -> CraneCont_Node_1.
      while (!_stack.empty()) {
        CraneFrame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<CraneEnter>(_frame)) {
          auto _f = std::move(std::get<CraneEnter>(_frame));
          const tree *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename tree::Leaf>(_sv.v())) {
            _result = f;
          } else {
            const auto &[a0, a1, a2] = std::get<typename tree::Node>(_sv.v());
            _stack.emplace_back(CraneCont_Node{a0, a1, a2});
            _stack.emplace_back(CraneEnter{crane_raw(a0)});
          }
        } else if (std::holds_alternative<CraneCont_Node>(_frame)) {
          auto _f = std::move(std::get<CraneCont_Node>(_frame));
          std::shared_ptr<tree> a0 = std::move(_f.a0);
          uint64_t a1 = _f.a1;
          std::shared_ptr<tree> a2 = std::move(_f.a2);
          _stack.emplace_back(
              CraneCont_Node_1{std::move(_result), std::move(a0), a1, a2});
          _stack.emplace_back(CraneEnter{crane_raw(a2)});
        } else {
          auto _f = std::move(std::get<CraneCont_Node_1>(_frame));
          std::shared_ptr<tree> a0 = std::move(_f.a0);
          uint64_t a1 = _f.a1;
          std::shared_ptr<tree> a2 = std::move(_f.a2);
          _result = f0(*a0, std::move(_f._tmp2), a1, *a2, std::move(_result));
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
                      throw std::logic_error(
                          "unreachable: inactive constructor field at this "
                          "instantiation");
                    }
                  }(),
                  (a1 ? std::make_shared<mylist<A>>(
                            crane_convert<mylist<A>>(*a1))
                      : nullptr)};
            }
          }()) {}

    static mylist<A> mynil() { return mylist<A>(Mynil{}); }

    static mylist<A> mycons(A a0, mylist<A> a1) {
      return mylist<A>(
          Mycons{std::move(a0), std::make_shared<mylist<A>>(std::move(a1))});
    }

    // MANIPULATORS
    ~mylist() {
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

    template <typename T1, typename F0>
      requires std::is_invocable_r_v<T1, F0 &, const A &>
    mylist<T1> map_list(F0 &&f) const {
      std::optional<mylist<T1>> _root{};
      std::shared_ptr<mylist<T1>> *_write = nullptr;
      const mylist<A> *_loop_self = this;
      while (true) {
        auto &&_sv = *_loop_self;
        if (std::holds_alternative<typename mylist<A>::Mynil>(_sv.v())) {
          auto _value = mylist<T1>::mynil();
          (_write ? *(*_write = std::make_shared<mylist<T1>>(std::move(_value)))
                  : _root.emplace(std::move(_value)));
          break;
        } else {
          const auto &[a0, a1] = std::get<typename mylist<A>::Mycons>(_sv.v());
          auto _cell = typename mylist<T1>::Mycons(f(a0), nullptr);
          mylist<T1> &_node =
              (_write
                   ? *(*_write = std::make_shared<mylist<T1>>(std::move(_cell)))
                   : _root.emplace(std::move(_cell)));
          _write = &std::get<typename mylist<T1>::Mycons>(_node.v_mut()).a1;
          _loop_self = crane_raw(a1);
          continue;
        }
      }
      return std::move(*_root);
    }

    mylist<A> myapp(mylist<A> l2) const {
      std::optional<mylist<A>> _root{};
      std::shared_ptr<mylist<A>> *_write = nullptr;
      const mylist<A> *_loop_self = this;
      mylist<A> _loop_l2 = std::move(l2);
      while (true) {
        auto &&_sv = *_loop_self;
        if (std::holds_alternative<typename mylist<A>::Mynil>(_sv.v())) {
          auto _value = std::move(_loop_l2);
          (_write ? *(*_write = std::make_shared<mylist<A>>(std::move(_value)))
                  : _root.emplace(std::move(_value)));
          break;
        } else {
          const auto &[a0, a1] = std::get<typename mylist<A>::Mycons>(_sv.v());
          auto _cell = typename mylist<A>::Mycons(a0, nullptr);
          mylist<A> &_node =
              (_write
                   ? *(*_write = std::make_shared<mylist<A>>(std::move(_cell)))
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

      /// CraneEnter: captures varying parameters for each recursive call.
      struct CraneEnter {
        const mylist<A> *_self;
      };

      /// CraneCont_Mycons: saves [a0, a1], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_Mycons {
        A a0;
        std::shared_ptr<mylist<A>> a1;
      };

      using CraneFrame = std::variant<CraneEnter, CraneCont_Mycons>;
      T1 _result{};
      crane::small_vector<CraneFrame> _stack;
      _stack.emplace_back(CraneEnter{_self});
      /// Loopified mylist_rect: CraneEnter -> CraneCont_Mycons.
      while (!_stack.empty()) {
        CraneFrame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<CraneEnter>(_frame)) {
          auto _f = std::move(std::get<CraneEnter>(_frame));
          const mylist<A> *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename mylist<A>::Mynil>(_sv.v())) {
            _result = f;
          } else {
            const auto &[a0, a1] =
                std::get<typename mylist<A>::Mycons>(_sv.v());
            _stack.emplace_back(CraneCont_Mycons{a0, a1});
            _stack.emplace_back(CraneEnter{crane_raw(a1)});
          }
        } else {
          auto _f = std::move(std::get<CraneCont_Mycons>(_frame));
          auto a0 = std::move(_f.a0);
          std::shared_ptr<mylist<A>> a1 = std::move(_f.a1);
          _result = f0(a0, *a1, std::move(_result));
        }
      }
      return _result;
    }
  };

  static uint64_t sum_list(const mylist<uint64_t> &l);
  static inline const uint64_t test_dup = []() {
    tree t = tree::node(tree::leaf(), UINT64_C(42), tree::leaf());
    return std::move(t).dup_tree().tree_sum();
  }();
  static inline const uint64_t test_let_reuse =
      tree::node(tree::node(tree::leaf(), UINT64_C(5), tree::leaf()),
                 UINT64_C(10),
                 tree::node(tree::leaf(), UINT64_C(15), tree::leaf()))
          .let_reuse();

  /// TEST 3: Apply a higher-order function multiple times
  /// to a closure that captures a tree.
  template <typename F0>
    requires std::is_invocable_r_v<uint64_t, F0 &, uint64_t> &&
             std::is_invocable_r_v<uint64_t, F0 &, uint64_t &>
  static uint64_t apply_twice(F0 &&f, uint64_t x) {
    return f(f(x));
  }

  static inline const uint64_t test_apply_twice = []() {
    return []() {
      tree t = tree::node(tree::leaf(), UINT64_C(7), tree::leaf());
      crane::fn<uint64_t(uint64_t)> f = [=](uint64_t n) {
        return (t.tree_sum() + n);
      };
      return apply_twice(f, UINT64_C(0));
    }();
  }();
  static inline const uint64_t test_tree_from_tree = []() {
    tree t = tree::node(tree::leaf(), UINT64_C(5), tree::leaf());
    return std::move(t).tree_from_tree().tree_sum();
  }();
  /// TEST 5: Complex fold that builds a tree from a list.
  static tree fold_left_tree(const mylist<uint64_t> &l, tree acc);
  static inline const uint64_t test_fold_tree = []() {
    mylist<uint64_t> l = mylist<uint64_t>::mycons(
        UINT64_C(1),
        mylist<uint64_t>::mycons(
            UINT64_C(2),
            mylist<uint64_t>::mycons(UINT64_C(3), mylist<uint64_t>::mynil())));
    return fold_left_tree(std::move(l), tree::leaf()).tree_sum();
  }();

  /// TEST 6: Concat two lists, using both in the result.
  template <typename T1>
  static mylist<T1> concat_flat(
      const mylist<mylist<T1>> &ls) { /// CraneEnter: captures varying
                                      /// parameters for each recursive call.

    struct CraneEnter {
      const mylist<mylist<T1>> *ls;
    };

    /// CraneCont_Mycons: saves [a0], resumes after recursive call, then
    /// processes rest.
    struct CraneCont_Mycons {
      mylist<T1> a0;
    };

    using CraneFrame = std::variant<CraneEnter, CraneCont_Mycons>;
    mylist<T1> _result{};
    crane::small_vector<CraneFrame> _stack;
    _stack.emplace_back(CraneEnter{&ls});
    /// Loopified concat_flat: CraneEnter -> CraneCont_Mycons.
    while (!_stack.empty()) {
      CraneFrame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<CraneEnter>(_frame)) {
        auto _f = std::move(std::get<CraneEnter>(_frame));
        const mylist<mylist<T1>> &ls = *_f.ls;
        if (std::holds_alternative<typename mylist<mylist<T1>>::Mynil>(
                ls.v())) {
          _result = mylist<T1>::mynil();
        } else {
          const auto &[a0, a1] =
              std::get<typename mylist<mylist<T1>>::Mycons>(ls.v());
          _stack.emplace_back(CraneCont_Mycons{a0});
          _stack.emplace_back(CraneEnter{crane_raw(a1)});
        }
      } else {
        auto _f = std::move(std::get<CraneCont_Mycons>(_frame));
        mylist<T1> a0 = std::move(_f.a0);
        _result = a0.myapp(std::move(_result));
      }
    }
    return _result;
  }

  static inline const uint64_t test_concat = []() {
    mylist<uint64_t> l1 = mylist<uint64_t>::mycons(
        UINT64_C(1),
        mylist<uint64_t>::mycons(UINT64_C(2), mylist<uint64_t>::mynil()));
    mylist<uint64_t> l2 = mylist<uint64_t>::mycons(
        UINT64_C(3),
        mylist<uint64_t>::mycons(UINT64_C(4), mylist<uint64_t>::mynil()));
    mylist<uint64_t> l3 = mylist<uint64_t>::mycons(
        UINT64_C(5),
        mylist<uint64_t>::mycons(UINT64_C(6), mylist<uint64_t>::mynil()));
    mylist<mylist<uint64_t>> ls = mylist<mylist<uint64_t>>::mycons(
        std::move(l1),
        mylist<mylist<uint64_t>>::mycons(
            std::move(l2),
            mylist<mylist<uint64_t>>::mycons(
                std::move(l3), mylist<mylist<uint64_t>>::mynil())));
    return sum_list(concat_flat<uint64_t>(std::move(ls)));
  }();
  static inline const uint64_t test_chain = []() {
    tree t = tree::node(tree::leaf(), UINT64_C(10), tree::leaf());
    return std::move(t).chain_transforms();
  }();
  /// TEST 8: Nested constructor building: build a list of trees
  /// using the same tree in different positions.
  static mylist<tree> build_tree_list(const tree &t, uint64_t n);
  static uint64_t sum_tree_list(const mylist<tree> &l);
  static inline const uint64_t test_build_tree_list = []() {
    tree t = tree::node(tree::leaf(), UINT64_C(10), tree::leaf());
    mylist<tree> trees = build_tree_list(std::move(t), UINT64_C(3));
    return sum_tree_list(std::move(trees));
  }();
  static inline const uint64_t test_triple_use =
      tree::node(tree::leaf(), UINT64_C(7), tree::leaf()).triple_use();
};

#endif // INCLUDED_MEM_SAFETY_PROBE18
