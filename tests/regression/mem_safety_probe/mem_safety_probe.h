#ifndef INCLUDED_MEM_SAFETY_PROBE
#define INCLUDED_MEM_SAFETY_PROBE

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

struct MemSafetyProbe {
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

    /// ---- TEST 11: Closure captures two different tree values ----
    /// A function that creates a closure capturing TWO different trees.
    /// Both must be correctly cloned or captured by value.
    uint64_t combine_trees(const tree &t2, uint64_t x) const {
      return (this->sum_values(x) + t2.sum_values(x));
    }

    /// ---- TEST 9: Map tree with closure ----
    /// Recursive function that passes a closure through recursive calls.
    /// The closure must remain valid across all recursive invocations.
    template <typename F0>
      requires std::is_invocable_r_v<uint64_t, F0 &, uint64_t &>
    tree map_tree(F0 &&f) const {
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
        tree _tmp2;
        uint64_t a1;
      };

      using CraneFrame =
          std::variant<CraneEnter, CraneCont_Node, CraneCont_Node_1>;
      tree _result{};
      crane::small_vector<CraneFrame> _stack;
      _stack.emplace_back(CraneEnter{_self});
      /// Loopified map_tree: CraneEnter -> CraneCont_Node -> CraneCont_Node_1.
      while (!_stack.empty()) {
        CraneFrame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<CraneEnter>(_frame)) {
          auto _f = std::move(std::get<CraneEnter>(_frame));
          const tree *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename tree::Leaf>(_sv.v())) {
            _result = tree::leaf();
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
          _result = tree::node(std::move(_f._tmp2), f(a1), std::move(_result));
        }
      }
      return _result;
    }

    /// ---- TEST 3: Closure in pair construction ----
    /// Tests whether pair/tuple construction with closures handles
    /// capture correctly.
    std::pair<crane::fn<uint64_t(uint64_t)>, crane::fn<uint64_t(uint64_t)>>
    pair_of_closures() const {
      tree _self_val = *this;
      return std::make_pair(
          [=, _self_val = std::move(_self_val)](uint64_t _x0) -> uint64_t {
            return std::move(_self_val).sum_values(_x0);
          },
          [](uint64_t n) { return n; });
    }

    /// Sum all values in a tree, plus an accumulator.
    uint64_t sum_values(uint64_t x) const {
      if (std::holds_alternative<typename tree::Leaf>(this->v())) {
        return x;
      } else {
        const auto &[a0, a1, a2] = std::get<typename tree::Node>(this->v());
        auto &&_sv0 = *a0;
        if (std::holds_alternative<typename tree::Leaf>(_sv0.v())) {
          return (a1 + x);
        } else {
          const auto &[a00, a10, a20] = std::get<typename tree::Node>(_sv0.v());
          auto &&_sv1 = *a2;
          if (std::holds_alternative<typename tree::Leaf>(_sv1.v())) {
            return (a10 + x);
          } else {
            const auto &[a01, a11, a21] =
                std::get<typename tree::Node>(_sv1.v());
            return (((a10 + a11) + a1) + x);
          }
        }
      }
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

  /// A wrapper for closures.
  struct fn_box {
    // DATA
    crane::fn<uint64_t(uint64_t)> a0;

    // ACCESSORS
    fn_box clone() const { return {a0}; }

    // CREATORS
    static fn_box box(crane::fn<uint64_t(uint64_t)> a0) {
      return {std::move(a0)};
    }

    uint64_t apply_box(uint64_t x) const {
      const auto &[a0] = *this;
      return a0(x);
    }

    template <typename T1, typename F0> T1 fn_box_rec(F0 &&f) const {
      return this->template fn_box_rect<T1>(f);
    }

    template <typename T1, typename F0>
      requires std::is_invocable_r_v<T1, F0 &,
                                     const crane::fn<uint64_t(uint64_t)> &>
    T1 fn_box_rect(F0 &&f) const {
      const auto &[a0] = *this;
      return f(a0);
    }
  };

  /// Custom list type.
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

  /// ---- TEST 1: Higher-order function calling closure multiple times ----
  /// If f is a partial application with & capture and apply_twice calls
  /// it twice, the second call would use a moved-from value.
  template <typename F0>
    requires std::is_invocable_r_v<uint64_t, F0 &, uint64_t> &&
             std::is_invocable_r_v<uint64_t, F0 &, uint64_t &>
  static uint64_t apply_twice(F0 &&f, uint64_t x) {
    return f(f(x));
  }

  static inline const uint64_t test_hof_double = []() {
    return []() {
      tree t = tree::node(tree::node(tree::leaf(), UINT64_C(10), tree::leaf()),
                          UINT64_C(20),
                          tree::node(tree::leaf(), UINT64_C(30), tree::leaf()));
      crane::fn<uint64_t(uint64_t)> f = [=](uint64_t _x0) -> uint64_t {
        return std::move(t).sum_values(_x0);
      };
      return apply_twice(f, UINT64_C(0));
    }();
  }();
  /// ---- TEST 2: Build list of closures from tree branches ----
  /// Each closure captures a tree value via partial application.
  /// The closures must survive after the function returns.
  static mylist<crane::fn<uint64_t(uint64_t)>>
  build_adders(const mylist<tree> &trees);
  static uint64_t apply_all(const mylist<crane::fn<uint64_t(uint64_t)>> &fns,
                            uint64_t x);
  static inline const uint64_t test_closure_list = []() {
    tree t1 = tree::node(tree::leaf(), UINT64_C(10), tree::leaf());
    tree t2 = tree::node(tree::leaf(), UINT64_C(20), tree::leaf());
    tree t3 = tree::node(tree::leaf(), UINT64_C(30), tree::leaf());
    mylist<crane::fn<uint64_t(uint64_t)>> fns =
        build_adders(mylist<tree>::mycons(
            std::move(t1),
            mylist<tree>::mycons(
                std::move(t2),
                mylist<tree>::mycons(std::move(t3), mylist<tree>::mynil()))));
    return apply_all(std::move(fns), UINT64_C(5));
  }();
  static inline const uint64_t test_pair_closures = []() {
    tree t = tree::node(tree::leaf(), UINT64_C(42), tree::leaf());
    std::pair<crane::fn<uint64_t(uint64_t)>, crane::fn<uint64_t(uint64_t)>> p =
        std::move(t).pair_of_closures();
    return (p.first(UINT64_C(10)) + p.second(UINT64_C(100)));
  }();

  /// ---- TEST 4: Fold composing closures ----
  /// Each iteration wraps the accumulator in a new closure that captures
  /// a tree value. Tests deep closure chaining with value type captures.
  static uint64_t fold_compose(const mylist<tree> &trees,
                               const crane::fn<uint64_t(uint64_t)> &acc,
                               uint64_t x0_) {
    crane::fn<uint64_t(uint64_t)> _loop_acc = acc;
    mylist<tree> _loop_trees = trees;
    while (true) {
      if (std::holds_alternative<typename mylist<tree>::Mynil>(
              _loop_trees.v())) {
        return _loop_acc(x0_);
      } else {
        const auto &[a0, a1] =
            std::get<typename mylist<tree>::Mycons>(_loop_trees.v());
        const mylist<tree> &a1_value = *a1;
        _loop_acc = [=](uint64_t n) { return _loop_acc(a0.sum_values(n)); };
        _loop_trees = a1_value;
      }
    }
  }

  static inline const uint64_t test_fold_compose = []() {
    tree t1 = tree::node(tree::leaf(), UINT64_C(10), tree::leaf());
    tree t2 = tree::node(tree::leaf(), UINT64_C(20), tree::leaf());
    return fold_compose(
        mylist<tree>::mycons(
            std::move(t1),
            mylist<tree>::mycons(std::move(t2), mylist<tree>::mynil())),
        [](uint64_t n) { return n; }, UINT64_C(5));
  }();
  /// ---- TEST 5: Partial application + match scrutinee reuse ----
  /// f captures t by partial application, then t is used as a match
  /// scrutinee. The escape analysis must handle this correctly.
  static uint64_t match_partial(tree t);
  static inline const uint64_t test_match_partial = match_partial(tree::node(
      tree::node(tree::leaf(), UINT64_C(10), tree::leaf()), UINT64_C(20),
      tree::node(tree::leaf(), UINT64_C(30), tree::leaf())));
  /// ---- TEST 6: Deep currying chain ----
  /// Multi-level partial application where each level binds a new value.
  static uint64_t add3(uint64_t a, uint64_t b, uint64_t c);
  static inline const uint64_t test_deep_curry = []() {
    tree t = tree::node(tree::leaf(), UINT64_C(10), tree::leaf());
    uint64_t v = std::move(t).sum_values(UINT64_C(0));
    return add3(v, UINT64_C(20), UINT64_C(30));
  }();
  /// ---- TEST 7: Store partial application in Box, then apply twice ----
  /// The Box stores a closure. If the closure uses & capture,
  /// the Box holds dangling references after make_box returns.
  static fn_box make_box(tree t);
  static inline const uint64_t test_box_apply_twice = []() {
    tree t = tree::node(tree::node(tree::leaf(), UINT64_C(10), tree::leaf()),
                        UINT64_C(20),
                        tree::node(tree::leaf(), UINT64_C(30), tree::leaf()));
    fn_box b = make_box(std::move(t));
    return (b.apply_box(UINT64_C(0)) + b.apply_box(UINT64_C(99)));
  }();
  /// ---- TEST 8: Two closures capture the same tree ----
  /// Both must independently own data. The second partial application
  /// should not move the tree.
  static inline const uint64_t test_dual_capture = []() {
    return []() {
      tree t = tree::node(tree::leaf(), UINT64_C(42), tree::leaf());
      crane::fn<uint64_t(uint64_t)> f = [=](uint64_t _x0) -> uint64_t {
        return t.sum_values(_x0);
      };
      crane::fn<uint64_t(uint64_t)> g = [&](uint64_t _x0) -> uint64_t {
        return std::move(t).sum_values(_x0);
      };
      return (f(UINT64_C(1)) + g(UINT64_C(2)));
    }();
  }();
  static inline const uint64_t test_map_tree = []() {
    tree t = tree::node(tree::node(tree::leaf(), UINT64_C(10), tree::leaf()),
                        UINT64_C(20),
                        tree::node(tree::leaf(), UINT64_C(30), tree::leaf()));
    tree t2 =
        std::move(t).map_tree([](uint64_t n) { return (n + UINT64_C(1)); });
    return std::move(t2).sum_values(UINT64_C(0));
  }();
  /// ---- TEST 10: Partial application stored in Box via match ----
  /// The partial application captures a match-bound tree value and
  /// is stored in a Box. Tests closure escape through constructor inside match.
  static fn_box box_from_match(const tree &t);
  static inline const uint64_t test_box_from_match = []() {
    tree t = tree::node(tree::node(tree::leaf(), UINT64_C(10), tree::leaf()),
                        UINT64_C(20),
                        tree::node(tree::leaf(), UINT64_C(30), tree::leaf()));
    fn_box b = box_from_match(std::move(t));
    return std::move(b).apply_box(UINT64_C(5));
  }();
  static inline const uint64_t test_combine = []() {
    tree t1 = tree::node(tree::leaf(), UINT64_C(10), tree::leaf());
    tree t2 = tree::node(tree::leaf(), UINT64_C(20), tree::leaf());
    return std::move(t1).combine_trees(std::move(t2), UINT64_C(5));
  }();
  /// ---- TEST 12: Chain of partial applications with intermediate let ----
  /// f captures t, then g uses f's result to build another closure.
  /// Tests that intermediate values are properly kept alive.
  static inline const uint64_t test_chain_partial = []() {
    return []() {
      tree t = tree::node(tree::node(tree::leaf(), UINT64_C(10), tree::leaf()),
                          UINT64_C(20),
                          tree::node(tree::leaf(), UINT64_C(30), tree::leaf()));
      crane::fn<uint64_t(uint64_t)> f = [&](uint64_t _x0) -> uint64_t {
        return std::move(t).sum_values(_x0);
      };
      uint64_t v = f(UINT64_C(0));
      return add3(v, UINT64_C(100), UINT64_C(200));
    }();
  }();
};

#endif // INCLUDED_MEM_SAFETY_PROBE
