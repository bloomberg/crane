#ifndef INCLUDED_MEM_SAFETY_PROBE
#define INCLUDED_MEM_SAFETY_PROBE

#include <any>
#include <functional>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

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
      if (std::holds_alternative<typename tree::Leaf>(this->v())) {
        return tree::leaf();
      } else {
        const auto &[a0, a1, a2] = std::get<typename tree::Node>(this->v());
        return tree::node(a0->map_tree(f), f(a1), a2->map_tree(f));
      }
    }

    /// ---- TEST 3: Closure in pair construction ----
    /// Tests whether pair/tuple construction with closures handles
    /// capture correctly.
    std::pair<std::function<uint64_t(uint64_t)>,
              std::function<uint64_t(uint64_t)>>
    pair_of_closures() const {
      tree _self_val = *this;
      return std::make_pair(
          [=](uint64_t _x0) mutable -> uint64_t {
            return _self_val.sum_values(_x0);
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

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, tree &, T1 &, uint64_t &, tree &,
                                     T1 &>
    T1 tree_rec(T1 f, F1 &&f0) const {
      if (std::holds_alternative<typename tree::Leaf>(this->v())) {
        return f;
      } else {
        const auto &[a0, a1, a2] = std::get<typename tree::Node>(this->v());
        return f0(*a0, a0->template tree_rec<T1>(f, f0), a1, *a2,
                  a2->template tree_rec<T1>(f, f0));
      }
    }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, tree &, T1 &, uint64_t &, tree &,
                                     T1 &>
    T1 tree_rect(T1 f, F1 &&f0) const {
      if (std::holds_alternative<typename tree::Leaf>(this->v())) {
        return f;
      } else {
        const auto &[a0, a1, a2] = std::get<typename tree::Node>(this->v());
        return f0(*a0, a0->template tree_rect<T1>(f, f0), a1, *a2,
                  a2->template tree_rect<T1>(f, f0));
      }
    }
  };

  /// A wrapper for closures.
  struct fn_box {
    // DATA
    std::function<uint64_t(uint64_t)> a0;

    // ACCESSORS
    fn_box clone() const { return {a0}; }

    // CREATORS
    static fn_box box(std::function<uint64_t(uint64_t)> a0) {
      return {std::move(a0)};
    }

    uint64_t apply_box(uint64_t x) const {
      const auto &[a0] = *this;
      return a0(x);
    }

    template <typename T1, typename F0>
      requires std::is_invocable_r_v<T1, F0 &,
                                     std::function<uint64_t(uint64_t)> &>
    T1 fn_box_rec(F0 &&f) const {
      const auto &[a0] = *this;
      return f(a0);
    }

    template <typename T1, typename F0>
      requires std::is_invocable_r_v<T1, F0 &,
                                     std::function<uint64_t(uint64_t)> &>
    T1 fn_box_rect(F0 &&f) const {
      const auto &[a0] = *this;
      return f(a0);
    }
  }; /// Custom list type.

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

    template <typename _U> explicit mylist(const mylist<_U> &_other) {
      if (std::holds_alternative<typename mylist<_U>::Mynil>(_other.v())) {
        this->v_ = Mynil{};
      } else {
        const auto &[a0, a1] =
            std::get<typename mylist<_U>::Mycons>(_other.v());
        this->v_ = Mycons{
            [&]() -> A {
              if constexpr (std::is_same_v<_U, std::any>) {
                if (a0.type() == typeid(A))
                  return std::any_cast<A>(a0);
                if constexpr (requires {
                                typename A::first_type;
                                typename A::second_type;
                              }) {
                  const auto &[_k, _v] =
                      std::any_cast<std::pair<std::any, std::any>>(a0);
                  return A{
                      [&]() -> typename A::first_type {
                        if constexpr (std::is_same_v<typename A::first_type,
                                                     std::any>)
                          return _k;
                        else
                          return std::any_cast<typename A::first_type>(_k);
                      }(),
                      [&]() -> typename A::second_type {
                        if constexpr (std::is_same_v<typename A::second_type,
                                                     std::any>)
                          return _v;
                        else
                          return std::any_cast<typename A::second_type>(_v);
                      }()};
                }
                return std::any_cast<A>(a0);
              } else
                return A(a0);
            }(),
            a1 ? std::make_shared<mylist<A>>(*a1) : nullptr};
      }
    }

    static mylist<A> mynil() { return mylist(Mynil{}); }

    static mylist<A> mycons(A a0, mylist<A> a1) {
      return mylist(
          Mycons{std::move(a0), std::make_shared<mylist<A>>(std::move(a1))});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, A &, mylist<A> &, T1 &>
    T1 mylist_rec(T1 f, F1 &&f0) const {
      if (std::holds_alternative<typename mylist<A>::Mynil>(this->v())) {
        return f;
      } else {
        const auto &[a0, a1] = std::get<typename mylist<A>::Mycons>(this->v());
        return f0(a0, *a1, a1->template mylist_rec<T1>(f, f0));
      }
    }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, A &, mylist<A> &, T1 &>
    T1 mylist_rect(T1 f, F1 &&f0) const {
      if (std::holds_alternative<typename mylist<A>::Mynil>(this->v())) {
        return f;
      } else {
        const auto &[a0, a1] = std::get<typename mylist<A>::Mycons>(this->v());
        return f0(a0, *a1, a1->template mylist_rect<T1>(f, f0));
      }
    }
  };

  /// ---- TEST 1: Higher-order function calling closure multiple times ----
  /// If f is a partial application with & capture and apply_twice calls
  /// it twice, the second call would use a moved-from value.
  template <typename F0>
    requires std::is_invocable_r_v<uint64_t, F0 &, uint64_t &>
  static uint64_t apply_twice(F0 &&f, uint64_t x) {
    return f(f(x));
  }

  static inline const uint64_t test_hof_double = []() {
    return []() {
      tree t = tree::node(tree::node(tree::leaf(), UINT64_C(10), tree::leaf()),
                          UINT64_C(20),
                          tree::node(tree::leaf(), UINT64_C(30), tree::leaf()));
      std::function<uint64_t(uint64_t)> f =
          [=](uint64_t _x0) mutable -> uint64_t { return t.sum_values(_x0); };
      return apply_twice(f, UINT64_C(0));
    }();
  }();
  /// ---- TEST 2: Build list of closures from tree branches ----
  /// Each closure captures a tree value via partial application.
  /// The closures must survive after the function returns.
  static mylist<std::function<uint64_t(uint64_t)>>
  build_adders(const mylist<tree> &trees);
  static uint64_t
  apply_all(const mylist<std::function<uint64_t(uint64_t)>> &fns, uint64_t x);
  static inline const uint64_t test_closure_list = []() {
    tree t1 = tree::node(tree::leaf(), UINT64_C(10), tree::leaf());
    tree t2 = tree::node(tree::leaf(), UINT64_C(20), tree::leaf());
    tree t3 = tree::node(tree::leaf(), UINT64_C(30), tree::leaf());
    mylist<std::function<uint64_t(uint64_t)>> fns =
        build_adders(mylist<tree>::mycons(
            std::move(t1),
            mylist<tree>::mycons(
                std::move(t2),
                mylist<tree>::mycons(std::move(t3), mylist<tree>::mynil()))));
    return apply_all(std::move(fns), UINT64_C(5));
  }();
  static inline const uint64_t test_pair_closures = []() {
    tree t = tree::node(tree::leaf(), UINT64_C(42), tree::leaf());
    std::pair<std::function<uint64_t(uint64_t)>,
              std::function<uint64_t(uint64_t)>>
        p = std::move(t).pair_of_closures();
    return (p.first(UINT64_C(10)) + p.second(UINT64_C(100)));
  }();

  /// ---- TEST 4: Fold composing closures ----
  /// Each iteration wraps the accumulator in a new closure that captures
  /// a tree value. Tests deep closure chaining with value type captures.
  static uint64_t
  fold_compose(const mylist<tree> &trees, std::function<uint64_t(uint64_t)> acc,
               uint64_t _x0) { /// _Enter: captures varying parameters for each
                               /// recursive call.

    struct _Enter {
      std::function<uint64_t(uint64_t)> acc;
      mylist<tree> trees;
    };

    using _Frame = std::variant<_Enter>;
    uint64_t _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{std::move(acc), trees});
    /// Loopified fold_compose: _Enter.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      auto _f = std::move(std::get<_Enter>(_frame));
      std::function<uint64_t(uint64_t)> acc = std::move(_f.acc);
      const mylist<tree> &trees = _f.trees;
      _result = [=]() mutable -> std::function<uint64_t(uint64_t)> {
        if (std::holds_alternative<typename mylist<tree>::Mynil>(trees.v())) {
          return acc;
        } else {
          const auto &[a0, a1] =
              std::get<typename mylist<tree>::Mycons>(trees.v());
          const mylist<tree> &a1_value = *a1;
          return [=](uint64_t _x0) mutable -> uint64_t {
            return fold_compose(
                a1_value,
                [=](uint64_t n) mutable { return acc(a0.sum_values(n)); }, _x0);
          };
        }
      }()(_x0);
    }
    return _result;
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
      std::function<uint64_t(uint64_t)> f =
          [=](uint64_t _x0) mutable -> uint64_t { return t.sum_values(_x0); };
      std::function<uint64_t(uint64_t)> g = [&](uint64_t _x0) -> uint64_t {
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
      std::function<uint64_t(uint64_t)> f = [&](uint64_t _x0) -> uint64_t {
        return std::move(t).sum_values(_x0);
      };
      uint64_t v = f(UINT64_C(0));
      return add3(v, UINT64_C(100), UINT64_C(200));
    }();
  }();
};

#endif // INCLUDED_MEM_SAFETY_PROBE
