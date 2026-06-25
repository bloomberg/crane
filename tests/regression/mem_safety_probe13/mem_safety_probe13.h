#ifndef INCLUDED_MEM_SAFETY_PROBE13
#define INCLUDED_MEM_SAFETY_PROBE13

#include <any>
#include <functional>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

struct MemSafetyProbe13 {
  /// Probe 13: Value-type move semantics and the flatten optimization.
  ///
  /// The flatten optimization (make_owned_param_matches +
  /// optimize_frame_push_args) marks match branches as owned and
  /// moves unique_ptr child fields into Enter frames. If a closure
  /// or continuation simultaneously references the same field,
  /// the move creates use-after-move.
  ///
  /// Also tests: closures returned from functions that take
  /// value-type parameters, and deep pattern match nesting
  /// with closures at each level.
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
      std::vector<std::shared_ptr<tree>> _stack = {};
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
          _drain(_cur->v_mut());
        }
      }
    }

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    /// TEST 3: Function that matches twice on same tree.
    /// First match extracts subtrees, second match on a subtree
    /// creates a closure capturing the other subtree.
    uint64_t double_match() const {
      if (std::holds_alternative<typename tree::Leaf>(this->v())) {
        return UINT64_C(0);
      } else {
        const auto &[a0, a1, a2] = std::get<typename tree::Node>(this->v());
        const tree &a0_value = *a0;
        const tree &a2_value = *a2;
        if (std::holds_alternative<typename tree::Leaf>(a0_value.v())) {
          return (a2_value.tree_sum() + a1);
        } else {
          const auto &[a00, a10, a20] =
              std::get<typename tree::Node>(a0_value.v());
          const tree &a00_value = *a00;
          const tree &a20_value = *a20;
          std::function<uint64_t(uint64_t)> f = [=](uint64_t n) mutable {
            return ((a2_value.tree_sum() + a20_value.tree_sum()) + n);
          };
          return (f(a10) + a00_value.tree_sum());
        }
      }
    }

    uint64_t tree_sum() const {
      if (std::holds_alternative<typename tree::Leaf>(this->v())) {
        return UINT64_C(0);
      } else {
        const auto &[a0, a1, a2] = std::get<typename tree::Node>(this->v());
        return ((a0->tree_sum() + a1) + a2->tree_sum());
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
    ~mylist() {
      std::vector<std::shared_ptr<mylist<A>>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<Mycons>(&_v)) {
          if (_alt->a1) {
            _stack.push_back(std::move(_alt->a1));
          }
        }
      };
      _drain(v_mut());
      while (!_stack.empty()) {
        auto _cur = std::move(_stack.back());
        _stack.pop_back();
        if (_cur.use_count() == 1) {
          _drain(_cur->v_mut());
        }
      }
    }

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    mylist<A> app(mylist<A> l2) const {
      if (std::holds_alternative<typename mylist<A>::Mynil>(this->v())) {
        return l2;
      } else {
        const auto &[a0, a1] = std::get<typename mylist<A>::Mycons>(this->v());
        return mylist<A>::mycons(a0, a1->app(std::move(l2)));
      }
    }

    template <typename T1, typename F0>
      requires std::is_invocable_r_v<T1, F0 &, A &>
    mylist<T1> map_list(F0 &&f) const {
      if (std::holds_alternative<typename mylist<A>::Mynil>(this->v())) {
        return mylist<T1>::mynil();
      } else {
        const auto &[a0, a1] = std::get<typename mylist<A>::Mycons>(this->v());
        return mylist<T1>::mycons(f(a0), a1->template map_list<T1>(f));
      }
    }

    uint64_t length() const {
      if (std::holds_alternative<typename mylist<A>::Mynil>(this->v())) {
        return UINT64_C(0);
      } else {
        const auto &[a0, a1] = std::get<typename mylist<A>::Mycons>(this->v());
        return (UINT64_C(1) + a1->length());
      }
    }

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

  static uint64_t sum_list(const mylist<uint64_t> &l);
  /// TEST 1: Double-recursion on tree where both subtrees
  /// are used in closures AND in recursive calls.
  /// Tests if the flatten optimization moves unique_ptr fields
  /// that are also captured by closures.
  static std::pair<mylist<uint64_t>, mylist<std::function<uint64_t(uint64_t)>>>
  tree_vals_and_fns(const tree &t);
  static inline const uint64_t test_vals_and_fns = []() {
    tree t = tree::node(tree::node(tree::leaf(), UINT64_C(3), tree::leaf()),
                        UINT64_C(7),
                        tree::node(tree::leaf(), UINT64_C(11), tree::leaf()));
    auto [vals, fns] = tree_vals_and_fns(std::move(t));
    uint64_t val_sum = sum_list(std::move(vals));
    uint64_t fn_sum = sum_list(std::move(fns).template map_list<uint64_t>(
        [](std::function<uint64_t(uint64_t)> f) { return f(UINT64_C(0)); }));
    return (val_sum + fn_sum);
  }();
  static inline const uint64_t test_double_match = []() {
    tree t = tree::node(
        tree::node(tree::node(tree::leaf(), UINT64_C(1), tree::leaf()),
                   UINT64_C(2),
                   tree::node(tree::leaf(), UINT64_C(3), tree::leaf())),
        UINT64_C(10), tree::node(tree::leaf(), UINT64_C(20), tree::leaf()));
    return std::move(t).double_match();
  }();
  /// TEST 4: Deeply nested tree with closures at EVERY level.
  /// Each closure captures values from its level AND from the parent.
  /// Tests stack depth and closure lifetime with deep nesting.
  static tree make_deep(uint64_t n);
  static mylist<std::function<uint64_t(uint64_t)>>
  depth_fns(const tree &t, uint64_t parent_val);
  static inline const uint64_t test_depth_fns = []() {
    tree t = make_deep(UINT64_C(5));
    mylist<std::function<uint64_t(uint64_t)>> fns =
        depth_fns(std::move(t), UINT64_C(0));
    return sum_list(std::move(fns).template map_list<uint64_t>(
        [](std::function<uint64_t(uint64_t)> f) { return f(UINT64_C(0)); }));
  }();

  /// TEST 5: Transform a tree by replacing each value with a
  /// function, then evaluate. Tests closures in recursive
  /// tree transformation.
  struct ftree {
    // TYPES
    struct FLeaf {};

    struct FNode {
      std::shared_ptr<ftree> a0;
      std::function<uint64_t(uint64_t)> a1;
      std::shared_ptr<ftree> a2;
    };

    using variant_t = std::variant<FLeaf, FNode>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    ftree() {}

    explicit ftree(FLeaf _v) : v_(_v) {}

    explicit ftree(FNode _v) : v_(std::move(_v)) {}

    static ftree fleaf() { return ftree(FLeaf{}); }

    static ftree fnode(ftree a0, std::function<uint64_t(uint64_t)> a1,
                       ftree a2) {
      return ftree(FNode{std::make_shared<ftree>(std::move(a0)), std::move(a1),
                         std::make_shared<ftree>(std::move(a2))});
    }

    // MANIPULATORS
    ~ftree() {
      std::vector<std::shared_ptr<ftree>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<FNode>(&_v)) {
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
          _drain(_cur->v_mut());
        }
      }
    }

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    uint64_t eval_ftree(uint64_t base) const {
      if (std::holds_alternative<typename ftree::FLeaf>(this->v())) {
        return UINT64_C(0);
      } else {
        const auto &[a0, a1, a2] = std::get<typename ftree::FNode>(this->v());
        return ((a0->eval_ftree(base) + a1(base)) + a2->eval_ftree(base));
      }
    }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, ftree &, T1 &,
                                     std::function<uint64_t(uint64_t)> &,
                                     ftree &, T1 &>
    T1 ftree_rec(T1 f, F1 &&f0) const {
      if (std::holds_alternative<typename ftree::FLeaf>(this->v())) {
        return f;
      } else {
        const auto &[a0, a1, a2] = std::get<typename ftree::FNode>(this->v());
        return f0(*a0, a0->template ftree_rec<T1>(f, f0), a1, *a2,
                  a2->template ftree_rec<T1>(f, f0));
      }
    }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, ftree &, T1 &,
                                     std::function<uint64_t(uint64_t)> &,
                                     ftree &, T1 &>
    T1 ftree_rect(T1 f, F1 &&f0) const {
      if (std::holds_alternative<typename ftree::FLeaf>(this->v())) {
        return f;
      } else {
        const auto &[a0, a1, a2] = std::get<typename ftree::FNode>(this->v());
        return f0(*a0, a0->template ftree_rect<T1>(f, f0), a1, *a2,
                  a2->template ftree_rect<T1>(f, f0));
      }
    }
  };

  static ftree tree_to_ftree(const tree &t);
  static inline const uint64_t test_ftree = []() {
    tree t = tree::node(tree::node(tree::leaf(), UINT64_C(3), tree::leaf()),
                        UINT64_C(7),
                        tree::node(tree::leaf(), UINT64_C(11), tree::leaf()));
    ftree ft = tree_to_ftree(std::move(t));
    return std::move(ft).eval_ftree(UINT64_C(100));
  }();
  /// TEST 6: Flatten a tree of lists into a single list,
  /// where each list element is a closure.
  static mylist<std::function<uint64_t(uint64_t)>>
  flatten_tree_fns(const tree &t);
  static inline const uint64_t test_flatten_fns = []() {
    tree t = tree::node(tree::node(tree::leaf(), UINT64_C(3), tree::leaf()),
                        UINT64_C(7),
                        tree::node(tree::leaf(), UINT64_C(11), tree::leaf()));
    mylist<std::function<uint64_t(uint64_t)>> fns =
        flatten_tree_fns(std::move(t));
    return sum_list(std::move(fns).template map_list<uint64_t>(
        [](std::function<uint64_t(uint64_t)> f) { return f(UINT64_C(1)); }));
  }();
};

#endif // INCLUDED_MEM_SAFETY_PROBE13
