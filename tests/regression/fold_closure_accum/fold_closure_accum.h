#ifndef INCLUDED_FOLD_CLOSURE_ACCUM
#define INCLUDED_FOLD_CLOSURE_ACCUM

#include <any>
#include <functional>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

template <typename A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    A a;
    std::shared_ptr<List<A>> l;
  };

  using variant_t = std::variant<Nil, Cons>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  List() {}

  explicit List(Nil _v) : v_(_v) {}

  explicit List(Cons _v) : v_(std::move(_v)) {}

  template <typename _U> explicit List(const List<_U> &_other) {
    if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
      this->v_ = Nil{};
    } else {
      const auto &[a, l] = std::get<typename List<_U>::Cons>(_other.v());
      this->v_ = Cons{
          [&]() -> A {
            if constexpr (std::is_same_v<_U, std::any>) {
              if (a.type() == typeid(A))
                return std::any_cast<A>(a);
              if constexpr (requires {
                              typename A::first_type;
                              typename A::second_type;
                            }) {
                const auto &[_k, _v] =
                    std::any_cast<std::pair<std::any, std::any>>(a);
                return A{[&]() -> typename A::first_type {
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
              return std::any_cast<A>(a);
            } else
              return A(a);
          }(),
          l ? std::make_shared<List<A>>(*l) : nullptr};
    }
  }

  static List<A> nil() { return List(Nil{}); }

  static List<A> cons(A a, List<A> l) {
    return List(Cons{std::move(a), std::make_shared<List<A>>(std::move(l))});
  }

  // MANIPULATORS
  ~List() {
    std::vector<std::shared_ptr<List<A>>> _stack = {};
    auto _drain = [&](variant_t &_v) {
      if (auto *_alt = std::get_if<Cons>(&_v)) {
        if (_alt->l) {
          _stack.push_back(std::move(_alt->l));
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

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, A &, T1 &>
  T1 fold_right(F0 &&f, T1 a0) const {
    if (std::holds_alternative<typename List<A>::Nil>(this->v())) {
      return a0;
    } else {
      const auto &[a1, a2] = std::get<typename List<A>::Cons>(this->v());
      return f(a1, a2->template fold_right<T1>(f, a0));
    }
  }
};

struct FoldClosureAccum {
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
  };

  template <typename T1, typename F1>
    requires std::is_invocable_r_v<T1, F1 &, tree &, T1 &, uint64_t &, tree &,
                                   T1 &>
  static T1 tree_rect(T1 f, F1 &&f0, const tree &t) {
    if (std::holds_alternative<typename tree::Leaf>(t.v())) {
      return f;
    } else {
      const auto &[a0, a1, a2] = std::get<typename tree::Node>(t.v());
      return f0(*a0, tree_rect<T1>(f, f0, *a0), a1, *a2,
                tree_rect<T1>(f, f0, *a2));
    }
  }

  template <typename T1, typename F1>
    requires std::is_invocable_r_v<T1, F1 &, tree &, T1 &, uint64_t &, tree &,
                                   T1 &>
  static T1 tree_rec(T1 f, F1 &&f0, const tree &t) {
    if (std::holds_alternative<typename tree::Leaf>(t.v())) {
      return f;
    } else {
      const auto &[a0, a1, a2] = std::get<typename tree::Node>(t.v());
      return f0(*a0, tree_rec<T1>(f, f0, *a0), a1, *a2,
                tree_rec<T1>(f, f0, *a2));
    }
  } /// Sum all values in a tree.

  static uint64_t tree_sum(const tree &t);
  /// Build a composed function by folding over a list of trees.
  /// Each step takes the accumulated function and the current tree,
  /// producing a new function that adds tree_sum of the current tree
  /// to the accumulated function's result.
  ///
  /// BUG HYPOTHESIS: Each fold step creates a closure &acc, &t that
  /// captures the previous closure (acc) and the current tree (t).
  /// If captures are by reference, the previous closure is stack-local
  /// and dies when the fold step returns, creating a dangling chain.
  static uint64_t compose_adders(const List<tree> &trees, uint64_t _x0);
  /// Test: compose adders from 3 trees.
  /// t1 sums to 10, t2 sums to 20, t3 sums to 30.
  /// compose_adders t1; t2; t3 x = x + 30 + 20 + 10 = x + 60
  /// Expected: compose_adders t1; t2; t3 0 = 60
  static inline const uint64_t fold_bug = []() {
    tree t1 = tree::node(tree::leaf(), UINT64_C(10), tree::leaf());
    tree t2 = tree::node(tree::leaf(), UINT64_C(20), tree::leaf());
    tree t3 = tree::node(tree::leaf(), UINT64_C(30), tree::leaf());
    return compose_adders(
        List<tree>::cons(std::move(t1),
                         List<tree>::cons(std::move(t2),
                                          List<tree>::cons(std::move(t3),
                                                           List<tree>::nil()))),
        UINT64_C(0));
  }();
  /// Test with non-zero starting value.
  /// Expected: compose_adders t1; t2; t3 7 = 67
  static inline const uint64_t fold_bug_offset = []() {
    tree t1 = tree::node(tree::leaf(), UINT64_C(10), tree::leaf());
    tree t2 = tree::node(tree::leaf(), UINT64_C(20), tree::leaf());
    tree t3 = tree::node(tree::leaf(), UINT64_C(30), tree::leaf());
    return compose_adders(
        List<tree>::cons(std::move(t1),
                         List<tree>::cons(std::move(t2),
                                          List<tree>::cons(std::move(t3),
                                                           List<tree>::nil()))),
        UINT64_C(7));
  }();
  /// Invoke the composed function twice — tests if closures survive
  /// multiple invocations.
  static inline const uint64_t fold_bug_double = []() {
    return []() {
      tree t1 = tree::node(tree::leaf(), UINT64_C(10), tree::leaf());
      tree t2 = tree::node(tree::leaf(), UINT64_C(20), tree::leaf());
      std::function<uint64_t(uint64_t)> f =
          [=](uint64_t _x0) mutable -> uint64_t {
        return compose_adders(
            List<tree>::cons(t1, List<tree>::cons(t2, List<tree>::nil())), _x0);
      };
      return (f(UINT64_C(0)) + f(UINT64_C(100)));
    }();
  }();
};

#endif // INCLUDED_FOLD_CLOSURE_ACCUM
