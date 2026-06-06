#ifndef INCLUDED_MEM_SAFETY_PROBE25
#define INCLUDED_MEM_SAFETY_PROBE25

#include <any>
#include <functional>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

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

    /// TEST 8: Option wrapping a closure from match.
    /// Exercises different code path for returning closures
    /// through an inductive constructor.
    std::optional<std::function<uint64_t(uint64_t)>>
    match_closure_opt(bool b) const {
      tree _self_val = *this;
      if (b) {
        return std::make_optional<std::function<uint64_t(uint64_t)>>(
            [=](uint64_t x) mutable {
              if (std::holds_alternative<typename tree::Leaf>(_self_val.v())) {
                return x;
              } else {
                const auto &[a0, a1, a2] =
                    std::get<typename tree::Node>(_self_val.v());
                return (((x + a0->tree_sum()) + a1) + a2->tree_sum());
              }
            });
      } else {
        return std::optional<std::function<uint64_t(uint64_t)>>();
      }
    }

    /// TEST 7: Return closure from match that captures a tree child,
    /// then store it in a pair. Double-wrapping test.
    std::pair<std::function<uint64_t(uint64_t)>, uint64_t>
    match_then_pair() const {
      tree _self_val = *this;
      std::function<uint64_t(uint64_t)> f = [=](uint64_t x) mutable {
        if (std::holds_alternative<typename tree::Leaf>(_self_val.v())) {
          return x;
        } else {
          const auto &[a0, a1, a2] =
              std::get<typename tree::Node>(_self_val.v());
          return ((x + a0->tree_sum()) + a1);
        }
      };
      return std::make_pair(f, std::move(*this).tree_sum());
    }

    /// TEST 5: Deep match — closure captures grandchild of tree.
    /// ll is child-of-child, accessed via two levels of unique_ptr deref.
    uint64_t deep_match_closure(uint64_t x) const {
      if (std::holds_alternative<typename tree::Leaf>(this->v())) {
        return x;
      } else {
        const auto &[a0, a1, a2] = std::get<typename tree::Node>(this->v());
        auto &&_sv0 = *a0;
        if (std::holds_alternative<typename tree::Leaf>(_sv0.v())) {
          return (x + a1);
        } else {
          const auto &[a00, a10, a20] = std::get<typename tree::Node>(_sv0.v());
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
        const auto &[a0, a1, a2] = std::get<typename tree::Node>(this->v());
        if (std::holds_alternative<typename tree::Leaf>(t2.v())) {
          return (x + a1);
        } else {
          const auto &[a00, a10, a20] = std::get<typename tree::Node>(t2.v());
          return (((x + a0->tree_sum()) + a10) + a20->tree_sum());
        }
      }
    }

    /// TEST 3: Return PAIR of closures from match.
    /// Each closure captures different match-bound children.
    std::pair<std::function<uint64_t(uint64_t)>,
              std::function<uint64_t(uint64_t)>>
    pair_closures() const {
      if (std::holds_alternative<typename tree::Leaf>(this->v())) {
        return std::make_pair([](uint64_t x) { return x; },
                              [](uint64_t x) { return x; });
      } else {
        const auto &[a0, a1, a2] = std::get<typename tree::Node>(this->v());
        const tree &a0_value = *a0;
        const tree &a2_value = *a2;
        return std::make_pair(
            [=](uint64_t x) mutable { return (x + a0_value.tree_sum()); },
            [=](uint64_t x) mutable { return (x + a2_value.tree_sum()); });
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

  static inline const uint64_t test_make_sum_fn =
      tree::node(tree::node(tree::leaf(), UINT64_C(3), tree::leaf()),
                 UINT64_C(7),
                 tree::node(tree::leaf(), UINT64_C(11), tree::leaf()))
          .make_sum_fn(UINT64_C(100));
  static inline const uint64_t test_match_closure =
      tree::node(tree::node(tree::leaf(), UINT64_C(3), tree::leaf()),
                 UINT64_C(7),
                 tree::node(tree::leaf(), UINT64_C(11), tree::leaf()))
          .match_closure(UINT64_C(100));
  static inline const uint64_t test_pair_closures = []() {
    std::pair<std::function<uint64_t(uint64_t)>,
              std::function<uint64_t(uint64_t)>>
        p = tree::node(tree::node(tree::leaf(), UINT64_C(3), tree::leaf()),
                       UINT64_C(7),
                       tree::node(tree::leaf(), UINT64_C(11), tree::leaf()))
                .pair_closures();
    return (p.first(UINT64_C(100)) + p.second(UINT64_C(200)));
  }();
  static inline const uint64_t test_nested_match_closure =
      tree::node(tree::node(tree::leaf(), UINT64_C(3), tree::leaf()),
                 UINT64_C(7),
                 tree::node(tree::leaf(), UINT64_C(11), tree::leaf()))
          .nested_match_closure(
              tree::node(tree::node(tree::leaf(), UINT64_C(2), tree::leaf()),
                         UINT64_C(5),
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

  static mylist<std::function<uint64_t(uint64_t)>> build_adders(const tree &t);
  static uint64_t
  apply_first(const mylist<std::function<uint64_t(uint64_t)>> &l, uint64_t x);
  static inline const uint64_t test_build_adders = []() {
    mylist<std::function<uint64_t(uint64_t)>> adders =
        build_adders(tree::node(tree::leaf(), UINT64_C(42), tree::leaf()));
    return apply_first(std::move(adders), UINT64_C(100));
  }();
  static inline const uint64_t test_match_then_pair = []() {
    std::pair<std::function<uint64_t(uint64_t)>, uint64_t> p =
        tree::node(tree::node(tree::leaf(), UINT64_C(4), tree::leaf()),
                   UINT64_C(6),
                   tree::node(tree::leaf(), UINT64_C(9), tree::leaf()))
            .match_then_pair();
    return (p.first(UINT64_C(100)) + p.second);
  }();
  static inline const uint64_t test_match_closure_opt = []() -> uint64_t {
    auto _cs = tree::node(tree::node(tree::leaf(), UINT64_C(2), tree::leaf()),
                          UINT64_C(5),
                          tree::node(tree::leaf(), UINT64_C(8), tree::leaf()))
                   .match_closure_opt(true);
    if (_cs.has_value()) {
      const std::function<uint64_t(uint64_t)> &f = *_cs;
      return f(UINT64_C(100));
    } else {
      return UINT64_C(0);
    }
  }();
};

#endif // INCLUDED_MEM_SAFETY_PROBE25
