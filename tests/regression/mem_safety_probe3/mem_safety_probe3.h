#ifndef INCLUDED_MEM_SAFETY_PROBE3
#define INCLUDED_MEM_SAFETY_PROBE3

#include <any>
#include <functional>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

struct MemSafetyProbe3 {
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

    /// TEST 9: Closure stored in option alongside tree data in pair.
    std::pair<std::optional<std::function<uint64_t(uint64_t)>>, tree>
    opt_pair(bool b) const {
      return std::make_pair(
          (b ? std::make_optional<std::function<uint64_t(uint64_t)>>(
                   [&](uint64_t _x0) -> uint64_t {
                     return this->sum_values(_x0);
                   })
             : std::optional<std::function<uint64_t(uint64_t)>>()),
          *this);
    }

    /// TEST 8: Three closures, each capturing different tree,
    /// applied in a specific order with results feeding forward.
    uint64_t chain_three(tree t2, const tree &t3) const {
      std::function<uint64_t(uint64_t)> f1 = [&](uint64_t _x0) -> uint64_t {
        return std::move(*this).sum_values(_x0);
      };
      std::function<uint64_t(uint64_t)> f2 = [&](uint64_t _x0) -> uint64_t {
        return std::move(t2).sum_values(_x0);
      };
      return t3.sum_values(f2(f1(UINT64_C(0))));
    }

    /// TEST 7: Map a tree, producing a new tree. Then sum the new tree.
    /// The mapped function captures a tree value.
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

    /// TEST 6: Nested pair: pair of pairs of closures.
    std::pair<std::pair<std::function<uint64_t(uint64_t)>,
                        std::function<uint64_t(uint64_t)>>,
              uint64_t>
    nested_pair() const {
      tree _self_val = *this;
      return std::make_pair(std::make_pair(
                                [=](uint64_t _x0) mutable -> uint64_t {
                                  return _self_val.sum_values(_x0);
                                },
                                [](uint64_t x) { return x; }),
                            this->sum_values(UINT64_C(0)));
    }

    /// TEST 5: Mutual use: tree used BOTH as partial application arg
    /// AND as match scrutinee in the SAME scope.
    uint64_t mutual_use() const {
      tree _self_val = *this;
      std::function<uint64_t(uint64_t)> f =
          [=](uint64_t _x0) mutable -> uint64_t {
        return _self_val.sum_values(_x0);
      };
      uint64_t r = [&]() {
        if (std::holds_alternative<typename tree::Leaf>(this->v())) {
          return UINT64_C(0);
        } else {
          auto &[a0, a1, a2] = std::get<typename tree::Node>(this->v());
          return a1;
        }
      }();
      return f(r);
    }

    /// TEST 4: Tree traversal that builds up a nat accumulator
    /// using local fixpoint. The tree is captured in the fixpoint scope.
    uint64_t tree_sum() const {
      if (std::holds_alternative<typename tree::Leaf>(this->v())) {
        return UINT64_C(0);
      } else {
        const auto &[a0, a1, a2] = std::get<typename tree::Node>(this->v());
        return ((a0->tree_sum() + a1) + a2->tree_sum());
      }
    }

    /// TEST 3: Partial application result stored in a pair, then both
    /// elements of the pair are applied. The pair construction must
    /// properly clone the closures.
    std::pair<std::function<uint64_t(uint64_t)>,
              std::function<uint64_t(uint64_t)>>
    paired_closures(tree t2) const {
      tree _self_val = *this;
      return std::make_pair(
          [=](uint64_t _x0) mutable -> uint64_t {
            return _self_val.sum_values(_x0);
          },
          [=](uint64_t _x0) mutable -> uint64_t { return t2.sum_values(_x0); });
    }

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

  /// TEST 1: Local fixpoint capturing a tree value.
  /// The fixpoint accesses the captured tree on each recursive call.
  static inline const uint64_t local_fix_capture = []() {
    return []() {
      tree t = tree::node(tree::leaf(), UINT64_C(42), tree::leaf());
      auto helper_impl = [&](auto &_self_helper, uint64_t n) -> uint64_t {
        if (n <= 0) {
          return t.sum_values(UINT64_C(0));
        } else {
          uint64_t n_ = n - 1;
          return (t.sum_values(UINT64_C(1)) + _self_helper(_self_helper, n_));
        }
      };
      auto helper = [&](uint64_t n) -> uint64_t {
        return helper_impl(helper_impl, n);
      };
      return helper(UINT64_C(3));
    }();
  }();
  /// TEST 2: Local fixpoint returning a closure that captures
  /// a match-destructured field from a tree.
  static inline const uint64_t fix_with_closure = []() {
    return []() {
      tree t = tree::node(tree::node(tree::leaf(), UINT64_C(10), tree::leaf()),
                          UINT64_C(20),
                          tree::node(tree::leaf(), UINT64_C(30), tree::leaf()));
      if (std::holds_alternative<typename tree::Leaf>(t.v_mut())) {
        return UINT64_C(0);
      } else {
        auto &[a0, a1, a2] = std::get<typename tree::Node>(t.v_mut());
        std::function<uint64_t(uint64_t)> fl = [&](uint64_t _x0) -> uint64_t {
          return a0->sum_values(_x0);
        };
        uint64_t vl = fl(a1);
        std::function<uint64_t(uint64_t)> fr = [&](uint64_t _x0) -> uint64_t {
          return a2->sum_values(_x0);
        };
        uint64_t vr = fr(std::move(a1));
        return (vl + vr);
      }
    }();
  }();
  static inline const uint64_t test_paired_closures = []() {
    tree t1 = tree::node(tree::leaf(), UINT64_C(10), tree::leaf());
    tree t2 = tree::node(tree::leaf(), UINT64_C(20), tree::leaf());
    std::pair<std::function<uint64_t(uint64_t)>,
              std::function<uint64_t(uint64_t)>>
        p = std::move(t1).paired_closures(std::move(t2));
    return (p.first(UINT64_C(5)) + p.second(UINT64_C(5)));
  }();
  static inline const uint64_t test_tree_sum =
      tree::node(tree::node(tree::leaf(), UINT64_C(10), tree::leaf()),
                 UINT64_C(20),
                 tree::node(tree::leaf(), UINT64_C(30), tree::leaf()))
          .tree_sum();
  /// f = sum_values (Node (Node Leaf 10 Leaf) 20 (...))
  /// r = 20. f 20 = 10+30+20+20 = 80
  static inline const uint64_t test_mutual_use =
      tree::node(tree::node(tree::leaf(), UINT64_C(10), tree::leaf()),
                 UINT64_C(20),
                 tree::node(tree::leaf(), UINT64_C(30), tree::leaf()))
          .mutual_use();
  static inline const uint64_t test_nested_pair = []() {
    tree t = tree::node(tree::leaf(), UINT64_C(42), tree::leaf());
    std::pair<std::pair<std::function<uint64_t(uint64_t)>,
                        std::function<uint64_t(uint64_t)>>,
              uint64_t>
        p = std::move(t).nested_pair();
    return (((p.first).first(UINT64_C(10)) + (p.first).second(UINT64_C(10))) +
            p.second);
  }();
  static inline const uint64_t test_map_with_captured = []() {
    return []() {
      tree t = tree::node(tree::node(tree::leaf(), UINT64_C(5), tree::leaf()),
                          UINT64_C(10),
                          tree::node(tree::leaf(), UINT64_C(15), tree::leaf()));
      tree t2 = tree::node(tree::leaf(), UINT64_C(100), tree::leaf());
      tree mapped = std::move(t).map_tree(
          [=](uint64_t v) mutable { return (v + t2.sum_values(UINT64_C(0))); });
      return std::move(mapped).tree_sum();
    }();
  }();
  static inline const uint64_t test_chain_three =
      tree::node(tree::leaf(), UINT64_C(10), tree::leaf())
          .chain_three(tree::node(tree::leaf(), UINT64_C(20), tree::leaf()),
                       tree::node(tree::leaf(), UINT64_C(30), tree::leaf()));
  static inline const uint64_t test_opt_pair = []() {
    tree t = tree::node(tree::leaf(), UINT64_C(42), tree::leaf());
    std::pair<std::optional<std::function<uint64_t(uint64_t)>>, tree> p =
        std::move(t).opt_pair(true);
    auto _cs = p.first;
    if (_cs.has_value()) {
      const std::function<uint64_t(uint64_t)> &f = *_cs;
      return (f(UINT64_C(10)) + std::move(p).second.sum_values(UINT64_C(0)));
    } else {
      return UINT64_C(0);
    }
  }();
  /// TEST 10: Large tree with deep recursion — stresses the
  /// loopified tree traversal and clone mechanisms.
  static tree build_deep(uint64_t n);
  static inline const uint64_t test_deep_tree = []() {
    tree t = build_deep(UINT64_C(100));
    return std::move(t).tree_sum();
  }();

  /// TEST 11: Fixpoint that takes a function argument and uses it
  /// alongside captured tree data.
  template <typename F0>
    requires std::is_invocable_r_v<uint64_t, F0 &, uint64_t &>
  static uint64_t
  apply_n_times(F0 &&f, uint64_t n,
                uint64_t x) { /// _Enter: captures varying parameters for each
                              /// recursive call.

    struct _Enter {
      uint64_t n;
    };

    /// _Resume_n_: resumes after recursive call with _result.
    struct _Resume_n_ {};

    using _Frame = std::variant<_Enter, _Resume_n_>;
    uint64_t _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{n});
    /// Loopified apply_n_times: _Enter -> _Resume_n_.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        uint64_t n = _f.n;
        if (n <= 0) {
          _result = std::move(x);
        } else {
          uint64_t n_ = n - 1;
          _stack.emplace_back(_Resume_n_{});
          _stack.emplace_back(_Enter{n_});
        }
      } else {
        auto _f = std::move(std::get<_Resume_n_>(_frame));
        _result = f(std::move(_result));
      }
    }
    return _result;
  }

  static inline const uint64_t test_apply_n = []() {
    return []() {
      tree t = tree::node(tree::leaf(), UINT64_C(10), tree::leaf());
      return apply_n_times(
          [=](uint64_t _x0) mutable -> uint64_t { return t.sum_values(_x0); },
          UINT64_C(5), UINT64_C(0));
    }();
  }();
  /// TEST 12: Closure that partially applies a fixpoint.
  /// The fixpoint itself takes a function argument.
  static inline const uint64_t test_partial_fix = []() {
    return []() {
      tree t = tree::node(tree::leaf(), UINT64_C(5), tree::leaf());
      std::function<uint64_t(uint64_t)> f =
          [=](uint64_t _x0) mutable -> uint64_t {
        return apply_n_times(
            [=](uint64_t _x0) mutable -> uint64_t { return t.sum_values(_x0); },
            UINT64_C(3), _x0);
      };
      return (f(UINT64_C(0)) + f(UINT64_C(10)));
    }();
  }();
};

#endif // INCLUDED_MEM_SAFETY_PROBE3
