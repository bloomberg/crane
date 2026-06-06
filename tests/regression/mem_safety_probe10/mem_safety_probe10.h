#ifndef INCLUDED_MEM_SAFETY_PROBE10
#define INCLUDED_MEM_SAFETY_PROBE10

#include <any>
#include <functional>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

struct MemSafetyProbe10 {
  /// Probe 10: Recursive functions that RETURN closures.
  /// Tests whether return_captures_by_value processes lambdas
  /// correctly through loopification.
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

    /// TEST 8: Closure returned from function, capturing a TREE value.
    /// The tree is a value type with unique_ptr self-references.
    /// Tests whether = capture correctly deep-copies the tree.
    uint64_t make_tree_summer(uint64_t n) const {
      return (this->tree_sum() + n);
    }

    /// TEST 5: Closure capturing value from OUTER match,
    /// returned from INNER match. Tests nested match +
    /// capture interaction.
    uint64_t nested_match_closure(bool b, uint64_t n) const {
      if (std::holds_alternative<typename tree::Leaf>(this->v())) {
        return n;
      } else {
        const auto &[a0, a1, a2] = std::get<typename tree::Node>(this->v());
        if (b) {
          return ((a0->tree_sum() + a1) + n);
        } else {
          return ((a2->tree_sum() + a1) + n);
        }
      }
    }

    /// TEST 1: Recursive function that returns a closure.
    /// Each level composes the closure from recursive results.
    /// After loopification, these closures are assigned to _result,
    /// not returned via Sreturn.
    uint64_t tree_to_adder(uint64_t _x0) const {
      tree _self_val = *this;
      return [=]() mutable -> std::function<uint64_t(uint64_t)> {
        if (std::holds_alternative<typename tree::Leaf>(_self_val.v())) {
          return [](uint64_t n) { return n; };
        } else {
          const auto &[a0, a1, a2] =
              std::get<typename tree::Node>(_self_val.v());
          const tree &a0_value = *a0;
          const tree &a2_value = *a2;
          std::function<uint64_t(uint64_t)> fl =
              [=](uint64_t _x0) mutable -> uint64_t {
            return a0_value.tree_to_adder(_x0);
          };
          std::function<uint64_t(uint64_t)> fr =
              [=](uint64_t _x0) mutable -> uint64_t {
            return a2_value.tree_to_adder(_x0);
          };
          return [=](uint64_t n) mutable { return fl((a1 + fr(n))); };
        }
      }()(_x0);
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

  static uint64_t sum_fns(const mylist<std::function<uint64_t(uint64_t)>> &l);
  static inline const uint64_t test_tree_adder = []() {
    tree t = tree::node(tree::node(tree::leaf(), UINT64_C(10), tree::leaf()),
                        UINT64_C(20),
                        tree::node(tree::leaf(), UINT64_C(30), tree::leaf()));
    return std::move(t).tree_to_adder(UINT64_C(5));
  }();

  /// TEST 2: Build closures during list traversal,
  /// where each closure captures the HEAD of the list
  /// and the closure from the previous step.
  static uint64_t
  chain_adders(const mylist<uint64_t> &l, std::function<uint64_t(uint64_t)> acc,
               uint64_t _x0) { /// _Enter: captures varying parameters for each
                               /// recursive call.

    struct _Enter {
      std::function<uint64_t(uint64_t)> acc;
      mylist<uint64_t> l;
    };

    using _Frame = std::variant<_Enter>;
    uint64_t _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{std::move(acc), l});
    /// Loopified chain_adders: _Enter.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      auto _f = std::move(std::get<_Enter>(_frame));
      std::function<uint64_t(uint64_t)> acc = std::move(_f.acc);
      const mylist<uint64_t> &l = std::move(_f.l);
      _result = [=]() mutable -> std::function<uint64_t(uint64_t)> {
        if (std::holds_alternative<typename mylist<uint64_t>::Mynil>(l.v())) {
          return acc;
        } else {
          const auto &[a0, a1] =
              std::get<typename mylist<uint64_t>::Mycons>(l.v());
          const mylist<uint64_t> &a1_value = *a1;
          return [=](uint64_t _x0) mutable -> uint64_t {
            return chain_adders(
                a1_value, [=](uint64_t n) mutable { return acc((a0 + n)); },
                _x0);
          };
        }
      }()(_x0);
    }
    return _result;
  }

  static inline const uint64_t test_chain = []() {
    mylist<uint64_t> l = mylist<uint64_t>::mycons(
        UINT64_C(10),
        mylist<uint64_t>::mycons(
            UINT64_C(20),
            mylist<uint64_t>::mycons(UINT64_C(30), mylist<uint64_t>::mynil())));
    return chain_adders(
        std::move(l), [](uint64_t x) { return x; }, UINT64_C(7));
  }();
  /// TEST 3: Recursive function returning a list of closures.
  /// Each closure captures the tree node's value and subtrees.
  static mylist<std::function<uint64_t(uint64_t)>>
  collect_adders(const tree &t);
  static inline const uint64_t test_collect_adders = []() {
    tree t = tree::node(tree::node(tree::leaf(), UINT64_C(5), tree::leaf()),
                        UINT64_C(10),
                        tree::node(tree::leaf(), UINT64_C(15), tree::leaf()));
    return sum_fns(collect_adders(std::move(t)));
  }();
  /// TEST 4: Closure returned from nested match.
  /// Tests return_captures_by_value through Sif branches.
  static uint64_t choose_fn(const std::optional<bool> &o, uint64_t v,
                            uint64_t n);
  static inline const uint64_t test_choose = []() {
    std::function<uint64_t(uint64_t)> f1 = [](uint64_t _x0) -> uint64_t {
      return choose_fn(std::make_optional<bool>(true), UINT64_C(10), _x0);
    };
    std::function<uint64_t(uint64_t)> f2 = [](uint64_t _x0) -> uint64_t {
      return choose_fn(std::make_optional<bool>(false), UINT64_C(3), _x0);
    };
    std::function<uint64_t(uint64_t)> f3 = [](uint64_t _x0) -> uint64_t {
      return choose_fn(std::optional<bool>(), UINT64_C(99), _x0);
    };
    return ((f1(UINT64_C(5)) + f2(UINT64_C(7))) + f3(UINT64_C(42)));
  }();
  static inline const uint64_t test_nested = []() {
    return []() {
      tree t = tree::node(tree::node(tree::leaf(), UINT64_C(5), tree::leaf()),
                          UINT64_C(10),
                          tree::node(tree::leaf(), UINT64_C(15), tree::leaf()));
      std::function<uint64_t(uint64_t)> f1 =
          [=](uint64_t _x0) mutable -> uint64_t {
        return t.nested_match_closure(true, _x0);
      };
      std::function<uint64_t(uint64_t)> f2 = [&](uint64_t _x0) -> uint64_t {
        return std::move(t).nested_match_closure(false, _x0);
      };
      return (f1(UINT64_C(0)) + f2(UINT64_C(0)));
    }();
  }();
  /// TEST 6: Function returning closure in pair.
  /// Tests pair construction with closure.
  static std::pair<std::function<uint64_t(uint64_t)>, uint64_t>
  pair_with_fn(uint64_t n);
  static inline const uint64_t test_pair_fn = []() {
    std::pair<std::function<uint64_t(uint64_t)>, uint64_t> p =
        pair_with_fn(UINT64_C(10));
    return (p.first(UINT64_C(5)) + p.second);
  }();
  /// TEST 7: Mutually recursive functions using a fixpoint
  /// where one captures the other's result as a closure.
  static mylist<std::function<uint64_t(uint64_t)>>
  build_tree_fns(const tree &t, uint64_t depth);
  static inline const uint64_t test_tree_fns = []() {
    tree t = tree::node(tree::node(tree::leaf(), UINT64_C(3), tree::leaf()),
                        UINT64_C(7),
                        tree::node(tree::leaf(), UINT64_C(11), tree::leaf()));
    return sum_fns(build_tree_fns(std::move(t), UINT64_C(2)));
  }();
  static inline const uint64_t test_tree_capture = []() {
    tree t = tree::node(tree::node(tree::leaf(), UINT64_C(100), tree::leaf()),
                        UINT64_C(200),
                        tree::node(tree::leaf(), UINT64_C(300), tree::leaf()));
    return std::move(t).make_tree_summer(UINT64_C(0));
  }();
};

#endif // INCLUDED_MEM_SAFETY_PROBE10
