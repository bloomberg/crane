#ifndef INCLUDED_MEM_SAFETY_PROBE6
#define INCLUDED_MEM_SAFETY_PROBE6

#include <any>
#include <functional>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

struct MemSafetyProbe6 {
  /// These tests probe closures that capture RECURSIVE self-reference
  /// fields from match bindings. In C++, these fields are unique_ptr.
  /// A lambda capturing a unique_ptr by = fails (non-copyable).
  /// A lambda capturing by & would dangle if returned.
  /// Crane must pre-copy or clone the field.
  ///
  /// NOTE: All functions use nat as FIRST argument to avoid
  /// methodification bugs with curried return types.
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

    /// TEST 3: Closure returned from match that applies a function
    /// to the tail — forces unique_ptr access and HOF.
    template <typename T1, typename F0>
      requires std::is_invocable_r_v<T1, F0 &, A &>
    mylist<T1> mymap(F0 &&f) const {
      if (std::holds_alternative<typename mylist<A>::Mynil>(this->v())) {
        return mylist<T1>::mynil();
      } else {
        const auto &[a0, a1] = std::get<typename mylist<A>::Mycons>(this->v());
        return mylist<T1>::mycons(f(a0), a1->template mymap<T1>(f));
      }
    }

    /// TEST 2: Closure from match that reconstructs using both
    /// a value field and a recursive field.
    mylist<A> head_and_tail(uint64_t, const A &, const A &) const {
      if (std::holds_alternative<typename mylist<A>::Mynil>(this->v())) {
        return mylist<A>::mynil();
      } else {
        const auto &[a0, a1] = std::get<typename mylist<A>::Mycons>(this->v());
        return mylist<A>::mycons(a0, *a1);
      }
    }

    /// TEST 1: Return a closure that uses the TAIL of the list.
    /// xs is a unique_ptr<mylist> field — the closure must clone it.
    uint64_t tail_adder(uint64_t, uint64_t n) const {
      if (std::holds_alternative<typename mylist<A>::Mynil>(this->v())) {
        return n;
      } else {
        const auto &[a0, a1] = std::get<typename mylist<A>::Mycons>(this->v());
        return (a1->length() + n);
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

  static inline const uint64_t test_tail_adder = []() {
    mylist<uint64_t> l = mylist<uint64_t>::mycons(
        UINT64_C(1),
        mylist<uint64_t>::mycons(
            UINT64_C(2),
            mylist<uint64_t>::mycons(UINT64_C(3), mylist<uint64_t>::mynil())));
    return std::move(l).tail_adder(UINT64_C(0), UINT64_C(100));
  }();
  static inline const uint64_t test_head_and_tail = []() {
    return []() {
      mylist<uint64_t> l = mylist<uint64_t>::mycons(
          UINT64_C(10),
          mylist<uint64_t>::mycons(UINT64_C(20), mylist<uint64_t>::mynil()));
      std::function<mylist<uint64_t>(uint64_t)> f =
          [&](uint64_t _x0) -> mylist<uint64_t> {
        return std::move(l).head_and_tail(UINT64_C(0), UINT64_C(0), _x0);
      };
      mylist<uint64_t> l2 = f(UINT64_C(99));
      return std::move(l2).length();
    }();
  }();

  /// f reconstructs the list 10, 20. length 10,20 = 2
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

    /// TEST 4: Return a closure that captures BOTH subtrees of a tree.
    /// Both l and r are unique_ptr fields.
    tree both_subtrees(uint64_t, bool x) const {
      if (std::holds_alternative<typename tree::Leaf>(this->v())) {
        return tree::leaf();
      } else {
        const auto &[a0, a1, a2] = std::get<typename tree::Node>(this->v());
        if (x) {
          return *a0;
        } else {
          return *a2;
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

  template <typename F2>
    requires std::is_invocable_r_v<uint64_t, F2 &, uint64_t &>
  static mylist<uint64_t> tail_mapper(uint64_t, const mylist<uint64_t> &l,
                                      F2 &&x) {
    if (std::holds_alternative<typename mylist<uint64_t>::Mynil>(l.v())) {
      return mylist<uint64_t>::mynil();
    } else {
      const auto &[a0, a1] = std::get<typename mylist<uint64_t>::Mycons>(l.v());
      return mylist<uint64_t>::mycons(a0, a1->template mymap<uint64_t>(x));
    }
  }

  static inline const uint64_t test_tail_mapper = []() {
    return []() {
      mylist<uint64_t> l = mylist<uint64_t>::mycons(
          UINT64_C(1),
          mylist<uint64_t>::mycons(
              UINT64_C(2), mylist<uint64_t>::mycons(
                               UINT64_C(3), mylist<uint64_t>::mynil())));
      std::function<mylist<uint64_t>(std::function<uint64_t(uint64_t)>)> f =
          [&](std::function<uint64_t(uint64_t)> _x0) -> mylist<uint64_t> {
        return tail_mapper(UINT64_C(0), std::move(l), _x0);
      };
      mylist<uint64_t> l2 = f([](uint64_t n) { return (n * UINT64_C(10)); });
      return std::move(l2).length();
    }();
  }();
  static inline const uint64_t test_both_subtrees = []() {
    return []() {
      tree t = tree::node(tree::node(tree::leaf(), UINT64_C(10), tree::leaf()),
                          UINT64_C(20),
                          tree::node(tree::leaf(), UINT64_C(30), tree::leaf()));
      std::function<tree(bool)> sel = [=](bool _x0) mutable -> tree {
        return t.both_subtrees(UINT64_C(0), _x0);
      };
      return (sel(true).tree_sum() + sel(false).tree_sum());
    }();
  }();
  /// TEST 5: Chain of closures each pre-computing from the tail.
  static mylist<std::function<uint64_t(uint64_t)>>
  build_chain(const mylist<uint64_t> &l);
  static uint64_t
  apply_chain(const mylist<std::function<uint64_t(uint64_t)>> &fns, uint64_t x);
  static inline const uint64_t test_chain = []() {
    mylist<uint64_t> l = mylist<uint64_t>::mycons(
        UINT64_C(10),
        mylist<uint64_t>::mycons(
            UINT64_C(20),
            mylist<uint64_t>::mycons(UINT64_C(30), mylist<uint64_t>::mynil())));
    mylist<std::function<uint64_t(uint64_t)>> fns = build_chain(std::move(l));
    return apply_chain(std::move(fns), UINT64_C(0));
  }();
  /// TEST 6: Closure captures tail, then tail is used again
  /// after the closure is created — tests double use.
  static uint64_t capture_and_reuse(uint64_t _x, const mylist<uint64_t> &l);
  static inline const uint64_t test_capture_reuse = capture_and_reuse(
      UINT64_C(0),
      mylist<uint64_t>::mycons(
          UINT64_C(5),
          mylist<uint64_t>::mycons(
              UINT64_C(1), mylist<uint64_t>::mycons(
                               UINT64_C(2), mylist<uint64_t>::mynil()))));
};

#endif // INCLUDED_MEM_SAFETY_PROBE6
