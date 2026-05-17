#ifndef INCLUDED_MEM_SAFETY_PROBE11
#define INCLUDED_MEM_SAFETY_PROBE11

#include <functional>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

struct MemSafetyProbe11 {
  /// Probe 11: Closure escape through ACCUMULATOR in loopified
  /// tail-recursive functions, specifically testing the interaction
  /// between the new flatten optimization (make_owned_param_matches)
  /// and closure capture in match branches.
  ///
  /// Key attack vector: A tail-recursive function with an accumulator
  /// that stores closures. Each closure captures a unique_ptr field
  /// from the match destructuring. After loopification, the match
  /// uses v_mut() and mutable bindings. If closures capture mutable
  /// bindings by reference and the field is later moved, we get
  /// use-after-move.
  template <typename A> struct mylist {
    // TYPES
    struct Mynil {};

    struct Mycons {
      A a0;
      std::unique_ptr<mylist<A>> a1;
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

    mylist(const mylist<A> &_other) : v_(std::move(_other.clone().v_)) {}

    mylist(mylist<A> &&_other) noexcept : v_(std::move(_other.v_)) {}

    mylist<A> &operator=(const mylist<A> &_other) {
      v_ = std::move(_other.clone().v_);
      return *this;
    }

    mylist<A> &operator=(mylist<A> &&_other) noexcept {
      v_ = std::move(_other.v_);
      return *this;
    }

    // ACCESSORS
    mylist<A> clone() const {
      mylist<A> _out{};

      struct _CloneFrame {
        const mylist<A> *_src;
        mylist<A> *_dst;
      };

      std::vector<_CloneFrame> _stack{};
      _stack.reserve(8);
      _stack.push_back({this, &_out});
      while (!_stack.empty()) {
        auto _frame = _stack.back();
        _stack.pop_back();
        const mylist<A> *_src = _frame._src;
        mylist<A> *_dst = _frame._dst;
        if (std::holds_alternative<Mynil>(_src->v())) {
          _dst->v_ = Mynil{};
        } else {
          const auto &_alt = std::get<Mycons>(_src->v());
          _dst->v_ = Mycons{_alt.a0,
                            _alt.a1 ? std::make_unique<mylist<A>>() : nullptr};
          auto &_dst_alt = std::get<Mycons>(_dst->v_);
          if (_alt.a1) {
            _stack.push_back({_alt.a1.get(), _dst_alt.a1.get()});
          }
        }
      }
      return _out;
    }

    // CREATORS
    template <typename _U> explicit mylist(const mylist<_U> &_other) {
      if (std::holds_alternative<typename mylist<_U>::Mynil>(_other.v())) {
        this->v_ = Mynil{};
      } else {
        const auto &[a0, a1] =
            std::get<typename mylist<_U>::Mycons>(_other.v());
        this->v_ =
            Mycons{A(a0), a1 ? std::make_unique<mylist<A>>(*a1) : nullptr};
      }
    }

    static mylist<A> mynil() { return mylist(Mynil{}); }

    static mylist<A> mycons(A a0, mylist<A> a1) {
      return mylist(
          Mycons{std::move(a0), std::make_unique<mylist<A>>(std::move(a1))});
    }

    // MANIPULATORS
    ~mylist() {
      std::vector<std::unique_ptr<mylist<A>>> _stack{};
      _stack.reserve(8);
      auto _drain = [&](mylist<A> &_node) {
        if (std::holds_alternative<Mycons>(_node.v_)) {
          auto &_alt = std::get<Mycons>(_node.v_);
          if (_alt.a1) {
            _stack.push_back(std::move(_alt.a1));
          }
        }
      };
      _drain(*this);
      while (!_stack.empty()) {
        auto _node = std::move(_stack.back());
        _stack.pop_back();
        if (_node) {
          _drain(*_node);
        }
      }
    }

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    unsigned int length() const {
      if (std::holds_alternative<typename mylist<A>::Mynil>(this->v())) {
        return 0u;
      } else {
        const auto &[a0, a1] = std::get<typename mylist<A>::Mycons>(this->v());
        return (1u + (*a1).length());
      }
    }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, A &, mylist<A> &, T1 &>
    T1 mylist_rec(T1 f, F1 &&f0) const {
      if (std::holds_alternative<typename mylist<A>::Mynil>(this->v())) {
        return f;
      } else {
        const auto &[a0, a1] = std::get<typename mylist<A>::Mycons>(this->v());
        return f0(a0, *a1, (*a1).template mylist_rec<T1>(f, f0));
      }
    }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, A &, mylist<A> &, T1 &>
    T1 mylist_rect(T1 f, F1 &&f0) const {
      if (std::holds_alternative<typename mylist<A>::Mynil>(this->v())) {
        return f;
      } else {
        const auto &[a0, a1] = std::get<typename mylist<A>::Mycons>(this->v());
        return f0(a0, *a1, (*a1).template mylist_rect<T1>(f, f0));
      }
    }
  };

  static unsigned int
  sum_fns(const mylist<std::function<unsigned int(unsigned int)>> &l);

  struct tree {
    // TYPES
    struct Leaf {};

    struct Node {
      std::unique_ptr<tree> a0;
      unsigned int a1;
      std::unique_ptr<tree> a2;
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

    tree(const tree &_other) : v_(std::move(_other.clone().v_)) {}

    tree(tree &&_other) noexcept : v_(std::move(_other.v_)) {}

    tree &operator=(const tree &_other) {
      v_ = std::move(_other.clone().v_);
      return *this;
    }

    tree &operator=(tree &&_other) noexcept {
      v_ = std::move(_other.v_);
      return *this;
    }

    // ACCESSORS
    tree clone() const {
      tree _out{};

      struct _CloneFrame {
        const tree *_src;
        tree *_dst;
      };

      std::vector<_CloneFrame> _stack{};
      _stack.reserve(8);
      _stack.push_back({this, &_out});
      while (!_stack.empty()) {
        auto _frame = _stack.back();
        _stack.pop_back();
        const tree *_src = _frame._src;
        tree *_dst = _frame._dst;
        if (std::holds_alternative<Leaf>(_src->v())) {
          _dst->v_ = Leaf{};
        } else {
          const auto &_alt = std::get<Node>(_src->v());
          _dst->v_ = Node{_alt.a0 ? std::make_unique<tree>() : nullptr, _alt.a1,
                          _alt.a2 ? std::make_unique<tree>() : nullptr};
          auto &_dst_alt = std::get<Node>(_dst->v_);
          if (_alt.a0) {
            _stack.push_back({_alt.a0.get(), _dst_alt.a0.get()});
          }
          if (_alt.a2) {
            _stack.push_back({_alt.a2.get(), _dst_alt.a2.get()});
          }
        }
      }
      return _out;
    }

    // CREATORS
    static tree leaf() { return tree(Leaf{}); }

    static tree node(tree a0, unsigned int a1, tree a2) {
      return tree(Node{std::make_unique<tree>(std::move(a0)), a1,
                       std::make_unique<tree>(std::move(a2))});
    }

    // MANIPULATORS
    ~tree() {
      std::vector<std::unique_ptr<tree>> _stack{};
      _stack.reserve(8);
      auto _drain = [&](tree &_node) {
        if (std::holds_alternative<Node>(_node.v_)) {
          auto &_alt = std::get<Node>(_node.v_);
          if (_alt.a0) {
            _stack.push_back(std::move(_alt.a0));
          }
          if (_alt.a2) {
            _stack.push_back(std::move(_alt.a2));
          }
        }
      };
      _drain(*this);
      while (!_stack.empty()) {
        auto _node = std::move(_stack.back());
        _stack.pop_back();
        if (_node) {
          _drain(*_node);
        }
      }
    }

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    /// TEST 6: Function that matches on a tree AND returns a closure
    /// that RETURNS A TREE. Tests capture of value types in returned
    /// closures where the return type contains unique_ptr.
    tree tree_transformer(unsigned int n) const {
      if (std::holds_alternative<typename tree::Leaf>(this->v())) {
        return tree::node(tree::leaf(), n, tree::leaf());
      } else {
        const auto &[a0, a1, a2] = std::get<typename tree::Node>(this->v());
        return tree::node(*a0, (a1 + n), *a2);
      }
    }

    /// TEST 4: Closure capturing pattern variables from a NESTED match.
    /// The outer match destructs a tree, the inner match destructs a list.
    /// Tests pre-copy across nested match scopes.
    unsigned int nested_capture(const mylist<unsigned int> &l,
                                unsigned int n) const {
      if (std::holds_alternative<typename tree::Leaf>(this->v())) {
        return n;
      } else {
        const auto &[a0, a1, a2] = std::get<typename tree::Node>(this->v());
        if (std::holds_alternative<typename mylist<unsigned int>::Mynil>(
                l.v())) {
          return (a1 + n);
        } else {
          const auto &[a00, a10] =
              std::get<typename mylist<unsigned int>::Mycons>(l.v());
          return (((((*a0).tree_sum() + (*a2).tree_sum()) + a00) + a1) + n);
        }
      }
    }

    unsigned int tree_depth() const {
      if (std::holds_alternative<typename tree::Leaf>(this->v())) {
        return 0u;
      } else {
        const auto &[a0, a1, a2] = std::get<typename tree::Node>(this->v());
        unsigned int dl = (*a0).tree_depth();
        unsigned int dr = (*a2).tree_depth();
        return (1u + (dl <= dr ? dr : dl));
      }
    }

    unsigned int tree_sum() const {
      if (std::holds_alternative<typename tree::Leaf>(this->v())) {
        return 0u;
      } else {
        const auto &[a0, a1, a2] = std::get<typename tree::Node>(this->v());
        return (((*a0).tree_sum() + a1) + (*a2).tree_sum());
      }
    }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, tree &, T1 &, unsigned int &,
                                     tree &, T1 &>
    T1 tree_rec(T1 f, F1 &&f0) const {
      if (std::holds_alternative<typename tree::Leaf>(this->v())) {
        return f;
      } else {
        const auto &[a0, a1, a2] = std::get<typename tree::Node>(this->v());
        return f0(*a0, (*a0).template tree_rec<T1>(f, f0), a1, *a2,
                  (*a2).template tree_rec<T1>(f, f0));
      }
    }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, tree &, T1 &, unsigned int &,
                                     tree &, T1 &>
    T1 tree_rect(T1 f, F1 &&f0) const {
      if (std::holds_alternative<typename tree::Leaf>(this->v())) {
        return f;
      } else {
        const auto &[a0, a1, a2] = std::get<typename tree::Node>(this->v());
        return f0(*a0, (*a0).template tree_rect<T1>(f, f0), a1, *a2,
                  (*a2).template tree_rect<T1>(f, f0));
      }
    }
  };

  /// TEST 1: Accumulate closures that capture BOTH subtrees.
  /// Each closure uses tree_sum on both l and r.
  /// Both subtrees are also used in recursive calls.
  /// After loopification with flatten, the subtrees' unique_ptrs
  /// may be moved into continuation frames.
  template <typename T1>
  static unsigned int _collect_dual_captures_f(const T1, const tree l,
                                               const tree r) {
    return (std::move(l).tree_sum() + r.tree_sum());
  }

  static mylist<std::function<unsigned int(unsigned int)>>
  collect_dual_captures(const tree &t,
                        mylist<std::function<unsigned int(unsigned int)>> acc);
  static inline const unsigned int test_dual_capture = []() {
    tree t =
        tree::node(tree::node(tree::leaf(), 5u, tree::leaf()), 10u,
                   tree::node(tree::leaf(), 15u,
                              tree::node(tree::leaf(), 20u, tree::leaf())));
    return sum_fns(collect_dual_captures(
        std::move(t),
        mylist<std::function<unsigned int(unsigned int)>>::mynil()));
  }();

  /// TEST 2: Closure captures the TAIL of the list (unique_ptr field).
  /// Each closure computes length of the tail.
  /// After loopification, the tail pointer may be moved.
  template <typename T1>
  static unsigned int _capture_tails_f(const T1, const unsigned int x,
                                       const mylist<unsigned int> xs) {
    return (std::move(x) + xs.length());
  }

  static mylist<std::function<unsigned int(unsigned int)>>
  capture_tails(const mylist<unsigned int> &l,
                mylist<std::function<unsigned int(unsigned int)>> acc);
  static inline const unsigned int test_capture_tails = []() {
    mylist<unsigned int> l = mylist<unsigned int>::mycons(
        100u, mylist<unsigned int>::mycons(
                  200u, mylist<unsigned int>::mycons(
                            300u, mylist<unsigned int>::mynil())));
    return sum_fns(capture_tails(
        std::move(l),
        mylist<std::function<unsigned int(unsigned int)>>::mynil()));
  }();

  /// TEST 3: Closure captures a SUBTREE, but the subtree is ALSO
  /// passed to a recursive call AND used in the continuation.
  /// Tests whether the clone/pre-copy mechanism handles triple use.
  template <typename T1>
  static unsigned int _triple_use_tree_fl(const T1, const tree l) {
    return std::move(l).tree_sum();
  }

  template <typename T1>
  static unsigned int _triple_use_tree_fr(const T1, const tree r) {
    return r.tree_sum();
  }

  static mylist<std::function<unsigned int(unsigned int)>>
  triple_use_tree(const tree &t,
                  mylist<std::function<unsigned int(unsigned int)>> acc);
  static inline const unsigned int test_triple_use = []() {
    tree t = tree::node(tree::node(tree::leaf(), 3u, tree::leaf()), 7u,
                        tree::node(tree::leaf(), 11u, tree::leaf()));
    return sum_fns(triple_use_tree(
        std::move(t),
        mylist<std::function<unsigned int(unsigned int)>>::mynil()));
  }();
  static inline const unsigned int test_nested_capture = []() {
    tree t = tree::node(tree::node(tree::leaf(), 10u, tree::leaf()), 20u,
                        tree::node(tree::leaf(), 30u, tree::leaf()));
    mylist<unsigned int> l = mylist<unsigned int>::mycons(
        5u, mylist<unsigned int>::mycons(99u, mylist<unsigned int>::mynil()));
    return std::move(t).nested_capture(std::move(l), 7u);
  }();

  /// TEST 5: Tail-recursive function with two accumulators,
  /// one of which stores closures that capture the other.
  /// Tests whether accumulator values are properly captured.
  template <typename T1>
  static unsigned int _dual_accum_f(const T1, const unsigned int new_sum) {
    return new_sum;
  }

  static mylist<std::function<unsigned int(unsigned int)>>
  dual_accum(const mylist<unsigned int> &l, unsigned int sum_acc,
             mylist<std::function<unsigned int(unsigned int)>> fn_acc);
  static inline const unsigned int test_dual_accum = []() {
    mylist<unsigned int> l = mylist<unsigned int>::mycons(
        10u, mylist<unsigned int>::mycons(
                 20u, mylist<unsigned int>::mycons(
                          30u, mylist<unsigned int>::mynil())));
    return sum_fns(
        dual_accum(std::move(l), 0u,
                   mylist<std::function<unsigned int(unsigned int)>>::mynil()));
  }();
  static inline const unsigned int test_tree_transformer = []() {
    return []() {
      tree t = tree::node(tree::node(tree::leaf(), 5u, tree::leaf()), 10u,
                          tree::node(tree::leaf(), 15u, tree::leaf()));
      std::function<tree(unsigned int)> f = [&](unsigned int _x0) -> tree {
        return std::move(t).tree_transformer(_x0);
      };
      tree t2 = f(100u);
      return std::move(t2).tree_sum();
    }();
  }();
};

#endif // INCLUDED_MEM_SAFETY_PROBE11
