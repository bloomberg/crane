#ifndef INCLUDED_MEM_SAFETY_PROBE11
#define INCLUDED_MEM_SAFETY_PROBE11

#include <functional>
#include <memory>
#include <optional>
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
  template <typename t_A> struct mylist {
    // TYPES
    struct Mynil {};

    struct Mycons {
      t_A d_a0;
      std::unique_ptr<mylist<t_A>> d_a1;
    };

    using variant_t = std::variant<Mynil, Mycons>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    mylist() {}

    explicit mylist(Mynil _v) : d_v_(_v) {}

    explicit mylist(Mycons _v) : d_v_(std::move(_v)) {}

    mylist(const mylist<t_A> &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    mylist(mylist<t_A> &&_other) : d_v_(std::move(_other.d_v_)) {}

    mylist<t_A> &operator=(const mylist<t_A> &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    mylist<t_A> &operator=(mylist<t_A> &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    mylist<t_A> clone() const {
      mylist<t_A> _out{};

      struct _CloneFrame {
        const mylist<t_A> *_src;
        mylist<t_A> *_dst;
      };

      std::vector<_CloneFrame> _stack{};
      _stack.reserve(8);
      _stack.push_back({this, &_out});
      while (!_stack.empty()) {
        auto _frame = _stack.back();
        _stack.pop_back();
        const mylist<t_A> *_src = _frame._src;
        mylist<t_A> *_dst = _frame._dst;
        if (std::holds_alternative<Mynil>(_src->v())) {
          _dst->d_v_ = Mynil();
        } else {
          const auto &_alt = std::get<Mycons>(_src->v());
          _dst->d_v_ = Mycons(
              _alt.d_a0, _alt.d_a1 ? std::make_unique<mylist<t_A>>() : nullptr);
          auto &_dst_alt = std::get<Mycons>(_dst->d_v_);
          if (_alt.d_a1) {
            _stack.push_back({_alt.d_a1.get(), _dst_alt.d_a1.get()});
          }
        }
      }
      return _out;
    }

    // CREATORS
    template <typename _U> explicit mylist(const mylist<_U> &_other) {
      if (std::holds_alternative<typename mylist<_U>::Mynil>(_other.v())) {
        this->d_v_ = Mynil();
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename mylist<_U>::Mycons>(_other.v());
        this->d_v_ = Mycons(
            t_A(d_a0), d_a1 ? std::make_unique<mylist<t_A>>(*d_a1) : nullptr);
      }
    }

    static mylist<t_A> mynil() { return mylist(Mynil()); }

    static mylist<t_A> mycons(t_A a0, mylist<t_A> a1) {
      return mylist(
          Mycons(std::move(a0), std::make_unique<mylist<t_A>>(std::move(a1))));
    }

    // MANIPULATORS
    ~mylist() {
      std::vector<std::unique_ptr<mylist<t_A>>> _stack{};
      _stack.reserve(8);
      auto _drain = [&](mylist<t_A> &_node) {
        if (std::holds_alternative<Mycons>(_node.d_v_)) {
          auto &_alt = std::get<Mycons>(_node.d_v_);
          if (_alt.d_a1) {
            _stack.push_back(std::move(_alt.d_a1));
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

    inline variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    const variant_t &v() const { return d_v_; }

    unsigned int length() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename mylist<t_A>::Mynil>(_sv.v())) {
        return 0u;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename mylist<t_A>::Mycons>(_sv.v());
        return (1u + (*(d_a1)).length());
      }
    }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, t_A &, mylist<t_A> &, T1 &>
    T1 mylist_rec(const T1 f, F1 &&f0) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename mylist<t_A>::Mynil>(_sv.v())) {
        return f;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename mylist<t_A>::Mycons>(_sv.v());
        return f0(d_a0, *(d_a1), (*(d_a1)).template mylist_rec<T1>(f, f0));
      }
    }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, t_A &, mylist<t_A> &, T1 &>
    T1 mylist_rect(const T1 f, F1 &&f0) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename mylist<t_A>::Mynil>(_sv.v())) {
        return f;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename mylist<t_A>::Mycons>(_sv.v());
        return f0(d_a0, *(d_a1), (*(d_a1)).template mylist_rect<T1>(f, f0));
      }
    }
  };

  static unsigned int
  sum_fns(const mylist<std::function<unsigned int(unsigned int)>> &l);

  struct tree {
    // TYPES
    struct Leaf {};

    struct Node {
      std::unique_ptr<tree> d_a0;
      unsigned int d_a1;
      std::unique_ptr<tree> d_a2;
    };

    using variant_t = std::variant<Leaf, Node>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    tree() {}

    explicit tree(Leaf _v) : d_v_(_v) {}

    explicit tree(Node _v) : d_v_(std::move(_v)) {}

    tree(const tree &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    tree(tree &&_other) : d_v_(std::move(_other.d_v_)) {}

    tree &operator=(const tree &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    tree &operator=(tree &&_other) {
      d_v_ = std::move(_other.d_v_);
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
          _dst->d_v_ = Leaf();
        } else {
          const auto &_alt = std::get<Node>(_src->v());
          _dst->d_v_ =
              Node(_alt.d_a0 ? std::make_unique<tree>() : nullptr, _alt.d_a1,
                   _alt.d_a2 ? std::make_unique<tree>() : nullptr);
          auto &_dst_alt = std::get<Node>(_dst->d_v_);
          if (_alt.d_a0) {
            _stack.push_back({_alt.d_a0.get(), _dst_alt.d_a0.get()});
          }
          if (_alt.d_a2) {
            _stack.push_back({_alt.d_a2.get(), _dst_alt.d_a2.get()});
          }
        }
      }
      return _out;
    }

    // CREATORS
    static tree leaf() { return tree(Leaf()); }

    static tree node(tree a0, unsigned int a1, tree a2) {
      return tree(Node(std::make_unique<tree>(std::move(a0)), std::move(a1),
                       std::make_unique<tree>(std::move(a2))));
    }

    // MANIPULATORS
    ~tree() {
      std::vector<std::unique_ptr<tree>> _stack{};
      _stack.reserve(8);
      auto _drain = [&](tree &_node) {
        if (std::holds_alternative<Node>(_node.d_v_)) {
          auto &_alt = std::get<Node>(_node.d_v_);
          if (_alt.d_a0) {
            _stack.push_back(std::move(_alt.d_a0));
          }
          if (_alt.d_a2) {
            _stack.push_back(std::move(_alt.d_a2));
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

    inline variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    const variant_t &v() const { return d_v_; }

    /// TEST 6: Function that matches on a tree AND returns a closure
    /// that RETURNS A TREE. Tests capture of value types in returned
    /// closures where the return type contains unique_ptr.
    tree tree_transformer(const unsigned int n) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename tree::Leaf>(_sv.v())) {
        return tree::node(tree::leaf(), n, tree::leaf());
      } else {
        const auto &[d_a0, d_a1, d_a2] = std::get<typename tree::Node>(_sv.v());
        return tree::node(*(d_a0), (d_a1 + n), *(d_a2));
      }
    }

    /// TEST 4: Closure capturing pattern variables from a NESTED match.
    /// The outer match destructs a tree, the inner match destructs a list.
    /// Tests pre-copy across nested match scopes.
    unsigned int nested_capture(const mylist<unsigned int> &l,
                                const unsigned int n) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename tree::Leaf>(_sv.v())) {
        return n;
      } else {
        const auto &[d_a0, d_a1, d_a2] = std::get<typename tree::Node>(_sv.v());
        if (std::holds_alternative<typename mylist<unsigned int>::Mynil>(
                l.v())) {
          return (d_a1 + n);
        } else {
          const auto &[d_a00, d_a10] =
              std::get<typename mylist<unsigned int>::Mycons>(l.v());
          return (
              ((((*(d_a0)).tree_sum() + (*(d_a2)).tree_sum()) + d_a00) + d_a1) +
              n);
        }
      }
    }

    unsigned int tree_depth() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename tree::Leaf>(_sv.v())) {
        return 0u;
      } else {
        const auto &[d_a0, d_a1, d_a2] = std::get<typename tree::Node>(_sv.v());
        unsigned int dl = (*(d_a0)).tree_depth();
        unsigned int dr = (*(d_a2)).tree_depth();
        return (1u + (dl <= dr ? dr : dl));
      }
    }

    unsigned int tree_sum() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename tree::Leaf>(_sv.v())) {
        return 0u;
      } else {
        const auto &[d_a0, d_a1, d_a2] = std::get<typename tree::Node>(_sv.v());
        return (((*(d_a0)).tree_sum() + d_a1) + (*(d_a2)).tree_sum());
      }
    }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, tree &, T1 &, unsigned int &,
                                     tree &, T1 &>
    T1 tree_rec(const T1 f, F1 &&f0) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename tree::Leaf>(_sv.v())) {
        return f;
      } else {
        const auto &[d_a0, d_a1, d_a2] = std::get<typename tree::Node>(_sv.v());
        return f0(*(d_a0), (*(d_a0)).template tree_rec<T1>(f, f0), d_a1,
                  *(d_a2), (*(d_a2)).template tree_rec<T1>(f, f0));
      }
    }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, tree &, T1 &, unsigned int &,
                                     tree &, T1 &>
    T1 tree_rect(const T1 f, F1 &&f0) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename tree::Leaf>(_sv.v())) {
        return f;
      } else {
        const auto &[d_a0, d_a1, d_a2] = std::get<typename tree::Node>(_sv.v());
        return f0(*(d_a0), (*(d_a0)).template tree_rect<T1>(f, f0), d_a1,
                  *(d_a2), (*(d_a2)).template tree_rect<T1>(f, f0));
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
  dual_accum(const mylist<unsigned int> &l, const unsigned int sum_acc,
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
