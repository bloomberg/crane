#ifndef INCLUDED_MEM_SAFETY_PROBE28
#define INCLUDED_MEM_SAFETY_PROBE28

#include <algorithm>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

template <typename t_A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    t_A d_a0;
    std::unique_ptr<List<t_A>> d_a1;
  };

  using variant_t = std::variant<Nil, Cons>;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  List() {}

  explicit List(Nil _v) : d_v_(_v) {}

  explicit List(Cons _v) : d_v_(std::move(_v)) {}

  List(const List<t_A> &_other) : d_v_(std::move(_other.clone().d_v_)) {}

  List(List<t_A> &&_other) : d_v_(std::move(_other.d_v_)) {}

  List<t_A> &operator=(const List<t_A> &_other) {
    d_v_ = std::move(_other.clone().d_v_);
    return *this;
  }

  List<t_A> &operator=(List<t_A> &&_other) {
    d_v_ = std::move(_other.d_v_);
    return *this;
  }

  // ACCESSORS
  List<t_A> clone() const {
    List<t_A> _out{};

    struct _CloneFrame {
      const List<t_A> *_src;
      List<t_A> *_dst;
    };

    std::vector<_CloneFrame> _stack{};
    _stack.reserve(8);
    _stack.push_back({this, &_out});
    while (!_stack.empty()) {
      auto _frame = _stack.back();
      _stack.pop_back();
      const List<t_A> *_src = _frame._src;
      List<t_A> *_dst = _frame._dst;
      if (std::holds_alternative<Nil>(_src->v())) {
        _dst->d_v_ = Nil{};
      } else {
        const auto &_alt = std::get<Cons>(_src->v());
        _dst->d_v_ = Cons{_alt.d_a0,
                          _alt.d_a1 ? std::make_unique<List<t_A>>() : nullptr};
        auto &_dst_alt = std::get<Cons>(_dst->d_v_);
        if (_alt.d_a1) {
          _stack.push_back({_alt.d_a1.get(), _dst_alt.d_a1.get()});
        }
      }
    }
    return _out;
  }

  // CREATORS
  template <typename _U> explicit List(const List<_U> &_other) {
    if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
      this->d_v_ = Nil{};
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<_U>::Cons>(_other.v());
      this->d_v_ =
          Cons{t_A(d_a0), d_a1 ? std::make_unique<List<t_A>>(*d_a1) : nullptr};
    }
  }

  static List<t_A> nil() { return List(Nil{}); }

  static List<t_A> cons(t_A a0, List<t_A> a1) {
    return List(
        Cons{std::move(a0), std::make_unique<List<t_A>>(std::move(a1))});
  }

  // MANIPULATORS
  ~List() {
    std::vector<std::unique_ptr<List<t_A>>> _stack{};
    _stack.reserve(8);
    auto _drain = [&](List<t_A> &_node) {
      if (std::holds_alternative<Cons>(_node.d_v_)) {
        auto &_alt = std::get<Cons>(_node.d_v_);
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
};

struct MemSafetyProbe28 {
  /// Probe 28: Move optimization in loopified code.
  ///
  /// Attack vector: The flatten optimization (make_owned_param_matches +
  /// optimize_frame_push_args) moves *(d_child) into _Enter frames when
  /// the parameter is non-pointer-safe. A function with TWO tree params
  /// where t1 is the structural argument and t2 varies non-structurally
  /// makes t2 NOT pointer-safe. If t2's children are moved via the
  /// optimization but t2 is also used non-recursively (e.g. tree_sum t2),
  /// the _After frame references corrupted data.
  ///
  /// Key insight: Coq's structural recursion guarantees that single-tree
  /// recursion always passes CPPderef sub-terms, making the param
  /// pointer-safe. Two-param functions break this when the non-structural
  /// param varies non-uniformly.
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
          _dst->d_v_ = Leaf{};
        } else {
          const auto &_alt = std::get<Node>(_src->v());
          _dst->d_v_ =
              Node{_alt.d_a0 ? std::make_unique<tree>() : nullptr, _alt.d_a1,
                   _alt.d_a2 ? std::make_unique<tree>() : nullptr};
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
    static tree leaf() { return tree(Leaf{}); }

    static tree node(tree a0, unsigned int a1, tree a2) {
      return tree(Node{std::make_unique<tree>(std::move(a0)), std::move(a1),
                       std::make_unique<tree>(std::move(a2))});
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
  };

  template <typename T1, typename F1>
    requires std::is_invocable_r_v<T1, F1 &, tree &, T1 &, unsigned int &,
                                   tree &, T1 &>
  static T1 tree_rect(const T1 f, F1 &&f0, const tree &t) {
    if (std::holds_alternative<typename tree::Leaf>(t.v())) {
      return f;
    } else {
      const auto &[d_a0, d_a1, d_a2] = std::get<typename tree::Node>(t.v());
      return f0(*(d_a0), tree_rect<T1>(f, f0, *(d_a0)), d_a1, *(d_a2),
                tree_rect<T1>(f, f0, *(d_a2)));
    }
  }

  template <typename T1, typename F1>
    requires std::is_invocable_r_v<T1, F1 &, tree &, T1 &, unsigned int &,
                                   tree &, T1 &>
  static T1 tree_rec(const T1 f, F1 &&f0, const tree &t) {
    if (std::holds_alternative<typename tree::Leaf>(t.v())) {
      return f;
    } else {
      const auto &[d_a0, d_a1, d_a2] = std::get<typename tree::Node>(t.v());
      return f0(*(d_a0), tree_rec<T1>(f, f0, *(d_a0)), d_a1, *(d_a2),
                tree_rec<T1>(f, f0, *(d_a2)));
    }
  }

  static unsigned int tree_sum(const tree &t);
  static unsigned int tree_depth(const tree &t);
  /// TEST 1: zip_trees - Two tree params, t1 structural, t2 non-structural.
  /// t2 is NOT pointer-safe because some calls pass Leaf (not CPPderef).
  /// In the Node/Node branch, t2's children are used for recursion AND
  /// tree_sum t2 uses the whole tree. If the optimization moves *(l2),
  /// tree_sum t2 might see corrupted data.
  static unsigned int zip_trees(const tree &t1, const tree &t2);
  static inline const unsigned int test_zip_trees =
      zip_trees(tree::node(tree::node(tree::leaf(), 1u, tree::leaf()), 2u,
                           tree::node(tree::leaf(), 3u, tree::leaf())),
                tree::node(tree::node(tree::leaf(), 10u, tree::leaf()), 20u,
                           tree::node(tree::leaf(), 30u, tree::leaf())));
  /// TEST 2: zip_depth - Similar but uses tree_depth on t2.
  /// Tests a different tree traversal on the non-pointer-safe param.
  static unsigned int zip_depth(const tree &t1, const tree &t2);
  static inline const unsigned int test_zip_depth =
      zip_depth(tree::node(tree::node(tree::leaf(), 1u, tree::leaf()), 2u,
                           tree::node(tree::leaf(), 3u, tree::leaf())),
                tree::node(tree::node(tree::leaf(), 10u, tree::leaf()), 20u,
                           tree::node(tree::leaf(), 30u, tree::leaf())));
  /// TEST 3: zip_and_build - Recurse and also construct using t2's children.
  /// t2's left child is used for recursion AND returned as part of result.
  static unsigned int zip_and_sum(const tree &t1, const tree &t2);
  static inline const unsigned int test_zip_and_sum =
      zip_and_sum(tree::node(tree::leaf(), 5u, tree::leaf()),
                  tree::node(tree::node(tree::leaf(), 10u, tree::leaf()), 20u,
                             tree::node(tree::leaf(), 30u, tree::leaf())));
  /// TEST 4: double_zip - Both t1 and t2 are trees, but t2 is used
  /// in a different way for each call. Makes t2 non-pointer-safe.
  static unsigned int double_zip(const tree &t1, const tree &t2);
  static inline const unsigned int test_double_zip =
      double_zip(tree::node(tree::node(tree::leaf(), 1u, tree::leaf()), 2u,
                            tree::node(tree::leaf(), 3u, tree::leaf())),
                 tree::node(tree::leaf(), 10u, tree::leaf()));
  /// TEST 5: zip with list accumulator. t2 is tree, acc is list.
  /// t2 non-pointer-safe due to Leaf in some calls.
  static List<unsigned int> zip_collect(const tree &t1, const tree &t2,
                                        List<unsigned int> acc);
  static unsigned int list_sum(const List<unsigned int> &l);
  static inline const unsigned int test_zip_collect = list_sum(zip_collect(
      tree::node(tree::leaf(), 5u, tree::leaf()),
      tree::node(tree::leaf(), 10u, tree::leaf()), List<unsigned int>::nil()));
  /// TEST 6: Three-way recursion with non-pointer-safe second tree.
  static tree merge_trees(const tree &t1, tree t2);
  static inline const unsigned int test_merge_trees =
      tree_sum(merge_trees(tree::node(tree::leaf(), 5u, tree::leaf()),
                           tree::node(tree::leaf(), 10u, tree::leaf())));
  /// TEST 7: Deep trees to stress the optimization.
  static tree build_balanced(const unsigned int n);
  static inline const unsigned int test_deep_zip =
      zip_trees(build_balanced(5u), build_balanced(5u));
  /// TEST 8: Nested zip where result of one zip feeds into another.
  static inline const unsigned int test_nested_zip = []() {
    tree t1 = tree::node(tree::node(tree::leaf(), 1u, tree::leaf()), 2u,
                         tree::node(tree::leaf(), 3u, tree::leaf()));
    tree t2 = tree::node(tree::node(tree::leaf(), 10u, tree::leaf()), 20u,
                         tree::node(tree::leaf(), 30u, tree::leaf()));
    return (zip_trees(t1, t2) + zip_depth(t1, t2));
  }();
};

#endif // INCLUDED_MEM_SAFETY_PROBE28
