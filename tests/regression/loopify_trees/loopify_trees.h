#ifndef INCLUDED_LOOPIFY_TREES
#define INCLUDED_LOOPIFY_TREES

#include <any>
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

  List<A> app(List<A> m) const {
    if (std::holds_alternative<typename List<A>::Nil>(this->v())) {
      return m;
    } else {
      const auto &[a0, a1] = std::get<typename List<A>::Cons>(this->v());
      return List<A>::cons(a0, a1->app(std::move(m)));
    }
  }
};

/// Consolidated UNIQUE tree algorithms - domain-specific tree operations.
struct LoopifyTrees {
  template <typename A> struct tree {
    // TYPES
    struct Leaf {};

    struct Node {
      std::shared_ptr<tree<A>> l;
      A x;
      std::shared_ptr<tree<A>> r;
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

    template <typename _U> explicit tree(const tree<_U> &_other) {
      if (std::holds_alternative<typename tree<_U>::Leaf>(_other.v())) {
        this->v_ = Leaf{};
      } else {
        const auto &[l, x, r] = std::get<typename tree<_U>::Node>(_other.v());
        this->v_ = Node{
            l ? std::make_shared<tree<A>>(*l) : nullptr,
            [&]() -> A {
              if constexpr (std::is_same_v<_U, std::any>) {
                if (x.type() == typeid(A))
                  return std::any_cast<A>(x);
                if constexpr (requires {
                                typename A::first_type;
                                typename A::second_type;
                              }) {
                  const auto &[_k, _v] =
                      std::any_cast<std::pair<std::any, std::any>>(x);
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
                return std::any_cast<A>(x);
              } else
                return A(x);
            }(),
            r ? std::make_shared<tree<A>>(*r) : nullptr};
      }
    }

    static tree<A> leaf() { return tree(Leaf{}); }

    static tree<A> node(tree<A> l, A x, tree<A> r) {
      return tree(Node{std::make_shared<tree<A>>(std::move(l)), std::move(x),
                       std::make_shared<tree<A>>(std::move(r))});
    }

    // MANIPULATORS
    ~tree() {
      std::vector<std::shared_ptr<tree<A>>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<Node>(&_v)) {
          if (_alt->l) {
            _stack.push_back(std::move(_alt->l));
          }
          if (_alt->r) {
            _stack.push_back(std::move(_alt->r));
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

    /// tree_map f t applies f to all values in tree.
    template <typename T1, typename F0>
      requires std::is_invocable_r_v<T1, F0 &, A &>
    tree<T1> tree_map(F0 &&f) const {
      if (std::holds_alternative<typename tree<A>::Leaf>(this->v())) {
        return tree<T1>::leaf();
      } else {
        const auto &[a0, a1, a2] = std::get<typename tree<A>::Node>(this->v());
        return tree<T1>::node(a0->template tree_map<T1>(f), f(a1),
                              a2->template tree_map<T1>(f));
      }
    }

    /// mirror_equal t1 t2 checks if t1 and t2 are mirror images.
    bool mirror_equal(const tree<A> &t2) const {
      if (std::holds_alternative<typename tree<A>::Leaf>(this->v())) {
        if (std::holds_alternative<typename tree<A>::Leaf>(t2.v())) {
          return true;
        } else {
          return false;
        }
      } else {
        const auto &[a0, a1, a2] = std::get<typename tree<A>::Node>(this->v());
        if (std::holds_alternative<typename tree<A>::Leaf>(t2.v())) {
          return false;
        } else {
          const auto &[a00, a10, a20] =
              std::get<typename tree<A>::Node>(t2.v());
          return ((a0->mirror_equal(*a20) && a2->mirror_equal(*a00)) && true);
        }
      }
    }

    /// tree_to_list inorder traversal.
    List<A> tree_to_list() const {
      if (std::holds_alternative<typename tree<A>::Leaf>(this->v())) {
        return List<A>::nil();
      } else {
        const auto &[a0, a1, a2] = std::get<typename tree<A>::Node>(this->v());
        return a0->tree_to_list().app(List<A>::cons(a1, a2->tree_to_list()));
      }
    }

    /// count_leaves counts leaf nodes.
    uint64_t count_leaves() const {
      if (std::holds_alternative<typename tree<A>::Leaf>(this->v())) {
        return UINT64_C(1);
      } else {
        const auto &[a0, a1, a2] = std::get<typename tree<A>::Node>(this->v());
        return (a0->count_leaves() + a2->count_leaves());
      }
    }

    A rightmost(A default0) const {
      if (std::holds_alternative<typename tree<A>::Leaf>(this->v())) {
        return default0;
      } else {
        const auto &[a0, a1, a2] = std::get<typename tree<A>::Node>(this->v());
        auto &&_sv = *a2;
        if (std::holds_alternative<typename tree<A>::Leaf>(_sv.v())) {
          return a1;
        } else {
          return a2->rightmost(default0);
        }
      }
    }

    /// leftmost/rightmost finds edge values.
    A leftmost(A default0) const {
      if (std::holds_alternative<typename tree<A>::Leaf>(this->v())) {
        return default0;
      } else {
        const auto &[a0, a1, a2] = std::get<typename tree<A>::Node>(this->v());
        auto &&_sv = *a0;
        if (std::holds_alternative<typename tree<A>::Leaf>(_sv.v())) {
          return a1;
        } else {
          return a0->leftmost(default0);
        }
      }
    }

    /// same_shape tests structural equality.
    template <typename T1> bool same_shape(const tree<T1> &t2) const {
      if (std::holds_alternative<typename tree<A>::Leaf>(this->v())) {
        if (std::holds_alternative<typename tree<T1>::Leaf>(t2.v())) {
          return true;
        } else {
          return false;
        }
      } else {
        const auto &[a0, a1, a2] = std::get<typename tree<A>::Node>(this->v());
        if (std::holds_alternative<typename tree<T1>::Leaf>(t2.v())) {
          return false;
        } else {
          const auto &[a00, a10, a20] =
              std::get<typename tree<T1>::Node>(t2.v());
          if (a0->template same_shape<T1>(*a00)) {
            return a2->template same_shape<T1>(*a20);
          } else {
            return false;
          }
        }
      }
    }

    tree<A> mirror() const {
      if (std::holds_alternative<typename tree<A>::Leaf>(this->v())) {
        return tree<A>::leaf();
      } else {
        const auto &[a0, a1, a2] = std::get<typename tree<A>::Node>(this->v());
        return tree<A>::node(a2->mirror(), a1, a0->mirror());
      }
    }

    uint64_t tree_size() const {
      if (std::holds_alternative<typename tree<A>::Leaf>(this->v())) {
        return UINT64_C(0);
      } else {
        const auto &[a0, a1, a2] = std::get<typename tree<A>::Node>(this->v());
        return ((a0->tree_size() + a2->tree_size()) + 1);
      }
    }

    uint64_t tree_height() const {
      if (std::holds_alternative<typename tree<A>::Leaf>(this->v())) {
        return UINT64_C(0);
      } else {
        const auto &[a0, a1, a2] = std::get<typename tree<A>::Node>(this->v());
        uint64_t lh = a0->tree_height();
        uint64_t rh = a2->tree_height();
        return ((lh <= rh ? rh : lh) + 1);
      }
    }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, tree<A> &, T1 &, A &, tree<A> &,
                                     T1 &>
    T1 tree_rec(T1 f, F1 &&f0) const {
      if (std::holds_alternative<typename tree<A>::Leaf>(this->v())) {
        return f;
      } else {
        const auto &[a0, a1, a2] = std::get<typename tree<A>::Node>(this->v());
        return f0(*a0, a0->template tree_rec<T1>(f, f0), a1, *a2,
                  a2->template tree_rec<T1>(f, f0));
      }
    }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, tree<A> &, T1 &, A &, tree<A> &,
                                     T1 &>
    T1 tree_rect(T1 f, F1 &&f0) const {
      if (std::holds_alternative<typename tree<A>::Leaf>(this->v())) {
        return f;
      } else {
        const auto &[a0, a1, a2] = std::get<typename tree<A>::Node>(this->v());
        return f0(*a0, a0->template tree_rect<T1>(f, f0), a1, *a2,
                  a2->template tree_rect<T1>(f, f0));
      }
    }
  };

  static uint64_t tree_sum(const tree<uint64_t> &t);
  /// leaf_sum sums only leaf values.
  static uint64_t leaf_sum(const tree<uint64_t> &t);
  /// insert_bst BST insertion.
  static tree<uint64_t> insert_bst(uint64_t x, const tree<uint64_t> &t);
  /// count_paths t n counts root-to-leaf paths that sum to n.
  static uint64_t count_paths(const tree<uint64_t> &t, uint64_t n);
  /// sum_of_max_branches sums maximum values along each path.
  static uint64_t sum_of_max_branches(const tree<uint64_t> &t);

  struct ternary {
    // TYPES
    struct TLeaf {};

    struct TNode {
      std::shared_ptr<ternary> a0;
      std::shared_ptr<ternary> a1;
      std::shared_ptr<ternary> a2;
      uint64_t a3;
    };

    using variant_t = std::variant<TLeaf, TNode>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    ternary() {}

    explicit ternary(TLeaf _v) : v_(_v) {}

    explicit ternary(TNode _v) : v_(std::move(_v)) {}

    static ternary tleaf() { return ternary(TLeaf{}); }

    static ternary tnode(ternary a0, ternary a1, ternary a2, uint64_t a3) {
      return ternary(TNode{std::make_shared<ternary>(std::move(a0)),
                           std::make_shared<ternary>(std::move(a1)),
                           std::make_shared<ternary>(std::move(a2)), a3});
    }

    // MANIPULATORS
    ~ternary() {
      std::vector<std::shared_ptr<ternary>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<TNode>(&_v)) {
          if (_alt->a0) {
            _stack.push_back(std::move(_alt->a0));
          }
          if (_alt->a1) {
            _stack.push_back(std::move(_alt->a1));
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

    uint64_t ternary_depth() const {
      if (std::holds_alternative<typename ternary::TLeaf>(this->v())) {
        return UINT64_C(0);
      } else {
        const auto &[a0, a1, a2, a3] =
            std::get<typename ternary::TNode>(this->v());
        uint64_t d1 = a0->ternary_depth();
        uint64_t d2 = a1->ternary_depth();
        uint64_t d3 = a2->ternary_depth();
        return ([&]() -> uint64_t {
          if ((d1 <= d2 ? d2 : d1) <= d3) {
            return d3;
          } else {
            if (d1 <= d2) {
              return d2;
            } else {
              return d1;
            }
          }
        }() + 1);
      }
    }

    uint64_t ternary_sum() const {
      if (std::holds_alternative<typename ternary::TLeaf>(this->v())) {
        return UINT64_C(0);
      } else {
        const auto &[a0, a1, a2, a3] =
            std::get<typename ternary::TNode>(this->v());
        return (a3 +
                (a0->ternary_sum() + (a1->ternary_sum() + a2->ternary_sum())));
      }
    }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, ternary &, T1 &, ternary &, T1 &,
                                     ternary &, T1 &, uint64_t &>
    T1 ternary_rec(T1 f, F1 &&f0) const {
      if (std::holds_alternative<typename ternary::TLeaf>(this->v())) {
        return f;
      } else {
        const auto &[a0, a1, a2, a3] =
            std::get<typename ternary::TNode>(this->v());
        return f0(*a0, a0->template ternary_rec<T1>(f, f0), *a1,
                  a1->template ternary_rec<T1>(f, f0), *a2,
                  a2->template ternary_rec<T1>(f, f0), a3);
      }
    }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, ternary &, T1 &, ternary &, T1 &,
                                     ternary &, T1 &, uint64_t &>
    T1 ternary_rect(T1 f, F1 &&f0) const {
      if (std::holds_alternative<typename ternary::TLeaf>(this->v())) {
        return f;
      } else {
        const auto &[a0, a1, a2, a3] =
            std::get<typename ternary::TNode>(this->v());
        return f0(*a0, a0->template ternary_rect<T1>(f, f0), *a1,
                  a1->template ternary_rect<T1>(f, f0), *a2,
                  a2->template ternary_rect<T1>(f, f0), a3);
      }
    }
  };

  /// Rose tree: a tree with variable number of children.
  struct rose {
    // TYPES
    struct RNode {
      uint64_t a0;
      std::shared_ptr<List<rose>> a1;
    };

    using variant_t = std::variant<RNode>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    rose() {}

    explicit rose(RNode _v) : v_(std::move(_v)) {}

    static rose rnode(uint64_t a0, List<rose> a1) {
      return rose(RNode{a0, std::make_shared<List<rose>>(std::move(a1))});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    /// rose_depth t computes the depth of a rose tree.
    uint64_t rose_depth() const {
      const auto &[a0, a1] = std::get<typename rose::RNode>(this->v());
      return (depth_rose_list_fuel(UINT64_C(1000), *a1) + 1);
    }

    /// rose_flatten t flattens a rose tree to a list (pre-order).
    List<uint64_t> rose_flatten() const {
      const auto &[a0, a1] = std::get<typename rose::RNode>(this->v());
      return List<uint64_t>::cons(a0,
                                  flatten_rose_list_fuel(UINT64_C(1000), *a1));
    }

    /// rose_map f t applies f to all values in a rose tree.
    template <typename F0>
      requires std::is_invocable_r_v<uint64_t, F0 &, uint64_t &>
    rose rose_map(F0 &&f) const {
      const auto &[a0, a1] = std::get<typename rose::RNode>(this->v());
      return rose::rnode(f(a0), map_rose_list_fuel(UINT64_C(1000), f, *a1));
    }

    /// rose_sum t sums all values in a rose tree.
    uint64_t rose_sum() const {
      const auto &[a0, a1] = std::get<typename rose::RNode>(this->v());
      return (a0 + sum_rose_list_fuel(UINT64_C(1000), *a1));
    }

    template <typename T1, typename F0>
      requires std::is_invocable_r_v<T1, F0 &, uint64_t &, List<rose> &>
    T1 rose_rec(F0 &&f) const {
      const auto &[a0, a1] = std::get<typename rose::RNode>(this->v());
      return f(a0, *a1);
    }

    template <typename T1, typename F0>
      requires std::is_invocable_r_v<T1, F0 &, uint64_t &, List<rose> &>
    T1 rose_rect(F0 &&f) const {
      const auto &[a0, a1] = std::get<typename rose::RNode>(this->v());
      return f(a0, *a1);
    }
  };

  /// Helper: sum all values in a list of rose trees (processes both tree and
  /// list levels in one recursive function to enable full loopification).
  static uint64_t sum_rose_list_fuel(uint64_t fuel, const List<rose> &cs);

  /// Helper: map function over all values in a list of rose trees.
  template <typename F1>
    requires std::is_invocable_r_v<uint64_t, F1 &, uint64_t &>
  static List<rose> map_rose_list_fuel(
      uint64_t fuel, F1 &&f,
      const List<rose> &
          cs) { /// _Enter: captures varying parameters for each recursive call.

    struct _Enter {
      const List<rose> *cs;
      uint64_t fuel;
    };

    /// _After_RNode: saves [a10, g, a00], dispatches next recursive call.
    struct _After_RNode {
      const List<rose> *a10;
      uint64_t g;
      uint64_t a00;
    };

    /// _Combine_RNode: receives partial results, combines with _result from
    /// final call.
    struct _Combine_RNode {
      List<rose> _result;
      uint64_t a00;
    };

    using _Frame = std::variant<_Enter, _After_RNode, _Combine_RNode>;
    List<rose> _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{&cs, fuel});
    /// Loopified map_rose_list_fuel: _Enter -> _After_RNode -> _Combine_RNode.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const List<rose> &cs = *_f.cs;
        uint64_t fuel = _f.fuel;
        if (fuel <= 0) {
          _result = List<rose>::nil();
        } else {
          uint64_t g = fuel - 1;
          if (std::holds_alternative<typename List<rose>::Nil>(cs.v())) {
            _result = List<rose>::nil();
          } else {
            const auto &[a0, a1] = std::get<typename List<rose>::Cons>(cs.v());
            const auto &[a00, a10] = std::get<typename rose::RNode>(a0.v());
            _stack.emplace_back(_After_RNode{a10.get(), g, f(a00)});
            _stack.emplace_back(_Enter{a1.get(), g});
          }
        }
      } else if (std::holds_alternative<_After_RNode>(_frame)) {
        auto _f = std::move(std::get<_After_RNode>(_frame));
        _stack.emplace_back(_Combine_RNode{std::move(_result), _f.a00});
        _stack.emplace_back(_Enter{_f.a10, _f.g});
      } else {
        auto _f = std::move(std::get<_Combine_RNode>(_frame));
        _result = List<rose>::cons(rose::rnode(_f.a00, std::move(_result)),
                                   std::move(_f._result));
      }
    }
    return _result;
  }

  /// Helper: flatten a list of rose trees to a flat list of nats.
  static List<uint64_t> flatten_rose_list_fuel(uint64_t fuel,
                                               const List<rose> &cs);
  /// Helper: compute maximum depth among a list of rose trees.
  static uint64_t depth_rose_list_fuel(uint64_t fuel, const List<rose> &cs);
  /// tree_max t1 t2 element-wise maximum of two trees.
  static tree<uint64_t> tree_max(tree<uint64_t> t1, tree<uint64_t> t2);
  /// Helper: extract values from trees.
  static List<uint64_t> extract_tree_values(const List<tree<uint64_t>> &ts);
  /// Helper: extract children from trees.
  static List<tree<uint64_t>>
  extract_tree_children(const List<tree<uint64_t>> &ts);
  /// tree_levels t returns list of lists, one per level (breadth-first).
  static List<List<uint64_t>>
  tree_levels_fuel(uint64_t fuel, const List<tree<uint64_t>> &trees);
  static List<List<uint64_t>> tree_levels(tree<uint64_t> t);
  /// count_nodes t returns tuple (node_count, sum_of_values).
  static std::pair<uint64_t, uint64_t> count_nodes(const tree<uint64_t> &t);
  /// Helper: append two lists of lists.
  static List<List<uint64_t>> append_list_lists(const List<List<uint64_t>> &l1,
                                                List<List<uint64_t>> l2);
  /// Helper: prepend value to all lists in a list of lists.
  static List<List<uint64_t>> map_cons_to_all(uint64_t x,
                                              const List<List<uint64_t>> &lsts);
  /// paths t returns all root-to-leaf paths in tree.
  static List<List<uint64_t>> paths(const tree<uint64_t> &t);
  /// collect_sorted t collects and sorts all tree values.
  static List<uint64_t> collect_unsorted(const tree<uint64_t> &t);
  /// Simple insertion sort for collect_sorted.
  static List<uint64_t> insert_sorted(uint64_t x, const List<uint64_t> &l);
  static List<uint64_t> sort_list(const List<uint64_t> &l);
  static List<uint64_t> collect_sorted(const tree<uint64_t> &t);

  /// or_search p t searches tree for element satisfying predicate.
  template <typename F0>
    requires std::is_invocable_r_v<bool, F0 &, uint64_t &>
  static bool
  or_search(F0 &&p,
            const tree<uint64_t> &t) { /// _Enter: captures varying parameters
                                       /// for each recursive call.

    struct _Enter {
      const tree<uint64_t> *t;
    };

    /// _After2: saves [a0], dispatches next recursive call.
    struct _After2 {
      const tree<uint64_t> *a0;
    };

    /// _Combine1: receives partial results, combines with _result from final
    /// call.
    struct _Combine1 {
      bool _result;
    };

    using _Frame = std::variant<_Enter, _After2, _Combine1>;
    bool _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{&t});
    /// Loopified or_search: _Enter -> _After2 -> _Combine1.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const tree<uint64_t> &t = *_f.t;
        if (std::holds_alternative<typename tree<uint64_t>::Leaf>(t.v())) {
          _result = false;
        } else {
          const auto &[a0, a1, a2] =
              std::get<typename tree<uint64_t>::Node>(t.v());
          if (p(a1)) {
            _result = true;
          } else {
            _stack.emplace_back(_After2{a0.get()});
            _stack.emplace_back(_Enter{a2.get()});
          }
        }
      } else if (std::holds_alternative<_After2>(_frame)) {
        auto _f = std::move(std::get<_After2>(_frame));
        _stack.emplace_back(_Combine1{std::move(_result)});
        _stack.emplace_back(_Enter{_f.a0});
      } else {
        auto _f = std::move(std::get<_Combine1>(_frame));
        _result = (std::move(_result) || std::move(_f._result));
      }
    }
    return _result;
  }

  struct quadtree {
    // TYPES
    struct QLeaf {
      uint64_t a0;
    };

    struct Quad {
      std::shared_ptr<quadtree> a0;
      std::shared_ptr<quadtree> a1;
      std::shared_ptr<quadtree> a2;
      std::shared_ptr<quadtree> a3;
    };

    using variant_t = std::variant<QLeaf, Quad>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    quadtree() {}

    explicit quadtree(QLeaf _v) : v_(std::move(_v)) {}

    explicit quadtree(Quad _v) : v_(std::move(_v)) {}

    static quadtree qleaf(uint64_t a0) { return quadtree(QLeaf{a0}); }

    static quadtree quad(quadtree a0, quadtree a1, quadtree a2, quadtree a3) {
      return quadtree(Quad{std::make_shared<quadtree>(std::move(a0)),
                           std::make_shared<quadtree>(std::move(a1)),
                           std::make_shared<quadtree>(std::move(a2)),
                           std::make_shared<quadtree>(std::move(a3))});
    }

    // MANIPULATORS
    ~quadtree() {
      std::vector<std::shared_ptr<quadtree>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<Quad>(&_v)) {
          if (_alt->a0) {
            _stack.push_back(std::move(_alt->a0));
          }
          if (_alt->a1) {
            _stack.push_back(std::move(_alt->a1));
          }
          if (_alt->a2) {
            _stack.push_back(std::move(_alt->a2));
          }
          if (_alt->a3) {
            _stack.push_back(std::move(_alt->a3));
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

    /// quad_depth t computes depth of quadtree.
    uint64_t quad_depth() const {
      if (std::holds_alternative<typename quadtree::QLeaf>(this->v())) {
        return UINT64_C(0);
      } else {
        const auto &[a0, a1, a2, a3] =
            std::get<typename quadtree::Quad>(this->v());
        return (max4_impl(a0->quad_depth(), a1->quad_depth(), a2->quad_depth(),
                          a3->quad_depth()) +
                1);
      }
    }

    /// quad_sum t sums all values in a quadtree.
    uint64_t quad_sum() const {
      if (std::holds_alternative<typename quadtree::QLeaf>(this->v())) {
        const auto &[a0] = std::get<typename quadtree::QLeaf>(this->v());
        return a0;
      } else {
        const auto &[a0, a1, a2, a3] =
            std::get<typename quadtree::Quad>(this->v());
        return (a0->quad_sum() +
                (a1->quad_sum() + (a2->quad_sum() + a3->quad_sum())));
      }
    }

    template <typename T1, typename F0, typename F1>
      requires std::is_invocable_r_v<T1, F0 &, uint64_t &> &&
               std::is_invocable_r_v<T1, F1 &, quadtree &, T1 &, quadtree &,
                                     T1 &, quadtree &, T1 &, quadtree &, T1 &>
    T1 quadtree_rec(F0 &&f, F1 &&f0) const {
      if (std::holds_alternative<typename quadtree::QLeaf>(this->v())) {
        const auto &[a0] = std::get<typename quadtree::QLeaf>(this->v());
        return f(a0);
      } else {
        const auto &[a0, a1, a2, a3] =
            std::get<typename quadtree::Quad>(this->v());
        return f0(*a0, a0->template quadtree_rec<T1>(f, f0), *a1,
                  a1->template quadtree_rec<T1>(f, f0), *a2,
                  a2->template quadtree_rec<T1>(f, f0), *a3,
                  a3->template quadtree_rec<T1>(f, f0));
      }
    }

    template <typename T1, typename F0, typename F1>
      requires std::is_invocable_r_v<T1, F0 &, uint64_t &> &&
               std::is_invocable_r_v<T1, F1 &, quadtree &, T1 &, quadtree &,
                                     T1 &, quadtree &, T1 &, quadtree &, T1 &>
    T1 quadtree_rect(F0 &&f, F1 &&f0) const {
      if (std::holds_alternative<typename quadtree::QLeaf>(this->v())) {
        const auto &[a0] = std::get<typename quadtree::QLeaf>(this->v());
        return f(a0);
      } else {
        const auto &[a0, a1, a2, a3] =
            std::get<typename quadtree::Quad>(this->v());
        return f0(*a0, a0->template quadtree_rect<T1>(f, f0), *a1,
                  a1->template quadtree_rect<T1>(f, f0), *a2,
                  a2->template quadtree_rect<T1>(f, f0), *a3,
                  a3->template quadtree_rect<T1>(f, f0));
      }
    }
  };

  /// Helper: max of 4 values using nested max.
  static uint64_t max4_impl(uint64_t a, uint64_t b, uint64_t c, uint64_t d);

  /// Simple binary tree with values only at leaves.
  struct simple_tree {
    // TYPES
    struct SLeaf {
      uint64_t a0;
    };

    struct SNode {
      std::shared_ptr<simple_tree> a0;
      std::shared_ptr<simple_tree> a1;
    };

    using variant_t = std::variant<SLeaf, SNode>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    simple_tree() {}

    explicit simple_tree(SLeaf _v) : v_(std::move(_v)) {}

    explicit simple_tree(SNode _v) : v_(std::move(_v)) {}

    static simple_tree sleaf(uint64_t a0) { return simple_tree(SLeaf{a0}); }

    static simple_tree snode(simple_tree a0, simple_tree a1) {
      return simple_tree(SNode{std::make_shared<simple_tree>(std::move(a0)),
                               std::make_shared<simple_tree>(std::move(a1))});
    }

    // MANIPULATORS
    ~simple_tree() {
      std::vector<std::shared_ptr<simple_tree>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<SNode>(&_v)) {
          if (_alt->a0) {
            _stack.push_back(std::move(_alt->a0));
          }
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

    /// count_paths_simple t n counts paths with sum n (simpler variant).
    uint64_t count_paths_simple(uint64_t n) const {
      if (std::holds_alternative<typename simple_tree::SLeaf>(this->v())) {
        const auto &[a0] = std::get<typename simple_tree::SLeaf>(this->v());
        if (a0 == n) {
          return UINT64_C(1);
        } else {
          return UINT64_C(0);
        }
      } else {
        const auto &[a0, a1] = std::get<typename simple_tree::SNode>(this->v());
        if (n <= UINT64_C(0)) {
          return UINT64_C(0);
        } else {
          return (a0->count_paths_simple(
                      (((n - UINT64_C(1)) > n ? 0 : (n - UINT64_C(1))))) +
                  a1->count_paths_simple(
                      (((n - UINT64_C(1)) > n ? 0 : (n - UINT64_C(1))))));
        }
      }
    }

    /// simple_tree_sum t sums all leaf values.
    uint64_t simple_tree_sum() const {
      if (std::holds_alternative<typename simple_tree::SLeaf>(this->v())) {
        const auto &[a0] = std::get<typename simple_tree::SLeaf>(this->v());
        return a0;
      } else {
        const auto &[a0, a1] = std::get<typename simple_tree::SNode>(this->v());
        return (a0->simple_tree_sum() + a1->simple_tree_sum());
      }
    }

    template <typename T1, typename F0, typename F1>
      requires std::is_invocable_r_v<T1, F0 &, uint64_t &> &&
               std::is_invocable_r_v<T1, F1 &, simple_tree &, T1 &,
                                     simple_tree &, T1 &>
    T1 simple_tree_rec(F0 &&f, F1 &&f0) const {
      if (std::holds_alternative<typename simple_tree::SLeaf>(this->v())) {
        const auto &[a0] = std::get<typename simple_tree::SLeaf>(this->v());
        return f(a0);
      } else {
        const auto &[a0, a1] = std::get<typename simple_tree::SNode>(this->v());
        return f0(*a0, a0->template simple_tree_rec<T1>(f, f0), *a1,
                  a1->template simple_tree_rec<T1>(f, f0));
      }
    }

    template <typename T1, typename F0, typename F1>
      requires std::is_invocable_r_v<T1, F0 &, uint64_t &> &&
               std::is_invocable_r_v<T1, F1 &, simple_tree &, T1 &,
                                     simple_tree &, T1 &>
    T1 simple_tree_rect(F0 &&f, F1 &&f0) const {
      if (std::holds_alternative<typename simple_tree::SLeaf>(this->v())) {
        const auto &[a0] = std::get<typename simple_tree::SLeaf>(this->v());
        return f(a0);
      } else {
        const auto &[a0, a1] = std::get<typename simple_tree::SNode>(this->v());
        return f0(*a0, a0->template simple_tree_rect<T1>(f, f0), *a1,
                  a1->template simple_tree_rect<T1>(f, f0));
      }
    }
  };

  /// Helper: compute minimum of three values.
  static uint64_t min3(uint64_t a, uint64_t b, uint64_t c);
  /// Helper: compute maximum of three values.
  static uint64_t max3(uint64_t a, uint64_t b, uint64_t c);
  /// tree_min_max t finds minimum and maximum values in tree.
  static std::pair<uint64_t, uint64_t> tree_min_max(const tree<uint64_t> &t);
  /// all_paths_sum t sums all root-to-leaf path sums.
  static uint64_t all_paths_sum(const tree<uint64_t> &t);
  /// tree_contains x t checks if value exists in tree.
  static bool tree_contains(uint64_t x, const tree<uint64_t> &t);
};

#endif // INCLUDED_LOOPIFY_TREES
