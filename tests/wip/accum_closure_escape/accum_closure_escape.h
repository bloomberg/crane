#ifndef INCLUDED_ACCUM_CLOSURE_ESCAPE
#define INCLUDED_ACCUM_CLOSURE_ESCAPE

#include <functional>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

struct AccumClosureEscape {
  /// This test explores closure escape through ACCUMULATOR patterns,
  /// which are different from the direct-return-in-constructor pattern
  /// tested by the other wip tests.
  ///
  /// Key difference: closures are built up in an accumulator during
  /// recursion. Each recursive step adds a new closure to a list.
  /// The closures capture pattern variables from the current match
  /// scope, which may be references into shared_ptr nodes.
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

    mylist<A> mylist_append(mylist<A> l2) const {
      if (std::holds_alternative<typename mylist<A>::Mynil>(this->v())) {
        return l2;
      } else {
        const auto &[a0, a1] = std::get<typename mylist<A>::Mycons>(this->v());
        return mylist<A>::mycons(a0, (*a1).mylist_append(std::move(l2)));
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

  /// A simple tree for supplying values.
  struct tree {
    // TYPES
    struct TLeaf {};

    struct TNode {
      std::unique_ptr<tree> a0;
      uint64_t a1;
      std::unique_ptr<tree> a2;
    };

    using variant_t = std::variant<TLeaf, TNode>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    tree() {}

    explicit tree(TLeaf _v) : v_(_v) {}

    explicit tree(TNode _v) : v_(std::move(_v)) {}

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
        if (std::holds_alternative<TLeaf>(_src->v())) {
          _dst->v_ = TLeaf{};
        } else {
          const auto &_alt = std::get<TNode>(_src->v());
          _dst->v_ =
              TNode{_alt.a0 ? std::make_unique<tree>() : nullptr, _alt.a1,
                    _alt.a2 ? std::make_unique<tree>() : nullptr};
          auto &_dst_alt = std::get<TNode>(_dst->v_);
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
    static tree tleaf() { return tree(TLeaf{}); }

    static tree tnode(tree a0, uint64_t a1, tree a2) {
      return tree(TNode{std::make_unique<tree>(std::move(a0)), a1,
                        std::make_unique<tree>(std::move(a2))});
    }

    // MANIPULATORS
    ~tree() {
      std::vector<std::unique_ptr<tree>> _stack{};
      _stack.reserve(8);
      auto _drain = [&](tree &_node) {
        if (std::holds_alternative<TNode>(_node.v_)) {
          auto &_alt = std::get<TNode>(_node.v_);
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

    /// Build closures from TREE traversal: tree nodes become closures.
    /// Each closure captures pattern variables from tree match.
    mylist<std::function<uint64_t(uint64_t)>> tree_to_adders() const {
      if (std::holds_alternative<typename tree::TLeaf>(this->v())) {
        return mylist<std::function<uint64_t(uint64_t)>>::mynil();
      } else {
        const auto &[a0, a1, a2] = std::get<typename tree::TNode>(this->v());
        const tree &a0_value = *a0;
        const tree &a2_value = *a2;
        return mylist<std::function<uint64_t(uint64_t)>>::mycons(
            [=](uint64_t x) mutable { return (a1 + x); },
            a0_value.tree_to_adders().mylist_append(a2_value.tree_to_adders()));
      }
    }

    mylist<uint64_t> tree_to_list() const {
      if (std::holds_alternative<typename tree::TLeaf>(this->v())) {
        return mylist<uint64_t>::mynil();
      } else {
        const auto &[a0, a1, a2] = std::get<typename tree::TNode>(this->v());
        return mylist<uint64_t>::mycons(
            a1, (*a0).tree_to_list().mylist_append((*a2).tree_to_list()));
      }
    }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, tree &, T1 &, uint64_t &, tree &,
                                     T1 &>
    T1 tree_rec(T1 f, F1 &&f0) const {
      if (std::holds_alternative<typename tree::TLeaf>(this->v())) {
        return f;
      } else {
        const auto &[a0, a1, a2] = std::get<typename tree::TNode>(this->v());
        return f0(*a0, (*a0).template tree_rec<T1>(f, f0), a1, *a2,
                  (*a2).template tree_rec<T1>(f, f0));
      }
    }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, tree &, T1 &, uint64_t &, tree &,
                                     T1 &>
    T1 tree_rect(T1 f, F1 &&f0) const {
      if (std::holds_alternative<typename tree::TLeaf>(this->v())) {
        return f;
      } else {
        const auto &[a0, a1, a2] = std::get<typename tree::TNode>(this->v());
        return f0(*a0, (*a0).template tree_rect<T1>(f, f0), a1, *a2,
                  (*a2).template tree_rect<T1>(f, f0));
      }
    }
  };

  /// Fold-left that builds a closure from each element.
  ///
  /// SIMPLE LAMBDA VERSION: Each closure fun x => h + x captures
  /// h from the pattern match. These are simple lambdas, so they
  /// should capture by =.
  static mylist<std::function<uint64_t(uint64_t)>>
  build_adders(const mylist<uint64_t> &l,
               mylist<std::function<uint64_t(uint64_t)>> acc);
  /// Apply first closure from the list.
  static uint64_t
  apply_first(const mylist<std::function<uint64_t(uint64_t)>> &fns, uint64_t x);
  /// Apply all closures and sum.
  static uint64_t
  apply_all_sum(const mylist<std::function<uint64_t(uint64_t)>> &fns,
                uint64_t x);
  /// test1: build_adders 10, 20, 30  = 30+_, 20+_, 10+_ (reversed)
  /// apply_first result 5 = 30 + 5 = 35
  static inline const uint64_t test1 = []() {
    mylist<std::function<uint64_t(uint64_t)>> fns = build_adders(
        mylist<uint64_t>::mycons(
            UINT64_C(10),
            mylist<uint64_t>::mycons(
                UINT64_C(20), mylist<uint64_t>::mycons(
                                  UINT64_C(30), mylist<uint64_t>::mynil()))),
        mylist<std::function<uint64_t(uint64_t)>>::mynil());
    return apply_first(std::move(fns), UINT64_C(5));
  }();
  /// test2: apply all closures: (30+5) + (20+5) + (10+5) = 35+25+15 = 75
  static inline const uint64_t test2 = []() {
    mylist<std::function<uint64_t(uint64_t)>> fns = build_adders(
        mylist<uint64_t>::mycons(
            UINT64_C(10),
            mylist<uint64_t>::mycons(
                UINT64_C(20), mylist<uint64_t>::mycons(
                                  UINT64_C(30), mylist<uint64_t>::mynil()))),
        mylist<std::function<uint64_t(uint64_t)>>::mynil());
    return apply_all_sum(std::move(fns), UINT64_C(5));
  }();

  /// COMPOSE CLOSURES: Each step builds a composed function.
  /// This creates closures that capture OTHER closures.
  static uint64_t compose_from_list(const mylist<uint64_t> &l,
                                    std::function<uint64_t(uint64_t)> acc,
                                    uint64_t _x0) {
    return [=]() mutable -> std::function<uint64_t(uint64_t)> {
      if (std::holds_alternative<typename mylist<uint64_t>::Mynil>(l.v())) {
        return acc;
      } else {
        const auto &[a0, a1] =
            std::get<typename mylist<uint64_t>::Mycons>(l.v());
        const mylist<uint64_t> &a1_value = *a1;
        return [=](uint64_t _x0) mutable -> uint64_t {
          return compose_from_list(
              a1_value, [=](uint64_t x) mutable { return acc((a0 + x)); }, _x0);
        };
      }
    }()(_x0);
  }

  /// test3: compose_from_list 10, 20, 30 id
  /// = fun x => id (10 + (20 + (30 + x)))
  /// = fun x => 60 + x
  /// test3 = 60 + 7 = 67
  static inline const uint64_t test3 = compose_from_list(
      mylist<uint64_t>::mycons(
          UINT64_C(10),
          mylist<uint64_t>::mycons(
              UINT64_C(20), mylist<uint64_t>::mycons(
                                UINT64_C(30), mylist<uint64_t>::mynil()))),
      [](uint64_t x) { return x; }, UINT64_C(7));
  /// test4: Tree (Node (Node Leaf 10 Leaf) 20 (Node Leaf 30 Leaf))
  /// Closures: 20+_, 10+_, 30+_
  /// apply_all_sum with 5: (20+5) + (10+5) + (30+5) = 25+15+35 = 75
  static inline const uint64_t test4 = []() {
    tree t = tree::tnode(
        tree::tnode(tree::tleaf(), UINT64_C(10), tree::tleaf()), UINT64_C(20),
        tree::tnode(tree::tleaf(), UINT64_C(30), tree::tleaf()));
    return apply_all_sum(std::move(t).tree_to_adders(), UINT64_C(5));
  }();
  /// Store a closure and then clobber the stack before using it.
  static inline const uint64_t test5 = []() {
    tree t =
        tree::tnode(tree::tnode(tree::tleaf(), UINT64_C(42), tree::tleaf()),
                    UINT64_C(100), tree::tleaf());
    mylist<std::function<uint64_t(uint64_t)>> fns =
        std::move(t).tree_to_adders();
    return apply_first(std::move(fns), UINT64_C(0));
  }();
};

#endif // INCLUDED_ACCUM_CLOSURE_ESCAPE
