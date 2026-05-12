#ifndef INCLUDED_MEM_SAFETY_PROBE10
#define INCLUDED_MEM_SAFETY_PROBE10

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

    /// TEST 8: Closure returned from function, capturing a TREE value.
    /// The tree is a value type with unique_ptr self-references.
    /// Tests whether = capture correctly deep-copies the tree.
    unsigned int make_tree_summer(const unsigned int n) const {
      return ((*(this)).tree_sum() + n);
    }

    /// TEST 5: Closure capturing value from OUTER match,
    /// returned from INNER match. Tests nested match +
    /// capture interaction.
    unsigned int nested_match_closure(const bool b,
                                      const unsigned int n) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename tree::Leaf>(_sv.v())) {
        return n;
      } else {
        const auto &[d_a0, d_a1, d_a2] = std::get<typename tree::Node>(_sv.v());
        if (b) {
          return (((*(d_a0)).tree_sum() + d_a1) + n);
        } else {
          return (((*(d_a2)).tree_sum() + d_a1) + n);
        }
      }
    }

    /// TEST 1: Recursive function that returns a closure.
    /// Each level composes the closure from recursive results.
    /// After loopification, these closures are assigned to _result,
    /// not returned via Sreturn.
    unsigned int tree_to_adder(const unsigned int _x0) const {
      const tree *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const tree *_self;
      };

      using _Frame = std::variant<_Enter>;
      unsigned int _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(8);
      _stack.emplace_back(_Enter(_self));
      /// Loopified tree_to_adder: _Enter.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        auto _f = std::move(std::get<_Enter>(_frame));
        const tree *_self = _f._self;
        tree _self_val = *(_self);
        _result = [=]() mutable -> std::function<unsigned int(unsigned int)> {
          if (std::holds_alternative<typename tree::Leaf>(_self_val.v())) {
            return [](const unsigned int n) { return n; };
          } else {
            const auto &[d_a0, d_a1, d_a2] =
                std::get<typename tree::Node>(_self_val.v());
            tree d_a0_value = *(d_a0);
            tree d_a2_value = *(d_a2);
            std::function<unsigned int(unsigned int)> fl =
                [=](unsigned int _x0) mutable -> unsigned int {
              return d_a0_value.tree_to_adder(_x0);
            };
            std::function<unsigned int(unsigned int)> fr =
                [=](unsigned int _x0) mutable -> unsigned int {
              return d_a2_value.tree_to_adder(_x0);
            };
            return [=](const unsigned int n) mutable {
              return fl((d_a1 + fr(n)));
            };
          }
        }()(_x0);
      }
      return _result;
    }

    unsigned int tree_sum() const {
      const tree *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const tree *_self;
      };

      /// _After_Node: saves [_s0, d_a1], dispatches next recursive call.
      struct _After_Node {
        tree *_s0;
        unsigned int d_a1;
      };

      /// _Combine_Node: receives partial results, combines with _result from
      /// final call.
      struct _Combine_Node {
        unsigned int _result;
        unsigned int d_a1;
      };

      using _Frame = std::variant<_Enter, _After_Node, _Combine_Node>;
      unsigned int _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(8);
      _stack.emplace_back(_Enter(_self));
      /// Loopified tree_sum: _Enter -> _After_Node -> _Combine_Node.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const tree *_self = _f._self;
          auto &&_sv = *(_self);
          if (std::holds_alternative<typename tree::Leaf>(_sv.v())) {
            _result = 0u;
          } else {
            const auto &[d_a0, d_a1, d_a2] =
                std::get<typename tree::Node>(_sv.v());
            _stack.emplace_back(_After_Node(d_a0.get(), d_a1));
            _stack.emplace_back(_Enter(d_a2.get()));
          }
        } else if (std::holds_alternative<_After_Node>(_frame)) {
          auto _f = std::move(std::get<_After_Node>(_frame));
          _stack.emplace_back(_Combine_Node(_result, _f.d_a1));
          _stack.emplace_back(_Enter(_f._s0));
        } else {
          auto _f = std::move(std::get<_Combine_Node>(_frame));
          _result = ((_result + _f.d_a1) + _f._result);
        }
      }
      return _result;
    }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, tree &, T1 &, unsigned int &,
                                     tree &, T1 &>
    T1 tree_rec(const T1 f, F1 &&f0) const {
      const tree *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const tree *_self;
      };

      /// _After_Node: saves [_s0, d_a2, d_a1, d_a0], dispatches next recursive
      /// call.
      struct _After_Node {
        tree *_s0;
        tree d_a2;
        unsigned int d_a1;
        tree d_a0;
      };

      /// _Combine_Node: receives partial results, combines with _result from
      /// final call.
      struct _Combine_Node {
        T1 _result;
        tree d_a2;
        unsigned int d_a1;
        tree d_a0;
      };

      using _Frame = std::variant<_Enter, _After_Node, _Combine_Node>;
      T1 _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(8);
      _stack.emplace_back(_Enter(_self));
      /// Loopified tree_rec: _Enter -> _After_Node -> _Combine_Node.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const tree *_self = _f._self;
          auto &&_sv = *(_self);
          if (std::holds_alternative<typename tree::Leaf>(_sv.v())) {
            _result = f;
          } else {
            const auto &[d_a0, d_a1, d_a2] =
                std::get<typename tree::Node>(_sv.v());
            _stack.emplace_back(
                _After_Node(d_a0.get(), *(d_a2), d_a1, *(d_a0)));
            _stack.emplace_back(_Enter(d_a2.get()));
          }
        } else if (std::holds_alternative<_After_Node>(_frame)) {
          auto _f = std::move(std::get<_After_Node>(_frame));
          _stack.emplace_back(_Combine_Node(_result, std::move(_f.d_a2),
                                            _f.d_a1, std::move(_f.d_a0)));
          _stack.emplace_back(_Enter(_f._s0));
        } else {
          auto _f = std::move(std::get<_Combine_Node>(_frame));
          _result = f0(_f.d_a0, _result, _f.d_a1, _f.d_a2, _f._result);
        }
      }
      return _result;
    }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, tree &, T1 &, unsigned int &,
                                     tree &, T1 &>
    T1 tree_rect(const T1 f, F1 &&f0) const {
      const tree *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const tree *_self;
      };

      /// _After_Node: saves [_s0, d_a2, d_a1, d_a0], dispatches next recursive
      /// call.
      struct _After_Node {
        tree *_s0;
        tree d_a2;
        unsigned int d_a1;
        tree d_a0;
      };

      /// _Combine_Node: receives partial results, combines with _result from
      /// final call.
      struct _Combine_Node {
        T1 _result;
        tree d_a2;
        unsigned int d_a1;
        tree d_a0;
      };

      using _Frame = std::variant<_Enter, _After_Node, _Combine_Node>;
      T1 _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(8);
      _stack.emplace_back(_Enter(_self));
      /// Loopified tree_rect: _Enter -> _After_Node -> _Combine_Node.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const tree *_self = _f._self;
          auto &&_sv = *(_self);
          if (std::holds_alternative<typename tree::Leaf>(_sv.v())) {
            _result = f;
          } else {
            const auto &[d_a0, d_a1, d_a2] =
                std::get<typename tree::Node>(_sv.v());
            _stack.emplace_back(
                _After_Node(d_a0.get(), *(d_a2), d_a1, *(d_a0)));
            _stack.emplace_back(_Enter(d_a2.get()));
          }
        } else if (std::holds_alternative<_After_Node>(_frame)) {
          auto _f = std::move(std::get<_After_Node>(_frame));
          _stack.emplace_back(_Combine_Node(_result, std::move(_f.d_a2),
                                            _f.d_a1, std::move(_f.d_a0)));
          _stack.emplace_back(_Enter(_f._s0));
        } else {
          auto _f = std::move(std::get<_Combine_Node>(_frame));
          _result = f0(_f.d_a0, _result, _f.d_a1, _f.d_a2, _f._result);
        }
      }
      return _result;
    }
  };

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

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, t_A &, mylist<t_A> &, T1 &>
    T1 mylist_rec(const T1 f, F1 &&f0) const {
      const mylist *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const mylist *_self;
      };

      /// _Resume_Mycons: saves [f0, d_a1, d_a0], resumes after recursive call
      /// with _result.
      struct _Resume_Mycons {
        F1 f0;
        mylist<t_A> d_a1;
        t_A d_a0;
      };

      using _Frame = std::variant<_Enter, _Resume_Mycons>;
      T1 _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(8);
      _stack.emplace_back(_Enter(_self));
      /// Loopified mylist_rec: _Enter -> _Resume_Mycons.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const mylist *_self = _f._self;
          auto &&_sv = *(_self);
          if (std::holds_alternative<typename mylist<t_A>::Mynil>(_sv.v())) {
            _result = f;
          } else {
            const auto &[d_a0, d_a1] =
                std::get<typename mylist<t_A>::Mycons>(_sv.v());
            _stack.emplace_back(_Resume_Mycons(f0, *(d_a1), d_a0));
            _stack.emplace_back(_Enter(d_a1.get()));
          }
        } else {
          auto _f = std::move(std::get<_Resume_Mycons>(_frame));
          _result = _f.f0(_f.d_a0, _f.d_a1, _result);
        }
      }
      return _result;
    }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, t_A &, mylist<t_A> &, T1 &>
    T1 mylist_rect(const T1 f, F1 &&f0) const {
      const mylist *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const mylist *_self;
      };

      /// _Resume_Mycons: saves [f0, d_a1, d_a0], resumes after recursive call
      /// with _result.
      struct _Resume_Mycons {
        F1 f0;
        mylist<t_A> d_a1;
        t_A d_a0;
      };

      using _Frame = std::variant<_Enter, _Resume_Mycons>;
      T1 _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(8);
      _stack.emplace_back(_Enter(_self));
      /// Loopified mylist_rect: _Enter -> _Resume_Mycons.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const mylist *_self = _f._self;
          auto &&_sv = *(_self);
          if (std::holds_alternative<typename mylist<t_A>::Mynil>(_sv.v())) {
            _result = f;
          } else {
            const auto &[d_a0, d_a1] =
                std::get<typename mylist<t_A>::Mycons>(_sv.v());
            _stack.emplace_back(_Resume_Mycons(f0, *(d_a1), d_a0));
            _stack.emplace_back(_Enter(d_a1.get()));
          }
        } else {
          auto _f = std::move(std::get<_Resume_Mycons>(_frame));
          _result = _f.f0(_f.d_a0, _f.d_a1, _result);
        }
      }
      return _result;
    }
  };

  static unsigned int
  sum_fns(const mylist<std::function<unsigned int(unsigned int)>> &l);
  static inline const unsigned int test_tree_adder = []() {
    tree t = tree::node(tree::node(tree::leaf(), 10u, tree::leaf()), 20u,
                        tree::node(tree::leaf(), 30u, tree::leaf()));
    return std::move(t).tree_to_adder(5u);
  }();

  /// TEST 2: Build closures during list traversal,
  /// where each closure captures the HEAD of the list
  /// and the closure from the previous step.
  static unsigned int
  chain_adders(const mylist<unsigned int> &l,
               const std::function<unsigned int(unsigned int)> acc,
               const unsigned int _x0) { /// _Enter: captures varying parameters
                                         /// for each recursive call.

    struct _Enter {
      std::function<unsigned int(unsigned int)> acc;
      mylist<unsigned int> l;
    };

    using _Frame = std::variant<_Enter>;
    unsigned int _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter(acc, l));
    /// Loopified chain_adders: _Enter.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      auto _f = std::move(std::get<_Enter>(_frame));
      const std::function<unsigned int(unsigned int)> &acc = _f.acc;
      const mylist<unsigned int> &l = _f.l;
      _result = [=]() mutable -> std::function<unsigned int(unsigned int)> {
        if (std::holds_alternative<typename mylist<unsigned int>::Mynil>(
                l.v())) {
          return acc;
        } else {
          const auto &[d_a0, d_a1] =
              std::get<typename mylist<unsigned int>::Mycons>(l.v());
          mylist<unsigned int> d_a1_value = *(d_a1);
          return [=](unsigned int _x0) mutable -> unsigned int {
            return chain_adders(
                d_a1_value,
                [=](const unsigned int n) mutable { return acc((d_a0 + n)); },
                _x0);
          };
        }
      }()(_x0);
    }
    return _result;
  }

  static inline const unsigned int test_chain = []() {
    mylist<unsigned int> l = mylist<unsigned int>::mycons(
        10u, mylist<unsigned int>::mycons(
                 20u, mylist<unsigned int>::mycons(
                          30u, mylist<unsigned int>::mynil())));
    return chain_adders(
        std::move(l), [](const unsigned int x) { return x; }, 7u);
  }();
  /// TEST 3: Recursive function returning a list of closures.
  /// Each closure captures the tree node's value and subtrees.
  static mylist<std::function<unsigned int(unsigned int)>>
  collect_adders(const tree &t);
  static inline const unsigned int test_collect_adders = []() {
    tree t = tree::node(tree::node(tree::leaf(), 5u, tree::leaf()), 10u,
                        tree::node(tree::leaf(), 15u, tree::leaf()));
    return sum_fns(collect_adders(std::move(t)));
  }();
  /// TEST 4: Closure returned from nested match.
  /// Tests return_captures_by_value through Sif branches.
  static unsigned int choose_fn(const std::optional<bool> &o,
                                const unsigned int v, const unsigned int n);
  static inline const unsigned int test_choose = []() {
    std::function<unsigned int(unsigned int)> f1 =
        [](unsigned int _x0) -> unsigned int {
      return choose_fn(std::make_optional<bool>(true), 10u, _x0);
    };
    std::function<unsigned int(unsigned int)> f2 =
        [](unsigned int _x0) -> unsigned int {
      return choose_fn(std::make_optional<bool>(false), 3u, _x0);
    };
    std::function<unsigned int(unsigned int)> f3 =
        [](unsigned int _x0) -> unsigned int {
      return choose_fn(std::optional<bool>(), 99u, _x0);
    };
    return ((f1(5u) + f2(7u)) + f3(42u));
  }();
  static inline const unsigned int test_nested = []() {
    return []() {
      tree t = tree::node(tree::node(tree::leaf(), 5u, tree::leaf()), 10u,
                          tree::node(tree::leaf(), 15u, tree::leaf()));
      std::function<unsigned int(unsigned int)> f1 =
          [=](unsigned int _x0) mutable -> unsigned int {
        return t.nested_match_closure(true, _x0);
      };
      std::function<unsigned int(unsigned int)> f2 =
          [&](unsigned int _x0) -> unsigned int {
        return std::move(t).nested_match_closure(false, _x0);
      };
      return (f1(0u) + f2(0u));
    }();
  }();
  /// TEST 6: Function returning closure in pair.
  /// Tests pair construction with closure.
  static std::pair<std::function<unsigned int(unsigned int)>, unsigned int>
  pair_with_fn(const unsigned int n);
  static inline const unsigned int test_pair_fn = []() {
    std::pair<std::function<unsigned int(unsigned int)>, unsigned int> p =
        pair_with_fn(10u);
    return (p.first(5u) + p.second);
  }();
  /// TEST 7: Mutually recursive functions using a fixpoint
  /// where one captures the other's result as a closure.
  static mylist<std::function<unsigned int(unsigned int)>>
  build_tree_fns(const tree &t, const unsigned int depth);
  static inline const unsigned int test_tree_fns = []() {
    tree t = tree::node(tree::node(tree::leaf(), 3u, tree::leaf()), 7u,
                        tree::node(tree::leaf(), 11u, tree::leaf()));
    return sum_fns(build_tree_fns(std::move(t), 2u));
  }();
  static inline const unsigned int test_tree_capture = []() {
    tree t = tree::node(tree::node(tree::leaf(), 100u, tree::leaf()), 200u,
                        tree::node(tree::leaf(), 300u, tree::leaf()));
    return std::move(t).make_tree_summer(0u);
  }();
};

#endif // INCLUDED_MEM_SAFETY_PROBE10
