#ifndef INCLUDED_MEM_SAFETY_PROBE25
#define INCLUDED_MEM_SAFETY_PROBE25

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

    /// TEST 8: Option wrapping a closure from match.
    /// Exercises different code path for returning closures
    /// through an inductive constructor.
    std::optional<std::function<unsigned int(unsigned int)>>
    match_closure_opt(const bool b) const {
      tree _self_val = *(this);
      if (b) {
        return std::make_optional<std::function<unsigned int(unsigned int)>>(
            [=](const unsigned int x) mutable {
              if (std::holds_alternative<typename tree::Leaf>(_self_val.v())) {
                return x;
              } else {
                const auto &[d_a0, d_a1, d_a2] =
                    std::get<typename tree::Node>(_self_val.v());
                return (((x + (*(d_a0)).tree_sum()) + d_a1) +
                        (*(d_a2)).tree_sum());
              }
            });
      } else {
        return std::optional<std::function<unsigned int(unsigned int)>>();
      }
    }

    /// TEST 7: Return closure from match that captures a tree child,
    /// then store it in a pair. Double-wrapping test.
    std::pair<std::function<unsigned int(unsigned int)>, unsigned int>
    match_then_pair() const {
      tree _self_val = *(this);
      std::function<unsigned int(unsigned int)> f =
          [=](const unsigned int x) mutable {
            if (std::holds_alternative<typename tree::Leaf>(_self_val.v())) {
              return x;
            } else {
              const auto &[d_a0, d_a1, d_a2] =
                  std::get<typename tree::Node>(_self_val.v());
              return ((x + (*(d_a0)).tree_sum()) + d_a1);
            }
          };
      return std::make_pair(f, std::move(*(this)).tree_sum());
    }

    /// TEST 5: Deep match — closure captures grandchild of tree.
    /// ll is child-of-child, accessed via two levels of unique_ptr deref.
    unsigned int deep_match_closure(const unsigned int x) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename tree::Leaf>(_sv.v())) {
        return x;
      } else {
        const auto &[d_a0, d_a1, d_a2] = std::get<typename tree::Node>(_sv.v());
        auto &&_sv0 = *(d_a0);
        if (std::holds_alternative<typename tree::Leaf>(_sv0.v())) {
          return (x + d_a1);
        } else {
          const auto &[d_a00, d_a10, d_a20] =
              std::get<typename tree::Node>(_sv0.v());
          return (((x + (*(d_a00)).tree_sum()) + d_a10) + d_a1);
        }
      }
    }

    /// TEST 4: Nested match returning closure. Both match levels
    /// contribute captured variables to the closure.
    unsigned int nested_match_closure(const tree &t2,
                                      const unsigned int x) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename tree::Leaf>(_sv.v())) {
        return x;
      } else {
        const auto &[d_a0, d_a1, d_a2] = std::get<typename tree::Node>(_sv.v());
        if (std::holds_alternative<typename tree::Leaf>(t2.v())) {
          return (x + d_a1);
        } else {
          const auto &[d_a00, d_a10, d_a20] =
              std::get<typename tree::Node>(t2.v());
          return (((x + (*(d_a0)).tree_sum()) + d_a10) + (*(d_a20)).tree_sum());
        }
      }
    }

    /// TEST 3: Return PAIR of closures from match.
    /// Each closure captures different match-bound children.
    std::pair<std::function<unsigned int(unsigned int)>,
              std::function<unsigned int(unsigned int)>>
    pair_closures() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename tree::Leaf>(_sv.v())) {
        return std::make_pair([](const unsigned int x) { return x; },
                              [](const unsigned int x) { return x; });
      } else {
        const auto &[d_a0, d_a1, d_a2] = std::get<typename tree::Node>(_sv.v());
        tree d_a0_value = *(d_a0);
        tree d_a2_value = *(d_a2);
        return std::make_pair(
            [=](const unsigned int x) mutable {
              return (x + d_a0_value.tree_sum());
            },
            [=](const unsigned int x) mutable {
              return (x + d_a2_value.tree_sum());
            });
      }
    }

    /// TEST 2: Return closure from match branch — captures children.
    /// After IIFE inlining, the Smatch is at the top level, and
    /// return_captures_by_value may not traverse into it.
    unsigned int match_closure(const unsigned int x) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename tree::Leaf>(_sv.v())) {
        return x;
      } else {
        const auto &[d_a0, d_a1, d_a2] = std::get<typename tree::Node>(_sv.v());
        return (((x + (*(d_a0)).tree_sum()) + d_a1) + (*(d_a2)).tree_sum());
      }
    }

    /// TEST 1: Return closure that captures the whole tree parameter.
    /// The closure body calls tree_sum on t. If t is passed by const ref
    /// and the closure uses &, t's binding dangles when function returns.
    /// The test calls the closure AFTER the tree temporary is destroyed.
    unsigned int make_sum_fn(const unsigned int x) const {
      return (x + (*(this)).tree_sum());
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
    T1 tree_rec(T1 f, F1 &&f0) const {
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
    T1 tree_rect(T1 f, F1 &&f0) const {
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

  static inline const unsigned int test_make_sum_fn =
      tree::node(tree::node(tree::leaf(), 3u, tree::leaf()), 7u,
                 tree::node(tree::leaf(), 11u, tree::leaf()))
          .make_sum_fn(100u);
  static inline const unsigned int test_match_closure =
      tree::node(tree::node(tree::leaf(), 3u, tree::leaf()), 7u,
                 tree::node(tree::leaf(), 11u, tree::leaf()))
          .match_closure(100u);
  static inline const unsigned int test_pair_closures = []() {
    std::pair<std::function<unsigned int(unsigned int)>,
              std::function<unsigned int(unsigned int)>>
        p = tree::node(tree::node(tree::leaf(), 3u, tree::leaf()), 7u,
                       tree::node(tree::leaf(), 11u, tree::leaf()))
                .pair_closures();
    return (p.first(100u) + p.second(200u));
  }();
  static inline const unsigned int test_nested_match_closure =
      tree::node(tree::node(tree::leaf(), 3u, tree::leaf()), 7u,
                 tree::node(tree::leaf(), 11u, tree::leaf()))
          .nested_match_closure(
              tree::node(tree::node(tree::leaf(), 2u, tree::leaf()), 5u,
                         tree::node(tree::leaf(), 8u, tree::leaf())),
              100u);
  static inline const unsigned int test_deep_match_closure =
      tree::node(tree::node(tree::node(tree::leaf(), 1u, tree::leaf()), 2u,
                            tree::node(tree::leaf(), 3u, tree::leaf())),
                 10u, tree::leaf())
          .deep_match_closure(100u);

  /// TEST 6: Build a list of closures from recursive tree traversal.
  /// Each closure captures v from the current node.
  /// Tests whether closures stored in constructor fields are safe.
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
    T1 mylist_rec(T1 f, F1 &&f0) const {
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
    T1 mylist_rect(T1 f, F1 &&f0) const {
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

  static mylist<std::function<unsigned int(unsigned int)>>
  build_adders(const tree &t);
  static unsigned int
  apply_first(const mylist<std::function<unsigned int(unsigned int)>> &l,
              const unsigned int x);
  static inline const unsigned int test_build_adders = []() {
    mylist<std::function<unsigned int(unsigned int)>> adders =
        build_adders(tree::node(tree::leaf(), 42u, tree::leaf()));
    return apply_first(std::move(adders), 100u);
  }();
  static inline const unsigned int test_match_then_pair = []() {
    std::pair<std::function<unsigned int(unsigned int)>, unsigned int> p =
        tree::node(tree::node(tree::leaf(), 4u, tree::leaf()), 6u,
                   tree::node(tree::leaf(), 9u, tree::leaf()))
            .match_then_pair();
    return (p.first(100u) + p.second);
  }();
  static inline const unsigned int test_match_closure_opt =
      []() -> unsigned int {
    auto _cs = tree::node(tree::node(tree::leaf(), 2u, tree::leaf()), 5u,
                          tree::node(tree::leaf(), 8u, tree::leaf()))
                   .match_closure_opt(true);
    if (_cs.has_value()) {
      const std::function<unsigned int(unsigned int)> &f = *_cs;
      return f(100u);
    } else {
      return 0u;
    }
  }();
};

#endif // INCLUDED_MEM_SAFETY_PROBE25
