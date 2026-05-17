#ifndef INCLUDED_MEM_SAFETY_PROBE3
#define INCLUDED_MEM_SAFETY_PROBE3

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
      return tree(Node{std::make_unique<tree>(std::move(a0)), a1,
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

    /// TEST 9: Closure stored in option alongside tree data in pair.
    std::pair<std::optional<std::function<unsigned int(unsigned int)>>, tree>
    opt_pair(bool b) const {
      return std::make_pair(
          (b ? std::make_optional<std::function<unsigned int(unsigned int)>>(
                   [&](unsigned int _x0) -> unsigned int {
                     return (*this).sum_values(_x0);
                   })
             : std::optional<std::function<unsigned int(unsigned int)>>()),
          *this);
    }

    /// TEST 8: Three closures, each capturing different tree,
    /// applied in a specific order with results feeding forward.
    unsigned int chain_three(tree t2, const tree &t3) const {
      std::function<unsigned int(unsigned int)> f1 =
          [&](unsigned int _x0) -> unsigned int {
        return std::move(*this).sum_values(_x0);
      };
      std::function<unsigned int(unsigned int)> f2 =
          [&](unsigned int _x0) -> unsigned int {
        return std::move(t2).sum_values(_x0);
      };
      return t3.sum_values(f2(f1(0u)));
    }

    /// TEST 7: Map a tree, producing a new tree. Then sum the new tree.
    /// The mapped function captures a tree value.
    template <typename F0>
      requires std::is_invocable_r_v<unsigned int, F0 &, unsigned int &>
    tree map_tree(F0 &&f) const {
      const tree *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const tree *_self;
      };

      /// _After_Node: saves [_s0, d_a1], dispatches next recursive call.
      struct _After_Node {
        tree *_s0;
        decltype(std::declval<F0 &>()(std::declval<unsigned int &>())) d_a1;
      };

      /// _Combine_Node: receives partial results, combines with _result from
      /// final call.
      struct _Combine_Node {
        tree _result;
        decltype(std::declval<F0 &>()(std::declval<unsigned int &>())) d_a1;
      };

      using _Frame = std::variant<_Enter, _After_Node, _Combine_Node>;
      tree _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(8);
      _stack.emplace_back(_Enter{_self});
      /// Loopified map_tree: _Enter -> _After_Node -> _Combine_Node.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const tree *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename tree::Leaf>(_sv.v())) {
            _result = tree::leaf();
          } else {
            const auto &[d_a0, d_a1, d_a2] =
                std::get<typename tree::Node>(_sv.v());
            _stack.emplace_back(_After_Node{d_a0.get(), f(d_a1)});
            _stack.emplace_back(_Enter{d_a2.get()});
          }
        } else if (std::holds_alternative<_After_Node>(_frame)) {
          auto _f = std::move(std::get<_After_Node>(_frame));
          _stack.emplace_back(_Combine_Node{std::move(_result), _f.d_a1});
          _stack.emplace_back(_Enter{_f._s0});
        } else {
          auto _f = std::move(std::get<_Combine_Node>(_frame));
          _result = tree::node(_result, _f.d_a1, _f._result);
        }
      }
      return _result;
    }

    /// TEST 6: Nested pair: pair of pairs of closures.
    std::pair<std::pair<std::function<unsigned int(unsigned int)>,
                        std::function<unsigned int(unsigned int)>>,
              unsigned int>
    nested_pair() const {
      tree _self_val = *this;
      return std::make_pair(std::make_pair(
                                [=](unsigned int _x0) mutable -> unsigned int {
                                  return _self_val.sum_values(_x0);
                                },
                                [](unsigned int x) { return x; }),
                            (*this).sum_values(0u));
    }

    /// TEST 5: Mutual use: tree used BOTH as partial application arg
    /// AND as match scrutinee in the SAME scope.
    unsigned int mutual_use() const {
      tree _self_val = *this;
      std::function<unsigned int(unsigned int)> f =
          [=](unsigned int _x0) mutable -> unsigned int {
        return _self_val.sum_values(_x0);
      };
      unsigned int r = [&]() {
        if (std::holds_alternative<typename tree::Leaf>(this->v())) {
          return 0u;
        } else {
          auto &[d_a0, d_a1, d_a2] = std::get<typename tree::Node>(this->v());
          return d_a1;
        }
      }();
      return f(r);
    }

    /// TEST 4: Tree traversal that builds up a nat accumulator
    /// using local fixpoint. The tree is captured in the fixpoint scope.
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
      _stack.emplace_back(_Enter{_self});
      /// Loopified tree_sum: _Enter -> _After_Node -> _Combine_Node.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const tree *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename tree::Leaf>(_sv.v())) {
            _result = 0u;
          } else {
            const auto &[d_a0, d_a1, d_a2] =
                std::get<typename tree::Node>(_sv.v());
            _stack.emplace_back(_After_Node{d_a0.get(), d_a1});
            _stack.emplace_back(_Enter{d_a2.get()});
          }
        } else if (std::holds_alternative<_After_Node>(_frame)) {
          auto _f = std::move(std::get<_After_Node>(_frame));
          _stack.emplace_back(_Combine_Node{_result, _f.d_a1});
          _stack.emplace_back(_Enter{_f._s0});
        } else {
          auto _f = std::move(std::get<_Combine_Node>(_frame));
          _result = ((_result + _f.d_a1) + _f._result);
        }
      }
      return _result;
    }

    /// TEST 3: Partial application result stored in a pair, then both
    /// elements of the pair are applied. The pair construction must
    /// properly clone the closures.
    std::pair<std::function<unsigned int(unsigned int)>,
              std::function<unsigned int(unsigned int)>>
    paired_closures(tree t2) const {
      tree _self_val = *this;
      return std::make_pair(
          [=](unsigned int _x0) mutable -> unsigned int {
            return _self_val.sum_values(_x0);
          },
          [=](unsigned int _x0) mutable -> unsigned int {
            return t2.sum_values(_x0);
          });
    }

    unsigned int sum_values(unsigned int x) const {
      if (std::holds_alternative<typename tree::Leaf>(this->v())) {
        return x;
      } else {
        const auto &[d_a0, d_a1, d_a2] =
            std::get<typename tree::Node>(this->v());
        auto &&_sv0 = *d_a0;
        if (std::holds_alternative<typename tree::Leaf>(_sv0.v())) {
          return (d_a1 + x);
        } else {
          const auto &[d_a00, d_a10, d_a20] =
              std::get<typename tree::Node>(_sv0.v());
          auto &&_sv1 = *d_a2;
          if (std::holds_alternative<typename tree::Leaf>(_sv1.v())) {
            return (d_a10 + x);
          } else {
            const auto &[d_a01, d_a11, d_a21] =
                std::get<typename tree::Node>(_sv1.v());
            return (((d_a10 + d_a11) + d_a1) + x);
          }
        }
      }
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
      _stack.emplace_back(_Enter{_self});
      /// Loopified tree_rec: _Enter -> _After_Node -> _Combine_Node.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const tree *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename tree::Leaf>(_sv.v())) {
            _result = f;
          } else {
            const auto &[d_a0, d_a1, d_a2] =
                std::get<typename tree::Node>(_sv.v());
            _stack.emplace_back(_After_Node{d_a0.get(), *d_a2, d_a1, *d_a0});
            _stack.emplace_back(_Enter{d_a2.get()});
          }
        } else if (std::holds_alternative<_After_Node>(_frame)) {
          auto _f = std::move(std::get<_After_Node>(_frame));
          _stack.emplace_back(_Combine_Node{_result, std::move(_f.d_a2),
                                            _f.d_a1, std::move(_f.d_a0)});
          _stack.emplace_back(_Enter{_f._s0});
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
      _stack.emplace_back(_Enter{_self});
      /// Loopified tree_rect: _Enter -> _After_Node -> _Combine_Node.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const tree *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename tree::Leaf>(_sv.v())) {
            _result = f;
          } else {
            const auto &[d_a0, d_a1, d_a2] =
                std::get<typename tree::Node>(_sv.v());
            _stack.emplace_back(_After_Node{d_a0.get(), *d_a2, d_a1, *d_a0});
            _stack.emplace_back(_Enter{d_a2.get()});
          }
        } else if (std::holds_alternative<_After_Node>(_frame)) {
          auto _f = std::move(std::get<_After_Node>(_frame));
          _stack.emplace_back(_Combine_Node{_result, std::move(_f.d_a2),
                                            _f.d_a1, std::move(_f.d_a0)});
          _stack.emplace_back(_Enter{_f._s0});
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
          _dst->d_v_ = Mynil{};
        } else {
          const auto &_alt = std::get<Mycons>(_src->v());
          _dst->d_v_ = Mycons{
              _alt.d_a0, _alt.d_a1 ? std::make_unique<mylist<t_A>>() : nullptr};
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
        this->d_v_ = Mynil{};
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename mylist<_U>::Mycons>(_other.v());
        this->d_v_ = Mycons{
            t_A(d_a0), d_a1 ? std::make_unique<mylist<t_A>>(*d_a1) : nullptr};
      }
    }

    static mylist<t_A> mynil() { return mylist(Mynil{}); }

    static mylist<t_A> mycons(t_A a0, mylist<t_A> a1) {
      return mylist(
          Mycons{std::move(a0), std::make_unique<mylist<t_A>>(std::move(a1))});
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
      _stack.emplace_back(_Enter{_self});
      /// Loopified mylist_rec: _Enter -> _Resume_Mycons.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const mylist *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename mylist<t_A>::Mynil>(_sv.v())) {
            _result = f;
          } else {
            const auto &[d_a0, d_a1] =
                std::get<typename mylist<t_A>::Mycons>(_sv.v());
            _stack.emplace_back(_Resume_Mycons{f0, *d_a1, d_a0});
            _stack.emplace_back(_Enter{d_a1.get()});
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
      _stack.emplace_back(_Enter{_self});
      /// Loopified mylist_rect: _Enter -> _Resume_Mycons.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const mylist *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename mylist<t_A>::Mynil>(_sv.v())) {
            _result = f;
          } else {
            const auto &[d_a0, d_a1] =
                std::get<typename mylist<t_A>::Mycons>(_sv.v());
            _stack.emplace_back(_Resume_Mycons{f0, *d_a1, d_a0});
            _stack.emplace_back(_Enter{d_a1.get()});
          }
        } else {
          auto _f = std::move(std::get<_Resume_Mycons>(_frame));
          _result = _f.f0(_f.d_a0, _f.d_a1, _result);
        }
      }
      return _result;
    }
  };

  /// TEST 1: Local fixpoint capturing a tree value.
  /// The fixpoint accesses the captured tree on each recursive call.
  static inline const unsigned int local_fix_capture = []() {
    return []() {
      tree t = tree::node(tree::leaf(), 42u, tree::leaf());
      auto helper_impl = [&](auto &_self_helper,
                             unsigned int n) -> unsigned int {
        if (n <= 0) {
          return t.sum_values(0u);
        } else {
          unsigned int n_ = n - 1;
          return (t.sum_values(1u) + _self_helper(_self_helper, n_));
        }
      };
      auto helper = [&](unsigned int n) -> unsigned int {
        return helper_impl(helper_impl, n);
      };
      return helper(3u);
    }();
  }();
  /// TEST 2: Local fixpoint returning a closure that captures
  /// a match-destructured field from a tree.
  static inline const unsigned int fix_with_closure = []() {
    return []() {
      tree t = tree::node(tree::node(tree::leaf(), 10u, tree::leaf()), 20u,
                          tree::node(tree::leaf(), 30u, tree::leaf()));
      if (std::holds_alternative<typename tree::Leaf>(t.v_mut())) {
        return 0u;
      } else {
        auto &[d_a0, d_a1, d_a2] = std::get<typename tree::Node>(t.v_mut());
        std::function<unsigned int(unsigned int)> fl =
            [&](unsigned int _x0) -> unsigned int {
          return (*d_a0).sum_values(_x0);
        };
        unsigned int vl = fl(d_a1);
        std::function<unsigned int(unsigned int)> fr =
            [&](unsigned int _x0) -> unsigned int {
          return (*d_a2).sum_values(_x0);
        };
        unsigned int vr = fr(std::move(d_a1));
        return (vl + vr);
      }
    }();
  }();
  static inline const unsigned int test_paired_closures = []() {
    tree t1 = tree::node(tree::leaf(), 10u, tree::leaf());
    tree t2 = tree::node(tree::leaf(), 20u, tree::leaf());
    std::pair<std::function<unsigned int(unsigned int)>,
              std::function<unsigned int(unsigned int)>>
        p = std::move(t1).paired_closures(std::move(t2));
    return (p.first(5u) + p.second(5u));
  }();
  static inline const unsigned int test_tree_sum =
      tree::node(tree::node(tree::leaf(), 10u, tree::leaf()), 20u,
                 tree::node(tree::leaf(), 30u, tree::leaf()))
          .tree_sum();
  /// f = sum_values (Node (Node Leaf 10 Leaf) 20 (...))
  /// r = 20. f 20 = 10+30+20+20 = 80
  static inline const unsigned int test_mutual_use =
      tree::node(tree::node(tree::leaf(), 10u, tree::leaf()), 20u,
                 tree::node(tree::leaf(), 30u, tree::leaf()))
          .mutual_use();
  static inline const unsigned int test_nested_pair = []() {
    tree t = tree::node(tree::leaf(), 42u, tree::leaf());
    std::pair<std::pair<std::function<unsigned int(unsigned int)>,
                        std::function<unsigned int(unsigned int)>>,
              unsigned int>
        p = std::move(t).nested_pair();
    return (((p.first).first(10u) + (p.first).second(10u)) + p.second);
  }();
  static inline const unsigned int test_map_with_captured = []() {
    return []() {
      tree t = tree::node(tree::node(tree::leaf(), 5u, tree::leaf()), 10u,
                          tree::node(tree::leaf(), 15u, tree::leaf()));
      tree t2 = tree::node(tree::leaf(), 100u, tree::leaf());
      tree mapped = std::move(t).map_tree(
          [=](unsigned int v) mutable { return (v + t2.sum_values(0u)); });
      return std::move(mapped).tree_sum();
    }();
  }();
  static inline const unsigned int test_chain_three =
      tree::node(tree::leaf(), 10u, tree::leaf())
          .chain_three(tree::node(tree::leaf(), 20u, tree::leaf()),
                       tree::node(tree::leaf(), 30u, tree::leaf()));
  static inline const unsigned int test_opt_pair = []() {
    tree t = tree::node(tree::leaf(), 42u, tree::leaf());
    std::pair<std::optional<std::function<unsigned int(unsigned int)>>, tree>
        p = std::move(t).opt_pair(true);
    auto _cs = p.first;
    if (_cs.has_value()) {
      const std::function<unsigned int(unsigned int)> &f = *_cs;
      return (f(10u) + p.second.sum_values(0u));
    } else {
      return 0u;
    }
  }();
  /// TEST 10: Large tree with deep recursion — stresses the
  /// loopified tree traversal and clone mechanisms.
  static tree build_deep(unsigned int n);
  static inline const unsigned int test_deep_tree = []() {
    tree t = build_deep(100u);
    return std::move(t).tree_sum();
  }();

  /// TEST 11: Fixpoint that takes a function argument and uses it
  /// alongside captured tree data.
  template <typename F0>
    requires std::is_invocable_r_v<unsigned int, F0 &, unsigned int &>
  static unsigned int
  apply_n_times(F0 &&f, unsigned int n,
                unsigned int x) { /// _Enter: captures varying parameters for
                                  /// each recursive call.

    struct _Enter {
      unsigned int n;
    };

    /// _Resume_n_: saves [f], resumes after recursive call with _result.
    struct _Resume_n_ {
      F0 f;
    };

    using _Frame = std::variant<_Enter, _Resume_n_>;
    unsigned int _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{n});
    /// Loopified apply_n_times: _Enter -> _Resume_n_.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        unsigned int n = _f.n;
        if (n <= 0) {
          _result = x;
        } else {
          unsigned int n_ = n - 1;
          _stack.emplace_back(_Resume_n_{f});
          _stack.emplace_back(_Enter{n_});
        }
      } else {
        auto _f = std::move(std::get<_Resume_n_>(_frame));
        _result = _f.f(_result);
      }
    }
    return _result;
  }

  static inline const unsigned int test_apply_n = []() {
    return []() {
      tree t = tree::node(tree::leaf(), 10u, tree::leaf());
      return apply_n_times(
          [=](unsigned int _x0) mutable -> unsigned int {
            return t.sum_values(_x0);
          },
          5u, 0u);
    }();
  }();
  /// TEST 12: Closure that partially applies a fixpoint.
  /// The fixpoint itself takes a function argument.
  static inline const unsigned int test_partial_fix = []() {
    return []() {
      tree t = tree::node(tree::leaf(), 5u, tree::leaf());
      std::function<unsigned int(unsigned int)> f =
          [=](unsigned int _x0) mutable -> unsigned int {
        return apply_n_times(
            [=](unsigned int _x0) mutable -> unsigned int {
              return t.sum_values(_x0);
            },
            3u, _x0);
      };
      return (f(0u) + f(10u));
    }();
  }();
};

#endif // INCLUDED_MEM_SAFETY_PROBE3
