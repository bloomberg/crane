#ifndef INCLUDED_MEM_SAFETY_PROBE13
#define INCLUDED_MEM_SAFETY_PROBE13

#include <functional>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

struct MemSafetyProbe13 {
  /// Probe 13: Value-type move semantics and the flatten optimization.
  ///
  /// The flatten optimization (make_owned_param_matches +
  /// optimize_frame_push_args) marks match branches as owned and
  /// moves unique_ptr child fields into Enter frames. If a closure
  /// or continuation simultaneously references the same field,
  /// the move creates use-after-move.
  ///
  /// Also tests: closures returned from functions that take
  /// value-type parameters, and deep pattern match nesting
  /// with closures at each level.
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

    /// TEST 3: Function that matches twice on same tree.
    /// First match extracts subtrees, second match on a subtree
    /// creates a closure capturing the other subtree.
    unsigned int double_match() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename tree::Leaf>(_sv.v())) {
        return 0u;
      } else {
        const auto &[d_a0, d_a1, d_a2] = std::get<typename tree::Node>(_sv.v());
        tree d_a0_value = *(d_a0);
        tree d_a2_value = *(d_a2);
        if (std::holds_alternative<typename tree::Leaf>(d_a0_value.v())) {
          return (d_a2_value.tree_sum() + d_a1);
        } else {
          const auto &[d_a00, d_a10, d_a20] =
              std::get<typename tree::Node>(d_a0_value.v());
          tree d_a00_value = *(d_a00);
          tree d_a20_value = *(d_a20);
          std::function<unsigned int(unsigned int)> f =
              [=](const unsigned int n) mutable {
                return ((d_a2_value.tree_sum() + d_a20_value.tree_sum()) + n);
              };
          return (f(d_a10) + d_a00_value.tree_sum());
        }
      }
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
      _stack.emplace_back(_Enter{_self});
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
          auto &&_sv = *(_self);
          if (std::holds_alternative<typename tree::Leaf>(_sv.v())) {
            _result = f;
          } else {
            const auto &[d_a0, d_a1, d_a2] =
                std::get<typename tree::Node>(_sv.v());
            _stack.emplace_back(
                _After_Node{d_a0.get(), *(d_a2), d_a1, *(d_a0)});
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
          auto &&_sv = *(_self);
          if (std::holds_alternative<typename tree::Leaf>(_sv.v())) {
            _result = f;
          } else {
            const auto &[d_a0, d_a1, d_a2] =
                std::get<typename tree::Node>(_sv.v());
            _stack.emplace_back(
                _After_Node{d_a0.get(), *(d_a2), d_a1, *(d_a0)});
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

    mylist<t_A> app(mylist<t_A> l2) const {
      std::unique_ptr<mylist<t_A>> _head{};
      std::unique_ptr<mylist<t_A>> *_write = &_head;
      const mylist *_loop_self = this;
      mylist<t_A> _loop_l2 = std::move(l2);
      while (true) {
        auto &&_sv = *(_loop_self);
        if (std::holds_alternative<typename mylist<t_A>::Mynil>(_sv.v())) {
          *(_write) = std::make_unique<mylist<t_A>>(std::move(_loop_l2));
          break;
        } else {
          const auto &[d_a0, d_a1] =
              std::get<typename mylist<t_A>::Mycons>(_sv.v());
          auto _cell = std::make_unique<mylist<t_A>>(
              typename mylist<t_A>::Mycons(d_a0, nullptr));
          *(_write) = std::move(_cell);
          _write =
              &std::get<typename mylist<t_A>::Mycons>((*_write)->v_mut()).d_a1;
          _loop_self = d_a1.get();
          continue;
        }
      }
      return std::move(*(_head));
    }

    template <typename T1, typename F0>
      requires std::is_invocable_r_v<T1, F0 &, t_A &>
    mylist<T1> map_list(F0 &&f) const {
      std::unique_ptr<mylist<T1>> _head{};
      std::unique_ptr<mylist<T1>> *_write = &_head;
      const mylist *_loop_self = this;
      while (true) {
        auto &&_sv = *(_loop_self);
        if (std::holds_alternative<typename mylist<t_A>::Mynil>(_sv.v())) {
          *(_write) = std::make_unique<mylist<T1>>(mylist<T1>::mynil());
          break;
        } else {
          const auto &[d_a0, d_a1] =
              std::get<typename mylist<t_A>::Mycons>(_sv.v());
          auto _cell = std::make_unique<mylist<T1>>(
              typename mylist<T1>::Mycons(f(d_a0), nullptr));
          *(_write) = std::move(_cell);
          _write =
              &std::get<typename mylist<T1>::Mycons>((*_write)->v_mut()).d_a1;
          _loop_self = d_a1.get();
          continue;
        }
      }
      return std::move(*(_head));
    }

    unsigned int length() const {
      const mylist *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const mylist *_self;
      };

      /// _Resume_Mycons: saves [_s0], resumes after recursive call with
      /// _result.
      struct _Resume_Mycons {
        decltype(1u) _s0;
      };

      using _Frame = std::variant<_Enter, _Resume_Mycons>;
      unsigned int _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(8);
      _stack.emplace_back(_Enter{_self});
      /// Loopified length: _Enter -> _Resume_Mycons.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const mylist *_self = _f._self;
          auto &&_sv = *(_self);
          if (std::holds_alternative<typename mylist<t_A>::Mynil>(_sv.v())) {
            _result = 0u;
          } else {
            const auto &[d_a0, d_a1] =
                std::get<typename mylist<t_A>::Mycons>(_sv.v());
            _stack.emplace_back(_Resume_Mycons{1u});
            _stack.emplace_back(_Enter{d_a1.get()});
          }
        } else {
          auto _f = std::move(std::get<_Resume_Mycons>(_frame));
          _result = (_f._s0 + _result);
        }
      }
      return _result;
    }

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
          auto &&_sv = *(_self);
          if (std::holds_alternative<typename mylist<t_A>::Mynil>(_sv.v())) {
            _result = f;
          } else {
            const auto &[d_a0, d_a1] =
                std::get<typename mylist<t_A>::Mycons>(_sv.v());
            _stack.emplace_back(_Resume_Mycons{f0, *(d_a1), d_a0});
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
          auto &&_sv = *(_self);
          if (std::holds_alternative<typename mylist<t_A>::Mynil>(_sv.v())) {
            _result = f;
          } else {
            const auto &[d_a0, d_a1] =
                std::get<typename mylist<t_A>::Mycons>(_sv.v());
            _stack.emplace_back(_Resume_Mycons{f0, *(d_a1), d_a0});
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

  static unsigned int sum_list(const mylist<unsigned int> &l);
  /// TEST 1: Double-recursion on tree where both subtrees
  /// are used in closures AND in recursive calls.
  /// Tests if the flatten optimization moves unique_ptr fields
  /// that are also captured by closures.
  static std::pair<mylist<unsigned int>,
                   mylist<std::function<unsigned int(unsigned int)>>>
  tree_vals_and_fns(const tree &t);
  static inline const unsigned int test_vals_and_fns = []() {
    tree t = tree::node(tree::node(tree::leaf(), 3u, tree::leaf()), 7u,
                        tree::node(tree::leaf(), 11u, tree::leaf()));
    auto _cs = tree_vals_and_fns(t);
    const mylist<unsigned int> &vals = _cs.first;
    const mylist<std::function<unsigned int(unsigned int)>> &fns = _cs.second;
    unsigned int val_sum = sum_list(vals);
    unsigned int fn_sum = sum_list(fns.template map_list<unsigned int>(
        [](const std::function<unsigned int(unsigned int)> f) {
          return f(0u);
        }));
    return (val_sum + fn_sum);
  }();
  static inline const unsigned int test_double_match = []() {
    tree t =
        tree::node(tree::node(tree::node(tree::leaf(), 1u, tree::leaf()), 2u,
                              tree::node(tree::leaf(), 3u, tree::leaf())),
                   10u, tree::node(tree::leaf(), 20u, tree::leaf()));
    return std::move(t).double_match();
  }();
  /// TEST 4: Deeply nested tree with closures at EVERY level.
  /// Each closure captures values from its level AND from the parent.
  /// Tests stack depth and closure lifetime with deep nesting.
  static tree make_deep(const unsigned int n);
  static mylist<std::function<unsigned int(unsigned int)>>
  depth_fns(const tree &t, const unsigned int parent_val);
  static inline const unsigned int test_depth_fns = []() {
    tree t = make_deep(5u);
    mylist<std::function<unsigned int(unsigned int)>> fns =
        depth_fns(std::move(t), 0u);
    return sum_list(std::move(fns).template map_list<unsigned int>(
        [](const std::function<unsigned int(unsigned int)> f) {
          return f(0u);
        }));
  }();

  /// TEST 5: Transform a tree by replacing each value with a
  /// function, then evaluate. Tests closures in recursive
  /// tree transformation.
  struct ftree {
    // TYPES
    struct FLeaf {};

    struct FNode {
      std::unique_ptr<ftree> d_a0;
      std::function<unsigned int(unsigned int)> d_a1;
      std::unique_ptr<ftree> d_a2;
    };

    using variant_t = std::variant<FLeaf, FNode>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    ftree() {}

    explicit ftree(FLeaf _v) : d_v_(_v) {}

    explicit ftree(FNode _v) : d_v_(std::move(_v)) {}

    ftree(const ftree &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    ftree(ftree &&_other) : d_v_(std::move(_other.d_v_)) {}

    ftree &operator=(const ftree &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    ftree &operator=(ftree &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    ftree clone() const {
      ftree _out{};

      struct _CloneFrame {
        const ftree *_src;
        ftree *_dst;
      };

      std::vector<_CloneFrame> _stack{};
      _stack.reserve(8);
      _stack.push_back({this, &_out});
      while (!_stack.empty()) {
        auto _frame = _stack.back();
        _stack.pop_back();
        const ftree *_src = _frame._src;
        ftree *_dst = _frame._dst;
        if (std::holds_alternative<FLeaf>(_src->v())) {
          _dst->d_v_ = FLeaf{};
        } else {
          const auto &_alt = std::get<FNode>(_src->v());
          _dst->d_v_ =
              FNode{_alt.d_a0 ? std::make_unique<ftree>() : nullptr, _alt.d_a1,
                    _alt.d_a2 ? std::make_unique<ftree>() : nullptr};
          auto &_dst_alt = std::get<FNode>(_dst->d_v_);
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
    static ftree fleaf() { return ftree(FLeaf{}); }

    static ftree fnode(ftree a0, std::function<unsigned int(unsigned int)> a1,
                       ftree a2) {
      return ftree(FNode{std::make_unique<ftree>(std::move(a0)), std::move(a1),
                         std::make_unique<ftree>(std::move(a2))});
    }

    // MANIPULATORS
    ~ftree() {
      std::vector<std::unique_ptr<ftree>> _stack{};
      _stack.reserve(8);
      auto _drain = [&](ftree &_node) {
        if (std::holds_alternative<FNode>(_node.d_v_)) {
          auto &_alt = std::get<FNode>(_node.d_v_);
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

    unsigned int eval_ftree(const unsigned int base) const {
      const ftree *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const ftree *_self;
      };

      /// _After_FNode: saves [_s0, base], dispatches next recursive call.
      struct _After_FNode {
        ftree *_s0;
        unsigned int base;
      };

      /// _Combine_FNode: receives partial results, combines with _result from
      /// final call.
      struct _Combine_FNode {
        unsigned int _result;
        unsigned int base;
      };

      using _Frame = std::variant<_Enter, _After_FNode, _Combine_FNode>;
      unsigned int _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(8);
      _stack.emplace_back(_Enter{_self});
      /// Loopified eval_ftree: _Enter -> _After_FNode -> _Combine_FNode.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const ftree *_self = _f._self;
          auto &&_sv = *(_self);
          if (std::holds_alternative<typename ftree::FLeaf>(_sv.v())) {
            _result = 0u;
          } else {
            const auto &[d_a0, d_a1, d_a2] =
                std::get<typename ftree::FNode>(_sv.v());
            _stack.emplace_back(_After_FNode{d_a0.get(), d_a1(base)});
            _stack.emplace_back(_Enter{d_a2.get()});
          }
        } else if (std::holds_alternative<_After_FNode>(_frame)) {
          auto _f = std::move(std::get<_After_FNode>(_frame));
          _stack.emplace_back(_Combine_FNode{_result, _f.base});
          _stack.emplace_back(_Enter{_f._s0});
        } else {
          auto _f = std::move(std::get<_Combine_FNode>(_frame));
          _result = ((_result + _f.base) + _f._result);
        }
      }
      return _result;
    }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<
          T1, F1 &, ftree &, T1 &, std::function<unsigned int(unsigned int)> &,
          ftree &, T1 &>
    T1 ftree_rec(T1 f, F1 &&f0) const {
      const ftree *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const ftree *_self;
      };

      /// _After_FNode: saves [_s0, d_a2, d_a1, d_a0], dispatches next recursive
      /// call.
      struct _After_FNode {
        ftree *_s0;
        ftree d_a2;
        std::function<unsigned int(unsigned int)> d_a1;
        ftree d_a0;
      };

      /// _Combine_FNode: receives partial results, combines with _result from
      /// final call.
      struct _Combine_FNode {
        T1 _result;
        ftree d_a2;
        std::function<unsigned int(unsigned int)> d_a1;
        ftree d_a0;
      };

      using _Frame = std::variant<_Enter, _After_FNode, _Combine_FNode>;
      T1 _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(8);
      _stack.emplace_back(_Enter{_self});
      /// Loopified ftree_rec: _Enter -> _After_FNode -> _Combine_FNode.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const ftree *_self = _f._self;
          auto &&_sv = *(_self);
          if (std::holds_alternative<typename ftree::FLeaf>(_sv.v())) {
            _result = f;
          } else {
            const auto &[d_a0, d_a1, d_a2] =
                std::get<typename ftree::FNode>(_sv.v());
            _stack.emplace_back(
                _After_FNode{d_a0.get(), *(d_a2), std::move(d_a1), *(d_a0)});
            _stack.emplace_back(_Enter{d_a2.get()});
          }
        } else if (std::holds_alternative<_After_FNode>(_frame)) {
          auto _f = std::move(std::get<_After_FNode>(_frame));
          _stack.emplace_back(_Combine_FNode{_result, std::move(_f.d_a2),
                                             std::move(_f.d_a1),
                                             std::move(_f.d_a0)});
          _stack.emplace_back(_Enter{_f._s0});
        } else {
          auto _f = std::move(std::get<_Combine_FNode>(_frame));
          _result = f0(_f.d_a0, _result, _f.d_a1, _f.d_a2, _f._result);
        }
      }
      return _result;
    }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<
          T1, F1 &, ftree &, T1 &, std::function<unsigned int(unsigned int)> &,
          ftree &, T1 &>
    T1 ftree_rect(T1 f, F1 &&f0) const {
      const ftree *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const ftree *_self;
      };

      /// _After_FNode: saves [_s0, d_a2, d_a1, d_a0], dispatches next recursive
      /// call.
      struct _After_FNode {
        ftree *_s0;
        ftree d_a2;
        std::function<unsigned int(unsigned int)> d_a1;
        ftree d_a0;
      };

      /// _Combine_FNode: receives partial results, combines with _result from
      /// final call.
      struct _Combine_FNode {
        T1 _result;
        ftree d_a2;
        std::function<unsigned int(unsigned int)> d_a1;
        ftree d_a0;
      };

      using _Frame = std::variant<_Enter, _After_FNode, _Combine_FNode>;
      T1 _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(8);
      _stack.emplace_back(_Enter{_self});
      /// Loopified ftree_rect: _Enter -> _After_FNode -> _Combine_FNode.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const ftree *_self = _f._self;
          auto &&_sv = *(_self);
          if (std::holds_alternative<typename ftree::FLeaf>(_sv.v())) {
            _result = f;
          } else {
            const auto &[d_a0, d_a1, d_a2] =
                std::get<typename ftree::FNode>(_sv.v());
            _stack.emplace_back(
                _After_FNode{d_a0.get(), *(d_a2), std::move(d_a1), *(d_a0)});
            _stack.emplace_back(_Enter{d_a2.get()});
          }
        } else if (std::holds_alternative<_After_FNode>(_frame)) {
          auto _f = std::move(std::get<_After_FNode>(_frame));
          _stack.emplace_back(_Combine_FNode{_result, std::move(_f.d_a2),
                                             std::move(_f.d_a1),
                                             std::move(_f.d_a0)});
          _stack.emplace_back(_Enter{_f._s0});
        } else {
          auto _f = std::move(std::get<_Combine_FNode>(_frame));
          _result = f0(_f.d_a0, _result, _f.d_a1, _f.d_a2, _f._result);
        }
      }
      return _result;
    }
  };

  static ftree tree_to_ftree(const tree &t);
  static inline const unsigned int test_ftree = []() {
    tree t = tree::node(tree::node(tree::leaf(), 3u, tree::leaf()), 7u,
                        tree::node(tree::leaf(), 11u, tree::leaf()));
    ftree ft = tree_to_ftree(std::move(t));
    return std::move(ft).eval_ftree(100u);
  }();
  /// TEST 6: Flatten a tree of lists into a single list,
  /// where each list element is a closure.
  static mylist<std::function<unsigned int(unsigned int)>>
  flatten_tree_fns(const tree &t);
  static inline const unsigned int test_flatten_fns = []() {
    tree t = tree::node(tree::node(tree::leaf(), 3u, tree::leaf()), 7u,
                        tree::node(tree::leaf(), 11u, tree::leaf()));
    mylist<std::function<unsigned int(unsigned int)>> fns =
        flatten_tree_fns(std::move(t));
    return sum_list(std::move(fns).template map_list<unsigned int>(
        [](const std::function<unsigned int(unsigned int)> f) {
          return f(1u);
        }));
  }();
};

#endif // INCLUDED_MEM_SAFETY_PROBE13
