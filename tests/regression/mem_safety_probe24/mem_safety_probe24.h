#ifndef INCLUDED_MEM_SAFETY_PROBE24
#define INCLUDED_MEM_SAFETY_PROBE24

#include <functional>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

struct MemSafetyProbe24 {
  /// Probe 24: Complex value-type interactions.
  ///
  /// Attack vectors:
  /// 1. Use-after-move in pair/constructor arguments: if Crane
  /// generates std::move(t) alongside t.field in the same expression
  /// 2. Rose-tree with list children: complex ownership when
  /// flattening nested value types
  /// 3. Multi-use of owned variable in constructor calls: t used in
  /// both constructor position AND field-access position
  /// 4. Value-type stored in option/pair then accessed through
  /// projection — tests whether projections access moved-from data
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

    /// TEST 6: Store a tree AND its sum in a pair, then transform
    /// both. Tests that clone is independent of original.
    unsigned int clone_and_transform() const {
      std::pair<tree, unsigned int> p =
          std::make_pair(*(this), (*(this)).tree_sum());
      tree t2 = p.first;
      unsigned int s = p.second;
      tree t3 = std::move(t2).map_tree(
          [=](const unsigned int n) mutable { return (n + s); });
      return std::move(t3).tree_sum();
    }

    /// TEST 5: Nested value type — list of trees stored in a tree-like
    /// structure. Tests clone correctness and ownership for nested types.
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
          auto &&_sv = *(_self);
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

    /// TEST 4: Recursive function where result uses BOTH t (for return)
    /// and t's children (through recursive calls) — not loopified because
    /// return type is pair. Tests use-after-move in make_pair.
    std::pair<tree, unsigned int> tag_tree() const {
      const tree *_self = this;
      auto &&_sv = *(_self);
      if (std::holds_alternative<typename tree::Leaf>(_sv.v())) {
        return std::make_pair(tree::leaf(), 0u);
      } else {
        const auto &[d_a0, d_a1, d_a2] = std::get<typename tree::Node>(_sv.v());
        std::pair<tree, unsigned int> pl = (*(d_a0)).tag_tree();
        std::pair<tree, unsigned int> pr = (*(d_a2)).tag_tree();
        return std::make_pair(*(_self), ((d_a1 + pl.second) + pr.second));
      }
    }

    /// TEST 3: Triple use of t in one expression.
    std::pair<std::pair<tree, tree>, unsigned int> triple_use() const {
      return std::make_pair(std::make_pair(*(this), *(this)),
                            (*(this)).tree_sum());
    }

    /// TEST 2: Pair where BOTH elements use t, one as value
    /// and one through a function.
    std::pair<tree, unsigned int> pair_self() const {
      return std::make_pair(*(this), (*(this)).tree_sum());
    }

    /// TEST 1: Variable used as BOTH whole value AND for field access
    /// in the same constructor. In C++, tree::node(t, tree_sum(t), Leaf)
    /// where t must be cloned and tree_sum accesses t's children.
    tree self_annotate() const {
      return tree::node(*(this), (*(this)).tree_sum(), tree::leaf());
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
        this->d_v_ =
            Mycons{t_A(d_a0),
                   d_a1 ? std::make_unique<MemSafetyProbe24::mylist<t_A>>(*d_a1)
                        : nullptr};
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
  static inline const unsigned int test_self_annotate =
      tree::node(tree::leaf(), 5u, tree::leaf()).self_annotate().tree_sum();
  static inline const unsigned int test_pair_self = []() {
    std::pair<tree, unsigned int> p =
        tree::node(tree::node(tree::leaf(), 3u, tree::leaf()), 7u,
                   tree::node(tree::leaf(), 11u, tree::leaf()))
            .pair_self();
    return (p.first.tree_sum() + p.second);
  }();
  static inline const unsigned int test_triple_use = []() {
    std::pair<std::pair<tree, tree>, unsigned int> p =
        tree::node(tree::leaf(), 5u, tree::leaf()).triple_use();
    return (((p.first).first.tree_sum() + (p.first).second.tree_sum()) +
            p.second);
  }();
  static inline const unsigned int test_tag_tree = []() {
    std::pair<tree, unsigned int> p =
        tree::node(tree::node(tree::leaf(), 2u, tree::leaf()), 5u,
                   tree::node(tree::leaf(), 8u, tree::leaf()))
            .tag_tree();
    return (p.first.tree_sum() + p.second);
  }();
  static mylist<unsigned int> tree_to_list(const tree &t);
  static inline const unsigned int test_nested_ops = []() {
    tree t = tree::node(tree::node(tree::leaf(), 3u, tree::leaf()), 7u,
                        tree::node(tree::leaf(), 11u, tree::leaf()));
    tree doubled = t.map_tree([](const unsigned int n) { return (n * 2u); });
    mylist<unsigned int> flat = tree_to_list(std::move(doubled));
    return (sum_list(std::move(flat)) + std::move(t).tree_sum());
  }();
  static inline const unsigned int test_clone_and_transform =
      tree::node(tree::node(tree::leaf(), 1u, tree::leaf()), 2u,
                 tree::node(tree::leaf(), 3u, tree::leaf()))
          .clone_and_transform();
  /// TEST 7: Build a tree from a list, using accumulated state.
  /// Tests interaction between list recursion and tree construction.
  static tree list_to_tree(const mylist<unsigned int> &l, tree acc);
  static inline const unsigned int test_list_to_tree =
      list_to_tree(mylist<unsigned int>::mycons(
                       1u, mylist<unsigned int>::mycons(
                               2u, mylist<unsigned int>::mycons(
                                       3u, mylist<unsigned int>::mynil()))),
                   tree::leaf())
          .tree_sum();
  /// TEST 8: Zip two trees, producing a list of pairs.
  /// Both trees are destructured simultaneously.
  static mylist<std::pair<unsigned int, unsigned int>>
  zip_trees(const tree &t1, const tree &t2);
  static inline const unsigned int test_zip_trees = sum_list([]() {
    mylist<std::pair<unsigned int, unsigned int>> pairs =
        zip_trees(tree::node(tree::node(tree::leaf(), 1u, tree::leaf()), 2u,
                             tree::node(tree::leaf(), 3u, tree::leaf())),
                  tree::node(tree::node(tree::leaf(), 10u, tree::leaf()), 20u,
                             tree::node(tree::leaf(), 30u, tree::leaf())));
    std::function<unsigned int(std::pair<unsigned int, unsigned int>)>
        add_pair = [](const std::pair<unsigned int, unsigned int> &p) {
          return (p.first + p.second);
        };
    if (std::holds_alternative<
            typename mylist<std::pair<unsigned int, unsigned int>>::Mynil>(
            pairs.v_mut())) {
      return mylist<unsigned int>::mycons(0u, mylist<unsigned int>::mynil());
    } else {
      auto &[d_a0, d_a1] = std::get<
          typename mylist<std::pair<unsigned int, unsigned int>>::Mycons>(
          pairs.v_mut());
      auto &&_sv0 = *(d_a1);
      if (std::holds_alternative<
              typename mylist<std::pair<unsigned int, unsigned int>>::Mynil>(
              _sv0.v())) {
        return mylist<unsigned int>::mycons(add_pair(d_a0),
                                            mylist<unsigned int>::mynil());
      } else {
        const auto &[d_a00, d_a10] = std::get<
            typename mylist<std::pair<unsigned int, unsigned int>>::Mycons>(
            _sv0.v());
        auto &&_sv1 = *(d_a10);
        if (std::holds_alternative<
                typename mylist<std::pair<unsigned int, unsigned int>>::Mynil>(
                _sv1.v())) {
          return mylist<unsigned int>::mycons(
              add_pair(d_a0),
              mylist<unsigned int>::mycons(add_pair(d_a00),
                                           mylist<unsigned int>::mynil()));
        } else {
          const auto &[d_a01, d_a11] = std::get<
              typename mylist<std::pair<unsigned int, unsigned int>>::Mycons>(
              _sv1.v());
          return mylist<unsigned int>::mycons(
              add_pair(d_a0),
              mylist<unsigned int>::mycons(
                  add_pair(d_a00),
                  mylist<unsigned int>::mycons(add_pair(d_a01),
                                               mylist<unsigned int>::mynil())));
        }
      }
    }
  }());
};

#endif // INCLUDED_MEM_SAFETY_PROBE24
