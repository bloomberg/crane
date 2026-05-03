#ifndef INCLUDED_MEM_SAFETY_PROBE15
#define INCLUDED_MEM_SAFETY_PROBE15

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

struct MemSafetyProbe15 {
  /// Probe 15: Focused on finding RUNTIME memory safety bugs.
  ///
  /// Key attack vectors:
  /// 1. Flatten optimization: v_mut() + unique_ptr field moves
  /// in loopified Enter frames
  /// 2. Value-type tree where subtrees are read AFTER being
  /// potentially moved by the frame push
  /// 3. Closures that capture match bindings from owned matches
  /// 4. Deep trees with many unique_ptr indirections
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

    /// TEST 7: Two passes over the same tree.
    /// First pass collects values, second pass computes sums.
    /// Tests that the tree is not consumed by the first pass.
    unsigned int two_pass() const {
      mylist<unsigned int> vals = flatten(*(this));
      mylist<unsigned int> sums = subtree_sums(*(this));
      return (sum_list(std::move(vals)) + sum_list(std::move(sums)));
    }

    /// TEST 4: Tree zipping — combine two trees into one.
    tree zip_trees(tree t2) const {
      const tree *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const tree *_self;
        tree t2;
      };

      /// _After_Node: saves [_s0, d_a00, _s2], dispatches next recursive call.
      struct _After_Node {
        tree *_s0;
        tree d_a00;
        unsigned int _s2;
      };

      /// _Combine_Node: receives partial results, combines with _result from
      /// final call.
      struct _Combine_Node {
        tree _result;
        unsigned int _s1;
      };

      using _Frame = std::variant<_Enter, _After_Node, _Combine_Node>;
      tree _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(16);
      _stack.emplace_back(_Enter{_self, t2});
      /// Loopified zip_trees: _Enter -> _After_Node -> _Combine_Node.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const tree *_self = _f._self;
          tree t2 = std::move(_f.t2);
          auto &&_sv = *(_self);
          if (std::holds_alternative<typename tree::Leaf>(_sv.v())) {
            _result = std::move(t2);
          } else {
            const auto &[d_a0, d_a1, d_a2] =
                std::get<typename tree::Node>(_sv.v());
            if (std::holds_alternative<typename tree::Leaf>(t2.v_mut())) {
              _result = *(_self);
            } else {
              auto &[d_a00, d_a10, d_a20] =
                  std::get<typename tree::Node>(t2.v_mut());
              _stack.emplace_back(
                  _After_Node{d_a0.get(), *(d_a00), (d_a1 + d_a10)});
              _stack.emplace_back(_Enter{d_a2.get(), std::move(*(d_a20))});
            }
          }
        } else if (std::holds_alternative<_After_Node>(_frame)) {
          auto _f = std::move(std::get<_After_Node>(_frame));
          _stack.emplace_back(_Combine_Node{std::move(_result), _f._s2});
          _stack.emplace_back(_Enter{_f._s0, std::move(_f.d_a00)});
        } else {
          auto _f = std::move(std::get<_Combine_Node>(_frame));
          _result = tree::node(_result, _f._s1, _f._result);
        }
      }
      return _result;
    }

    /// TEST 3: Tree mirror that uses both subtrees.
    tree mirror() const {
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
        tree _result;
        unsigned int d_a1;
      };

      using _Frame = std::variant<_Enter, _After_Node, _Combine_Node>;
      tree _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(16);
      _stack.emplace_back(_Enter{_self});
      /// Loopified mirror: _Enter -> _After_Node -> _Combine_Node.
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
            _stack.emplace_back(_After_Node{d_a2.get(), d_a1});
            _stack.emplace_back(_Enter{d_a0.get()});
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
      _stack.reserve(16);
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
      _stack.reserve(16);
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
      _stack.reserve(16);
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
                   d_a1 ? std::make_unique<MemSafetyProbe15::mylist<t_A>>(*d_a1)
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

    /// TEST 8: Map over a list, transforming each element.
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

    /// TEST 6: List reversal using accumulator.
    /// Tests owned parameter match optimization.
    mylist<t_A> rev_aux(mylist<t_A> acc) const {
      mylist<t_A> _result;
      const mylist *_loop_self = this;
      mylist<t_A> _loop_acc = std::move(acc);
      while (true) {
        auto &&_sv = *(_loop_self);
        if (std::holds_alternative<typename mylist<t_A>::Mynil>(_sv.v())) {
          _result = std::move(_loop_acc);
          break;
        } else {
          const auto &[d_a0, d_a1] =
              std::get<typename mylist<t_A>::Mycons>(_sv.v());
          _loop_self = d_a1.get();
          _loop_acc = mylist<t_A>::mycons(d_a0, std::move(_loop_acc));
        }
      }
      return _result;
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
      _stack.reserve(16);
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

    mylist<t_A> myapp(mylist<t_A> l2) const {
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
      _stack.reserve(16);
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
      _stack.reserve(16);
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
  /// TEST 1: Tree flattening where left subtree is used AFTER
  /// right subtree recursive call.
  /// In loopified code, the Enter frame for the right subtree
  /// may move the left subtree's pointer.
  static mylist<unsigned int> flatten(const tree &t);
  static inline const unsigned int test_flatten = []() {
    tree t =
        tree::node(tree::node(tree::node(tree::leaf(), 1u, tree::leaf()), 2u,
                              tree::node(tree::leaf(), 3u, tree::leaf())),
                   4u,
                   tree::node(tree::node(tree::leaf(), 5u, tree::leaf()), 6u,
                              tree::node(tree::leaf(), 7u, tree::leaf())));
    return sum_list(flatten(std::move(t)));
  }();
  /// TEST 2: Tree to list where each element is the sum of
  /// its subtree. Uses both subtrees for computation AND recursion.
  static mylist<unsigned int> subtree_sums(const tree &t);
  static inline const unsigned int test_subtree_sums = []() {
    tree t = tree::node(tree::node(tree::leaf(), 3u, tree::leaf()), 7u,
                        tree::node(tree::leaf(), 11u, tree::leaf()));
    return sum_list(subtree_sums(std::move(t)));
  }();
  static inline const unsigned int test_mirror = []() {
    tree t = tree::node(tree::node(tree::leaf(), 1u,
                                   tree::node(tree::leaf(), 2u, tree::leaf())),
                        3u, tree::node(tree::leaf(), 4u, tree::leaf()));
    return std::move(t).mirror().tree_sum();
  }();
  static inline const unsigned int test_zip = []() {
    tree t1 = tree::node(tree::node(tree::leaf(), 1u, tree::leaf()), 10u,
                         tree::node(tree::leaf(), 2u, tree::leaf()));
    tree t2 = tree::node(tree::node(tree::leaf(), 3u, tree::leaf()), 20u,
                         tree::node(tree::leaf(), 4u, tree::leaf()));
    return std::move(t1).zip_trees(std::move(t2)).tree_sum();
  }();
  /// TEST 5: Deep left-spine tree.
  /// Stresses the frame stack depth.
  static tree left_spine(const unsigned int n);
  static inline const unsigned int test_deep_spine =
      left_spine(100u).tree_sum();
  static inline const unsigned int test_rev = []() {
    mylist<unsigned int> l = mylist<unsigned int>::mycons(
        1u, mylist<unsigned int>::mycons(
                2u, mylist<unsigned int>::mycons(
                        3u, mylist<unsigned int>::mycons(
                                4u, mylist<unsigned int>::mynil()))));
    mylist<unsigned int> r =
        std::move(l).rev_aux(mylist<unsigned int>::mynil());
    return sum_list(std::move(r));
  }();
  static inline const unsigned int test_two_pass =
      tree::node(tree::node(tree::leaf(), 3u, tree::leaf()), 7u,
                 tree::node(tree::leaf(), 11u, tree::leaf()))
          .two_pass();
  static inline const unsigned int test_map = []() {
    mylist<unsigned int> l = mylist<unsigned int>::mycons(
        10u, mylist<unsigned int>::mycons(
                 20u, mylist<unsigned int>::mycons(
                          30u, mylist<unsigned int>::mynil())));
    mylist<unsigned int> l2 = std::move(l).template map_list<unsigned int>(
        [](const unsigned int x) { return (x + 1u); });
    return sum_list(std::move(l2));
  }();
  /// TEST 9: Build a large tree and verify all values are preserved.
  static tree make_tree(const unsigned int n);
  static inline const unsigned int test_large_tree = make_tree(6u).tree_sum();
};

#endif // INCLUDED_MEM_SAFETY_PROBE15
