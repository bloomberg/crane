#ifndef INCLUDED_MEM_SAFETY_PROBE6
#define INCLUDED_MEM_SAFETY_PROBE6

#include <functional>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

struct MemSafetyProbe6 {
  /// These tests probe closures that capture RECURSIVE self-reference
  /// fields from match bindings. In C++, these fields are unique_ptr.
  /// A lambda capturing a unique_ptr by = fails (non-copyable).
  /// A lambda capturing by & would dangle if returned.
  /// Crane must pre-copy or clone the field.
  ///
  /// NOTE: All functions use nat as FIRST argument to avoid
  /// methodification bugs with curried return types.
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

    /// TEST 3: Closure returned from match that applies a function
    /// to the tail — forces unique_ptr access and HOF.
    template <typename T1, typename F0>
      requires std::is_invocable_r_v<T1, F0 &, t_A &>
    mylist<T1> mymap(F0 &&f) const {
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

    /// TEST 2: Closure from match that reconstructs using both
    /// a value field and a recursive field.
    mylist<t_A> head_and_tail(const unsigned int, const t_A &,
                              const t_A &) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename mylist<t_A>::Mynil>(_sv.v())) {
        return mylist<t_A>::mynil();
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename mylist<t_A>::Mycons>(_sv.v());
        return mylist<t_A>::mycons(d_a0, *(d_a1));
      }
    }

    /// TEST 1: Return a closure that uses the TAIL of the list.
    /// xs is a unique_ptr<mylist> field — the closure must clone it.
    unsigned int tail_adder(const unsigned int, const unsigned int n) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename mylist<t_A>::Mynil>(_sv.v())) {
        return n;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename mylist<t_A>::Mycons>(_sv.v());
        return ((*(d_a1)).length() + n);
      }
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
      _stack.emplace_back(_Enter(_self));
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
            _stack.emplace_back(_Resume_Mycons(1u));
            _stack.emplace_back(_Enter(d_a1.get()));
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

  static inline const unsigned int test_tail_adder = []() {
    mylist<unsigned int> l = mylist<unsigned int>::mycons(
        1u, mylist<unsigned int>::mycons(
                2u, mylist<unsigned int>::mycons(
                        3u, mylist<unsigned int>::mynil())));
    return std::move(l).tail_adder(0u, 100u);
  }();
  static inline const unsigned int test_head_and_tail = []() {
    return []() {
      mylist<unsigned int> l = mylist<unsigned int>::mycons(
          10u,
          mylist<unsigned int>::mycons(20u, mylist<unsigned int>::mynil()));
      std::function<mylist<unsigned int>(unsigned int)> f =
          [&](unsigned int _x0) -> mylist<unsigned int> {
        return std::move(l).head_and_tail(0u, 0u, _x0);
      };
      mylist<unsigned int> l2 = f(99u);
      return std::move(l2).length();
    }();
  }();

  /// f reconstructs the list 10, 20. length 10,20 = 2
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

    /// TEST 4: Return a closure that captures BOTH subtrees of a tree.
    /// Both l and r are unique_ptr fields.
    tree both_subtrees(const unsigned int, const bool x) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename tree::Leaf>(_sv.v())) {
        return tree::leaf();
      } else {
        const auto &[d_a0, d_a1, d_a2] = std::get<typename tree::Node>(_sv.v());
        if (x) {
          return *(d_a0);
        } else {
          return *(d_a2);
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

  template <typename F2>
    requires std::is_invocable_r_v<unsigned int, F2 &, unsigned int &>
  static mylist<unsigned int>
  tail_mapper(const unsigned int, const mylist<unsigned int> &l, F2 &&x) {
    if (std::holds_alternative<typename mylist<unsigned int>::Mynil>(l.v())) {
      return mylist<unsigned int>::mynil();
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename mylist<unsigned int>::Mycons>(l.v());
      return mylist<unsigned int>::mycons(
          d_a0, (*(d_a1)).template mymap<unsigned int>(x));
    }
  }

  static inline const unsigned int test_tail_mapper = []() {
    return []() {
      mylist<unsigned int> l = mylist<unsigned int>::mycons(
          1u, mylist<unsigned int>::mycons(
                  2u, mylist<unsigned int>::mycons(
                          3u, mylist<unsigned int>::mynil())));
      std::function<mylist<unsigned int>(
          std::function<unsigned int(unsigned int)>)>
          f = [&](std::function<unsigned int(unsigned int)> _x0)
          -> mylist<unsigned int> {
        return tail_mapper(0u, std::move(l), _x0);
      };
      mylist<unsigned int> l2 =
          f([](const unsigned int n) { return (n * 10u); });
      return std::move(l2).length();
    }();
  }();
  static inline const unsigned int test_both_subtrees = []() {
    return []() {
      tree t = tree::node(tree::node(tree::leaf(), 10u, tree::leaf()), 20u,
                          tree::node(tree::leaf(), 30u, tree::leaf()));
      std::function<tree(bool)> sel = [=](bool _x0) mutable -> tree {
        return t.both_subtrees(0u, _x0);
      };
      return (sel(true).tree_sum() + sel(false).tree_sum());
    }();
  }();
  /// TEST 5: Chain of closures each pre-computing from the tail.
  static mylist<std::function<unsigned int(unsigned int)>>
  build_chain(const mylist<unsigned int> &l);
  static unsigned int
  apply_chain(const mylist<std::function<unsigned int(unsigned int)>> &fns,
              const unsigned int x);
  static inline const unsigned int test_chain = []() {
    mylist<unsigned int> l = mylist<unsigned int>::mycons(
        10u, mylist<unsigned int>::mycons(
                 20u, mylist<unsigned int>::mycons(
                          30u, mylist<unsigned int>::mynil())));
    mylist<std::function<unsigned int(unsigned int)>> fns =
        build_chain(std::move(l));
    return apply_chain(std::move(fns), 0u);
  }();
  /// TEST 6: Closure captures tail, then tail is used again
  /// after the closure is created — tests double use.
  static unsigned int capture_and_reuse(const unsigned int _x,
                                        const mylist<unsigned int> &l);
  static inline const unsigned int test_capture_reuse = capture_and_reuse(
      0u, mylist<unsigned int>::mycons(
              5u, mylist<unsigned int>::mycons(
                      1u, mylist<unsigned int>::mycons(
                              2u, mylist<unsigned int>::mynil()))));
};

#endif // INCLUDED_MEM_SAFETY_PROBE6
