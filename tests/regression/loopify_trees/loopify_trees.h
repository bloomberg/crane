#ifndef INCLUDED_LOOPIFY_TREES
#define INCLUDED_LOOPIFY_TREES

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
    std::unique_ptr<List<A>> l;
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

  List(const List<A> &_other) : v_(std::move(_other.clone().v_)) {}

  List(List<A> &&_other) noexcept : v_(std::move(_other.v_)) {}

  List<A> &operator=(const List<A> &_other) {
    v_ = std::move(_other.clone().v_);
    return *this;
  }

  List<A> &operator=(List<A> &&_other) noexcept {
    v_ = std::move(_other.v_);
    return *this;
  }

  // ACCESSORS
  List<A> clone() const {
    List<A> _out{};

    struct _CloneFrame {
      const List<A> *_src;
      List<A> *_dst;
    };

    std::vector<_CloneFrame> _stack{};
    _stack.reserve(8);
    _stack.push_back({this, &_out});
    while (!_stack.empty()) {
      auto _frame = _stack.back();
      _stack.pop_back();
      const List<A> *_src = _frame._src;
      List<A> *_dst = _frame._dst;
      if (std::holds_alternative<Nil>(_src->v())) {
        _dst->v_ = Nil{};
      } else {
        const auto &_alt = std::get<Cons>(_src->v());
        _dst->v_ = Cons{_alt.a, _alt.l ? std::make_unique<List<A>>() : nullptr};
        auto &_dst_alt = std::get<Cons>(_dst->v_);
        if (_alt.l) {
          _stack.push_back({_alt.l.get(), _dst_alt.l.get()});
        }
      }
    }
    return _out;
  }

  // CREATORS
  template <typename _U> explicit List(const List<_U> &_other) {
    if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
      this->v_ = Nil{};
    } else {
      const auto &[a, l] = std::get<typename List<_U>::Cons>(_other.v());
      this->v_ = Cons{A(a), l ? std::make_unique<List<A>>(*l) : nullptr};
    }
  }

  static List<A> nil() { return List(Nil{}); }

  static List<A> cons(A a, List<A> l) {
    return List(Cons{std::move(a), std::make_unique<List<A>>(std::move(l))});
  }

  // MANIPULATORS
  ~List() {
    std::vector<std::unique_ptr<List<A>>> _stack{};
    _stack.reserve(8);
    auto _drain = [&](List<A> &_node) {
      if (std::holds_alternative<Cons>(_node.v_)) {
        auto &_alt = std::get<Cons>(_node.v_);
        if (_alt.l) {
          _stack.push_back(std::move(_alt.l));
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

  List<A> app(List<A> m) const {
    std::unique_ptr<List<A>> _head{};
    std::unique_ptr<List<A>> *_write = &_head;
    const List *_loop_self = this;
    List<A> _loop_m = std::move(m);
    while (true) {
      auto &&_sv = *_loop_self;
      if (std::holds_alternative<typename List<A>::Nil>(_sv.v())) {
        *_write = std::make_unique<List<A>>(std::move(_loop_m));
        break;
      } else {
        const auto &[a0, a1] = std::get<typename List<A>::Cons>(_sv.v());
        auto _cell =
            std::make_unique<List<A>>(typename List<A>::Cons(a0, nullptr));
        *_write = std::move(_cell);
        _write = &std::get<typename List<A>::Cons>((*_write)->v_mut()).l;
        _loop_self = a1.get();
        continue;
      }
    }
    return std::move(*_head);
  }
};

/// Consolidated UNIQUE tree algorithms - domain-specific tree operations.
struct LoopifyTrees {
  template <typename A> struct tree {
    // TYPES
    struct Leaf {};

    struct Node {
      std::unique_ptr<tree<A>> l;
      A x;
      std::unique_ptr<tree<A>> r;
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

    tree(const tree<A> &_other) : v_(std::move(_other.clone().v_)) {}

    tree(tree<A> &&_other) noexcept : v_(std::move(_other.v_)) {}

    tree<A> &operator=(const tree<A> &_other) {
      v_ = std::move(_other.clone().v_);
      return *this;
    }

    tree<A> &operator=(tree<A> &&_other) noexcept {
      v_ = std::move(_other.v_);
      return *this;
    }

    // ACCESSORS
    tree<A> clone() const {
      tree<A> _out{};

      struct _CloneFrame {
        const tree<A> *_src;
        tree<A> *_dst;
      };

      std::vector<_CloneFrame> _stack{};
      _stack.reserve(8);
      _stack.push_back({this, &_out});
      while (!_stack.empty()) {
        auto _frame = _stack.back();
        _stack.pop_back();
        const tree<A> *_src = _frame._src;
        tree<A> *_dst = _frame._dst;
        if (std::holds_alternative<Leaf>(_src->v())) {
          _dst->v_ = Leaf{};
        } else {
          const auto &_alt = std::get<Node>(_src->v());
          _dst->v_ =
              Node{_alt.l ? std::make_unique<tree<A>>() : nullptr, _alt.x,
                   _alt.r ? std::make_unique<tree<A>>() : nullptr};
          auto &_dst_alt = std::get<Node>(_dst->v_);
          if (_alt.l) {
            _stack.push_back({_alt.l.get(), _dst_alt.l.get()});
          }
          if (_alt.r) {
            _stack.push_back({_alt.r.get(), _dst_alt.r.get()});
          }
        }
      }
      return _out;
    }

    // CREATORS
    template <typename _U> explicit tree(const tree<_U> &_other) {
      if (std::holds_alternative<typename tree<_U>::Leaf>(_other.v())) {
        this->v_ = Leaf{};
      } else {
        const auto &[l, x, r] = std::get<typename tree<_U>::Node>(_other.v());
        this->v_ = Node{l ? std::make_unique<tree<A>>(*l) : nullptr, A(x),
                        r ? std::make_unique<tree<A>>(*r) : nullptr};
      }
    }

    static tree<A> leaf() { return tree(Leaf{}); }

    static tree<A> node(tree<A> l, A x, tree<A> r) {
      return tree(Node{std::make_unique<tree<A>>(std::move(l)), std::move(x),
                       std::make_unique<tree<A>>(std::move(r))});
    }

    // MANIPULATORS
    ~tree() {
      std::vector<std::unique_ptr<tree<A>>> _stack{};
      _stack.reserve(8);
      auto _drain = [&](tree<A> &_node) {
        if (std::holds_alternative<Node>(_node.v_)) {
          auto &_alt = std::get<Node>(_node.v_);
          if (_alt.l) {
            _stack.push_back(std::move(_alt.l));
          }
          if (_alt.r) {
            _stack.push_back(std::move(_alt.r));
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

    /// tree_map f t applies f to all values in tree.
    template <typename T1, typename F0>
      requires std::is_invocable_r_v<T1, F0 &, A &>
    tree<T1> tree_map(F0 &&f) const {
      const tree *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const tree *_self;
      };

      /// _After_Node: saves [_s0, a1], dispatches next recursive call.
      struct _After_Node {
        tree<A> *_s0;
        decltype(std::declval<F0 &>()(std::declval<A &>())) a1;
      };

      /// _Combine_Node: receives partial results, combines with _result from
      /// final call.
      struct _Combine_Node {
        tree<T1> _result;
        decltype(std::declval<F0 &>()(std::declval<A &>())) a1;
      };

      using _Frame = std::variant<_Enter, _After_Node, _Combine_Node>;
      tree<T1> _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(8);
      _stack.emplace_back(_Enter{_self});
      /// Loopified tree_map: _Enter -> _After_Node -> _Combine_Node.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const tree *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename tree<A>::Leaf>(_sv.v())) {
            _result = tree<T1>::leaf();
          } else {
            const auto &[a0, a1, a2] =
                std::get<typename tree<A>::Node>(_sv.v());
            _stack.emplace_back(_After_Node{a0.get(), f(a1)});
            _stack.emplace_back(_Enter{a2.get()});
          }
        } else if (std::holds_alternative<_After_Node>(_frame)) {
          auto _f = std::move(std::get<_After_Node>(_frame));
          _stack.emplace_back(_Combine_Node{std::move(_result), _f.a1});
          _stack.emplace_back(_Enter{_f._s0});
        } else {
          auto _f = std::move(std::get<_Combine_Node>(_frame));
          _result = tree<T1>::node(_result, _f.a1, _f._result);
        }
      }
      return _result;
    }

    /// mirror_equal t1 t2 checks if t1 and t2 are mirror images.
    bool mirror_equal(const tree<A> &t2) const {
      const tree *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const tree *_self;
        const tree<A> *t2;
      };

      /// _After_Node: saves [_s0, a20, _s2], dispatches next recursive call.
      struct _After_Node {
        tree<A> *_s0;
        const tree<A> *a20;
        decltype(true) _s2;
      };

      /// _Combine_Node: receives partial results, combines with _result from
      /// final call.
      struct _Combine_Node {
        bool _result;
        decltype(true) _s1;
      };

      using _Frame = std::variant<_Enter, _After_Node, _Combine_Node>;
      bool _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(8);
      _stack.emplace_back(_Enter{_self, &t2});
      /// Loopified mirror_equal: _Enter -> _After_Node -> _Combine_Node.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const tree *_self = _f._self;
          const tree<A> &t2 = *_f.t2;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename tree<A>::Leaf>(_sv.v())) {
            if (std::holds_alternative<typename tree<A>::Leaf>(t2.v())) {
              _result = true;
            } else {
              _result = false;
            }
          } else {
            const auto &[a0, a1, a2] =
                std::get<typename tree<A>::Node>(_sv.v());
            if (std::holds_alternative<typename tree<A>::Leaf>(t2.v())) {
              _result = false;
            } else {
              const auto &[a00, a10, a20] =
                  std::get<typename tree<A>::Node>(t2.v());
              _stack.emplace_back(_After_Node{a0.get(), a20.get(), true});
              _stack.emplace_back(_Enter{a2.get(), a00.get()});
            }
          }
        } else if (std::holds_alternative<_After_Node>(_frame)) {
          auto _f = std::move(std::get<_After_Node>(_frame));
          _stack.emplace_back(_Combine_Node{_result, _f._s2});
          _stack.emplace_back(_Enter{_f._s0, _f.a20});
        } else {
          auto _f = std::move(std::get<_Combine_Node>(_frame));
          _result = ((_result && _f._result) && _f._s1);
        }
      }
      return _result;
    }

    /// tree_to_list inorder traversal.
    List<A> tree_to_list() const {
      const tree *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const tree *_self;
      };

      /// _After_Node: saves [_s0, a1], dispatches next recursive call.
      struct _After_Node {
        tree<A> *_s0;
        A a1;
      };

      /// _Combine_Node: receives partial results, combines with _result from
      /// final call.
      struct _Combine_Node {
        List<A> _result;
        A a1;
      };

      using _Frame = std::variant<_Enter, _After_Node, _Combine_Node>;
      List<A> _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(8);
      _stack.emplace_back(_Enter{_self});
      /// Loopified tree_to_list: _Enter -> _After_Node -> _Combine_Node.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const tree *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename tree<A>::Leaf>(_sv.v())) {
            _result = List<A>::nil();
          } else {
            const auto &[a0, a1, a2] =
                std::get<typename tree<A>::Node>(_sv.v());
            _stack.emplace_back(_After_Node{a0.get(), a1});
            _stack.emplace_back(_Enter{a2.get()});
          }
        } else if (std::holds_alternative<_After_Node>(_frame)) {
          auto _f = std::move(std::get<_After_Node>(_frame));
          _stack.emplace_back(_Combine_Node{std::move(_result), _f.a1});
          _stack.emplace_back(_Enter{_f._s0});
        } else {
          auto _f = std::move(std::get<_Combine_Node>(_frame));
          _result = _result.app(List<A>::cons(_f.a1, _f._result));
        }
      }
      return _result;
    }

    /// count_leaves counts leaf nodes.
    uint64_t count_leaves() const {
      const tree *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const tree *_self;
      };

      /// _After_Node: saves [_s0], dispatches next recursive call.
      struct _After_Node {
        tree<A> *_s0;
      };

      /// _Combine_Node: receives partial results, combines with _result from
      /// final call.
      struct _Combine_Node {
        uint64_t _result;
      };

      using _Frame = std::variant<_Enter, _After_Node, _Combine_Node>;
      uint64_t _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(8);
      _stack.emplace_back(_Enter{_self});
      /// Loopified count_leaves: _Enter -> _After_Node -> _Combine_Node.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const tree *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename tree<A>::Leaf>(_sv.v())) {
            _result = UINT64_C(1);
          } else {
            const auto &[a0, a1, a2] =
                std::get<typename tree<A>::Node>(_sv.v());
            _stack.emplace_back(_After_Node{a0.get()});
            _stack.emplace_back(_Enter{a2.get()});
          }
        } else if (std::holds_alternative<_After_Node>(_frame)) {
          auto _f = std::move(std::get<_After_Node>(_frame));
          _stack.emplace_back(_Combine_Node{_result});
          _stack.emplace_back(_Enter{_f._s0});
        } else {
          auto _f = std::move(std::get<_Combine_Node>(_frame));
          _result = (_result + _f._result);
        }
      }
      return _result;
    }

    A rightmost(A default0) const {
      const tree *_loop_self = this;
      while (true) {
        auto &&_sv = *_loop_self;
        if (std::holds_alternative<typename tree<A>::Leaf>(_sv.v())) {
          return default0;
        } else {
          const auto &[a0, a1, a2] = std::get<typename tree<A>::Node>(_sv.v());
          auto &&_sv = *a2;
          if (std::holds_alternative<typename tree<A>::Leaf>(_sv.v())) {
            return a1;
          } else {
            _loop_self = a2.get();
          }
        }
      }
    }

    /// leftmost/rightmost finds edge values.
    A leftmost(A default0) const {
      const tree *_loop_self = this;
      while (true) {
        auto &&_sv = *_loop_self;
        if (std::holds_alternative<typename tree<A>::Leaf>(_sv.v())) {
          return default0;
        } else {
          const auto &[a0, a1, a2] = std::get<typename tree<A>::Node>(_sv.v());
          auto &&_sv = *a0;
          if (std::holds_alternative<typename tree<A>::Leaf>(_sv.v())) {
            return a1;
          } else {
            _loop_self = a0.get();
          }
        }
      }
    }

    /// same_shape tests structural equality.
    template <typename T1> bool same_shape(const tree<T1> &t2) const {
      const tree *_self = this;
      auto &&_sv = *_self;
      if (std::holds_alternative<typename tree<A>::Leaf>(_sv.v())) {
        if (std::holds_alternative<typename tree<T1>::Leaf>(t2.v())) {
          return true;
        } else {
          return false;
        }
      } else {
        const auto &[a0, a1, a2] = std::get<typename tree<A>::Node>(_sv.v());
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
      const tree *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const tree *_self;
      };

      /// _After_Node: saves [_s0, a1], dispatches next recursive call.
      struct _After_Node {
        tree<A> *_s0;
        A a1;
      };

      /// _Combine_Node: receives partial results, combines with _result from
      /// final call.
      struct _Combine_Node {
        tree<A> _result;
        A a1;
      };

      using _Frame = std::variant<_Enter, _After_Node, _Combine_Node>;
      tree<A> _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(8);
      _stack.emplace_back(_Enter{_self});
      /// Loopified mirror: _Enter -> _After_Node -> _Combine_Node.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const tree *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename tree<A>::Leaf>(_sv.v())) {
            _result = tree<A>::leaf();
          } else {
            const auto &[a0, a1, a2] =
                std::get<typename tree<A>::Node>(_sv.v());
            _stack.emplace_back(_After_Node{a2.get(), a1});
            _stack.emplace_back(_Enter{a0.get()});
          }
        } else if (std::holds_alternative<_After_Node>(_frame)) {
          auto _f = std::move(std::get<_After_Node>(_frame));
          _stack.emplace_back(_Combine_Node{std::move(_result), _f.a1});
          _stack.emplace_back(_Enter{_f._s0});
        } else {
          auto _f = std::move(std::get<_Combine_Node>(_frame));
          _result = tree<A>::node(_result, _f.a1, _f._result);
        }
      }
      return _result;
    }

    uint64_t tree_size() const {
      const tree *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const tree *_self;
      };

      /// _After_Node: saves [_s0], dispatches next recursive call.
      struct _After_Node {
        tree<A> *_s0;
      };

      /// _Combine_Node: receives partial results, combines with _result from
      /// final call.
      struct _Combine_Node {
        uint64_t _result;
      };

      using _Frame = std::variant<_Enter, _After_Node, _Combine_Node>;
      uint64_t _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(8);
      _stack.emplace_back(_Enter{_self});
      /// Loopified tree_size: _Enter -> _After_Node -> _Combine_Node.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const tree *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename tree<A>::Leaf>(_sv.v())) {
            _result = UINT64_C(0);
          } else {
            const auto &[a0, a1, a2] =
                std::get<typename tree<A>::Node>(_sv.v());
            _stack.emplace_back(_After_Node{a0.get()});
            _stack.emplace_back(_Enter{a2.get()});
          }
        } else if (std::holds_alternative<_After_Node>(_frame)) {
          auto _f = std::move(std::get<_After_Node>(_frame));
          _stack.emplace_back(_Combine_Node{_result});
          _stack.emplace_back(_Enter{_f._s0});
        } else {
          auto _f = std::move(std::get<_Combine_Node>(_frame));
          _result = ((_result + _f._result) + 1);
        }
      }
      return _result;
    }

    uint64_t tree_height() const {
      const tree *_self = this;
      auto &&_sv = *_self;
      if (std::holds_alternative<typename tree<A>::Leaf>(_sv.v())) {
        return UINT64_C(0);
      } else {
        const auto &[a0, a1, a2] = std::get<typename tree<A>::Node>(_sv.v());
        uint64_t lh = a0->tree_height();
        uint64_t rh = a2->tree_height();
        return ((lh <= rh ? rh : lh) + 1);
      }
    }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, tree<A> &, T1 &, A &, tree<A> &,
                                     T1 &>
    T1 tree_rec(T1 f, F1 &&f0) const {
      const tree *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const tree *_self;
      };

      /// _After_Node: saves [_s0, a2, a1, a0], dispatches next recursive call.
      struct _After_Node {
        tree<A> *_s0;
        tree<A> a2;
        A a1;
        tree<A> a0;
      };

      /// _Combine_Node: receives partial results, combines with _result from
      /// final call.
      struct _Combine_Node {
        T1 _result;
        tree<A> a2;
        A a1;
        tree<A> a0;
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
          if (std::holds_alternative<typename tree<A>::Leaf>(_sv.v())) {
            _result = std::move(f);
          } else {
            const auto &[a0, a1, a2] =
                std::get<typename tree<A>::Node>(_sv.v());
            _stack.emplace_back(_After_Node{a0.get(), *a2, a1, *a0});
            _stack.emplace_back(_Enter{a2.get()});
          }
        } else if (std::holds_alternative<_After_Node>(_frame)) {
          auto _f = std::move(std::get<_After_Node>(_frame));
          _stack.emplace_back(_Combine_Node{_result, std::move(_f.a2), _f.a1,
                                            std::move(_f.a0)});
          _stack.emplace_back(_Enter{_f._s0});
        } else {
          auto _f = std::move(std::get<_Combine_Node>(_frame));
          _result = f0(_f.a0, _result, _f.a1, _f.a2, _f._result);
        }
      }
      return _result;
    }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, tree<A> &, T1 &, A &, tree<A> &,
                                     T1 &>
    T1 tree_rect(T1 f, F1 &&f0) const {
      const tree *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const tree *_self;
      };

      /// _After_Node: saves [_s0, a2, a1, a0], dispatches next recursive call.
      struct _After_Node {
        tree<A> *_s0;
        tree<A> a2;
        A a1;
        tree<A> a0;
      };

      /// _Combine_Node: receives partial results, combines with _result from
      /// final call.
      struct _Combine_Node {
        T1 _result;
        tree<A> a2;
        A a1;
        tree<A> a0;
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
          if (std::holds_alternative<typename tree<A>::Leaf>(_sv.v())) {
            _result = std::move(f);
          } else {
            const auto &[a0, a1, a2] =
                std::get<typename tree<A>::Node>(_sv.v());
            _stack.emplace_back(_After_Node{a0.get(), *a2, a1, *a0});
            _stack.emplace_back(_Enter{a2.get()});
          }
        } else if (std::holds_alternative<_After_Node>(_frame)) {
          auto _f = std::move(std::get<_After_Node>(_frame));
          _stack.emplace_back(_Combine_Node{_result, std::move(_f.a2), _f.a1,
                                            std::move(_f.a0)});
          _stack.emplace_back(_Enter{_f._s0});
        } else {
          auto _f = std::move(std::get<_Combine_Node>(_frame));
          _result = f0(_f.a0, _result, _f.a1, _f.a2, _f._result);
        }
      }
      return _result;
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
      std::unique_ptr<ternary> a0;
      std::unique_ptr<ternary> a1;
      std::unique_ptr<ternary> a2;
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

    ternary(const ternary &_other) : v_(std::move(_other.clone().v_)) {}

    ternary(ternary &&_other) noexcept : v_(std::move(_other.v_)) {}

    ternary &operator=(const ternary &_other) {
      v_ = std::move(_other.clone().v_);
      return *this;
    }

    ternary &operator=(ternary &&_other) noexcept {
      v_ = std::move(_other.v_);
      return *this;
    }

    // ACCESSORS
    ternary clone() const {
      ternary _out{};

      struct _CloneFrame {
        const ternary *_src;
        ternary *_dst;
      };

      std::vector<_CloneFrame> _stack{};
      _stack.reserve(8);
      _stack.push_back({this, &_out});
      while (!_stack.empty()) {
        auto _frame = _stack.back();
        _stack.pop_back();
        const ternary *_src = _frame._src;
        ternary *_dst = _frame._dst;
        if (std::holds_alternative<TLeaf>(_src->v())) {
          _dst->v_ = TLeaf{};
        } else {
          const auto &_alt = std::get<TNode>(_src->v());
          _dst->v_ =
              TNode{_alt.a0 ? std::make_unique<ternary>() : nullptr,
                    _alt.a1 ? std::make_unique<ternary>() : nullptr,
                    _alt.a2 ? std::make_unique<ternary>() : nullptr, _alt.a3};
          auto &_dst_alt = std::get<TNode>(_dst->v_);
          if (_alt.a0) {
            _stack.push_back({_alt.a0.get(), _dst_alt.a0.get()});
          }
          if (_alt.a1) {
            _stack.push_back({_alt.a1.get(), _dst_alt.a1.get()});
          }
          if (_alt.a2) {
            _stack.push_back({_alt.a2.get(), _dst_alt.a2.get()});
          }
        }
      }
      return _out;
    }

    // CREATORS
    static ternary tleaf() { return ternary(TLeaf{}); }

    static ternary tnode(ternary a0, ternary a1, ternary a2, uint64_t a3) {
      return ternary(TNode{std::make_unique<ternary>(std::move(a0)),
                           std::make_unique<ternary>(std::move(a1)),
                           std::make_unique<ternary>(std::move(a2)), a3});
    }

    // MANIPULATORS
    ~ternary() {
      std::vector<std::unique_ptr<ternary>> _stack{};
      _stack.reserve(8);
      auto _drain = [&](ternary &_node) {
        if (std::holds_alternative<TNode>(_node.v_)) {
          auto &_alt = std::get<TNode>(_node.v_);
          if (_alt.a0) {
            _stack.push_back(std::move(_alt.a0));
          }
          if (_alt.a1) {
            _stack.push_back(std::move(_alt.a1));
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

    uint64_t ternary_depth() const {
      const ternary *_self = this;
      auto &&_sv = *_self;
      if (std::holds_alternative<typename ternary::TLeaf>(_sv.v())) {
        return UINT64_C(0);
      } else {
        const auto &[a0, a1, a2, a3] =
            std::get<typename ternary::TNode>(_sv.v());
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
      const ternary *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const ternary *_self;
      };

      /// _After_TNode: saves [_s0, _s1, a3], dispatches next recursive call.
      struct _After_TNode {
        const ternary *_s0;
        const ternary *_s1;
        uint64_t a3;
      };

      /// _After_TNode_1: saves [_result, _s1, a3], dispatches next recursive
      /// call.
      struct _After_TNode_1 {
        uint64_t _result;
        const ternary *_s1;
        uint64_t a3;
      };

      /// _Combine_TNode: receives partial results, combines with _result from
      /// final call.
      struct _Combine_TNode {
        uint64_t _result_0;
        uint64_t _result_1;
        uint64_t a3;
      };

      using _Frame =
          std::variant<_Enter, _After_TNode, _After_TNode_1, _Combine_TNode>;
      uint64_t _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(8);
      _stack.emplace_back(_Enter{_self});
      /// Loopified ternary_sum: _Enter -> _After_TNode -> _After_TNode_1 ->
      /// _Combine_TNode.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const ternary *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename ternary::TLeaf>(_sv.v())) {
            _result = UINT64_C(0);
          } else {
            const auto &[a0, a1, a2, a3] =
                std::get<typename ternary::TNode>(_sv.v());
            _stack.emplace_back(_After_TNode{a1.get(), a0.get(), a3});
            _stack.emplace_back(_Enter{a2.get()});
          }
        } else if (std::holds_alternative<_After_TNode>(_frame)) {
          auto _f = std::move(std::get<_After_TNode>(_frame));
          _stack.emplace_back(_After_TNode_1{_result, _f._s1, _f.a3});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_After_TNode_1>(_frame)) {
          auto _f = std::move(std::get<_After_TNode_1>(_frame));
          _stack.emplace_back(_Combine_TNode{_f._result, _result, _f.a3});
          _stack.emplace_back(_Enter{_f._s1});
        } else {
          auto _f = std::move(std::get<_Combine_TNode>(_frame));
          _result = (_f.a3 + (_result + (_f._result_1 + _f._result_0)));
        }
      }
      return _result;
    }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, ternary &, T1 &, ternary &, T1 &,
                                     ternary &, T1 &, uint64_t &>
    T1 ternary_rec(T1 f, F1 &&f0) const {
      const ternary *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const ternary *_self;
      };

      /// _After_TNode: saves [_s0, _s1, a3, a2, a1, a0], dispatches next
      /// recursive call.
      struct _After_TNode {
        const ternary *_s0;
        const ternary *_s1;
        uint64_t a3;
        ternary a2;
        ternary a1;
        ternary a0;
      };

      /// _After_TNode_1: saves [_result, _s1, a3, a2, a1, a0], dispatches next
      /// recursive call.
      struct _After_TNode_1 {
        T1 _result;
        const ternary *_s1;
        uint64_t a3;
        ternary a2;
        ternary a1;
        ternary a0;
      };

      /// _Combine_TNode: receives partial results, combines with _result from
      /// final call.
      struct _Combine_TNode {
        T1 _result_0;
        T1 _result_1;
        uint64_t a3;
        ternary a2;
        ternary a1;
        ternary a0;
      };

      using _Frame =
          std::variant<_Enter, _After_TNode, _After_TNode_1, _Combine_TNode>;
      T1 _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(8);
      _stack.emplace_back(_Enter{_self});
      /// Loopified ternary_rec: _Enter -> _After_TNode -> _After_TNode_1 ->
      /// _Combine_TNode.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const ternary *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename ternary::TLeaf>(_sv.v())) {
            _result = std::move(f);
          } else {
            const auto &[a0, a1, a2, a3] =
                std::get<typename ternary::TNode>(_sv.v());
            _stack.emplace_back(
                _After_TNode{a1.get(), a0.get(), a3, *a2, *a1, *a0});
            _stack.emplace_back(_Enter{a2.get()});
          }
        } else if (std::holds_alternative<_After_TNode>(_frame)) {
          auto _f = std::move(std::get<_After_TNode>(_frame));
          _stack.emplace_back(_After_TNode_1{_result, _f._s1, _f.a3,
                                             std::move(_f.a2), std::move(_f.a1),
                                             std::move(_f.a0)});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_After_TNode_1>(_frame)) {
          auto _f = std::move(std::get<_After_TNode_1>(_frame));
          _stack.emplace_back(_Combine_TNode{_f._result, _result, _f.a3,
                                             std::move(_f.a2), std::move(_f.a1),
                                             std::move(_f.a0)});
          _stack.emplace_back(_Enter{_f._s1});
        } else {
          auto _f = std::move(std::get<_Combine_TNode>(_frame));
          _result = f0(_f.a0, _result, _f.a1, _f._result_1, _f.a2, _f._result_0,
                       _f.a3);
        }
      }
      return _result;
    }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, ternary &, T1 &, ternary &, T1 &,
                                     ternary &, T1 &, uint64_t &>
    T1 ternary_rect(T1 f, F1 &&f0) const {
      const ternary *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const ternary *_self;
      };

      /// _After_TNode: saves [_s0, _s1, a3, a2, a1, a0], dispatches next
      /// recursive call.
      struct _After_TNode {
        const ternary *_s0;
        const ternary *_s1;
        uint64_t a3;
        ternary a2;
        ternary a1;
        ternary a0;
      };

      /// _After_TNode_1: saves [_result, _s1, a3, a2, a1, a0], dispatches next
      /// recursive call.
      struct _After_TNode_1 {
        T1 _result;
        const ternary *_s1;
        uint64_t a3;
        ternary a2;
        ternary a1;
        ternary a0;
      };

      /// _Combine_TNode: receives partial results, combines with _result from
      /// final call.
      struct _Combine_TNode {
        T1 _result_0;
        T1 _result_1;
        uint64_t a3;
        ternary a2;
        ternary a1;
        ternary a0;
      };

      using _Frame =
          std::variant<_Enter, _After_TNode, _After_TNode_1, _Combine_TNode>;
      T1 _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(8);
      _stack.emplace_back(_Enter{_self});
      /// Loopified ternary_rect: _Enter -> _After_TNode -> _After_TNode_1 ->
      /// _Combine_TNode.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const ternary *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename ternary::TLeaf>(_sv.v())) {
            _result = std::move(f);
          } else {
            const auto &[a0, a1, a2, a3] =
                std::get<typename ternary::TNode>(_sv.v());
            _stack.emplace_back(
                _After_TNode{a1.get(), a0.get(), a3, *a2, *a1, *a0});
            _stack.emplace_back(_Enter{a2.get()});
          }
        } else if (std::holds_alternative<_After_TNode>(_frame)) {
          auto _f = std::move(std::get<_After_TNode>(_frame));
          _stack.emplace_back(_After_TNode_1{_result, _f._s1, _f.a3,
                                             std::move(_f.a2), std::move(_f.a1),
                                             std::move(_f.a0)});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_After_TNode_1>(_frame)) {
          auto _f = std::move(std::get<_After_TNode_1>(_frame));
          _stack.emplace_back(_Combine_TNode{_f._result, _result, _f.a3,
                                             std::move(_f.a2), std::move(_f.a1),
                                             std::move(_f.a0)});
          _stack.emplace_back(_Enter{_f._s1});
        } else {
          auto _f = std::move(std::get<_Combine_TNode>(_frame));
          _result = f0(_f.a0, _result, _f.a1, _f._result_1, _f.a2, _f._result_0,
                       _f.a3);
        }
      }
      return _result;
    }
  };

  /// Rose tree: a tree with variable number of children.
  struct rose {
    // TYPES
    struct RNode {
      uint64_t a0;
      std::unique_ptr<List<rose>> a1;
    };

    using variant_t = std::variant<RNode>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    rose() {}

    explicit rose(RNode _v) : v_(std::move(_v)) {}

    rose(const rose &_other) : v_(std::move(_other.clone().v_)) {}

    rose(rose &&_other) noexcept : v_(std::move(_other.v_)) {}

    rose &operator=(const rose &_other) {
      v_ = std::move(_other.clone().v_);
      return *this;
    }

    rose &operator=(rose &&_other) noexcept {
      v_ = std::move(_other.v_);
      return *this;
    }

    // ACCESSORS
    rose clone() const {
      rose _out{};

      struct _CloneFrame {
        const rose *_src;
        rose *_dst;
      };

      std::vector<_CloneFrame> _stack{};
      _stack.reserve(8);
      _stack.push_back({this, &_out});
      while (!_stack.empty()) {
        auto _frame = _stack.back();
        _stack.pop_back();
        const rose *_src = _frame._src;
        rose *_dst = _frame._dst;
        const auto &_alt = std::get<RNode>(_src->v());
        _dst->v_ =
            RNode{_alt.a0, _alt.a1 ? std::make_unique<List<rose>>() : nullptr};
        auto &_dst_alt = std::get<RNode>(_dst->v_);
        [&] {
          if (_alt.a1) {
            const List<rose> *_lsrc = _alt.a1.get();
            List<rose> *_ldst = _dst_alt.a1.get();
            while (
                std::holds_alternative<typename List<rose>::Cons>(_lsrc->v())) {
              const auto &_lsrc_c =
                  std::get<typename List<rose>::Cons>(_lsrc->v());
              _ldst->v_mut() = typename List<rose>::Cons{
                  rose{}, _lsrc_c.l ? std::make_unique<List<rose>>() : nullptr};
              auto &_ldst_c =
                  std::get<typename List<rose>::Cons>(_ldst->v_mut());
              _stack.push_back({&_lsrc_c.a, &_ldst_c.a});
              if (_lsrc_c.l) {
                _lsrc = _lsrc_c.l.get();
                _ldst = _ldst_c.l.get();
              } else {
                break;
              }
            }
            if (std::holds_alternative<typename List<rose>::Nil>(_lsrc->v())) {
              _ldst->v_mut() = typename List<rose>::Nil{};
            }
          }
        }();
      }
      return _out;
    }

    // CREATORS
    static rose rnode(uint64_t a0, List<rose> a1) {
      return rose(RNode{a0, std::make_unique<List<rose>>(std::move(a1))});
    }

    // MANIPULATORS
    ~rose() {
      std::vector<std::unique_ptr<rose>> _stack{};
      _stack.reserve(8);
      auto _drain = [&](rose &_node) {
        if (std::holds_alternative<RNode>(_node.v_)) {
          auto &_alt = std::get<RNode>(_node.v_);
          if (_alt.a1) {
            auto *_lp = _alt.a1.get();
            while (
                std::holds_alternative<typename List<rose>::Cons>(_lp->v())) {
              auto &_lc = std::get<typename List<rose>::Cons>(_lp->v_mut());
              _stack.push_back(std::make_unique<rose>(std::move(_lc.a)));
              if (_lc.l) {
                _lp = _lc.l.get();
              } else {
                break;
              }
            }
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
  static List<rose> map_rose_list_fuel(uint64_t fuel, F1 &&f,
                                       const List<rose> &cs) {
    if (fuel <= 0) {
      return List<rose>::nil();
    } else {
      uint64_t g = fuel - 1;
      if (std::holds_alternative<typename List<rose>::Nil>(cs.v())) {
        return List<rose>::nil();
      } else {
        const auto &[a0, a1] = std::get<typename List<rose>::Cons>(cs.v());
        const auto &[a00, a10] = std::get<typename rose::RNode>(a0.v());
        return List<rose>::cons(
            rose::rnode(f(a00), map_rose_list_fuel(g, f, *a10)),
            map_rose_list_fuel(g, f, *a1));
      }
    }
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
  static bool or_search(F0 &&p, const tree<uint64_t> &t) {
    if (std::holds_alternative<typename tree<uint64_t>::Leaf>(t.v())) {
      return false;
    } else {
      const auto &[a0, a1, a2] = std::get<typename tree<uint64_t>::Node>(t.v());
      if (p(a1)) {
        return true;
      } else {
        return (or_search(p, *a0) || or_search(p, *a2));
      }
    }
  }

  struct quadtree {
    // TYPES
    struct QLeaf {
      uint64_t a0;
    };

    struct Quad {
      std::unique_ptr<quadtree> a0;
      std::unique_ptr<quadtree> a1;
      std::unique_ptr<quadtree> a2;
      std::unique_ptr<quadtree> a3;
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

    quadtree(const quadtree &_other) : v_(std::move(_other.clone().v_)) {}

    quadtree(quadtree &&_other) noexcept : v_(std::move(_other.v_)) {}

    quadtree &operator=(const quadtree &_other) {
      v_ = std::move(_other.clone().v_);
      return *this;
    }

    quadtree &operator=(quadtree &&_other) noexcept {
      v_ = std::move(_other.v_);
      return *this;
    }

    // ACCESSORS
    quadtree clone() const {
      quadtree _out{};

      struct _CloneFrame {
        const quadtree *_src;
        quadtree *_dst;
      };

      std::vector<_CloneFrame> _stack{};
      _stack.reserve(8);
      _stack.push_back({this, &_out});
      while (!_stack.empty()) {
        auto _frame = _stack.back();
        _stack.pop_back();
        const quadtree *_src = _frame._src;
        quadtree *_dst = _frame._dst;
        if (std::holds_alternative<QLeaf>(_src->v())) {
          const auto &_alt = std::get<QLeaf>(_src->v());
          _dst->v_ = QLeaf{_alt.a0};
        } else {
          const auto &_alt = std::get<Quad>(_src->v());
          _dst->v_ = Quad{_alt.a0 ? std::make_unique<quadtree>() : nullptr,
                          _alt.a1 ? std::make_unique<quadtree>() : nullptr,
                          _alt.a2 ? std::make_unique<quadtree>() : nullptr,
                          _alt.a3 ? std::make_unique<quadtree>() : nullptr};
          auto &_dst_alt = std::get<Quad>(_dst->v_);
          if (_alt.a0) {
            _stack.push_back({_alt.a0.get(), _dst_alt.a0.get()});
          }
          if (_alt.a1) {
            _stack.push_back({_alt.a1.get(), _dst_alt.a1.get()});
          }
          if (_alt.a2) {
            _stack.push_back({_alt.a2.get(), _dst_alt.a2.get()});
          }
          if (_alt.a3) {
            _stack.push_back({_alt.a3.get(), _dst_alt.a3.get()});
          }
        }
      }
      return _out;
    }

    // CREATORS
    static quadtree qleaf(uint64_t a0) { return quadtree(QLeaf{a0}); }

    static quadtree quad(quadtree a0, quadtree a1, quadtree a2, quadtree a3) {
      return quadtree(Quad{std::make_unique<quadtree>(std::move(a0)),
                           std::make_unique<quadtree>(std::move(a1)),
                           std::make_unique<quadtree>(std::move(a2)),
                           std::make_unique<quadtree>(std::move(a3))});
    }

    // MANIPULATORS
    ~quadtree() {
      std::vector<std::unique_ptr<quadtree>> _stack{};
      _stack.reserve(8);
      auto _drain = [&](quadtree &_node) {
        if (std::holds_alternative<Quad>(_node.v_)) {
          auto &_alt = std::get<Quad>(_node.v_);
          if (_alt.a0) {
            _stack.push_back(std::move(_alt.a0));
          }
          if (_alt.a1) {
            _stack.push_back(std::move(_alt.a1));
          }
          if (_alt.a2) {
            _stack.push_back(std::move(_alt.a2));
          }
          if (_alt.a3) {
            _stack.push_back(std::move(_alt.a3));
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

    /// quad_depth t computes depth of quadtree.
    uint64_t quad_depth() const {
      const quadtree *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const quadtree *_self;
      };

      /// _After_Quad: saves [_s0, _s1, _s2], dispatches next recursive call.
      struct _After_Quad {
        const quadtree *_s0;
        const quadtree *_s1;
        const quadtree *_s2;
      };

      /// _After_Quad_1: saves [_result, _s1, _s2], dispatches next recursive
      /// call.
      struct _After_Quad_1 {
        uint64_t _result;
        const quadtree *_s1;
        const quadtree *_s2;
      };

      /// _After_Quad_2: saves [_result_0, _result_1, _s2], dispatches next
      /// recursive call.
      struct _After_Quad_2 {
        uint64_t _result_0;
        uint64_t _result_1;
        const quadtree *_s2;
      };

      /// _Combine_Quad: receives partial results, combines with _result from
      /// final call.
      struct _Combine_Quad {
        uint64_t _result_0;
        uint64_t _result_1;
        uint64_t _result_2;
      };

      using _Frame = std::variant<_Enter, _After_Quad, _After_Quad_1,
                                  _After_Quad_2, _Combine_Quad>;
      uint64_t _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(8);
      _stack.emplace_back(_Enter{_self});
      /// Loopified quad_depth: _Enter -> _After_Quad -> _After_Quad_1 ->
      /// _After_Quad_2 -> _Combine_Quad.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const quadtree *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename quadtree::QLeaf>(_sv.v())) {
            _result = UINT64_C(0);
          } else {
            const auto &[a0, a1, a2, a3] =
                std::get<typename quadtree::Quad>(_sv.v());
            _stack.emplace_back(_After_Quad{a2.get(), a1.get(), a0.get()});
            _stack.emplace_back(_Enter{a3.get()});
          }
        } else if (std::holds_alternative<_After_Quad>(_frame)) {
          auto _f = std::move(std::get<_After_Quad>(_frame));
          _stack.emplace_back(_After_Quad_1{_result, _f._s1, _f._s2});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_After_Quad_1>(_frame)) {
          auto _f = std::move(std::get<_After_Quad_1>(_frame));
          _stack.emplace_back(_After_Quad_2{_f._result, _result, _f._s2});
          _stack.emplace_back(_Enter{_f._s1});
        } else if (std::holds_alternative<_After_Quad_2>(_frame)) {
          auto _f = std::move(std::get<_After_Quad_2>(_frame));
          _stack.emplace_back(
              _Combine_Quad{_f._result_0, _f._result_1, _result});
          _stack.emplace_back(_Enter{_f._s2});
        } else {
          auto _f = std::move(std::get<_Combine_Quad>(_frame));
          _result =
              (max4_impl(_result, _f._result_2, _f._result_1, _f._result_0) +
               1);
        }
      }
      return _result;
    }

    /// quad_sum t sums all values in a quadtree.
    uint64_t quad_sum() const {
      const quadtree *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const quadtree *_self;
      };

      /// _After_Quad: saves [_s0, _s1, _s2], dispatches next recursive call.
      struct _After_Quad {
        const quadtree *_s0;
        const quadtree *_s1;
        const quadtree *_s2;
      };

      /// _After_Quad_1: saves [_result, _s1, _s2], dispatches next recursive
      /// call.
      struct _After_Quad_1 {
        uint64_t _result;
        const quadtree *_s1;
        const quadtree *_s2;
      };

      /// _After_Quad_2: saves [_result_0, _result_1, _s2], dispatches next
      /// recursive call.
      struct _After_Quad_2 {
        uint64_t _result_0;
        uint64_t _result_1;
        const quadtree *_s2;
      };

      /// _Combine_Quad: receives partial results, combines with _result from
      /// final call.
      struct _Combine_Quad {
        uint64_t _result_0;
        uint64_t _result_1;
        uint64_t _result_2;
      };

      using _Frame = std::variant<_Enter, _After_Quad, _After_Quad_1,
                                  _After_Quad_2, _Combine_Quad>;
      uint64_t _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(8);
      _stack.emplace_back(_Enter{_self});
      /// Loopified quad_sum: _Enter -> _After_Quad -> _After_Quad_1 ->
      /// _After_Quad_2 -> _Combine_Quad.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const quadtree *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename quadtree::QLeaf>(_sv.v())) {
            const auto &[a0] = std::get<typename quadtree::QLeaf>(_sv.v());
            _result = std::move(a0);
          } else {
            const auto &[a0, a1, a2, a3] =
                std::get<typename quadtree::Quad>(_sv.v());
            _stack.emplace_back(_After_Quad{a2.get(), a1.get(), a0.get()});
            _stack.emplace_back(_Enter{a3.get()});
          }
        } else if (std::holds_alternative<_After_Quad>(_frame)) {
          auto _f = std::move(std::get<_After_Quad>(_frame));
          _stack.emplace_back(_After_Quad_1{_result, _f._s1, _f._s2});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_After_Quad_1>(_frame)) {
          auto _f = std::move(std::get<_After_Quad_1>(_frame));
          _stack.emplace_back(_After_Quad_2{_f._result, _result, _f._s2});
          _stack.emplace_back(_Enter{_f._s1});
        } else if (std::holds_alternative<_After_Quad_2>(_frame)) {
          auto _f = std::move(std::get<_After_Quad_2>(_frame));
          _stack.emplace_back(
              _Combine_Quad{_f._result_0, _f._result_1, _result});
          _stack.emplace_back(_Enter{_f._s2});
        } else {
          auto _f = std::move(std::get<_Combine_Quad>(_frame));
          _result = (_result + (_f._result_2 + (_f._result_1 + _f._result_0)));
        }
      }
      return _result;
    }

    template <typename T1, typename F0, typename F1>
      requires std::is_invocable_r_v<T1, F0 &, uint64_t &> &&
               std::is_invocable_r_v<T1, F1 &, quadtree &, T1 &, quadtree &,
                                     T1 &, quadtree &, T1 &, quadtree &, T1 &>
    T1 quadtree_rec(F0 &&f, F1 &&f0) const {
      const quadtree *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const quadtree *_self;
      };

      /// _After_Quad: saves [_s0, _s1, _s2, a3, a2, a1, a0], dispatches next
      /// recursive call.
      struct _After_Quad {
        const quadtree *_s0;
        const quadtree *_s1;
        const quadtree *_s2;
        quadtree a3;
        quadtree a2;
        quadtree a1;
        quadtree a0;
      };

      /// _After_Quad_1: saves [_result, _s1, _s2, a3, a2, a1, a0], dispatches
      /// next recursive call.
      struct _After_Quad_1 {
        T1 _result;
        const quadtree *_s1;
        const quadtree *_s2;
        quadtree a3;
        quadtree a2;
        quadtree a1;
        quadtree a0;
      };

      /// _After_Quad_2: saves [_result_0, _result_1, _s2, a3, a2, a1, a0],
      /// dispatches next recursive call.
      struct _After_Quad_2 {
        T1 _result_0;
        T1 _result_1;
        const quadtree *_s2;
        quadtree a3;
        quadtree a2;
        quadtree a1;
        quadtree a0;
      };

      /// _Combine_Quad: receives partial results, combines with _result from
      /// final call.
      struct _Combine_Quad {
        T1 _result_0;
        T1 _result_1;
        T1 _result_2;
        quadtree a3;
        quadtree a2;
        quadtree a1;
        quadtree a0;
      };

      using _Frame = std::variant<_Enter, _After_Quad, _After_Quad_1,
                                  _After_Quad_2, _Combine_Quad>;
      T1 _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(8);
      _stack.emplace_back(_Enter{_self});
      /// Loopified quadtree_rec: _Enter -> _After_Quad -> _After_Quad_1 ->
      /// _After_Quad_2 -> _Combine_Quad.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const quadtree *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename quadtree::QLeaf>(_sv.v())) {
            const auto &[a0] = std::get<typename quadtree::QLeaf>(_sv.v());
            _result = f(a0);
          } else {
            const auto &[a0, a1, a2, a3] =
                std::get<typename quadtree::Quad>(_sv.v());
            _stack.emplace_back(
                _After_Quad{a2.get(), a1.get(), a0.get(), *a3, *a2, *a1, *a0});
            _stack.emplace_back(_Enter{a3.get()});
          }
        } else if (std::holds_alternative<_After_Quad>(_frame)) {
          auto _f = std::move(std::get<_After_Quad>(_frame));
          _stack.emplace_back(_After_Quad_1{
              _result, _f._s1, _f._s2, std::move(_f.a3), std::move(_f.a2),
              std::move(_f.a1), std::move(_f.a0)});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_After_Quad_1>(_frame)) {
          auto _f = std::move(std::get<_After_Quad_1>(_frame));
          _stack.emplace_back(_After_Quad_2{
              _f._result, _result, _f._s2, std::move(_f.a3), std::move(_f.a2),
              std::move(_f.a1), std::move(_f.a0)});
          _stack.emplace_back(_Enter{_f._s1});
        } else if (std::holds_alternative<_After_Quad_2>(_frame)) {
          auto _f = std::move(std::get<_After_Quad_2>(_frame));
          _stack.emplace_back(_Combine_Quad{
              _f._result_0, _f._result_1, _result, std::move(_f.a3),
              std::move(_f.a2), std::move(_f.a1), std::move(_f.a0)});
          _stack.emplace_back(_Enter{_f._s2});
        } else {
          auto _f = std::move(std::get<_Combine_Quad>(_frame));
          _result = f0(_f.a0, _result, _f.a1, _f._result_2, _f.a2, _f._result_1,
                       _f.a3, _f._result_0);
        }
      }
      return _result;
    }

    template <typename T1, typename F0, typename F1>
      requires std::is_invocable_r_v<T1, F0 &, uint64_t &> &&
               std::is_invocable_r_v<T1, F1 &, quadtree &, T1 &, quadtree &,
                                     T1 &, quadtree &, T1 &, quadtree &, T1 &>
    T1 quadtree_rect(F0 &&f, F1 &&f0) const {
      const quadtree *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const quadtree *_self;
      };

      /// _After_Quad: saves [_s0, _s1, _s2, a3, a2, a1, a0], dispatches next
      /// recursive call.
      struct _After_Quad {
        const quadtree *_s0;
        const quadtree *_s1;
        const quadtree *_s2;
        quadtree a3;
        quadtree a2;
        quadtree a1;
        quadtree a0;
      };

      /// _After_Quad_1: saves [_result, _s1, _s2, a3, a2, a1, a0], dispatches
      /// next recursive call.
      struct _After_Quad_1 {
        T1 _result;
        const quadtree *_s1;
        const quadtree *_s2;
        quadtree a3;
        quadtree a2;
        quadtree a1;
        quadtree a0;
      };

      /// _After_Quad_2: saves [_result_0, _result_1, _s2, a3, a2, a1, a0],
      /// dispatches next recursive call.
      struct _After_Quad_2 {
        T1 _result_0;
        T1 _result_1;
        const quadtree *_s2;
        quadtree a3;
        quadtree a2;
        quadtree a1;
        quadtree a0;
      };

      /// _Combine_Quad: receives partial results, combines with _result from
      /// final call.
      struct _Combine_Quad {
        T1 _result_0;
        T1 _result_1;
        T1 _result_2;
        quadtree a3;
        quadtree a2;
        quadtree a1;
        quadtree a0;
      };

      using _Frame = std::variant<_Enter, _After_Quad, _After_Quad_1,
                                  _After_Quad_2, _Combine_Quad>;
      T1 _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(8);
      _stack.emplace_back(_Enter{_self});
      /// Loopified quadtree_rect: _Enter -> _After_Quad -> _After_Quad_1 ->
      /// _After_Quad_2 -> _Combine_Quad.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const quadtree *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename quadtree::QLeaf>(_sv.v())) {
            const auto &[a0] = std::get<typename quadtree::QLeaf>(_sv.v());
            _result = f(a0);
          } else {
            const auto &[a0, a1, a2, a3] =
                std::get<typename quadtree::Quad>(_sv.v());
            _stack.emplace_back(
                _After_Quad{a2.get(), a1.get(), a0.get(), *a3, *a2, *a1, *a0});
            _stack.emplace_back(_Enter{a3.get()});
          }
        } else if (std::holds_alternative<_After_Quad>(_frame)) {
          auto _f = std::move(std::get<_After_Quad>(_frame));
          _stack.emplace_back(_After_Quad_1{
              _result, _f._s1, _f._s2, std::move(_f.a3), std::move(_f.a2),
              std::move(_f.a1), std::move(_f.a0)});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_After_Quad_1>(_frame)) {
          auto _f = std::move(std::get<_After_Quad_1>(_frame));
          _stack.emplace_back(_After_Quad_2{
              _f._result, _result, _f._s2, std::move(_f.a3), std::move(_f.a2),
              std::move(_f.a1), std::move(_f.a0)});
          _stack.emplace_back(_Enter{_f._s1});
        } else if (std::holds_alternative<_After_Quad_2>(_frame)) {
          auto _f = std::move(std::get<_After_Quad_2>(_frame));
          _stack.emplace_back(_Combine_Quad{
              _f._result_0, _f._result_1, _result, std::move(_f.a3),
              std::move(_f.a2), std::move(_f.a1), std::move(_f.a0)});
          _stack.emplace_back(_Enter{_f._s2});
        } else {
          auto _f = std::move(std::get<_Combine_Quad>(_frame));
          _result = f0(_f.a0, _result, _f.a1, _f._result_2, _f.a2, _f._result_1,
                       _f.a3, _f._result_0);
        }
      }
      return _result;
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
      std::unique_ptr<simple_tree> a0;
      std::unique_ptr<simple_tree> a1;
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

    simple_tree(const simple_tree &_other) : v_(std::move(_other.clone().v_)) {}

    simple_tree(simple_tree &&_other) noexcept : v_(std::move(_other.v_)) {}

    simple_tree &operator=(const simple_tree &_other) {
      v_ = std::move(_other.clone().v_);
      return *this;
    }

    simple_tree &operator=(simple_tree &&_other) noexcept {
      v_ = std::move(_other.v_);
      return *this;
    }

    // ACCESSORS
    simple_tree clone() const {
      simple_tree _out{};

      struct _CloneFrame {
        const simple_tree *_src;
        simple_tree *_dst;
      };

      std::vector<_CloneFrame> _stack{};
      _stack.reserve(8);
      _stack.push_back({this, &_out});
      while (!_stack.empty()) {
        auto _frame = _stack.back();
        _stack.pop_back();
        const simple_tree *_src = _frame._src;
        simple_tree *_dst = _frame._dst;
        if (std::holds_alternative<SLeaf>(_src->v())) {
          const auto &_alt = std::get<SLeaf>(_src->v());
          _dst->v_ = SLeaf{_alt.a0};
        } else {
          const auto &_alt = std::get<SNode>(_src->v());
          _dst->v_ = SNode{_alt.a0 ? std::make_unique<simple_tree>() : nullptr,
                           _alt.a1 ? std::make_unique<simple_tree>() : nullptr};
          auto &_dst_alt = std::get<SNode>(_dst->v_);
          if (_alt.a0) {
            _stack.push_back({_alt.a0.get(), _dst_alt.a0.get()});
          }
          if (_alt.a1) {
            _stack.push_back({_alt.a1.get(), _dst_alt.a1.get()});
          }
        }
      }
      return _out;
    }

    // CREATORS
    static simple_tree sleaf(uint64_t a0) { return simple_tree(SLeaf{a0}); }

    static simple_tree snode(simple_tree a0, simple_tree a1) {
      return simple_tree(SNode{std::make_unique<simple_tree>(std::move(a0)),
                               std::make_unique<simple_tree>(std::move(a1))});
    }

    // MANIPULATORS
    ~simple_tree() {
      std::vector<std::unique_ptr<simple_tree>> _stack{};
      _stack.reserve(8);
      auto _drain = [&](simple_tree &_node) {
        if (std::holds_alternative<SNode>(_node.v_)) {
          auto &_alt = std::get<SNode>(_node.v_);
          if (_alt.a0) {
            _stack.push_back(std::move(_alt.a0));
          }
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

    /// count_paths_simple t n counts paths with sum n (simpler variant).
    uint64_t count_paths_simple(uint64_t n) const {
      const simple_tree *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const simple_tree *_self;
        uint64_t n;
      };

      /// _After2: saves [_s0, _s1], dispatches next recursive call.
      struct _After2 {
        simple_tree *_s0;
        decltype((((std::declval<uint64_t &>() - UINT64_C(1)) >
                           std::declval<uint64_t &>()
                       ? 0
                       : (std::declval<uint64_t &>() - UINT64_C(1))))) _s1;
      };

      /// _Combine1: receives partial results, combines with _result from final
      /// call.
      struct _Combine1 {
        uint64_t _result;
      };

      using _Frame = std::variant<_Enter, _After2, _Combine1>;
      uint64_t _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(8);
      _stack.emplace_back(_Enter{_self, n});
      /// Loopified count_paths_simple: _Enter -> _After2 -> _Combine1.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const simple_tree *_self = _f._self;
          uint64_t n = _f.n;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename simple_tree::SLeaf>(_sv.v())) {
            const auto &[a0] = std::get<typename simple_tree::SLeaf>(_sv.v());
            if (a0 == n) {
              _result = UINT64_C(1);
            } else {
              _result = UINT64_C(0);
            }
          } else {
            const auto &[a0, a1] =
                std::get<typename simple_tree::SNode>(_sv.v());
            if (n <= UINT64_C(0)) {
              _result = UINT64_C(0);
            } else {
              _stack.emplace_back(_After2{
                  a0.get(), (((n - UINT64_C(1)) > n ? 0 : (n - UINT64_C(1))))});
              _stack.emplace_back(_Enter{
                  a1.get(), (((n - UINT64_C(1)) > n ? 0 : (n - UINT64_C(1))))});
            }
          }
        } else if (std::holds_alternative<_After2>(_frame)) {
          auto _f = std::move(std::get<_After2>(_frame));
          _stack.emplace_back(_Combine1{_result});
          _stack.emplace_back(_Enter{_f._s0, _f._s1});
        } else {
          auto _f = std::move(std::get<_Combine1>(_frame));
          _result = (_result + _f._result);
        }
      }
      return _result;
    }

    /// simple_tree_sum t sums all leaf values.
    uint64_t simple_tree_sum() const {
      const simple_tree *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const simple_tree *_self;
      };

      /// _After_SNode: saves [_s0], dispatches next recursive call.
      struct _After_SNode {
        simple_tree *_s0;
      };

      /// _Combine_SNode: receives partial results, combines with _result from
      /// final call.
      struct _Combine_SNode {
        uint64_t _result;
      };

      using _Frame = std::variant<_Enter, _After_SNode, _Combine_SNode>;
      uint64_t _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(8);
      _stack.emplace_back(_Enter{_self});
      /// Loopified simple_tree_sum: _Enter -> _After_SNode -> _Combine_SNode.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const simple_tree *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename simple_tree::SLeaf>(_sv.v())) {
            const auto &[a0] = std::get<typename simple_tree::SLeaf>(_sv.v());
            _result = std::move(a0);
          } else {
            const auto &[a0, a1] =
                std::get<typename simple_tree::SNode>(_sv.v());
            _stack.emplace_back(_After_SNode{a0.get()});
            _stack.emplace_back(_Enter{a1.get()});
          }
        } else if (std::holds_alternative<_After_SNode>(_frame)) {
          auto _f = std::move(std::get<_After_SNode>(_frame));
          _stack.emplace_back(_Combine_SNode{_result});
          _stack.emplace_back(_Enter{_f._s0});
        } else {
          auto _f = std::move(std::get<_Combine_SNode>(_frame));
          _result = (_result + _f._result);
        }
      }
      return _result;
    }

    template <typename T1, typename F0, typename F1>
      requires std::is_invocable_r_v<T1, F0 &, uint64_t &> &&
               std::is_invocable_r_v<T1, F1 &, simple_tree &, T1 &,
                                     simple_tree &, T1 &>
    T1 simple_tree_rec(F0 &&f, F1 &&f0) const {
      const simple_tree *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const simple_tree *_self;
      };

      /// _After_SNode: saves [_s0, a1, a0], dispatches next recursive call.
      struct _After_SNode {
        simple_tree *_s0;
        simple_tree a1;
        simple_tree a0;
      };

      /// _Combine_SNode: receives partial results, combines with _result from
      /// final call.
      struct _Combine_SNode {
        T1 _result;
        simple_tree a1;
        simple_tree a0;
      };

      using _Frame = std::variant<_Enter, _After_SNode, _Combine_SNode>;
      T1 _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(8);
      _stack.emplace_back(_Enter{_self});
      /// Loopified simple_tree_rec: _Enter -> _After_SNode -> _Combine_SNode.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const simple_tree *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename simple_tree::SLeaf>(_sv.v())) {
            const auto &[a0] = std::get<typename simple_tree::SLeaf>(_sv.v());
            _result = f(a0);
          } else {
            const auto &[a0, a1] =
                std::get<typename simple_tree::SNode>(_sv.v());
            _stack.emplace_back(_After_SNode{a0.get(), *a1, *a0});
            _stack.emplace_back(_Enter{a1.get()});
          }
        } else if (std::holds_alternative<_After_SNode>(_frame)) {
          auto _f = std::move(std::get<_After_SNode>(_frame));
          _stack.emplace_back(
              _Combine_SNode{_result, std::move(_f.a1), std::move(_f.a0)});
          _stack.emplace_back(_Enter{_f._s0});
        } else {
          auto _f = std::move(std::get<_Combine_SNode>(_frame));
          _result = f0(_f.a0, _result, _f.a1, _f._result);
        }
      }
      return _result;
    }

    template <typename T1, typename F0, typename F1>
      requires std::is_invocable_r_v<T1, F0 &, uint64_t &> &&
               std::is_invocable_r_v<T1, F1 &, simple_tree &, T1 &,
                                     simple_tree &, T1 &>
    T1 simple_tree_rect(F0 &&f, F1 &&f0) const {
      const simple_tree *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const simple_tree *_self;
      };

      /// _After_SNode: saves [_s0, a1, a0], dispatches next recursive call.
      struct _After_SNode {
        simple_tree *_s0;
        simple_tree a1;
        simple_tree a0;
      };

      /// _Combine_SNode: receives partial results, combines with _result from
      /// final call.
      struct _Combine_SNode {
        T1 _result;
        simple_tree a1;
        simple_tree a0;
      };

      using _Frame = std::variant<_Enter, _After_SNode, _Combine_SNode>;
      T1 _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(8);
      _stack.emplace_back(_Enter{_self});
      /// Loopified simple_tree_rect: _Enter -> _After_SNode -> _Combine_SNode.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const simple_tree *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename simple_tree::SLeaf>(_sv.v())) {
            const auto &[a0] = std::get<typename simple_tree::SLeaf>(_sv.v());
            _result = f(a0);
          } else {
            const auto &[a0, a1] =
                std::get<typename simple_tree::SNode>(_sv.v());
            _stack.emplace_back(_After_SNode{a0.get(), *a1, *a0});
            _stack.emplace_back(_Enter{a1.get()});
          }
        } else if (std::holds_alternative<_After_SNode>(_frame)) {
          auto _f = std::move(std::get<_After_SNode>(_frame));
          _stack.emplace_back(
              _Combine_SNode{_result, std::move(_f.a1), std::move(_f.a0)});
          _stack.emplace_back(_Enter{_f._s0});
        } else {
          auto _f = std::move(std::get<_Combine_SNode>(_frame));
          _result = f0(_f.a0, _result, _f.a1, _f._result);
        }
      }
      return _result;
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
