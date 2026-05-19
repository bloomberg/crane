#ifndef INCLUDED_DEEP_MAP
#define INCLUDED_DEEP_MAP

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

struct DeepMap {
  template <typename A> struct tree {
    // TYPES
    struct Leaf {};

    struct Node {
      std::unique_ptr<tree<A>> a0;
      A a1;
      std::unique_ptr<tree<A>> a2;
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
              Node{_alt.a0 ? std::make_unique<tree<A>>() : nullptr, _alt.a1,
                   _alt.a2 ? std::make_unique<tree<A>>() : nullptr};
          auto &_dst_alt = std::get<Node>(_dst->v_);
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
    template <typename _U> explicit tree(const tree<_U> &_other) {
      if (std::holds_alternative<typename tree<_U>::Leaf>(_other.v())) {
        this->v_ = Leaf{};
      } else {
        const auto &[a0, a1, a2] =
            std::get<typename tree<_U>::Node>(_other.v());
        this->v_ = Node{a0 ? std::make_unique<tree<A>>(*a0) : nullptr, A(a1),
                        a2 ? std::make_unique<tree<A>>(*a2) : nullptr};
      }
    }

    static tree<A> leaf() { return tree(Leaf{}); }

    static tree<A> node(tree<A> a0, A a1, tree<A> a2) {
      return tree(Node{std::make_unique<tree<A>>(std::move(a0)), std::move(a1),
                       std::make_unique<tree<A>>(std::move(a2))});
    }

    // MANIPULATORS
    ~tree() {
      std::vector<std::unique_ptr<tree<A>>> _stack{};
      _stack.reserve(8);
      auto _drain = [&](tree<A> &_node) {
        if (std::holds_alternative<Node>(_node.v_)) {
          auto &_alt = std::get<Node>(_node.v_);
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
  };

  template <typename T1, typename T2, typename F1>
    requires std::is_invocable_r_v<T2, F1 &, tree<T1> &, T2 &, T1 &, tree<T1> &,
                                   T2 &>
  static T2
  tree_rect(T2 f, F1 &&f0,
            const tree<T1> &t) { /// _Enter: captures varying parameters for
                                 /// each recursive call.

    struct _Enter {
      const tree<T1> *t;
    };

    /// _After_Node: saves [a0_0, a2, a1, a0_1], dispatches next recursive call.
    struct _After_Node {
      const tree<T1> *a0_0;
      tree<T1> a2;
      T1 a1;
      tree<T1> a0_1;
    };

    /// _Combine_Node: receives partial results, combines with _result from
    /// final call.
    struct _Combine_Node {
      T2 _result;
      tree<T1> a2;
      T1 a1;
      tree<T1> a0;
    };

    using _Frame = std::variant<_Enter, _After_Node, _Combine_Node>;
    T2 _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{&t});
    /// Loopified tree_rect: _Enter -> _After_Node -> _Combine_Node.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const tree<T1> &t = *_f.t;
        if (std::holds_alternative<typename tree<T1>::Leaf>(t.v())) {
          _result = std::move(f);
        } else {
          const auto &[a0, a1, a2] = std::get<typename tree<T1>::Node>(t.v());
          _stack.emplace_back(_After_Node{a0.get(), *a2, a1, *a0});
          _stack.emplace_back(_Enter{a2.get()});
        }
      } else if (std::holds_alternative<_After_Node>(_frame)) {
        auto _f = std::move(std::get<_After_Node>(_frame));
        _stack.emplace_back(_Combine_Node{std::move(_result), std::move(_f.a2),
                                          std::move(_f.a1),
                                          std::move(_f.a0_1)});
        _stack.emplace_back(_Enter{_f.a0_0});
      } else {
        auto _f = std::move(std::get<_Combine_Node>(_frame));
        _result =
            f0(_f.a0, std::move(_result), _f.a1, _f.a2, std::move(_f._result));
      }
    }
    return _result;
  }

  template <typename T1, typename T2, typename F1>
    requires std::is_invocable_r_v<T2, F1 &, tree<T1> &, T2 &, T1 &, tree<T1> &,
                                   T2 &>
  static T2
  tree_rec(T2 f, F1 &&f0,
           const tree<T1> &t) { /// _Enter: captures varying parameters for each
                                /// recursive call.

    struct _Enter {
      const tree<T1> *t;
    };

    /// _After_Node: saves [a0_0, a2, a1, a0_1], dispatches next recursive call.
    struct _After_Node {
      const tree<T1> *a0_0;
      tree<T1> a2;
      T1 a1;
      tree<T1> a0_1;
    };

    /// _Combine_Node: receives partial results, combines with _result from
    /// final call.
    struct _Combine_Node {
      T2 _result;
      tree<T1> a2;
      T1 a1;
      tree<T1> a0;
    };

    using _Frame = std::variant<_Enter, _After_Node, _Combine_Node>;
    T2 _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{&t});
    /// Loopified tree_rec: _Enter -> _After_Node -> _Combine_Node.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const tree<T1> &t = *_f.t;
        if (std::holds_alternative<typename tree<T1>::Leaf>(t.v())) {
          _result = std::move(f);
        } else {
          const auto &[a0, a1, a2] = std::get<typename tree<T1>::Node>(t.v());
          _stack.emplace_back(_After_Node{a0.get(), *a2, a1, *a0});
          _stack.emplace_back(_Enter{a2.get()});
        }
      } else if (std::holds_alternative<_After_Node>(_frame)) {
        auto _f = std::move(std::get<_After_Node>(_frame));
        _stack.emplace_back(_Combine_Node{std::move(_result), std::move(_f.a2),
                                          std::move(_f.a1),
                                          std::move(_f.a0_1)});
        _stack.emplace_back(_Enter{_f.a0_0});
      } else {
        auto _f = std::move(std::get<_Combine_Node>(_frame));
        _result =
            f0(_f.a0, std::move(_result), _f.a1, _f.a2, std::move(_f._result));
      }
    }
    return _result;
  }

  /// Build a maximally-unbalanced tree (right spine = linked list).
  /// Tail-recursive via accumulator, should be loopified.
  static tree<uint64_t> build_right(uint64_t n, tree<uint64_t> acc);

  /// Recursive tree map — visits every node.
  template <typename T1, typename T2, typename F0>
    requires std::is_invocable_r_v<T2, F0 &, T1 &>
  static tree<T2>
  tmap(F0 &&f,
       const tree<T1> &
           t) { /// _Enter: captures varying parameters for each recursive call.

    struct _Enter {
      const tree<T1> *t;
    };

    /// _After_Node: saves [a0, a1], dispatches next recursive call.
    struct _After_Node {
      const tree<T1> *a0;
      T2 a1;
    };

    /// _Combine_Node: receives partial results, combines with _result from
    /// final call.
    struct _Combine_Node {
      tree<T2> _result;
      T2 a1;
    };

    using _Frame = std::variant<_Enter, _After_Node, _Combine_Node>;
    tree<T2> _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{&t});
    /// Loopified tmap: _Enter -> _After_Node -> _Combine_Node.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const tree<T1> &t = *_f.t;
        if (std::holds_alternative<typename tree<T1>::Leaf>(t.v())) {
          _result = tree<T2>::leaf();
        } else {
          const auto &[a0, a1, a2] = std::get<typename tree<T1>::Node>(t.v());
          _stack.emplace_back(_After_Node{a0.get(), f(a1)});
          _stack.emplace_back(_Enter{a2.get()});
        }
      } else if (std::holds_alternative<_After_Node>(_frame)) {
        auto _f = std::move(std::get<_After_Node>(_frame));
        _stack.emplace_back(
            _Combine_Node{std::move(_result), std::move(_f.a1)});
        _stack.emplace_back(_Enter{_f.a0});
      } else {
        auto _f = std::move(std::get<_Combine_Node>(_frame));
        _result =
            tree<T2>::node(std::move(_result), _f.a1, std::move(_f._result));
      }
    }
    return _result;
  }

  static tree<uint64_t> map_inc(const tree<uint64_t> &t);
  /// Get root value.
  static uint64_t root_or_zero(const tree<uint64_t> &t);
};

#endif // INCLUDED_DEEP_MAP
