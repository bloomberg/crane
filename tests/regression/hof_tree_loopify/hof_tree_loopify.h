#ifndef INCLUDED_HOF_TREE_LOOPIFY
#define INCLUDED_HOF_TREE_LOOPIFY

#include <any>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

struct HofTreeLoopify {
  template <typename A> struct tree {
    // TYPES
    struct Leaf {};

    struct Node {
      std::shared_ptr<tree<A>> l;
      A x;
      std::shared_ptr<tree<A>> r;
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

    template <typename _U> explicit tree(const tree<_U> &_other) {
      if (std::holds_alternative<typename tree<_U>::Leaf>(_other.v())) {
        this->v_ = Leaf{};
      } else {
        const auto &[l, x, r] = std::get<typename tree<_U>::Node>(_other.v());
        this->v_ = Node{
            l ? std::make_shared<tree<A>>(*l) : nullptr,
            [&]() -> A {
              if constexpr (std::is_same_v<_U, std::any>) {
                if (x.type() == typeid(A))
                  return std::any_cast<A>(x);
                if constexpr (requires {
                                typename A::first_type;
                                typename A::second_type;
                              }) {
                  const auto &[_k, _v] =
                      std::any_cast<std::pair<std::any, std::any>>(x);
                  return A{
                      [&]() -> typename A::first_type {
                        if constexpr (std::is_same_v<typename A::first_type,
                                                     std::any>)
                          return _k;
                        else
                          return std::any_cast<typename A::first_type>(_k);
                      }(),
                      [&]() -> typename A::second_type {
                        if constexpr (std::is_same_v<typename A::second_type,
                                                     std::any>)
                          return _v;
                        else
                          return std::any_cast<typename A::second_type>(_v);
                      }()};
                }
                return std::any_cast<A>(x);
              } else
                return A(x);
            }(),
            r ? std::make_shared<tree<A>>(*r) : nullptr};
      }
    }

    static tree<A> leaf() { return tree(Leaf{}); }

    static tree<A> node(tree<A> l, A x, tree<A> r) {
      return tree(Node{std::make_shared<tree<A>>(std::move(l)), std::move(x),
                       std::make_shared<tree<A>>(std::move(r))});
    }

    // MANIPULATORS
    ~tree() {
      std::vector<std::shared_ptr<tree<A>>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<Node>(&_v)) {
          if (_alt->l) {
            _stack.push_back(std::move(_alt->l));
          }
          if (_alt->r) {
            _stack.push_back(std::move(_alt->r));
          }
        }
      };
      _drain(v_mut());
      while (!_stack.empty()) {
        auto _cur = std::move(_stack.back());
        _stack.pop_back();
        if (_cur.use_count() == 1) {
          _drain(_cur->v_mut());
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
      std::decay_t<T1> a1;
      tree<T1> a0_1;
    };

    /// _Combine_Node: receives partial results, combines with _result from
    /// final call.
    struct _Combine_Node {
      std::decay_t<T2> _result;
      tree<T1> a2;
      std::decay_t<T1> a1;
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
        _result = f0(std::move(_f.a0), std::move(_result), std::move(_f.a1),
                     std::move(_f.a2), std::move(_f._result));
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
      std::decay_t<T1> a1;
      tree<T1> a0_1;
    };

    /// _Combine_Node: receives partial results, combines with _result from
    /// final call.
    struct _Combine_Node {
      std::decay_t<T2> _result;
      tree<T1> a2;
      std::decay_t<T1> a1;
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
        _result = f0(std::move(_f.a0), std::move(_result), std::move(_f.a1),
                     std::move(_f.a2), std::move(_f._result));
      }
    }
    return _result;
  }

  static tree<uint64_t> depth_tree(uint64_t n);

  template <typename T1, typename T2, typename F0>
    requires std::is_invocable_r_v<T2, F0 &, T1 &>
  static tree<T2>
  tree_map(F0 &&f,
           const tree<T1> &t) { /// _Enter: captures varying parameters for each
                                /// recursive call.

    struct _Enter {
      const tree<T1> *t;
    };

    /// _After_Node: saves [a0, a1], dispatches next recursive call.
    struct _After_Node {
      const tree<T1> *a0;
      std::decay_t<T2> a1;
    };

    /// _Combine_Node: receives partial results, combines with _result from
    /// final call.
    struct _Combine_Node {
      tree<T2> _result;
      std::decay_t<T2> a1;
    };

    using _Frame = std::variant<_Enter, _After_Node, _Combine_Node>;
    tree<T2> _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{&t});
    /// Loopified tree_map: _Enter -> _After_Node -> _Combine_Node.
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
        _result = tree<T2>::node(std::move(_result), std::move(_f.a1),
                                 std::move(_f._result));
      }
    }
    return _result;
  }

  template <typename T1, typename T2, typename F1>
    requires std::is_invocable_r_v<T2, F1 &, T2 &, T1 &, T2 &>
  static T2
  tree_fold(T2 base, F1 &&f,
            const tree<T1> &t) { /// _Enter: captures varying parameters for
                                 /// each recursive call.

    struct _Enter {
      const tree<T1> *t;
    };

    /// _After_Node: saves [a0, a1], dispatches next recursive call.
    struct _After_Node {
      const tree<T1> *a0;
      std::decay_t<T1> a1;
    };

    /// _Combine_Node: receives partial results, combines with _result from
    /// final call.
    struct _Combine_Node {
      std::decay_t<T2> _result;
      std::decay_t<T1> a1;
    };

    using _Frame = std::variant<_Enter, _After_Node, _Combine_Node>;
    T2 _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{&t});
    /// Loopified tree_fold: _Enter -> _After_Node -> _Combine_Node.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const tree<T1> &t = *_f.t;
        if (std::holds_alternative<typename tree<T1>::Leaf>(t.v())) {
          _result = std::move(base);
        } else {
          const auto &[a0, a1, a2] = std::get<typename tree<T1>::Node>(t.v());
          _stack.emplace_back(_After_Node{a0.get(), a1});
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
            f(std::move(_result), std::move(_f.a1), std::move(_f._result));
      }
    }
    return _result;
  }

  template <typename T1, typename T2, typename T3, typename F0>
    requires std::is_invocable_r_v<T3, F0 &, T1 &, T2 &>
  static tree<T3>
  tree_zip_with(F0 &&f, const tree<T1> &t1,
                const tree<T2> &t2) { /// _Enter: captures varying parameters
                                      /// for each recursive call.

    struct _Enter {
      const tree<T2> *t2;
      const tree<T1> *t1;
    };

    /// _After_Node: saves [a00, a0, _s2], dispatches next recursive call.
    struct _After_Node {
      const tree<T2> *a00;
      const tree<T1> *a0;
      std::decay_t<T3> _s2;
    };

    /// _Combine_Node: receives partial results, combines with _result from
    /// final call.
    struct _Combine_Node {
      tree<T3> _result;
      std::decay_t<T3> _s1;
    };

    using _Frame = std::variant<_Enter, _After_Node, _Combine_Node>;
    tree<T3> _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{&t2, &t1});
    /// Loopified tree_zip_with: _Enter -> _After_Node -> _Combine_Node.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const tree<T2> &t2 = *_f.t2;
        const tree<T1> &t1 = *_f.t1;
        if (std::holds_alternative<typename tree<T1>::Leaf>(t1.v())) {
          _result = tree<T3>::leaf();
        } else {
          const auto &[a0, a1, a2] = std::get<typename tree<T1>::Node>(t1.v());
          if (std::holds_alternative<typename tree<T2>::Leaf>(t2.v())) {
            _result = tree<T3>::leaf();
          } else {
            const auto &[a00, a10, a20] =
                std::get<typename tree<T2>::Node>(t2.v());
            _stack.emplace_back(_After_Node{a00.get(), a0.get(), f(a1, a10)});
            _stack.emplace_back(_Enter{a20.get(), a2.get()});
          }
        }
      } else if (std::holds_alternative<_After_Node>(_frame)) {
        auto _f = std::move(std::get<_After_Node>(_frame));
        _stack.emplace_back(
            _Combine_Node{std::move(_result), std::move(_f._s2)});
        _stack.emplace_back(_Enter{_f.a00, _f.a0});
      } else {
        auto _f = std::move(std::get<_Combine_Node>(_frame));
        _result = tree<T3>::node(std::move(_result), std::move(_f._s1),
                                 std::move(_f._result));
      }
    }
    return _result;
  }

  template <typename T1, typename T2, typename T3, typename F0>
    requires std::is_invocable_r_v<std::pair<T3, T2>, F0 &, T3 &, T1 &>
  static std::pair<T3, tree<T2>>
  tree_map_accum(F0 &&f, T3 acc,
                 const tree<T1> &t) { /// _Enter: captures varying parameters
                                      /// for each recursive call.

    struct _Enter {
      const tree<T1> *t;
      T3 acc;
    };

    /// _Cont_Node: saves [a1, a2], resumes after recursive call, then processes
    /// rest.
    struct _Cont_Node {
      std::decay_t<T1> a1;
      const tree<T1> *a2;
    };

    /// _Cont_acc2: saves [l_, x_], resumes after recursive call, then processes
    /// rest.
    struct _Cont_acc2 {
      tree<T2> l_;
      std::decay_t<T2> x_;
    };

    using _Frame = std::variant<_Enter, _Cont_Node, _Cont_acc2>;
    std::pair<T3, tree<T2>> _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{&t, acc});
    /// Loopified tree_map_accum: _Enter -> _Cont_Node -> _Cont_acc2.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const tree<T1> &t = *_f.t;
        auto acc = std::move(_f.acc);
        if (std::holds_alternative<typename tree<T1>::Leaf>(t.v())) {
          _result = std::make_pair(std::move(acc), tree<T2>::leaf());
        } else {
          const auto &[a0, a1, a2] = std::get<typename tree<T1>::Node>(t.v());
          _stack.emplace_back(_Cont_Node{a1, a2.get()});
          _stack.emplace_back(_Enter{a0.get(), std::move(acc)});
        }
      } else if (std::holds_alternative<_Cont_Node>(_frame)) {
        auto _f = std::move(std::get<_Cont_Node>(_frame));
        auto a1 = std::move(_f.a1);
        const tree<T1> &a2 = *_f.a2;
        std::pair<T3, tree<T2>> _rc1 = std::move(_result);
        auto [acc1, l_] = _rc1;
        auto [acc2, x_] = f(acc1, a1);
        _stack.emplace_back(_Cont_acc2{l_, x_});
        _stack.emplace_back(_Enter{&a2, acc2});
      } else {
        auto _f = std::move(std::get<_Cont_acc2>(_frame));
        tree<T2> l_ = std::move(_f.l_);
        auto x_ = std::move(_f.x_);
        std::pair<T3, tree<T2>> _rc2 = std::move(_result);
        auto [acc3, r_] = _rc2;
        _result = std::make_pair(
            acc3, tree<T2>::node(std::move(l_), x_, std::move(r_)));
      }
    }
    return _result;
  }

  static inline const tree<uint64_t> small_tree = tree<uint64_t>::node(
      tree<uint64_t>::node(
          tree<uint64_t>::node(tree<uint64_t>::leaf(), UINT64_C(1),
                               tree<uint64_t>::leaf()),
          UINT64_C(2),
          tree<uint64_t>::node(tree<uint64_t>::leaf(), UINT64_C(3),
                               tree<uint64_t>::leaf())),
      UINT64_C(4),
      tree<uint64_t>::node(
          tree<uint64_t>::node(tree<uint64_t>::leaf(), UINT64_C(5),
                               tree<uint64_t>::leaf()),
          UINT64_C(6),
          tree<uint64_t>::node(tree<uint64_t>::leaf(), UINT64_C(7),
                               tree<uint64_t>::leaf())));
  static inline const tree<uint64_t> mapped = tree_map<uint64_t, uint64_t>(
      [](uint64_t x) { return (x * UINT64_C(2)); }, small_tree);
  static inline const uint64_t folded = tree_fold<uint64_t, uint64_t>(
      UINT64_C(0),
      [](uint64_t l, uint64_t x, uint64_t r) { return ((l + x) + r); },
      small_tree);
  static inline const tree<uint64_t> zipped =
      tree_zip_with<uint64_t, uint64_t, uint64_t>(
          [](uint64_t _x0, uint64_t _x1) -> uint64_t { return (_x0 + _x1); },
          small_tree, small_tree);
  static inline const std::pair<uint64_t, tree<uint64_t>> accum =
      tree_map_accum<uint64_t, uint64_t, uint64_t>(
          [](uint64_t s, uint64_t x) { return std::make_pair((s + x), s); },
          UINT64_C(0), small_tree);
  static inline const tree<uint64_t> deep = depth_tree(UINT64_C(50000));
};

#endif // INCLUDED_HOF_TREE_LOOPIFY
