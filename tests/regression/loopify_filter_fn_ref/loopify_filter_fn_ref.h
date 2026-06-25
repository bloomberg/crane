#ifndef INCLUDED_LOOPIFY_FILTER_FN_REF
#define INCLUDED_LOOPIFY_FILTER_FN_REF

#include <any>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

struct LoopifyFilterFnRef {
  /// A binary tree with elements at nodes.
  template <typename A> struct tree {
    // TYPES
    struct Leaf {};

    struct Node {
      std::shared_ptr<tree<A>> a0;
      A a1;
      std::shared_ptr<tree<A>> a2;
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
        const auto &[a0, a1, a2] =
            std::get<typename tree<_U>::Node>(_other.v());
        this->v_ = Node{
            a0 ? std::make_shared<tree<A>>(*a0) : nullptr,
            [&]() -> A {
              if constexpr (std::is_same_v<_U, std::any>) {
                if (a1.type() == typeid(A))
                  return std::any_cast<A>(a1);
                if constexpr (requires {
                                typename A::first_type;
                                typename A::second_type;
                              }) {
                  const auto &[_k, _v] =
                      std::any_cast<std::pair<std::any, std::any>>(a1);
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
                return std::any_cast<A>(a1);
              } else
                return A(a1);
            }(),
            a2 ? std::make_shared<tree<A>>(*a2) : nullptr};
      }
    }

    static tree<A> leaf() { return tree(Leaf{}); }

    static tree<A> node(tree<A> a0, A a1, tree<A> a2) {
      return tree(Node{std::make_shared<tree<A>>(std::move(a0)), std::move(a1),
                       std::make_shared<tree<A>>(std::move(a2))});
    }

    // MANIPULATORS
    ~tree() {
      std::vector<std::shared_ptr<tree<A>>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<Node>(&_v)) {
          if (_alt->a0) {
            _stack.push_back(std::move(_alt->a0));
          }
          if (_alt->a2) {
            _stack.push_back(std::move(_alt->a2));
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

  /// Recursive filter: takes a predicate f and recurses on both subtrees.
  /// When loopified, f is stored in continuation frame structs.
  /// If f is passed as a function reference (e.g. a named function),
  /// the template parameter F0 deduces to a reference type, and the
  /// generated frame struct field F0 f becomes ill-formed with std::move.
  template <typename T1, typename F0>
    requires std::is_invocable_r_v<bool, F0 &, T1 &>
  static tree<T1>
  filter(F0 &&f,
         const tree<T1> &t) { /// _Enter: captures varying parameters for each
                              /// recursive call.

    struct _Enter {
      const tree<T1> *t;
    };

    /// _Cont_Node: saves [a1, a2], resumes after recursive call, then processes
    /// rest.
    struct _Cont_Node {
      std::decay_t<T1> a1;
      const tree<T1> *a2;
    };

    /// _Cont_Node_1: saves [a1, l_], resumes after recursive call, then
    /// processes rest.
    struct _Cont_Node_1 {
      std::decay_t<T1> a1;
      tree<T1> l_;
    };

    using _Frame = std::variant<_Enter, _Cont_Node, _Cont_Node_1>;
    tree<T1> _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{&t});
    /// Loopified filter: _Enter -> _Cont_Node -> _Cont_Node_1.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const tree<T1> &t = *_f.t;
        if (std::holds_alternative<typename tree<T1>::Leaf>(t.v())) {
          _result = tree<T1>::leaf();
        } else {
          const auto &[a0, a1, a2] = std::get<typename tree<T1>::Node>(t.v());
          _stack.emplace_back(_Cont_Node{a1, a2.get()});
          _stack.emplace_back(_Enter{a0.get()});
        }
      } else if (std::holds_alternative<_Cont_Node>(_frame)) {
        auto _f = std::move(std::get<_Cont_Node>(_frame));
        auto a1 = std::move(_f.a1);
        const tree<T1> &a2 = *_f.a2;
        tree<T1> l_ = std::move(_result);
        _stack.emplace_back(_Cont_Node_1{a1, std::move(l_)});
        _stack.emplace_back(_Enter{&a2});
      } else {
        auto _f = std::move(std::get<_Cont_Node_1>(_frame));
        auto a1 = std::move(_f.a1);
        tree<T1> l_ = std::move(_f.l_);
        tree<T1> r_ = std::move(_result);
        if (f(a1)) {
          _result = tree<T1>::node(std::move(l_), a1, std::move(r_));
        } else {
          _result = std::move(l_);
        }
      }
    }
    return _result;
  }

  /// A concrete predicate — will be passed as a function reference.
  static bool is_positive(uint64_t n);
  /// Entry point that calls filter with a named function.
  static inline const tree<uint64_t> test_filter = filter<uint64_t>(
      is_positive, tree<uint64_t>::node(
                       tree<uint64_t>::node(tree<uint64_t>::leaf(), UINT64_C(0),
                                            tree<uint64_t>::leaf()),
                       UINT64_C(1),
                       tree<uint64_t>::node(tree<uint64_t>::leaf(), UINT64_C(2),
                                            tree<uint64_t>::leaf())));
};

#endif // INCLUDED_LOOPIFY_FILTER_FN_REF
