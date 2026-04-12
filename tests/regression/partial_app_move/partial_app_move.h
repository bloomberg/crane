#ifndef INCLUDED_PARTIAL_APP_MOVE
#define INCLUDED_PARTIAL_APP_MOVE

#include <functional>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

struct PartialAppMove {
  struct tree {
    // TYPES
    struct Leaf {};

    struct Node {
      std::shared_ptr<tree> d_a0;
      unsigned int d_a1;
      std::shared_ptr<tree> d_a2;
    };

    using variant_t = std::variant<Leaf, Node>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    explicit tree(Leaf _v) : d_v_(std::move(_v)) {}

    explicit tree(Node _v) : d_v_(std::move(_v)) {}

    static std::shared_ptr<tree> leaf() {
      return std::make_shared<tree>(Leaf{});
    }

    static std::shared_ptr<tree> node(const std::shared_ptr<tree> &a0,
                                      unsigned int a1,
                                      const std::shared_ptr<tree> &a2) {
      return std::make_shared<tree>(Node{a0, std::move(a1), a2});
    }

    static std::shared_ptr<tree> node(std::shared_ptr<tree> &&a0,
                                      unsigned int a1,
                                      std::shared_ptr<tree> &&a2) {
      return std::make_shared<tree>(
          Node{std::move(a0), std::move(a1), std::move(a2)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, MapsTo<T1, std::shared_ptr<tree>, T1, unsigned int,
                                std::shared_ptr<tree>, T1>
                             F1>
  static T1 tree_rect(const T1 f, F1 &&f0, const std::shared_ptr<tree> &t) {
    struct _Enter {
      const std::shared_ptr<tree> t;
    };

    struct _Call1 {
      decltype(std::declval<const typename tree::Node &>().d_a0) _s0;
      decltype(std::declval<const typename tree::Node &>().d_a2) _s1;
      decltype(std::declval<const typename tree::Node &>().d_a1) _s2;
      decltype(std::declval<const typename tree::Node &>().d_a0) _s3;
    };

    struct _Call2 {
      T1 _s0;
      decltype(std::declval<const typename tree::Node &>().d_a2) _s1;
      decltype(std::declval<const typename tree::Node &>().d_a1) _s2;
      decltype(std::declval<const typename tree::Node &>().d_a0) _s3;
    };

    using _Frame = std::variant<_Enter, _Call1, _Call2>;
    T1 _result{};
    std::vector<_Frame> _stack;
    _stack.push_back(_Enter{t});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      std::visit(
          Overloaded{
              [&](_Enter _f) {
                const std::shared_ptr<tree> t = _f.t;
                std::visit(
                    Overloaded{[&](const typename tree::Leaf &) -> void {
                                 _result = f;
                               },
                               [&](const typename tree::Node &_args) -> void {
                                 _stack.push_back(_Call1{_args.d_a0, _args.d_a2,
                                                         _args.d_a1,
                                                         _args.d_a0});
                                 _stack.push_back(_Enter{_args.d_a2});
                               }},
                    t->v());
              },
              [&](_Call1 _f) {
                _stack.push_back(_Call2{_result, _f._s1, _f._s2, _f._s3});
                _stack.push_back(_Enter{_f._s0});
              },
              [&](_Call2 _f) {
                _result = f0(_f._s3, _result, _f._s2, _f._s1, _f._s0);
              }},
          _frame);
    }
    return _result;
  }

  template <typename T1, MapsTo<T1, std::shared_ptr<tree>, T1, unsigned int,
                                std::shared_ptr<tree>, T1>
                             F1>
  static T1 tree_rec(const T1 f, F1 &&f0, const std::shared_ptr<tree> &t) {
    struct _Enter {
      const std::shared_ptr<tree> t;
    };

    struct _Call1 {
      decltype(std::declval<const typename tree::Node &>().d_a0) _s0;
      decltype(std::declval<const typename tree::Node &>().d_a2) _s1;
      decltype(std::declval<const typename tree::Node &>().d_a1) _s2;
      decltype(std::declval<const typename tree::Node &>().d_a0) _s3;
    };

    struct _Call2 {
      T1 _s0;
      decltype(std::declval<const typename tree::Node &>().d_a2) _s1;
      decltype(std::declval<const typename tree::Node &>().d_a1) _s2;
      decltype(std::declval<const typename tree::Node &>().d_a0) _s3;
    };

    using _Frame = std::variant<_Enter, _Call1, _Call2>;
    T1 _result{};
    std::vector<_Frame> _stack;
    _stack.push_back(_Enter{t});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      std::visit(
          Overloaded{
              [&](_Enter _f) {
                const std::shared_ptr<tree> t = _f.t;
                std::visit(
                    Overloaded{[&](const typename tree::Leaf &) -> void {
                                 _result = f;
                               },
                               [&](const typename tree::Node &_args) -> void {
                                 _stack.push_back(_Call1{_args.d_a0, _args.d_a2,
                                                         _args.d_a1,
                                                         _args.d_a0});
                                 _stack.push_back(_Enter{_args.d_a2});
                               }},
                    t->v());
              },
              [&](_Call1 _f) {
                _stack.push_back(_Call2{_result, _f._s1, _f._s2, _f._s3});
                _stack.push_back(_Enter{_f._s0});
              },
              [&](_Call2 _f) {
                _result = f0(_f._s3, _result, _f._s2, _f._s1, _f._s0);
              }},
          _frame);
    }
    return _result;
  }

  /// A function taking two args: tree -> nat -> nat.
  /// Partial application of this to a tree creates a
  /// closure nat -> nat in C++ via & lambda.
  __attribute__((pure)) static unsigned int
  sum_values(const std::shared_ptr<tree> &t, const unsigned int x);
  /// Wrap a tree inside another Node.
  /// In C++, this calls tree::node() which has rvalue ref overloads.
  /// If escape analysis adds std::move(t) here, the move is REAL.
  static std::shared_ptr<tree> wrap(std::shared_ptr<tree> t);
  /// BUG TRIGGER: partial application creates a & lambda capturing t,
  /// then t is passed to a constructor (actually moved via rvalue ref),
  /// then the lambda accesses the moved-from t.
  __attribute__((pure)) static unsigned int
  trigger_bug(std::shared_ptr<tree> t);
  /// Build a tree and trigger the bug.
  static inline const unsigned int run_bug =
      trigger_bug(tree::node(tree::node(tree::leaf(), 10u, tree::leaf()), 20u,
                             tree::node(tree::leaf(), 30u, tree::leaf())));
  /// Inline version: t is a local variable, not a function parameter.
  /// This is where move optimization might actually move t.
  static inline const unsigned int inline_bug = []() {
    return []() {
      std::shared_ptr<tree> t =
          tree::node(tree::node(tree::leaf(), 10u, tree::leaf()), 20u,
                     tree::node(tree::leaf(), 30u, tree::leaf()));
      std::function<unsigned int(unsigned int)> f =
          [=](unsigned int _x0) mutable -> unsigned int {
        return sum_values(t, _x0);
      };
      std::shared_ptr<tree> w = tree::node(t, 42u, tree::leaf());
      return std::visit(
          Overloaded{[&](const typename tree::Leaf &) -> unsigned int {
                       return f(0u);
                     },
                     [&](const typename tree::Node &) -> unsigned int {
                       return f(99u);
                     }},
          w->v());
    }();
  }();
  /// Same but using wrap function.
  static inline const unsigned int inline_bug2 = []() {
    return []() {
      std::shared_ptr<tree> t =
          tree::node(tree::node(tree::leaf(), 10u, tree::leaf()), 20u,
                     tree::node(tree::leaf(), 30u, tree::leaf()));
      std::function<unsigned int(unsigned int)> f =
          [=](unsigned int _x0) mutable -> unsigned int {
        return sum_values(t, _x0);
      };
      std::shared_ptr<tree> w = wrap(std::move(t));
      return std::visit(
          Overloaded{[&](const typename tree::Leaf &) -> unsigned int {
                       return f(0u);
                     },
                     [&](const typename tree::Node &) -> unsigned int {
                       return f(99u);
                     }},
          w->v());
    }();
  }();
};

#endif // INCLUDED_PARTIAL_APP_MOVE
