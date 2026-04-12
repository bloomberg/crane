#ifndef INCLUDED_MOVE_SAFETY
#define INCLUDED_MOVE_SAFETY

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

struct MoveSafety {
  struct tree : public std::enable_shared_from_this<tree> {
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

    /// A function that stores its tree argument inside a constructor.
    /// This causes the parameter to be passed by value (it "escapes").
    std::shared_ptr<tree> wrap_tree() const {
      return tree::node(std::const_pointer_cast<tree>(this->shared_from_this()),
                        0u, tree::leaf());
    }

    __attribute__((pure)) unsigned int sum_values(const unsigned int x) const {
      return std::visit(
          Overloaded{
              [&](const typename tree::Leaf &) -> unsigned int { return x; },
              [&](const typename tree::Node &_args) -> unsigned int {
                return std::visit(
                    Overloaded{
                        [&](const typename tree::Leaf &) -> unsigned int {
                          return (_args.d_a1 + x);
                        },
                        [&](const typename tree::Node &_args0) -> unsigned int {
                          return std::visit(
                              Overloaded{[&](const typename tree::Leaf &)
                                             -> unsigned int {
                                           return (_args0.d_a1 + x);
                                         },
                                         [&](const typename tree::Node &_args1)
                                             -> unsigned int {
                                           return (
                                               ((_args0.d_a1 + _args1.d_a1) +
                                                _args.d_a1) +
                                               x);
                                         }},
                              _args.d_a2->v());
                        }},
                    _args.d_a0->v());
              }},
          this->v());
    }
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

  /// A wrapper for closures.
  struct fn_box {
    // TYPES
    struct Box {
      std::function<unsigned int(unsigned int)> d_a0;
    };

    using variant_t = std::variant<Box>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    explicit fn_box(Box _v) : d_v_(std::move(_v)) {}

    static std::shared_ptr<fn_box>
    box(std::function<unsigned int(unsigned int)> a0) {
      return std::make_shared<fn_box>(Box{std::move(a0)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    __attribute__((pure)) unsigned int apply_box(const unsigned int x) const {
      return std::visit(
          Overloaded{[&](const typename fn_box::Box &_args) -> unsigned int {
            return _args.d_a0(x);
          }},
          this->v());
    }

    template <typename T1,
              MapsTo<T1, std::function<unsigned int(unsigned int)>> F0>
    T1 fn_box_rec(F0 &&f) const {
      return std::visit(
          Overloaded{[&](const typename fn_box::Box &_args) -> T1 {
            return f(_args.d_a0);
          }},
          this->v());
    }

    template <typename T1,
              MapsTo<T1, std::function<unsigned int(unsigned int)>> F0>
    T1 fn_box_rect(F0 &&f) const {
      return std::visit(
          Overloaded{[&](const typename fn_box::Box &_args) -> T1 {
            return f(_args.d_a0);
          }},
          this->v());
    }
  };

  /// TEST 1: Partial application + function taking by value.
  /// The & lambda from partial application captures t by reference.
  /// Then wrap_tree takes t by value, so std::move(t) is generated.
  /// The lambda then holds a dangling reference.
  static inline const unsigned int bug_partial_then_wrap = []() {
    std::shared_ptr<tree> t =
        tree::node(tree::node(tree::leaf(), 10u, tree::leaf()), 20u,
                   tree::node(tree::leaf(), 30u, tree::leaf()));
    return std::move(t)->sum_values(99u);
  }();
  /// TEST 2: Store partial application in a Box.
  /// If the eta-expanded lambda uses & capture,
  /// the Box will hold a dangling reference after the
  /// function returns.
  static std::shared_ptr<fn_box> make_box(std::shared_ptr<tree> t);
  static inline const unsigned int bug_box_escape = []() {
    std::shared_ptr<tree> t =
        tree::node(tree::node(tree::leaf(), 10u, tree::leaf()), 20u,
                   tree::node(tree::leaf(), 30u, tree::leaf()));
    std::shared_ptr<fn_box> b = make_box(std::move(t));
    return std::move(b)->apply_box(99u);
  }();
  /// TEST 3: Two partial applications of same variable.
  /// Second one should not move t.
  static inline const unsigned int bug_double_partial = []() {
    return []() {
      std::shared_ptr<tree> t =
          tree::node(tree::node(tree::leaf(), 10u, tree::leaf()), 20u,
                     tree::node(tree::leaf(), 30u, tree::leaf()));
      std::function<unsigned int(unsigned int)> f =
          [=](unsigned int _x0) mutable -> unsigned int {
        return t->sum_values(_x0);
      };
      std::function<unsigned int(unsigned int)> g =
          [&](unsigned int _x0) -> unsigned int {
        return std::move(t)->sum_values(_x0);
      };
      return (f(1u) + g(2u));
    }();
  }();
  /// TEST 4: Partial application followed by identity function
  /// that takes by value (returns its argument).
  static std::shared_ptr<tree> tree_id(std::shared_ptr<tree> t);
  static inline const unsigned int bug_partial_then_id = []() {
    return []() {
      std::shared_ptr<tree> t =
          tree::node(tree::node(tree::leaf(), 10u, tree::leaf()), 20u,
                     tree::node(tree::leaf(), 30u, tree::leaf()));
      std::function<unsigned int(unsigned int)> f =
          [=](unsigned int _x0) mutable -> unsigned int {
        return t->sum_values(_x0);
      };
      std::shared_ptr<tree> t2 = tree_id(std::move(t));
      return std::visit(
          Overloaded{[&](const typename tree::Leaf &) -> unsigned int {
                       return f(0u);
                     },
                     [&](const typename tree::Node &_args) -> unsigned int {
                       return f(_args.d_a1);
                     }},
          t2->v());
    }();
  }();
};

#endif // INCLUDED_MOVE_SAFETY
