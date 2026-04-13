#ifndef INCLUDED_CLOSURE_CAPTURE_MATCH
#define INCLUDED_CLOSURE_CAPTURE_MATCH

#include <functional>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

struct ClosureCaptureMatch {
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
    explicit tree(Leaf _v) : d_v_(_v) {}

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

    /// Closure that captures a shared_ptr and is called AFTER
    /// the original data structure is dropped.
    __attribute__((pure)) unsigned int capture_and_drop() const {
      std::function<std::shared_ptr<tree>(unsigned int)> f =
          [&](unsigned int _x0) -> std::shared_ptr<tree> {
        return this->make_inserter(_x0);
      };
      return std::visit(
          Overloaded{
              [](const typename tree::Leaf &) -> unsigned int { return 0u; },
              [](const typename tree::Node &_args) -> unsigned int {
                return _args.d_a1;
              }},
          f(42u)->v());
    }

    /// Nested match returning a closure.
    /// The closure captures fields from BOTH match levels.
    __attribute__((pure)) unsigned int
    deep_capture(const unsigned int x) const {
      return std::visit(
          Overloaded{
              [&](const typename tree::Leaf &) -> auto { return x; },
              [&](const typename tree::Node &_args) -> auto {
                return std::visit(
                    Overloaded{
                        [&](const typename tree::Leaf &) -> auto {
                          return (_args.d_a1 + x);
                        },
                        [&](const typename tree::Node &_args0) -> auto {
                          return std::visit(
                              Overloaded{
                                  [&](const typename tree::Leaf &) -> auto {
                                    return (_args0.d_a1 + x);
                                  },
                                  [&](const typename tree::Node &_args1)
                                      -> auto {
                                    return (((_args0.d_a1 + _args1.d_a1) +
                                             _args.d_a1) +
                                            x);
                                  }},
                              _args.d_a2->v());
                        }},
                    _args.d_a0->v());
              }},
          this->v());
    }

    /// Return a closure from a match branch.
    /// The closure captures shared_ptr fields (left, right subtrees).
    /// If capture is by-reference instead of by-value, the closure
    /// would have dangling references after the match lambda returns.
    std::shared_ptr<tree> make_inserter(const unsigned int v) const {
      return std::visit(
          Overloaded{[&](const typename tree::Leaf &) -> auto {
                       return tree::node(tree::leaf(), v, tree::leaf());
                     },
                     [&](const typename tree::Node &_args) -> auto {
                       return tree::node(_args.d_a0, v, _args.d_a2);
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
    _stack.emplace_back(_Enter{t});
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
                                 _stack.emplace_back(
                                     _Call1{_args.d_a0, _args.d_a2, _args.d_a1,
                                            _args.d_a0});
                                 _stack.emplace_back(_Enter{_args.d_a2});
                               }},
                    t->v());
              },
              [&](_Call1 _f) {
                _stack.emplace_back(_Call2{_result, _f._s1, _f._s2, _f._s3});
                _stack.emplace_back(_Enter{_f._s0});
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
    _stack.emplace_back(_Enter{t});
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
                                 _stack.emplace_back(
                                     _Call1{_args.d_a0, _args.d_a2, _args.d_a1,
                                            _args.d_a0});
                                 _stack.emplace_back(_Enter{_args.d_a2});
                               }},
                    t->v());
              },
              [&](_Call1 _f) {
                _stack.emplace_back(_Call2{_result, _f._s1, _f._s2, _f._s3});
                _stack.emplace_back(_Enter{_f._s0});
              },
              [&](_Call2 _f) {
                _result = f0(_f._s3, _result, _f._s2, _f._s1, _f._s0);
              }},
          _frame);
    }
    return _result;
  }

  /// Store a closure in a data structure (not directly returned).
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

    __attribute__((pure)) unsigned int unbox(const unsigned int x) const {
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

  static std::shared_ptr<fn_box> box_from_match(const std::shared_ptr<tree> &t);
  /// Build a tree, extract closures, drop the tree, use closures.
  static inline const unsigned int test_capture = []() {
    return []() {
      std::shared_ptr<tree> t =
          tree::node(tree::node(tree::leaf(), 10u, tree::leaf()), 20u,
                     tree::node(tree::leaf(), 30u, tree::leaf()));
      std::function<unsigned int(unsigned int)> f =
          [=](unsigned int _x0) mutable -> unsigned int {
        return t->deep_capture(_x0);
      };
      std::shared_ptr<fn_box> b = box_from_match(std::move(t));
      return (f(5u) + std::move(b)->unbox(7u));
    }();
  }();
};

#endif // INCLUDED_CLOSURE_CAPTURE_MATCH
