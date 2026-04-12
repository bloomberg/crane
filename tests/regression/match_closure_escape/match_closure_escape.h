#ifndef INCLUDED_MATCH_CLOSURE_ESCAPE
#define INCLUDED_MATCH_CLOSURE_ESCAPE

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

struct MatchClosureEscape {
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
    return std::visit(
        Overloaded{[&](const typename tree::Leaf &) -> T1 { return f; },
                   [&](const typename tree::Node &_args) -> T1 {
                     return f0(_args.d_a0, tree_rect<T1>(f, f0, _args.d_a0),
                               _args.d_a1, _args.d_a2,
                               tree_rect<T1>(f, f0, _args.d_a2));
                   }},
        t->v());
  }

  template <typename T1, MapsTo<T1, std::shared_ptr<tree>, T1, unsigned int,
                                std::shared_ptr<tree>, T1>
                             F1>
  static T1 tree_rec(const T1 f, F1 &&f0, const std::shared_ptr<tree> &t) {
    return std::visit(
        Overloaded{[&](const typename tree::Leaf &) -> T1 { return f; },
                   [&](const typename tree::Node &_args) -> T1 {
                     return f0(_args.d_a0, tree_rec<T1>(f, f0, _args.d_a0),
                               _args.d_a1, _args.d_a2,
                               tree_rec<T1>(f, f0, _args.d_a2));
                   }},
        t->v());
  }

  /// A box for closures, forces the closure to be stored on the heap.
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

  /// BUG TRIGGER: match_arm_box
  /// The partial application sum_values l inside a match arm creates a
  /// & lambda capturing the match-bound variable _args (from std::visit).
  /// This lambda is stored in a Box constructor argument.
  /// return_captures_by_value does NOT handle lambdas inside constructor args.
  /// When the visit lambda returns, _args goes out of scope, and the Box
  /// holds a dangling reference to a destroyed shared_ptr.
  static std::shared_ptr<fn_box> match_arm_box(const std::shared_ptr<tree> &t);
  /// Use a top-level definition to get a shared_ptr (not unique_ptr).
  static inline const std::shared_ptr<tree> test_tree =
      tree::node(tree::node(tree::leaf(), 10u, tree::leaf()), 20u,
                 tree::node(tree::leaf(), 30u, tree::leaf()));
  static inline const unsigned int bug_match_box =
      match_arm_box(test_tree)->apply_box(99u);
};

#endif // INCLUDED_MATCH_CLOSURE_ESCAPE
