#ifndef INCLUDED_HOF_CLOSURE_ESCAPE
#define INCLUDED_HOF_CLOSURE_ESCAPE

#include <functional>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

struct HofClosureEscape {
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

    static std::unique_ptr<tree> leaf_uptr() {
      return std::make_unique<tree>(Leaf{});
    }

    static std::unique_ptr<tree> node_uptr(const std::shared_ptr<tree> &a0,
                                           unsigned int a1,
                                           const std::shared_ptr<tree> &a2) {
      return std::make_unique<tree>(Node{a0, std::move(a1), a2});
    }

    static std::unique_ptr<tree> node_uptr(std::shared_ptr<tree> &&a0,
                                           unsigned int a1,
                                           std::shared_ptr<tree> &&a2) {
      return std::make_unique<tree>(
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
    return std::visit(
        Overloaded{[&](const typename tree::Leaf _args) -> T1 { return f; },
                   [&](const typename tree::Node _args) -> T1 {
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
        Overloaded{[&](const typename tree::Leaf _args) -> T1 { return f; },
                   [&](const typename tree::Node _args) -> T1 {
                     return f0(_args.d_a0, tree_rec<T1>(f, f0, _args.d_a0),
                               _args.d_a1, _args.d_a2,
                               tree_rec<T1>(f, f0, _args.d_a2));
                   }},
        t->v());
  }

  __attribute__((pure)) static unsigned int
  sum_values(const std::shared_ptr<tree> &t, const unsigned int x);

  /// wrap_some is a helper that takes a function and wraps it in Some.
  /// The partial application happens at the CALL SITE of wrap_some,
  /// so the & lambda is created by the caller and passed through.
  template <MapsTo<unsigned int, unsigned int> F0>
  __attribute__((
      pure)) static std::optional<std::function<unsigned int(unsigned int)>>
  wrap_some(F0 &&f) {
    return std::make_optional<std::function<unsigned int(unsigned int)>>(f);
  }

  /// BUG: The partial application sum_values t creates a & lambda.
  /// Even though wrap_some just passes f through to Some,
  /// the & lambda was created in hof_escape's stack frame.
  /// When hof_escape returns, captured t is destroyed.
  __attribute__((
      pure)) static std::optional<std::function<unsigned int(unsigned int)>>
  hof_escape(const std::shared_ptr<tree> &t);
  __attribute__((pure)) static unsigned int
  apply_option(const std::optional<std::function<unsigned int(unsigned int)>> o,
               const unsigned int x); /// Clobber stack, then use the closure.
  static inline const unsigned int bug_hof_escape = []() {
    std::unique_ptr<tree> t1 =
        tree::node_uptr(tree::node(tree::leaf(), 10u, tree::leaf()), 20u,
                        tree::node(tree::leaf(), 30u, tree::leaf()));
    std::optional<std::function<unsigned int(unsigned int)>> o1 =
        hof_escape(std::move(t1));
    return apply_option(std::move(o1), 0u);
  }();
};

#endif // INCLUDED_HOF_CLOSURE_ESCAPE
