#ifndef INCLUDED_OPTION_SOME_ESCAPE
#define INCLUDED_OPTION_SOME_ESCAPE

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

struct OptionSomeEscape {
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
  };

  template <typename T1, MapsTo<T1, std::shared_ptr<tree>, T1, unsigned int,
                                std::shared_ptr<tree>, T1>
                             F1>
  static T1 tree_rect(const T1 f, F1 &&f0, const std::shared_ptr<tree> &t) {
    if (std::holds_alternative<typename tree::Leaf>(t->v())) {
      return f;
    } else {
      const auto &_m = *std::get_if<typename tree::Node>(&t->v());
      return f0(_m.d_a0, tree_rect<T1>(f, f0, _m.d_a0), _m.d_a1, _m.d_a2,
                tree_rect<T1>(f, f0, _m.d_a2));
    }
  }

  template <typename T1, MapsTo<T1, std::shared_ptr<tree>, T1, unsigned int,
                                std::shared_ptr<tree>, T1>
                             F1>
  static T1 tree_rec(const T1 f, F1 &&f0, const std::shared_ptr<tree> &t) {
    if (std::holds_alternative<typename tree::Leaf>(t->v())) {
      return f;
    } else {
      const auto &_m = *std::get_if<typename tree::Node>(&t->v());
      return f0(_m.d_a0, tree_rec<T1>(f, f0, _m.d_a0), _m.d_a1, _m.d_a2,
                tree_rec<T1>(f, f0, _m.d_a2));
    }
  }

  __attribute__((pure)) static unsigned int
  sum_values(const std::shared_ptr<tree> &t, const unsigned int x);
  /// BUG: Partial application stored in Some (std::make_optional).
  /// The & lambda captures parameter t by reference.
  /// return_captures_by_value doesn't handle lambdas inside
  /// std::make_optional. When the function returns, t is destroyed.
  __attribute__((
      pure)) static std::optional<std::function<unsigned int(unsigned int)>>
  option_escape(std::shared_ptr<tree> t);
  __attribute__((pure)) static unsigned int
  apply_option(const std::optional<std::function<unsigned int(unsigned int)>> o,
               const unsigned int
                   x); /// Clobber stack, then use the closure from the option.
  static inline const unsigned int bug_option_some = []() {
    std::shared_ptr<tree> t1 =
        tree::node(tree::node(tree::leaf(), 10u, tree::leaf()), 20u,
                   tree::node(tree::leaf(), 30u, tree::leaf()));
    std::optional<std::function<unsigned int(unsigned int)>> o1 =
        option_escape(std::move(t1));
    return apply_option(o1, 0u);
  }();
};

#endif // INCLUDED_OPTION_SOME_ESCAPE
