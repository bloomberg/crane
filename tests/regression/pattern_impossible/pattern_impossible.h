#ifndef INCLUDED_PATTERN_IMPOSSIBLE
#define INCLUDED_PATTERN_IMPOSSIBLE

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

struct PatternImpossible {
  enum class Three { ONE, TWO, THREE };

  template <typename T1> static T1 three_rect(T1 f, T1 f0, T1 f1, Three t) {
    switch (t) {
    case Three::ONE: {
      return f;
    }
    case Three::TWO: {
      return f0;
    }
    case Three::THREE: {
      return f1;
    }
    default:
      std::unreachable();
    }
  }

  template <typename T1> static T1 three_rec(T1 f, T1 f0, T1 f1, Three t) {
    switch (t) {
    case Three::ONE: {
      return f;
    }
    case Three::TWO: {
      return f0;
    }
    case Three::THREE: {
      return f1;
    }
    default:
      std::unreachable();
    }
  }

  struct nested {
    // TYPES
    struct Leaf {
      uint64_t a0;
    };

    struct Node {
      std::shared_ptr<nested> a0;
      std::shared_ptr<nested> a1;
    };

    using variant_t = std::variant<Leaf, Node>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    nested() {}

    explicit nested(Leaf _v) : v_(std::move(_v)) {}

    explicit nested(Node _v) : v_(std::move(_v)) {}

    static nested leaf(uint64_t a0) { return nested(Leaf{a0}); }

    static nested node(nested a0, nested a1) {
      return nested(Node{std::make_shared<nested>(std::move(a0)),
                         std::make_shared<nested>(std::move(a1))});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename F0, typename F1>
    requires std::is_invocable_r_v<T1, F0 &, uint64_t &> &&
             std::is_invocable_r_v<T1, F1 &, nested &, T1 &, nested &, T1 &>
  static T1 nested_rect(F0 &&f, F1 &&f0, const nested &n) {
    if (std::holds_alternative<typename nested::Leaf>(n.v())) {
      const auto &[a0] = std::get<typename nested::Leaf>(n.v());
      return f(a0);
    } else {
      const auto &[a0, a1] = std::get<typename nested::Node>(n.v());
      return f0(*a0, nested_rect<T1>(f, f0, *a0), *a1,
                nested_rect<T1>(f, f0, *a1));
    }
  }

  template <typename T1, typename F0, typename F1>
    requires std::is_invocable_r_v<T1, F0 &, uint64_t &> &&
             std::is_invocable_r_v<T1, F1 &, nested &, T1 &, nested &, T1 &>
  static T1 nested_rec(F0 &&f, F1 &&f0, const nested &n) {
    if (std::holds_alternative<typename nested::Leaf>(n.v())) {
      const auto &[a0] = std::get<typename nested::Leaf>(n.v());
      return f(a0);
    } else {
      const auto &[a0, a1] = std::get<typename nested::Node>(n.v());
      return f0(*a0, nested_rec<T1>(f, f0, *a0), *a1,
                nested_rec<T1>(f, f0, *a1));
    }
  }

  static uint64_t complex_match(Three x);
  static uint64_t nested_match(const nested &n);
  static uint64_t double_match(Three x, Three y);
  static uint64_t multi_arg_pattern(const nested &n);
  static inline const uint64_t test1 = complex_match(Three::ONE);
  static inline const uint64_t test2 = nested_match(
      nested::node(nested::leaf(UINT64_C(5)), nested::leaf(UINT64_C(10))));
  static inline const uint64_t test3 = double_match(Three::ONE, Three::TWO);
};

#endif // INCLUDED_PATTERN_IMPOSSIBLE
