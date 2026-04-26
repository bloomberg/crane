#ifndef INCLUDED_PATTERN_IMPOSSIBLE
#define INCLUDED_PATTERN_IMPOSSIBLE

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

template <typename T> struct is_unique_ptr : std::false_type {};

template <typename T>
struct is_unique_ptr<std::unique_ptr<T>> : std::true_type {
  using element_type = T;
};

template <typename T> struct is_shared_ptr : std::false_type {};

template <typename T>
struct is_shared_ptr<std::shared_ptr<T>> : std::true_type {
  using element_type = T;
};

template <typename T> struct is_optional : std::false_type {};

template <typename T> struct is_optional<std::optional<T>> : std::true_type {
  using element_type = T;
};

template <typename T> auto clone_value(const T &x) { return x; }

template <typename T>
std::unique_ptr<T> clone_value(const std::unique_ptr<T> &x) {
  return x ? std::make_unique<T>(x->clone()) : nullptr;
}

template <typename T>
std::shared_ptr<T> clone_value(const std::shared_ptr<T> &x) {
  if constexpr (requires { x->clone(); }) {
    return x ? std::make_shared<T>(x->clone()) : nullptr;
  } else {
    return x;
  }
}

template <typename Target, typename Source>
Target clone_as_value(const Source &x) {
  using TargetBare = std::remove_cvref_t<Target>;
  using SourceBare = std::remove_cvref_t<Source>;
  if constexpr (is_unique_ptr<TargetBare>::value) {
    using Inner = typename is_unique_ptr<TargetBare>::element_type;
    if constexpr (is_unique_ptr<SourceBare>::value) {
      using SourceInner = typename is_unique_ptr<SourceBare>::element_type;
      if (!x)
        return nullptr;
      if constexpr (std::is_same_v<Inner, SourceInner>) {
        return clone_value(x);
      } else if constexpr (requires {
                             typename Inner::crane_element_type;
                             x->template clone_as<
                                 typename Inner::crane_element_type>();
                           }) {
        return std::make_unique<Inner>(
            x->template clone_as<typename Inner::crane_element_type>());
      } else if constexpr (requires { x->template clone_as<Inner>(); }) {
        return std::make_unique<Inner>(x->template clone_as<Inner>());
      } else {
        return std::make_unique<Inner>(x->clone());
      }
    } else {
      if constexpr (requires { x.clone(); }) {
        return std::make_unique<Inner>(x.clone());
      } else if constexpr (std::is_same_v<Inner, SourceBare>) {
        if constexpr (requires { x.clone(); }) {
          return std::make_unique<Inner>(x.clone());
        } else {
          return std::make_unique<Inner>(x);
        }
      } else if constexpr (requires { x.template clone_as<Inner>(); }) {
        return std::make_unique<Inner>(x.template clone_as<Inner>());
      } else {
        if constexpr (requires { x.clone(); }) {
          return std::make_unique<Inner>(x.clone());
        } else {
          return std::make_unique<Inner>(x);
        }
      }
    }
  } else if constexpr (is_optional<TargetBare>::value) {
    using Inner = typename is_optional<TargetBare>::element_type;
    if constexpr (is_optional<SourceBare>::value) {
      if (!x)
        return std::nullopt;
      return Target{clone_as_value<Inner>(*x)};
    } else {
      return Target{clone_as_value<Inner>(x)};
    }
  } else if constexpr (is_shared_ptr<TargetBare>::value) {
    using Inner = typename is_shared_ptr<TargetBare>::element_type;
    if constexpr (is_shared_ptr<SourceBare>::value) {
      using SourceInner = typename is_shared_ptr<SourceBare>::element_type;
      if (!x)
        return nullptr;
      if constexpr (std::is_same_v<Inner, SourceInner>) {
        return clone_value(x);
      } else if constexpr (requires { x->template clone_as<Inner>(); }) {
        return std::make_shared<Inner>(x->template clone_as<Inner>());
      } else {
        return std::make_shared<Inner>(x->clone());
      }
    } else if constexpr (is_unique_ptr<SourceBare>::value) {
      if (!x)
        return nullptr;
      if constexpr (requires { x->template clone_as<Inner>(); }) {
        return std::make_shared<Inner>(x->template clone_as<Inner>());
      } else {
        return std::make_shared<Inner>(x->clone());
      }
    } else {
      if constexpr (std::is_same_v<Inner, SourceBare>) {
        return std::make_shared<Inner>(x.clone());
      } else if constexpr (requires { x.template clone_as<Inner>(); }) {
        return std::make_shared<Inner>(x.template clone_as<Inner>());
      } else {
        return std::make_shared<Inner>(x.clone());
      }
    }
  } else if constexpr (std::is_same_v<TargetBare, SourceBare>) {
    return clone_value(x);
  } else if constexpr (is_unique_ptr<SourceBare>::value) {
    using SourceInner = typename is_unique_ptr<SourceBare>::element_type;
    if constexpr (std::is_same_v<TargetBare, SourceInner>) {
      if (!x)
        return Target{};
      if constexpr (requires { x->clone(); }) {
        return x->clone();
      } else {
        return *x;
      }
    } else if constexpr (requires { x->template clone_as<TargetBare>(); }) {
      return x->template clone_as<TargetBare>();
    } else if constexpr (requires { x->clone(); }) {
      return x->clone();
    } else {
      return Target(*x);
    }
  } else if constexpr (is_shared_ptr<SourceBare>::value) {
    using SourceInner = typename is_shared_ptr<SourceBare>::element_type;
    if constexpr (std::is_same_v<TargetBare, SourceInner>) {
      return x ? x->clone() : Target{};
    } else if constexpr (requires { x->template clone_as<TargetBare>(); }) {
      return x->template clone_as<TargetBare>();
    } else {
      return Target(*x);
    }
  } else if constexpr (requires {
                         typename TargetBare::crane_element_type;
                         x.template clone_as<
                             typename TargetBare::crane_element_type>();
                       }) {
    return x.template clone_as<typename TargetBare::crane_element_type>();
  } else if constexpr (requires { x.template clone_as<TargetBare>(); }) {
    return x.template clone_as<TargetBare>();
  } else {
    return Target(x);
  }
}

struct PatternImpossible {
  enum class Three { e_ONE, e_TWO, e_THREE0 };

  template <typename T1>
  static T1 three_rect(const T1 f, const T1 f0, const T1 f1, const Three t) {
    switch (t) {
    case Three::e_ONE: {
      return f;
    }
    case Three::e_TWO: {
      return f0;
    }
    case Three::e_THREE0: {
      return f1;
    }
    default:
      std::unreachable();
    }
  }

  template <typename T1>
  static T1 three_rec(const T1 f, const T1 f0, const T1 f1, const Three t) {
    switch (t) {
    case Three::e_ONE: {
      return f;
    }
    case Three::e_TWO: {
      return f0;
    }
    case Three::e_THREE0: {
      return f1;
    }
    default:
      std::unreachable();
    }
  }

  struct nested {
    // TYPES
    struct Leaf {
      unsigned int d_a0;
    };

    struct Node {
      std::unique_ptr<nested> d_a0;
      std::unique_ptr<nested> d_a1;
    };

    using variant_t = std::variant<Leaf, Node>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    nested() {}

    explicit nested(Leaf _v) : d_v_(std::move(_v)) {}

    explicit nested(Node _v) : d_v_(std::move(_v)) {}

    nested(const nested &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    nested(nested &&_other) : d_v_(std::move(_other.d_v_)) {}

    __attribute__((pure)) nested &operator=(const nested &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    __attribute__((pure)) nested &operator=(nested &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) nested clone() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<Leaf>(_sv.v())) {
        const auto &[d_a0] = std::get<Leaf>(_sv.v());
        return nested(Leaf{d_a0});
      } else {
        const auto &[d_a0, d_a1] = std::get<Node>(_sv.v());
        return nested(Node{clone_as_value<std::unique_ptr<nested>>(d_a0),
                           clone_as_value<std::unique_ptr<nested>>(d_a1)});
      }
    }

    // CREATORS
    __attribute__((pure)) static nested leaf(unsigned int a0) {
      return nested(Leaf{std::move(a0)});
    }

    __attribute__((pure)) static nested node(const nested &a0,
                                             const nested &a1) {
      return nested(Node{std::make_unique<nested>(a0.clone()),
                         std::make_unique<nested>(a1.clone())});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) nested *operator->() { return this; }

    __attribute__((pure)) const nested *operator->() const { return this; }

    __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

    __attribute__((pure)) bool operator==(std::nullptr_t) const {
      return false;
    }

    // MANIPULATORS
    void reset() { *this = nested(); }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, MapsTo<T1, unsigned int> F0,
            MapsTo<T1, nested, T1, nested, T1> F1>
  static T1 nested_rect(F0 &&f, F1 &&f0, const nested &n) {
    if (std::holds_alternative<typename nested::Leaf>(n.v())) {
      const auto &[d_a0] = std::get<typename nested::Leaf>(n.v());
      return f(d_a0);
    } else {
      const auto &[d_a0, d_a1] = std::get<typename nested::Node>(n.v());
      return f0(*(d_a0), nested_rect<T1>(f, f0, *(d_a0)), *(d_a1),
                nested_rect<T1>(f, f0, *(d_a1)));
    }
  }

  template <typename T1, MapsTo<T1, unsigned int> F0,
            MapsTo<T1, nested, T1, nested, T1> F1>
  static T1 nested_rec(F0 &&f, F1 &&f0, const nested &n) {
    if (std::holds_alternative<typename nested::Leaf>(n.v())) {
      const auto &[d_a0] = std::get<typename nested::Leaf>(n.v());
      return f(d_a0);
    } else {
      const auto &[d_a0, d_a1] = std::get<typename nested::Node>(n.v());
      return f0(*(d_a0), nested_rec<T1>(f, f0, *(d_a0)), *(d_a1),
                nested_rec<T1>(f, f0, *(d_a1)));
    }
  }

  __attribute__((pure)) static unsigned int complex_match(const Three x);
  __attribute__((pure)) static unsigned int nested_match(const nested &n);
  __attribute__((pure)) static unsigned int double_match(const Three x,
                                                         const Three y);
  __attribute__((pure)) static unsigned int multi_arg_pattern(const nested &n);
  static inline const unsigned int test1 = complex_match(Three::e_ONE);
  static inline const unsigned int test2 =
      nested_match(nested::node(nested::leaf(5u), nested::leaf(10u)));
  static inline const unsigned int test3 =
      double_match(Three::e_ONE, Three::e_TWO);
};

#endif // INCLUDED_PATTERN_IMPOSSIBLE
