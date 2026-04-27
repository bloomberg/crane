#ifndef INCLUDED_PATTERN_IMPOSSIBLE
#define INCLUDED_PATTERN_IMPOSSIBLE

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

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
        return nested(Leaf{[](auto &&__v) -> unsigned int {
          if constexpr (
              requires { __v ? 0 : 0; } && requires { *__v; } &&
              requires { __v->clone(); } && requires { __v.get(); }) {
            using _E = std::remove_cvref_t<decltype(*__v)>;
            return __v ? std::make_unique<_E>(__v->clone()) : nullptr;
          } else if constexpr (requires { __v.clone(); }) {
            return __v.clone();
          } else {
            return __v;
          }
        }(d_a0)});
      } else {
        const auto &[d_a0, d_a1] = std::get<Node>(_sv.v());
        return nested(Node{
            d_a0 ? std::make_unique<PatternImpossible::nested>(d_a0->clone())
                 : nullptr,
            d_a1 ? std::make_unique<PatternImpossible::nested>(d_a1->clone())
                 : nullptr});
      }
    }

    // CREATORS
    __attribute__((pure)) static nested leaf(unsigned int a0) {
      return nested(Leaf{std::move(a0)});
    }

    __attribute__((pure)) static nested node(const nested &a0,
                                             const nested &a1) {
      return nested(
          Node{std::make_unique<nested>(a0), std::make_unique<nested>(a1)});
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
