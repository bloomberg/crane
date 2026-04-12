#ifndef INCLUDED_PATTERN_IMPOSSIBLE
#define INCLUDED_PATTERN_IMPOSSIBLE

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
      std::shared_ptr<nested> d_a0;
      std::shared_ptr<nested> d_a1;
    };

    using variant_t = std::variant<Leaf, Node>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    explicit nested(Leaf _v) : d_v_(std::move(_v)) {}

    explicit nested(Node _v) : d_v_(std::move(_v)) {}

    static std::shared_ptr<nested> leaf(unsigned int a0) {
      return std::make_shared<nested>(Leaf{std::move(a0)});
    }

    static std::shared_ptr<nested> node(const std::shared_ptr<nested> &a0,
                                        const std::shared_ptr<nested> &a1) {
      return std::make_shared<nested>(Node{a0, a1});
    }

    static std::shared_ptr<nested> node(std::shared_ptr<nested> &&a0,
                                        std::shared_ptr<nested> &&a1) {
      return std::make_shared<nested>(Node{std::move(a0), std::move(a1)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <
      typename T1, MapsTo<T1, unsigned int> F0,
      MapsTo<T1, std::shared_ptr<nested>, T1, std::shared_ptr<nested>, T1> F1>
  static T1 nested_rect(F0 &&f, F1 &&f0, const std::shared_ptr<nested> &n) {
    return std::visit(
        Overloaded{[&](const typename nested::Leaf &_args) -> T1 {
                     return f(_args.d_a0);
                   },
                   [&](const typename nested::Node &_args) -> T1 {
                     return f0(_args.d_a0, nested_rect<T1>(f, f0, _args.d_a0),
                               _args.d_a1, nested_rect<T1>(f, f0, _args.d_a1));
                   }},
        n->v());
  }

  template <
      typename T1, MapsTo<T1, unsigned int> F0,
      MapsTo<T1, std::shared_ptr<nested>, T1, std::shared_ptr<nested>, T1> F1>
  static T1 nested_rec(F0 &&f, F1 &&f0, const std::shared_ptr<nested> &n) {
    return std::visit(
        Overloaded{[&](const typename nested::Leaf &_args) -> T1 {
                     return f(_args.d_a0);
                   },
                   [&](const typename nested::Node &_args) -> T1 {
                     return f0(_args.d_a0, nested_rec<T1>(f, f0, _args.d_a0),
                               _args.d_a1, nested_rec<T1>(f, f0, _args.d_a1));
                   }},
        n->v());
  }

  __attribute__((pure)) static unsigned int complex_match(const Three x);
  __attribute__((pure)) static unsigned int
  nested_match(const std::shared_ptr<nested> &n);
  __attribute__((pure)) static unsigned int double_match(const Three x,
                                                         const Three y);
  __attribute__((pure)) static unsigned int
  multi_arg_pattern(const std::shared_ptr<nested> &n);
  static inline const unsigned int test1 = complex_match(Three::e_ONE);
  static inline const unsigned int test2 =
      nested_match(nested::node(nested::leaf(5u), nested::leaf(10u)));
  static inline const unsigned int test3 =
      double_match(Three::e_ONE, Three::e_TWO);
};

#endif // INCLUDED_PATTERN_IMPOSSIBLE
