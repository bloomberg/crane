#ifndef INCLUDED_PATTERN_IMPOSSIBLE
#define INCLUDED_PATTERN_IMPOSSIBLE

#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
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
    return [&](void) {
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
      }
    }();
  }

  template <typename T1>
  static T1 three_rec(const T1 f, const T1 f0, const T1 f1, const Three t) {
    return [&](void) {
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
      }
    }();
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

    // CREATORS
    explicit nested(Leaf _v) : d_v_(std::move(_v)) {}

    explicit nested(Node _v) : d_v_(std::move(_v)) {}

  public:
    // TYPES
    struct ctor {
      ctor() = delete;

      static std::shared_ptr<nested> Leaf_(unsigned int a0) {
        return std::shared_ptr<nested>(new nested(Leaf{a0}));
      }

      static std::shared_ptr<nested> Node_(const std::shared_ptr<nested> &a0,
                                           const std::shared_ptr<nested> &a1) {
        return std::shared_ptr<nested>(new nested(Node{a0, a1}));
      }

      static std::unique_ptr<nested> Leaf_uptr(unsigned int a0) {
        return std::unique_ptr<nested>(new nested(Leaf{a0}));
      }

      static std::unique_ptr<nested>
      Node_uptr(const std::shared_ptr<nested> &a0,
                const std::shared_ptr<nested> &a1) {
        return std::unique_ptr<nested>(new nested(Node{a0, a1}));
      }
    };

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <
      typename T1, MapsTo<T1, unsigned int> F0,
      MapsTo<T1, std::shared_ptr<nested>, T1, std::shared_ptr<nested>, T1> F1>
  static T1 nested_rect(F0 &&f, F1 &&f0, const std::shared_ptr<nested> &n) {
    return std::visit(Overloaded{[&](const typename nested::Leaf _args) -> T1 {
                                   unsigned int n0 = _args.d_a0;
                                   return f(std::move(n0));
                                 },
                                 [&](const typename nested::Node _args) -> T1 {
                                   std::shared_ptr<nested> n0 = _args.d_a0;
                                   std::shared_ptr<nested> n1 = _args.d_a1;
                                   return f0(n0, nested_rect<T1>(f, f0, n0), n1,
                                             nested_rect<T1>(f, f0, n1));
                                 }},
                      n->v());
  }

  template <
      typename T1, MapsTo<T1, unsigned int> F0,
      MapsTo<T1, std::shared_ptr<nested>, T1, std::shared_ptr<nested>, T1> F1>
  static T1 nested_rec(F0 &&f, F1 &&f0, const std::shared_ptr<nested> &n) {
    return std::visit(Overloaded{[&](const typename nested::Leaf _args) -> T1 {
                                   unsigned int n0 = _args.d_a0;
                                   return f(std::move(n0));
                                 },
                                 [&](const typename nested::Node _args) -> T1 {
                                   std::shared_ptr<nested> n0 = _args.d_a0;
                                   std::shared_ptr<nested> n1 = _args.d_a1;
                                   return f0(n0, nested_rec<T1>(f, f0, n0), n1,
                                             nested_rec<T1>(f, f0, n1));
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
  static inline const unsigned int test2 = nested_match(
      nested::ctor::Node_(nested::ctor::Leaf_(5u), nested::ctor::Leaf_(10u)));
  static inline const unsigned int test3 =
      double_match(Three::e_ONE, Three::e_TWO);
};

#endif // INCLUDED_PATTERN_IMPOSSIBLE
