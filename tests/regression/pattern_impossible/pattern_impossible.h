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
  enum class three { One, Two, Three0 };

  template <typename T1>
  static T1 three_rect(const T1 f, const T1 f0, const T1 f1, const three t) {
    return [&](void) {
      switch (t) {
      case three::One: {
        return f;
      }
      case three::Two: {
        return f0;
      }
      case three::Three0: {
        return f1;
      }
      }
    }();
  }

  template <typename T1>
  static T1 three_rec(const T1 f, const T1 f0, const T1 f1, const three t) {
    return [&](void) {
      switch (t) {
      case three::One: {
        return f;
      }
      case three::Two: {
        return f0;
      }
      case three::Three0: {
        return f1;
      }
      }
    }();
  }

  struct nested {
    // TYPES
    struct Leaf {
      unsigned int _a0;
    };

    struct Node {
      std::shared_ptr<nested> _a0;
      std::shared_ptr<nested> _a1;
    };

    using variant_t = std::variant<Leaf, Node>;

  private:
    // DATA
    variant_t v_;

    // CREATORS
    explicit nested(Leaf _v) : v_(std::move(_v)) {}

    explicit nested(Node _v) : v_(std::move(_v)) {}

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
    variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <
      typename T1, MapsTo<T1, unsigned int> F0,
      MapsTo<T1, std::shared_ptr<nested>, T1, std::shared_ptr<nested>, T1> F1>
  static T1 nested_rect(F0 &&f, F1 &&f0, const std::shared_ptr<nested> &n) {
    return std::visit(Overloaded{[&](const typename nested::Leaf _args) -> T1 {
                                   unsigned int n0 = _args._a0;
                                   return f(std::move(n0));
                                 },
                                 [&](const typename nested::Node _args) -> T1 {
                                   std::shared_ptr<nested> n0 = _args._a0;
                                   std::shared_ptr<nested> n1 = _args._a1;
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
                                   unsigned int n0 = _args._a0;
                                   return f(std::move(n0));
                                 },
                                 [&](const typename nested::Node _args) -> T1 {
                                   std::shared_ptr<nested> n0 = _args._a0;
                                   std::shared_ptr<nested> n1 = _args._a1;
                                   return f0(n0, nested_rec<T1>(f, f0, n0), n1,
                                             nested_rec<T1>(f, f0, n1));
                                 }},
                      n->v());
  }

  static unsigned int complex_match(const three x);
  static unsigned int nested_match(const std::shared_ptr<nested> &n);
  static unsigned int double_match(const three x, const three y);
  static unsigned int multi_arg_pattern(const std::shared_ptr<nested> &n);
  static inline const unsigned int test1 = complex_match(three::One);
  static inline const unsigned int test2 = nested_match(
      nested::ctor::Node_(nested::ctor::Leaf_(5u), nested::ctor::Leaf_(10u)));
  static inline const unsigned int test3 = double_match(three::One, three::Two);
};
