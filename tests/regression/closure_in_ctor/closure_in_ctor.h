#ifndef INCLUDED_CLOSURE_IN_CTOR
#define INCLUDED_CLOSURE_IN_CTOR

#include <functional>
#include <memory>
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

template <typename T> auto clone_value(const T &x) { return x; }

template <typename T>
std::unique_ptr<T> clone_value(const std::unique_ptr<T> &x) {
  return x ? std::make_unique<T>(x->clone()) : nullptr;
}

template <typename T>
std::shared_ptr<T> clone_value(const std::shared_ptr<T> &x) {
  return x ? std::make_shared<T>(x->clone()) : nullptr;
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
      if constexpr (std::is_same_v<Inner, SourceBare>) {
        return std::make_unique<Inner>(x.clone());
      } else if constexpr (requires { x.template clone_as<Inner>(); }) {
        return std::make_unique<Inner>(x.template clone_as<Inner>());
      } else {
        return std::make_unique<Inner>(x.clone());
      }
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
      return x ? x->clone() : Target{};
    } else if constexpr (requires { x->template clone_as<TargetBare>(); }) {
      return x->template clone_as<TargetBare>();
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

struct ClosureInCtor {
  struct box {
    // TYPES
    struct Box0 {
      std::function<unsigned int(unsigned int)> d_a0;
    };

    struct Empty {};

    using variant_t = std::variant<Box0, Empty>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    box() {}

    explicit box(Box0 _v) : d_v_(std::move(_v)) {}

    explicit box(Empty _v) : d_v_(_v) {}

    box(const box &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    box(box &&_other) : d_v_(std::move(_other.d_v_)) {}

    __attribute__((pure)) box &operator=(const box &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    __attribute__((pure)) box &operator=(box &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) box clone() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<Box0>(_sv.v())) {
        const auto &[d_a0] = std::get<Box0>(_sv.v());
        return box(Box0{clone_value(d_a0)});
      } else {
        return box(Empty{});
      }
    }

    // CREATORS
    __attribute__((pure)) static box
    box0(std::function<unsigned int(unsigned int)> a0) {
      return box(Box0{std::move(a0)});
    }

    constexpr static box empty() { return box(Empty{}); }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) box *operator->() { return this; }

    __attribute__((pure)) const box *operator->() const { return this; }

    __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

    __attribute__((pure)) bool operator==(std::nullptr_t) const {
      return false;
    }

    // MANIPULATORS
    void reset() { *this = box(); }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1,
            MapsTo<T1, std::function<unsigned int(unsigned int)>> F0>
  static T1 box_rect(F0 &&f, const T1 f0, const box &b) {
    if (std::holds_alternative<typename box::Box0>(b.v())) {
      const auto &[d_a0] = std::get<typename box::Box0>(b.v());
      return f(d_a0);
    } else {
      return f0;
    }
  }

  template <typename T1,
            MapsTo<T1, std::function<unsigned int(unsigned int)>> F0>
  static T1 box_rec(F0 &&f, const T1 f0, const box &b) {
    if (std::holds_alternative<typename box::Box0>(b.v())) {
      const auto &[d_a0] = std::get<typename box::Box0>(b.v());
      return f(d_a0);
    } else {
      return f0;
    }
  }

  /// A local fixpoint captures the function parameter n and is stored
  /// in Box — a user-defined inductive (not option, not pair).
  ///
  /// BUG: Local fixpoints generate std::function with & capture
  /// (needed for self-reference). This & also captures n by reference.
  /// The fixpoint escapes through Box, so return_captures_by_value
  /// does NOT apply. After make_box_fix returns, n is destroyed,
  /// and the captured reference dangles.
  ///
  /// Difference from fix_escape_capture: escapes through a CUSTOM
  /// INDUCTIVE constructor, not a pair.
  __attribute__((pure)) static box make_box_fix(unsigned int n);
  /// test1: make_box_fix(5) returns Box(add) where add(x) = x + 5.
  /// Expected: add(3) = 5 + 3 = 8.
  /// Bug: & captures dangling reference to n.
  static inline const unsigned int test1 = []() {
    auto &&_sv = make_box_fix(5u);
    if (std::holds_alternative<typename box::Box0>(_sv.v())) {
      const auto &[d_a0] = std::get<typename box::Box0>(_sv.v());
      return d_a0(3u);
    } else {
      return 999u;
    }
  }();
  /// test2: Interleave noise between closure creation and use.
  /// Expected: add(10) = 42 + 10 = 52.
  static inline const unsigned int test2 = []() {
    box b = make_box_fix(42u);
    if (std::holds_alternative<typename box::Box0>(b.v())) {
      const auto &[d_a0] = std::get<typename box::Box0>(b.v());
      return d_a0(10u);
    } else {
      return 999u;
    }
  }();
  /// test3: Two boxes — capture different parameters.
  /// Expected: add_10(0) + add_20(0) = 10 + 20 = 30.
  static inline const unsigned int test3 = []() {
    box b1 = make_box_fix(10u);
    box b2 = make_box_fix(20u);
    if (std::holds_alternative<typename box::Box0>(b1.v())) {
      const auto &[d_a0] = std::get<typename box::Box0>(b1.v());
      if (std::holds_alternative<typename box::Box0>(b2.v())) {
        const auto &[d_a00] = std::get<typename box::Box0>(b2.v());
        return (d_a0(0u) + d_a00(0u));
      } else {
        return 999u;
      }
    } else {
      return 999u;
    }
  }();
};

#endif // INCLUDED_CLOSURE_IN_CTOR
