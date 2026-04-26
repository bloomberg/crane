#ifndef INCLUDED_EXISTENTIAL_CLOSURE_PROBE
#define INCLUDED_EXISTENTIAL_CLOSURE_PROBE

#include <any>
#include <functional>
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

struct ExistentialClosureProbe {
  /// Type-indexed inductive wrapping a value of erased type.
  /// The type index A is erased to std::any by Crane.
  /// Values stored in the wrapper must be recovered via any_cast.
  struct wrap {
    // TYPES
    struct Wrap0 {
      std::any d_a;
    };

    using variant_t = std::variant<Wrap0>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    wrap() {}

    explicit wrap(Wrap0 _v) : d_v_(std::move(_v)) {}

    wrap(const wrap &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    wrap(wrap &&_other) : d_v_(std::move(_other.d_v_)) {}

    __attribute__((pure)) wrap &operator=(const wrap &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    __attribute__((pure)) wrap &operator=(wrap &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) wrap clone() const {
      auto &&_sv = *(this);
      const auto &[d_a] = std::get<Wrap0>(_sv.v());
      return wrap(Wrap0{d_a});
    }

    // CREATORS
    __attribute__((pure)) static wrap wrap0(std::any a) {
      return wrap(Wrap0{std::move(a)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) wrap *operator->() { return this; }

    __attribute__((pure)) const wrap *operator->() const { return this; }

    __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

    __attribute__((pure)) bool operator==(std::nullptr_t) const {
      return false;
    }

    // MANIPULATORS
    void reset() { *this = wrap(); }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, typename F0>
  static T1 wrap_rect(F0 &&f, const wrap &w) {
    const auto &[d_a] = std::get<typename wrap::Wrap0>(w.v());
    return std::any_cast<T1>(f(d_a));
  }

  template <typename T1, typename F0>
  static T1 wrap_rec(F0 &&f, const wrap &w) {
    const auto &[d_a] = std::get<typename wrap::Wrap0>(w.v());
    return std::any_cast<T1>(f(d_a));
  }

  template <typename T1> static T1 unwrap(const wrap &w) {
    const auto &[d_a] = std::get<typename wrap::Wrap0>(w.v());
    return std::any_cast<T1>(d_a);
  }

  /// Pack a closure into a type-erased wrapper.
  __attribute__((pure)) static wrap pack_fn(unsigned int base);
  /// Unpack and apply.
  __attribute__((pure)) static unsigned int
  apply_packed(const wrap &_x0, const unsigned int &_x1);
  /// test1: pack base=10, apply to 5. Expected: 15.
  static inline const unsigned int test1 = apply_packed(pack_fn(10u), 5u);
  /// test2: Pack and unpack through a let binding.
  /// base=42, apply to 0. Expected: 42.
  static inline const unsigned int test2 = []() {
    wrap p = pack_fn(42u);
    return apply_packed(p, 0u);
  }();
  /// Store a closure that captures another closure.
  __attribute__((pure)) static wrap pack_composed(unsigned int a,
                                                  unsigned int b);
  /// test3: a=3, b=2, g(5) = (5+3)*2 = 16.
  static inline const unsigned int test3 =
      apply_packed(pack_composed(3u, 2u), 5u);
};

#endif // INCLUDED_EXISTENTIAL_CLOSURE_PROBE
