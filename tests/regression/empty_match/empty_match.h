#ifndef INCLUDED_EMPTY_MATCH
#define INCLUDED_EMPTY_MATCH

#include <memory>
#include <optional>
#include <stdexcept>
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

struct EmptyMatch {
  struct empty {
    empty() = delete;
  };

  template <typename T1> static T1 empty_rect(const empty &) {
    throw std::logic_error("absurd case");
  }

  template <typename T1> static T1 empty_rec(const empty &) {
    throw std::logic_error("absurd case");
  }

  template <typename T1> static T1 absurd(const empty &) {
    throw std::logic_error("absurd case");
  }

  __attribute__((pure)) static unsigned int from_empty(const empty &_x0);

  template <typename t_A, typename t_B> struct either {
    // TYPES
    struct Left {
      t_A d_a0;
    };

    struct Right {
      t_B d_a0;
    };

    using variant_t = std::variant<Left, Right>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    either() {}

    explicit either(Left _v) : d_v_(std::move(_v)) {}

    explicit either(Right _v) : d_v_(std::move(_v)) {}

    either(const either<t_A, t_B> &_other)
        : d_v_(std::move(_other.clone().d_v_)) {}

    either(either<t_A, t_B> &&_other) : d_v_(std::move(_other.d_v_)) {}

    __attribute__((pure)) either<t_A, t_B> &
    operator=(const either<t_A, t_B> &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    __attribute__((pure)) either<t_A, t_B> &
    operator=(either<t_A, t_B> &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) either<t_A, t_B> clone() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<Left>(_sv.v())) {
        const auto &[d_a0] = std::get<Left>(_sv.v());
        return either<t_A, t_B>(Left{clone_as_value<t_A>(d_a0)});
      } else {
        const auto &[d_a0] = std::get<Right>(_sv.v());
        return either<t_A, t_B>(Right{clone_as_value<t_B>(d_a0)});
      }
    }

    template <typename _CloneT0, typename _CloneT1>
    __attribute__((pure)) either<_CloneT0, _CloneT1> clone_as() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<Left>(_sv.v())) {
        const auto &[d_a0] = std::get<Left>(_sv.v());
        return either<_CloneT0, _CloneT1>(
            typename either<_CloneT0, _CloneT1>::Left{
                clone_as_value<_CloneT0>(d_a0)});
      } else {
        const auto &[d_a0] = std::get<Right>(_sv.v());
        return either<_CloneT0, _CloneT1>(
            typename either<_CloneT0, _CloneT1>::Right{
                clone_as_value<_CloneT1>(d_a0)});
      }
    }

    // CREATORS
    __attribute__((pure)) static either<t_A, t_B> left(t_A a0) {
      return either(Left{std::move(a0)});
    }

    __attribute__((pure)) static either<t_A, t_B> right(t_B a0) {
      return either(Right{std::move(a0)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) either<t_A, t_B> *operator->() { return this; }

    __attribute__((pure)) const either<t_A, t_B> *operator->() const {
      return this;
    }

    __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

    __attribute__((pure)) bool operator==(std::nullptr_t) const {
      return false;
    }

    // MANIPULATORS
    void reset() { *this = either<t_A, t_B>(); }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, typename T2, typename T3, MapsTo<T3, T1> F0,
            MapsTo<T3, T2> F1>
  static T3 either_rect(F0 &&f, F1 &&f0, const either<T1, T2> &e) {
    if (std::holds_alternative<typename either<T1, T2>::Left>(e.v())) {
      const auto &[d_a0] = std::get<typename either<T1, T2>::Left>(e.v());
      return f(d_a0);
    } else {
      const auto &[d_a0] = std::get<typename either<T1, T2>::Right>(e.v());
      return f0(d_a0);
    }
  }

  template <typename T1, typename T2, typename T3, MapsTo<T3, T1> F0,
            MapsTo<T3, T2> F1>
  static T3 either_rec(F0 &&f, F1 &&f0, const either<T1, T2> &e) {
    if (std::holds_alternative<typename either<T1, T2>::Left>(e.v())) {
      const auto &[d_a0] = std::get<typename either<T1, T2>::Left>(e.v());
      return f(d_a0);
    } else {
      const auto &[d_a0] = std::get<typename either<T1, T2>::Right>(e.v());
      return f0(d_a0);
    }
  }

  template <typename T1> static T1 handle_left(const either<T1, empty> &e) {
    if (std::holds_alternative<typename either<T1, empty>::Left>(e.v())) {
      const auto &[d_a0] = std::get<typename either<T1, empty>::Left>(e.v());
      return d_a0;
    } else {
      const auto &[d_a0] = std::get<typename either<T1, empty>::Right>(e.v());
      return absurd<T1>(d_a0);
    }
  }

  static inline const either<unsigned int, empty> test_either =
      either<unsigned int, empty>::left(5u);
  static inline const unsigned int test_handle =
      handle_left<unsigned int>(test_either);

  template <typename T1, typename T2>
  static either<T1, T2> complex_absurd(const empty &) {
    throw std::logic_error("absurd case");
  }
};

#endif // INCLUDED_EMPTY_MATCH
