#ifndef INCLUDED_FREE_MONAD
#define INCLUDED_FREE_MONAD

#include <any>
#include <functional>
#include <memory>
#include <optional>
#include <string>
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

enum class Unit { e_TT };

struct FreeMonad {
  struct IO {
    // TYPES
    struct Pure {
      std::any d_a;
    };

    struct Bind {
      std::unique_ptr<IO> d_a;
      std::function<std::unique_ptr<IO>(std::any)> d_b;
    };

    struct Get_line {};

    struct Print {
      std::string d_a0;
    };

    using variant_t = std::variant<Pure, Bind, Get_line, Print>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    IO() {}

    explicit IO(Pure _v) : d_v_(std::move(_v)) {}

    explicit IO(Bind _v) : d_v_(std::move(_v)) {}

    explicit IO(Get_line _v) : d_v_(_v) {}

    explicit IO(Print _v) : d_v_(std::move(_v)) {}

    IO(const IO &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    IO(IO &&_other) : d_v_(std::move(_other.d_v_)) {}

    __attribute__((pure)) IO &operator=(const IO &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    __attribute__((pure)) IO &operator=(IO &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) IO clone() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<Pure>(_sv.v())) {
        const auto &[d_a] = std::get<Pure>(_sv.v());
        return IO(Pure{d_a});
      } else if (std::holds_alternative<Bind>(_sv.v())) {
        const auto &[d_a, d_b] = std::get<Bind>(_sv.v());
        return IO(Bind{clone_as_value<std::unique_ptr<IO>>(d_a), d_b});
      } else if (std::holds_alternative<Get_line>(_sv.v())) {
        return IO(Get_line{});
      } else {
        const auto &[d_a0] = std::get<Print>(_sv.v());
        return IO(Print{d_a0});
      }
    }

    // CREATORS
    __attribute__((pure)) static IO pure(std::any a) {
      return IO(Pure{std::move(a)});
    }

    __attribute__((pure)) static IO bind(const IO &a,
                                         std::function<IO(std::any)> b) {
      return IO(Bind{std::make_unique<IO>(a.clone()), [=](std::any x0) mutable {
                       return clone_as_value<std::unique_ptr<IO>>(b(x0));
                     }});
    }

    __attribute__((pure)) static IO get_line() { return IO(Get_line{}); }

    __attribute__((pure)) static IO print(std::string a0) {
      return IO(Print{std::move(a0)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) IO *operator->() { return this; }

    __attribute__((pure)) const IO *operator->() const { return this; }

    __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

    __attribute__((pure)) bool operator==(std::nullptr_t) const {
      return false;
    }

    // MANIPULATORS
    void reset() { *this = IO(); }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, typename F0, typename F1, MapsTo<T1, std::string> F3>
  static T1 IO_rect(F0 &&f, F1 &&f0, const T1 f1, F3 &&f2, const IO &i) {
    if (std::holds_alternative<typename IO::Pure>(i.v())) {
      const auto &[d_a] = std::get<typename IO::Pure>(i.v());
      return std::any_cast<T1>(f(d_a));
    } else if (std::holds_alternative<typename IO::Bind>(i.v())) {
      const auto &[d_a, d_b] = std::get<typename IO::Bind>(i.v());
      return std::any_cast<T1>(
          f0(clone_as_value<FreeMonad::IO>(d_a),
             IO_rect<T1>(f, f0, f1, f2, clone_as_value<FreeMonad::IO>(d_a)),
             clone_value(d_b), [=](const std::any a) mutable {
               return IO_rect<T1>(f, f0, f1, f2, clone_value(d_b)(a));
             }));
    } else if (std::holds_alternative<typename IO::Get_line>(i.v())) {
      return f1;
    } else {
      const auto &[d_a0] = std::get<typename IO::Print>(i.v());
      return f2(d_a0);
    }
  }

  template <typename T1, typename F0, typename F1, MapsTo<T1, std::string> F3>
  static T1 IO_rec(F0 &&f, F1 &&f0, const T1 f1, F3 &&f2, const IO &i) {
    if (std::holds_alternative<typename IO::Pure>(i.v())) {
      const auto &[d_a] = std::get<typename IO::Pure>(i.v());
      return std::any_cast<T1>(f(d_a));
    } else if (std::holds_alternative<typename IO::Bind>(i.v())) {
      const auto &[d_a, d_b] = std::get<typename IO::Bind>(i.v());
      return std::any_cast<T1>(
          f0(clone_as_value<FreeMonad::IO>(d_a),
             IO_rec<T1>(f, f0, f1, f2, clone_as_value<FreeMonad::IO>(d_a)),
             clone_value(d_b), [=](const std::any a) mutable {
               return IO_rec<T1>(f, f0, f1, f2, clone_value(d_b)(a));
             }));
    } else if (std::holds_alternative<typename IO::Get_line>(i.v())) {
      return f1;
    } else {
      const auto &[d_a0] = std::get<typename IO::Print>(i.v());
      return f2(d_a0);
    }
  }

  static inline const IO test = IO::pure(Unit::e_TT);
};

#endif // INCLUDED_FREE_MONAD
