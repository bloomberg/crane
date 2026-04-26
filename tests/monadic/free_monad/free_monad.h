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

template <typename T> auto clone_value(const T &x) { return x; }

template <typename T>
std::unique_ptr<T> clone_value(const std::unique_ptr<T> &x) {
  if constexpr (requires { x->clone(); }) {
    return x ? std::make_unique<T>(x->clone()) : nullptr;
  } else {
    return x ? std::make_unique<T>(*x) : nullptr;
  }
}

template <typename Target, typename Source>
Target clone_as_value(const Source &x) {
  using T = std::remove_cvref_t<Target>;
  using S = std::remove_cvref_t<Source>;
  if constexpr (requires(const S &s) {
                  s.has_value();
                  *s;
                }) {
    if (!x.has_value())
      return T{};
    using TInner = std::remove_cvref_t<decltype(*std::declval<const T &>())>;
    return T{clone_as_value<TInner>(*x)};
  } else if constexpr (std::is_same_v<T, S>) {
    if constexpr (is_unique_ptr<T>::value) {
      return clone_value(x);
    } else if constexpr (requires { x.clone(); }) {
      return x.clone();
    } else {
      return x;
    }
  } else if constexpr (is_unique_ptr<S>::value) {
    if (!x)
      return T{};
    return clone_as_value<T>(*x);
  } else if constexpr (is_unique_ptr<T>::value) {
    using Inner = typename is_unique_ptr<T>::element_type;
    return std::make_unique<Inner>(clone_as_value<Inner>(x));
  } else {
    return T(x);
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
        return IO(Bind{clone_value(d_a), clone_value(d_b)});
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
      return IO(Bind{std::make_unique<IO>(a), [=](std::any x0) mutable {
                       return std::make_unique<IO>(b(x0));
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
