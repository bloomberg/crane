#ifndef INCLUDED_SUM
#define INCLUDED_SUM

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

struct Sum {
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
        t_A __c0;
        if constexpr (
            requires { d_a0 ? 0 : 0; } && requires { *d_a0; } &&
            requires { d_a0->clone(); } && requires { d_a0.get(); }) {
          using _E = std::remove_cvref_t<decltype(*d_a0)>;
          __c0 = d_a0 ? std::make_unique<_E>(d_a0->clone()) : nullptr;
        } else if constexpr (requires { d_a0.clone(); }) {
          __c0 = d_a0.clone();
        } else {
          __c0 = d_a0;
        }
        return either<t_A, t_B>(Left{std::move(__c0)});
      } else {
        const auto &[d_a0] = std::get<Right>(_sv.v());
        t_B __c0;
        if constexpr (
            requires { d_a0 ? 0 : 0; } && requires { *d_a0; } &&
            requires { d_a0->clone(); } && requires { d_a0.get(); }) {
          using _E = std::remove_cvref_t<decltype(*d_a0)>;
          __c0 = d_a0 ? std::make_unique<_E>(d_a0->clone()) : nullptr;
        } else if constexpr (requires { d_a0.clone(); }) {
          __c0 = d_a0.clone();
        } else {
          __c0 = d_a0;
        }
        return either<t_A, t_B>(Right{std::move(__c0)});
      }
    }

    // CREATORS
    template <typename _U0, typename _U1>
    explicit either(const either<_U0, _U1> &_other) {
      if (std::holds_alternative<typename either<_U0, _U1>::Left>(_other.v())) {
        const auto &[d_a0] =
            std::get<typename either<_U0, _U1>::Left>(_other.v());
        d_v_ = Left{[&]<typename _DstT = t_A>(auto &&__v) -> _DstT {
          if constexpr (
              requires { *__v; } && !requires { std::declval<_DstT>().get(); })
            return _DstT(*__v);
          else if constexpr (
              !requires { *__v; } &&
              requires { std::declval<_DstT>().get(); }) {
            using _E =
                std::remove_pointer_t<decltype(std::declval<_DstT>().get())>;
            return std::make_unique<_E>(std::move(__v));
          } else
            return _DstT(__v);
        }(d_a0)};
      } else {
        const auto &[d_a0] =
            std::get<typename either<_U0, _U1>::Right>(_other.v());
        d_v_ = Right{[&]<typename _DstT = t_B>(auto &&__v) -> _DstT {
          if constexpr (
              requires { *__v; } && !requires { std::declval<_DstT>().get(); })
            return _DstT(*__v);
          else if constexpr (
              !requires { *__v; } &&
              requires { std::declval<_DstT>().get(); }) {
            using _E =
                std::remove_pointer_t<decltype(std::declval<_DstT>().get())>;
            return std::make_unique<_E>(std::move(__v));
          } else
            return _DstT(__v);
        }(d_a0)};
      }
    }

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

    template <typename T1, MapsTo<T1, t_B> F0>
    __attribute__((pure)) either<t_A, T1> map_right(F0 &&f) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename either<t_A, t_B>::Left>(_sv.v())) {
        const auto &[d_a0] = std::get<typename either<t_A, t_B>::Left>(_sv.v());
        return either<t_A, T1>::left(d_a0);
      } else {
        const auto &[d_a0] =
            std::get<typename either<t_A, t_B>::Right>(_sv.v());
        return either<t_A, T1>::right(f(d_a0));
      }
    }

    template <typename T1, MapsTo<T1, t_A> F0>
    __attribute__((pure)) either<T1, t_B> map_left(F0 &&f) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename either<t_A, t_B>::Left>(_sv.v())) {
        const auto &[d_a0] = std::get<typename either<t_A, t_B>::Left>(_sv.v());
        return either<T1, t_B>::left(f(d_a0));
      } else {
        const auto &[d_a0] =
            std::get<typename either<t_A, t_B>::Right>(_sv.v());
        return either<T1, t_B>::right(d_a0);
      }
    }

    __attribute__((pure)) bool is_left() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename either<t_A, t_B>::Left>(_sv.v())) {
        return true;
      } else {
        return false;
      }
    }

    template <typename T1, MapsTo<T1, t_A> F0, MapsTo<T1, t_B> F1>
    T1 either_rec(F0 &&f, F1 &&f0) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename either<t_A, t_B>::Left>(_sv.v())) {
        const auto &[d_a0] = std::get<typename either<t_A, t_B>::Left>(_sv.v());
        return f(d_a0);
      } else {
        const auto &[d_a0] =
            std::get<typename either<t_A, t_B>::Right>(_sv.v());
        return f0(d_a0);
      }
    }

    template <typename T1, MapsTo<T1, t_A> F0, MapsTo<T1, t_B> F1>
    T1 either_rect(F0 &&f, F1 &&f0) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename either<t_A, t_B>::Left>(_sv.v())) {
        const auto &[d_a0] = std::get<typename either<t_A, t_B>::Left>(_sv.v());
        return f(d_a0);
      } else {
        const auto &[d_a0] =
            std::get<typename either<t_A, t_B>::Right>(_sv.v());
        return f0(d_a0);
      }
    }
  };

  static inline const either<unsigned int, bool> left_val =
      either<unsigned int, bool>::left(5u);
  static inline const either<unsigned int, bool> right_val =
      either<unsigned int, bool>::right(true);
  __attribute__((pure)) static unsigned int
  either_to_nat(const either<unsigned int, unsigned int> &e);

  template <typename t_A, typename t_B, typename t_C> struct triple {
    // TYPES
    struct First {
      t_A d_a0;
    };

    struct Second {
      t_B d_a0;
    };

    struct Third {
      t_C d_a0;
    };

    using variant_t = std::variant<First, Second, Third>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    triple() {}

    explicit triple(First _v) : d_v_(std::move(_v)) {}

    explicit triple(Second _v) : d_v_(std::move(_v)) {}

    explicit triple(Third _v) : d_v_(std::move(_v)) {}

    triple(const triple<t_A, t_B, t_C> &_other)
        : d_v_(std::move(_other.clone().d_v_)) {}

    triple(triple<t_A, t_B, t_C> &&_other) : d_v_(std::move(_other.d_v_)) {}

    __attribute__((pure)) triple<t_A, t_B, t_C> &
    operator=(const triple<t_A, t_B, t_C> &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    __attribute__((pure)) triple<t_A, t_B, t_C> &
    operator=(triple<t_A, t_B, t_C> &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) triple<t_A, t_B, t_C> clone() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<First>(_sv.v())) {
        const auto &[d_a0] = std::get<First>(_sv.v());
        t_A __c0;
        if constexpr (
            requires { d_a0 ? 0 : 0; } && requires { *d_a0; } &&
            requires { d_a0->clone(); } && requires { d_a0.get(); }) {
          using _E = std::remove_cvref_t<decltype(*d_a0)>;
          __c0 = d_a0 ? std::make_unique<_E>(d_a0->clone()) : nullptr;
        } else if constexpr (requires { d_a0.clone(); }) {
          __c0 = d_a0.clone();
        } else {
          __c0 = d_a0;
        }
        return triple<t_A, t_B, t_C>(First{std::move(__c0)});
      } else if (std::holds_alternative<Second>(_sv.v())) {
        const auto &[d_a0] = std::get<Second>(_sv.v());
        t_B __c0;
        if constexpr (
            requires { d_a0 ? 0 : 0; } && requires { *d_a0; } &&
            requires { d_a0->clone(); } && requires { d_a0.get(); }) {
          using _E = std::remove_cvref_t<decltype(*d_a0)>;
          __c0 = d_a0 ? std::make_unique<_E>(d_a0->clone()) : nullptr;
        } else if constexpr (requires { d_a0.clone(); }) {
          __c0 = d_a0.clone();
        } else {
          __c0 = d_a0;
        }
        return triple<t_A, t_B, t_C>(Second{std::move(__c0)});
      } else {
        const auto &[d_a0] = std::get<Third>(_sv.v());
        t_C __c0;
        if constexpr (
            requires { d_a0 ? 0 : 0; } && requires { *d_a0; } &&
            requires { d_a0->clone(); } && requires { d_a0.get(); }) {
          using _E = std::remove_cvref_t<decltype(*d_a0)>;
          __c0 = d_a0 ? std::make_unique<_E>(d_a0->clone()) : nullptr;
        } else if constexpr (requires { d_a0.clone(); }) {
          __c0 = d_a0.clone();
        } else {
          __c0 = d_a0;
        }
        return triple<t_A, t_B, t_C>(Third{std::move(__c0)});
      }
    }

    // CREATORS
    template <typename _U0, typename _U1, typename _U2>
    explicit triple(const triple<_U0, _U1, _U2> &_other) {
      if (std::holds_alternative<typename triple<_U0, _U1, _U2>::First>(
              _other.v())) {
        const auto &[d_a0] =
            std::get<typename triple<_U0, _U1, _U2>::First>(_other.v());
        d_v_ = First{[&]<typename _DstT = t_A>(auto &&__v) -> _DstT {
          if constexpr (
              requires { *__v; } && !requires { std::declval<_DstT>().get(); })
            return _DstT(*__v);
          else if constexpr (
              !requires { *__v; } &&
              requires { std::declval<_DstT>().get(); }) {
            using _E =
                std::remove_pointer_t<decltype(std::declval<_DstT>().get())>;
            return std::make_unique<_E>(std::move(__v));
          } else
            return _DstT(__v);
        }(d_a0)};
      } else if (std::holds_alternative<typename triple<_U0, _U1, _U2>::Second>(
                     _other.v())) {
        const auto &[d_a0] =
            std::get<typename triple<_U0, _U1, _U2>::Second>(_other.v());
        d_v_ = Second{[&]<typename _DstT = t_B>(auto &&__v) -> _DstT {
          if constexpr (
              requires { *__v; } && !requires { std::declval<_DstT>().get(); })
            return _DstT(*__v);
          else if constexpr (
              !requires { *__v; } &&
              requires { std::declval<_DstT>().get(); }) {
            using _E =
                std::remove_pointer_t<decltype(std::declval<_DstT>().get())>;
            return std::make_unique<_E>(std::move(__v));
          } else
            return _DstT(__v);
        }(d_a0)};
      } else {
        const auto &[d_a0] =
            std::get<typename triple<_U0, _U1, _U2>::Third>(_other.v());
        d_v_ = Third{[&]<typename _DstT = t_C>(auto &&__v) -> _DstT {
          if constexpr (
              requires { *__v; } && !requires { std::declval<_DstT>().get(); })
            return _DstT(*__v);
          else if constexpr (
              !requires { *__v; } &&
              requires { std::declval<_DstT>().get(); }) {
            using _E =
                std::remove_pointer_t<decltype(std::declval<_DstT>().get())>;
            return std::make_unique<_E>(std::move(__v));
          } else
            return _DstT(__v);
        }(d_a0)};
      }
    }

    __attribute__((pure)) static triple<t_A, t_B, t_C> first(t_A a0) {
      return triple(First{std::move(a0)});
    }

    __attribute__((pure)) static triple<t_A, t_B, t_C> second(t_B a0) {
      return triple(Second{std::move(a0)});
    }

    __attribute__((pure)) static triple<t_A, t_B, t_C> third(t_C a0) {
      return triple(Third{std::move(a0)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) triple<t_A, t_B, t_C> *operator->() { return this; }

    __attribute__((pure)) const triple<t_A, t_B, t_C> *operator->() const {
      return this;
    }

    __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

    __attribute__((pure)) bool operator==(std::nullptr_t) const {
      return false;
    }

    // MANIPULATORS
    void reset() { *this = triple<t_A, t_B, t_C>(); }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    template <typename T1, MapsTo<T1, t_A> F0, MapsTo<T1, t_B> F1,
              MapsTo<T1, t_C> F2>
    T1 triple_rec(F0 &&f, F1 &&f0, F2 &&f1) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename triple<t_A, t_B, t_C>::First>(
              _sv.v())) {
        const auto &[d_a0] =
            std::get<typename triple<t_A, t_B, t_C>::First>(_sv.v());
        return f(d_a0);
      } else if (std::holds_alternative<typename triple<t_A, t_B, t_C>::Second>(
                     _sv.v())) {
        const auto &[d_a0] =
            std::get<typename triple<t_A, t_B, t_C>::Second>(_sv.v());
        return f0(d_a0);
      } else {
        const auto &[d_a0] =
            std::get<typename triple<t_A, t_B, t_C>::Third>(_sv.v());
        return f1(d_a0);
      }
    }

    template <typename T1, MapsTo<T1, t_A> F0, MapsTo<T1, t_B> F1,
              MapsTo<T1, t_C> F2>
    T1 triple_rect(F0 &&f, F1 &&f0, F2 &&f1) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename triple<t_A, t_B, t_C>::First>(
              _sv.v())) {
        const auto &[d_a0] =
            std::get<typename triple<t_A, t_B, t_C>::First>(_sv.v());
        return f(d_a0);
      } else if (std::holds_alternative<typename triple<t_A, t_B, t_C>::Second>(
                     _sv.v())) {
        const auto &[d_a0] =
            std::get<typename triple<t_A, t_B, t_C>::Second>(_sv.v());
        return f0(d_a0);
      } else {
        const auto &[d_a0] =
            std::get<typename triple<t_A, t_B, t_C>::Third>(_sv.v());
        return f1(d_a0);
      }
    }
  };

  static inline const triple<unsigned int, bool, unsigned int> triple_test =
      triple<unsigned int, bool, unsigned int>::second(true);
  static inline const bool test_left = left_val.is_left();
  static inline const bool test_right = right_val.is_left();
  static inline const unsigned int test_either =
      either_to_nat(either<unsigned int, unsigned int>::left(3u));
};

#endif // INCLUDED_SUM
