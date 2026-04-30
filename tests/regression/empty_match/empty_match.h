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

  static unsigned int from_empty(const empty &_x0);

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

    either<t_A, t_B> &operator=(const either<t_A, t_B> &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    either<t_A, t_B> &operator=(either<t_A, t_B> &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    either<t_A, t_B> clone() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<Left>(_sv.v())) {
        const auto &[d_a0] = std::get<Left>(_sv.v());
        return either<t_A, t_B>(Left{d_a0});
      } else {
        const auto &[d_a0] = std::get<Right>(_sv.v());
        return either<t_A, t_B>(Right{d_a0});
      }
    }

    // CREATORS
    template <typename _U0, typename _U1>
    explicit either(const either<_U0, _U1> &_other) {
      if (std::holds_alternative<typename either<_U0, _U1>::Left>(_other.v())) {
        const auto &[d_a0] =
            std::get<typename either<_U0, _U1>::Left>(_other.v());
        d_v_ = Left{t_A(d_a0)};
      } else {
        const auto &[d_a0] =
            std::get<typename either<_U0, _U1>::Right>(_other.v());
        d_v_ = Right{t_B(d_a0)};
      }
    }

    static either<t_A, t_B> left(t_A a0) { return either(Left{std::move(a0)}); }

    static either<t_A, t_B> right(t_B a0) {
      return either(Right{std::move(a0)});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    const variant_t &v() const { return d_v_; }
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
