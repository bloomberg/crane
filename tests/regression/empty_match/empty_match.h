#ifndef INCLUDED_EMPTY_MATCH
#define INCLUDED_EMPTY_MATCH

#include <stdexcept>
#include <type_traits>
#include <utility>
#include <variant>

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

  template <typename A, typename B> struct either {
    // TYPES
    struct Left {
      A a0;
    };

    struct Right {
      B a0;
    };

    using variant_t = std::variant<Left, Right>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    either() {}

    explicit either(Left _v) : v_(std::move(_v)) {}

    explicit either(Right _v) : v_(std::move(_v)) {}

    either(const either<A, B> &_other) : v_(std::move(_other.clone().v_)) {}

    either(either<A, B> &&_other) : v_(std::move(_other.v_)) {}

    either<A, B> &operator=(const either<A, B> &_other) {
      v_ = std::move(_other.clone().v_);
      return *this;
    }

    either<A, B> &operator=(either<A, B> &&_other) {
      v_ = std::move(_other.v_);
      return *this;
    }

    // ACCESSORS
    either<A, B> clone() const {
      if (std::holds_alternative<Left>(this->v())) {
        const auto &[a0] = std::get<Left>(this->v());
        return either<A, B>(Left{a0});
      } else {
        const auto &[a0] = std::get<Right>(this->v());
        return either<A, B>(Right{a0});
      }
    }

    // CREATORS
    template <typename _U0, typename _U1>
    explicit either(const either<_U0, _U1> &_other) {
      if (std::holds_alternative<typename either<_U0, _U1>::Left>(_other.v())) {
        const auto &[a0] =
            std::get<typename either<_U0, _U1>::Left>(_other.v());
        this->v_ = Left{A(a0)};
      } else {
        const auto &[a0] =
            std::get<typename either<_U0, _U1>::Right>(_other.v());
        this->v_ = Right{B(a0)};
      }
    }

    static either<A, B> left(A a0) { return either(Left{std::move(a0)}); }

    static either<A, B> right(B a0) { return either(Right{std::move(a0)}); }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename T2, typename T3, typename F0, typename F1>
    requires std::is_invocable_r_v<T3, F0 &, T1 &> &&
             std::is_invocable_r_v<T3, F1 &, T2 &>
  static T3 either_rect(F0 &&f, F1 &&f0, const either<T1, T2> &e) {
    if (std::holds_alternative<typename either<T1, T2>::Left>(e.v())) {
      const auto &[a0] = std::get<typename either<T1, T2>::Left>(e.v());
      return f(a0);
    } else {
      const auto &[a0] = std::get<typename either<T1, T2>::Right>(e.v());
      return f0(a0);
    }
  }

  template <typename T1, typename T2, typename T3, typename F0, typename F1>
    requires std::is_invocable_r_v<T3, F0 &, T1 &> &&
             std::is_invocable_r_v<T3, F1 &, T2 &>
  static T3 either_rec(F0 &&f, F1 &&f0, const either<T1, T2> &e) {
    if (std::holds_alternative<typename either<T1, T2>::Left>(e.v())) {
      const auto &[a0] = std::get<typename either<T1, T2>::Left>(e.v());
      return f(a0);
    } else {
      const auto &[a0] = std::get<typename either<T1, T2>::Right>(e.v());
      return f0(a0);
    }
  }

  template <typename T1> static T1 handle_left(const either<T1, empty> &e) {
    if (std::holds_alternative<typename either<T1, empty>::Left>(e.v())) {
      const auto &[a0] = std::get<typename either<T1, empty>::Left>(e.v());
      return a0;
    } else {
      const auto &[a0] = std::get<typename either<T1, empty>::Right>(e.v());
      return absurd<T1>(a0);
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
