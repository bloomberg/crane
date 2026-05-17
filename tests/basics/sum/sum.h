#ifndef INCLUDED_SUM
#define INCLUDED_SUM

#include <type_traits>
#include <utility>
#include <variant>

struct Sum {
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

    either(const either<A, B> &_other) : v_(_other.v_) {}

    either(either<A, B> &&_other) noexcept : v_(std::move(_other.v_)) {}

    either<A, B> &operator=(const either<A, B> &_other) {
      v_ = _other.v_;
      return *this;
    }

    either<A, B> &operator=(either<A, B> &&_other) noexcept {
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

    template <typename T1, typename F0>
      requires std::is_invocable_r_v<T1, F0 &, B &>
    either<A, T1> map_right(F0 &&f) const {
      if (std::holds_alternative<typename either<A, B>::Left>(this->v())) {
        const auto &[a0] = std::get<typename either<A, B>::Left>(this->v());
        return either<A, T1>::left(a0);
      } else {
        const auto &[a0] = std::get<typename either<A, B>::Right>(this->v());
        return either<A, T1>::right(f(a0));
      }
    }

    template <typename T1, typename F0>
      requires std::is_invocable_r_v<T1, F0 &, A &>
    either<T1, B> map_left(F0 &&f) const {
      if (std::holds_alternative<typename either<A, B>::Left>(this->v())) {
        const auto &[a0] = std::get<typename either<A, B>::Left>(this->v());
        return either<T1, B>::left(f(a0));
      } else {
        const auto &[a0] = std::get<typename either<A, B>::Right>(this->v());
        return either<T1, B>::right(a0);
      }
    }

    bool is_left() const {
      if (std::holds_alternative<typename either<A, B>::Left>(this->v())) {
        return true;
      } else {
        return false;
      }
    }

    template <typename T1, typename F0, typename F1>
      requires std::is_invocable_r_v<T1, F0 &, A &> &&
               std::is_invocable_r_v<T1, F1 &, B &>
    T1 either_rec(F0 &&f, F1 &&f0) const {
      if (std::holds_alternative<typename either<A, B>::Left>(this->v())) {
        const auto &[a0] = std::get<typename either<A, B>::Left>(this->v());
        return f(a0);
      } else {
        const auto &[a0] = std::get<typename either<A, B>::Right>(this->v());
        return f0(a0);
      }
    }

    template <typename T1, typename F0, typename F1>
      requires std::is_invocable_r_v<T1, F0 &, A &> &&
               std::is_invocable_r_v<T1, F1 &, B &>
    T1 either_rect(F0 &&f, F1 &&f0) const {
      if (std::holds_alternative<typename either<A, B>::Left>(this->v())) {
        const auto &[a0] = std::get<typename either<A, B>::Left>(this->v());
        return f(a0);
      } else {
        const auto &[a0] = std::get<typename either<A, B>::Right>(this->v());
        return f0(a0);
      }
    }
  };

  static inline const either<unsigned int, bool> left_val =
      either<unsigned int, bool>::left(5u);
  static inline const either<unsigned int, bool> right_val =
      either<unsigned int, bool>::right(true);
  static unsigned int
  either_to_nat(const either<unsigned int, unsigned int> &e);

  template <typename A, typename B, typename C> struct triple {
    // TYPES
    struct First {
      A a0;
    };

    struct Second {
      B a0;
    };

    struct Third {
      C a0;
    };

    using variant_t = std::variant<First, Second, Third>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    triple() {}

    explicit triple(First _v) : v_(std::move(_v)) {}

    explicit triple(Second _v) : v_(std::move(_v)) {}

    explicit triple(Third _v) : v_(std::move(_v)) {}

    triple(const triple<A, B, C> &_other) : v_(_other.v_) {}

    triple(triple<A, B, C> &&_other) noexcept : v_(std::move(_other.v_)) {}

    triple<A, B, C> &operator=(const triple<A, B, C> &_other) {
      v_ = _other.v_;
      return *this;
    }

    triple<A, B, C> &operator=(triple<A, B, C> &&_other) noexcept {
      v_ = std::move(_other.v_);
      return *this;
    }

    // ACCESSORS
    triple<A, B, C> clone() const {
      if (std::holds_alternative<First>(this->v())) {
        const auto &[a0] = std::get<First>(this->v());
        return triple<A, B, C>(First{a0});
      } else if (std::holds_alternative<Second>(this->v())) {
        const auto &[a0] = std::get<Second>(this->v());
        return triple<A, B, C>(Second{a0});
      } else {
        const auto &[a0] = std::get<Third>(this->v());
        return triple<A, B, C>(Third{a0});
      }
    }

    // CREATORS
    template <typename _U0, typename _U1, typename _U2>
    explicit triple(const triple<_U0, _U1, _U2> &_other) {
      if (std::holds_alternative<typename triple<_U0, _U1, _U2>::First>(
              _other.v())) {
        const auto &[a0] =
            std::get<typename triple<_U0, _U1, _U2>::First>(_other.v());
        this->v_ = First{A(a0)};
      } else {
        if (std::holds_alternative<typename triple<_U0, _U1, _U2>::Second>(
                _other.v())) {
          const auto &[a0] =
              std::get<typename triple<_U0, _U1, _U2>::Second>(_other.v());
          this->v_ = Second{B(a0)};
        } else {
          const auto &[a0] =
              std::get<typename triple<_U0, _U1, _U2>::Third>(_other.v());
          this->v_ = Third{C(a0)};
        }
      }
    }

    static triple<A, B, C> first(A a0) { return triple(First{std::move(a0)}); }

    static triple<A, B, C> second(B a0) {
      return triple(Second{std::move(a0)});
    }

    static triple<A, B, C> third(C a0) { return triple(Third{std::move(a0)}); }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    template <typename T1, typename F0, typename F1, typename F2>
      requires std::is_invocable_r_v<T1, F0 &, A &> &&
               std::is_invocable_r_v<T1, F1 &, B &> &&
               std::is_invocable_r_v<T1, F2 &, C &>
    T1 triple_rec(F0 &&f, F1 &&f0, F2 &&f1) const {
      if (std::holds_alternative<typename triple<A, B, C>::First>(this->v())) {
        const auto &[a0] = std::get<typename triple<A, B, C>::First>(this->v());
        return f(a0);
      } else if (std::holds_alternative<typename triple<A, B, C>::Second>(
                     this->v())) {
        const auto &[a0] =
            std::get<typename triple<A, B, C>::Second>(this->v());
        return f0(a0);
      } else {
        const auto &[a0] = std::get<typename triple<A, B, C>::Third>(this->v());
        return f1(a0);
      }
    }

    template <typename T1, typename F0, typename F1, typename F2>
      requires std::is_invocable_r_v<T1, F0 &, A &> &&
               std::is_invocable_r_v<T1, F1 &, B &> &&
               std::is_invocable_r_v<T1, F2 &, C &>
    T1 triple_rect(F0 &&f, F1 &&f0, F2 &&f1) const {
      if (std::holds_alternative<typename triple<A, B, C>::First>(this->v())) {
        const auto &[a0] = std::get<typename triple<A, B, C>::First>(this->v());
        return f(a0);
      } else if (std::holds_alternative<typename triple<A, B, C>::Second>(
                     this->v())) {
        const auto &[a0] =
            std::get<typename triple<A, B, C>::Second>(this->v());
        return f0(a0);
      } else {
        const auto &[a0] = std::get<typename triple<A, B, C>::Third>(this->v());
        return f1(a0);
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
