#ifndef INCLUDED_SUM
#define INCLUDED_SUM

#include <any>
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

    template <typename _U0, typename _U1>
    explicit either(const either<_U0, _U1> &_other) {
      if (std::holds_alternative<typename either<_U0, _U1>::Left>(_other.v())) {
        const auto &[a0] =
            std::get<typename either<_U0, _U1>::Left>(_other.v());
        this->v_ = Left{[&]() -> A {
          if constexpr (std::is_same_v<_U0, std::any>) {
            if (a0.type() == typeid(A))
              return std::any_cast<A>(a0);
            if constexpr (requires {
                            typename A::first_type;
                            typename A::second_type;
                          }) {
              const auto &[_k, _v] =
                  std::any_cast<std::pair<std::any, std::any>>(a0);
              return A{[&]() -> typename A::first_type {
                         if constexpr (std::is_same_v<typename A::first_type,
                                                      std::any>)
                           return _k;
                         else
                           return std::any_cast<typename A::first_type>(_k);
                       }(),
                       [&]() -> typename A::second_type {
                         if constexpr (std::is_same_v<typename A::second_type,
                                                      std::any>)
                           return _v;
                         else
                           return std::any_cast<typename A::second_type>(_v);
                       }()};
            }
            return std::any_cast<A>(a0);
          } else
            return A(a0);
        }()};
      } else {
        const auto &[a0] =
            std::get<typename either<_U0, _U1>::Right>(_other.v());
        this->v_ = Right{[&]() -> B {
          if constexpr (std::is_same_v<_U1, std::any>) {
            if (a0.type() == typeid(B))
              return std::any_cast<B>(a0);
            if constexpr (requires {
                            typename B::first_type;
                            typename B::second_type;
                          }) {
              const auto &[_k, _v] =
                  std::any_cast<std::pair<std::any, std::any>>(a0);
              return B{[&]() -> typename B::first_type {
                         if constexpr (std::is_same_v<typename B::first_type,
                                                      std::any>)
                           return _k;
                         else
                           return std::any_cast<typename B::first_type>(_k);
                       }(),
                       [&]() -> typename B::second_type {
                         if constexpr (std::is_same_v<typename B::second_type,
                                                      std::any>)
                           return _v;
                         else
                           return std::any_cast<typename B::second_type>(_v);
                       }()};
            }
            return std::any_cast<B>(a0);
          } else
            return B(a0);
        }()};
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

  static inline const either<uint64_t, bool> left_val =
      either<uint64_t, bool>::left(UINT64_C(5));
  static inline const either<uint64_t, bool> right_val =
      either<uint64_t, bool>::right(true);
  static uint64_t either_to_nat(const either<uint64_t, uint64_t> &e);

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

    template <typename _U0, typename _U1, typename _U2>
    explicit triple(const triple<_U0, _U1, _U2> &_other) {
      if (std::holds_alternative<typename triple<_U0, _U1, _U2>::First>(
              _other.v())) {
        const auto &[a0] =
            std::get<typename triple<_U0, _U1, _U2>::First>(_other.v());
        this->v_ = First{[&]() -> A {
          if constexpr (std::is_same_v<_U0, std::any>) {
            if (a0.type() == typeid(A))
              return std::any_cast<A>(a0);
            if constexpr (requires {
                            typename A::first_type;
                            typename A::second_type;
                          }) {
              const auto &[_k, _v] =
                  std::any_cast<std::pair<std::any, std::any>>(a0);
              return A{[&]() -> typename A::first_type {
                         if constexpr (std::is_same_v<typename A::first_type,
                                                      std::any>)
                           return _k;
                         else
                           return std::any_cast<typename A::first_type>(_k);
                       }(),
                       [&]() -> typename A::second_type {
                         if constexpr (std::is_same_v<typename A::second_type,
                                                      std::any>)
                           return _v;
                         else
                           return std::any_cast<typename A::second_type>(_v);
                       }()};
            }
            return std::any_cast<A>(a0);
          } else
            return A(a0);
        }()};
      } else {
        if (std::holds_alternative<typename triple<_U0, _U1, _U2>::Second>(
                _other.v())) {
          const auto &[a0] =
              std::get<typename triple<_U0, _U1, _U2>::Second>(_other.v());
          this->v_ = Second{[&]() -> B {
            if constexpr (std::is_same_v<_U1, std::any>) {
              if (a0.type() == typeid(B))
                return std::any_cast<B>(a0);
              if constexpr (requires {
                              typename B::first_type;
                              typename B::second_type;
                            }) {
                const auto &[_k, _v] =
                    std::any_cast<std::pair<std::any, std::any>>(a0);
                return B{[&]() -> typename B::first_type {
                           if constexpr (std::is_same_v<typename B::first_type,
                                                        std::any>)
                             return _k;
                           else
                             return std::any_cast<typename B::first_type>(_k);
                         }(),
                         [&]() -> typename B::second_type {
                           if constexpr (std::is_same_v<typename B::second_type,
                                                        std::any>)
                             return _v;
                           else
                             return std::any_cast<typename B::second_type>(_v);
                         }()};
              }
              return std::any_cast<B>(a0);
            } else
              return B(a0);
          }()};
        } else {
          const auto &[a0] =
              std::get<typename triple<_U0, _U1, _U2>::Third>(_other.v());
          this->v_ = Third{[&]() -> C {
            if constexpr (std::is_same_v<_U2, std::any>) {
              if (a0.type() == typeid(C))
                return std::any_cast<C>(a0);
              if constexpr (requires {
                              typename C::first_type;
                              typename C::second_type;
                            }) {
                const auto &[_k, _v] =
                    std::any_cast<std::pair<std::any, std::any>>(a0);
                return C{[&]() -> typename C::first_type {
                           if constexpr (std::is_same_v<typename C::first_type,
                                                        std::any>)
                             return _k;
                           else
                             return std::any_cast<typename C::first_type>(_k);
                         }(),
                         [&]() -> typename C::second_type {
                           if constexpr (std::is_same_v<typename C::second_type,
                                                        std::any>)
                             return _v;
                           else
                             return std::any_cast<typename C::second_type>(_v);
                         }()};
              }
              return std::any_cast<C>(a0);
            } else
              return C(a0);
          }()};
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

  static inline const triple<uint64_t, bool, uint64_t> triple_test =
      triple<uint64_t, bool, uint64_t>::second(true);
  static inline const bool test_left = left_val.is_left();
  static inline const bool test_right = right_val.is_left();
  static inline const uint64_t test_either =
      either_to_nat(either<uint64_t, uint64_t>::left(UINT64_C(3)));
};

#endif // INCLUDED_SUM
