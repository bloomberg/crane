#ifndef INCLUDED_ROCQ_BUG_4844
#define INCLUDED_ROCQ_BUG_4844

#include <any>
#include <type_traits>
#include <utility>
#include <variant>

template <typename A, typename B> struct Sum {
  // TYPES
  struct Inl {
    A a0;
  };

  struct Inr {
    B a0;
  };

  using variant_t = std::variant<Inl, Inr>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  Sum() {}

  explicit Sum(Inl _v) : v_(std::move(_v)) {}

  explicit Sum(Inr _v) : v_(std::move(_v)) {}

  template <typename _U0, typename _U1>
  explicit Sum(const Sum<_U0, _U1> &_other) {
    if (std::holds_alternative<typename Sum<_U0, _U1>::Inl>(_other.v())) {
      const auto &[a0] = std::get<typename Sum<_U0, _U1>::Inl>(_other.v());
      this->v_ = Inl{[&]() -> A {
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
      const auto &[a0] = std::get<typename Sum<_U0, _U1>::Inr>(_other.v());
      this->v_ = Inr{[&]() -> B {
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

  static Sum<A, B> inl(A a0) { return Sum(Inl{std::move(a0)}); }

  static Sum<A, B> inr(B a0) { return Sum(Inr{std::move(a0)}); }

  // MANIPULATORS
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

struct RocqBug4844 {
  static inline const Sum<std::any, std::any> semilogic =
      Sum<std::any, std::any>::inl(std::any{});
  enum class SomeType { BUILD_SOMETYPE };
  using ST = std::any;
  static inline const SomeType SomeTrue = SomeType::BUILD_SOMETYPE;
  using abstrSum = Sum<ST, ST>;
  static inline const abstrSum semilogic_ = std::any_cast<abstrSum>(semilogic);

  struct box {
    // DATA
    Sum<ST, ST> a0;

    // ACCESSORS
    box clone() const { return {a0}; }

    // CREATORS
    static box box0(Sum<ST, ST> a0) { return {std::move(a0)}; }
  };

  template <typename T1, typename F1>
    requires std::is_invocable_r_v<T1, F1 &, Sum<ST, ST> &>
  static T1 box_rect(SomeType, F1 &&f, const box &b) {
    const auto &[a0] = b;
    return f(a0);
  }

  template <typename T1, typename F1>
    requires std::is_invocable_r_v<T1, F1 &, Sum<ST, ST> &>
  static T1 box_rec(SomeType, F1 &&f, const box &b) {
    const auto &[a0] = b;
    return f(a0);
  }

  static inline const box boxed_semilogic = box::box0(semilogic);
};

#endif // INCLUDED_ROCQ_BUG_4844
