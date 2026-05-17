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

  Sum(const Sum<A, B> &_other) : v_(_other.v_) {}

  Sum(Sum<A, B> &&_other) noexcept : v_(std::move(_other.v_)) {}

  Sum<A, B> &operator=(const Sum<A, B> &_other) {
    v_ = _other.v_;
    return *this;
  }

  Sum<A, B> &operator=(Sum<A, B> &&_other) noexcept {
    v_ = std::move(_other.v_);
    return *this;
  }

  // ACCESSORS
  Sum<A, B> clone() const {
    if (std::holds_alternative<Inl>(this->v())) {
      const auto &[a0] = std::get<Inl>(this->v());
      return Sum<A, B>(Inl{a0});
    } else {
      const auto &[a0] = std::get<Inr>(this->v());
      return Sum<A, B>(Inr{a0});
    }
  }

  // CREATORS
  template <typename _U0, typename _U1>
  explicit Sum(const Sum<_U0, _U1> &_other) {
    if (std::holds_alternative<typename Sum<_U0, _U1>::Inl>(_other.v())) {
      const auto &[a0] = std::get<typename Sum<_U0, _U1>::Inl>(_other.v());
      this->v_ = Inl{A(a0)};
    } else {
      const auto &[a0] = std::get<typename Sum<_U0, _U1>::Inr>(_other.v());
      this->v_ = Inr{B(a0)};
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
