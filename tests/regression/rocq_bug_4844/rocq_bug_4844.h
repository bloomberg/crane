#ifndef INCLUDED_ROCQ_BUG_4844
#define INCLUDED_ROCQ_BUG_4844

#include <any>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

template <typename t_A, typename t_B> struct Sum {
  // TYPES
  struct Inl {
    t_A d_a0;
  };

  struct Inr {
    t_B d_a0;
  };

  using variant_t = std::variant<Inl, Inr>;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  Sum() {}

  explicit Sum(Inl _v) : d_v_(std::move(_v)) {}

  explicit Sum(Inr _v) : d_v_(std::move(_v)) {}

  Sum(const Sum<t_A, t_B> &_other) : d_v_(std::move(_other.clone().d_v_)) {}

  Sum(Sum<t_A, t_B> &&_other) : d_v_(std::move(_other.d_v_)) {}

  __attribute__((pure)) Sum<t_A, t_B> &operator=(const Sum<t_A, t_B> &_other) {
    d_v_ = std::move(_other.clone().d_v_);
    return *this;
  }

  __attribute__((pure)) Sum<t_A, t_B> &operator=(Sum<t_A, t_B> &&_other) {
    d_v_ = std::move(_other.d_v_);
    return *this;
  }

  // ACCESSORS
  __attribute__((pure)) Sum<t_A, t_B> clone() const {
    auto &&_sv = *(this);
    if (std::holds_alternative<Inl>(_sv.v())) {
      const auto &[d_a0] = std::get<Inl>(_sv.v());
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
      return Sum<t_A, t_B>(Inl{std::move(__c0)});
    } else {
      const auto &[d_a0] = std::get<Inr>(_sv.v());
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
      return Sum<t_A, t_B>(Inr{std::move(__c0)});
    }
  }

  // CREATORS
  template <typename _U0, typename _U1>
  explicit Sum(const Sum<_U0, _U1> &_other) {
    if (std::holds_alternative<typename Sum<_U0, _U1>::Inl>(_other.v())) {
      const auto &[d_a0] = std::get<typename Sum<_U0, _U1>::Inl>(_other.v());
      d_v_ = Inl{[&]<typename _DstT = t_A>(auto &&__v) -> _DstT {
        if constexpr (
            requires { *__v; } && !requires { std::declval<_DstT>().get(); })
          return _DstT(*__v);
        else if constexpr (
            !requires { *__v; } && requires { std::declval<_DstT>().get(); }) {
          using _E =
              std::remove_pointer_t<decltype(std::declval<_DstT>().get())>;
          return std::make_unique<_E>(std::move(__v));
        } else
          return _DstT(__v);
      }(d_a0)};
    } else {
      const auto &[d_a0] = std::get<typename Sum<_U0, _U1>::Inr>(_other.v());
      d_v_ = Inr{[&]<typename _DstT = t_B>(auto &&__v) -> _DstT {
        if constexpr (
            requires { *__v; } && !requires { std::declval<_DstT>().get(); })
          return _DstT(*__v);
        else if constexpr (
            !requires { *__v; } && requires { std::declval<_DstT>().get(); }) {
          using _E =
              std::remove_pointer_t<decltype(std::declval<_DstT>().get())>;
          return std::make_unique<_E>(std::move(__v));
        } else
          return _DstT(__v);
      }(d_a0)};
    }
  }

  __attribute__((pure)) static Sum<t_A, t_B> inl(t_A a0) {
    return Sum(Inl{std::move(a0)});
  }

  __attribute__((pure)) static Sum<t_A, t_B> inr(t_B a0) {
    return Sum(Inr{std::move(a0)});
  }

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) Sum<t_A, t_B> *operator->() { return this; }

  __attribute__((pure)) const Sum<t_A, t_B> *operator->() const { return this; }

  __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

  __attribute__((pure)) bool operator==(std::nullptr_t) const { return false; }

  // MANIPULATORS
  void reset() { *this = Sum<t_A, t_B>(); }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }
};

struct RocqBug4844 {
  static inline const Sum<std::any, std::any> semilogic =
      Sum<std::any, std::any>::inl(std::any{});
  enum class SomeType { e_BUILD_SOMETYPE };
  using ST = std::any;
  static inline const SomeType SomeTrue = SomeType::e_BUILD_SOMETYPE;
  using abstrSum = Sum<ST, ST>;
  static inline const abstrSum semilogic_ = std::any_cast<abstrSum>(semilogic);

  struct box {
    // TYPES
    struct Box0 {
      Sum<ST, ST> d_a0;
    };

    using variant_t = std::variant<Box0>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    box() {}

    explicit box(Box0 _v) : d_v_(std::move(_v)) {}

    box(const box &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    box(box &&_other) : d_v_(std::move(_other.d_v_)) {}

    __attribute__((pure)) box &operator=(const box &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    __attribute__((pure)) box &operator=(box &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) box clone() const {
      auto &&_sv = *(this);
      const auto &[d_a0] = std::get<Box0>(_sv.v());
      return box(Box0{d_a0.clone()});
    }

    // CREATORS
    constexpr static box box0(Sum<ST, ST> a0) {
      return box(Box0{std::move(a0)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) box *operator->() { return this; }

    __attribute__((pure)) const box *operator->() const { return this; }

    __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

    __attribute__((pure)) bool operator==(std::nullptr_t) const {
      return false;
    }

    // MANIPULATORS
    void reset() { *this = box(); }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, MapsTo<T1, Sum<ST, ST>> F1>
  static T1 box_rect(const SomeType, F1 &&f, const box &b) {
    const auto &[d_a0] = std::get<typename box::Box0>(b.v());
    return f(d_a0);
  }

  template <typename T1, MapsTo<T1, Sum<ST, ST>> F1>
  static T1 box_rec(const SomeType, F1 &&f, const box &b) {
    const auto &[d_a0] = std::get<typename box::Box0>(b.v());
    return f(d_a0);
  }

  static inline const box boxed_semilogic = box::box0(semilogic);
};

#endif // INCLUDED_ROCQ_BUG_4844
