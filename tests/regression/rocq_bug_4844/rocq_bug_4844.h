#ifndef INCLUDED_ROCQ_BUG_4844
#define INCLUDED_ROCQ_BUG_4844

#include <any>
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

template <typename T> auto clone_value(const T &x) { return x; }

template <typename T>
std::unique_ptr<T> clone_value(const std::unique_ptr<T> &x) {
  return x ? std::make_unique<T>(x->clone()) : nullptr;
}

template <typename T>
std::shared_ptr<T> clone_value(const std::shared_ptr<T> &x) {
  return x ? std::make_shared<T>(x->clone()) : nullptr;
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
      if constexpr (std::is_same_v<Inner, SourceBare>) {
        return std::make_unique<Inner>(x.clone());
      } else if constexpr (requires { x.template clone_as<Inner>(); }) {
        return std::make_unique<Inner>(x.template clone_as<Inner>());
      } else {
        return std::make_unique<Inner>(x.clone());
      }
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
      return x ? x->clone() : Target{};
    } else if constexpr (requires { x->template clone_as<TargetBare>(); }) {
      return x->template clone_as<TargetBare>();
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
      return Sum<t_A, t_B>(Inl{clone_as_value<t_A>(d_a0)});
    } else {
      const auto &[d_a0] = std::get<Inr>(_sv.v());
      return Sum<t_A, t_B>(Inr{clone_as_value<t_B>(d_a0)});
    }
  }

  template <typename _CloneT0, typename _CloneT1>
  __attribute__((pure)) Sum<_CloneT0, _CloneT1> clone_as() const {
    auto &&_sv = *(this);
    if (std::holds_alternative<Inl>(_sv.v())) {
      const auto &[d_a0] = std::get<Inl>(_sv.v());
      return Sum<_CloneT0, _CloneT1>(typename Sum<_CloneT0, _CloneT1>::Inl{
          clone_as_value<_CloneT0>(d_a0)});
    } else {
      const auto &[d_a0] = std::get<Inr>(_sv.v());
      return Sum<_CloneT0, _CloneT1>(typename Sum<_CloneT0, _CloneT1>::Inr{
          clone_as_value<_CloneT1>(d_a0)});
    }
  }

  // CREATORS
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
      return box(Box0{clone_as_value<Sum<ST, ST>>(d_a0)});
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
