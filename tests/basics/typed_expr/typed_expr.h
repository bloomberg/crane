#ifndef INCLUDED_TYPED_EXPR
#define INCLUDED_TYPED_EXPR

#include <any>
#include <memory>
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

template <typename T> struct is_optional : std::false_type {};

template <typename T> struct is_optional<std::optional<T>> : std::true_type {
  using element_type = T;
};

template <typename T> auto clone_value(const T &x) { return x; }

template <typename T>
std::unique_ptr<T> clone_value(const std::unique_ptr<T> &x) {
  return x ? std::make_unique<T>(x->clone()) : nullptr;
}

template <typename T>
std::shared_ptr<T> clone_value(const std::shared_ptr<T> &x) {
  if constexpr (requires { x->clone(); }) {
    return x ? std::make_shared<T>(x->clone()) : nullptr;
  } else {
    return x;
  }
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
      if constexpr (requires { x.clone(); }) {
        return std::make_unique<Inner>(x.clone());
      } else if constexpr (std::is_same_v<Inner, SourceBare>) {
        if constexpr (requires { x.clone(); }) {
          return std::make_unique<Inner>(x.clone());
        } else {
          return std::make_unique<Inner>(x);
        }
      } else if constexpr (requires { x.template clone_as<Inner>(); }) {
        return std::make_unique<Inner>(x.template clone_as<Inner>());
      } else {
        if constexpr (requires { x.clone(); }) {
          return std::make_unique<Inner>(x.clone());
        } else {
          return std::make_unique<Inner>(x);
        }
      }
    }
  } else if constexpr (is_optional<TargetBare>::value) {
    using Inner = typename is_optional<TargetBare>::element_type;
    if constexpr (is_optional<SourceBare>::value) {
      if (!x)
        return std::nullopt;
      return Target{clone_as_value<Inner>(*x)};
    } else {
      return Target{clone_as_value<Inner>(x)};
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
      if (!x)
        return Target{};
      if constexpr (requires { x->clone(); }) {
        return x->clone();
      } else {
        return *x;
      }
    } else if constexpr (requires { x->template clone_as<TargetBare>(); }) {
      return x->template clone_as<TargetBare>();
    } else if constexpr (requires { x->clone(); }) {
      return x->clone();
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

enum class Ty { e_TNAT, e_TBOOL };

struct Expr {
  // TYPES
  struct ENat {
    unsigned int d_a0;
  };

  struct EBool {
    bool d_a0;
  };

  struct EAdd {
    std::unique_ptr<Expr> d_a0;
    std::unique_ptr<Expr> d_a1;
  };

  struct EEq {
    std::unique_ptr<Expr> d_a0;
    std::unique_ptr<Expr> d_a1;
  };

  struct EIf {
    Ty d_t;
    std::unique_ptr<Expr> d_a1;
    std::unique_ptr<Expr> d_a2;
    std::unique_ptr<Expr> d_a3;
  };

  using variant_t = std::variant<ENat, EBool, EAdd, EEq, EIf>;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  Expr() {}

  explicit Expr(ENat _v) : d_v_(std::move(_v)) {}

  explicit Expr(EBool _v) : d_v_(std::move(_v)) {}

  explicit Expr(EAdd _v) : d_v_(std::move(_v)) {}

  explicit Expr(EEq _v) : d_v_(std::move(_v)) {}

  explicit Expr(EIf _v) : d_v_(std::move(_v)) {}

  Expr(const Expr &_other) : d_v_(std::move(_other.clone().d_v_)) {}

  Expr(Expr &&_other) : d_v_(std::move(_other.d_v_)) {}

  __attribute__((pure)) Expr &operator=(const Expr &_other) {
    d_v_ = std::move(_other.clone().d_v_);
    return *this;
  }

  __attribute__((pure)) Expr &operator=(Expr &&_other) {
    d_v_ = std::move(_other.d_v_);
    return *this;
  }

  // ACCESSORS
  __attribute__((pure)) Expr clone() const {
    auto &&_sv = *(this);
    if (std::holds_alternative<ENat>(_sv.v())) {
      const auto &[d_a0] = std::get<ENat>(_sv.v());
      return Expr(ENat{d_a0});
    } else if (std::holds_alternative<EBool>(_sv.v())) {
      const auto &[d_a0] = std::get<EBool>(_sv.v());
      return Expr(EBool{d_a0});
    } else if (std::holds_alternative<EAdd>(_sv.v())) {
      const auto &[d_a0, d_a1] = std::get<EAdd>(_sv.v());
      return Expr(EAdd{clone_as_value<std::unique_ptr<Expr>>(d_a0),
                       clone_as_value<std::unique_ptr<Expr>>(d_a1)});
    } else if (std::holds_alternative<EEq>(_sv.v())) {
      const auto &[d_a0, d_a1] = std::get<EEq>(_sv.v());
      return Expr(EEq{clone_as_value<std::unique_ptr<Expr>>(d_a0),
                      clone_as_value<std::unique_ptr<Expr>>(d_a1)});
    } else {
      const auto &[d_t, d_a1, d_a2, d_a3] = std::get<EIf>(_sv.v());
      return Expr(EIf{d_t, clone_as_value<std::unique_ptr<Expr>>(d_a1),
                      clone_as_value<std::unique_ptr<Expr>>(d_a2),
                      clone_as_value<std::unique_ptr<Expr>>(d_a3)});
    }
  }

  // CREATORS
  __attribute__((pure)) static Expr enat(unsigned int a0) {
    return Expr(ENat{std::move(a0)});
  }

  __attribute__((pure)) static Expr ebool(bool a0) {
    return Expr(EBool{std::move(a0)});
  }

  __attribute__((pure)) static Expr eadd(const Expr &a0, const Expr &a1) {
    return Expr(EAdd{std::make_unique<Expr>(a0.clone()),
                     std::make_unique<Expr>(a1.clone())});
  }

  __attribute__((pure)) static Expr eeq(const Expr &a0, const Expr &a1) {
    return Expr(EEq{std::make_unique<Expr>(a0.clone()),
                    std::make_unique<Expr>(a1.clone())});
  }

  __attribute__((pure)) static Expr eif(Ty t, const Expr &a1, const Expr &a2,
                                        const Expr &a3) {
    return Expr(EIf{std::move(t), std::make_unique<Expr>(a1.clone()),
                    std::make_unique<Expr>(a2.clone()),
                    std::make_unique<Expr>(a3.clone())});
  }

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) Expr *operator->() { return this; }

  __attribute__((pure)) const Expr *operator->() const { return this; }

  __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

  __attribute__((pure)) bool operator==(std::nullptr_t) const { return false; }

  // MANIPULATORS
  void reset() { *this = Expr(); }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }

  std::any eval(const Ty) const {
    auto &&_sv = *(this);
    if (std::holds_alternative<typename Expr::ENat>(_sv.v())) {
      const auto &[d_a0] = std::get<typename Expr::ENat>(_sv.v());
      return d_a0;
    } else if (std::holds_alternative<typename Expr::EBool>(_sv.v())) {
      const auto &[d_a0] = std::get<typename Expr::EBool>(_sv.v());
      return d_a0;
    } else if (std::holds_alternative<typename Expr::EAdd>(_sv.v())) {
      const auto &[d_a0, d_a1] = std::get<typename Expr::EAdd>(_sv.v());
      return (std::any_cast<unsigned int>((*(d_a0)).eval(Ty::e_TNAT)) +
              std::any_cast<unsigned int>((*(d_a1)).eval(Ty::e_TNAT)));
    } else if (std::holds_alternative<typename Expr::EEq>(_sv.v())) {
      const auto &[d_a0, d_a1] = std::get<typename Expr::EEq>(_sv.v());
      return std::any_cast<unsigned int>((*(d_a0)).eval(Ty::e_TNAT)) ==
             std::any_cast<unsigned int>((*(d_a1)).eval(Ty::e_TNAT));
    } else {
      const auto &[d_t, d_a1, d_a2, d_a3] =
          std::get<typename Expr::EIf>(_sv.v());
      if (std::any_cast<bool>((*(d_a1)).eval(Ty::e_TBOOL))) {
        return (*(d_a2)).eval(d_t);
      } else {
        return (*(d_a3)).eval(d_t);
      }
    }
  }
};

#endif // INCLUDED_TYPED_EXPR
