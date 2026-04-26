#ifndef INCLUDED_ROCQ_BUG_13581
#define INCLUDED_ROCQ_BUG_13581

#include <functional>
#include <memory>
#include <optional>
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

template <typename T> auto clone_value(const T &x) { return x; }

template <typename T>
std::unique_ptr<T> clone_value(const std::unique_ptr<T> &x) {
  if constexpr (requires { x->clone(); }) {
    return x ? std::make_unique<T>(x->clone()) : nullptr;
  } else {
    return x ? std::make_unique<T>(*x) : nullptr;
  }
}

template <typename Target, typename Source>
Target clone_as_value(const Source &x) {
  using T = std::remove_cvref_t<Target>;
  using S = std::remove_cvref_t<Source>;
  if constexpr (requires(const S &s) {
                  s.has_value();
                  *s;
                }) {
    if (!x.has_value())
      return T{};
    using TInner = std::remove_cvref_t<decltype(*std::declval<const T &>())>;
    return T{clone_as_value<TInner>(*x)};
  } else if constexpr (std::is_same_v<T, S>) {
    if constexpr (is_unique_ptr<T>::value) {
      return clone_value(x);
    } else if constexpr (requires { x.clone(); }) {
      return x.clone();
    } else {
      return x;
    }
  } else if constexpr (is_unique_ptr<S>::value) {
    if (!x)
      return T{};
    return clone_as_value<T>(*x);
  } else if constexpr (is_unique_ptr<T>::value) {
    using Inner = typename is_unique_ptr<T>::element_type;
    return std::make_unique<Inner>(clone_as_value<Inner>(x));
  } else {
    return T(x);
  }
}

enum class Unit { e_TT };
enum class Bool0 { e_TRUE0, e_FALSE0 };

struct Nat {
  // TYPES
  struct O {};

  struct S {
    std::unique_ptr<Nat> d_a0;
  };

  using variant_t = std::variant<O, S>;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  Nat() {}

  explicit Nat(O _v) : d_v_(_v) {}

  explicit Nat(S _v) : d_v_(std::move(_v)) {}

  Nat(const Nat &_other) : d_v_(std::move(_other.clone().d_v_)) {}

  Nat(Nat &&_other) : d_v_(std::move(_other.d_v_)) {}

  __attribute__((pure)) Nat &operator=(const Nat &_other) {
    d_v_ = std::move(_other.clone().d_v_);
    return *this;
  }

  __attribute__((pure)) Nat &operator=(Nat &&_other) {
    d_v_ = std::move(_other.d_v_);
    return *this;
  }

  // ACCESSORS
  __attribute__((pure)) Nat clone() const {
    auto &&_sv = *(this);
    if (std::holds_alternative<O>(_sv.v())) {
      return Nat(O{});
    } else {
      const auto &[d_a0] = std::get<S>(_sv.v());
      return Nat(S{clone_value(d_a0)});
    }
  }

  // CREATORS
  __attribute__((pure)) static Nat o() { return Nat(O{}); }

  __attribute__((pure)) static Nat s(const Nat &a0) {
    return Nat(S{std::make_unique<Nat>(a0)});
  }

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) Nat *operator->() { return this; }

  __attribute__((pure)) const Nat *operator->() const { return this; }

  __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

  __attribute__((pure)) bool operator==(std::nullptr_t) const { return false; }

  // MANIPULATORS
  void reset() { *this = Nat(); }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }

  __attribute__((pure)) Nat add(Nat m) const {
    auto &&_sv = *(this);
    if (std::holds_alternative<typename Nat::O>(_sv.v())) {
      return m;
    } else {
      const auto &[d_a0] = std::get<typename Nat::S>(_sv.v());
      return Nat::s((*(d_a0)).add(m));
    }
  }
};

struct RocqBug13581 {
  template <typename t_T0> struct mixin_of {
    std::function<t_T0(t_T0)> mixin_f;

    __attribute__((pure)) mixin_of<t_T0> *operator->() { return this; }

    __attribute__((pure)) const mixin_of<t_T0> *operator->() const {
      return this;
    }

    // ACCESSORS
    __attribute__((pure)) mixin_of<t_T0> clone() const {
      return mixin_of<t_T0>{(*(this)).mixin_f};
    }
  };

  static inline const mixin_of<Nat> d =
      mixin_of<Nat>{[](Nat x0) { return x0; }};

  template <typename t_T0> struct R {
    std::function<t_T0(t_T0)> g;
    Nat x;

    __attribute__((pure)) R<t_T0> *operator->() { return this; }

    __attribute__((pure)) const R<t_T0> *operator->() const { return this; }

    // ACCESSORS
    __attribute__((pure)) R<t_T0> clone() const {
      return R<t_T0>{(*(this)).g, (*(this)).x};
    }
  };

  template <typename T1>
  __attribute__((pure)) static Nat y(const Nat &, const Nat &,
                                     const R<T1> &r0) {
    return r0.x.add(r0.x);
  }

  static inline const R<Nat> r = R<Nat>{[](Nat x0) { return x0; }, Nat::o()};
  template <typename t_T> struct I;
  template <typename t_T> struct J;

  template <typename t_T> struct I {
    // TYPES
    struct C {};

    struct D {
      std::unique_ptr<J<t_T>> d_a0;
    };

    using variant_t = std::variant<C, D>;
    using crane_element_type = t_T;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    I() {}

    explicit I(C _v) : d_v_(_v) {}

    explicit I(D _v) : d_v_(std::move(_v)) {}

    I(const I<t_T> &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    I(I<t_T> &&_other) : d_v_(std::move(_other.d_v_)) {}

    __attribute__((pure)) I<t_T> &operator=(const I<t_T> &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    __attribute__((pure)) I<t_T> &operator=(I<t_T> &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) I<t_T> clone() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<C>(_sv.v())) {
        return I<t_T>(C{});
      } else {
        const auto &[d_a0] = std::get<D>(_sv.v());
        return I<t_T>(D{clone_value(d_a0)});
      }
    }

    // CREATORS
    template <typename _U> explicit I(const I<_U> &_other) {
      if (std::holds_alternative<typename I<_U>::C>(_other.v())) {
        d_v_ = C{};
      } else {
        const auto &[d_a0] = std::get<typename I<_U>::D>(_other.v());
        d_v_ =
            D{d_a0 ? std::make_unique<RocqBug13581::J<t_T>>(*d_a0) : nullptr};
      }
    }

    __attribute__((pure)) static I<t_T> c() { return I(C{}); }

    __attribute__((pure)) static I<t_T> d(const J<t_T> &a0) {
      return I(D{std::make_unique<J<t_T>>(a0)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) I<t_T> *operator->() { return this; }

    __attribute__((pure)) const I<t_T> *operator->() const { return this; }

    __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

    __attribute__((pure)) bool operator==(std::nullptr_t) const {
      return false;
    }

    // MANIPULATORS
    void reset() { *this = I<t_T>(); }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename t_T> struct J {
    // TYPES
    struct E {
      std::unique_ptr<I<t_T>> d_a0;
    };

    using variant_t = std::variant<E>;
    using crane_element_type = t_T;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    J() {}

    explicit J(E _v) : d_v_(std::move(_v)) {}

    J(const J<t_T> &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    J(J<t_T> &&_other) : d_v_(std::move(_other.d_v_)) {}

    __attribute__((pure)) J<t_T> &operator=(const J<t_T> &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    __attribute__((pure)) J<t_T> &operator=(J<t_T> &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) J<t_T> clone() const {
      auto &&_sv = *(this);
      const auto &[d_a0] = std::get<E>(_sv.v());
      return J<t_T>(E{clone_value(d_a0)});
    }

    // CREATORS
    template <typename _U> explicit J(const J<_U> &_other) {
      const auto &[d_a0] = std::get<typename J<_U>::E>(_other.v());
      d_v_ = E{d_a0 ? std::make_unique<RocqBug13581::I<t_T>>(*d_a0) : nullptr};
    }

    __attribute__((pure)) static J<t_T> e(const I<t_T> &a0) {
      return J(E{std::make_unique<I<t_T>>(a0)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) J<t_T> *operator->() { return this; }

    __attribute__((pure)) const J<t_T> *operator->() const { return this; }

    __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

    __attribute__((pure)) bool operator==(std::nullptr_t) const {
      return false;
    }

    // MANIPULATORS
    void reset() { *this = J<t_T>(); }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, typename T2, MapsTo<T2, J<T1>> F3>
  static T2 I_rect(const T1, const T1, const T2 f, F3 &&f0, const Nat &,
                   const I<T1> &i) {
    if (std::holds_alternative<typename I<T1>::C>(i.v())) {
      return f;
    } else {
      const auto &[d_a0] = std::get<typename I<T1>::D>(i.v());
      return f0(*(d_a0));
    }
  }

  template <typename T1, typename T2, MapsTo<T2, J<T1>> F3>
  static T2 I_rec(const T1, const T1, const T2 f, F3 &&f0, const Nat &,
                  const I<T1> &i) {
    if (std::holds_alternative<typename I<T1>::C>(i.v())) {
      return f;
    } else {
      const auto &[d_a0] = std::get<typename I<T1>::D>(i.v());
      return f0(*(d_a0));
    }
  }

  template <typename T1, typename T2, MapsTo<T2, I<T1>> F2>
  static T2 J_rect(const T1, const T1, F2 &&f, const Bool0, const J<T1> &j) {
    const auto &[d_a0] = std::get<typename J<T1>::E>(j.v());
    return f(*(d_a0));
  }

  template <typename T1, typename T2, MapsTo<T2, I<T1>> F2>
  static T2 J_rec(const T1, const T1, F2 &&f, const Bool0, const J<T1> &j) {
    const auto &[d_a0] = std::get<typename J<T1>::E>(j.v());
    return f(*(d_a0));
  }

  static inline const I<Nat> c = I<Nat>::d(J<Nat>::e(I<Nat>::c()));
};

#endif // INCLUDED_ROCQ_BUG_13581
