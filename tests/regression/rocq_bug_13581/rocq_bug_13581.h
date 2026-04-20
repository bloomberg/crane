#ifndef INCLUDED_ROCQ_BUG_13581
#define INCLUDED_ROCQ_BUG_13581

#include <functional>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

enum class Unit { e_TT };
enum class Bool0 { e_TRUE0, e_FALSE0 };

struct Nat {
  // TYPES
  struct O {};

  struct S {
    std::shared_ptr<Nat> d_a0;
  };

  using variant_t = std::variant<O, S>;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  explicit Nat(O _v) : d_v_(_v) {}

  explicit Nat(S _v) : d_v_(std::move(_v)) {}

  static std::shared_ptr<Nat> o() { return std::make_shared<Nat>(O{}); }

  static std::shared_ptr<Nat> s(const std::shared_ptr<Nat> &a0) {
    return std::make_shared<Nat>(S{a0});
  }

  static std::shared_ptr<Nat> s(std::shared_ptr<Nat> &&a0) {
    return std::make_shared<Nat>(S{std::move(a0)});
  }

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }

  std::shared_ptr<Nat> add(std::shared_ptr<Nat> m) const {
    if (std::holds_alternative<typename Nat::O>(this->v())) {
      return m;
    } else {
      const auto &[d_a0] = std::get<typename Nat::S>(this->v());
      return Nat::s(d_a0->add(m));
    }
  }
};

struct RocqBug13581 {
  template <typename t_T0> struct mixin_of {
    std::function<t_T0(t_T0)> mixin_f;
  };

  static inline const std::shared_ptr<mixin_of<std::shared_ptr<Nat>>> d =
      std::make_shared<mixin_of<std::shared_ptr<Nat>>>(
          mixin_of<std::shared_ptr<Nat>>{
              [](std::shared_ptr<Nat> x0) { return x0; }});

  template <typename t_T0> struct R {
    std::function<t_T0(t_T0)> g;
    std::shared_ptr<Nat> x;
  };

  template <typename T1>
  static std::shared_ptr<Nat> y(const std::shared_ptr<Nat> &,
                                const std::shared_ptr<Nat> &,
                                const std::shared_ptr<R<T1>> &r0) {
    return r0->x->add(r0->x);
  }

  static inline const std::shared_ptr<R<std::shared_ptr<Nat>>> r =
      std::make_shared<R<std::shared_ptr<Nat>>>(R<std::shared_ptr<Nat>>{
          [](std::shared_ptr<Nat> x0) { return x0; }, Nat::o()});
  template <typename t_T> struct I;
  template <typename t_T> struct J;

  template <typename t_T> struct I {
    // TYPES
    struct C {};

    struct D {
      std::shared_ptr<J<t_T>> d_a0;
    };

    using variant_t = std::variant<C, D>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    explicit I(C _v) : d_v_(_v) {}

    explicit I(D _v) : d_v_(std::move(_v)) {}

    static std::shared_ptr<I<t_T>> c() { return std::make_shared<I<t_T>>(C{}); }

    static std::shared_ptr<I<t_T>> d(const std::shared_ptr<J<t_T>> &a0) {
      return std::make_shared<I<t_T>>(D{a0});
    }

    static std::shared_ptr<I<t_T>> d(std::shared_ptr<J<t_T>> &&a0) {
      return std::make_shared<I<t_T>>(D{std::move(a0)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename t_T> struct J {
    // TYPES
    struct E {
      std::shared_ptr<I<t_T>> d_a0;
    };

    using variant_t = std::variant<E>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    explicit J(E _v) : d_v_(std::move(_v)) {}

    static std::shared_ptr<J<t_T>> e(const std::shared_ptr<I<t_T>> &a0) {
      return std::make_shared<J<t_T>>(E{a0});
    }

    static std::shared_ptr<J<t_T>> e(std::shared_ptr<I<t_T>> &&a0) {
      return std::make_shared<J<t_T>>(E{std::move(a0)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, typename T2, MapsTo<T2, std::shared_ptr<J<T1>>> F3>
  static T2 I_rect(const T1, const T1, const T2 f, F3 &&f0,
                   const std::shared_ptr<Nat> &,
                   const std::shared_ptr<I<T1>> &i) {
    if (std::holds_alternative<typename I<T1>::C>(i->v())) {
      return f;
    } else {
      const auto &[d_a0] = std::get<typename I<T1>::D>(i->v());
      return f0(d_a0);
    }
  }

  template <typename T1, typename T2, MapsTo<T2, std::shared_ptr<J<T1>>> F3>
  static T2 I_rec(const T1, const T1, const T2 f, F3 &&f0,
                  const std::shared_ptr<Nat> &,
                  const std::shared_ptr<I<T1>> &i) {
    if (std::holds_alternative<typename I<T1>::C>(i->v())) {
      return f;
    } else {
      const auto &[d_a0] = std::get<typename I<T1>::D>(i->v());
      return f0(d_a0);
    }
  }

  template <typename T1, typename T2, MapsTo<T2, std::shared_ptr<I<T1>>> F2>
  static T2 J_rect(const T1, const T1, F2 &&f, const Bool0,
                   const std::shared_ptr<J<T1>> &j) {
    const auto &[d_a0] = std::get<typename J<T1>::E>(j->v());
    return f(d_a0);
  }

  template <typename T1, typename T2, MapsTo<T2, std::shared_ptr<I<T1>>> F2>
  static T2 J_rec(const T1, const T1, F2 &&f, const Bool0,
                  const std::shared_ptr<J<T1>> &j) {
    const auto &[d_a0] = std::get<typename J<T1>::E>(j->v());
    return f(d_a0);
  }

  static inline const std::shared_ptr<I<std::shared_ptr<Nat>>> c =
      I<std::shared_ptr<Nat>>::d(
          J<std::shared_ptr<Nat>>::e(I<std::shared_ptr<Nat>>::c()));
};

#endif // INCLUDED_ROCQ_BUG_13581
