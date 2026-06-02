#ifndef INCLUDED_ROCQ_BUG_13581
#define INCLUDED_ROCQ_BUG_13581

#include <functional>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

enum class Unit { TT };
enum class Bool0 { TRUE_, FALSE_ };

struct Nat {
  // TYPES
  struct O {};

  struct S {
    std::shared_ptr<Nat> a0;
  };

  using variant_t = std::variant<O, S>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  Nat() {}

  explicit Nat(O _v) : v_(_v) {}

  explicit Nat(S _v) : v_(std::move(_v)) {}

  static Nat o() { return Nat(O{}); }

  static Nat s(Nat a0) { return Nat(S{std::make_shared<Nat>(std::move(a0))}); }

  // MANIPULATORS
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

  Nat add(Nat m) const {
    if (std::holds_alternative<typename Nat::O>(this->v())) {
      return m;
    } else {
      const auto &[a0] = std::get<typename Nat::S>(this->v());
      return Nat::s(a0->add(std::move(m)));
    }
  }
};

struct RocqBug13581 {
  template <typename T0> struct mixin_of {
    std::function<T0(T0)> mixin_f;
  };

  static inline const mixin_of<Nat> d =
      mixin_of<Nat>{[](Nat x0) { return x0; }};

  template <typename T0> struct R {
    std::function<T0(T0)> g;
    Nat x;
  };

  template <typename T1>
  static Nat y(const Nat &, const Nat &, const R<T1> &r0) {
    return r0.x.add(r0.x);
  }

  static inline const R<Nat> r = R<Nat>{[](Nat x0) { return x0; }, Nat::o()};
  template <typename T> struct I;
  template <typename T> struct J;

  template <typename T> struct I {
    // TYPES
    struct C {};

    struct D {
      std::shared_ptr<J<T>> a0;
    };

    using variant_t = std::variant<C, D>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    I() {}

    explicit I(C _v) : v_(_v) {}

    explicit I(D _v) : v_(std::move(_v)) {}

    template <typename _U> explicit I(const I<_U> &_other) {
      if (std::holds_alternative<typename I<_U>::C>(_other.v())) {
        this->v_ = C{};
      } else {
        const auto &[a0] = std::get<typename I<_U>::D>(_other.v());
        this->v_ = D{a0 ? std::make_shared<RocqBug13581::J<T>>(*a0) : nullptr};
      }
    }

    static I<T> c() { return I(C{}); }

    static I<T> d(J<T> a0) {
      return I(D{std::make_shared<J<T>>(std::move(a0))});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T> struct J {
    // TYPES
    struct E {
      std::shared_ptr<I<T>> a0;
    };

    using variant_t = std::variant<E>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    J() {}

    explicit J(E _v) : v_(std::move(_v)) {}

    template <typename _U> explicit J(const J<_U> &_other) {
      const auto &[a0] = std::get<typename J<_U>::E>(_other.v());
      this->v_ = E{a0 ? std::make_shared<RocqBug13581::I<T>>(*a0) : nullptr};
    }

    static J<T> e(I<T> a0) {
      return J(E{std::make_shared<I<T>>(std::move(a0))});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename T2, typename F3>
    requires std::is_invocable_r_v<T2, F3 &, J<T1> &>
  static T2 I_rect(const T1 &, const T1 &, T2 f, F3 &&f0, const Nat &,
                   const I<T1> &i) {
    if (std::holds_alternative<typename I<T1>::C>(i.v())) {
      return f;
    } else {
      const auto &[a0] = std::get<typename I<T1>::D>(i.v());
      return f0(*a0);
    }
  }

  template <typename T1, typename T2, typename F3>
    requires std::is_invocable_r_v<T2, F3 &, J<T1> &>
  static T2 I_rec(const T1 &, const T1 &, T2 f, F3 &&f0, const Nat &,
                  const I<T1> &i) {
    if (std::holds_alternative<typename I<T1>::C>(i.v())) {
      return f;
    } else {
      const auto &[a0] = std::get<typename I<T1>::D>(i.v());
      return f0(*a0);
    }
  }

  template <typename T1, typename T2, typename F2>
    requires std::is_invocable_r_v<T2, F2 &, I<T1> &>
  static T2 J_rect(const T1 &, const T1 &, F2 &&f, Bool0, const J<T1> &j) {
    const auto &[a0] = std::get<typename J<T1>::E>(j.v());
    return f(*a0);
  }

  template <typename T1, typename T2, typename F2>
    requires std::is_invocable_r_v<T2, F2 &, I<T1> &>
  static T2 J_rec(const T1 &, const T1 &, F2 &&f, Bool0, const J<T1> &j) {
    const auto &[a0] = std::get<typename J<T1>::E>(j.v());
    return f(*a0);
  }

  static inline const I<Nat> c = I<Nat>::d(J<Nat>::e(I<Nat>::c()));
};

#endif // INCLUDED_ROCQ_BUG_13581
