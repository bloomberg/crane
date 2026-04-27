#ifndef INCLUDED_TUPLE
#define INCLUDED_TUPLE

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

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
      return Nat(S{d_a0 ? std::make_unique<Nat>(d_a0->clone()) : nullptr});
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
};

template <typename t_A, typename t_B> struct Prod {
  // TYPES
  struct Pair {
    t_A d_a0;
    t_B d_a1;
  };

  using variant_t = std::variant<Pair>;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  Prod() {}

  explicit Prod(Pair _v) : d_v_(std::move(_v)) {}

  Prod(const Prod<t_A, t_B> &_other) : d_v_(std::move(_other.clone().d_v_)) {}

  Prod(Prod<t_A, t_B> &&_other) : d_v_(std::move(_other.d_v_)) {}

  __attribute__((pure)) Prod<t_A, t_B> &
  operator=(const Prod<t_A, t_B> &_other) {
    d_v_ = std::move(_other.clone().d_v_);
    return *this;
  }

  __attribute__((pure)) Prod<t_A, t_B> &operator=(Prod<t_A, t_B> &&_other) {
    d_v_ = std::move(_other.d_v_);
    return *this;
  }

  // ACCESSORS
  __attribute__((pure)) Prod<t_A, t_B> clone() const {
    auto &&_sv = *(this);
    const auto &[d_a0, d_a1] = std::get<Pair>(_sv.v());
    return Prod<t_A, t_B>(Pair{d_a0, d_a1});
  }

  // CREATORS
  template <typename _U0, typename _U1>
  explicit Prod(const Prod<_U0, _U1> &_other) {
    const auto &[d_a0, d_a1] =
        std::get<typename Prod<_U0, _U1>::Pair>(_other.v());
    d_v_ = Pair{t_A(d_a0), t_B(d_a1)};
  }

  __attribute__((pure)) static Prod<t_A, t_B> pair(t_A a0, t_B a1) {
    return Prod(Pair{std::move(a0), std::move(a1)});
  }

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) Prod<t_A, t_B> *operator->() { return this; }

  __attribute__((pure)) const Prod<t_A, t_B> *operator->() const {
    return this;
  }

  __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

  __attribute__((pure)) bool operator==(std::nullptr_t) const { return false; }

  // MANIPULATORS
  void reset() { *this = Prod<t_A, t_B>(); }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }
};

struct Tuple {
  template <typename a, typename b> using pair = Prod<a, b>;

  template <typename T1, typename T2>
  __attribute__((pure)) static Prod<T1, T2> make_pair(const T1 a, const T2 b) {
    return Prod<T1, T2>::pair(a, b);
  }

  template <typename T1, typename T2> static T1 fst(const Prod<T1, T2> &p) {
    const auto &[d_a0, d_a1] = std::get<typename Prod<T1, T2>::Pair>(p.v());
    return d_a0;
  }

  template <typename T1, typename T2> static T2 snd(const Prod<T1, T2> &p) {
    const auto &[d_a0, d_a1] = std::get<typename Prod<T1, T2>::Pair>(p.v());
    return d_a1;
  }

  template <typename T1, typename T2>
  constexpr static Prod<T2, T1> swap(const Prod<T1, T2> &p) {
    const auto &[d_a0, d_a1] = std::get<typename Prod<T1, T2>::Pair>(p.v());
    return Prod<T2, T1>::pair(d_a1, d_a0);
  }

  static inline const Prod<Nat, Nat> test_pair =
      make_pair<Nat, Nat>(Nat::s(Nat::o()), Nat::s(Nat::s(Nat::o())));
  static inline const Nat test_fst = fst<Nat, Nat>(test_pair);
  static inline const Prod<Nat, Nat> test_swap = swap<Nat, Nat>(test_pair);
};

#endif // INCLUDED_TUPLE
