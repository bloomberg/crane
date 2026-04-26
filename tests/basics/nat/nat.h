#ifndef INCLUDED_NAT
#define INCLUDED_NAT

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

struct Nat {
  /// Peano natural numbers: O is zero and S n is the successor of n.
  // TYPES
  struct O {};

  struct S {
    std::unique_ptr<Nat> d_n;
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
      const auto &[d_n] = std::get<S>(_sv.v());
      return Nat(S{clone_value(d_n)});
    }
  }

  // CREATORS
  __attribute__((pure)) static Nat o() { return Nat(O{}); }

  __attribute__((pure)) static Nat s(const Nat &n) {
    return Nat(S{std::make_unique<Nat>(n)});
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

  template <typename T1, MapsTo<T1, Nat, T1> F1>
  T1 nat_rect(const T1 f, F1 &&f0) const {
    auto &&_sv = *(this);
    if (std::holds_alternative<typename Nat::O>(_sv.v())) {
      return f;
    } else {
      const auto &[d_n] = std::get<typename Nat::S>(_sv.v());
      return f0(*(d_n), (*(d_n)).template nat_rect<T1>(f, f0));
    }
  }

  template <typename T1, MapsTo<T1, Nat, T1> F1>
  T1 nat_rec(const T1 f, F1 &&f0) const {
    auto &&_sv = *(this);
    if (std::holds_alternative<typename Nat::O>(_sv.v())) {
      return f;
    } else {
      const auto &[d_n] = std::get<typename Nat::S>(_sv.v());
      return f0(*(d_n), (*(d_n)).template nat_rec<T1>(f, f0));
    }
  }

  /// add m n computes the sum of m and n by recursion on m.
  __attribute__((pure)) Nat add(Nat n) const {
    auto &&_sv = *(this);
    if (std::holds_alternative<typename Nat::O>(_sv.v())) {
      return n;
    } else {
      const auto &[d_n] = std::get<typename Nat::S>(_sv.v());
      return Nat::s((*(d_n)).add(n));
    }
  }

  /// Convert a Peano nat to a machine int.
  __attribute__((pure)) int nat_to_int() const {
    auto &&_sv = *(this);
    if (std::holds_alternative<typename Nat::O>(_sv.v())) {
      return 0;
    } else {
      const auto &[d_n] = std::get<typename Nat::S>(_sv.v());
      return 1 + (*(d_n)).nat_to_int();
    }
  }
};

#endif // INCLUDED_NAT
