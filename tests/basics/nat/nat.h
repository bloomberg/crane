#ifndef INCLUDED_NAT
#define INCLUDED_NAT

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

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
      return Nat(S{d_n ? std::make_unique<Nat>(d_n->clone()) : nullptr});
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
