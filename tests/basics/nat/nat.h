#ifndef INCLUDED_NAT
#define INCLUDED_NAT

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

struct Nat {
  /// Peano natural numbers: O is zero and S n is the successor of n.
  // TYPES
  struct O {};

  struct S {
    std::shared_ptr<Nat> d_n;
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

  static std::shared_ptr<Nat> s(const std::shared_ptr<Nat> &n) {
    return std::make_shared<Nat>(S{n});
  }

  static std::shared_ptr<Nat> s(std::shared_ptr<Nat> &&n) {
    return std::make_shared<Nat>(S{std::move(n)});
  }

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }

  template <typename T1, MapsTo<T1, std::shared_ptr<Nat>, T1> F1>
  T1 nat_rect(const T1 f, F1 &&f0) const {
    if (std::holds_alternative<typename Nat::O>(this->v())) {
      return f;
    } else {
      const auto &[d_n] = std::get<typename Nat::S>(this->v());
      return f0(d_n, d_n->template nat_rect<T1>(f, f0));
    }
  }

  template <typename T1, MapsTo<T1, std::shared_ptr<Nat>, T1> F1>
  T1 nat_rec(const T1 f, F1 &&f0) const {
    if (std::holds_alternative<typename Nat::O>(this->v())) {
      return f;
    } else {
      const auto &[d_n] = std::get<typename Nat::S>(this->v());
      return f0(d_n, d_n->template nat_rec<T1>(f, f0));
    }
  }

  /// add m n computes the sum of m and n by recursion on m.
  std::shared_ptr<Nat> add(std::shared_ptr<Nat> n) const {
    if (std::holds_alternative<typename Nat::O>(this->v())) {
      return n;
    } else {
      const auto &[d_n] = std::get<typename Nat::S>(this->v());
      return Nat::s(d_n->add(n));
    }
  }

  /// Convert a Peano nat to a machine int.
  __attribute__((pure)) int nat_to_int() const {
    if (std::holds_alternative<typename Nat::O>(this->v())) {
      return 0;
    } else {
      const auto &[d_n] = std::get<typename Nat::S>(this->v());
      return 1 + d_n->nat_to_int();
    }
  }
};

#endif // INCLUDED_NAT
