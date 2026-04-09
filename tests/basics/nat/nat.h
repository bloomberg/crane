#ifndef INCLUDED_NAT
#define INCLUDED_NAT

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

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
  explicit Nat(O _v) : d_v_(std::move(_v)) {}

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

  /// Convert a Peano nat to a machine int.
  __attribute__((pure)) int nat_to_int() const {
    return std::visit(
        Overloaded{[](const typename Nat::O _args) -> int { return 0; },
                   [](const typename Nat::S _args) -> int {
                     return 1 + _args.d_n->nat_to_int();
                   }},
        this->v());
  }

  template <typename T1, MapsTo<T1, std::shared_ptr<Nat>, T1> F1>
  T1 nat_rec(const T1 f, F1 &&f0) const {
    return std::visit(
        Overloaded{[&](const typename Nat::O _args) -> T1 { return f; },
                   [&](const typename Nat::S _args) -> T1 {
                     return f0(_args.d_n,
                               _args.d_n->template nat_rec<T1>(f, f0));
                   }},
        this->v());
  }

  template <typename T1, MapsTo<T1, std::shared_ptr<Nat>, T1> F1>
  T1 nat_rect(const T1 f, F1 &&f0) const {
    return std::visit(
        Overloaded{[&](const typename Nat::O _args) -> T1 { return f; },
                   [&](const typename Nat::S _args) -> T1 {
                     return f0(_args.d_n,
                               _args.d_n->template nat_rect<T1>(f, f0));
                   }},
        this->v());
  }

  /// add m n computes the sum of m and n by recursion on m.
  std::shared_ptr<Nat> add(std::shared_ptr<Nat> n) const {
    return std::visit(
        Overloaded{[&](const typename Nat::O _args) -> std::shared_ptr<Nat> {
                     return n;
                   },
                   [&](const typename Nat::S _args) -> std::shared_ptr<Nat> {
                     return Nat::s(_args.d_n->add(n));
                   }},
        this->v());
  }
};

#endif // INCLUDED_NAT
