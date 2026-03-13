#ifndef INCLUDED_NAT
#define INCLUDED_NAT

#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

struct Nat {
  /// Peano natural numbers: O is zero and S n is the successor of n.
  struct nat {
    // TYPES
    struct O {};

    struct S {
      std::shared_ptr<nat> d_a0;
    };

    using variant_t = std::variant<O, S>;

  private:
    // DATA
    variant_t d_v_;

    // CREATORS
    explicit nat(O _v) : d_v_(std::move(_v)) {}

    explicit nat(S _v) : d_v_(std::move(_v)) {}

  public:
    // TYPES
    struct ctor {
      ctor() = delete;

      static std::shared_ptr<nat> O_() {
        return std::shared_ptr<nat>(new nat(O{}));
      }

      static std::shared_ptr<nat> S_(const std::shared_ptr<nat> &a0) {
        return std::shared_ptr<nat>(new nat(S{a0}));
      }

      static std::unique_ptr<nat> O_uptr() {
        return std::unique_ptr<nat>(new nat(O{}));
      }

      static std::unique_ptr<nat> S_uptr(const std::shared_ptr<nat> &a0) {
        return std::unique_ptr<nat>(new nat(S{a0}));
      }
    };

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    /// Convert a Peano nat to a machine int.
    __attribute__((pure)) int nat_to_int() const {
      return std::visit(
          Overloaded{[](const typename nat::O _args) -> int { return 0; },
                     [](const typename nat::S _args) -> int {
                       std::shared_ptr<nat> n_ = _args.d_a0;
                       return 1 + std::move(n_)->nat_to_int();
                     }},
          this->v());
    }

    template <typename T1, MapsTo<T1, std::shared_ptr<nat>, T1> F1>
    T1 nat_rec(const T1 f, F1 &&f0) const {
      return std::visit(
          Overloaded{[&](const typename nat::O _args) -> T1 { return f; },
                     [&](const typename nat::S _args) -> T1 {
                       std::shared_ptr<nat> n0 = _args.d_a0;
                       return f0(n0, n0->template nat_rec<T1>(f, f0));
                     }},
          this->v());
    }

    template <typename T1, MapsTo<T1, std::shared_ptr<nat>, T1> F1>
    T1 nat_rect(const T1 f, F1 &&f0) const {
      return std::visit(
          Overloaded{[&](const typename nat::O _args) -> T1 { return f; },
                     [&](const typename nat::S _args) -> T1 {
                       std::shared_ptr<nat> n0 = _args.d_a0;
                       return f0(n0, n0->template nat_rect<T1>(f, f0));
                     }},
          this->v());
    }

    /// add m n computes the sum of m and n by recursion on m.
    std::shared_ptr<nat> add(std::shared_ptr<nat> n) const {
      return std::visit(
          Overloaded{[&](const typename nat::O _args) -> std::shared_ptr<nat> {
                       return n;
                     },
                     [&](const typename nat::S _args) -> std::shared_ptr<nat> {
                       std::shared_ptr<nat> x = _args.d_a0;
                       return nat::ctor::S_(std::move(x)->add(n));
                     }},
          this->v());
    }
  };
};

#endif // INCLUDED_NAT
