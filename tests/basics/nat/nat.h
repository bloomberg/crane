#include <functional>
#include <iostream>
#include <memory>
#include <string>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

struct Nat {
  struct Nat {
    struct O;
    struct S;
    using nat = std::variant<O, S>;
    struct O {
      static std::shared_ptr<nat> make();
    };
    struct S {
      std::shared_ptr<nat> _a0;
      static std::shared_ptr<nat> make(std::shared_ptr<nat> _a0);
    };
  };

  template <typename T1, MapsTo<T1, std::shared_ptr<typename Nat::nat>, T1> F1>
  T1 nat_rect(const T1 f, F1 &&f0, const std::shared_ptr<typename Nat::nat> n) {
    return std::visit(
        Overloaded{[&](const typename Nat::O _args) -> T1 { return f; },
                   [&](const typename Nat::S _args) -> T1 {
                     std::shared_ptr<typename Nat::nat> n0 = _args._a0;
                     return f0(n0, nat_rect<T1>(f, f0, n0));
                   }},
        *n);
  }

  template <typename T1, MapsTo<T1, std::shared_ptr<typename Nat::nat>, T1> F1>
  T1 nat_rec(const T1 f, F1 &&f0, const std::shared_ptr<typename Nat::nat> n) {
    return std::visit(
        Overloaded{[&](const typename Nat::O _args) -> T1 { return f; },
                   [&](const typename Nat::S _args) -> T1 {
                     std::shared_ptr<typename Nat::nat> n0 = _args._a0;
                     return f0(n0, nat_rec<T1>(f, f0, n0));
                   }},
        *n);
  }

  static std::shared_ptr<typename Nat::nat>
  add(const std::shared_ptr<typename Nat::nat> m,
      const std::shared_ptr<typename Nat::nat> n);

  static int nat_to_int(const std::shared_ptr<typename Nat::nat> n);
};
