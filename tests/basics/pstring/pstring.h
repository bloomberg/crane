#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <string>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

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

struct List {
  template <typename A> struct nil;
  template <typename A> struct cons;
  template <typename A> using list = std::variant<nil<A>, cons<A>>;
  template <typename A> struct nil {
    static std::shared_ptr<list<A>> make() {
      return std::make_shared<list<A>>(nil<A>{});
    }
  };
  template <typename A> struct cons {
    A _a0;
    std::shared_ptr<list<A>> _a1;
    static std::shared_ptr<list<A>> make(A _a0, std::shared_ptr<list<A>> _a1) {
      return std::make_shared<list<A>>(cons<A>{_a0, _a1});
    }
  };
};

struct PString {
  static std::string nat_to_string(const std::shared_ptr<typename Nat::nat> n);

  static int nat_to_int(const std::shared_ptr<typename Nat::nat> n);

  template <typename T1, MapsTo<std::string, T1> F0>
  std::string list_to_string(F0 &&p,
                             const std::shared_ptr<typename List::list<T1>> l) {
    return std::visit(
        Overloaded{[&](const typename List::nil<T1> _args) -> std::string {
                     return "[]";
                   },
                   [&](const typename List::cons<T1> _args) -> std::string {
                     T1 y = _args._a0;
                     std::shared_ptr<typename List::list<T1>> l_ = _args._a1;
                     return p(y) + "::" + list_to_string<T1>(p, l_);
                   }},
        *l);
  }
};
