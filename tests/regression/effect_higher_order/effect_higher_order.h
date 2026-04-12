#ifndef INCLUDED_EFFECT_HIGHER_ORDER
#define INCLUDED_EFFECT_HIGHER_ORDER

#include <cstdlib>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <string>
#include <type_traits>
#include <utility>
#include <variant>

using namespace std::string_literals;
template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

template <typename t_A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    t_A d_a0;
    std::shared_ptr<List<t_A>> d_a1;
  };

  using variant_t = std::variant<Nil, Cons>;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  explicit List(Nil _v) : d_v_(_v) {}

  explicit List(Cons _v) : d_v_(std::move(_v)) {}

  static std::shared_ptr<List<t_A>> nil() {
    return std::make_shared<List<t_A>>(Nil{});
  }

  static std::shared_ptr<List<t_A>> cons(t_A a0,
                                         const std::shared_ptr<List<t_A>> &a1) {
    return std::make_shared<List<t_A>>(Cons{std::move(a0), a1});
  }

  static std::shared_ptr<List<t_A>> cons(t_A a0,
                                         std::shared_ptr<List<t_A>> &&a1) {
    return std::make_shared<List<t_A>>(Cons{std::move(a0), std::move(a1)});
  }

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }
};

struct EffectHigherOrder {
  /// 1. Higher-order function with effectful callback
  template <MapsTo<void, std::string> F0>
  static void apply_effect(F0 &&f, const std::string _x0) {
    f(_x0);
    return;
  }

  /// 2. Map-like function over a list with effects
  template <MapsTo<void, std::string> F0>
  static void for_each_str(F0 &&f,
                           const std::shared_ptr<List<std::string>> &xs) {
    {
      std::visit(Overloaded{[](const typename List<std::string>::Nil &)
                                -> std::monostate { return std::monostate{}; },
                            [&](const typename List<std::string>::Cons &_args)
                                -> std::monostate {
                              f(_args.d_a0);
                              for_each_str(f, _args.d_a1);
                              return std::monostate{};
                            }},
                 xs->v());
      return;
    }
  } /// 3. Callback that returns a value

  template <typename F0> static std::string with_line(F0 &&f) {
    std::string _bind_result = []() -> std::string {
      std::string _r;
      std::getline(std::cin, _r);
      return _r;
    }();
    return f(_bind_result);
  }

  /// 4. Nested bind in callback
  template <MapsTo<std::string, std::string> F0>
  static std::string transform_input(F0 &&f) {
    std::string line;
    std::getline(std::cin, line);
    return f(line);
  }

  /// 5. Effectful callback passed as argument
  static void greet_all(const std::shared_ptr<List<std::string>> &names);
  /// 6. Callback with env effect
  static std::string lookup_or_ask(const std::string name);
  /// 7. Chain of lookups
  static std::shared_ptr<List<std::string>>
  lookup_all(const std::shared_ptr<List<std::string>> &names);

  /// 8. Effect in let-bound function
  static std::string process_input();
};

#endif // INCLUDED_EFFECT_HIGHER_ORDER
