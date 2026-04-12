#ifndef INCLUDED_EFFECT_RECURSIVE_LIST
#define INCLUDED_EFFECT_RECURSIVE_LIST

#include <cstdlib>
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
  explicit List(Nil _v) : d_v_(std::move(_v)) {}

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

struct EffectRecursiveList {
  /// 1. Recursive function building a list from stdin lines
  static std::shared_ptr<List<std::string>> read_n_lines(const unsigned int n);

  /// 2. Map a function over a list with effects
  template <MapsTo<void, std::string> F0>
  static void map_effect(F0 &&f, const std::shared_ptr<List<std::string>> &xs) {
    {
      std::visit(Overloaded{[](const typename List<std::string>::Nil &)
                                -> std::monostate { return std::monostate{}; },
                            [&](const typename List<std::string>::Cons &_args)
                                -> std::monostate {
                              f(_args.d_a0);
                              map_effect(f, _args.d_a1);
                              return std::monostate{};
                            }},
                 xs->v());
      return;
    }
  }

  /// 3. Fold a list with effects, accumulating a result
  static std::string fold_effect(const std::shared_ptr<List<std::string>> &xs,
                                 const std::string acc);
  /// 4. Read lines and store each in env with index
  static unsigned int store_lines(const std::string prefix,
                                  const unsigned int n);
  /// 5. Collect env values into a list
  static std::shared_ptr<List<std::optional<std::string>>>
  collect_envs(const std::shared_ptr<List<std::string>> &names);

  /// 6. Read a line and prepend to existing list
  static std::shared_ptr<List<std::string>>
  read_and_prepend(std::shared_ptr<List<std::string>> xs);
};

#endif // INCLUDED_EFFECT_RECURSIVE_LIST
