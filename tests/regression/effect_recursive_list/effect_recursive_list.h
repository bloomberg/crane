#ifndef INCLUDED_EFFECT_RECURSIVE_LIST
#define INCLUDED_EFFECT_RECURSIVE_LIST

#include <any>
#include <cstdlib>
#include <iostream>
#include <memory>
#include <optional>
#include <string>
#include <type_traits>
#include <utility>
#include <variant>

using namespace std::string_literals;

template <typename A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    A a;
    std::shared_ptr<List<A>> l;
  };

  using variant_t = std::variant<Nil, Cons>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  List() {}

  explicit List(Nil _v) : v_(_v) {}

  explicit List(Cons _v) : v_(std::move(_v)) {}

  template <typename _U> explicit List(const List<_U> &_other) {
    if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
      this->v_ = Nil{};
    } else {
      const auto &[a, l] = std::get<typename List<_U>::Cons>(_other.v());
      this->v_ = Cons{
          [&]() -> A {
            if constexpr (std::is_same_v<_U, std::any>) {
              if (a.type() == typeid(A))
                return std::any_cast<A>(a);
              if constexpr (requires {
                              typename A::first_type;
                              typename A::second_type;
                            }) {
                const auto &[_k, _v] =
                    std::any_cast<std::pair<std::any, std::any>>(a);
                return A{[&]() -> typename A::first_type {
                           if constexpr (std::is_same_v<typename A::first_type,
                                                        std::any>)
                             return _k;
                           else
                             return std::any_cast<typename A::first_type>(_k);
                         }(),
                         [&]() -> typename A::second_type {
                           if constexpr (std::is_same_v<typename A::second_type,
                                                        std::any>)
                             return _v;
                           else
                             return std::any_cast<typename A::second_type>(_v);
                         }()};
              }
              return std::any_cast<A>(a);
            } else
              return A(a);
          }(),
          l ? std::make_shared<List<A>>(*l) : nullptr};
    }
  }

  static List<A> nil() { return List(Nil{}); }

  static List<A> cons(A a, List<A> l) {
    return List(Cons{std::move(a), std::make_shared<List<A>>(std::move(l))});
  }

  // MANIPULATORS
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

struct EffectRecursiveList {
  /// 1. Recursive function building a list from stdin lines
  static List<std::string> read_n_lines(uint64_t n);

  /// 2. Map a function over a list with effects
  template <typename F0>
    requires std::is_invocable_r_v<void, F0 &, std::string &>
  static void map_effect(F0 &&f, const List<std::string> &xs) {
    if (std::holds_alternative<typename List<std::string>::Nil>(xs.v())) {
      return;
    } else {
      const auto &[a0, a1] = std::get<typename List<std::string>::Cons>(xs.v());
      f(a0);
      map_effect(f, *a1);
      return;
    }
  }

  /// 3. Fold a list with effects, accumulating a result
  static std::string fold_effect(const List<std::string> &xs, std::string acc);
  /// 4. Read lines and store each in env with index
  static uint64_t store_lines(std::string prefix, uint64_t n);
  /// 5. Collect env values into a list
  static List<std::optional<std::string>>
  collect_envs(const List<std::string> &names);

  /// 6. Read a line and prepend to existing list
  static List<std::string> read_and_prepend(List<std::string> xs);
};

#endif // INCLUDED_EFFECT_RECURSIVE_LIST
