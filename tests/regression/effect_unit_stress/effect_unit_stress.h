#ifndef INCLUDED_EFFECT_UNIT_STRESS
#define INCLUDED_EFFECT_UNIT_STRESS

#include <any>
#include <cstdint>
#include <filesystem>
#include <fstream>
#include <iostream>
#include <memory>
#include <optional>
#include <string>
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

struct EffectUnitStress {
  /// 1. Ret tt at different nesting depths
  static void ret_tt_simple();
  static void ret_tt_after_bind();
  static void ret_tt_after_effect();
  /// 2. Bind where RHS is Ret of the LHS binding
  static std::string bind_identity();
  /// 3. Bind where RHS ignores the binding
  static uint64_t bind_ignore();
  /// 4. Multiple Ret tt in if-then-else
  static void conditional_tt(bool b);
  /// 5. Ret in one branch, effect in other
  static void conditional_mixed(bool b);
  /// 6. Tuple of monadic results
  static std::pair<std::string, std::string> pair_of_effects();
  /// 7. match on nat with monadic body
  static std::string nat_dispatch(uint64_t n);
  /// 8. let in monadic context with pure computation
  static int64_t let_pure_in_monadic();
  /// 9. Nested if in monadic context
  static std::string nested_if_monadic(bool b1, bool b2);
  /// 10. Monadic function returning option
  static std::optional<uint64_t> safe_head(const List<uint64_t> &xs);
};

#endif // INCLUDED_EFFECT_UNIT_STRESS
