#ifndef INCLUDED_MONADIC_VOID_EDGE
#define INCLUDED_MONADIC_VOID_EDGE

#include <any>
#include <filesystem>
#include <fstream>
#include <iostream>
#include <memory>
#include <optional>
#include <string>
#include <system_error>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

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
  ~List() {
    std::vector<std::shared_ptr<List<A>>> _stack = {};
    auto _drain = [&](variant_t &_v) {
      if (auto *_alt = std::get_if<Cons>(&_v)) {
        if (_alt->l) {
          _stack.push_back(std::move(_alt->l));
        }
      }
    };
    _drain(v_mut());
    while (!_stack.empty()) {
      auto _cur = std::move(_stack.back());
      _stack.pop_back();
      if (_cur.use_count() == 1) {
        _drain(_cur->v_mut());
      }
    }
  }

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

struct MonadicVoidEdge {
  /// 1. Bind where LHS is void and RHS returns a value
  static uint64_t bind_void_then_value();
  /// 2. Bind where both sides are void
  static void bind_void_void();
  /// 3. Let-binding the result of a monadic void call
  static uint64_t let_bind_monadic_void();
  /// 4. Passing unit through a chain of binds
  static void unit_chain();
  /// 5. Match on a value obtained from a bind
  static uint64_t match_after_bind();
  /// 6. Void function called in a non-tail bind position
  static std::string void_nontail();
  /// 7. Nested binds returning unit at every level
  static void deeply_nested_void();

  /// 8. Higher-order: pass a monadic void function as callback
  template <typename F0>
    requires std::is_invocable_r_v<void, F0 &, uint64_t &>
  static void apply_effect(F0 &&f, uint64_t _x0) {
    f(_x0);
    return;
  }

  static void test_apply_effect();
  /// 9. Monadic function returning option unit
  static std::optional<std::monostate> maybe_print(bool b);
  /// 10. Bind result used in a pair
  static std::pair<uint64_t, uint64_t> bind_into_pair();
  /// 11. Void function result stored in list (should stay Unit, not void)
  static List<std::monostate> unit_in_list();
  /// 12. Mixed: some binds void, some value, interleaved
  static uint64_t mixed_binds();
  /// 13. Function that takes itree as argument and sequences
  static void sequence_effects(const std::monostate &e1,
                               const std::monostate &e2);
  static void test_sequence();
};

#endif // INCLUDED_MONADIC_VOID_EDGE
