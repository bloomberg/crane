#ifndef INCLUDED_EFFECT_GETLINE_STRESS
#define INCLUDED_EFFECT_GETLINE_STRESS

#include "crane_fn.h"
#include "obj.h"
#include <any>
#include <atomic>
#include <crane_itree.h>
#include <cstdint>
#include <filesystem>
#include <fstream>
#include <iostream>
#include <memory>
#include <stdexcept>
#include <string>
#include <system_error>
#include <utility>
#include <variant>

using namespace std::string_literals;

template <typename A> struct List;

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

  template <typename _U>
  List(const List<_U> &_other)
      : v_([&]() -> variant_t {
          if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
            return Nil{};
          } else {
            const auto &[a, l] = std::get<typename List<_U>::Cons>(_other.v());
            return Cons{
                [&]() -> A {
                  if constexpr (crane_convertible<A, const _U &>) {
                    return crane_convert<A>(a);
                  } else {
                    throw std::logic_error("unreachable: inactive constructor "
                                           "field at this instantiation");
                  }
                }(),
                (l ? std::make_shared<List<A>>(crane_convert<List<A>>(*l))
                   : nullptr)};
          }
        }()) {}

  static List<A> nil() { return List<A>(Nil{}); }

  static List<A> cons(A a, List<A> l) {
    return List<A>(Cons{std::move(a), std::make_shared<List<A>>(std::move(l))});
  }

  // MANIPULATORS
  ~List() {
    auto _next = [&](variant_t &_v) -> std::shared_ptr<List<A>> {
      if (auto *_alt = std::get_if<Cons>(&_v)) {
        if (_alt->l && _alt->l.use_count() == 1) {
          std::atomic_thread_fence(std::memory_order_acquire);
          return std::move(_alt->l);
        }
      }
      return nullptr;
    };
    std::shared_ptr<List<A>> _cur = _next(v_mut());
    while (_cur) {
      _cur = _next(_cur->v_mut());
    }
  }

  List(const List &) = default;
  List &operator=(const List &) = default;
  List(List &&) noexcept = default;
  List &operator=(List &&) noexcept = default;

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

struct EffectGetlineStress {
  /// 1. get_line in both branches of if-then-else
  static std::string get_or_default(bool ask);
  /// 2. get_line in a match arm
  static std::string get_nth_line(uint64_t n);
  /// 3. Recursive function that uses get_line in a loop
  static List<std::string> read_lines(uint64_t n, const List<std::string> &acc);
  /// 4. get_line result immediately used in another effect
  static void read_and_echo();
  /// 5. get_line result used in a let chain
  static int64_t get_line_length();
  /// 6. Two get_lines with results combined
  static std::string concat_two_lines();
  /// 7. get_line inside a monadic map
  static std::pair<std::string, int64_t> get_and_measure();
  /// 8. Conditional get_line with print
  static std::string interactive_prompt(bool ask);
};

#endif // INCLUDED_EFFECT_GETLINE_STRESS
