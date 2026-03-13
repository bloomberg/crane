#ifndef INCLUDED_UNIT_TYPE
#define INCLUDED_UNIT_TYPE

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

enum class Unit { e_TT };

struct UnitType {
  static inline const Unit unit_val = Unit::e_TT;
  __attribute__((pure)) static Unit return_unit(const unsigned int _x);
  __attribute__((pure)) static unsigned int take_unit(const Unit _x);
  __attribute__((pure)) static unsigned int match_unit(const Unit u);

  template <typename t_A, typename t_B> struct pair {
    // TYPES
    struct Pair0 {
      t_A d_a0;
      t_B d_a1;
    };

    using variant_t = std::variant<Pair0>;

  private:
    // DATA
    variant_t d_v_;

    // CREATORS
    explicit pair(Pair0 _v) : d_v_(std::move(_v)) {}

  public:
    // TYPES
    struct ctor {
      ctor() = delete;

      static std::shared_ptr<pair<t_A, t_B>> Pair0_(t_A a0, t_B a1) {
        return std::shared_ptr<pair<t_A, t_B>>(
            new pair<t_A, t_B>(Pair0{a0, a1}));
      }

      static std::unique_ptr<pair<t_A, t_B>> Pair0_uptr(t_A a0, t_B a1) {
        return std::unique_ptr<pair<t_A, t_B>>(
            new pair<t_A, t_B>(Pair0{a0, a1}));
      }
    };

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, typename T2, typename T3, MapsTo<T3, T1, T2> F0>
  static T3 pair_rect(F0 &&f, const std::shared_ptr<pair<T1, T2>> &p) {
    return std::visit(
        Overloaded{[&](const typename pair<T1, T2>::Pair0 _args) -> T3 {
          T1 a = _args.d_a0;
          T2 b = _args.d_a1;
          return f(a, b);
        }},
        p->v());
  }

  template <typename T1, typename T2, typename T3, MapsTo<T3, T1, T2> F0>
  static T3 pair_rec(F0 &&f, const std::shared_ptr<pair<T1, T2>> &p) {
    return std::visit(
        Overloaded{[&](const typename pair<T1, T2>::Pair0 _args) -> T3 {
          T1 a = _args.d_a0;
          T2 b = _args.d_a1;
          return f(a, b);
        }},
        p->v());
  }

  static inline const std::shared_ptr<pair<unsigned int, Unit>> pair_with_unit =
      pair<unsigned int, Unit>::ctor::Pair0_(3u, Unit::e_TT);
  static inline const std::shared_ptr<pair<Unit, Unit>> unit_pair =
      pair<Unit, Unit>::ctor::Pair0_(Unit::e_TT, Unit::e_TT);
  __attribute__((pure)) static Unit unit_to_unit(const Unit u);

  template <typename T1, typename T2> static T2 seq(const T1 _x, const T2 b) {
    return b;
  }

  static inline const unsigned int sequenced = seq<Unit, unsigned int>(
      Unit::e_TT, seq<Unit, unsigned int>(Unit::e_TT, 5u));
  static inline const unsigned int test_take = take_unit(Unit::e_TT);
  static inline const unsigned int test_match = match_unit(Unit::e_TT);
  static inline const unsigned int test_seq = sequenced;
};

#endif // INCLUDED_UNIT_TYPE
