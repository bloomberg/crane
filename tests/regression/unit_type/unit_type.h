#ifndef INCLUDED_UNIT_TYPE
#define INCLUDED_UNIT_TYPE

#include <type_traits>
#include <utility>
#include <variant>

struct UnitType {
  static inline const std::monostate unit_val = std::monostate{};
  static void return_unit(uint64_t _x);
  static uint64_t take_unit(std::monostate _x);
  static uint64_t match_unit(std::monostate u);

  template <typename A, typename B> struct pair {
    // DATA
    A a0;
    B a1;

    // ACCESSORS
    pair<A, B> clone() const { return {a0, a1}; }

    // CREATORS
    static pair<A, B> pair0(A a0, B a1) {
      return {std::move(a0), std::move(a1)};
    }
  };

  template <typename T1, typename T2, typename T3, typename F0>
    requires std::is_invocable_r_v<T3, F0 &, T1 &, T2 &>
  static T3 pair_rect(F0 &&f, const pair<T1, T2> &p) {
    const auto &[a0, a1] = p;
    return f(a0, a1);
  }

  template <typename T1, typename T2, typename T3, typename F0>
    requires std::is_invocable_r_v<T3, F0 &, T1 &, T2 &>
  static T3 pair_rec(F0 &&f, const pair<T1, T2> &p) {
    const auto &[a0, a1] = p;
    return f(a0, a1);
  }

  static inline const pair<uint64_t, std::monostate> pair_with_unit =
      pair<uint64_t, std::monostate>::pair0(UINT64_C(3), std::monostate{});
  static inline const pair<std::monostate, std::monostate> unit_pair =
      pair<std::monostate, std::monostate>::pair0(std::monostate{},
                                                  std::monostate{});
  static void unit_to_unit(std::monostate u);

  template <typename T1, typename T2> static T2 seq(const T1 &, T2 b) {
    return b;
  }

  static inline const uint64_t sequenced = seq<std::monostate, uint64_t>(
      std::monostate{},
      seq<std::monostate, uint64_t>(std::monostate{}, UINT64_C(5)));
  static inline const uint64_t test_take = take_unit(std::monostate{});
  static inline const uint64_t test_match = match_unit(std::monostate{});
  static inline const uint64_t test_seq = sequenced;
};

#endif // INCLUDED_UNIT_TYPE
