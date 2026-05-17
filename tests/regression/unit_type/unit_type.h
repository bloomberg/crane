#ifndef INCLUDED_UNIT_TYPE
#define INCLUDED_UNIT_TYPE

#include <type_traits>
#include <utility>
#include <variant>

struct UnitType {
  static inline const std::monostate unit_val = std::monostate{};
  static void return_unit(unsigned int _x);
  static unsigned int take_unit(std::monostate _x);
  static unsigned int match_unit(std::monostate u);

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

  static inline const pair<unsigned int, std::monostate> pair_with_unit =
      pair<unsigned int, std::monostate>::pair0(3u, std::monostate{});
  static inline const pair<std::monostate, std::monostate> unit_pair =
      pair<std::monostate, std::monostate>::pair0(std::monostate{},
                                                  std::monostate{});
  static void unit_to_unit(std::monostate u);

  template <typename T1, typename T2> static T2 seq(const T1 &, T2 b) {
    return b;
  }

  static inline const unsigned int sequenced =
      seq<std::monostate, unsigned int>(
          std::monostate{},
          seq<std::monostate, unsigned int>(std::monostate{}, 5u));
  static inline const unsigned int test_take = take_unit(std::monostate{});
  static inline const unsigned int test_match = match_unit(std::monostate{});
  static inline const unsigned int test_seq = sequenced;
};

#endif // INCLUDED_UNIT_TYPE
