#ifndef INCLUDED_PRIM_ARRAY
#define INCLUDED_PRIM_ARRAY

#include <algorithm>
#include <any>
#include <cassert>
#include <cstdint>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <persistent_array.h>
#include <stdexcept>
#include <string>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

struct PrimArray {
  static inline const persistent_array<unsigned int> arr5 =
      persistent_array<unsigned int>(int64_t(5), 0u);
  static inline const unsigned int get_default = arr5.get(int64_t(0));
  static inline const int64_t arr5_len = arr5.length();
  static inline const persistent_array<unsigned int> arr5_modified =
      arr5.set(int64_t(2), 42u);
  static inline const unsigned int get_modified = arr5_modified.get(int64_t(2));
  static inline const unsigned int get_original = arr5.get(int64_t(2));
  static inline const persistent_array<unsigned int> arr_chain =
      arr5.set(int64_t(0), 10u).set(int64_t(1), 20u).set(int64_t(2), 30u);
  static inline const unsigned int chain_0 = arr_chain.get(int64_t(0));
  static inline const unsigned int chain_1 = arr_chain.get(int64_t(1));
  static inline const unsigned int chain_2 = arr_chain.get(int64_t(2));
  static inline const unsigned int chain_3 = arr_chain.get(int64_t(3));
  static inline const persistent_array<unsigned int> arr_copy =
      arr5_modified.copy();
  static inline const unsigned int copy_val = arr_copy.get(int64_t(2));
  static inline const unsigned int oob_get = arr5.get(int64_t(99));
};

#endif // INCLUDED_PRIM_ARRAY
