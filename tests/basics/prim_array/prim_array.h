#ifndef INCLUDED_PRIM_ARRAY
#define INCLUDED_PRIM_ARRAY

#include <cstdint>
#include <persistent_array.h>

struct PrimArray {
  static inline const persistent_array<uint64_t> arr5 =
      persistent_array<uint64_t>(INT64_C(5), UINT64_C(0));
  static inline const uint64_t get_default = arr5.get(INT64_C(0));
  static inline const int64_t arr5_len = arr5.length();
  static inline const persistent_array<uint64_t> arr5_modified =
      arr5.set(INT64_C(2), UINT64_C(42));
  static inline const uint64_t get_modified = arr5_modified.get(INT64_C(2));
  static inline const uint64_t get_original = arr5.get(INT64_C(2));
  static inline const persistent_array<uint64_t> arr_chain =
      ((arr5.set(INT64_C(0), UINT64_C(10))).set(INT64_C(1), UINT64_C(20)))
          .set(INT64_C(2), UINT64_C(30));
  static inline const uint64_t chain_0 = arr_chain.get(INT64_C(0));
  static inline const uint64_t chain_1 = arr_chain.get(INT64_C(1));
  static inline const uint64_t chain_2 = arr_chain.get(INT64_C(2));
  static inline const uint64_t chain_3 = arr_chain.get(INT64_C(3));
  static inline const persistent_array<uint64_t> arr_copy =
      arr5_modified.copy();
  static inline const uint64_t copy_val = arr_copy.get(INT64_C(2));
  static inline const uint64_t oob_get = arr5.get(INT64_C(99));
};

#endif // INCLUDED_PRIM_ARRAY
