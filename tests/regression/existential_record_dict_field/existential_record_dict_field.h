#ifndef INCLUDED_EXISTENTIAL_RECORD_DICT_FIELD
#define INCLUDED_EXISTENTIAL_RECORD_DICT_FIELD

#include "crane_fn.h"
#include "fn.h"
#include "obj.h"
#include <cstdint>

struct ExistentialRecordDictField {
  template <typename A> struct ShR {
    crane::fn<uint64_t(A)> sh;

    // ACCESSORS
    template <typename CraneU> operator ShR<CraneU>() const {
      return {crane_convert<crane::fn<uint64_t(CraneU)>>(sh)};
    }
  };

  static inline const ShR<uint64_t> shN =
      ShR<uint64_t>{[](uint64_t n) { return n; }};

  struct packed {
    ShR<crane::obj> dict;
    crane::obj val;
  };

  using ty = crane::obj;
  static uint64_t shp(const packed &p);
  static inline const uint64_t result = shp(packed{shN, UINT64_C(4)});
};

#endif // INCLUDED_EXISTENTIAL_RECORD_DICT_FIELD
