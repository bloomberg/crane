#pragma once

#include <cstdint>

struct EponymousRecordOwnType_Mod {
  struct EponymousRecordOwnType {
    uint64_t field;
  };

  static inline const EponymousRecordOwnType default_value =
      EponymousRecordOwnType{UINT64_C(5)};
  static inline const uint64_t answer = default_value.field;
};
